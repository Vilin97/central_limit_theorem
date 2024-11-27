import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Probability.Moments
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Data.Complex.Exponential
import Mathlib.Probability.StrongLaw

#check ProbabilityTheory.mgf
#check ProbabilityTheory.gaussianReal

-- Blueprint: https://www.overleaf.com/read/gbcxfrhjfxqv#a8e535

-- Plan:
-- 1. Play around with mathlib's mgf (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments.html) and gaussian distribution (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian.html)
-- 2. State lemma 2 in the blueprint
-- 3. ...

open MeasureTheory ProbabilityTheory

variable [MeasurableSpace Ω] (μ: Measure Ω)

-- MGF of standard gaussian is exp(t^2/2)
theorem mgf_of_gaussian (X: Ω → ℝ) (hXm: Measurable X) (hX: (Measure.map X μ) = (gaussianReal 0 1)) :
  ∀ t : ℝ, mgf X μ t = Real.exp (t ^ 2 / 2) := by
    intro t
    calc
      mgf X μ t = μ[fun w => Real.exp (t * (X w))] := by
        simp [mgf]
      _ = (Measure.map X μ)[fun x => Real.exp (t * x)] := by
        simp
        have t₁: AEMeasurable X μ := by exact Measurable.aemeasurable hXm
        have t₂: AEStronglyMeasurable (fun x ↦ Real.exp (t * x)) (Measure.map X μ) := by
          apply AEMeasurable.aestronglyMeasurable
          apply Measurable.aemeasurable
          apply Real.measurable_exp.comp
          exact Continuous.measurable (continuous_const.mul continuous_id)
        rw [MeasureTheory.integral_map t₁ t₂]
      _ = ∫ (x : ℝ), Real.exp (t * x) * (gaussianPDFReal 0 1 x) := by
        rw [hX]
        rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
        rw [gaussianPDF_def]
        simp [ENNReal.ofReal]
        rw [integral_withDensity_eq_integral_smul]
        have : (fun x => (gaussianPDFReal 0 1 x).toNNReal • Real.exp (t * x)) = (fun x => Real.exp (t * x) * gaussianPDFReal 0 1 x) := by
            ext x
            rw [NNReal.smul_def]
            rw [Real.coe_toNNReal (gaussianPDFReal 0 1 x) (gaussianPDFReal_nonneg 0 1 x)]
            rw [mul_comm (Real.exp (t * x)) (gaussianPDFReal 0 1 x)]
            rfl
        · simp [this]
        apply Measurable.real_toNNReal
        exact measurable_gaussianPDFReal 0 1
      _ = ∫ (x : ℝ), Real.exp (t * x) * ((√(2 * Real.pi))⁻¹ * Real.exp (- (x ^ 2) / 2)) := by
        simp [gaussianPDFReal]
      _ = Real.exp (t ^ 2/ 2) * ∫ (x : ℝ), (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2) := by
        have : (fun x => Real.exp (t * x) * ((√(2 * Real.pi))⁻¹ * Real.exp (- (x ^ 2) / 2))) =  (fun x => Real.exp (t ^ 2/ 2) * (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2)) := by
            ext x
            simp [mul_sub, sub_eq_zero, mul_assoc, mul_comm, mul_left_comm, ← Real.exp_sub, ← Real.exp_add]
            field_simp [Real.exp_ne_zero]
            rw [← Real.exp_add, ← Real.exp_add]
            field_simp
            ring
        rw [this]
        simp [mul_assoc, integral_mul_left]
      _ = Real.exp (t ^ 2 / 2) := by
        have h: ∫ (x : ℝ), (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2) = ∫ (x : ℝ), (gaussianPDFReal t 1 x) := by
          simp [gaussianPDFReal]
        rw [h, integral_gaussianPDFReal_eq_one]
        ring
        simp only [ne_eq, one_ne_zero, not_false_eq_true]

-- (mgf α • X) t = (mgf X) (α * t)
lemma mgf_smul_left (X : Ω → ℝ) (α t : ℝ) : (mgf (α • X)) μ t = (mgf X) μ (t * α) := by
    rw [mgf, mgf]
    simp [mul_assoc]

-- mgfs of identically distributed function are equal
lemma mgf_ident_fun (X Y : Ω → ℝ) (hident : IdentDistrib X Y μ μ) : mgf X μ t = mgf Y μ t := by
    rw [mgf, mgf]
    apply IdentDistrib.integral_eq
    let u := fun x => Real.exp (t * x)
    have compX : (fun ω ↦ Real.exp (t * X ω)) = u ∘ X := rfl
    have compY : (fun ω ↦ Real.exp (t * Y ω)) = u ∘ Y := rfl
    rw [compX, compY]
    exact IdentDistrib.comp hident (Measurable.exp (measurable_const_mul t))

-- Xᵢ iid => mgf (1/√n ∑ᵢ Xᵢ) t = ((mgf X₀) (t/√n))^n
theorem mgf_of_iid
{Y : ℕ → Ω → ℝ} -- sequence of random variables
{Z : ℕ → Ω → ℝ} -- sum of a given number of random variables
(h_meas : ∀ (i : ℕ), Measurable (Y i)) -- measurable
(h_indep : ProbabilityTheory.iIndepFun (fun (i : ℕ) => inferInstance) Y μ) -- independent
(hident : ∀ (i : ℕ), ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ) -- identically distributed
(Z_def : ∀ n : ℕ, Z n = (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, (Y i)) ) -- def of Z as the sum of a given number of random variables
: ∀ n : ℕ, ∀ t : ℝ, mgf (Z n) μ t = (mgf (Y 0) μ (t * (√n)⁻¹)) ^ n := by
    intro n
    rw [Z_def]
    intro t
    rw [mgf_smul_left μ (∑ i ∈ Finset.range n, (Y i)) (Real.sqrt n)⁻¹ t]
    rw [iIndepFun.mgf_sum h_indep h_meas]
    have mgf_eq : ∀ i ∈ Finset.range n, (fun i => (mgf (Y i) μ (t * (√↑n)⁻¹))) i = mgf (Y 0) μ (t * (√↑n)⁻¹) := by
        intro i _
        exact mgf_ident_fun μ (Y i) (Y 0) (hident i)
    nth_rw 4 [← Finset.card_range n]
    exact Finset.prod_eq_pow_card mgf_eq

-- TODO: add little o term
theorem lemma4
{Yi : Ω → ℝ}
(h_meas : Measurable Yi)
(h_zero_mean : μ[Yi] = 0) -- zero mean
(h_unit_variance : μ[Yi ^ 2] = 1) -- unit variance
: ∀ n : ℕ, n ≠ 0 → (∀ t : ℝ, mgf Yi μ (t / Real.sqrt n) = 1 + t ^ 2 / (2 * n)) := by
  sorry
-- Asymptotics.IsLittleO

-- TODO: add little o term
theorem lemma5
: ∀ t : ℝ, Filter.Tendsto (fun (n : ℕ) => (1 + t ^ 2 / (2 * n)) ^ n) Filter.atTop (nhds (Real.exp (t ^ 2 / 2))) := by
  intro t
  let t' : ℝ := t ^ 2 / 2
  have h₁ : (fun (n : ℕ) => (1 + t ^ 2 / (2 * n)) ^ n) = (fun (n : ℕ) => (1 + t' / n) ^ n) := by
    ext n
    simp [t']
    ring
  have h₂ : Real.exp (t ^ 2 / 2) = Real.exp t' := by
    simp [t']
  rw [h₁, h₂]
  apply tendsto_one_plus_div_pow_exp

-- hard!
theorem lemma45
{Yi : Ω → ℝ}
(h_meas : Measurable Yi)
(h_zero_mean : μ[Yi] = 0) -- zero mean
(h_unit_variance : μ[Yi ^ 2] = 1) -- unit variance
: ∀ t : ℝ, Filter.Tendsto (fun (n : ℕ) => mgf Yi μ (t / Real.sqrt n)) Filter.atTop (nhds (Real.exp (t ^ 2 / 2))) := sorry

theorem lemma6
{Y : ℕ → Ω → ℝ} -- sequence of random variables
{Z : ℕ → Ω → ℝ} -- sum of a given number of random variables
{X: Ω → ℝ}
(hXm: Measurable X)
(hX: (Measure.map X μ) = (gaussianReal 0 1))
(h_meas : ∀ (i : ℕ), Measurable (Y i)) -- measurable
(h_indep : ProbabilityTheory.iIndepFun (fun (i : ℕ) => inferInstance) Y μ) -- independent
(hident : ∀ (i : ℕ), ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ) -- identically distributed
(h_zero_mean : ∀ i, μ[Y i] = 0) -- zero mean
(h_unit_variance : ∀ i, μ[(Y i)^2] = 1) -- unit variance
(Z_def : ∀ n : ℕ, ∀ w : Ω, Z n w = ∑ i ∈ Finset.range n, (Y i w) / (Real.sqrt n)) -- def of Z as the sum of a given number of random variables
: ∀ t : ℝ, Filter.Tendsto (fun (n : ℕ) => mgf (Z n) μ t - mgf X μ t) Filter.atTop (nhds 0) := by
  sorry

-- exp (↑(-x) * Complex.I)

theorem levy_continuity
{X : ℕ → Ω → ℝ} -- sequence of random variables
{Y : Ω → ℝ} -- another random variable
(pointwise_conv : ∀ t : ℝ, Filter.Tendsto (fun (n : ℕ) => mgf (X n) μ t - mgf Y μ t) Filter.atTop (nhds 0)) -- mgf Xn and mgf Y converge pointwise
: ∀ t : ℝ, Filter.Tendsto (fun (n : ℕ) => (μ {w | ∑ i ∈ Finset.range n, (X i w) ≤ t}) - (μ {w | Y w ≤ t})) Filter.atTop (nhds 0) := by
  sorry
