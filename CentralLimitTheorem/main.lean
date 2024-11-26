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

theorem CLT
{Y : ℕ → Ω → ℝ} -- sequence of random variables
(h_meas : ∀ (i : ℕ), Measurable (Y i)) -- measurable
(h_indep : ProbabilityTheory.iIndepFun (fun (i : ℕ) => inferInstance) Y μ) -- independent
(hident : ∀ (i : ℕ), ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ) -- identically distributed
(h_zero_mean : ∀ i, μ[Y i] = 0) -- zero mean
(h_unit_variance : ∀ i, μ[(Y i)^2] = 1) -- unit variance
(h_gaussian: (Measure.map X μ) = (gaussianReal 0 1)) -- limit is standard Gaussian
: ∀ t : ℝ, Filter.Tendsto
  (fun (n : ℕ) => (μ {w | ∑ i ∈ Finset.range n, (Y i w)/(Real.sqrt n) ≤ t}) - (μ {w | X w ≤ t})) Filter.atTop (nhds 0) := by -- converge in distribution
  sorry

lemma mgf_of_gaussian_integral_eq: (fun x => Real.exp (t * x) * ((√(2 * Real.pi))⁻¹ * Real.exp (- (x ^ 2) / 2))) =  (fun x => Real.exp (t ^ 2/ 2) * (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2)) := by
  ext x
  simp [mul_sub, sub_eq_zero, mul_assoc, mul_comm, mul_left_comm, ← Real.exp_sub, ← Real.exp_add]
  field_simp [Real.exp_ne_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  field_simp
  ring

lemma mgf_of_gaussian_integral_eq₂:  (fun x => (gaussianPDFReal 0 1 x).toNNReal • Real.exp (t * x)) = (fun x => Real.exp (t * x) * gaussianPDFReal 0 1 x) := by
  ext x
  rw [NNReal.smul_def]
  rw [Real.coe_toNNReal (gaussianPDFReal 0 1 x) (gaussianPDFReal_nonneg 0 1 x)]
  rw [mul_comm (Real.exp (t * x)) (gaussianPDFReal 0 1 x)]
  rfl

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
        · simp [mgf_of_gaussian_integral_eq₂]
        apply Measurable.real_toNNReal
        exact measurable_gaussianPDFReal 0 1
      _ = ∫ (x : ℝ), Real.exp (t * x) * ((√(2 * Real.pi))⁻¹ * Real.exp (- (x ^ 2) / 2)) := by
        simp [gaussianPDFReal]
      _ = Real.exp (t ^ 2/ 2) * ∫ (x : ℝ), (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2) := by
        rw [mgf_of_gaussian_integral_eq]
        simp [mul_assoc, integral_mul_left]
      _ = Real.exp (t ^ 2 / 2) := by
        have h: ∫ (x : ℝ), (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2) = ∫ (x : ℝ), (gaussianPDFReal t 1 x) := by
          simp [gaussianPDFReal]
        rw [h, integral_gaussianPDFReal_eq_one]
        ring
        simp only [ne_eq, one_ne_zero, not_false_eq_true]

theorem mgf_of_iid_unit_norm
{Y : ℕ → Ω → ℝ} -- sequence of random variables
{Z : ℕ → Ω → ℝ} -- sum of a given number of random variables
(h_meas : ∀ (i : ℕ), Measurable (Y i)) -- measurable
(h_indep : ProbabilityTheory.iIndepFun (fun (i : ℕ) => inferInstance) Y μ) -- independent
(hident : ∀ (i : ℕ), ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ) -- identically distributed
(h_zero_mean : ∀ i, μ[Y i] = 0) -- zero mean
(h_unit_variance : ∀ i, μ[(Y i)^2] = 1) -- unit variance
(Z_def : ∀ n : ℕ, ∀ w : Ω, Z n w = ∑ i ∈ Finset.range n, (Y i w) / (Real.sqrt n)) -- def of Z as the sum of a given number of random variables
: ∀ n : ℕ, ∀ t : ℝ, mgf (Z n) μ t = (mgf (Y 0) μ (t / Real.sqrt n)) ^ n := by
  sorry

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
