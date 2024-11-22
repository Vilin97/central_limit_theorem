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

variable [MeasurableSpace Ω] (μ: Measure Ω) [IsProbabilityMeasure μ]
variable (X: Ω → ℝ)
-- TODO: Assert that X is measurable

-- have h: (fun x => ↑(gaussianPDFReal 0 1 x).toNNReal) = (fun x => (gaussianPDFReal 0 1 x)) := by
--   ext x
--   rw [Real.coe_toNNReal]
--   exact gaussianPDFReal_nonneg 0 1 x
-- rw [h]

#check integral_withDensity_eq_integral_smul

lemma mgf_of_gaussian_integral_eq: (fun x => Real.exp (t * x) * ((√(2 * Real.pi))⁻¹ * Real.exp (- (x ^ 2) / 2))) =  (fun x => Real.exp (t ^ 2/ 2) * (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2)) := by
  ext x
  simp [mul_sub, sub_eq_zero, mul_assoc, mul_comm, mul_left_comm, ← Real.exp_sub, ← Real.exp_add]
  field_simp [Real.exp_ne_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  field_simp
  ring

lemma mgf_of_gaussian_integral_eq₂:  (fun x => (gaussianPDFReal 0 1 x).toNNReal • Real.exp (t * x)) = (fun x => Real.exp (t * x) * gaussianPDFReal 0 1 x) := by
  ext x
  rw [Real.toNNReal_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  sorry


theorem mgf_of_gaussian (hXm: Measurable X) (hX: (Measure.map X μ) = (gaussianReal 0 1)) :
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
        simp [toNNreal]
        rw [integral_withDensity_eq_integral_smul]
        · simp [mgf_of_gaussian_integral_eq₂]
        sorry
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

#check mgf_of_gaussian


variable {Y : ℕ → Ω → ℝ}
#check ∑ i ≤ 2, Y i

theorem CLT
(h_meas : ∀ (i : ℕ), Measurable (Y i)) -- measurable
(h_indep : ProbabilityTheory.iIndepFun (fun (i : ℕ) => inferInstance) Y μ) -- independent
(hident : ∀ (i : ℕ), ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ) -- identically distributed
(h_zero_mean : ∀ i, μ[Y i] = 0) -- zero mean
(h_unit_variance : ∀ i, μ[(Y i)^2] = 1) -- unit variance
(h_gaussian: (Measure.map X μ) = (gaussianReal 0 1)) -- limit is standard Gaussian
: ∀ t : ℝ, Filter.Tendsto
  (fun (n : ℕ) => (μ {w | ∑ i ∈ Finset.range n, (Y i w)/(Real.sqrt n) ≤ t}) - (μ {w | X w ≤ t})) Filter.atTop (nhds 0) := by -- converge in distribution
  sorry
