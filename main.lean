import Mathlib.Probability.Moments
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Basic

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

#check integral_withDensity_eq_integral_smul

lemma mgf_of_gaussian_integral_eq: (fun x => Real.exp (t * x) * ((√(2 * Real.pi))⁻¹ * Real.exp (- (x ^ 2) / 2))) =  (fun x => Real.exp (t ^ 2/ 2) * (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2)) := by
  ext x
  simp [mul_sub, sub_eq_zero, mul_assoc, mul_comm, mul_left_comm, ← Real.exp_sub, ← Real.exp_add]
  field_simp [Real.exp_ne_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  field_simp
  ring

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
        rw [gaussianReal_of_var_ne_zero]
        · rw [gaussianPDF_def]
          simp [ENNReal.ofReal]
          rw [integral_withDensity_eq_integral_smul]
          ·
            sorry
          sorry
        exact one_ne_zero
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



-- If Y are identically distributed, then they have same mgf for all i.
lemma mgf_sum_of_iid
  (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ)
  (h_indep : ∀ i j, i ≠ j → ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B → μ ({ω | X i ω ∈ A} ∩ {ω | X j ω ∈ B}) = μ {ω | X i ω ∈ A} * μ {ω | X j ω ∈ B})
  (h_iid : ∀ i j, ∀ t, ∫ ω, Real.exp (t * X i ω) ∂μ = ∫ ω, Real.exp (t * X j ω) ∂μ)
  (MGF : (Ω → ℝ) → ℝ → ℝ) : ∀ t, MGF (λ ω => ∑ i in Finset.Ico 0 n, X i ω) t = (MGF (X 0)) t ^ n :=

  sorry
