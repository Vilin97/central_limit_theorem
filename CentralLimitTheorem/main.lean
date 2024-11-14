import Mathlib.Probability.Moments
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Data.Complex.Exponential

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
        have t₂: AEStronglyMeasurable (fun x ↦ Real.exp (t * x)) (Measure.map X μ) := by sorry
        rw [MeasureTheory.integral_map t₁ t₂]
      _ = ∫ (x : ℝ), Real.exp (t * x) * (gaussianPDFReal 0 1 x) := by
        rw [hX]
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
