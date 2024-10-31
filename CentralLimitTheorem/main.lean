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

theorem mgf_of_gaussian (hX: (Measure.map X μ) = (gaussianReal 0 1)) :
  ∀ t : ℝ, mgf X μ t = Real.exp (t ^ 2 / 2) := by
    intro t
    simp [mgf]
    calc
      mgf X μ t = μ[fun w => Real.exp ((X w) * t)] := by sorry
      _ = (Measure.map X μ)[fun x => Real.exp (x * t)] := by sorry
      _ = ∫ (x : ℝ), Real.exp (t * x) * (gaussianPDFReal 0 1 x) := by sorry
      _ = ∫ (x : ℝ), Real.exp (t * x) * (√(2 * Real.pi))⁻¹ * Real.exp (- (x ^ 2) / 2) := by sorry
      _ = ∫ (x : ℝ), (√(2 * Real.pi))⁻¹ * Real.exp (t * x - (x ^ 2) / 2) := by sorry
      _ = Real.exp (t ^ 2/ 2) * ∫ (x : ℝ), (√(2 * Real.pi))⁻¹ * Real.exp (- ((x - t) ^ 2) / 2) := by sorry
      _ = Real.exp (t ^ 2 / 2) := by sorry

#check mgf_of_gaussian

-- #check ProbabilityTheory.mgf fun x => ((ProbabilityTheory.gaussianReal 0 1).measureOf x).toReal (ProbabilityTheory.gaussianReal 0 1)
