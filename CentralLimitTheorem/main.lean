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

example (X : ℝ → ℝ) : ∀ t : ℝ, ProbabilityTheory.mgf X (ProbabilityTheory.gaussianReal 0 1) t = Real.exp (t ^ 2 / 2) := by
    intro t
    simp [ProbabilityTheory.mgf, ProbabilityTheory.gaussianReal]
    sorry

-- #check ProbabilityTheory.mgf fun x => ((ProbabilityTheory.gaussianReal 0 1).measureOf x).toReal (ProbabilityTheory.gaussianReal 0 1)
