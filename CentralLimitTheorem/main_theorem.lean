import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Probability.Moments
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Data.Complex.Exponential
import Mathlib.Probability.StrongLaw
import CentralLimitTheorem.main

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
  (fun (n : ℕ) => (μ {w | ∑ i ∈ Finset.range n, (Y i w) * (√n)⁻¹ ≤ t}) - (μ {w | X w ≤ t})) Filter.atTop (nhds 0) := by -- converge in distribution
    sorry
