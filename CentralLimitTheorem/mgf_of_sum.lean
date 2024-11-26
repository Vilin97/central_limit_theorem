-- prove mgf of sum of iid random variables is equal to the mgf of one of them to the power of n, where n is the number of iid var

-- how to define 2 random var that indepdent
-- how to define 2 that are identically distributed
-- state the thm

lemma mgf_sum_of_iid {Ω : Type} [ProbabilitySpace Ω]
  (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ)
  (h_indep : ∀ i j, i ≠ j → independent (X i) (X j) P)
  (h_iid : ∀ i j, identical_distribution (X i) (X j) P)
  (MGF : (Ω → ℝ) → (ℝ → ℝ)) :
  (fun t => MGF (fun ω => ∑ i in Finset.range n, X i ω) t) =
  (fun t => (MGF (X 0)) t ^ n) := by

  sorry
