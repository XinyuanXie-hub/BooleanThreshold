module

public import BooleanThreshold.JSSConditionalIntervals
public import BooleanThreshold.JSSConditionalSliceAverage

public section

open scoped BigOperators

namespace BooleanThreshold

/-- A cyclic local mass estimate on a prefix gives the integer coefficient
bound used to count the alternate-branch tests. -/
theorem sliceAverage_preprocess_local_bound {P N K n : ℕ} (hN : 0 < N)
    (A : Finset ℤ) (hA : ∃ l u : ℤ, A = Finset.Ico l u)
    (hLo : N ≤ A.card) (hHi : A.card ≤ K * N) (hP : A.card ≤ P)
    (a : ℕ → ZMod P) (f : ZMod P → ℝ) (hf : ∀ t, 0 ≤ f t) (ℓ s : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (hMass : ∀ u, ∑ t ∈ cyclicInterval P N u, sliceAverage a f ℓ s t ≤ R / Real.sqrt (n : ℝ))
    (t : ZMod P) (b : Bool) :
    (∑ z ∈ A, sliceAverage a f ℓ s (t + if b then -(z : ZMod P) else (z : ZMod P))) ≤
      ((K : ℝ) * R) / ((N : ℝ) * Real.sqrt (n : ℝ)) * (A.card : ℝ) := by
  refine (sum_signed_integer_interval_le_of_cyclic_mass hN A hA hLo hHi hP
    (sliceAverage a f ℓ s) (sliceAverage_nonneg a f hf ℓ s) (by positivity) hMass t b).trans_eq ?_
  rw [← mul_div_assoc, div_div, mul_comm (Real.sqrt (n : ℝ))]

end BooleanThreshold
