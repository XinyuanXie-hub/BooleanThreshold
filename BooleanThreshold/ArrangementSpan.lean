module

public import BooleanThreshold.ArrangementTuples

public section

namespace BooleanThreshold

/-- A bound on bad spans of raw sign tuples gives a lower bound on the threshold-function count. -/
theorem threshold_count_lower_of_bad_signSpan_card (n : ℕ) (hn : 1 ≤ n) (δ : ℝ)
    (h : (Nat.card {v : Fin n → Fin (n + 1) → Bool // ¬ SignSpanGood v} : ℝ) ≤
      δ * ((2 : ℝ) ^ (n + 1)) ^ n) :
    (1 - δ - n / (2 : ℝ) ^ n) * (2 * ((2 ^ n - 1).choose n : ℝ)) ≤
      (Nat.card (BooleanThresholdFunction n) : ℝ) := by
  classical
  let good : Type := {v : Fin n → Fin n → Bool // NormalizedGoodTuple v}
  let bad : Type := {v : Fin n → Fin n → Bool // ¬ NormalizedGoodTuple v}
  let rawBad : Type := {v : Fin n → Fin (n + 1) → Bool // ¬ SignSpanGood v}
  have hsplit : Nat.card good + Nat.card bad = (2 ^ n) ^ n := by
    have hs := Nat.card_congr (Equiv.sumCompl (@NormalizedGoodTuple n))
    rw [Nat.card_sum] at hs
    simpa [good, bad, Nat.card_fun, Nat.card_eq_fintype_card] using hs
  have hsplit' : (Nat.card good : ℝ) + (Nat.card bad : ℝ) = ((2 : ℝ) ^ n) ^ n := by
    exact_mod_cast hsplit
  have hraw : (2 : ℝ) ^ n * (Nat.card bad : ℝ) ≤ (Nat.card rawBad : ℝ) := by
    exact_mod_cast
      (show 2 ^ n * Nat.card bad ≤ Nat.card rawBad from card_badNormalized_mul_le n n)
  have hbad : (Nat.card bad : ℝ) ≤ δ * ((2 : ℝ) ^ n) ^ n := by
    refine (mul_le_mul_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ n)).mp ?_
    calc
      _ ≤ (Nat.card rawBad : ℝ) := hraw
      _ ≤ δ * ((2 : ℝ) ^ (n + 1)) ^ n := h
      _ = _ := by rw [pow_succ, mul_pow]; ring
  have hgood : (1 - δ) * ((2 : ℝ) ^ n) ^ n ≤ (Nat.card good : ℝ) := by
    rw [sub_mul, one_mul, sub_le_iff_le_add]
    exact hsplit'.symm.le.trans (add_le_add le_rfl hbad)
  have hsub := choose_mul_sub_le_card_good_sets n hn δ hgood
  have hcount : 2 * ((arrangementGoodSets n).card : ℝ) ≤
      (Nat.card (BooleanThresholdFunction n) : ℝ) := by
    exact_mod_cast twice_good_sets_le_threshold_count n
  rw [mul_left_comm]
  exact (mul_le_mul_of_nonneg_left hsub (by norm_num)).trans hcount

end BooleanThreshold
