module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

open Filter
open scoped BigOperators

namespace BooleanThreshold

private theorem twice_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 1 ≤ n
    · have hpow := ih h
      rw [pow_succ]
      omega
    · have : n = 0 := by omega
      simp [this]

/-- The sum of the lower binomial terms in the chamber upper bound. -/
theorem threshold_binomial_tail {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, ((2 ^ n - 1).choose k : ℝ) ≤
      2 * (n : ℝ) ^ 2 * ((2 ^ n - 1).choose n : ℝ) / 2 ^ n := by
  let m := 2 ^ n - 1
  change ∑ k ∈ Finset.range n, (m.choose k : ℝ) ≤
    2 * (n : ℝ) ^ 2 * (m.choose n : ℝ) / 2 ^ n
  have hpow := twice_le_two_pow hn
  have hm : n - 1 ≤ m / 2 := by dsimp [m]; omega
  have hmono (k : ℕ) (hk : k ≤ n - 1) : m.choose k ≤ m.choose (n - 1) := by
    induction hk using Nat.decreasingInduction with
    | self => rfl
    | of_succ j hj ih => exact (Nat.choose_le_succ_of_lt_half_left (hj.trans_le hm)).trans ih
  have hrec : m.choose n * n = m.choose (n - 1) * (m - (n - 1)) := by
    have h := Nat.choose_succ_right_eq m (n - 1)
    rwa [Nat.sub_add_cancel hn] at h
  have hmult : m.choose (n - 1) * 2 ^ n ≤ m.choose n * (2 * n) := by
    calc
      m.choose (n - 1) * 2 ^ n ≤ m.choose (n - 1) * (2 * (m - (n - 1))) :=
        Nat.mul_le_mul_left _ (by dsimp [m]; omega)
      _ = m.choose n * (2 * n) := by
        rw [← mul_left_comm 2, ← hrec, mul_left_comm]
  have hprev : (m.choose (n - 1) : ℝ) ≤ (m.choose n : ℝ) * (2 * n) / 2 ^ n := by
    apply (le_div_iff₀ (by positivity)).2
    exact_mod_cast hmult
  calc
    ∑ k ∈ Finset.range n, (m.choose k : ℝ) ≤
      ∑ _k ∈ Finset.range n, (m.choose (n - 1) : ℝ) :=
        Finset.sum_le_sum fun k hk => by
          exact_mod_cast hmono k (by have := Finset.mem_range.mp hk; omega)
    _ = (n : ℝ) * (m.choose (n - 1) : ℝ) := by simp
    _ ≤ n * ((m.choose n : ℝ) * (2 * n) / 2 ^ n) := by gcongr
    _ = 2 * (n : ℝ) ^ 2 * (m.choose n : ℝ) / 2 ^ n := by ring

/-- The leading binomial term in the count of threshold functions. -/
def thresholdMainTerm (n : ℕ) : ℝ :=
  2 * ((2 ^ n - 1).choose n : ℝ)

theorem thresholdMainTerm_pos {n : ℕ} (hn : 1 ≤ n) : 0 < thresholdMainTerm n := by
  have hpow := twice_le_two_pow hn
  have hchoose : 0 < (2 ^ n - 1).choose n := Nat.choose_pos (by omega)
  unfold thresholdMainTerm
  positivity

/-- The chamber upper bound has a relative error of at most a constant times `n⁻⁹⁹`. -/
theorem threshold_upper_error_from_binomial :
    ∃ C > (0 : ℝ), ∀ n ≥ (1 : ℕ),
      2 * (∑ k ∈ Finset.Iic n, ((2 ^ n - 1).choose k : ℝ)) - thresholdMainTerm n ≤
        C * (thresholdMainTerm n / (n : ℝ) ^ 99) := by
  obtain ⟨A, hA, hpoly⟩ := polynomial_div_pow_bounded 101 (show (1 : ℝ) < 2 by norm_num)
  refine ⟨2 * A, by positivity, fun n hn => ?_⟩
  let m := 2 ^ n - 1
  have hscale : (n : ℝ) ^ 2 / 2 ^ n ≤ A / (n : ℝ) ^ 99 := by
    have hnpos : 0 < (n : ℝ) := by positivity
    apply (le_div_iff₀ (pow_pos hnpos _)).2
    rw [div_mul_eq_mul_div, ← pow_add]
    exact hpoly n
  rw [← Nat.range_succ_eq_Iic, Finset.sum_range_succ, thresholdMainTerm]
  calc
    2 * ((∑ k ∈ Finset.range n, (m.choose k : ℝ)) + (m.choose n : ℝ)) -
      2 * (m.choose n : ℝ) = 2 * (∑ k ∈ Finset.range n, (m.choose k : ℝ)) := by ring
    _ ≤ 2 * (2 * (n : ℝ) ^ 2 * (m.choose n : ℝ) / 2 ^ n) := by
      gcongr
      exact threshold_binomial_tail hn
    _ = (4 * (m.choose n : ℝ)) * ((n : ℝ) ^ 2 / 2 ^ n) := by ring
    _ ≤ (4 * (m.choose n : ℝ)) * (A / (n : ℝ) ^ 99) := by gcongr
    _ = 2 * A * (2 * (m.choose n : ℝ) / (n : ℝ) ^ 99) := by ring

/-- Reduce the claimed count to the chamber upper bound and the eventual lower bound. -/
theorem threshold_asymptotic_of_bounds
    (upper : ∀ n ≥ (1 : ℕ), Nat.card (BooleanThresholdFunction n) ≤
      2 * ∑ k ∈ Finset.Iic n, (2 ^ n - 1).choose k)
    (lower : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      thresholdMainTerm n - (Nat.card (BooleanThresholdFunction n) : ℝ) ≤
        C * (thresholdMainTerm n / (n : ℝ) ^ 99)) :
    ∃ C > (0 : ℝ), ∀ n ≥ (1 : ℕ),
      |(Nat.card (BooleanThresholdFunction n) : ℝ) - thresholdMainTerm n| ≤
        C * thresholdMainTerm n / (n : ℝ) ^ 99 := by
  let error (n : ℕ) := thresholdMainTerm n / (n : ℝ) ^ 99
  have herror n (hn : 1 ≤ n) : 0 < error n :=
    div_pos (thresholdMainTerm_pos hn) (pow_pos (by positivity) _)
  obtain ⟨A, hApos, hA⟩ := threshold_upper_error_from_binomial
  obtain ⟨B, hB⟩ := lower
  have habs : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      |(Nat.card (BooleanThresholdFunction n) : ℝ) - thresholdMainTerm n| ≤ C * error n := by
    refine ⟨max A B, (hB.and (eventually_ge_atTop 1)).mono ?_⟩
    intro n hn
    have hupper : (Nat.card (BooleanThresholdFunction n) : ℝ) ≤
        2 * ∑ k ∈ Finset.Iic n, ((2 ^ n - 1).choose k : ℝ) := by
      exact_mod_cast upper n hn.2
    rw [abs_sub_le_iff]
    exact ⟨(sub_le_sub_right hupper _).trans ((hA n hn.2).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (herror n hn.2).le)),
      hn.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (herror n hn.2).le)⟩
  obtain ⟨C, hC, h⟩ := relative_bound_of_eventually herror habs
  exact ⟨C, hC, fun n hn => by simpa [error, mul_div_assoc] using h n hn⟩

end BooleanThreshold
