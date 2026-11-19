module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Finset Filter
open scoped BigOperators

namespace BooleanThreshold

private theorem two_pow_le_mul_choose_middle (n : ℕ) :
    (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (n.choose (n / 2) : ℝ) := by
  have he : (2 : ℝ) ^ n = ∑ i ∈ range (n + 1), (n.choose i : ℝ) := by
    exact_mod_cast (Nat.sum_range_choose n).symm
  rw [he]
  calc
    _ ≤ ∑ _i ∈ range (n + 1), (n.choose (n / 2) : ℝ) :=
      sum_le_sum fun i _ => by exact_mod_cast Nat.choose_le_middle i n
    _ = _ := by simp [nsmul_eq_mul]

private theorem choose_succ_le_two_mul_choose {n k : ℕ} (hk : n ≤ 3 * k) :
    (n.choose (k + 1) : ℝ) ≤ 2 * (n.choose k : ℝ) := by
  apply (mul_le_mul_iff_of_pos_right (show 0 < (k : ℝ) + 1 by positivity)).mp
  calc
    _ = (n.choose k : ℝ) * (n - k : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq n k
    _ ≤ (n.choose k : ℝ) * (2 * ((k : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact_mod_cast (show n - k ≤ 2 * (k + 1) by omega)
    _ = _ := by ring

private theorem choose_add_le_two_pow_mul_choose {n k : ℕ} (hk : n ≤ 3 * k) (d : ℕ) :
    (n.choose (k + d) : ℝ) ≤ (2 : ℝ) ^ d * (n.choose k : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      _ ≤ 2 * (n.choose (k + d) : ℝ) :=
        choose_succ_le_two_mul_choose (k := k + d) (by omega)
      _ ≤ 2 * ((2 : ℝ) ^ d * (n.choose k : ℝ)) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

private theorem eventually_nat_add_one_le_exp {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ Real.exp (c * (n : ℝ)) := by
  have hlimit := tendsto_pow_const_div_const_pow_of_one_lt 1 (Real.one_lt_exp_iff.mpr hc)
  filter_upwards [hlimit.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num), eventually_ge_atTop 1]
    with n hn hn'
  have h := (div_le_iff₀ (show 0 < Real.exp c ^ n by positivity)).1 hn
  rw [pow_one, ← Real.exp_nat_mul, mul_comm (n : ℝ)] at h
  have h₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn'
  linarith

/-- Binomial coefficients near the middle of a nearly full prefix have
exponential base arbitrarily close to two. -/
theorem eventually_near_middle_choose_lower {b : ℝ} (hb₁ : 1 < b) (hb₂ : b < 2) :
    ∃ η > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ ℓ ≤ n,
      (1 - η) * (n : ℝ) ≤ (ℓ : ℝ) → ∀ s ≤ ℓ,
        |2 * (s : ℝ) - (ℓ : ℝ)| ≤ 2 * η * (ℓ : ℝ) →
          b ^ n ≤ (ℓ.choose s : ℝ) := by
  have hb₀ : 0 < b := zero_lt_one.trans hb₁
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hGap : 0 < Real.log 2 - Real.log b := sub_pos.mpr (Real.log_lt_log hb₀ hb₂)
  let η := min (1 / 6 : ℝ) ((Real.log 2 - Real.log b) / (4 * Real.log 2))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hGap (by positivity))
  have hη₆ : η ≤ 1 / 6 := min_le_left _ _
  have hηlog : η * (4 * Real.log 2) ≤ Real.log 2 - Real.log b :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let c := (1 - 2 * η) * Real.log 2 - Real.log b
  have hc : 0 < c := by dsimp [c]; nlinarith only [hGap, hηlog]
  refine ⟨η, hη, ?_⟩
  filter_upwards [eventually_nat_add_one_le_exp hc] with n hExp
  intro ℓ hℓn hLong s hs hCenter
  let j := min s (ℓ - s)
  have hjm : j ≤ ℓ / 2 := by dsimp [j]; omega
  have hj : (1 / 2 - η) * (ℓ : ℝ) ≤ (j : ℝ) := by
    rw [show (j : ℝ) = min (s : ℝ) ((ℓ : ℝ) - s) by
      simp [j, Nat.cast_min, Nat.cast_sub hs]]
    rw [abs_le] at hCenter
    exact le_min (by linarith only [hCenter.1]) (by linarith only [hCenter.2])
  have hthird : ℓ ≤ 3 * j := by
    have h := mul_le_mul_of_nonneg_right (show (1 / 3 : ℝ) ≤ 1 / 2 - η by linarith)
      (Nat.cast_nonneg ℓ)
    exact_mod_cast (show (ℓ : ℝ) ≤ 3 * (j : ℝ) by linarith only [hj, h])
  have hsame : ℓ.choose j = ℓ.choose s := by
    by_cases h : s ≤ ℓ - s
    · simp [j, h]
    · simpa only [j, min_eq_right (le_of_not_ge h)] using Nat.choose_symm hs
  let d := ℓ / 2 - j
  have hmid : ((ℓ / 2 : ℕ) : ℝ) ≤ (ℓ : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    exact_mod_cast Nat.div_mul_le_self ℓ 2
  have hdiff : (d : ℝ) ≤ η * (ℓ : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub hjm]
    linarith only [hj, hmid]
  have hchoose : (ℓ.choose (ℓ / 2) : ℝ) ≤ (2 : ℝ) ^ d * (ℓ.choose s : ℝ) := by
    have h := choose_add_le_two_pow_mul_choose hthird d
    rwa [show j + d = ℓ / 2 by dsimp [d]; omega, hsame] at h
  let e := ℓ - d
  have hed : e + d = ℓ := by dsimp [e, d]; omega
  have hSize : (1 - 2 * η) * (n : ℝ) ≤ (e : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (show (ℓ : ℝ) ≤ n by exact_mod_cast hℓn) hη.le
    have he : (e : ℝ) + (d : ℝ) = ℓ := by exact_mod_cast hed
    linarith only [hLong, hdiff, h, he]
  have hPow : b ^ n * ((n : ℝ) + 1) ≤ (2 : ℝ) ^ e := by
    calc
      _ ≤ b ^ n * Real.exp (c * (n : ℝ)) := mul_le_mul_of_nonneg_left hExp (by positivity)
      _ = Real.exp (((1 - 2 * η) * (n : ℝ)) * Real.log 2) := by
        rw [show b ^ n = Real.exp ((n : ℝ) * Real.log b) by
          rw [Real.exp_nat_mul, Real.exp_log hb₀], ← Real.exp_add]
        congr 1
        dsimp [c]
        ring
      _ ≤ Real.exp ((e : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hSize hlog2.le)
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hScaled : (2 : ℝ) ^ e ≤ ((ℓ : ℝ) + 1) * (ℓ.choose s : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < (2 : ℝ) ^ d by positivity)).mp
    calc
      _ = (2 : ℝ) ^ ℓ := by rw [← pow_add, hed]
      _ ≤ ((ℓ : ℝ) + 1) * (ℓ.choose (ℓ / 2) : ℝ) := two_pow_le_mul_choose_middle ℓ
      _ ≤ ((ℓ : ℝ) + 1) * ((2 : ℝ) ^ d * (ℓ.choose s : ℝ)) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ = _ := by ring
  apply (mul_le_mul_iff_of_pos_right (show 0 < (ℓ : ℝ) + 1 by positivity)).mp
  calc
    _ ≤ b ^ n * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ hℓn) (by positivity)
    _ ≤ _ := hPow.trans (hScaled.trans_eq (mul_comm _ _))

end BooleanThreshold
