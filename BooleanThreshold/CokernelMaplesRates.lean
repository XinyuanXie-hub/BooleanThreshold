module

public import BooleanThreshold.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Ring

public noncomputable section

open Filter
open scoped BigOperators Topology

namespace BooleanThreshold

/-- The logarithmically many columns left after the initial exposure. -/
@[expose] def maplesSuffixLength (L : ℝ) (n : ℕ) : ℕ := ⌈L * Real.log (n : ℝ)⌉₊

private theorem suffixLength_cast_le {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 3 ≤ n) :
    (maplesSuffixLength L n : ℝ) ≤ (L + 1) * Real.log (n : ℝ) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le (show 0 < (n : ℝ) by positivity)).mpr
      (Real.exp_one_lt_three.le.trans hn')
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hL (zero_le_one.trans hlog))).le
  unfold maplesSuffixLength
  linarith only [hceil, hlog]

theorem eventually_maplesSuffixLength_le_half {L : ℝ} (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop, 2 * maplesSuffixLength L n ≤ n := by
  let a := 1 / (2 * (L + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 1)).bound ha
  filter_upwards [eventually_ge_atTop 3, tendsto_natCast_atTop_atTop.eventually hsmall] with n hn hsmalln
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hsmall' : Real.log (n : ℝ) ≤ a * (n : ℝ) := by
    simpa only [Function.comp_apply, id_eq, pow_one, Real.norm_eq_abs, abs_of_nonneg hlog,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hsmalln
  have heq : (L + 1) * a = 1 / 2 := by
    dsimp [a]
    field_simp
  have h := (suffixLength_cast_le hL hn).trans
    (mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ L + 1))
  rw [← mul_assoc, heq] at h
  exact_mod_cast (show 2 * (maplesSuffixLength L n : ℝ) ≤ n by linarith only [h])

private theorem eventually_maples_quotient_error_le {L d : ℝ} (hL : 0 ≤ L) (hd : 0 < d)
    (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q ≤ n ^ B →
      (q : ℝ) ^ (maplesSuffixLength L n * maplesSuffixLength L n) * Real.exp (-d * (n : ℝ)) ≤
        Real.exp (-(d / 2) * (n : ℝ)) := by
  let T := (B : ℝ) * (L + 1) ^ 2
  let a := (d / 2) / (T + 1)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound ha
  filter_upwards [eventually_ge_atTop 3, tendsto_natCast_atTop_atTop.eventually hsmall]
    with n hn hsmalln q hq
  let k := maplesSuffixLength L n
  let x := Real.log (n : ℝ)
  have hnpos : 0 < (n : ℝ) := by positivity
  have hx : 0 ≤ x := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hsmall' : x ^ 3 ≤ a * (n : ℝ) := by
    simpa only [x, Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx _),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hsmalln
  have hkb : (k : ℝ) ≤ (L + 1) * x := suffixLength_cast_le hL hn
  have ht : (B : ℝ) * ((k : ℝ) ^ 2) * x ≤ (d / 2) * (n : ℝ) := by
    calc
      _ ≤ (B : ℝ) * (((L + 1) * x) ^ 2) * x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hkb _) (Nat.cast_nonneg _)) hx
      _ = T * x ^ 3 := by dsimp [T]; ring
      _ ≤ (T + 1) * x ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hx _)
      _ ≤ (T + 1) * (a * (n : ℝ)) := mul_le_mul_of_nonneg_left hsmall' (by positivity)
      _ = _ := by
        dsimp [a]
        rw [← mul_assoc, mul_comm (T + 1), div_mul_cancel₀
          _ (by positivity : (0 : ℝ) < T + 1).ne']
  change (q : ℝ) ^ (k * k) * Real.exp (-d * (n : ℝ)) ≤ _
  calc
    _ ≤ ((n : ℝ) ^ B) ^ (k * k) * Real.exp (-d * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hq) _) (by positivity)
    _ = Real.exp (((B : ℝ) * (k : ℝ) ^ 2 * x) + (-d * (n : ℝ))) := by
      rw [show (n : ℝ) = Real.exp x from (Real.exp_log hnpos).symm, ← Real.exp_nat_mul,
        ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      push_cast
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      linarith only [ht]

private theorem eventually_poly_geom_le {A a base : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hbase : 0 < base) (hbase' : base < 1) (B M : ℕ) :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ B * base ^ n ≤ a / (n : ℝ) ^ M := by
  have hb := one_lt_inv₀ hbase |>.mpr hbase'
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (B + M) hb
  have hs := ht.eventually_le_const (div_pos ha hA)
  filter_upwards [hs, eventually_ge_atTop 1] with n hn hpos
  have hN : 0 < (n : ℝ) := by exact_mod_cast hpos
  change (n : ℝ) ^ (B + M) / (base⁻¹) ^ n ≤ a / A at hn
  rw [inv_pow, div_inv_eq_mul, pow_add] at hn
  apply (le_div_iff₀ (pow_pos hN _)).mpr
  have h := (le_div_iff₀ hA).mp hn
  convert h using 1
  ring

theorem maplesSuffixLength_nonneg_factor (M : ℕ) :
    0 ≤ (((M : ℝ) + 2) / Real.log 2) := by
  have hlog := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  positivity

/-- A logarithmically shortened exposure makes the rank-error term
smaller than any prescribed inverse power. -/
private theorem eventually_maples_rank_error_le (M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      204 * (n : ℝ) * (1 / 2 : ℝ) ^ maplesSuffixLength (((M : ℝ) + 2) / Real.log 2) n ≤
        (1 / 4 : ℝ) / (n : ℝ) ^ M := by
  filter_upwards [eventually_ge_atTop (816 : ℕ)] with n hn
  let L := ((M : ℝ) + 2) / Real.log 2
  let k := maplesSuffixLength L n
  have hnR : (816 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by positivity
  have hlog := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hk : ((M : ℝ) + 2) * Real.log (n : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    have hk' := mul_le_mul_of_nonneg_right (Nat.le_ceil (L * Real.log (n : ℝ))) hlog.le
    change L * Real.log (n : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log 2 at hk'
    convert hk' using 1
    dsimp [L]
    field_simp
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 / (n : ℝ) ^ (M + 2) := by
    rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]]
    rw [← Real.exp_nat_mul, show (n : ℝ) ^ (M + 2) = Real.exp (((M : ℝ) + 2) * Real.log (n : ℝ)) by
      rw [show ((M : ℝ) + 2) = ((M + 2 : ℕ) : ℝ) by simp, Real.exp_nat_mul, Real.exp_log hn₀]]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith only [hk]
  change 204 * (n : ℝ) * (1 / 2 : ℝ) ^ k ≤ _
  refine (mul_le_mul_of_nonneg_left hpow (by positivity)).trans ?_
  rw [pow_add]
  apply (le_div_iff₀ (pow_pos hn₀ M)).mpr
  field_simp
  nlinarith only [hnR, mul_le_mul_of_nonneg_right hnR hn₀.le]

/-- The error contributions from mixing, sparse normals, and rank
failures are bounded by the prescribed inverse power. -/
theorem eventually_maples_comparison_error_le {d : ℝ} (hd : 0 < d) (B M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q ≤ n ^ B →
      let k := maplesSuffixLength (((M : ℝ) + 2) / Real.log 2) n
      (k : ℝ) * (q : ℝ) ^ (k * k) * Real.exp (-d * (n : ℝ)) +
        ((102 : ℝ) * (14739 / 16384 : ℝ) ^ n + 2 * (q : ℝ) * (1 / 2 : ℝ) ^ n) +
        204 * (n : ℝ) * (1 / 2 : ℝ) ^ k ≤ 1 / (n : ℝ) ^ M := by
  let L := ((M : ℝ) + 2) / Real.log 2
  have hL : 0 ≤ L := maplesSuffixLength_nonneg_factor M
  have hshift : 0 < Real.exp (-(d / 2)) := Real.exp_pos _
  have hshift' : Real.exp (-(d / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  filter_upwards [eventually_maples_rank_error_le M, eventually_maplesSuffixLength_le_half hL,
    eventually_maples_quotient_error_le hL hd B,
    eventually_poly_geom_le (A := 1) (a := 1 / 4) (by norm_num) (by norm_num) hshift hshift' 1 M,
    eventually_poly_geom_le (A := 102) (a := 1 / 4) (base := 14739 / 16384)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 M,
    eventually_poly_geom_le (A := 2) (a := 1 / 4) (base := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) B M]
    with n hrank hk hqpow hmix hsparse hdivisor q hq
  let k := maplesSuffixLength L n
  have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show k ≤ n by dsimp [k] at *; omega)
  have hmix' : (k : ℝ) * (q : ℝ) ^ (k * k) * Real.exp (-d * (n : ℝ)) ≤
      (1 / 4 : ℝ) / (n : ℝ) ^ M := by
    rw [mul_assoc]
    have hb := mul_le_mul hkn (hqpow q hq) (by positivity) (Nat.cast_nonneg (α := ℝ) n)
    rw [mul_comm (-(d / 2)), Real.exp_nat_mul] at hb
    exact hb.trans (by simpa only [one_mul, pow_one] using hmix)
  have hsparse' : (102 : ℝ) * (14739 / 16384 : ℝ) ^ n ≤ (1 / 4 : ℝ) / (n : ℝ) ^ M :=
    by simpa only [pow_zero, mul_one] using hsparse
  have hdivisor' : (2 : ℝ) * (q : ℝ) * (1 / 2 : ℝ) ^ n ≤ (1 / 4 : ℝ) / (n : ℝ) ^ M :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hq)
      (by norm_num : (0 : ℝ) ≤ 2)) (by positivity)).trans hdivisor
  change (k : ℝ) * (q : ℝ) ^ (k * k) * Real.exp (-d * (n : ℝ)) + _ + _ ≤ _
  exact (add_le_add (add_le_add hmix' (add_le_add hsparse' hdivisor')) hrank).trans_eq (by ring)

end BooleanThreshold
