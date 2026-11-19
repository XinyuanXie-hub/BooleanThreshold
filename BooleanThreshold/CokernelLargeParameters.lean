module

public import BooleanThreshold.CokernelLargePrimes
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Filter

namespace BooleanThreshold

theorem eventually_constant_lt_nat_rpow {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C < (N : ℝ) ^ a := by
  exact ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop C)

private theorem eventually_scale_rpow_lt {a b : ℝ} (hab : a < b) (A : ℝ)
    {B : ℝ} (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, A * (N : ℝ) ^ a < B * (N : ℝ) ^ b := by
  filter_upwards [eventually_constant_lt_nat_rpow (sub_pos.mpr hab) (A / B), eventually_ge_atTop 1]
    with N hN hpos
  have hN' : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hh := (div_lt_iff₀ hB).1 hN
  calc
    _ = (N : ℝ) ^ a * A := mul_comm _ _
    _ < (N : ℝ) ^ a * ((N : ℝ) ^ (b - a) * B) :=
      mul_lt_mul_of_pos_left hh (Real.rpow_pos_of_pos hN' _)
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_add hN']
      rw [show a + (b - a) = b by ring, mul_comm]

private theorem log_nat_le_rpow {N : ℕ} {a : ℝ} (ha : 0 < a) :
    Real.log (N : ℝ) ≤ (N : ℝ) ^ a / a := Real.log_le_rpow_div (Nat.cast_nonneg _) ha

/-- The number of remaining columns is at most three times the fourth root. -/
theorem binaryRemainingLength_le_quarter_root {N : ℕ} (hN : 1 ≤ N) :
    ((N - binaryInitialLength N : ℕ) : ℝ) ≤ 3 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  let t := ⌈2 * (N : ℝ) ^ (1 / 4 : ℝ)⌉₊
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ht : ((N - binaryInitialLength N : ℕ) : ℝ) ≤ (t : ℝ) := by
    change ((N - (N - t) : ℕ) : ℝ) ≤ (t : ℝ)
    exact_mod_cast (show N - (N - t) ≤ t by omega)
  have hceil := (Nat.ceil_lt_add_one (a := 2 * (N : ℝ) ^ (1 / 4 : ℝ)) (by positivity)).le
  have hroot := Real.one_le_rpow hN' (by norm_num : (0 : ℝ) ≤ 1 / 4)
  exact ht.trans (hceil.trans (by linarith))

theorem eventually_binaryInitialLength_half : ∀ᶠ N : ℕ in atTop, N ≤ 2 * binaryInitialLength N := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_scale_rpow_lt (a := 1 / 4) (b := 1) (by norm_num) 6 (B := 1) (by norm_num)]
    with N hN hscale
  let t := N - binaryInitialLength N
  have ht := binaryRemainingLength_le_quarter_root hN
  have hN' : 2 * t ≤ N := by
    have h : (2 : ℝ) * t ≤ (N : ℝ) := by
      norm_num [Real.rpow_one] at hscale
      change (t : ℝ) ≤ _ at ht
      linarith
    exact_mod_cast h
  dsimp [t] at hN'
  omega

/-- Bertrand's postulate gives an auxiliary prime with logarithm between
one and two times a positive power, above any prescribed polynomial cutoff. -/
theorem eventually_exists_auxiliary_binary_prime_of_rpow (K : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ N ^ K < p ∧
      Real.exp ((N : ℝ) ^ a) < (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ a) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_constant_lt_nat_rpow ha (Real.log 4),
    eventually_scale_rpow_lt (a := a / 2) (b := a) (by linarith) ((K : ℝ) / (a / 2))
      (B := 1) (by norm_num)] with N hN hlog hscale
  let x := (N : ℝ) ^ a
  let n := ⌈Real.exp x⌉₊
  have hnn : n ≠ 0 := Nat.ne_of_gt (Nat.one_le_ceil_iff.mpr (Real.exp_pos x))
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hnn
  have hx : Real.exp x < (p : ℝ) := (Nat.le_ceil _).trans_lt (by exact_mod_cast hnp)
  have hN' : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hK : ((N : ℝ) ^ K) < Real.exp x := by
    apply (Real.log_lt_iff_lt_exp (by positivity)).mp
    rw [Real.log_pow]
    have hl := log_nat_le_rpow (N := N) (a := a / 2) (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ (K : ℝ) by positivity)
    simp only [one_mul] at hscale
    change _ < (N : ℝ) ^ a
    exact (hmul.trans_eq (by ring)).trans_lt hscale
  refine ⟨p, hp, ?_, hx, ?_⟩
  · exact_mod_cast hK.trans hx
  · calc
      (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpn
      _ ≤ 2 * (Real.exp x + 1) := mul_le_mul_of_nonneg_left
        (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le (by positivity)
      _ ≤ 4 * Real.exp x := by
        have h := Real.one_le_exp (show 0 ≤ x by positivity)
        linarith
      _ = Real.exp (Real.log 4 + x) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change _ ≤ 2 * x
        change Real.log 4 < x at hlog
        linarith

theorem eventually_exists_auxiliary_binary_prime (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ N ^ K < p ∧
      Real.exp ((N : ℝ) ^ (1 / 2 : ℝ)) < (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ (1 / 2 : ℝ)) :=
  eventually_exists_auxiliary_binary_prime_of_rpow K (by norm_num)

/-- A progression matrix of bounded rank, with a fourth-root number of
exceptions and polynomial coefficients, has minors smaller than the auxiliary prime. -/
theorem eventually_binary_progression_minors_lt_exp {C : ℝ} (hC : 0 < C) (D K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (V k : ℕ), (V : ℝ) ≤ C * (N : ℝ) ^ K →
      k ≤ D + (N - binaryInitialLength N) →
      (k.factorial : ℝ) * ((N : ℝ) * (V : ℝ)) ^ k < Real.exp ((N : ℝ) ^ (1 / 2 : ℝ)) := by
  let A := (3 + (D : ℝ)) * (Real.log (C + 1) + 8 * ((K : ℝ) + 2))
  filter_upwards [eventually_ge_atTop 1,
    eventually_scale_rpow_lt (a := 1 / 4) (b := 1) (by norm_num) (3 + (D : ℝ)) (B := 1)
      (by norm_num),
    eventually_scale_rpow_lt (a := 3 / 8) (b := 1 / 2) (by norm_num) A (B := 1)
      (by norm_num)] with N hN hscale hsmall
  intro V k hV hk
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) := zero_lt_one.trans_le hN'
  let x := (N : ℝ) ^ (1 / 4 : ℝ)
  let y := (N : ℝ) ^ (1 / 8 : ℝ)
  have hx : 1 ≤ x := Real.one_le_rpow hN' (by norm_num)
  have hy : 1 ≤ y := Real.one_le_rpow hN' (by norm_num)
  have hkx : (k : ℝ) ≤ (3 + (D : ℝ)) * x := by
    have hcast : (k : ℝ) ≤ (D : ℝ) + ((N - binaryInitialLength N : ℕ) : ℝ) := by exact_mod_cast hk
    have ht := binaryRemainingLength_le_quarter_root hN
    change ((N - binaryInitialLength N : ℕ) : ℝ) ≤ 3 * x at ht
    have hDx := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg D)
    nlinarith
  have hkN : k ≤ N := by
    have hscale' : (3 + (D : ℝ)) * x ≤ (N : ℝ) := by
      simpa only [x, one_mul, Real.rpow_one] using hscale.le
    exact_mod_cast hkx.trans hscale'
  let b := (C + 1) * (N : ℝ) ^ (K + 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 ≤ Real.log (C + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log (N : ℝ) ≤ 8 * y := by
    have h := log_nat_le_rpow (N := N) (a := 1 / 8) (by norm_num)
    change _ ≤ y / _ at h
    linarith
  have hlog : Real.log b ≤ (Real.log (C + 1) + 8 * ((K : ℝ) + 2)) * y := by
    unfold b
    rw [Real.log_mul (by positivity : C + 1 ≠ 0) (by positivity : (N : ℝ) ^ (K + 2) ≠ 0),
      Real.log_pow, Nat.cast_add]
    have h₀ := mul_le_mul_of_nonneg_left hy hc
    have h₁ := mul_le_mul_of_nonneg_left hl (show 0 ≤ (K : ℝ) + 2 by positivity)
    norm_num at *
    nlinarith
  have hlog' : 0 ≤ Real.log b :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hN'))
  have hbsmall : b ^ k < Real.exp ((N : ℝ) ^ (1 / 2 : ℝ)) := by
    apply (Real.log_lt_iff_lt_exp (by positivity)).mp
    rw [Real.log_pow]
    calc
      _ ≤ ((3 + (D : ℝ)) * x) * ((Real.log (C + 1) + 8 * ((K : ℝ) + 2)) * y) :=
        mul_le_mul hkx hlog hlog' (by positivity)
      _ = A * (N : ℝ) ^ (3 / 8 : ℝ) := by
        have hxy : x * y = (N : ℝ) ^ (3 / 8 : ℝ) := by
          dsimp [x, y]
          rw [← Real.rpow_add hp]
          congr 1
          norm_num
        rw [← hxy]
        dsimp [A]
        ring
      _ < _ := by simpa only [one_mul] using hsmall
  have hfact : (k.factorial : ℝ) ≤ (N : ℝ) ^ k := by
    exact_mod_cast (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hkN _)
  calc
    _ ≤ (N : ℝ) ^ k * ((N : ℝ) * (V : ℝ)) ^ k := mul_le_mul_of_nonneg_right hfact (by positivity)
    _ = ((N : ℝ) ^ 2 * (V : ℝ)) ^ k := by rw [← mul_pow]; ring
    _ ≤ b ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      calc
        _ ≤ (N : ℝ) ^ 2 * ((C + 1) * (N : ℝ) ^ K) :=
          mul_le_mul_of_nonneg_left (hV.trans (mul_le_mul_of_nonneg_right (show C ≤ C + 1 by linarith)
            (show 0 ≤ (N : ℝ) ^ K by positivity))) (by positivity)
        _ = b := by unfold b; rw [pow_add]; ring
    _ < _ := hbsmall


/-- The prefactor counting exception sets, generators, and lengths grows
slower than every positive exponential. -/
theorem eventually_binary_progression_prefactor_le_exp {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (D K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p V d : ℕ),
      (p : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ (1 / 2 : ℝ)) →
      (V : ℝ) ≤ C * (N : ℝ) ^ K → d ≤ D →
      (N.choose (N - binaryInitialLength N) : ℝ) * ((V + 1 : ℕ) : ℝ) ^ d *
        (p : ℝ) ^ ((N - binaryInitialLength N) + d) ≤ Real.exp (ε * (N : ℝ)) := by
  let A := 6 + (D : ℝ) * (Real.log (C + 1) + 2 * (K : ℝ)) + 2 * (3 + (D : ℝ))
  filter_upwards [eventually_ge_atTop 1,
    eventually_scale_rpow_lt (a := 3 / 4) (b := 1) (by norm_num) A hε]
    with N hN hsmall
  intro p V d hp hV hd
  let t := N - binaryInitialLength N
  let x := (N : ℝ) ^ (1 / 4 : ℝ)
  let y := (N : ℝ) ^ (1 / 2 : ℝ)
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hN'
  have hx : 1 ≤ x := Real.one_le_rpow hN' (by norm_num)
  have hy : 1 ≤ y := Real.one_le_rpow hN' (by norm_num)
  have hxy : x * y = (N : ℝ) ^ (3 / 4 : ℝ) := by
    dsimp [x, y]
    rw [← Real.rpow_add hNpos]
    congr 1
    norm_num
  have ht : (t : ℝ) ≤ 3 * x := binaryRemainingLength_le_quarter_root hN
  have hd' : (d : ℝ) ≤ (D : ℝ) * x := by
    exact (by exact_mod_cast hd : (d : ℝ) ≤ (D : ℝ)).trans
      (le_mul_of_one_le_right (Nat.cast_nonneg _) hx)
  have htd : (t : ℝ) + (d : ℝ) ≤ (3 + (D : ℝ)) * x := by nlinarith
  have hl : Real.log (N : ℝ) ≤ 2 * y := by
    have h := log_nat_le_rpow (N := N) (a := 1 / 2) (by norm_num)
    change _ ≤ y / _ at h
    linarith
  let b := (C + 1) * (N : ℝ) ^ K
  have hb : 0 < b := by dsimp [b]; positivity
  have hb₁ : 1 ≤ b := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hN')
  have hC' : 0 ≤ Real.log (C + 1) := Real.log_nonneg (by linarith)
  have hlog : Real.log b ≤ (Real.log (C + 1) + 2 * (K : ℝ)) * y := by
    unfold b
    rw [Real.log_mul (by positivity : C + 1 ≠ 0) (by positivity : (N : ℝ) ^ K ≠ 0), Real.log_pow]
    have h₀ := mul_le_mul_of_nonneg_left hy hC'
    have h₁ := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg K : 0 ≤ (K : ℝ))
    nlinarith
  have hV' : ((V + 1 : ℕ) : ℝ) ≤ b := by
    unfold b
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_le_add hV (one_le_pow₀ hN')
  have hchoose : (N.choose t : ℝ) ≤ (N : ℝ) ^ t := by exact_mod_cast Nat.choose_le_pow N t
  have hBound : (N.choose t : ℝ) * ((V + 1 : ℕ) : ℝ) ^ d * (p : ℝ) ^ (t + d) ≤
      Real.exp ((t : ℝ) * Real.log (N : ℝ) + (d : ℝ) * Real.log b +
        ((t : ℝ) + (d : ℝ)) * (2 * y)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hNpos, Real.exp_log hb, ← Nat.cast_add, Real.exp_nat_mul]
    gcongr
  refine hBound.trans (Real.exp_le_exp.mpr ?_)
  have h₁ := mul_le_mul ht hl (Real.log_natCast_nonneg N) (by positivity)
  have h₂ := mul_le_mul hd' hlog (Real.log_nonneg hb₁) (by positivity)
  have h₃ := mul_le_mul_of_nonneg_right htd (show 0 ≤ 2 * y by positivity)
  calc
    _ ≤ (3 * x) * (2 * y) + ((D : ℝ) * x) * ((Real.log (C + 1) + 2 * (K : ℝ)) * y) +
        ((3 + (D : ℝ)) * x) * (2 * y) := add_le_add (add_le_add h₁ h₂) h₃
    _ = A * (N : ℝ) ^ (3 / 4 : ℝ) := by rw [← hxy]; dsimp [A]; ring
    _ ≤ _ := by simpa only [Real.rpow_one] using hsmall.le

/-- The number of primes below the auxiliary prime has smaller growth
than any positive exponential. -/
theorem eventually_auxiliary_prime_add_one_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
      (p : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ (1 / 2 : ℝ)) →
      (p : ℝ) + 1 ≤ Real.exp (ε * (N : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_scale_rpow_lt (a := 1 / 2) (b := 1) (by norm_num) (2 + Real.log 2) hε]
    with N hN hs
  intro p hp
  let x := (N : ℝ) ^ (1 / 2 : ℝ)
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : 1 ≤ x := Real.one_le_rpow hN' (by norm_num)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    (p : ℝ) + 1 ≤ Real.exp (2 * x) + 1 := add_le_add hp le_rfl
    _ ≤ 2 * Real.exp (2 * x) := by
      have h := Real.one_le_exp (show 0 ≤ 2 * x by positivity)
      linarith
    _ = Real.exp (Real.log 2 + 2 * x) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp ((2 + Real.log 2) * x) := by
      have hm := mul_le_mul_of_nonneg_left hx hlog
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      simpa only [Real.rpow_one] using hs.le

theorem exists_geometric_bucket {u x : ℝ} (J : ℕ) (hu : u ^ J < x) (hx : x ≤ 1) :
    ∃ j : Fin J, u ^ (j.val + 1) < x ∧ x ≤ u ^ j.val := by
  let h : ∃ k : ℕ, u ^ k < x := ⟨J, hu⟩
  let k := Nat.find h
  have hk : u ^ k < x := Nat.find_spec h
  have hkn : k ≤ J := Nat.find_min' h hu
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact (not_lt_of_ge hx) hk
  let j := k - 1
  have hj : j + 1 = k := Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)
  have hlt : j < k := by omega
  refine ⟨⟨j, by omega⟩, ?_, ?_⟩
  · change u ^ (j + 1) < x
    rwa [hj]
  · exact le_of_not_gt (Nat.find_min h hlt)

@[expose] noncomputable def binaryAtomRatio (N : ℕ) : ℝ := 1 / (N : ℝ) ^ (1 / 16 : ℝ)

theorem binaryAtomRatio_pos {N : ℕ} (hN : 0 < N) : 0 < binaryAtomRatio N := by
  unfold binaryAtomRatio
  positivity

theorem binaryAtomRatio_le_one {N : ℕ} (hN : 1 ≤ N) : binaryAtomRatio N ≤ 1 := by
  unfold binaryAtomRatio
  exact div_le_one_of_le₀ (Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)) (by positivity)

theorem binaryAtomRatio_pow_eq_lowest (N : ℕ) :
    binaryAtomRatio N ^ (16 * 104) = 1 / (N : ℝ) ^ 104 := by
  unfold binaryAtomRatio
  rw [div_pow, one_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
  norm_num [Real.rpow_natCast]

end BooleanThreshold
