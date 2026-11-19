module

public import BooleanThreshold.CokernelLargeParameters
public import Mathlib.Analysis.Complex.ExponentialBounds

public section

open Filter

namespace BooleanThreshold

/-- A fixed upper bound for the rank of the bounded-height expansion. -/
abbrev binaryExpansionRank : ℕ := 1260

/-- Parameters for the Fourier sampling and finite-field transfer estimates. -/
structure BinaryDirectParameters (N K : ℕ) (ε : ℝ) where
  prime : ℕ
  sumLength : ℕ
  height : ℕ
  sampleLength : ℕ
  level : ℝ
  prime_prime : prime.Prime
  cutoff_lt_prime : N ^ K < prime
  sumLength_pos : 0 < sumLength
  rank_mul_height_le : binaryExpansionRank * height ≤ sumLength
  height_le_size : height ≤ N
  exp_neg_level_le : Real.exp (-level) ≤ (1 / (N : ℝ) ^ 104) / 2
  energy_budget : 2 * level ≤ (1 / (256 * (sumLength : ℝ) ^ 2)) * (N - binaryInitialLength N : ℕ)
  sumset_size_lt : 8 * (N : ℝ) ^ 104 < ((height : ℝ) + 1) ^ binaryExpansionRank
  alphabet_ratio : 8 * (N : ℝ) ^ (1 / 16 : ℝ) ≤ (sumLength : ℝ) / 4
  sample_weight_lt : ∀ p ≤ prime, 2 * (p : ℝ) *
    Real.exp (-(sampleLength : ℝ) / (128 * (sumLength : ℝ) ^ 2)) < 1
  sample_count_le : ∀ p ≤ prime, (N.choose (N - binaryInitialLength N) : ℝ) *
    (p : ℝ) ^ ((N - binaryInitialLength N) + sampleLength) ≤ Real.exp (ε * (N : ℝ))
  prime_count_le : (prime : ℝ) ≤ Real.exp (ε * (N : ℝ))
  minor_lt : ∀ r ≤ binaryExpansionRank + (N - binaryInitialLength N),
    (r.factorial : ℤ) * ((N : ℤ) * (height.factorial * (height + 1) : ℕ)) ^ r < (prime : ℤ)

/-- With `x = N^(1/48)`, the sumset length grows as `x^4`, the log of the
auxiliary prime as `x^18`, and the sample count has log of order at most `x^44`.
The integer minors have log of order at most `x^17`. -/
theorem eventually_binaryDirectParameters (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Nonempty (BinaryDirectParameters N K ε) := by
  let D : ℕ := binaryExpansionRank
  let cE : ℝ := 256 * 210 * 48 * (D : ℝ) ^ 2
  let cMinor : ℝ := (D + 3 : ℝ) * 194
  let cCount : ℝ := 152 + 2048 * (D : ℝ) ^ 2
  have hroot : (0 : ℝ) < 1 / 48 := by norm_num
  filter_upwards [eventually_ge_atTop 9, eventually_ge_atTop (2 * D),
    eventually_binaryInitialLength_half, eventually_exists_auxiliary_binary_prime_of_rpow K
      (a := 3 / 8) (by norm_num),
    eventually_constant_lt_nat_rpow hroot 32,
    eventually_constant_lt_nat_rpow hroot cE,
    eventually_constant_lt_nat_rpow hroot cMinor,
    eventually_constant_lt_nat_rpow hroot (cCount / ε)]
    with N hN hND hhalf hprime hx32 hxE hxMinor hxCount
  obtain ⟨p₀, hp₀, hcut, hp₀lo, hp₀hi⟩ := hprime
  let x := (N : ℝ) ^ (1 / 48 : ℝ)
  let H := ⌊x ^ 4⌋₊
  let k := D * H
  let L := ⌈512 * (k : ℝ) ^ 2 * (1 + x ^ 18)⌉₊
  let V := H.factorial * (H + 1)
  let M := 105 * Real.log (N : ℝ)
  let t := N - binaryInitialLength N
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hx : 1 ≤ x := Real.one_le_rpow hN₁ (by norm_num)
  have hxp (j : ℕ) : x ^ j = (N : ℝ) ^ ((j : ℝ) / 48) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    congr 1
    ring
  have hx48 : x ^ 48 = (N : ℝ) := by simpa using hxp 48
  have hx12 : x ^ 12 = (N : ℝ) ^ (1 / 4 : ℝ) := by
    convert hxp 12 using 2
    norm_num
  have hx18 : x ^ 18 = (N : ℝ) ^ (3 / 8 : ℝ) := by
    convert hxp 18 using 2
    norm_num
  have hx3 : x ^ 3 = (N : ℝ) ^ (1 / 16 : ℝ) := by
    convert hxp 3 using 2
    norm_num
  have hxpow (j : ℕ) : 1 ≤ x ^ j := one_le_pow₀ hx
  have hmono {i j : ℕ} (hij : i ≤ j) : x ^ i ≤ x ^ j := pow_le_pow_right₀ hx hij
  have hlN : Real.log (N : ℝ) ≤ 48 * x := by
    have h := Real.log_le_rpow_div (Nat.cast_nonneg N) hroot
    change Real.log (N : ℝ) ≤ x / (1 / 48) at h
    linarith
  have htlo : 2 * x ^ 12 ≤ (t : ℝ) := by
    let u := ⌈2 * (N : ℝ) ^ (1 / 4 : ℝ)⌉₊
    have hu : u ≤ N := by
      change N ≤ 2 * (N - u) at hhalf
      omega
    have ht : t = u := Nat.sub_sub_self hu
    rw [ht, hx12]
    exact Nat.le_ceil _
  have hthi : (t : ℝ) ≤ 3 * x ^ 12 := by
    rw [hx12]
    exact binaryRemainingLength_le_quarter_root (by omega)
  have hHle : (H : ℝ) ≤ x ^ 4 := Nat.floor_le (by positivity)
  have hHge : x ^ 4 < (H : ℝ) + 1 := Nat.lt_floor_add_one _
  have hH₁ : 1 ≤ H := Nat.le_floor (by simpa using hxpow 4)
  have hHleN : H ≤ N := by exact_mod_cast hHle.trans ((hmono (show 4 ≤ 48 by decide)).trans_eq hx48)
  have hD₂ : 2 ≤ D := by decide
  have hk₀ : 0 < k := Nat.mul_pos (by omega) (by omega)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk₀
  have hkUpper : (k : ℝ) ≤ (D : ℝ) * x ^ 4 := by
    simpa only [k, Nat.cast_mul] using mul_le_mul_of_nonneg_left hHle (Nat.cast_nonneg D)
  have hkLower : x ^ 4 ≤ (k : ℝ) := by
    have h : H + 1 ≤ k := calc
      _ ≤ 2 * H := by omega
      _ ≤ _ := Nat.mul_le_mul_right H hD₂
    exact hHge.le.trans (by exact_mod_cast h)
  have hpLo : Real.exp (x ^ 18) < (p₀ : ℝ) := by rwa [hx18]
  have hpHi : (p₀ : ℝ) ≤ Real.exp (2 * x ^ 18) := by rwa [hx18]
  have hCCount : cCount < ε * x := by
    have h := (div_lt_iff₀ hε).mp hxCount
    simpa only [mul_comm] using h
  have hFinalExp : cCount * x ^ 44 ≤ ε * (N : ℝ) := by
    calc
      _ ≤ (ε * x) * x ^ 44 := mul_le_mul_of_nonneg_right hCCount.le (by positivity)
      _ = ε * x ^ 45 := by ring
      _ ≤ ε * x ^ 48 := mul_le_mul_of_nonneg_left (hmono (by decide)) hε.le
      _ = _ := by rw [hx48]
  refine ⟨⟨p₀, k, H, L, M, hp₀, hcut, hk₀, le_rfl, hHleN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have hExp : Real.exp (-M) = 1 / (N : ℝ) ^ 105 := by
      rw [show -M = -((105 : ℕ) * Real.log (N : ℝ)) by rfl,
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log hNpos, one_div]
    rw [hExp, div_div, show (105 : ℕ) = 104 + 1 by decide, pow_succ]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast (show 2 ≤ N by omega)) (by positivity))
  · have hM : 2 * M ≤ (210 * 48) * x := by dsimp [M]; linarith
    have hkSq : (k : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 * x ^ 8 := by
      calc
        _ ≤ ((D : ℝ) * x ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hkUpper _
        _ = _ := by ring
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    change 2 * M * (256 * (k : ℝ) ^ 2) ≤ (t : ℝ)
    calc
      _ ≤ ((210 * 48) * x) * (256 * ((D : ℝ) ^ 2 * x ^ 8)) := by gcongr
      _ = cE * x ^ 9 := by dsimp [cE]; ring
      _ ≤ x * x ^ 9 := mul_le_mul_of_nonneg_right hxE.le (by positivity)
      _ = x ^ 10 := by ring
      _ ≤ 2 * x ^ 12 := (hmono (by decide)).trans (le_mul_of_one_le_left (by positivity) (by norm_num))
      _ ≤ _ := htlo
  · calc
      _ < (N : ℝ) ^ 105 := by
        rw [show (105 : ℕ) = 104 + 1 by decide, pow_succ, mul_comm 8]
        exact mul_lt_mul_of_pos_left (by exact_mod_cast (show 8 < N by omega)) (by positivity)
      _ = (x ^ 4) ^ binaryExpansionRank := by
        rw [← hx48, ← pow_mul, ← pow_mul]
        rfl
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hHge.le _
  · rw [← hx3]
    apply le_div_iff₀ (by norm_num) |>.mpr
    calc
      _ = 32 * x ^ 3 := by ring
      _ ≤ x * x ^ 3 := mul_le_mul_of_nonneg_right hx32.le (by positivity)
      _ = x ^ 4 := by ring
      _ ≤ _ := hkLower
  · intro p hp
    have hPL : (4 : ℝ) * (1 + x ^ 18) ≤ (L : ℝ) / (128 * (k : ℝ) ^ 2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have h := Nat.le_ceil (512 * (k : ℝ) ^ 2 * (1 + x ^ 18))
      exact (show 4 * (1 + x ^ 18) * (128 * (k : ℝ) ^ 2) =
          512 * (k : ℝ) ^ 2 * (1 + x ^ 18) by ring).le.trans h
    have hP : (p : ℝ) ≤ Real.exp (2 * x ^ 18) :=
      (show (p : ℝ) ≤ p₀ by exact_mod_cast hp).trans hpHi
    calc
      _ ≤ 2 * Real.exp (2 * x ^ 18) * Real.exp (-(4 * (1 + x ^ 18))) := by
        rw [neg_div]
        gcongr
      _ = 2 * Real.exp (2 * x ^ 18 - 4 * (1 + x ^ 18)) := by
        rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
      _ ≤ 2 * Real.exp (-4) := by gcongr; linarith [hxpow 18]
      _ < 1 := by
        rw [Real.exp_neg]
        have h : 2 < Real.exp 4 := lt_of_lt_of_le (by norm_num) (Real.add_one_le_exp 4)
        simpa only [div_eq_mul_inv] using (div_lt_one (Real.exp_pos 4)).mpr h
  · intro p hp
    have hL : (L : ℝ) ≤ (1024 * (D : ℝ) ^ 2 + 1) * x ^ 26 := by
      calc
        _ ≤ 512 * (k : ℝ) ^ 2 * (1 + x ^ 18) + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).le
        _ ≤ 512 * ((D : ℝ) * x ^ 4) ^ 2 * (2 * x ^ 18) + x ^ 26 := by
          gcongr
          · linarith [hxpow 18]
          · exact hxpow 26
        _ = _ := by ring
    have hP : (p : ℝ) ≤ Real.exp (2 * x ^ 18) :=
      (show (p : ℝ) ≤ p₀ by exact_mod_cast hp).trans hpHi
    have hchoose : (N.choose t : ℝ) ≤ (N : ℝ) ^ t := by exact_mod_cast Nat.choose_le_pow N t
    calc
      _ ≤ (N : ℝ) ^ t * Real.exp (2 * x ^ 18) ^ (t + L) := by gcongr
      _ = Real.exp (((t : ℝ) * Real.log (N : ℝ)) + ((t : ℝ) + L) * (2 * x ^ 18)) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hNpos, ← Nat.cast_add, Real.exp_nat_mul]
      _ ≤ Real.exp (cCount * x ^ 44) := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ 3 * x ^ 12 * (48 * x) +
              (3 * x ^ 12 + (1024 * (D : ℝ) ^ 2 + 1) * x ^ 26) * (2 * x ^ 18) := by gcongr
          _ = 144 * x ^ 13 + 6 * x ^ 30 + (2048 * (D : ℝ) ^ 2 + 2) * x ^ 44 := by ring
          _ ≤ 144 * x ^ 44 + 6 * x ^ 44 + (2048 * (D : ℝ) ^ 2 + 2) * x ^ 44 := by gcongr <;> decide
          _ = _ := by dsimp [cCount]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hFinalExp
  · refine hpHi.trans (Real.exp_le_exp.mpr ?_)
    refine le_trans ?_ hFinalExp
    have hC : 2 ≤ cCount := by dsimp [cCount]; nlinarith [sq_nonneg (D : ℝ)]
    exact mul_le_mul hC (hmono (by decide)) (by positivity) (by positivity)
  · intro r hr
    have hrcast : (r : ℝ) ≤ (D : ℝ) + (t : ℝ) := by exact_mod_cast hr
    have hrN : r ≤ N := by
      have hm := binaryInitialLength_le N
      change r ≤ D + (N - binaryInitialLength N) at hr
      omega
    have hrCast : (r : ℝ) ≤ (D + 3 : ℝ) * x ^ 12 := by
      have hd₁ := mul_le_mul_of_nonneg_left (hxpow 12) (Nat.cast_nonneg D : 0 ≤ (D : ℝ))
      nlinarith
    have hVpos : 0 < (V : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.factorial_pos H) (Nat.succ_pos H)
    have hV : (V : ℝ) ≤ ((H : ℝ) + 1) ^ (H + 1) := by
      have h : V ≤ (H + 1) ^ (H + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ ((Nat.factorial_le_pow H).trans (Nat.pow_le_pow_left (by omega) _))
      exact_mod_cast h
    have hH₂ : (H : ℝ) + 1 ≤ 2 * x ^ 4 := by linarith [hxpow 4]
    have hlogH : Real.log ((H : ℝ) + 1) ≤ 49 * x := by
      have h : (H : ℝ) + 1 ≤ 2 * (N : ℝ) := by
        have hh : (H : ℝ) ≤ N := by exact_mod_cast hHleN
        linarith
      calc
        _ ≤ Real.log (2 * (N : ℝ)) := Real.log_le_log (by positivity) h
        _ = Real.log 2 + Real.log (N : ℝ) := Real.log_mul (by norm_num) hNpos.ne'
        _ ≤ _ := by
          have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_iff_le_exp (by norm_num)).mpr Real.exp_one_gt_two.le
          linarith
    have hlogV : Real.log (V : ℝ) ≤ 98 * x ^ 5 := calc
      _ ≤ Real.log (((H : ℝ) + 1) ^ (H + 1)) := Real.log_le_log hVpos hV
      _ = ((H : ℝ) + 1) * Real.log ((H : ℝ) + 1) := by rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
      _ ≤ (2 * x ^ 4) * (49 * x) :=
        mul_le_mul hH₂ hlogH (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg H))) (by positivity)
      _ = _ := by ring
    have hlog : Real.log ((N : ℝ) ^ 2 * (V : ℝ)) ≤ 194 * x ^ 5 := by
      rw [Real.log_mul (by positivity) hVpos.ne', Real.log_pow]
      have hx₅ : x ≤ x ^ 5 := by simpa using hmono (i := 1) (j := 5) (by decide)
      norm_num at ⊢
      linarith
    have hfac : (r.factorial : ℝ) ≤ (N : ℝ) ^ r := by
      exact_mod_cast (Nat.factorial_le_pow r).trans (Nat.pow_le_pow_left hrN _)
    have hR : (r.factorial : ℝ) * ((N : ℝ) * (V : ℝ)) ^ r < (p₀ : ℝ) := calc
      _ ≤ (N : ℝ) ^ r * ((N : ℝ) * (V : ℝ)) ^ r := mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = ((N : ℝ) ^ 2 * (V : ℝ)) ^ r := by rw [← mul_pow]; ring
      _ < Real.exp (x ^ 18) := by
        apply (Real.log_lt_iff_lt_exp (by positivity)).mp
        rw [Real.log_pow]
        have hlogNonneg : 0 ≤ Real.log ((N : ℝ) ^ 2 * (V : ℝ)) := by
          have hv : 1 ≤ (V : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (Nat.factorial_pos H) (Nat.succ_pos H))
          exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN₁) hv)
        calc
          _ ≤ ((D + 3 : ℝ) * x ^ 12) * (194 * x ^ 5) :=
            mul_le_mul hrCast hlog hlogNonneg (by positivity)
          _ = cMinor * x ^ 17 := by dsimp [cMinor]; ring
          _ < x * x ^ 17 := mul_lt_mul_of_pos_right hxMinor (by positivity)
          _ = _ := by ring
      _ < _ := hpLo
    exact_mod_cast hR

end BooleanThreshold
