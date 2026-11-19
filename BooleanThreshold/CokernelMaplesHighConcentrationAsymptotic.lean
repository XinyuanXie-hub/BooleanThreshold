module

public import BooleanThreshold.CokernelMaplesHighConcentration
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds

public section

open Filter Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Classical

namespace BooleanThreshold

private theorem eventually_log_pow_le (j : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ j ≤ c * (n : ℝ) := by
  have he := (Real.isLittleO_pow_log_id_atTop (n := j)).bound hc
  filter_upwards [eventually_ge_atTop 1, tendsto_natCast_atTop_atTop.eventually he] with n hn hh
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.log_nonneg hx) j),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hh

private theorem eventually_maples_alphabet_parameters {L : ℝ} (hL : 0 ≤ L) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ ∃ k t s : ℕ, ∃ M : ℝ,
      768 ≤ k ∧ t ≤ n / 128 ∧ ⌈L * Real.log (n : ℝ)⌉₊ ≤ t ∧
      2 * M ≤ (1 / (256 * (k : ℝ) ^ 2)) * t ∧
      (n : ℝ) ^ (B * (s + t) + t + 1) ≤ 2 ^ n ∧ (n : ℝ) ^ B ≤ 2 ^ n ∧
      ∀ r : ℕ, 0 < r → r ≤ n ^ B →
        Real.exp (-M) ≤ 1 / (r : ℝ) ∧
        2 * (r : ℝ) * Real.exp (-(s : ℝ) / (128 * (k : ℝ) ^ 2)) < 1 := by
  let C := B * (512 * (B + 1) + 1) + 1
  let K := max (max 768 (1024 * (B + 1))) ⌈2 * L⌉₊
  have hK : ∀ᶠ n : ℕ in atTop, (K : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop 1, hK, eventually_log_pow_le 4 (by norm_num : (0 : ℝ) < 1 / 128),
    eventually_log_pow_le 5 (div_pos hlog2 (by positivity : (0 : ℝ) < (C : ℝ) + 1))]
    with n hn hlogK ht' hpref
  let x := Real.log (n : ℝ)
  let k := ⌊x⌋₊
  let t := k ^ 4
  let s := 512 * (B + 1) * t
  let M := ((B : ℝ) + 1) * x
  have hkK : K ≤ k := Nat.le_floor hlogK
  have hk₀ : 768 ≤ k := ((le_max_left _ _).trans (le_max_left _ _)).trans hkK
  have hk₁ : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk₁
  have hkpos : 0 < (k : ℝ) := zero_lt_one.trans_le hkR
  have hkB : 1024 * (B + 1) ≤ k := ((le_max_right _ _).trans (le_max_left _ _)).trans hkK
  have hkBR : 1024 * ((B : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hkB
  have hx₀ : 0 ≤ x := Real.log_nonneg (by exact_mod_cast hn)
  have hxlo : (k : ℝ) ≤ x := Nat.floor_le hx₀
  have hxhi : x ≤ 2 * (k : ℝ) := by linarith [Nat.lt_floor_add_one x]
  have hx₁ : 1 ≤ x := hkR.trans hxlo
  have htR : (t : ℝ) ≤ x ^ 4 := by
    exact (Nat.cast_pow _ _).le.trans (pow_le_pow_left₀ hkpos.le hxlo _)
  have ht : t ≤ n / 128 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    have h : (t : ℝ) ≤ (n : ℝ) / 128 :=
      htR.trans (by simpa only [x, div_eq_mul_inv, one_mul, mul_comm] using ht')
    exact_mod_cast ((le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).mp h)
  have hLk : 2 * L ≤ (k : ℝ) := by
    have hceil : ⌈2 * L⌉₊ ≤ k := (le_max_right _ _).trans hkK
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hkpow : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hkR (show 1 ≤ (3 : ℕ) by decide)
  have hsuf : ⌈L * Real.log (n : ℝ)⌉₊ ≤ t := by
    apply Nat.ceil_le.mpr
    calc
      _ ≤ L * (2 * (k : ℝ)) := mul_le_mul_of_nonneg_left hxhi hL
      _ = (2 * L) * (k : ℝ) := by ring
      _ ≤ (k : ℝ) * (k : ℝ) := mul_le_mul_of_nonneg_right hLk hkpos.le
      _ ≤ (k : ℝ) ^ 3 * (k : ℝ) := mul_le_mul_of_nonneg_right hkpow hkpos.le
      _ = _ := by dsimp [t]; push_cast; ring
  have hM : 2 * M ≤ (1 / (256 * (k : ℝ) ^ 2)) * t := by
    calc
      _ ≤ (2 * ((B : ℝ) + 1)) * (2 * (k : ℝ)) := by
        dsimp [M]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hxhi (by positivity : 0 ≤ 2 * ((B : ℝ) + 1))
      _ ≤ (k : ℝ) ^ 2 / 256 := by
        nlinarith only [mul_le_mul_of_nonneg_right hkBR hkpos.le]
      _ = _ := by dsimp [t]; push_cast; field_simp
  have hexponent : B * (s + t) + t + 1 = C * t + 1 := by dsimp [C, s]; ring
  have hrealExp : ((B * (s + t) + t + 1 : ℕ) : ℝ) ≤ ((C : ℝ) + 1) * x ^ 4 := by
    rw [hexponent]
    push_cast
    have hx₄ : 1 ≤ x ^ 4 := one_le_pow₀ hx₁
    have h := mul_le_mul_of_nonneg_left htR (Nat.cast_nonneg (α := ℝ) C)
    linarith
  have hprefR : ((B * (s + t) + t + 1 : ℕ) : ℝ) * x ≤ Real.log 2 * (n : ℝ) := by
    calc
      _ ≤ (((C : ℝ) + 1) * x ^ 4) * x := mul_le_mul_of_nonneg_right hrealExp hx₀
      _ = ((C : ℝ) + 1) * x ^ 5 := by ring
      _ ≤ ((C : ℝ) + 1) * (Real.log 2 / ((C : ℝ) + 1) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hpref (by positivity)
      _ = _ := by field_simp
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hPref : (n : ℝ) ^ (B * (s + t) + t + 1) ≤ 2 ^ n := by
    calc
      _ = Real.exp (((B * (s + t) + t + 1 : ℕ) : ℝ) * x) := by
        rw [Real.exp_nat_mul, Real.exp_log hnpos]
      _ ≤ Real.exp (Real.log 2 * (n : ℝ)) := Real.exp_le_exp.mpr hprefR
      _ = _ := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hBcap : (n : ℝ) ^ B ≤ 2 ^ n := by
    have ht₁ : 1 ≤ t := by dsimp [t]; exact one_le_pow_of_one_le' hk₁ _
    have hBsub : B ≤ B * (s + t) := by
      simpa only [mul_one] using Nat.mul_le_mul_left B (show 1 ≤ s + t by omega)
    exact (pow_le_pow_right₀ hnR (show B ≤ B * (s + t) + t + 1 by omega)).trans hPref
  refine ⟨hn, k, t, s, M, hk₀, ht, hsuf, hM, hPref, hBcap, fun r hr hrn => ?_⟩
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hlogr : Real.log (r : ℝ) ≤ (B : ℝ) * x := by
    rw [← Real.log_pow]
    exact Real.log_le_log hrR (by exact_mod_cast hrn)
  refine ⟨?_, ?_⟩
  · calc
      Real.exp (-M) ≤ Real.exp (-Real.log (r : ℝ)) := by
        apply Real.exp_le_exp.mpr
        dsimp [M]
        linarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log hrR, inv_eq_one_div]
  · have hsR : (s : ℝ) / (128 * (k : ℝ) ^ 2) = 4 * ((B : ℝ) + 1) * (k : ℝ) ^ 2 := by
      dsimp [s, t]
      push_cast
      field_simp
      ring
    have hlog2' : Real.log 2 < 1 :=
      (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two
    have hkSq : (k : ℝ) < 2 * (k : ℝ) ^ 2 := by
      have h : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        simpa only [pow_one] using pow_le_pow_right₀ hkR (show 1 ≤ (2 : ℕ) by decide)
      nlinarith only [h, hkpos]
    have hbound : Real.log (2 * (r : ℝ)) < (s : ℝ) / (128 * (k : ℝ) ^ 2) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hrR.ne', hsR]
      calc
        _ ≤ 2 * ((B : ℝ) + 1) * (k : ℝ) := by
          linarith [hlog2', hlogr, mul_le_mul_of_nonneg_left hxhi (Nat.cast_nonneg (α := ℝ) B), hkR]
        _ < _ := by
          have h := mul_lt_mul_of_pos_left hkSq (show 0 < 2 * ((B : ℝ) + 1) by positivity)
          linarith
    rw [← Real.exp_log (show 0 < 2 * (r : ℝ) by positivity), ← Real.exp_add, Real.exp_lt_one_iff]
    simpa only [neg_div, sub_eq_add_neg] using sub_neg.mpr hbound

private theorem exists_doubling_interval {n : ℕ} (hn : 1 ≤ n) {ρ x : ℝ}
    (hlo : ρ ≤ x) (hhi : x ≤ 2 ^ n * ρ) :
    ∃ j : Fin n, 2 ^ j.val * ρ ≤ x ∧ x ≤ 2 * (2 ^ j.val * ρ) := by
  let h : ∃ j : ℕ, x ≤ (2 : ℝ) ^ (j + 1) * ρ :=
    ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩
  let j := Nat.find h
  have hj : j ≤ n - 1 := Nat.find_min' h (by rwa [Nat.sub_add_cancel hn])
  have hjlo : 2 ^ j * ρ ≤ x := by
    by_cases hzero : j = 0
    · simpa [hzero] using hlo
    · exact le_of_lt (lt_of_not_ge (by
        have hmin := Nat.find_min h (show j - 1 < j by omega)
        rwa [Nat.sub_add_cancel (show 1 ≤ j by omega)] at hmin))
  refine ⟨⟨j, by omega⟩, hjlo, ?_⟩
  have hupper := Nat.find_spec h
  change x ≤ (2 : ℝ) ^ (j + 1) * ρ at hupper
  simpa only [pow_succ, mul_left_comm, mul_assoc] using hupper

/-- High annihilation probability of a dense cyclic normal is exponentially
unlikely, uniformly over all polynomially bounded moduli. -/
theorem maples_high_concentration_exclusion {L : ℝ} (hL : 0 ≤ L) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (r : ℕ) [NeZero r], r ≤ n ^ B →
      (uniformOn Set.univ).real {R : Fin (n - ⌈L * Real.log (n : ℝ)⌉₊) → Fin n → Bool |
        ∃ a : Fin n → ZMod r, DenseCyclicNormal a ∧ 16 / (r : ℝ) < binaryZeroAtom a ∧
          ∀ i, a ⬝ᵥ binaryColumn (ZMod r) (R i) = 0} ≤ (1 / 2 : ℝ) ^ n := by
  filter_upwards [eventually_maples_alphabet_parameters hL B] with n hp
  obtain ⟨hn, k, t, s, M, hk, ht, hsuf, hM, hPref, hBcap, hratom⟩ := hp
  intro r _ hrn
  let m := n - ⌈L * Real.log (n : ℝ)⌉₊
  let ρ (j : Fin n) := (2 : ℝ) ^ j.val * (16 / (r : ℝ))
  let q (j : Fin n) := min (2 * ρ j) 1
  let E (j : Fin n) : Set (Fin m → Fin n → Bool) :=
    {R | ∃ a : Fin n → ZMod r, DenseCyclicNormal a ∧ ρ j ≤ binaryZeroAtom a ∧
      binaryZeroAtom a ≤ q j ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod r) (R i) = 0}
  let μ : Measure (Fin m → Fin n → Bool) := uniformOn Set.univ
  have hr : 0 < r := NeZero.pos r
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hcR : (768 : ℝ) ≤ k := by exact_mod_cast hk
  have hrle : (r : ℝ) ≤ (n : ℝ) ^ B := by exact_mod_cast hrn
  have hm : n - t ≤ m := Nat.sub_le_sub_left hsuf n
  have hρ (j : Fin n) : 0 < ρ j := by dsimp [ρ]; positivity
  have hq (j : Fin n) : 0 ≤ q j := le_min (by dsimp [ρ]; positivity) zero_le_one
  have hrρ (j : Fin n) : (r : ℝ) * ρ j = (2 : ℝ) ^ j.val * 16 := by
    dsimp [ρ]
    field_simp
  have hρone (j : Fin n) : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
  have hcut (j : Fin n) : Real.exp (-M) ≤ ρ j / 2 := by
    refine (hratom r hr hrn).1.trans ?_
    rw [div_le_iff₀ hrR]
    have h16 : (16 : ℝ) ≤ (r : ℝ) * ρ j := by
      rw [hrρ]
      exact le_mul_of_one_le_left (by norm_num) (hρone j)
    nlinarith only [h16]
  have hsub : {R : Fin m → Fin n → Bool | ∃ a : Fin n → ZMod r, DenseCyclicNormal a ∧
      16 / (r : ℝ) < binaryZeroAtom a ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod r) (R i) = 0} ⊆
      ⋃ j : Fin n, E j := by
    rintro R ⟨a, hdense, ha, hz⟩
    have hAtom : binaryZeroAtom a ≤ 1 := measureReal_le_one
    have hupper : (1 : ℝ) ≤ 2 ^ n * (16 / (r : ℝ)) := by
      rw [← mul_div_assoc, le_div_iff₀ hrR, one_mul]
      exact (hrle.trans hBcap).trans (le_mul_of_one_le_right (by positivity) (by norm_num))
    obtain ⟨j, hj₁, hj₂⟩ := exists_doubling_interval hn ha.le (hAtom.trans hupper)
    exact Set.mem_iUnion.mpr ⟨j, a, hdense, hj₁, le_min hj₂ hAtom, hz⟩
  have hE (j : Fin n) : μ.real (E j) ≤
      (n : ℝ) ^ (B * (s + t) + t) * (1 / 4 : ℝ) ^ n := by
    have hlarge : 8 < (r : ℝ) * ρ j := by
      rw [hrρ]
      linarith [hρone j]
    have h :=
      sampled_dense_cyclic_annihilation_mass_le (m := m) (hρ j) (hq j) ht (by omega : 0 < k)
        hM (hcut j) hlarge (hratom r hr hrn).2
    let V := 24 / (ρ j * (k : ℝ))
    have hV : 0 ≤ V := by dsimp [V]; positivity
    have hVq : V * q j ≤ 1 / 16 := by
      calc
        _ ≤ V * (2 * ρ j) := mul_le_mul_of_nonneg_left (min_le_left _ _) hV
        _ = 48 / (k : ℝ) := by
          dsimp [V]
          field_simp [(hρ j).ne', hkR.ne']
          ring
        _ ≤ _ := by apply (div_le_iff₀ hkR).mpr; linarith
    have hpower : V ^ (n - t) * q j ^ m ≤ (1 / 4 : ℝ) ^ n := by
      have hnt : n ≤ 2 * (n - t) := by omega
      calc
        _ ≤ V ^ (n - t) * q j ^ (n - t) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (hq j) (min_le_right _ _) hm) (by positivity)
        _ = (V * q j) ^ (n - t) := (mul_pow ..).symm
        _ ≤ (1 / 16 : ℝ) ^ (n - t) := pow_le_pow_left₀ (mul_nonneg hV (hq j)) hVq _
        _ = (1 / 4 : ℝ) ^ (2 * (n - t)) := by rw [pow_mul]; norm_num
        _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hnt
    have hfactor : (r : ℝ) ^ s * (n.choose t : ℝ) * (r : ℝ) ^ t ≤ (n : ℝ) ^ (B * (s + t) + t) := by
      rw [mul_right_comm, ← pow_add]
      calc
        _ ≤ ((n : ℝ) ^ B) ^ (s + t) * (n : ℝ) ^ t :=
          mul_le_mul (pow_le_pow_left₀ hrR.le hrle _)
            (by exact_mod_cast Nat.choose_le_pow n t) (by positivity) (by positivity)
        _ = _ := by rw [← pow_mul, ← pow_add]
    calc
      _ ≤ ((r : ℝ) ^ s * (n.choose t : ℝ) * (r : ℝ) ^ t) *
          (V ^ (n - t) * q j ^ m) := by simpa only [E, μ, V, mul_assoc] using h
      _ ≤ _ := mul_le_mul hfactor hpower (by positivity) (by positivity)
  calc
    _ ≤ μ.real (⋃ j : Fin n, E j) := measureReal_mono hsub
    _ ≤ ∑ j : Fin n, μ.real (E j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin n, (n : ℝ) ^ (B * (s + t) + t) * (1 / 4 : ℝ) ^ n := sum_le_sum fun j _ => hE j
    _ = (n : ℝ) ^ (B * (s + t) + t + 1) * (1 / 4 : ℝ) ^ n := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
      ring
    _ ≤ (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := mul_le_mul_of_nonneg_right hPref (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

end BooleanThreshold
