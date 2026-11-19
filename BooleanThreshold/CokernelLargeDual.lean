module

public import BooleanThreshold.KKSLargeRadius
import Mathlib.Data.Fintype.EquivFin

public section

open Finset AddChar Complex
open scoped BigOperators Pointwise Classical

namespace BooleanThreshold

/-- The mean character defect of a field element against a set of frequencies. -/
@[expose] noncomputable def dualMeanDefect {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (c : ZMod p) : ℝ :=
  (∑ s ∈ S, (1 - (ZMod.stdAddChar (c * s)).re) / 2) / S.card

theorem characterDefect_nonneg {p : ℕ} [NeZero p] (c : ZMod p) :
    0 ≤ (1 - (ZMod.stdAddChar c).re) / 2 := by
  have h := Complex.re_le_norm (ZMod.stdAddChar c)
  rw [norm_standard_character] at h
  linarith

theorem characterDefect_le_one {p : ℕ} [NeZero p] (c : ZMod p) :
    (1 - (ZMod.stdAddChar c).re) / 2 ≤ 1 := by
  have h := Complex.abs_re_le_norm (ZMod.stdAddChar c)
  rw [norm_standard_character, abs_le] at h
  linarith only [h.1]

theorem dualMeanDefect_nonneg {p : ℕ} [NeZero p] (S : Finset (ZMod p)) (c : ZMod p) :
    0 ≤ dualMeanDefect S c :=
  div_nonneg (sum_nonneg fun s _ => characterDefect_nonneg (c * s)) (Nat.cast_nonneg _)

/-- A frequency set of uniformly bounded energy has few coefficients of large mean defect. -/
theorem exists_dualMeanDefect_exceptions {p N t : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (a : Fin N → ZMod p) {M b : ℝ}
    (hM : ∀ s ∈ S, characterEnergy a s ≤ M) (hb : 0 < b)
    (hcount : 2 * M ≤ b * (t : ℝ)) (ht : t ≤ N) :
    ∃ E : Finset (Fin N), E.card = t ∧ ∀ i ∉ E, dualMeanDefect S (a i) ≤ b := by
  let bad := univ.filter (fun i : Fin N => b < dualMeanDefect S (a i))
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hmean : (∑ i, dualMeanDefect S (a i)) ≤ 2 * M := by
    simp only [dualMeanDefect]
    rw [← sum_div, sum_comm]
    refine (div_le_iff₀ hSpos).mpr ?_
    calc
      _ = ∑ s ∈ S, 2 * characterEnergy a s := by
        apply sum_congr rfl
        intro s _
        rw [← sum_div, characterEnergy]
        ring
      _ ≤ ∑ _s ∈ S, 2 * M := sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hM s hs) (by norm_num)
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  have hbad : bad.card ≤ t := by
    have hh : b * (bad.card : ℝ) ≤ b * (t : ℝ) := by
      calc
        _ = ∑ _i ∈ bad, b := by simp [nsmul_eq_mul, mul_comm]
        _ ≤ ∑ i ∈ bad, dualMeanDefect S (a i) :=
          sum_le_sum fun i hi => ((mem_filter.mp hi).2).le
        _ ≤ ∑ i, dualMeanDefect S (a i) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => dualMeanDefect_nonneg S (a i)
        _ ≤ _ := hmean.trans hcount
    exact_mod_cast (mul_le_mul_iff_of_pos_left hb).mp hh
  obtain ⟨E, hE, _, hcard⟩ := exists_subsuperset_card_eq (subset_univ bad) hbad (by simpa using ht)
  refine ⟨E, hcard, fun i hi => le_of_not_gt ?_⟩
  exact fun h => hi (hE (mem_filter.mpr ⟨mem_univ _, h⟩))

private theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hx : ZMod.stdAddChar x ≠ 0 := by
    intro h
    simpa [h] using norm_standard_character x
  apply mul_left_cancel₀ hx
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  change ZMod.stdAddChar x * (starRingEnd ℂ) (ZMod.stdAddChar x) = 1
  rw [Complex.mul_conj', norm_standard_character]
  norm_num

private noncomputable def characterSum {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (c : ZMod p) : ℂ :=
  ∑ s ∈ S, ZMod.stdAddChar (c * s)

private theorem characterSum_norm_sq_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ c : ZMod p, ‖characterSum S c‖ ^ 2) = (p : ℝ) * S.card := by
  have hExpand (c : ZMod p) :
      characterSum S c * star (characterSum S c) =
        ∑ s ∈ S, ∑ t ∈ S, ZMod.stdAddChar (c * (s - t)) := by
    change (∑ s ∈ S, ZMod.stdAddChar (c * s)) *
      (starRingEnd ℂ) (∑ t ∈ S, ZMod.stdAddChar (c * t)) = _
    rw [map_sum, sum_mul]
    apply sum_congr rfl
    intro s _
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    rw [show (starRingEnd ℂ) (ZMod.stdAddChar (c * t)) =
      ZMod.stdAddChar (-(c * t)) from stdAddChar_conj _, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hOrth (s t : ZMod p) :
      (∑ c : ZMod p, ZMod.stdAddChar (c * (s - t))) = if s = t then (p : ℂ) else 0 := by
    simpa only [mul_comm, sub_eq_zero] using sum_standard_mul_character (s - t)
  have hSum : (∑ c : ZMod p, characterSum S c * star (characterSum S c)) = (p : ℂ) * S.card := by
    simp_rw [hExpand]
    rw [sum_comm]
    calc
      _ = ∑ s ∈ S, ∑ t ∈ S, ∑ c : ZMod p, ZMod.stdAddChar (c * (s - t)) := by
        apply sum_congr rfl
        intro s _
        rw [sum_comm]
      _ = _ := by
        simp only [hOrth, sum_ite_eq]
        rw [show (∑ s ∈ S, if s ∈ S then (p : ℂ) else 0) = ∑ _s ∈ S, (p : ℂ) by
          exact sum_congr rfl fun s hs => ite_eq_left hs]
        simp [nsmul_eq_mul, mul_comm]
  have hNorm (x : ℂ) : (x * star x).re = ‖x‖ ^ 2 := by
    change (x * (starRingEnd ℂ) x).re = _
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have h := congrArg Complex.re hSum
  simpa only [Complex.re_sum, hNorm, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] using h

/-- The points of small mean character defect form a set of size at most
four times the inverse density of the frequency set. -/
theorem card_dualMeanDefect_le_quarter {p : ℕ} [NeZero p]
    (S A : Finset (ZMod p)) (hS : S.Nonempty)
    (hA : ∀ c ∈ A, dualMeanDefect S c ≤ 1 / 4) :
    (A.card : ℝ) ≤ 4 * (p : ℝ) / S.card := by
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hRe (c : ZMod p) : dualMeanDefect S c =
      ((S.card : ℝ) - (characterSum S c).re) / (2 * (S.card : ℝ)) := by
    rw [dualMeanDefect, ← sum_div, sum_sub_distrib, characterSum, Complex.re_sum]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    ring
  have hb (c : ZMod p) (hc : c ∈ A) : ((S.card : ℝ) / 2) ^ 2 ≤ ‖characterSum S c‖ ^ 2 := by
    have h := hA c hc
    rw [hRe, div_le_iff₀ (by positivity)] at h
    have h' : (S.card : ℝ) / 2 ≤ ‖characterSum S c‖ := by
      refine (le_trans ?_ (Complex.re_le_norm _))
      linarith
    exact pow_le_pow_left₀ (by positivity) h' _
  have hSum : (A.card : ℝ) * ((S.card : ℝ) / 2) ^ 2 ≤ (p : ℝ) * S.card := by
    calc
      _ = ∑ _c ∈ A, ((S.card : ℝ) / 2) ^ 2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ c ∈ A, ‖characterSum S c‖ ^ 2 := sum_le_sum hb
      _ ≤ ∑ c, ‖characterSum S c‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun c _ _ => sq_nonneg _
      _ = _ := characterSum_norm_sq_sum S
  apply (le_div_iff₀ hSpos).mpr
  apply (mul_le_mul_iff_of_pos_right hSpos).mp
  nlinarith only [hSum]

private theorem dualMeanDefect_eq_radius_sq {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (c : ZMod p) :
    let e := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
    let a : Fin S.card → ZMod p := fun j => e j
    dualMeanDefect S c = charRadius a c ^ 2 / (4 * (S.card : ℝ)) := by
  dsimp only
  let e := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let a : Fin S.card → ZMod p := fun j => e j
  change _ = charRadius a c ^ 2 / (4 * (S.card : ℝ))
  have h : (∑ j : Fin S.card, (1 - (ZMod.stdAddChar (a j * c)).re)) =
      ∑ s ∈ S, (1 - (ZMod.stdAddChar (c * s)).re) := by
    conv_rhs => rw [← Finset.sum_coe_sort]
    exact Fintype.sum_equiv e _ _ (fun j => by simp [a, mul_comm])
  rw [dualMeanDefect, ← sum_div, ← h]
  have h' := characterEnergy_eq_radius_sq a c
  rw [characterEnergy] at h'
  rw [show (∑ j : Fin S.card, (1 - (ZMod.stdAddChar (a j * c)).re)) =
      charRadius a c ^ 2 / 2 by linarith]
  ring

/-- The square root of mean character defect is subadditive. -/
theorem dualMeanDefect_pointwise_nsmul_le {p : ℕ} [NeZero p]
    (S A : Finset (ZMod p)) (hS : S.Nonempty) {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ c ∈ A, dualMeanDefect S c ≤ b) (k : ℕ) :
    ∀ c ∈ k • A, dualMeanDefect S c ≤ (k : ℝ) ^ 2 * b := by
  let e := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let a : Fin S.card → ZMod p := fun j => e j
  let r := charRadius a
  let d := Real.sqrt (4 * (S.card : ℝ) * b)
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hd : d ^ 2 = 4 * (S.card : ℝ) * b := Real.sq_sqrt (by positivity)
  have hr (c : ZMod p) : dualMeanDefect S c = r c ^ 2 / (4 * (S.card : ℝ)) :=
    dualMeanDefect_eq_radius_sq S c
  have hrA (c : ZMod p) (hc : c ∈ A) : r c ≤ d := by
    have hrn : 0 ≤ r c := norm_nonneg _
    have hdn : 0 ≤ d := Real.sqrt_nonneg _
    apply (sq_le_sq₀ hrn hdn).mp
    rw [hd]
    have h := hA c hc
    rw [hr, div_le_iff₀ (by positivity), mul_comm b] at h
    exact h
  intro c hc
  have he := radius_mem_pointwise_nsmul_les r (charRadius_zero a) (charRadius_add_le a) A d hrA k c hc
  rw [hr, div_le_iff₀ (by positivity)]
  calc
    _ ≤ ((k : ℝ) * d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he _
    _ = _ := by rw [mul_pow, hd]; ring

theorem dualMeanDefect_sumset_card_le {p k : ℕ} [NeZero p]
    (S A : Finset (ZMod p)) (hSn : S.Nonempty) (hk : 0 < k)
    (hA : ∀ c ∈ A, dualMeanDefect S c ≤ 1 / (16 * (k : ℝ) ^ 2)) :
    ((k • A).card : ℝ) ≤ 4 * (p : ℝ) / S.card := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  refine card_dualMeanDefect_le_quarter S _ hSn fun c hc => ?_
  refine (dualMeanDefect_pointwise_nsmul_le S A hSn (by positivity) hA k c hc).trans ?_
  field_simp
  nlinarith only [sq_nonneg (k : ℝ)]

/-- Mean defect controls both the size of a sumset and, by Cauchy–Davenport,
the number of admissible coefficients. -/
theorem dualMeanDefect_sumset_card_bounds {p k : ℕ} [Fact p.Prime]
    (S A : Finset (ZMod p)) (hS : 4 < S.card) (hk : 0 < k)
    (hA : ∀ c ∈ A, dualMeanDefect S c ≤ 1 / (16 * (k : ℝ) ^ 2)) :
    ((k • A).card : ℝ) ≤ 4 * (p : ℝ) / S.card ∧
      (A.card : ℝ) ≤ (4 * (p : ℝ) / S.card) / k + 1 := by
  have hSn : S.Nonempty := card_pos.mp (by omega)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbound := dualMeanDefect_sumset_card_le S A hSn hk hA
  refine ⟨hbound, ?_⟩
  by_cases hAn : A.Nonempty
  · have hp := Fact.out (p := p.Prime)
    have hSR : (4 : ℝ) < S.card := by exact_mod_cast hS
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hlt : (k • A).card < p := by
      have h : ((k • A).card : ℝ) < p :=
        hbound.trans_lt ((div_lt_iff₀ (by positivity)).mpr (by nlinarith only [mul_lt_mul_of_pos_right hSR hpR]))
      exact_mod_cast h
    have hcd := card_pointwise_nsmul_ge hp A hAn k
    have hh : k * (A.card - 1) ≤ (k • A).card := by omega
    have hhR : (k : ℝ) * ((A.card : ℝ) - 1) ≤ ((k • A).card : ℝ) := by
      rw [← Nat.cast_one, ← Nat.cast_sub (show 1 ≤ A.card from hAn.card_pos)]
      exact_mod_cast hh
    have hQ : (A.card : ℝ) - 1 ≤ (4 * (p : ℝ) / S.card) / k := by
      apply (le_div_iff₀ hkR).mpr
      rw [mul_comm _ (k : ℝ)]
      exact hhR.trans hbound
    linarith
  · rw [not_nonempty_iff_eq_empty.mp hAn]
    simp only [card_empty, Nat.cast_zero]
    positivity

end BooleanThreshold
