module

public import BooleanThreshold.JSSConditionalFourierMoment
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

open Filter
open scoped BigOperators Classical Topology

namespace BooleanThreshold

private theorem card_integer_interval_le {s : Finset ℤ} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ z ∈ s, a ≤ (z : ℝ) ∧ (z : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b - a + 1 := by
  by_cases h : s.Nonempty
  · let l := s.min' h
    let u := s.max' h
    have hl := s.min'_mem h
    have hu := s.max'_mem h
    have hlu : l ≤ u := s.min'_le _ hu
    have hcard : ((Finset.Icc l u).card : ℝ) = (u : ℝ) + 1 - l := by
      exact_mod_cast Int.card_Icc_of_le l u (hlu.trans (by omega : u ≤ u + 1))
    have hsub : s ⊆ Finset.Icc l u := fun z hz =>
      Finset.mem_Icc.mpr ⟨s.min'_le z hz, s.le_max' z hz⟩
    calc
      _ ≤ ((Finset.Icc l u).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = _ := hcard
      _ ≤ _ := by linarith only [(hs l hl).1, (hs u hu).2]
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith only [hab]

private theorem card_close_to_integer_le (a : ℤ) (N : ℕ) {ω ε : ℝ}
    (hω : 0 < ω) (hscale : 1 ≤ (N : ℝ) * ω) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    (((Finset.Ico a (a + (N : ℤ))).filter fun z : ℤ =>
      |ω * (z : ℝ) - (round (ω * (z : ℝ)) : ℝ)| < ε).card : ℝ) ≤
      3 * (2 * ε + ω) * N := by
  let X := Finset.Ico a (a + (N : ℤ))
  let r (z : ℤ) := round (ω * (z : ℝ))
  let T := X.filter fun z : ℤ => |ω * (z : ℝ) - (r z : ℝ)| < ε
  let L := ω * (a : ℝ) - ε
  let U := ω * ((a : ℝ) + N) + ε
  let J := Finset.Icc ⌈L⌉ ⌊U⌋
  have hJ : ∀ z ∈ T, r z ∈ J := by
    intro z hz
    obtain ⟨hz, h⟩ := Finset.mem_filter.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_Ico.mp hz
    have ha' : (a : ℝ) ≤ z := by exact_mod_cast ha
    have hb' : (z : ℝ) ≤ (a : ℝ) + N := by exact_mod_cast hb.le
    obtain ⟨hl, hu⟩ := abs_lt.mp h
    apply Finset.mem_Icc.mpr
    refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
    · dsimp [L]
      linarith only [hu, mul_le_mul_of_nonneg_left ha' hω.le]
    · dsimp [U]
      linarith only [hl, mul_le_mul_of_nonneg_left hb' hω.le]
  have hcardJ : (J.card : ℝ) ≤ (N : ℝ) * ω + 2 := by
    have hlu : L ≤ U := by dsimp [L, U]; nlinarith only [hscale, hε]
    have hh := card_integer_interval_le (s := J) hlu (fun j hj => by
      obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hj
      exact ⟨Int.ceil_le.mp ha, Int.le_floor.mp hb⟩)
    dsimp [U, L] at hh
    linarith only [hh, hε']
  have hcardF (j : ℤ) : (((T.filter fun z => r z = j).card : ℕ) : ℝ) ≤ 2 * ε / ω + 1 := by
    have hh := card_integer_interval_le (s := T.filter fun z => r z = j)
      (div_le_div_of_nonneg_right (show (j : ℝ) - ε ≤ j + ε by linarith only [hε]) hω.le) ?_
    · convert hh using 1
      rw [← sub_div]
      congr 2
      ring
    · intro z hz
      obtain ⟨hz, h⟩ := Finset.mem_filter.mp hz
      have hd := (Finset.mem_filter.mp hz).2
      rw [h] at hd
      obtain ⟨hl, hu⟩ := abs_lt.mp hd
      constructor
      · exact (div_le_iff₀ hω).mpr (by linarith only [hl])
      · exact (le_div_iff₀ hω).mpr (by linarith only [hu])
  have hcard : T.card = ∑ j ∈ J, (T.filter fun z => r z = j).card :=
    Finset.card_eq_sum_card_fiberwise hJ
  change (T.card : ℝ) ≤ _
  calc
    _ = ∑ j ∈ J, ((T.filter fun z => r z = j).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _j ∈ J, (2 * ε / ω + 1) := Finset.sum_le_sum fun j _ => hcardF j
    _ = (J.card : ℝ) * (2 * ε / ω + 1) := by simp [mul_add]
    _ ≤ ((N : ℝ) * ω + 2) * (2 * ε / ω + 1) :=
      mul_le_mul_of_nonneg_right hcardJ (by positivity)
    _ ≤ (3 * (N : ℝ) * ω) * (2 * ε / ω + 1) :=
      mul_le_mul_of_nonneg_right (by linarith only [hscale]) (by positivity)
    _ = _ := by field_simp

private theorem abs_cos_pi_eq_cos_distance (x : ℝ) :
    |Real.cos (Real.pi * x)| = Real.cos (Real.pi * |x - (round x : ℝ)|) := by
  let r := round x
  have heq : Real.pi * x = Real.pi * (x - (r : ℝ)) + r * Real.pi := by ring
  have hdist : Real.pi * |x - (r : ℝ)| ≤ Real.pi / 2 := by
    have h := mul_le_mul_of_nonneg_left (abs_sub_round x) Real.pi_pos.le
    linarith only [h]
  have hnonneg : 0 ≤ Real.cos (Real.pi * |x - (r : ℝ)|) := by
    apply Real.cos_nonneg_of_mem_Icc
    exact ⟨(neg_nonpos.mpr Real.pi_div_two_pos.le).trans (by positivity), hdist⟩
  change |Real.cos (Real.pi * x)| = Real.cos (Real.pi * |x - (r : ℝ)|)
  rw [heq, Real.cos_add_int_mul_pi, abs_mul, ← Real.cos_int_mul_pi, Real.abs_cos_int_mul_pi,
    one_mul, ← Real.cos_abs, abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg hnonneg]

private theorem abs_cos_pi_le_of_distance {x ε : ℝ} (hε : 0 ≤ ε)
    (h : ε ≤ |x - (round x : ℝ)|) : |Real.cos (Real.pi * x)| ≤ Real.cos (Real.pi * ε) := by
  rw [abs_cos_pi_eq_cos_distance]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) _ (mul_le_mul_of_nonneg_left h Real.pi_pos.le)
  have hd := mul_le_mul_of_nonneg_left (abs_sub_round x) Real.pi_pos.le
  linarith only [hd, Real.pi_pos]

/-- Averaging a high cosine power over a long interval gives an arbitrarily
small moment uniformly for frequencies between the reciprocal interval length
and a sufficiently small constant. -/
theorem exists_cosine_interval_moment_le {q : ℝ} (hq : 0 < q) :
    ∃ b > (0 : ℝ), ∃ p : ℕ, ∀ (a : ℤ) (N : ℕ) (ω : ℝ),
      1 ≤ (N : ℝ) * ω → ω ≤ b →
      ∑ z ∈ Finset.Ico a (a + (N : ℤ)), |Real.cos (Real.pi * (ω * ((z : ℤ) : ℝ)))| ^ (2 * p) ≤ q * N := by
  let b := min (q / 36) (1 / 4)
  have hb : 0 < b := lt_min (by positivity) (by norm_num)
  have hb₁ : b ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hπb : Real.pi * b ≤ Real.pi / 2 := by
    have h := mul_le_mul_of_nonneg_left hb₁ Real.pi_pos.le
    linarith only [h]
  have hcos₀ : 0 ≤ Real.cos (Real.pi * b) :=
    Real.cos_nonneg_of_mem_Icc ⟨(neg_nonpos.mpr Real.pi_div_two_pos.le).trans (by positivity), hπb⟩
  have hcos₁ : Real.cos (Real.pi * b) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hπb (by positivity)
  let c := Real.cos (Real.pi * b) ^ 2
  have hc : |c| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_lt_one₀ hcos₀ hcos₁ (by decide)
  have hlim := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).eventually_le_const
    (show (0 : ℝ) < q / 2 by positivity)
  obtain ⟨p, hp⟩ := eventually_atTop.mp hlim
  have hp' : Real.cos (Real.pi * b) ^ (2 * p) ≤ q / 2 := by
    rw [pow_mul]
    exact hp p le_rfl
  refine ⟨b, hb, p, fun a N ω hscale hωb => ?_⟩
  have hω : 0 < ω := by
    by_contra! hω
    exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hω)
      (zero_lt_one.trans_le hscale)
  let X := Finset.Ico a (a + (N : ℤ))
  let T := X.filter fun z : ℤ => |ω * (z : ℝ) - (round (ω * (z : ℝ)) : ℝ)| < b
  let f (z : ℤ) := |Real.cos (Real.pi * (ω * (z : ℝ)))| ^ (2 * p)
  have hX : X.card = N := by
    dsimp only [X]
    rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]
  have ht : (T.card : ℝ) ≤ (q / 4) * N := by
    refine (card_close_to_integer_le a N hω hscale hb.le hb₁).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hq' : b ≤ q / 36 := min_le_left _ _
    linarith only [hq', hωb]
  have htf (z : ℤ) (hz : z ∈ X \ T) : f z ≤ q / 2 := by
    have h := Finset.mem_sdiff.mp hz
    have hd : b ≤ |ω * (z : ℝ) - (round (ω * (z : ℝ)) : ℝ)| :=
      le_of_not_gt fun hlt => h.2 (Finset.mem_filter.mpr ⟨h.1, hlt⟩)
    exact (pow_le_pow_left₀ (abs_nonneg _) (abs_cos_pi_le_of_distance hb.le hd) _).trans hp'
  change (∑ z ∈ X, f z) ≤ _
  have hTX : T ⊆ X := Finset.filter_subset _ _
  rw [← Finset.sum_sdiff hTX]
  calc
    _ ≤ (∑ _z ∈ X \ T, q / 2) + ∑ _z ∈ T, (1 : ℝ) := by
      apply add_le_add (Finset.sum_le_sum htf)
      exact Finset.sum_le_sum fun z _ => pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
    _ = ((X \ T).card : ℝ) * (q / 2) + (T.card : ℝ) := by simp
    _ ≤ (N : ℝ) * (q / 2) + (q / 4) * N := by
      refine add_le_add (mul_le_mul_of_nonneg_right ?_ (by positivity)) ht
      rw [← hX]
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : X \ T ⊆ X)
    _ ≤ _ := by nlinarith only [mul_nonneg hq.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

private theorem norm_half_exp_add_one (x : ℝ) :
    ‖(1 + Complex.exp (2 * ((x : ℂ) * Complex.I))) / 2‖ = |Real.cos x| := by
  have hc : (Real.cos x : ℂ) =
      (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I)) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
    rw [mul_comm, Complex.ofReal_cos, Complex.two_cos]
  have heq : (1 + Complex.exp (2 * ((x : ℂ) * Complex.I))) / 2 =
      Complex.exp ((x : ℂ) * Complex.I) * (Real.cos x : ℂ) := by
    rw [hc, ← mul_div_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have ha : (x : ℂ) * Complex.I + (x : ℂ) * Complex.I = 2 * ((x : ℂ) * Complex.I) := by ring
    have hb : (x : ℂ) * Complex.I + -(x : ℂ) * Complex.I = 0 := by ring
    rw [ha, hb, Complex.exp_zero, add_comm]
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_cyclicShiftMultiplier_eq_abs_cos {P : ℕ} [NeZero P] (k : ZMod P) (y : ℤ) :
    ‖cyclicShiftMultiplier k y‖ = |Real.cos (Real.pi * (|(k.valMinAbs : ℝ) / (P : ℝ)| * (y : ℝ)))| := by
  let θ := (k.valMinAbs : ℝ) / (P : ℝ)
  have hex : ZMod.stdAddChar ((y : ZMod P) * k) =
      Complex.exp (2 * (((Real.pi * (θ * (y : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
    rw [show (y : ZMod P) * k = ((y * k.valMinAbs : ℤ) : ZMod P) by simp [Int.cast_mul],
      ZMod.stdAddChar_coe]
    congr 1
    dsimp [θ]
    push_cast
    ring
  rw [cyclicShiftMultiplier, hex, norm_half_exp_add_one]
  change |Real.cos (Real.pi * (θ * (y : ℝ)))| = |Real.cos (Real.pi * (|θ| * (y : ℝ)))|
  rcases le_total 0 θ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, neg_mul, mul_neg, Real.cos_neg]

/-- The fair-shift Fourier multipliers have uniformly small moments on a band
above the reciprocal length of an interval of integral shifts. -/
theorem exists_cyclicShiftMultiplier_interval_moment_le {q : ℝ} (hq : 0 < q) :
    ∃ b > (0 : ℝ), ∃ p : ℕ, ∀ (P N : ℕ) [NeZero P] (k : ZMod P) (a : ℤ),
      1 ≤ (N : ℝ) * |(k.valMinAbs : ℝ) / (P : ℝ)| → |(k.valMinAbs : ℝ) / (P : ℝ)| ≤ b →
      ∑ y ∈ Finset.Ico a (a + (N : ℤ)), ‖cyclicShiftMultiplier k y‖ ^ (2 * p) ≤ q * N := by
  obtain ⟨b, hb, p, h⟩ := exists_cosine_interval_moment_le hq
  exact ⟨b, hb, p, fun P N _ k a hscale hband => by
    simp_rw [norm_cyclicShiftMultiplier_eq_abs_cos]
    exact h a N _ hscale hband⟩

end BooleanThreshold
