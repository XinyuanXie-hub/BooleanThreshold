module

public import BooleanThreshold.JSSConditionalFourierMoment
public import BooleanThreshold.JSSConditionalAdaptive
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace BooleanThreshold

private theorem cyclicShiftAverage_comm {P : ℕ} (f : ZMod P → ℂ) (y z : ℤ) :
    cyclicShiftAverage y (cyclicShiftAverage z f) = cyclicShiftAverage z (cyclicShiftAverage y f) := by
  funext t
  simp only [cyclicShiftAverage]
  rw [add_right_comm (a := t) (b := (z : ZMod P)) (c := (y : ZMod P))]
  ring

private theorem cyclicShiftSmoothing_average_comm {P m : ℕ} (f : ZMod P → ℂ) (z : ℤ) (y : Fin m → ℤ) :
    cyclicShiftSmoothing (cyclicShiftAverage z f) y = cyclicShiftAverage z (cyclicShiftSmoothing f y) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cyclicShiftSmoothing, ih, cyclicShiftSmoothing, cyclicShiftAverage_comm]

private theorem cyclicShiftSmoothing_succ_forward {P m : ℕ} (f : ZMod P → ℂ) (y : Fin (m + 1) → ℤ) :
    cyclicShiftSmoothing f y = cyclicShiftSmoothing (cyclicShiftAverage (y 0) f) (Fin.tail y) := by
  rw [cyclicShiftSmoothing, cyclicShiftSmoothing_average_comm]

private theorem cyclicShiftAverage_re {P : ℕ} (f : ZMod P → ℂ) (y : ℤ) (t : ZMod P) :
    (cyclicShiftAverage y f t).re = ((f t).re + (f (t + (y : ZMod P))).re) / 2 := by
  rw [cyclicShiftAverage, div_eq_mul_inv]
  norm_num [Complex.mul_re, Complex.add_re, div_eq_mul_inv]

private def pathNext {P : ℕ} (v : Bool) (t : ZMod P) (y : ℤ) : ZMod P :=
  if v then t - (y : ZMod P) else t

private def pathOther {P : ℕ} (v : Bool) (t : ZMod P) (y : ℤ) : ZMod P :=
  if v then t - (y : ZMod P) else t + (y : ZMod P)

private theorem exists_preferredPredecessor {P : ℕ} (f : ZMod P → ℂ) (y : ℤ) (s : ZMod P) :
    ∃ v t, pathNext v t y = s ∧ (f (pathOther v t y)).re ≤ (f t).re ∧
      (cyclicShiftAverage y f s).re = ((f t).re + (f (pathOther v t y)).re) / 2 := by
  rw [cyclicShiftAverage_re]
  by_cases h : (f (s + (y : ZMod P))).re ≤ (f s).re
  · exact ⟨false, s, rfl, h, rfl⟩
  · refine ⟨true, s + (y : ZMod P), by simp [pathNext], ?_, ?_⟩
    · simpa [pathOther] using le_of_not_ge h
    · simp [pathOther, add_comm]

private def acceptsSparsePath {P m : ℕ} (a : ℝ) (v S : Fin m → Bool) (f : ZMod P → ℂ)
    (t : ZMod P) (y : Fin m → ℤ) : Prop :=
  acceptsAdaptivePath
    (fun i (s : (ZMod P → ℂ) × ZMod P) z => (cyclicShiftAverage z s.1, pathNext (v i) s.2 z))
    (fun i s z => S i = true → a ≤ (s.1 (pathOther (v i) s.2 z)).re) (f, t) y

private def falseCount {m : ℕ} (S : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => S i = false).card

private theorem falseCount_cons {m : ℕ} (S : Fin m → Bool) (b : Bool) :
    falseCount (Fin.cons b S) = (if b = false then 1 else 0) + falseCount S := by
  simp only [falseCount]
  rw [Finset.card_eq_sum_ite (Finset.subset_univ _), Finset.card_eq_sum_ite (Finset.subset_univ _),
    Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem exists_sparsePath {P m : ℕ} {a : ℝ} (ha : 0 < a)
    (f : ZMod P → ℂ) (t : ZMod P) (y : Fin m → ℤ) (ht : a ≤ (cyclicShiftSmoothing f y t).re) :
    ∃ (v S : Fin m → Bool) (s : ZMod P), acceptsSparsePath (a / 2) v S f s y ∧
      (falseCount S : ℝ) * (a / 2) ≤ (f s).re - (cyclicShiftSmoothing f y t).re := by
  induction m generalizing f t with
  | zero =>
    refine ⟨fun _ => false, fun _ => false, t, trivial, ?_⟩
    simp [falseCount, cyclicShiftSmoothing]
  | succ m ih =>
    rw [cyclicShiftSmoothing_succ_forward] at ht ⊢
    let g := cyclicShiftAverage (y 0) f
    let h := (cyclicShiftSmoothing g (Fin.tail y) t).re
    obtain ⟨v, S, s, hp, hcost⟩ := ih g t (Fin.tail y) ht
    obtain ⟨b, r, hr, hle, hmean⟩ := exists_preferredPredecessor f (y 0) s
    have hs : a ≤ (g s).re := by
      have hnn : 0 ≤ (falseCount S : ℝ) * (a / 2) := by positivity
      linarith only [hcost, ht, hnn]
    have hmono : (g s).re ≤ (f r).re := by
      change (g s).re = _ at hmean
      linarith only [hmean, hle]
    let b' : Bool := decide (a / 2 ≤ (f (pathOther b r (y 0))).re)
    refine ⟨Fin.cons b v, Fin.cons b' S, r, ?_, ?_⟩
    · rw [acceptsSparsePath, acceptsAdaptivePath]
      simp only [Fin.cons_zero, hr]
      exact ⟨fun hb => of_decide_eq_true hb, hp⟩
    · rw [falseCount_cons, Nat.cast_add, add_mul]
      have hfirst :
          ((if b' = false then 1 else 0 : ℕ) : ℝ) * (a / 2) ≤ (f r).re - (g s).re := by
        by_cases hb : a / 2 ≤ (f (pathOther b r (y 0))).re
        · simpa [b', hb] using sub_nonneg.mpr hmono
        · simp only [b', decide_eq_false (not_le.mp hb).not_ge, ite_true,
            Nat.cast_one, one_mul]
          change (g s).re = _ at hmean
          linarith only [hmean, hs, lt_of_not_ge hb]
      linarith only [hcost, hfirst]

private theorem card_acceptsSparsePath_le {P m : ℕ} {a : ℝ}
    (U : (ZMod P → ℂ) → Prop) (hU : ∀ f, U f → ∀ z, U (cyclicShiftAverage z f))
    (B : Fin m → Finset ℤ) (v S : Fin m → Bool) (d : ℕ)
    (hstep : ∀ i f t, U f →
      (((B i).filter fun z => a ≤ (f (pathOther (v i) t z)).re).card) ≤ d)
    (f : ZMod P → ℂ) (t : ZMod P) (hf : U f) :
    (((Fintype.piFinset B).filter (acceptsSparsePath a v S f t)).card) ≤
      ∏ i, if S i then d else (B i).card := by
  unfold acceptsSparsePath
  refine card_acceptsAdaptivePath_le _ _ (fun s => U s.1) (fun i s z h => hU s.1 h z) B _ ?_ (f, t) hf
  intro i s hs
  by_cases h : S i = true
  · simpa [h] using hstep i s.1 s.2 hs
  · simp [h]

private theorem prod_bool_card_le {m d N j : ℕ} (S : Fin m → Bool) (hd : d ≤ N) (hj : j ≤ m)
    (hS : falseCount S ≤ j) : (∏ i, if S i then d else N) ≤ d ^ (m - j) * N ^ j := by
  have hcond (i : Fin m) : (if S i then d else N) = if S i = false then N else d := by
    cases S i <;> rfl
  have hcompl : (Finset.univ.filter fun i : Fin m => ¬ S i = false).card = m - falseCount S := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => S i = false)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    change falseCount S + _ = m at h
    omega
  simp_rw [hcond]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, ← falseCount, hcompl, mul_comm]
  have hsplit : m - falseCount S = (m - j) + (j - falseCount S) := by omega
  rw [hsplit, pow_add, mul_assoc]
  apply Nat.mul_le_mul_left
  calc
    d ^ (j - falseCount S) * N ^ falseCount S ≤ N ^ (j - falseCount S) * N ^ falseCount S :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd _)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hS]

private theorem cyclicShiftAverage_sq_norm_sum_le {P : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (y : ℤ) : (∑ t, ‖cyclicShiftAverage y f t‖ ^ 2) ≤ ∑ t, ‖f t‖ ^ 2 := by
  have hpoint (t : ZMod P) : ‖cyclicShiftAverage y f t‖ ^ 2 ≤
      (‖f t‖ ^ 2 + ‖f (t + (y : ZMod P))‖ ^ 2) / 2 := by
    have hnorm : ‖cyclicShiftAverage y f t‖ ≤ (‖f t‖ + ‖f (t + (y : ZMod P))‖) / 2 := by
      rw [cyclicShiftAverage, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact div_le_div_of_nonneg_right (norm_add_le (f t) (f (t + (y : ZMod P)))) (by norm_num)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith only [hsq, sq_nonneg (‖f t‖ - ‖f (t + (y : ZMod P))‖)]
  have hshift : (∑ t : ZMod P, ‖f (t + (y : ZMod P))‖ ^ 2) = ∑ t : ZMod P, ‖f t‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight (y : ZMod P)) _ _ fun _ => rfl
  calc
    _ ≤ ∑ t : ZMod P, (‖f t‖ ^ 2 + ‖f (t + (y : ZMod P))‖ ^ 2) / 2 := by
      exact Finset.sum_le_sum fun t _ => hpoint t
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib, hshift]; ring

private theorem card_high_re_le {P d : ℕ} [NeZero P] {a : ℝ} (ha : 0 < a)
    (f : ZMod P → ℂ) (henergy : ∑ t, ‖f t‖ ^ 2 ≤ (d : ℝ) * a ^ 2) :
    (Finset.univ.filter fun t => a ≤ (f t).re).card ≤ d := by
  let H := Finset.univ.filter fun t => a ≤ (f t).re
  have hc : (H.card : ℝ) * a ^ 2 ≤ (d : ℝ) * a ^ 2 := by
    calc
      _ = ∑ _t ∈ H, a ^ 2 := by simp
      _ ≤ ∑ t ∈ H, ‖f t‖ ^ 2 := by
        refine Finset.sum_le_sum fun t ht => pow_le_pow_left₀ ha.le ?_ _
        exact ((Finset.mem_filter.mp ht).2).trans (Complex.re_le_norm _)
      _ ≤ ∑ t, ‖f t‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by positivity)
      _ ≤ _ := henergy
  exact_mod_cast le_of_mul_le_mul_right hc (sq_pos_of_pos ha)

/-- A small squared norm leaves few peaks at each stage of fair-shift
averaging. If a large value survives, an adaptive path must meet the peak
set in all but a bounded number of its shifts. -/
theorem cyclicShiftSmoothing_card_high_re_le {P m d N j : ℕ} [NeZero P] {a : ℝ} (ha : 0 < a)
    (B : Fin m → Finset ℤ) (hB : ∀ i, (B i).card = N)
    (hinj : ∀ i, Set.InjOn (fun x : ℤ => (x : ZMod P)) (B i))
    (hd : d ≤ N) (hj : j ≤ m) (f : ZMod P → ℂ)
    (henergy : ∑ t, ‖f t‖ ^ 2 ≤ (d : ℝ) * (a / 2) ^ 2)
    (hcap : ∀ t, (f t).re ≤ a + (j : ℝ) * (a / 2)) :
    ((Fintype.piFinset B).filter fun y => ∃ t, a ≤ (cyclicShiftSmoothing f y t).re).card ≤
      P * 4 ^ m * (d ^ (m - j) * N ^ j) := by
  let U (g : ZMod P → ℂ) : Prop := ∑ t, ‖g t‖ ^ 2 ≤ (d : ℝ) * (a / 2) ^ 2
  have hU (g : ZMod P → ℂ) (hg : U g) (z : ℤ) : U (cyclicShiftAverage z g) :=
    (cyclicShiftAverage_sq_norm_sum_le g z).trans hg
  have hstep (v : Fin m → Bool) (i : Fin m) (g : ZMod P → ℂ) (t : ZMod P) (hg : U g) :
      ((B i).filter fun z => a / 2 ≤ (g (pathOther (v i) t z)).re).card ≤ d := by
    let H : Finset (ZMod P) := Finset.univ.filter fun z => a / 2 ≤ (g z).re
    refine (Finset.card_le_card_of_injOn (pathOther (v i) t) (t := H) ?_ ?_).trans ?_
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
    · intro z hz z' hz' heq
      apply hinj i (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz').1
      cases hv : v i with
      | false => simpa [pathOther, hv] using heq
      | true => simpa [pathOther, hv, sub_eq_add_neg] using heq
    · exact card_high_re_le (by positivity) g hg
  let Q := ZMod P × ((Fin m → Bool) × (Fin m → Bool))
  let I : Finset Q := Finset.univ.filter fun q => falseCount q.2.2 ≤ j
  let X := Fintype.piFinset B
  let E (q : Q) := X.filter (acceptsSparsePath (a / 2) q.2.1 q.2.2 f q.1)
  have hcover : (X.filter fun y => ∃ t, a ≤ (cyclicShiftSmoothing f y t).re) ⊆ I.biUnion E := by
    intro y hy
    obtain ⟨hy₀, t, ht⟩ := Finset.mem_filter.mp hy
    obtain ⟨v, S, s, hS, hcost⟩ := exists_sparsePath ha f t y ht
    have hbudget : (falseCount S : ℝ) ≤ j := by
      apply le_of_mul_le_mul_right _ (show 0 < a / 2 by positivity)
      linarith only [hcost, hcap s, ht]
    have hS' : falseCount S ≤ j := by exact_mod_cast hbudget
    exact Finset.mem_biUnion.mpr ⟨(s, v, S), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS'⟩,
      Finset.mem_filter.mpr ⟨hy₀, hS⟩⟩
  have hE (q : Q) (hq : q ∈ I) : (E q).card ≤ d ^ (m - j) * N ^ j := by
    have hcard := card_acceptsSparsePath_le U hU B q.2.1 q.2.2 d (hstep q.2.1) f q.1 henergy
    simp only [hB] at hcard
    exact hcard.trans (prod_bool_card_le q.2.2 hd hj (Finset.mem_filter.mp hq).2)
  have hI : I.card ≤ P * 4 ^ m := by
    refine (Finset.card_le_univ I).trans (le_of_eq ?_)
    simp only [Q, Fintype.card_prod, ZMod.card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← mul_pow]
    norm_num
  calc
    _ ≤ (I.biUnion E).card := Finset.card_le_card hcover
    _ ≤ ∑ q ∈ I, (E q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ I, d ^ (m - j) * N ^ j := Finset.sum_le_sum hE
    _ = I.card * (d ^ (m - j) * N ^ j) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hI

theorem intCast_injOn_Ico_zmod {P N : ℕ} (a : ℤ) (hN : N ≤ P) :
    Set.InjOn (fun x : ℤ => (x : ZMod P)) (Finset.Ico a (a + (N : ℤ)) : Finset ℤ) := by
  intro x hx y hy hxy
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_Ico.mp (Finset.mem_coe.mp hx)
  obtain ⟨hy₁, hy₂⟩ := Finset.mem_Ico.mp (Finset.mem_coe.mp hy)
  have hd : (P : ℤ) ∣ x - y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simp [Int.cast_sub, hxy])
  have hd' : P ∣ (x - y).natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
  by_contra hne
  have hpos : 0 < (x - y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt : (x - y).natAbs < P := by
    have hZ : |x - y| < (P : ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
    rw [Int.abs_eq_natAbs] at hZ
    exact_mod_cast hZ
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos hd')

end BooleanThreshold
