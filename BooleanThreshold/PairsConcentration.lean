module

public import BooleanThreshold.NonPairSign
public import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

private def signSum {ι : Type*} [Fintype ι] (a : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, a i * (if x i then 1 else -1)

private theorem card_signSum_eq_le_pos {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (t : ℝ) :
    Nat.card {x : ι → Bool // signSum a x = t} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  let selected (x : ι → Bool) : Finset ι := Finset.univ.filter fun i => x i = true
  let vectors : Finset (ι → Bool) := Finset.univ.filter fun x => signSum a x = t
  let family : Finset (Finset ι) := vectors.image selected
  have hselected : Function.Injective selected := by
    intro x y h
    funext i
    have hmem : i ∈ selected x ↔ i ∈ selected y := by rw [h]
    simpa [selected] using hmem
  have hsum (x) : signSum a x = 2 * (∑ i ∈ selected x, a i) - ∑ i, a i := by
    simp only [signSum, selected, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [two_mul]
  have hanti : IsAntichain (· ⊆ ·) (family : Set (Finset ι)) := by
    intro s hs u hu hne hsubset
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (show s ∈ family from hs)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (show u ∈ family from hu)
    obtain ⟨i, hi, hnot⟩ := Finset.not_subset.mp (fun h => hne (Finset.Subset.antisymm hsubset h))
    have hlt : (∑ j ∈ selected x, a j) < ∑ j ∈ selected y, a j :=
      Finset.sum_lt_sum_of_subset hsubset hi hnot (ha i) (fun j _ _ => (ha j).le)
    have hx' : signSum a x = t := (Finset.mem_filter.mp hx).2
    have hy' : signSum a y = t := (Finset.mem_filter.mp hy).2
    linarith [hsum x, hsum y]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change vectors.card ≤ _
  rw [← Finset.card_image_of_injective vectors hselected]
  exact hanti.sperner

private theorem card_signSum_eq_le_ne_zero {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) (t : ℝ) :
    Nat.card {x : ι → Bool // signSum a x = t} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  let flip : (ι → Bool) ≃ (ι → Bool) :=
    Equiv.piCongrRight fun i => if a i < 0 then Equiv.boolNot else Equiv.refl Bool
  have hflip (x) : signSum a x = signSum (fun i => |a i|) (flip x) := by
    apply Finset.sum_congr rfl
    intro i _
    change a i * (if x i then 1 else -1) =
      |a i| * (if (if a i < 0 then Equiv.boolNot else Equiv.refl Bool) (x i) then 1 else -1)
    by_cases hi : a i < 0
    · rw [ite_eq_left hi, abs_of_neg hi]
      cases x i <;> simp
    · rw [ite_eq_right hi, abs_of_nonneg (le_of_not_gt hi)]
      rfl
  let e := flip.subtypeEquiv (p := fun x => signSum a x = t)
    (q := fun y => signSum (fun i => |a i|) y = t) (fun x => by rw [hflip x])
  rw [Nat.card_congr e]
  exact card_signSum_eq_le_pos _ (fun i => abs_pos.mpr (ha i)) t

private theorem card_signSum_eq_support {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (t : ℝ) [DecidablePred (fun i => a i ≠ 0)] :
    Nat.card {x : ι → Bool // signSum a x = t} =
      Nat.card {y : {i // a i ≠ 0} → Bool //
        signSum (fun i : {i // a i ≠ 0} => a i) y = t} *
        2 ^ Fintype.card {i // ¬ a i ≠ 0} := by
  classical
  let p := fun i => a i ≠ 0
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bool)
  have hsum (x) : signSum a x = signSum (fun i : Subtype p => a i) (e x).1 := by
    let w (i : ι) := a i * (if x i then 1 else -1)
    change ∑ i, w i = ∑ i : Subtype p, w i
    have hzero : (∑ i : {i // ¬ p i}, w i) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp [w, not_not.mp i.2]
    rw [← Fintype.sum_subtype_add_sum_subtype p w, hzero, add_zero]
  let fe := e.subtypeEquiv (p := fun x => signSum a x = t)
    (q := fun y => signSum (fun i : Subtype p => a i) y.1 = t) (fun x => by rw [hsum x])
  let pe := Equiv.prodSubtypeFstEquivSubtypeProd
    (β := {i // ¬ p i} → Bool) (p := fun y : Subtype p → Bool =>
      signSum (fun i : Subtype p => a i) y = t)
  rw [Nat.card_congr (fe.trans pe), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Subtype (fun i => ¬ p i) → Bool),
    Fintype.card_fun, Fintype.card_bool]

private theorem zeroAtom_eq_card (r : ℕ) (a : Fin r → ℝ) :
    zeroAtom a = (Nat.card {x : Fin r → Bool // signSum a x = 0} : ℝ≥0∞) / 2 ^ r := by
  rw [zeroAtom, uniformOn_signCube_apply]
  let event : Set (Fin r → Bool) := {x | signSum a x = 0}
  change uniformOn Set.univ event = _
  rw [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite event),
    Fintype.card_pi_const, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    ← Set.ncard_eq_toFinset_card]
  rfl

open scoped Classical in
/-- Littlewood–Offord's bound on the probability that a uniform sign row annihilates
a fixed coefficient vector, in terms of the number of its nonzero coefficients. -/
theorem zeroAtom_le_choose (r : ℕ) (a : Fin r → ℝ) :
    let k := (Finset.univ.filter fun i => a i ≠ 0).card
    zeroAtom a ≤ (k.choose (k / 2) : ℝ≥0∞) / 2 ^ k := by
  classical
  let p := fun i => a i ≠ 0
  let k := Fintype.card (Subtype p)
  let m := Fintype.card (Subtype (fun i => ¬ p i))
  have hkm : r = k + m := by
    have hm : m = r - k := by
      change Fintype.card (Subtype (fun i => ¬ p i)) = r - Fintype.card (Subtype p)
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
    rw [hm]
    have hk : k ≤ r := by simpa [k] using Fintype.card_subtype_le p
    omega
  dsimp only
  rw [← Fintype.card_subtype p]
  change zeroAtom a ≤ (k.choose (k / 2) : ℝ≥0∞) / 2 ^ k
  rw [zeroAtom_eq_card, card_signSum_eq_support, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (2 : ℝ≥0∞) ^ r = 2 ^ k * 2 ^ m := by rw [hkm, pow_add]
  rw [hpow, ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]
  gcongr
  exact card_signSum_eq_le_ne_zero _ (fun i => i.2) 0

private theorem choose_middle_le_three_eighths {k : ℕ} (hk : 3 ≤ k) :
    8 * k.choose (k / 2) ≤ 3 * 2 ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => decide
  | succ j ih =>
    let n := 3 + j
    have hstep : (n + 1).choose ((n + 1) / 2) ≤ 2 * n.choose (n / 2) := by
      cases hm : (n + 1) / 2 with
      | zero =>
        rw [Nat.choose_zero_right]
        have := Nat.choose_pos (Nat.div_le_self n 2)
        omega
      | succ m =>
        rw [Nat.choose_succ_succ, two_mul]
        exact Nat.add_le_add (Nat.choose_le_middle _ _) (Nat.choose_le_middle _ _)
    have hi : 8 * n.choose (n / 2) ≤ 3 * 2 ^ n := ih
    change 8 * (n + 1).choose ((n + 1) / 2) ≤ 3 * 2 ^ (n + 1)
    rw [pow_succ]
    omega

open scoped Classical in
/-- A relation using at least three coordinates has atom at most `3/8`. -/
theorem zeroAtom_le_three_eighths (r : ℕ) (a : Fin r → ℝ)
    (h : 3 ≤ (Finset.univ.filter fun i => a i ≠ 0).card) : zeroAtom a ≤ 3 / 8 := by
  refine (zeroAtom_le_choose r a).trans ?_
  let k := (Finset.univ.filter fun i => a i ≠ 0).card
  change (k.choose (k / 2) : ℝ≥0∞) / 2 ^ k ≤ 3 / 8
  rw [ENNReal.div_le_iff_le_mul (by simp) (by simp), ← ENNReal.mul_div_right_comm,
    ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  exact_mod_cast (by simpa [mul_comm] using choose_middle_le_three_eighths h :
    k.choose (k / 2) * 8 ≤ 3 * 2 ^ k)

end BooleanThreshold
