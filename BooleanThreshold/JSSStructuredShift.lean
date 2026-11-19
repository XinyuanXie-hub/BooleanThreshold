module

public import BooleanThreshold.JSSStructuredProjection

@[expose] public section

open scoped BigOperators

namespace BooleanThreshold

/-- A column difference divided by two, as recovered from its code. -/
def differenceSign (d : Option Bool) : ℤ :=
  d.elim 0 (fun b => if b then 1 else -1)

/-- Integer shifts introduced in the smaller square after eliminating the
difference column using its nonzero pivot. -/
def differenceProjectionShift {n : ℕ} (d : Fin (n + 2) → Option Bool)
    (p : Fin (n + 2)) (y : Fin n → Bool) : Fin (n + 1) → Fin (n + 1) → ℤ :=
  fun r => Fin.cons (if d (p.succAbove r) = none then 0 else -1)
    (fun j : Fin n => -(differenceSign (d (p.succAbove r)) * differenceSign (d p)) *
      (if y j then 1 else -1))

private noncomputable def collapsedRow {n : ℕ} (x : Fin (n + 2) → Bool) : Fin (n + 1) → ℝ :=
  Fin.cons ((realSigns x 0 + realSigns x (0 : Fin (n + 1)).succ) / 2)
    (fun j : Fin n => realSigns x j.succ.succ)

private theorem differenceSign_eq {n : ℕ} (x : Fin (n + 2) → Bool) :
    realSigns x 0 - realSigns x (0 : Fin (n + 1)).succ =
      2 * (differenceSign (differenceCode (x 0) (x (0 : Fin (n + 1)).succ)) : ℝ) := by
  cases h₁ : x 0 <;> cases h₂ : x (1 : Fin (n + 2)) <;>
    norm_num [realSigns, differenceCode, differenceSign, h₁, h₂]

private theorem collapsedRow_first {n : ℕ} (x : Fin (n + 2) → Bool) :
    collapsedRow x 0 = if differenceCode (x 0) (x (0 : Fin (n + 1)).succ) = none
      then realSigns x 0 else 0 := by
  cases h₁ : x 0 <;> cases h₂ : x (1 : Fin (n + 2)) <;>
    norm_num [collapsedRow, realSigns, differenceCode, h₁, h₂]

private theorem shifted_projection_row {n : ℕ} {d : Fin (n + 2) → Option Bool}
    {p : Fin (n + 2)} (hp : d p ≠ none)
    (M : {M : Fin (n + 2) → Fin (n + 2) → Bool // firstDifferencePattern M = d})
    (r : Fin (n + 1)) (j : Fin (n + 1)) :
    realSigns ((differencePatternEquiv d p hp M).2.val r) j +
        (differenceProjectionShift d p (differencePatternEquiv d p hp M).1 r j : ℝ) =
      collapsedRow (M.val (p.succAbove r)) j -
        (differenceSign (d (p.succAbove r)) : ℝ) * (differenceSign (d p) : ℝ) *
          collapsedRow (M.val p) j := by
  have hcode (k : Fin (n + 2)) : differenceCode (M.val k 0)
      (M.val k (0 : Fin (n + 1)).succ) = d k := congrFun M.prop k
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [collapsedRow_first, collapsedRow_first, hcode, hcode, ite_eq_right hp]
    by_cases hr : d (p.succAbove r) = none
    · simp [differencePatternEquiv, differenceProjectionShift, differenceSign, hr, realSigns]
    · simp [differencePatternEquiv, differenceProjectionShift, hr, realSigns]
  · cases hy : M.val p k.succ.succ <;>
      simp [differencePatternEquiv, differenceProjectionShift, collapsedRow, realSigns, hy,
        Int.cast_mul, sub_eq_add_neg]

private theorem collapsedRow_dot {n : ℕ} (x : Fin (n + 2) → Bool) (b : Fin (n + 2) → ℝ)
    (hb : b 0 = b (0 : Fin (n + 1)).succ) :
    (∑ j : Fin (n + 1), (Fin.cons (α := fun _ => ℝ) (2 * b 0) (fun i : Fin n => b i.succ.succ) j) *
      collapsedRow x j) = ∑ j : Fin (n + 2), b j * realSigns x j := by
  rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [collapsedRow, Fin.cons_zero, Fin.cons_succ]
  rw [← hb]
  ring

/-- A nonzero first-column difference in the span of the collapsed columns
forces a nonzero null vector in the shifted square from pivot elimination. -/
theorem shifted_projection_has_null {n : ℕ} {d : Fin (n + 2) → Option Bool}
    {p : Fin (n + 2)} (hp : d p ≠ none)
    (M : {M : Fin (n + 2) → Fin (n + 2) → Bool // firstDifferencePattern M = d})
    (hspan : signMatrixMap M.val (Pi.single 0 1 - Pi.single (0 : Fin (n + 1)).succ 1) ∈
      (equalCoefficientSubspace 0 (0 : Fin (n + 1)).succ).map (signMatrixMap M.val)) :
    ∃ a : Fin (n + 1) → ℝ, a ≠ 0 ∧ ∀ r,
      ∑ j, a j * (realSigns ((differencePatternEquiv d p hp M).2.val r) j +
        (differenceProjectionShift d p (differencePatternEquiv d p hp M).1 r j : ℝ)) = 0 := by
  obtain ⟨b, hb, hbmap⟩ := hspan
  have hb0 : b 0 = b (0 : Fin (n + 1)).succ := by
    change b 0 - b (0 : Fin (n + 1)).succ = 0 at hb
    exact sub_eq_zero.mp hb
  let a : Fin (n + 1) → ℝ := Fin.cons (2 * b 0) (fun j : Fin n => b j.succ.succ)
  have hdot (r : Fin (n + 2)) :
      (∑ j, a j * collapsedRow (M.val r) j) = 2 * (differenceSign (d r) : ℝ) := by
    calc
      _ = signMatrixMap M.val b r := by
        rw [signMatrixMap_apply]
        exact collapsedRow_dot (M.val r) b hb0
      _ = signMatrixMap M.val (Pi.single 0 1 - Pi.single (0 : Fin (n + 1)).succ 1) r :=
        congrFun hbmap r
      _ = _ := by
        rw [map_sub, Pi.sub_apply, signMatrixMap_basis, signMatrixMap_basis,
          differenceSign_eq, ← congrFun M.prop r]
        rfl
  have hdp : (differenceSign (d p) : ℝ) ^ 2 = 1 := by
    cases h : d p with
    | none => exact (hp h).elim
    | some x => cases x <;> norm_num [differenceSign, h]
  have ha : a ≠ 0 := by
    intro ha
    have hz := hdot p
    simp [ha] at hz
    simp [hz] at hdp
  refine ⟨a, ha, fun r => ?_⟩
  simp_rw [shifted_projection_row hp M r]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hm : (∑ j, a j * ((differenceSign (d (p.succAbove r)) : ℝ) *
      (differenceSign (d p) : ℝ) * collapsedRow (M.val p) j)) =
      ((differenceSign (d (p.succAbove r)) : ℝ) * (differenceSign (d p) : ℝ)) *
        ∑ j, a j * collapsedRow (M.val p) j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hm, hdot, hdot]
  calc
    _ = 2 * (differenceSign (d (p.succAbove r)) : ℝ) *
        (1 - (differenceSign (d p) : ℝ) ^ 2) := by ring
    _ = _ := by rw [hdp, sub_self, mul_zero]

end BooleanThreshold
