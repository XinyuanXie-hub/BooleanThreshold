module

public import BooleanThreshold.JSSStructuredPairs
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

/-- The difference code of the first two columns in every row. -/
def firstDifferencePattern {n : ℕ} (M : Fin (n + 2) → Fin (n + 2) → Bool) :
    Fin (n + 2) → Option Bool :=
  fun r => differenceCode (M r 0) (M r (0 : Fin (n + 1)).succ)

/-- Square Boolean matrices after removing a pivot row and merging two
columns. Fix the first bit at each remaining nonzero difference. -/
def fixedProjectionBits {n : ℕ} (d : Fin (n + 2) → Option Bool) (p : Fin (n + 2))
    (X : Fin (n + 1) → Fin (n + 1) → Bool) : Prop :=
  ∀ r, d (p.succAbove r) ≠ none → X r 0 = true

def fillDifferenceRow {n : ℕ} (d : Option Bool) (b : Bool) (tail : Fin n → Bool) :
    Fin (n + 2) → Bool :=
  Fin.cons (d.getD b) (Fin.cons (d.elim b (! ·)) tail)

private theorem differenceCode_fill_row {n : ℕ} (d : Option Bool) (b : Bool)
    (tail : Fin n → Bool) :
    differenceCode (fillDifferenceRow d b tail 0)
      (fillDifferenceRow d b tail (0 : Fin (n + 1)).succ) = d := by
  cases d with
  | none => simp [fillDifferenceRow, differenceCode]
  | some x => cases x <;> simp [fillDifferenceRow, differenceCode]

private theorem fill_row_original {n : ℕ} (row : Fin (n + 2) → Bool) :
    fillDifferenceRow
      (differenceCode (row 0) (row (0 : Fin (n + 1)).succ))
      (row 0) (fun j : Fin n => row j.succ.succ) = row := by
  funext j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) j
  · cases h₁ : row 0 <;> cases h₂ : row (0 : Fin (n + 1)).succ <;>
      simp_all [fillDifferenceRow, differenceCode]
  · cases h₁ : row 0 <;> cases h₂ : row (0 : Fin (n + 1)).succ <;>
      simp_all [fillDifferenceRow, differenceCode]
  · simp [fillDifferenceRow]

private theorem fill_row_code {n : ℕ} (row : Fin (n + 2) → Bool) (d : Option Bool)
    (h : differenceCode (row 0) (row (0 : Fin (n + 1)).succ) = d) :
    fillDifferenceRow d (if d = none then row 0 else true)
      (fun j : Fin n => row j.succ.succ) = row := by
  have hrow := fill_row_original row
  rw [h] at hrow
  cases d <;> simpa [fillDifferenceRow] using hrow

/-- A fixed difference pattern leaves the entries of the pivot row outside
the first two columns, plus the bits in the smaller square subject only to
one fixed entry for each nonpivot mismatch. -/
def differencePatternEquiv {n : ℕ} (d : Fin (n + 2) → Option Bool)
    (p : Fin (n + 2)) (hp : d p ≠ none) :
    {M : Fin (n + 2) → Fin (n + 2) → Bool // firstDifferencePattern M = d} ≃
      (Fin n → Bool) × {X : Fin (n + 1) → Fin (n + 1) → Bool // fixedProjectionBits d p X} where
  toFun M := (fun j => M.val p j.succ.succ,
    ⟨fun r => Fin.cons (if d (p.succAbove r) = none then M.val (p.succAbove r) 0 else true)
      (fun j : Fin n => M.val (p.succAbove r) j.succ.succ),
      fun r hr => by simp [hr]⟩)
  invFun X := ⟨Fin.insertNth p (fillDifferenceRow (d p) true X.1)
    (fun r => fillDifferenceRow (d (p.succAbove r)) (X.2.val r 0)
      (fun j : Fin n => X.2.val r j.succ)), by
        apply funext
        rw [p.forall_iff_succAbove]
        constructor
        · simp only [firstDifferencePattern, Fin.insertNth_apply_same]
          exact differenceCode_fill_row (d p) true X.1
        · intro r
          simp only [firstDifferencePattern, Fin.insertNth_apply_succAbove]
          exact differenceCode_fill_row (d (p.succAbove r)) (X.2.val r 0)
            (fun j => X.2.val r j.succ)⟩
  left_inv M := by
    apply Subtype.ext
    apply funext
    rw [p.forall_iff_succAbove]
    have hrow (r : Fin (n + 2)) :=
      fill_row_code (M.val r) (d r) (congrFun M.prop r)
    exact ⟨by simpa [hp] using hrow p, fun j => by simpa using hrow (p.succAbove j)⟩
  right_inv X := by
    apply Prod.ext
    · funext j
      simp [fillDifferenceRow]
    · apply Subtype.ext
      funext r j
      refine Fin.cases ?_ (fun k => ?_) j
      · by_cases hr : d (p.succAbove r) = none
        · simp [hr, fillDifferenceRow]
        · simp [hr, X.2.prop r hr]
      · simp [fillDifferenceRow]

end BooleanThreshold
