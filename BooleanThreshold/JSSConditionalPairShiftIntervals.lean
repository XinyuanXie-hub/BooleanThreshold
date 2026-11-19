module

public import BooleanThreshold.JSSConditionalPairSmoothing
public import Mathlib.Data.Int.Interval
import Mathlib.Logic.Equiv.Basic

public section

open Finset
open scoped BigOperators Classical

namespace BooleanThreshold

/-- The shift as a function of the second coefficient when the first is fixed. -/
@[expose] def pairedShiftEquiv (useFirst : Bool) (a : ℤ) : ℤ ≃ ℤ :=
  if useFirst then Equiv.subRight a else Equiv.subLeft a

theorem pairedSubsetShift_eq_pairedShiftEquiv {n k : ℕ}
    (e : Fin k × Bool ↪ Fin n) (a : Fin n → ℤ) (b : Fin n → Bool) (i : Fin k) :
    pairedSubsetShift e a b i =
      pairedShiftEquiv (b (e (i, false))) (a (e (i, false))) (a (e (i, true))) := by
  cases h : b (e (i, false)) <;> simp [pairedSubsetShift, pairedShiftEquiv, h]

/-- Conditioning on the first coefficient translates or reverses each
integer interval of values for the second coefficient. -/
theorem map_Ico_pairedShiftEquiv (useFirst : Bool) (a l u : ℤ) :
    (Ico l u).map (pairedShiftEquiv useFirst a).toEmbedding =
      if useFirst then Ico (l - a) (u - a) else Ico (a - u + 1) (a - l + 1) := by
  ext y
  rw [mem_map]
  cases useFirst
  · simp only [pairedShiftEquiv, Bool.false_eq_true, ite_false, mem_Ico, Equiv.toEmbedding_apply,
      Equiv.subLeft_apply]
    constructor
    · rintro ⟨x, h, rfl⟩
      omega
    · intro h
      exact ⟨a - y, by omega, by omega⟩
  · simp only [pairedShiftEquiv, ite_true, mem_Ico, Equiv.toEmbedding_apply, Equiv.subRight_apply]
    constructor
    · rintro ⟨x, h, rfl⟩
      omega
    · intro h
      exact ⟨y + a, by omega, by omega⟩

/-- The componentwise shift equivalences map the full coefficient grid
onto the grid of shifted intervals. -/
theorem map_piFinset_pairedShiftEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (useFirst : ι → Bool) (a : ι → ℤ) (B : ι → Finset ℤ) :
    (Fintype.piFinset B).map
        (Equiv.piCongrRight fun i => pairedShiftEquiv (useFirst i) (a i)).toEmbedding =
      Fintype.piFinset (fun i => (B i).map (pairedShiftEquiv (useFirst i) (a i)).toEmbedding) := by
  let e (i : ι) := pairedShiftEquiv (useFirst i) (a i)
  ext y
  simp only [mem_map, Fintype.mem_piFinset, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact ⟨x i, hx i, rfl⟩
  · intro hy
    refine ⟨fun i => (e i).symm (y i), fun i => ?_, ?_⟩
    · obtain ⟨x, hx, hxy⟩ := hy i
      change e i x = y i at hxy
      change (e i).symm (y i) ∈ B i
      rw [← hxy, Equiv.symm_apply_apply]
      exact hx
    · funext i
      exact (e i).apply_symm_apply (y i)

/-- As a result, the proportion of coefficient choices with a shift
property is the proportion of the corresponding translated grid. -/
theorem card_filter_piFinset_pairedShiftEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (useFirst : ι → Bool) (a : ι → ℤ) (B : ι → Finset ℤ) (P : (ι → ℤ) → Prop) :
    ((Fintype.piFinset B).filter (fun x => P (fun i => pairedShiftEquiv (useFirst i) (a i) (x i)))).card =
      ((Fintype.piFinset (fun i => (B i).map (pairedShiftEquiv (useFirst i) (a i)).toEmbedding)).filter P).card := by
  let e : (ι → ℤ) ≃ (ι → ℤ) := Equiv.piCongrRight (fun i => pairedShiftEquiv (useFirst i) (a i))
  change ((Fintype.piFinset B).filter (P ∘ e)).card = _
  rw [← map_piFinset_pairedShiftEquiv useFirst a B]
  have he : ((Fintype.piFinset B).filter (P ∘ e)).map e.toEmbedding =
      ((Fintype.piFinset B).map e.toEmbedding).filter P := by
    ext y
    simp only [mem_map, mem_filter, Function.comp_apply, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hp⟩
    · rintro ⟨⟨x, hx, rfl⟩, hp⟩
      exact ⟨x, ⟨hx, hp⟩, rfl⟩
  rw [← show e.toEmbedding = (Equiv.piCongrRight fun i => pairedShiftEquiv (useFirst i) (a i)).toEmbedding from rfl,
    ← he, card_map]

end BooleanThreshold
