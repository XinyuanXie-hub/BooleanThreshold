module

public import BooleanThreshold.JSSConditionalPairShiftIntervals

public section

open Finset
open scoped BigOperators Classical

namespace BooleanThreshold

/-- Split an array into its selected coordinates and the complementary coordinates. -/
@[expose] noncomputable def splitCoordinates {ι κ α : Type*} (e : κ ↪ ι) :
    (ι → α) ≃ (κ → α) × ({i : ι // i ∉ Set.range e} → α) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ Set.range e) (fun _ => α)).trans
    (Equiv.prodCongr (Equiv.piCongrLeft (fun _ => α) (Equiv.ofInjective e e.injective)).symm
      (Equiv.refl _))

@[simp]
theorem splitCoordinates_fst {ι κ α : Type*} (e : κ ↪ ι) (x : ι → α) (j : κ) :
    (splitCoordinates e x).1 j = x (e j) :=
  rfl

@[simp]
theorem splitCoordinates_snd {ι κ α : Type*} (e : κ ↪ ι) (x : ι → α)
    (j : {i : ι // i ∉ Set.range e}) :
    (splitCoordinates e x).2 j = x j :=
  rfl

theorem map_piFinset_splitCoordinates {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : ι → Finset α) (e : κ ↪ ι) :
    (Fintype.piFinset B).map (splitCoordinates (α := α) e).toEmbedding =
      (Fintype.piFinset (fun j : κ => B (e j))).product
        (Fintype.piFinset (fun j : {i : ι // i ∉ Set.range e} => B j)) := by
  let f := splitCoordinates (α := α) e
  have h (x : ι → α) : x ∈ Fintype.piFinset B ↔
      f x ∈ (Fintype.piFinset (fun j : κ => B (e j))).product
        (Fintype.piFinset (fun j : {i : ι // i ∉ Set.range e} => B j)) := by
    simp only [product_eq_sprod, mem_product, Fintype.mem_piFinset, f,
      splitCoordinates_fst, splitCoordinates_snd]
    refine ⟨fun hx => ⟨fun j => hx (e j), fun j => hx j⟩, fun hx i => ?_⟩
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      exact hx.1 j
    · exact hx.2 ⟨i, hi⟩
  ext x
  rw [mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).mp hy
  · intro hx
    refine ⟨f.symm x, (h (f.symm x)).mpr ?_, f.apply_symm_apply x⟩
    rwa [f.apply_symm_apply]

/-- A uniform count on the selected coordinate grids lifts to the full
grid when the same bound holds at each choice of complementary coordinates. -/
theorem card_filter_piFinset_le_of_coordinate_sections {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : ι → Finset α) (e : κ ↪ ι) (P : (ι → α) → Prop) {C : ℝ}
    (h : ∀ y ∈ Fintype.piFinset (fun j : {i : ι // i ∉ Set.range e} => B j),
      (((Fintype.piFinset (fun j : κ => B (e j))).filter
        (fun x => P ((splitCoordinates e).symm (x, y)))).card : ℝ) ≤
        C * ((Fintype.piFinset (fun j : κ => B (e j))).card : ℝ)) :
    (((Fintype.piFinset B).filter P).card : ℝ) ≤ C * ((Fintype.piFinset B).card : ℝ) := by
  let f := splitCoordinates (α := α) e
  let T := Fintype.piFinset B
  let X := Fintype.piFinset (fun j : κ => B (e j))
  let Y := Fintype.piFinset (fun j : {i : ι // i ∉ Set.range e} => B j)
  have hT : T.map f.toEmbedding = X.product Y := map_piFinset_splitCoordinates B e
  let Q (xy : (κ → α) × ({i : ι // i ∉ Set.range e} → α)) := P (f.symm xy)
  let E := (X.product Y).filter Q
  let E_y (y : {i : ι // i ∉ Set.range e} → α) := X.filter (fun x => Q (x, y))
  have hE : (T.filter P).map f.toEmbedding = E := by
    rw [Finset.map_filter, hT]
    rfl
  have hCover : E ⊆ Y.biUnion (fun y => (E_y y).image (fun x => (x, y))) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hxy, hP⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    exact mem_biUnion.mpr ⟨y, hy, mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, hP⟩, rfl⟩⟩
  have hSize : (E.card : ℝ) ≤ ∑ y ∈ Y, ((E_y y).card : ℝ) := by
    exact_mod_cast (card_le_card hCover).trans
      (card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le)))
  have hProd : X.card * Y.card = T.card := by
    rw [← card_product]
    change (X.product Y).card = T.card
    rw [← hT, card_map]
  calc
    _ = (E.card : ℝ) := by rw [← hE, card_map]
    _ ≤ ∑ y ∈ Y, ((E_y y).card : ℝ) := hSize
    _ ≤ ∑ _y ∈ Y, C * (X.card : ℝ) := sum_le_sum h
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, mul_comm (Y.card : ℝ), mul_assoc, ← Nat.cast_mul, hProd]

/-- The second coordinates of the mixed pairs are distinct. -/
@[expose] noncomputable def mixedPairSecondEmbedding {n k : ℕ}
    (e : Fin k × Bool ↪ Fin n) (b : Fin n → Bool) : Fin (mixedPairIndices e b).card ↪ Fin n :=
  (mixedPairEmbedding e b).trans
    ⟨fun i => e (i, true), fun i j h => congrArg Prod.fst (e.injective h)⟩

theorem first_not_mem_range_mixedPairSecondEmbedding {n k : ℕ}
    (e : Fin k × Bool ↪ Fin n) (b : Fin n → Bool) (i : Fin k) :
    e (i, false) ∉ Set.range (mixedPairSecondEmbedding e b) := by
  rintro ⟨j, hj⟩
  have he : e (mixedPairEmbedding e b j, true) = e (i, false) := hj
  have hb : true = false := congrArg Prod.snd (e.injective he)
  cases hb

/-- A uniform count on the independent shifted intervals bounds the number
of full coefficient arrays, after the first coordinate of each pair is fixed. -/
theorem card_filter_piFinset_le_of_mixed_shift_sections {n k : ℕ}
    (e : Fin k × Bool ↪ Fin n) (b : Fin n → Bool) (B : Fin n → Finset ℤ)
    (P : (Fin (mixedPairIndices e b).card → ℤ) → Prop) {C : ℝ}
    (h : ∀ fixed : Fin (mixedPairIndices e b).card → ℤ,
      (((Fintype.piFinset fun i =>
        (B (e (mixedPairEmbedding e b i, true))).map
          (pairedShiftEquiv (b (e (mixedPairEmbedding e b i, false))) (fixed i)).toEmbedding).filter P).card : ℝ)
        ≤ C * ((Fintype.piFinset (fun i : Fin (mixedPairIndices e b).card =>
          B (e (mixedPairEmbedding e b i, true)))).card : ℝ)) :
    (((Fintype.piFinset B).filter (fun a => P (fun i => pairedSubsetShift e a b (mixedPairEmbedding e b i)))).card
      : ℝ) ≤ C * ((Fintype.piFinset B).card : ℝ) := by
  let d := (mixedPairIndices e b).card
  let q := mixedPairSecondEmbedding e b
  let g (i : Fin d) := e (mixedPairEmbedding e b i, false)
  let G (i : Fin d) : {j : Fin n // j ∉ Set.range q} :=
    ⟨g i, first_not_mem_range_mixedPairSecondEmbedding e b _⟩
  let H (i : Fin d) := b (g i)
  apply card_filter_piFinset_le_of_coordinate_sections B q
  intro y _
  let fixed (i : Fin d) := y (G i)
  have he (x : Fin d → ℤ) (i : Fin d) :
      pairedSubsetShift e ((splitCoordinates q).symm (x, y)) b (mixedPairEmbedding e b i) =
        pairedShiftEquiv (H i) (fixed i) (x i) := by
    rw [pairedSubsetShift_eq_pairedShiftEquiv]
    let a := (splitCoordinates q).symm (x, y)
    have hleft : a (g i) = y (G i) := by
      have hh := congrArg (fun z => z.2 (G i)) ((splitCoordinates q).apply_symm_apply (x, y))
      change (splitCoordinates q a).2 (G i) = y (G i) at hh
      rwa [splitCoordinates_snd] at hh
    have hright : a (q i) = x i := by
      have hh := congrArg (fun z => z.1 i) ((splitCoordinates q).apply_symm_apply (x, y))
      change (splitCoordinates q a).1 i = x i at hh
      rwa [splitCoordinates_fst] at hh
    change pairedShiftEquiv (H i) (a (g i)) (a (q i)) = _
    rw [hleft, hright]
  simp_rw [he]
  rw [card_filter_piFinset_pairedShiftEquiv H fixed (fun i => B (q i)) P]
  exact h fixed

end BooleanThreshold
