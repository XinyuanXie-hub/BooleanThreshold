module

public import BooleanThreshold.DependenceEvents
public import BooleanThreshold.NonPairLargeAtom
public import BooleanThreshold.RankSelection
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section

open scoped ENNReal BigOperators Classical
open MeasureTheory ProbabilityTheory Module

namespace BooleanThreshold

/-- A square sign matrix in the Boolean row model. -/
abbrev BooleanSquareMatrix (r : ℕ) := Fin r → Fin r → Bool

/-- The event that some family of all but one row is linearly independent. -/
def someIndependentRows (r : ℕ) : Set (BooleanSquareMatrix (r + 1)) :=
  {v | ∃ i : Fin (r + 1), LinearIndependent ℝ (fun j => realSigns (Fin.removeNth i v j))}

/-- A square sign matrix admits a null relation of large support and large zero atom. -/
def squareLargeAtomEvent (r : ℕ) (cutoff : ℝ≥0∞) : Set (BooleanSquareMatrix r) :=
  {v | ∃ a, isLargeAtomVector cutoff a ∧ ∀ j, ∑ k, a k * realSigns (v j) k = 0}

/-- The null relation belongs to a prescribed structured set. -/
def structuredNullEvent (r : ℕ) (structured : Set (Fin r → ℝ)) : Set (BooleanSquareMatrix r) :=
  {v | ∃ a ∈ structured, ∀ j, ∑ k, a k * realSigns (v j) k = 0}

/-- Union bound over the row that is omitted in the one-dimensional kernel argument. -/
theorem squareLargeAtom_probability_le {r : ℕ} (cutoff : ℝ≥0∞) {corankError perRowError : ℝ}
    (hcorank : (uniformOn Set.univ).real (someIndependentRows r)ᶜ ≤ corankError)
    (hrow : ∀ i : Fin (r + 1),
      (uniformOn Set.univ).real (independentRowsLargeAtomEvent cutoff i) ≤ perRowError) :
    (uniformOn Set.univ).real (squareLargeAtomEvent (r + 1) cutoff) ≤
      corankError + (r + 1 : ℝ) * perRowError := by
  let μ : Measure (BooleanSquareMatrix (r + 1)) := uniformOn Set.univ
  let E := squareLargeAtomEvent (r + 1) cutoff
  let C := (someIndependentRows r)ᶜ
  let J := independentRowsLargeAtomEvent (r := r) cutoff
  have hcover : E ⊆ C ∪ ⋃ i, J i := by
    intro v hv
    by_cases hs : v ∈ someIndependentRows r
    · obtain ⟨i, hi⟩ := hs
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi, hv⟩)
    · exact Or.inl hs
  calc
    μ.real E ≤ μ.real (C ∪ ⋃ i, J i) := measureReal_mono hcover
    _ ≤ μ.real C + μ.real (⋃ i, J i) := measureReal_union_le _ _
    _ ≤ μ.real C + ∑ i, μ.real (J i) :=
      add_le_add (le_refl _) (measureReal_iUnion_fintype_le _)
    _ ≤ corankError + ∑ _i : Fin (r + 1), perRowError :=
      add_le_add hcorank (Finset.sum_le_sum fun i _ => hrow i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- Transfer the square high-atom event to the sign-column law of Theorem 7. -/
theorem signLaw_squareLargeAtom_probability (r : ℕ) (cutoff : ℝ≥0∞) :
    (signLaw r r).real {v | ∃ a, isLargeAtomVector cutoff a ∧ ∀ j, ∑ k, a k * v k j = 0} =
      (uniformOn Set.univ).real (squareLargeAtomEvent r cutoff) := by
  let E : Set (Fin r → Fin r → ℝ) := {v | ∃ a, isLargeAtomVector cutoff a ∧ ∀ j, ∑ k, a k * v j k = 0}
  change (signLaw r r).real ((fun v j k => v k j) ⁻¹' E) = _
  rw [measureReal_def, signLaw_transpose, ← measureReal_def, signLaw_real_apply]
  rfl

/-- Equal or opposite columns in the row model of a square sign matrix. -/
def squarePairEvent (r : ℕ) : Set (BooleanSquareMatrix r) :=
  {v | pairCollision (fun i j => realSigns (v j) i)}

theorem squarePair_probability (r : ℕ) :
    (uniformOn Set.univ).real (squarePairEvent r) = (signLaw r r).real {v | pairCollision v} := by
  let e := Equiv.piComm (fun (_ : Fin r) (_ : Fin r) => Bool)
  let P : Set (BooleanSquareMatrix r) := {v | pairCollision (fun i => realSigns (v i))}
  have hmap := map_uniformOn_univ_of_equiv e
  have hpre := congrArg (fun μ : Measure (BooleanSquareMatrix r) => μ P) hmap
  rw [Measure.map_apply (measurable_of_finite e) P.toFinite.measurableSet] at hpre
  rw [signLaw_real_apply, measureReal_def, measureReal_def]
  change (uniformOn Set.univ (e ⁻¹' P)).toReal = (uniformOn Set.univ P).toReal
  rw [hpre]

private theorem pairCollision_exists_support_two {n r : ℕ} {v : Fin r → Fin n → ℝ}
    (h : pairCollision v) : ∃ a : Fin r → ℝ,
      (Finset.univ.filter fun k => a k ≠ 0).card = 2 ∧ ∑ k, a k • v k = 0 := by
  obtain ⟨i, j, hij, hpair⟩ := h
  obtain ⟨t, ht, htV⟩ : ∃ t : ℝ, t ≠ 0 ∧ v i = t • v j := by
    rcases hpair with h | h
    · exact ⟨1, by simp, by simpa using h⟩
    · exact ⟨-1, by simp, by simpa using h⟩
  let a (k : Fin r) : ℝ := if k = i then 1 else if k = j then -t else 0
  have hsupport : (Finset.univ.filter fun k => a k ≠ 0) = {i, j} := by
    ext k
    by_cases hki : k = i
    · simp [a, hki]
    · simp [a, hki, ht]
  refine ⟨a, by simp [hsupport, hij.ne], ?_⟩
  have hsum : ∑ k ∈ {i, j}, a k • v k = ∑ k, a k • v k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hnot
    have hk : a k = 0 := by
      by_contra hk
      exact hnot (hsupport ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    rw [hk, zero_smul]
  rw [← hsum, Finset.sum_pair hij.ne, htV]
  simp [a, hij.ne', neg_smul]

private theorem support_card_smul {r : ℕ} (a : Fin r → ℝ) {t : ℝ} (ht : t ≠ 0) :
    (Finset.univ.filter fun k => (t • a) k ≠ 0).card =
      (Finset.univ.filter fun k => a k ≠ 0).card := by
  simp [Pi.smul_apply, smul_eq_mul, ht]

private theorem disjoint_pair_independentRowsLargeAtom {r : ℕ} (cutoff : ℝ≥0∞)
    (i : Fin (r + 1)) :
    Disjoint (squarePairEvent (r + 1)) (independentRowsLargeAtomEvent cutoff i) := by
  rw [Set.disjoint_left]
  intro v hpair hJ
  obtain ⟨a, ha2, ha⟩ := pairCollision_exists_support_two hpair
  have han : a ≠ 0 := by
    rintro rfl
    simp at ha2
  have ha' := sum_smul_eq_zero_iff.mp ha
  obtain ⟨hind, b, hb, hb'⟩ := hJ
  obtain ⟨t, ht, rfl⟩ := exists_nonzero_scalar_of_common_null
    (fun j => realSigns (Fin.removeNth i v j)) hind han hb.ne_zero
    (fun j => ha' (i.succAbove j)) (fun j => hb' (i.succAbove j))
  have hc := hb.1
  rw [support_card_smul a ht, ha2] at hc
  exact (Nat.lt_irrefl 2) hc

private theorem squarePairEvent_subset_structuredNullEvent {r : ℕ}
    {structured : Set (Fin r → ℝ)}
    (hS : ∀ a : Fin r → ℝ, (Finset.univ.filter fun k => a k ≠ 0).card = 2 →
      ∃ t : ℝ, t ≠ 0 ∧ t • a ∈ structured) :
    squarePairEvent r ⊆ structuredNullEvent r structured := by
  intro v hv
  obtain ⟨a, ha2, ha⟩ := pairCollision_exists_support_two hv
  obtain ⟨t, _, ht⟩ := hS a ha2
  refine ⟨t • a, ht, ?_⟩
  have ha' := sum_smul_eq_zero_iff.mp ha
  intro j
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ha' j, mul_zero]

/-- Structured long relations at rank one below full rank can be bounded by
subtracting the known pair contribution from the total structured probability. -/
theorem structured_largeAtom_probability_le {r : ℕ} (cutoff : ℝ≥0∞) (i : Fin (r + 1))
    (structured : Set (Fin (r + 1) → ℝ))
    (hS : ∀ a : Fin (r + 1) → ℝ, (Finset.univ.filter fun k => a k ≠ 0).card = 2 →
      ∃ t : ℝ, t ≠ 0 ∧ t • a ∈ structured)
    {main structuredError pairError : ℝ}
    (htotal : (uniformOn Set.univ).real (structuredNullEvent (r + 1) structured) ≤
      main + structuredError)
    (hpair : main - pairError ≤ (uniformOn Set.univ).real (squarePairEvent (r + 1))) :
    (uniformOn Set.univ).real (independentRowsLargeAtomEvent cutoff i ∩
        structuredNullEvent (r + 1) structured) ≤ structuredError + pairError := by
  let μ : Measure (BooleanSquareMatrix (r + 1)) := uniformOn Set.univ
  let F := squarePairEvent (r + 1)
  let S := structuredNullEvent (r + 1) structured
  let G := independentRowsLargeAtomEvent cutoff i ∩ S
  have hdisj : Disjoint F G :=
    (disjoint_pair_independentRowsLargeAtom cutoff i).mono_right Set.inter_subset_left
  have hP : F ⊆ S := squarePairEvent_subset_structuredNullEvent hS
  have hle : μ.real (F ∪ G) ≤ main + structuredError :=
    (measureReal_mono (Set.union_subset hP Set.inter_subset_right)).trans htotal
  rw [measureReal_union hdisj G.toFinite.measurableSet] at hle
  change μ.real G ≤ _
  change main - pairError ≤ μ.real F at hpair
  linarith only [hle, hpair]

/-- Failure to find an independent all-but-one row family is exactly the
event of row corank at least two. -/
theorem compl_someIndependentRows_eq (r : ℕ) :
    (someIndependentRows r)ᶜ = {v | finrank ℝ
      (Submodule.span ℝ (Set.range (fun i : Fin (r + 1) => realSigns (v i)))) < r} := by
  ext v
  let rows : Fin (r + 1) → Fin (r + 1) → ℝ := fun i => realSigns (v i)
  let W := Submodule.span ℝ (Set.range rows)
  change (¬ ∃ i : Fin (r + 1), LinearIndependent ℝ (rows ∘ i.succAbove)) ↔ finrank ℝ W < r
  constructor
  · intro h
    by_contra! hge
    have hle : finrank ℝ W ≤ r + 1 := by
      simpa [W, Set.finrank] using finrank_range_le_card (R := ℝ) rows
    rcases (show finrank ℝ W = r ∨ finrank ℝ W = r + 1 by omega) with hdim | hdim
    · exact h (exists_succAbove_linearIndependent_of_finrank_eq rows hdim)
    · have hind : LinearIndependent ℝ rows := by
        apply linearIndependent_iff_card_eq_finrank_span.mpr
        simpa [W, Set.finrank] using hdim.symm
      exact h ⟨0, hind.comp _ (fun _ _ h => Fin.succAbove_right_injective h)⟩
  · rintro hlt ⟨i, hi⟩
    have hdim := finrank_span_eq_card hi
    rw [Fintype.card_fin] at hdim
    have hsub :
        Submodule.span ℝ (Set.range (rows ∘ i.succAbove)) ≤ W :=
      Submodule.span_mono (Set.range_comp_subset_range _ _)
    have hle := Submodule.finrank_mono hsub
    omega

/-- Combine the corank, structured-matrix and conditional row estimates for
the square large-atom bound. -/
theorem squareLargeAtom_probability_le_of_concentration {r : ℕ} (cutoff : ℝ≥0∞)
    (normal : (Fin r → Fin (r + 1) → Bool) → Fin (r + 1) → ℝ)
    (hnz : ∀ A, normal A ≠ 0)
    (horth : ∀ A j, ∑ k, normal A k * realSigns (A j) k = 0)
    (structured : Set (Fin (r + 1) → ℝ))
    (hS : ∀ a : Fin (r + 1) → ℝ, (Finset.univ.filter fun k => a k ≠ 0).card = 2 →
      ∃ t : ℝ, t ≠ 0 ∧ t • a ∈ structured)
    (exceptional : Set (Fin r → Fin (r + 1) → Bool))
    (window : Set (Fin (r + 1) → Bool))
    {θ : ℝ≥0∞} (hθ : θ ≤ 1 / 2) (hW : 1 / 2 ≤ uniformOn Set.univ window)
    (hcomparison : ∀ A ∉ exceptional, normal A ∉ structured →
      uniformOn Set.univ {b | (∑ k, normal A k * realSigns b k = 0) ∧ b ∈ window} ≤
        θ * uniformOn Set.univ window * cutoff)
    {main corankError exceptionError structuredError pairError : ℝ}
    (hcorank : (uniformOn Set.univ).real
      {v : BooleanSquareMatrix (r + 1) |
        finrank ℝ (Submodule.span ℝ (Set.range (fun i => realSigns (v i)))) < r} ≤ corankError)
    (hexcept : (uniformOn Set.univ).real exceptional ≤ exceptionError)
    (htotal : (uniformOn Set.univ).real (structuredNullEvent (r + 1) structured) ≤
      main + structuredError)
    (hpair : main - pairError ≤ (uniformOn Set.univ).real (squarePairEvent (r + 1))) :
    (uniformOn Set.univ).real (squareLargeAtomEvent (r + 1) cutoff) ≤
      corankError + (r + 1 : ℝ) * (2 * exceptionError + 4 * (structuredError + pairError)) := by
  refine squareLargeAtom_probability_le cutoff (by rwa [compl_someIndependentRows_eq]) ?_
  intro i
  have hJ := independentRowsLargeAtom_probability_le cutoff i normal hnz horth structured
    exceptional window hθ hW hcomparison
  have hstructured := structured_largeAtom_probability_le cutoff i structured hS htotal hpair
  have hsub :
      {v | v ∈ independentRowsLargeAtomEvent cutoff i ∧
        ∃ a ∈ structured, isLargeAtomVector cutoff a ∧
          ∀ j, ∑ k, a k * realSigns (v j) k = 0} ⊆
      independentRowsLargeAtomEvent cutoff i ∩ structuredNullEvent (r + 1) structured := by
    rintro v ⟨hv, a, ha, _, hz⟩
    exact ⟨hv, a, ha, hz⟩
  have hbound := (measureReal_mono (μ := uniformOn Set.univ) hsub).trans hstructured
  linarith only [hJ, hexcept, hbound]

end BooleanThreshold
