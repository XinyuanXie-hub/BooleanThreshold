module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.MeasureTheory.Constructions.Pi

public section

open scoped ENNReal BigOperators
open MeasureTheory Module

namespace BooleanThreshold

/-- If the rows have a common nonzero null vector, at most `dim V - 1` of
the rows suffice to span them all. Extra rows can be selected to reach this size. -/
private theorem exists_spanning_rows
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {m : ℕ} (rows : Fin m → Module.Dual K V)
    (hm : finrank K V - 1 ≤ m) {a : V} (ha : a ≠ 0) (hzero : ∀ i, rows i a = 0) :
    ∃ I : Finset (Fin m), I.card = finrank K V - 1 ∧
      Submodule.span K (rows '' (I : Set (Fin m))) = Submodule.span K (Set.range rows) := by
  classical
  obtain ⟨κ, e, he, hspan, hind⟩ := exists_linearIndependent' K rows
  let : Fintype κ := Fintype.ofInjective e he
  let I₀ : Finset (Fin m) := Finset.univ.map ⟨e, he⟩
  have hI₀ : Set.range (rows ∘ e) = rows '' (I₀ : Set (Fin m)) := by
    ext x
    simp [I₀, Function.comp_def, Set.mem_image]
  have hker : Submodule.span K (Set.range rows) ≤ LinearMap.ker (Module.Dual.eval K V a) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hzero i)
  have hproper : LinearMap.ker (Module.Dual.eval K V a) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    apply ha
    exact (Module.bijective_dual_eval K V).injective
      ((LinearMap.ker_eq_top.mp h).trans (map_zero _).symm)
  have hdim : finrank K (Submodule.span K (Set.range rows)) < finrank K V := by
    have h := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_lt hker hproper)
    simpa using h
  have hcard : I₀.card ≤ finrank K V - 1 := by
    rw [show I₀.card = Fintype.card κ by simp [I₀], ← finrank_span_eq_card hind, hspan]
    omega
  obtain ⟨I, h₀I, _, hcardI⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ I₀) hcard (by simpa using hm)
  refine ⟨I, hcardI, le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
  rw [← hspan, hI₀]
  exact Submodule.span_mono (Set.image_mono h₀I)

variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {m : ℕ}

/-- Bound the probability of annihilating a witness chosen using only rows indexed by `I`. -/
private theorem measure_selected_null_vector_le
    (eval : Fin m → Ω → Module.Dual K V) (S : Set V) {q : ℝ≥0∞}
    (hconc : ∀ i a, a ∈ S → μ {x | eval i x a = 0} ≤ q) (I : Finset (Fin m))
    (chooseWitness : (I → Ω) → Option V)
    (hchoose : ∀ a₀ a, chooseWitness a₀ = some a → a ∈ S) :
    Measure.pi (fun _ : Fin m => μ)
        {rows | ∃ a, chooseWitness (fun i => rows i) = some a ∧ ∀ i, eval i (rows i) a = 0}
      ≤ q ^ (m - I.card) := by
  classical
  let ν₁ := Measure.pi fun _ : {i : Fin m // i ∈ I} => μ
  let ν₂ := Measure.pi fun _ : {i : Fin m // i ∉ I} => μ
  let event : Set ((I → Ω) × ({i : Fin m // i ∉ I} → Ω)) :=
    {x | ∃ a, chooseWitness x.1 = some a ∧ ∀ i : {i : Fin m // i ∉ I}, eval i (x.2 i) a = 0}
  have hevent : MeasurableSet event := event.toFinite.measurableSet
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => Ω) (· ∈ I)
  have hpres : MeasurePreserving e (Measure.pi (fun _ : Fin m => μ)) (ν₁.prod ν₂) :=
    by
      dsimp [e, ν₁, ν₂]
      convert measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => μ) (· ∈ I) using 1
      congr!
  calc
    _ ≤ (Measure.pi (fun _ : Fin m => μ)) (e ⁻¹' event) := by
      apply measure_mono
      rintro rows ⟨a, ha, hrows⟩
      exact ⟨a, ha, fun i => hrows i⟩
    _ = (ν₁.prod ν₂) event := hpres.measure_preimage hevent.nullMeasurableSet
    _ = ∫⁻ a₀, ν₂ (Prod.mk a₀ ⁻¹' event) ∂ν₁ := Measure.prod_apply hevent
    _ ≤ ∫⁻ _ : I → Ω, q ^ (m - I.card) ∂ν₁ := by
      apply lintegral_mono
      intro a₀
      cases h : chooseWitness a₀ with
      | none =>
          simp [event, h]
      | some a =>
          have hsubset : Prod.mk a₀ ⁻¹' event ⊆
              Set.pi Set.univ (fun i : {i : Fin m // i ∉ I} => {x | eval i x a = 0}) := by
            rintro rows ⟨b, hb, hrows⟩ i _
            change chooseWitness a₀ = some b at hb
            rw [h] at hb
            obtain rfl := Option.some.inj hb
            exact hrows i
          calc
            _ ≤ ν₂ (Set.pi Set.univ (fun i => {x | eval i x a = 0})) := measure_mono hsubset
            _ = ∏ i : {i : Fin m // i ∉ I}, μ {x | eval i x a = 0} := Measure.pi_pi _ _
            _ ≤ ∏ _i : {i : Fin m // i ∉ I}, q :=
              Finset.prod_le_prod fun i _ => hconc i a (hchoose a₀ a h)
            _ = _ := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_subtype_compl,
                Fintype.card_fin, Fintype.card_coe]
    _ = q ^ (m - I.card) := by simp

-- The dimension argument restricts the search to one witness per choice of rows.
/-- Concentration bound for a common null vector drawn from a prescribed set of
nonzero vectors, allowing a different evaluation rule at each row. -/
theorem measure_exists_null_vector_rowwise_le [FiniteDimensional K V]
    (eval : Fin m → Ω → Module.Dual K V) (S : Set V) {q : ℝ≥0∞}
    (hS : ∀ a ∈ S, a ≠ 0)
    (hconc : ∀ i a, a ∈ S → μ {x | eval i x a = 0} ≤ q)
    (hm : finrank K V - 1 ≤ m) :
    Measure.pi (fun _ : Fin m => μ) {rows | ∃ a ∈ S, ∀ i, eval i (rows i) a = 0}
      ≤ (m.choose (finrank K V - 1) : ℝ≥0∞) * q ^ (m - (finrank K V - 1)) := by
  classical
  let witnessExists (I : Finset (Fin m)) (selected : I → Ω) :=
    ∃ a ∈ S, ∀ i : I, eval i (selected i) a = 0
  let chooseWitness (I : Finset (Fin m)) (selected : I → Ω) : Option V :=
    if h : witnessExists I selected then some (Classical.choose h) else none
  let event (I : Finset (Fin m)) : Set (Fin m → Ω) :=
    {rows | ∃ a, chooseWitness I (fun i => rows i) = some a ∧ ∀ i, eval i (rows i) a = 0}
  let choices := (Finset.univ : Finset (Fin m)).powersetCard (finrank K V - 1)
  have hchoose (I : Finset (Fin m)) (selected : I → Ω) (a : V)
      (heq : chooseWitness I selected = some a) : a ∈ S := by
    by_cases h : witnessExists I selected
    · have hs : some (Classical.choose h) = some a := by
        simpa only [chooseWitness, dite_eq_left h] using heq
      rw [← Option.some.inj hs]
      exact (Classical.choose_spec h).1
    · simp [chooseWitness, h] at heq
  have hsubset :
      {rows | ∃ a ∈ S, ∀ i, eval i (rows i) a = 0} ⊆ ⋃ I ∈ choices, event I := by
    rintro rows ⟨a, ha, hzero⟩
    let L : Fin m → Module.Dual K V := fun i => eval i (rows i)
    obtain ⟨I, hcardI, hspan⟩ := exists_spanning_rows L hm (hS a ha) hzero
    have hI : I ∈ choices := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hcardI⟩
    have hex : witnessExists I (fun i => rows i) := ⟨a, ha, fun i => hzero i⟩
    let a' := Classical.choose hex
    have hvanish : Submodule.span K (L '' (I : Set (Fin m))) ≤
        LinearMap.ker (Module.Dual.eval K V a') := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact LinearMap.mem_ker.mpr ((Classical.choose_spec hex).2 ⟨i, hi⟩)
    refine Set.mem_iUnion₂.mpr ⟨I, hI, a', dite_eq_left hex, ?_⟩
    intro i
    refine LinearMap.mem_ker.mp (hvanish ?_)
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  let ν := Measure.pi (fun _ : Fin m => μ)
  calc
    _ ≤ ν (⋃ I ∈ choices, event I) := measure_mono hsubset
    _ ≤ ∑ I ∈ choices, ν (event I) := measure_biUnion_finset_le choices event
    _ ≤ ∑ _ ∈ choices, q ^ (m - (finrank K V - 1)) := by
      apply Finset.sum_le_sum
      intro I hI
      have hcardI := (Finset.mem_powersetCard.mp hI).2
      rw [← hcardI]
      exact measure_selected_null_vector_le eval S hconc I (chooseWitness I) (hchoose I)
    _ = _ := by simp [choices, Finset.card_powersetCard]

/-- Concentration bound for a common null vector when the row evaluations agree. -/
theorem measure_exists_null_vector_le [FiniteDimensional K V]
    (eval : Ω → Module.Dual K V) (S : Set V) {q : ℝ≥0∞}
    (hS : ∀ a ∈ S, a ≠ 0)
    (hconc : ∀ a ∈ S, μ {x | eval x a = 0} ≤ q)
    (hm : finrank K V - 1 ≤ m) :
    Measure.pi (fun _ : Fin m => μ) {rows | ∃ a ∈ S, ∀ i, eval (rows i) a = 0}
      ≤ (m.choose (finrank K V - 1) : ℝ≥0∞) * q ^ (m - (finrank K V - 1)) :=
  measure_exists_null_vector_rowwise_le (fun _ => eval) S hS (fun _ => hconc) hm

end BooleanThreshold
