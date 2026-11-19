module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.MeasureTheory.Constructions.Pi

public section

open MeasureTheory Module Submodule
open scoped ENNReal

namespace BooleanThreshold

/-- A finite-dimensional coordinate subspace has a set of coordinates that determines
all vectors in the subspace. -/
theorem exists_injective_coordinate_projection {K : Type*} [Field K] {n : ℕ}
    (U : Submodule K (Fin n → K)) :
    ∃ I : Finset (Fin n), I.card = finrank K U ∧
      Function.Injective (fun x : U => fun i : I => x.val i) := by
  classical
  let coord (i : Fin n) : Module.Dual K U := (LinearMap.proj i).comp U.subtype
  obtain ⟨κ, e, he, hspan, hind⟩ := exists_linearIndependent' K coord
  let : Fintype κ := Fintype.ofInjective e he
  let proj : U →ₗ[K] (κ → K) := LinearMap.pi (coord ∘ e)
  have hproj : Function.Injective proj := by
    intro x y hxy
    let ev := Module.Dual.eval K U (x - y)
    have hs : span K (Set.range (coord ∘ e)) ≤ LinearMap.ker ev := by
      apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply LinearMap.mem_ker.mpr
      change coord (e j) (x - y) = 0
      rw [map_sub, sub_eq_zero]
      exact congrFun hxy j
    rw [hspan] at hs
    apply Subtype.ext
    funext i
    have hi := LinearMap.mem_ker.mp (hs (subset_span (Set.mem_range_self i)))
    change coord i (x - y) = 0 at hi
    rwa [map_sub, sub_eq_zero] at hi
  let I := Finset.univ.map ⟨e, he⟩
  have hLo := LinearMap.finrank_le_finrank_of_injective hproj
  have hHi := hind.fintype_card_le_finrank
  have hcard : Fintype.card κ = finrank K U := by
    rw [finrank_fintype_fun_eq_card] at hLo
    rw [Subspace.dual_finrank_eq] at hHi
    exact le_antisymm hHi hLo
  refine ⟨I, by simp [I, hcard], fun x y hxy => hproj ?_⟩
  funext j
  let i : I := ⟨e j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  exact congrFun hxy i

/-- A vector with independent coordinates has subspace mass bounded by its
maximal coordinate atom raised to the codimension. -/
theorem product_mass_submodule_le
    {Ω K : Type*} [Field K] [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (value : Ω ↪ K)
    (b : ℝ≥0∞) (hb : ∀ z : Ω, μ {z} ≤ b) (U : Submodule K (Fin n → K)) :
    Measure.pi (fun _ : Fin n => μ) {x | (fun i => value (x i)) ∈ U} ≤
      b ^ (n - finrank K U) := by
  classical
  obtain ⟨I, hI, hinj⟩ := exists_injective_coordinate_projection U
  let J := {i : Fin n // i ∉ I}
  let μI := Measure.pi (fun _ : I => μ)
  let μJ := Measure.pi (fun _ : J => μ)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (· ∈ I)
  let E : Set (Fin n → Ω) := {x | (fun i => value (x i)) ∈ U}
  let E' : Set ((I → Ω) × (J → Ω)) := e.symm ⁻¹' E
  have hE' : MeasurableSet E' := (Set.toFinite _).measurableSet
  have hpres : MeasurePreserving e (Measure.pi (fun _ : Fin n => μ)) (μI.prod μJ) := by
    dsimp [e, μI, μJ]
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) (· ∈ I) using 1
    congr!
  have hpre : e ⁻¹' E' = E := by ext x; simp [E']
  calc
    _ = (μI.prod μJ) E' := by
      rw [← hpres.measure_preimage hE'.nullMeasurableSet, hpre]
    _ = ∫⁻ x : I → Ω, μJ (Prod.mk x ⁻¹' E') ∂μI := Measure.prod_apply hE'
    _ ≤ ∫⁻ _ : I → Ω, b ^ (n - finrank K U) ∂μI := by
      apply lintegral_mono
      intro x
      by_cases h : (Prod.mk x ⁻¹' E').Nonempty
      · obtain ⟨y, hy⟩ := h
        have huniq : Prod.mk x ⁻¹' E' ⊆ {y} := by
          intro z hz
          have hzer (w : J → Ω) (hw : w ∈ Prod.mk x ⁻¹' E') :
              (fun i => value (e.symm (x, w) i)) ∈ U := hw
          let u : U := ⟨_, hzer z hz⟩
          let v : U := ⟨_, hzer y hy⟩
          have hu (w : J → Ω) : (fun i : I => e.symm (x, w) i) = x :=
            congrArg Prod.fst (e.apply_symm_apply (x, w))
          have hUV : u = v := hinj (funext fun i => by
            change value (e.symm (x, z) i) = value (e.symm (x, y) i)
            rw [congrFun (hu z) i, congrFun (hu y) i])
          have hXY : e.symm (x, z) = e.symm (x, y) := by
            funext i
            exact value.injective (congrFun (congrArg Subtype.val hUV) i)
          have hzy : z = y := congrArg Prod.snd (e.symm.injective hXY)
          exact Set.mem_singleton_iff.mpr hzy
        have hcard : Fintype.card J = n - finrank K U := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hI]
        calc
          _ ≤ μJ {y} := measure_mono huniq
          _ = ∏ j, μ {y j} := Measure.pi_singleton _ _
          _ ≤ ∏ _j : J, b := Finset.prod_le_prod fun j _ => hb (y j)
          _ = _ := by simp [hcard]
      · have hm : Prod.mk x ⁻¹' E' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        simp [hm]
    _ = _ := by simp

end BooleanThreshold
