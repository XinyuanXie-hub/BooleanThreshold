module

public import Mathlib.Probability.UniformOn

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

/-- The real sign vector encoded by a Boolean vector. -/
def realSigns {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ :=
  fun j => if x j then 1 else -1

/-- The vertices of the sign cube in real coordinate space. -/
def signCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = -1 ∨ x i = 1}

/-- The law of independent uniform draws from the sign cube. -/
noncomputable def signLaw (n r : ℕ) : Measure (Fin r → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin r => uniformOn (signCube n))

theorem realSigns_injective (n : ℕ) : Function.Injective (@realSigns n) := by
  intro x y h
  funext j
  have hj := congrFun h j
  cases hx : x j <;> cases hy : y j <;> simp [realSigns, hx, hy] at hj ⊢
  all_goals norm_num at hj

theorem range_realSigns (n : ℕ) : Set.range (@realSigns n) = signCube n := by
  ext x
  change (∃ y, realSigns y = x) ↔ ∀ i, x i = -1 ∨ x i = 1
  constructor
  · rintro ⟨y, rfl⟩ i
    cases h : y i <;> simp [realSigns, h]
  · intro hx
    classical
    refine ⟨fun i => decide (x i = 1), ?_⟩
    funext i
    rcases hx i with hi | hi <;> norm_num [realSigns, hi]

theorem realSigns_mem_signCube {n : ℕ} (x : Fin n → Bool) : realSigns x ∈ signCube n := by
  rw [← range_realSigns]
  exact ⟨x, rfl⟩

theorem signCube_finite (n : ℕ) : (signCube n).Finite := by
  rw [← range_realSigns]
  exact Set.finite_range _

theorem signCube_ncard (n : ℕ) : (signCube n).ncard = 2 ^ n := by
  rw [← range_realSigns, Set.ncard_range_of_injective (realSigns_injective n)]
  simp [Nat.card_eq_fintype_card]

theorem signCube_nonempty (n : ℕ) : (signCube n).Nonempty :=
  ⟨fun _ => 1, fun _ => Or.inr rfl⟩

instance (n : ℕ) : IsProbabilityMeasure (uniformOn (signCube n)) :=
  isProbabilityMeasure_uniformOn (signCube_finite n) (signCube_nonempty n)

instance (n r : ℕ) : IsProbabilityMeasure (signLaw n r) := by
  unfold signLaw
  infer_instance

theorem uniformOn_finite_apply {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {s t : Set Ω} (hs : s.Finite) :
    uniformOn s t = ((s ∩ t).ncard : ℝ≥0∞) / (s.ncard : ℝ≥0∞) := by
  rw [uniformOn, cond_apply hs.measurableSet, Measure.count_apply_finite _ hs,
    Measure.count_apply_finite _ (hs.inter_of_left t), Set.ncard_eq_toFinset_card s hs,
    Set.ncard_eq_toFinset_card (s ∩ t) (hs.inter_of_left t), ENNReal.div_eq_inv_mul]

theorem uniformOn_finite_real_eq_card {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {s : Set Ω} (hs : s.Finite) (t : Set Ω) :
    (uniformOn s).real t = ((s ∩ t).ncard : ℝ) / (s.ncard : ℝ) := by
  rw [measureReal_def, uniformOn_finite_apply hs, ENNReal.toReal_div]
  simp

theorem uniformOn_univ_real_eq_card {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype Ω] (s : Set Ω) :
    (uniformOn Set.univ).real s = (s.ncard : ℝ) / Fintype.card Ω := by
  rw [measureReal_def, uniformOn_finite_apply Set.finite_univ, Set.univ_inter, Set.ncard_univ,
    Nat.card_eq_fintype_card, ENNReal.toReal_div]
  simp

theorem map_uniformOn_univ_eq_uniformOn_range
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α] [Finite Ω]
    {f : Ω → α} (hf : Function.Injective f) :
    (uniformOn Set.univ).map f = uniformOn (Set.range f) := by
  ext s hs
  rw [Measure.map_apply (measurable_of_finite f) hs, uniformOn_finite_apply Set.finite_univ,
    Set.univ_inter, uniformOn_finite_apply (Set.finite_range f),
    Set.ncard_range_of_injective hf, Set.ncard_univ,
    Set.inter_comm (Set.range f) s, ← Set.image_preimage_eq_inter_range,
    Set.ncard_image_of_injective _ hf]

theorem map_uniformOn_univ_of_equiv {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α] [Finite Ω] (e : Ω ≃ α) :
    (uniformOn Set.univ).map (e : Ω → α) = uniformOn Set.univ := by
  rw [map_uniformOn_univ_eq_uniformOn_range e.injective, e.surjective.range_eq]

theorem realSigns_measurableEmbedding (n : ℕ) : MeasurableEmbedding (@realSigns n) :=
  ⟨realSigns_injective n, measurable_of_finite _, fun {_} _ => ((Set.toFinite _).image _).measurableSet⟩

theorem realSigns_measurePreserving (n : ℕ) :
    MeasurePreserving (@realSigns n) (uniformOn Set.univ) (uniformOn (signCube n)) :=
  ⟨(realSigns_measurableEmbedding n).measurable, by
    rw [map_uniformOn_univ_eq_uniformOn_range (realSigns_injective n), range_realSigns]⟩

theorem uniformOn_signCube_apply {n : ℕ} (A : Set (Fin n → ℝ)) :
    uniformOn (signCube n) A = uniformOn Set.univ (realSigns ⁻¹' A) := by
  rw [← (realSigns_measurePreserving n).map_eq, (realSigns_measurableEmbedding n).map_apply]

theorem pi_uniformOn_univ {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω] [Nonempty Ω] :
    Measure.pi (fun _ : ι => uniformOn (Set.univ : Set Ω)) =
      uniformOn (Set.univ : Set (ι → Ω)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton]
  simp only [uniformOn_univ, Measure.count_singleton, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow]
  simp only [one_div, ENNReal.inv_pow]

private theorem signLaw_eq_map (n r : ℕ) :
    signLaw n r = (uniformOn Set.univ).map (fun x : Fin r → Fin n → Bool => fun i => realSigns (x i)) := by
  simpa only [pi_uniformOn_univ, signLaw] using
    (measurePreserving_pi (fun _ : Fin r => uniformOn Set.univ)
      (fun _ => uniformOn (signCube n)) (fun _ => realSigns_measurePreserving n)).map_eq.symm

/-- An event under the real sign law is measured by its preimage in the
uniform Boolean sample space. -/
theorem signLaw_apply {n r : ℕ} (s : Set (Fin r → Fin n → ℝ)) :
    signLaw n r s =
      uniformOn Set.univ ((fun x : Fin r → Fin n → Bool => fun i => realSigns (x i)) ⁻¹' s) := by
  let f := fun x : Fin r → Fin n → Bool => fun i => realSigns (x i)
  have hf : MeasurableEmbedding f :=
    ⟨fun x y h => funext fun i => realSigns_injective n (congrFun h i),
      measurable_of_finite _, fun {_} _ => ((Set.toFinite _).image _).measurableSet⟩
  rw [signLaw_eq_map, hf.map_apply]

theorem signLaw_real_apply {n r : ℕ} (s : Set (Fin r → Fin n → ℝ)) :
    (signLaw n r).real s =
      (uniformOn Set.univ).real
        ((fun x : Fin r → Fin n → Bool => fun i => realSigns (x i)) ⁻¹' s) := by
  simp only [measureReal_def, signLaw_apply]

/-- Events agreeing at all sign matrices have the same probability under the sign law. -/
theorem signLaw_apply_eq_of_on_cube {n r : ℕ} {s t : Set (Fin r → Fin n → ℝ)}
    (h : ∀ v, (∀ i, v i ∈ signCube n) → (v ∈ s ↔ v ∈ t)) :
    signLaw n r s = signLaw n r t := by
  rw [signLaw_apply, signLaw_apply]
  congr 1
  ext x
  exact h _ fun i => realSigns_mem_signCube (x i)

theorem signLaw_ae_mem_cube (n r : ℕ) : ∀ᵐ v ∂signLaw n r, ∀ i, v i ∈ signCube n := by
  rw [ae_iff, signLaw_apply_eq_of_on_cube (t := ∅)]
  · exact measure_empty
  · intro v hv
    simp [hv]

theorem pi_map_restrict_embedding {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (e : κ ↪ ι) :
    (Measure.pi (fun _ : ι => μ)).map (fun x j => x (e j)) = Measure.pi (fun _ : κ => μ) := by
  classical
  have hmeas : Measurable (fun (x : ι → Ω) (j : κ) => x (e j)) :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply (e j)
  refine (Measure.pi_eq fun s hs => ?_).symm
  let S := Function.extend e s (fun _ => Set.univ)
  have hpre : (fun (x : ι → Ω) (j : κ) => x (e j)) ⁻¹' Set.univ.pi s =
      Set.univ.pi S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        simpa [S, e.injective.extend_apply] using h j
      · simp [S, Function.extend_apply' _ _ _ hi]
    · intro h j
      simpa [S, e.injective.extend_apply] using h (e j)
  rw [Measure.map_apply hmeas (.univ_pi hs), hpre, Measure.pi_pi]
  have hS (i : ι) : μ (S i) = Function.extend e (fun j => μ (s j)) 1 i := by
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      simp [S, e.injective.extend_apply]
    · simp [S, Function.extend_apply' _ _ _ hi]
  simp_rw [hS]
  exact Finset.prod_extend_one_of_injective _ e.injective (fun _ => Finset.mem_univ _)

/-- Restricting to distinct vectors preserves the independent uniform sign law. -/
theorem signLaw_restrict_rows {n r s : ℕ} (e : Fin s ↪ Fin r) (A : Set (Fin s → Fin n → ℝ)) :
    signLaw n r ((fun v i => v (e i)) ⁻¹' A) = signLaw n s A := by
  let restrict := fun (x : Fin r → Fin n → Bool) (i : Fin s) => x (e i)
  let event := (fun x : Fin s → Fin n → Bool => fun i => realSigns (x i)) ⁻¹' A
  rw [signLaw_apply, signLaw_apply]
  change uniformOn Set.univ (restrict ⁻¹' event) = uniformOn Set.univ event
  have hm : MeasurableSet event := (Set.toFinite _).measurableSet
  rw [← Measure.map_apply (measurable_of_finite restrict) hm, ← pi_uniformOn_univ,
    pi_map_restrict_embedding (uniformOn (Set.univ : Set (Fin n → Bool))) e,
    pi_uniformOn_univ]

/-- The probability of a transposed event equals its probability in the transposed dimensions. -/
theorem signLaw_transpose {n r : ℕ} (A : Set (Fin n → Fin r → ℝ)) :
    signLaw n r ((fun v j i => v i j) ⁻¹' A) = signLaw r n A := by
  let e := Equiv.piComm (fun (_ : Fin r) (_ : Fin n) => Bool)
  let event := (fun x : Fin n → Fin r → Bool => fun i => realSigns (x i)) ⁻¹' A
  rw [signLaw_apply, signLaw_apply]
  change uniformOn Set.univ (e ⁻¹' event) = uniformOn Set.univ event
  have hm : MeasurableSet event := (Set.toFinite _).measurableSet
  rw [← Measure.map_apply (measurable_of_finite _) hm, map_uniformOn_univ_of_equiv e]

/-- Restricting each sign vector to distinct coordinates preserves the sign law. -/
theorem signLaw_restrict_columns {n r m : ℕ} (e : Fin m ↪ Fin n) (A : Set (Fin r → Fin m → ℝ)) :
    signLaw n r ((fun v i j => v i (e j)) ⁻¹' A) = signLaw m r A := by
  calc
    _ = signLaw r n ((fun v i j => v (e j) i) ⁻¹' A) :=
      signLaw_transpose ((fun v i j => v (e j) i) ⁻¹' A)
    _ = signLaw r m ((fun v i j => v j i) ⁻¹' A) :=
      signLaw_restrict_rows e ((fun v i j => v j i) ⁻¹' A)
    _ = _ := signLaw_transpose A

theorem signLaw_map_restrict_rows {n r s : ℕ} (e : Fin s ↪ Fin r) :
    (signLaw n r).map (fun v i => v (e i)) = signLaw n s := by
  have hm : Measurable (fun (v : Fin r → Fin n → ℝ) (i : Fin s) => v (e i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
  exact Measure.ext fun A hA => (Measure.map_apply hm hA).trans (signLaw_restrict_rows e A)

theorem signLaw_map_transpose (n r : ℕ) :
    (signLaw n r).map (fun v j i => v i j) = signLaw r n := by
  have hm : Measurable (fun (v : Fin r → Fin n → ℝ) (j : Fin n) (i : Fin r) => v i j) :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun i =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)
  exact Measure.ext fun A hA => (Measure.map_apply hm hA).trans (signLaw_transpose A)

theorem signLaw_map_restrict_columns {n r m : ℕ} (e : Fin m ↪ Fin n) :
    (signLaw n r).map (fun v i j => v i (e j)) = signLaw m r := by
  have hm : Measurable (fun (v : Fin r → Fin n → ℝ) (i : Fin r) (j : Fin m) => v i (e j)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      (measurable_pi_apply (e j)).comp (measurable_pi_apply i)
  exact Measure.ext fun A hA => (Measure.map_apply hm hA).trans (signLaw_restrict_columns e A)

end BooleanThreshold
