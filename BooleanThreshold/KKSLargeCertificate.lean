module

public import BooleanThreshold.NonPair
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

public section

open MeasureTheory Module Submodule
open scoped ENNReal

namespace BooleanThreshold

/-- A random independent certificate in the common annihilator lets us apply the
subspace concentration bound in codimension equal to the size of the certificate. -/
theorem common_null_mul_certificate_rowwise_le
    {Ω Ξ V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ξ] [Finite Ω] [Finite Ξ]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    {m d : ℕ} (eval : Fin m → Ω → Module.Dual ℝ V) (aux : Ξ → Module.Dual ℝ V)
    (S : Set V) {p lower : ℝ≥0∞} (hS : ∀ a ∈ S, a ≠ 0)
    (hconc : ∀ i a, a ∈ S → μ {row | eval i row a = 0} ≤ p)
    (hm : finrank ℝ V - d - 1 ≤ m)
    (hcert : ∀ a ∈ S, lower ≤ Measure.pi (fun _ : Fin d => ν)
      {w | LinearIndependent ℝ (aux ∘ w) ∧ ∀ j, aux (w j) a = 0}) :
    lower * Measure.pi (fun _ : Fin m => μ) {r | ∃ a ∈ S, ∀ i, eval i (r i) a = 0} ≤
      (m.choose (finrank ℝ V - d - 1) : ℝ≥0∞) * p ^ (m - (finrank ℝ V - d - 1)) := by
  classical
  let μm := Measure.pi (fun _ : Fin m => μ)
  let νd := Measure.pi (fun _ : Fin d => ν)
  let E : Set (Fin m → Ω) := {r | ∃ a ∈ S, ∀ i, eval i (r i) a = 0}
  let B : Set ((Fin m → Ω) × (Fin d → Ξ)) :=
    {rw | LinearIndependent ℝ (aux ∘ rw.2) ∧
      ∃ a ∈ S, (∀ i, eval i (rw.1 i) a = 0) ∧ ∀ j, aux (rw.2 j) a = 0}
  let upper := (m.choose (finrank ℝ V - d - 1) : ℝ≥0∞) * p ^ (m - (finrank ℝ V - d - 1))
  have hB : MeasurableSet B := (Set.toFinite _).measurableSet
  have hE : MeasurableSet E := (Set.toFinite _).measurableSet
  have hlower : lower * μm E ≤ μm.prod νd B := by
    rw [Measure.prod_apply hB, ← lintegral_indicator_const hE]
    apply lintegral_mono
    intro r
    by_cases hr : r ∈ E
    · rw [Set.indicator_of_mem hr]
      obtain ⟨a, ha, hra⟩ := hr
      exact (hcert a ha).trans <| measure_mono fun w hw => ⟨hw.1, a, ha, hra, hw.2⟩
    · simp [Set.indicator_of_notMem hr]
  have hupper : μm.prod νd B ≤ upper := by
    rw [Measure.prod_apply_symm hB]
    calc
      _ ≤ ∫⁻ _ : Fin d → Ξ, upper ∂νd := by
        apply lintegral_mono
        intro w
        by_cases hw : LinearIndependent ℝ (aux ∘ w)
        · let W := span ℝ (Set.range (aux ∘ w))
          let A := W.dualCoannihilator
          have hd : finrank ℝ W = d := by simp [W, finrank_span_eq_card hw]
          have hA : finrank ℝ A = finrank ℝ V - d := by
            have h := Subspace.finrank_add_finrank_dualCoannihilator_eq W
            change finrank ℝ W + finrank ℝ A = finrank ℝ V at h
            omega
          let S' : Set A := {a | (a : V) ∈ S}
          let eval' (i : Fin m) (r : Ω) : Module.Dual ℝ A := (eval i r).comp A.subtype
          have hS' (a : A) (ha : a ∈ S') : a ≠ 0 := by
            intro hz
            apply hS a ha
            exact congrArg Subtype.val hz
          have hsub : (fun r => (r, w)) ⁻¹' B ⊆
              {r | ∃ a ∈ S', ∀ i, eval' i (r i) a = 0} := by
            rintro r ⟨_, a, ha, hrow, haux⟩
            have hk : W ≤ LinearMap.ker (Module.Dual.eval ℝ V a) := by
              apply span_le.mpr
              rintro _ ⟨j, rfl⟩
              exact LinearMap.mem_ker.mpr (haux j)
            have haW : a ∈ A :=
              (Submodule.mem_dualCoannihilator a).mpr fun _ hf => LinearMap.mem_ker.mp (hk hf)
            exact ⟨⟨a, haW⟩, ha, hrow⟩
          refine (measure_mono hsub).trans ?_
          have h := measure_exists_null_vector_rowwise_le (μ := μ) (m := m) eval' S' hS'
            (fun i a ha => hconc i a ha) (by simpa [hA] using hm)
          simpa only [hA, upper] using h
        · have hempty : (fun r : Fin m → Ω => (r, w)) ⁻¹' B = ∅ :=
            Set.eq_empty_iff_forall_notMem.mpr fun _ h => hw h.1
          simp [hempty]
      _ = upper := by simp
  exact hlower.trans hupper

/-- Greedy independent sampling from a set that keeps mass at least `lower`
after removing any span of fewer than `d` vectors. -/
theorem independent_samples_probability_lower
    {K V Ξ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ] [Finite Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (aux : Ξ → V)
    (A : Set Ξ) (d : ℕ) (lower : ℝ≥0∞)
    (hstep : ∀ W : Submodule K V, finrank K W < d →
      lower ≤ ν (A \ {x | aux x ∈ W})) :
    lower ^ d ≤ Measure.pi (fun _ : Fin d => ν)
      {w | LinearIndependent K (aux ∘ w) ∧ ∀ j, w j ∈ A} := by
  classical
  let G (k : ℕ) : Set (Fin k → Ξ) :=
    {w | LinearIndependent K (aux ∘ w) ∧ ∀ j, w j ∈ A}
  have hG (k : ℕ) : MeasurableSet (G k) := (Set.toFinite _).measurableSet
  have hsample (k : ℕ) (hk : k ≤ d) : lower ^ k ≤ Measure.pi (fun _ : Fin k => ν) (G k) := by
    induction k with
    | zero =>
        have hG₀ : G 0 = Set.univ := by ext w; simp [G]
        simp [hG₀]
    | succ k ih =>
        let νk := Measure.pi (fun _ : Fin k => ν)
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Ξ) 0
        let B : Set (Ξ × (Fin k → Ξ)) :=
          {zw | zw.2 ∈ G k ∧ zw.1 ∈ A ∧ aux zw.1 ∉ span K (Set.range (aux ∘ zw.2))}
        have hB : MeasurableSet B := (Set.toFinite _).measurableSet
        have he : MeasurePreserving e (Measure.pi (fun _ : Fin (k + 1) => ν)) (ν.prod νk) :=
          measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0
        have hsub : e ⁻¹' B ⊆ G (k + 1) := by
          intro w hw
          have head_apply : (e w).1 = w 0 := rfl
          have tail_apply : (e w).2 = Fin.tail w := by
            funext j
            change w ((0 : Fin (k + 1)).succAbove j) = w j.succ
            simp
          obtain ⟨hind, hin⟩ : LinearIndependent K (aux ∘ Fin.tail w) ∧
              ∀ j, Fin.tail w j ∈ A := by
            have hh : (e w).2 ∈ G k := hw.1
            rwa [tail_apply] at hh
          have hhead : w 0 ∈ A := head_apply ▸ hw.2.1
          have hnot : aux (w 0) ∉ span K (Set.range (aux ∘ Fin.tail w)) := by
            have hh : aux (e w).1 ∉ span K (Set.range (aux ∘ (e w).2)) := hw.2.2
            rwa [head_apply, tail_apply] at hh
          refine ⟨?_, fun j => ?_⟩
          · have hcomp : aux ∘ w = Fin.cons (aux (w 0)) (aux ∘ Fin.tail w) := by
              funext j
              exact Fin.cases rfl (fun _ => rfl) j
            exact hcomp.symm ▸ linearIndependent_finCons.mpr ⟨hind, hnot⟩
          · exact Fin.cases hhead hin j
        have hmass : lower * νk (G k) ≤ ν.prod νk B := by
          rw [Measure.prod_apply_symm hB, ← lintegral_indicator_const (hG k)]
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ G k
          · rw [Set.indicator_of_mem hw]
            have hdim : finrank K (span K (Set.range (aux ∘ w))) < d := by
              rw [finrank_span_eq_card hw.1, Fintype.card_fin]
              omega
            exact (hstep _ hdim).trans <| measure_mono fun _ hx => ⟨hw, hx.1, hx.2⟩
          · simp [Set.indicator_of_notMem hw]
        calc
          _ = lower * lower ^ k := pow_succ' _ _
          _ ≤ lower * νk (G k) := by
            gcongr
            exact ih (by omega)
          _ ≤ ν.prod νk B := hmass
          _ = Measure.pi (fun _ : Fin (k + 1) => ν) (e ⁻¹' B) :=
            (he.measure_preimage hB.nullMeasurableSet).symm
          _ ≤ _ := measure_mono hsub
  exact hsample d le_rfl

end BooleanThreshold
