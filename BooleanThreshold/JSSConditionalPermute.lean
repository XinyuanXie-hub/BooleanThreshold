module

public import BooleanThreshold.JSSConditionalInversion
public import BooleanThreshold.JSSConditionalStartingKernel

public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- A reordering of the coordinates preserves the signs' total weight. -/
theorem signWeight_comp {n : ℕ} (e : Equiv.Perm (Fin n)) (b : Fin n → Bool) :
    signWeight (b ∘ e) = signWeight b := by
  have h : ∑ i, realSigns (b ∘ e) i = ∑ i, realSigns b i :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [sum_realSigns_eq_signWeight, sum_realSigns_eq_signWeight] at h
  apply Fin.ext
  exact_mod_cast (show ((signWeight (b ∘ e)).val : ℝ) = ((signWeight b).val : ℝ) by
    linarith only [h])

/-- The law on a fixed-weight slice is invariant under any coordinate permutation. -/
theorem uniformOn_signSlice_comp_preimage {n : ℕ} (e : Equiv.Perm (Fin n)) (m : Fin (n + 1))
    (E : Set (Fin n → Bool)) :
    uniformOn (signSlice n m) ((fun b => b ∘ e) ⁻¹' E) = uniformOn (signSlice n m) E := by
  let g : (Fin n → Bool) ≃ (Fin n → Bool) := Equiv.arrowCongr e.symm (Equiv.refl Bool)
  change uniformOn (signSlice n m) (g ⁻¹' E) = _
  have he := Set.ncard_preimage_of_injective_subset_range
    (s := signSlice n m ∩ E) g.injective (by simp [g.surjective.range_eq])
  have hpre : g ⁻¹' (signSlice n m ∩ E) = signSlice n m ∩ (g ⁻¹' E) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_inter_iff, signSlice, Set.mem_ofPred_eq]
    change (signWeight (b ∘ e) = m ∧ g b ∈ E) ↔ (signWeight b = m ∧ g b ∈ E)
    rw [signWeight_comp]
  rw [hpre] at he
  rw [uniformOn_finite_apply (signSlice n m).toFinite, uniformOn_finite_apply (signSlice n m).toFinite, he]

/-- Simultaneous reordering of signs and coefficients preserves their signed sum. -/
theorem signSum_comp {n : ℕ} (e : Equiv.Perm (Fin n)) (a : Fin n → ℝ) (b : Fin n → Bool) :
    signSum (a ∘ e) (b ∘ e) = signSum a b :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem signSlice_smallBall_comp {n : ℕ} (e : Equiv.Perm (Fin n)) (m : Fin (n + 1))
    (a : Fin n → ℝ) (z r : ℝ) :
    (uniformOn (signSlice n m)).real {b | |signSum (a ∘ e) b - z| ≤ r} =
      (uniformOn (signSlice n m)).real {b | |signSum a b - z| ≤ r} := by
  let E := {b | |signSum (a ∘ e) b - z| ≤ r}
  have hpre : (fun b => b ∘ e) ⁻¹' E = {b | |signSum a b - z| ≤ r} := by
    ext b
    simp [E, signSum_comp]
  have he := uniformOn_signSlice_comp_preimage e m E
  rw [hpre] at he
  exact congrArg ENNReal.toReal he.symm

/-- Reordering the coordinate boxes preserves their interval properties
and the two separated bands. -/
theorem oppositeBandBox_comp {n N B : ℕ} {α : ℝ} {P : Fin n → Finset ℤ}
    (h : oppositeBandBox n N B α P) (e : Equiv.Perm (Fin n)) :
    oppositeBandBox n N B α (P ∘ e) := by
  classical
  obtain ⟨hP, I, J, hI, hJ, hdisj, hlow, hhigh⟩ := h
  let I' := I.map e.symm.toEmbedding
  let J' := J.map e.symm.toEmbedding
  have hmem (S : Finset (Fin n)) (i : Fin n) :
      i ∈ S.map e.symm.toEmbedding ↔ e i ∈ S := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨j, hj, hj'⟩
      change e.symm j = i at hj'
      simpa only [← hj', Equiv.apply_symm_apply] using hj
    · intro hi
      exact ⟨e i, hi, e.symm_apply_apply i⟩
  refine ⟨fun i => hP (e i), I', J', ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [I', card_map] using hI
  · simpa only [J', card_map] using hJ
  · apply disjoint_left.mpr
    intro i hi hj
    exact disjoint_left.mp hdisj ((hmem I i).mp hi) ((hmem J i).mp hj)
  · exact fun i hi x hx => hlow (e i) ((hmem I i).mp hi) x hx
  · exact fun i hi x hx => hhigh (e i) ((hmem J i).mp hi) x hx

theorem piFinset_card_comp {n : ℕ} (e : Equiv.Perm (Fin n)) (P : Fin n → Finset ℤ) :
    (Fintype.piFinset (P ∘ e)).card = (Fintype.piFinset P).card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

private theorem mem_largeSliceBox_comp {n : ℕ} (e : Equiv.Perm (Fin n)) (m : Fin (n + 1))
    (P : Fin n → Finset ℤ) (h : ℝ) (w : Fin n → ℤ) :
    w ∘ e ∈ largeSliceBox n m (P ∘ e) h ↔ w ∈ largeSliceBox n m P h := by
  simp only [largeSliceBox, Finset.mem_filter, Fintype.mem_piFinset]
  apply and_congr
  · exact ⟨fun f i => by simpa using f (e.symm i), fun f i => f (e i)⟩
  · apply exists_congr
    intro z
    have hm := signSlice_smallBall_comp e m (fun i => (w i : ℝ)) z (2 * Real.sqrt (n : ℝ))
    exact Iff.of_eq (congrArg (fun r : ℝ => h ≤ r) hm)

theorem card_eq_of_comp_mem_iff {n : ℕ} {A B : Finset (Fin n → ℤ)}
    (e : Equiv.Perm (Fin n)) (h : ∀ w : Fin n → ℤ, w ∘ e ∈ B ↔ w ∈ A) :
    B.card = A.card := by
  symm
  let g : (Fin n → ℤ) ≃ (Fin n → ℤ) := Equiv.arrowCongr e.symm (Equiv.refl ℤ)
  refine Finset.card_bij' (fun w _ => g w) (fun w _ => g.symm w) ?_ ?_
    (fun w _ => g.symm_apply_apply w) (fun w _ => g.apply_symm_apply w)
  · intro w hw
    exact (h w).mpr hw
  · intro w hw
    apply (h (g.symm w)).mp
    change g (g.symm w) ∈ B
    rwa [g.apply_symm_apply]

/-- Reordering the product intervals leaves the count of points with a
large atom on the prescribed slice exactly unchanged. -/
theorem largeSliceBox_card_comp {n : ℕ} (e : Equiv.Perm (Fin n)) (m : Fin (n + 1))
    (P : Fin n → Finset ℤ) (h : ℝ) :
    (largeSliceBox n m (P ∘ e) h).card = (largeSliceBox n m P h).card :=
  card_eq_of_comp_mem_iff e (mem_largeSliceBox_comp e m P h)

/-- The cyclic subset average is unaffected by a common reordering of
the coefficients and the uniformly sampled fixed-weight signs. -/
theorem sliceAverage_cyclicIntegerCoordinates_comp {n P : ℕ} [NeZero P]
    (e : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (w : Fin n → ℤ) (f : ZMod P → ℝ)
    (t : ZMod P) :
    sliceAverage (cyclicIntegerCoordinates (P := P) (w ∘ e)) f n m.val t =
      sliceAverage (cyclicIntegerCoordinates (P := P) w) f n m.val t := by
  let μ := uniformOn (signSlice n m)
  let φ (b : Fin n → Bool) := b ∘ e
  let F (b : Fin n → Bool) := f (t + ∑ i ∈ univ.filter (fun i => b i),
    cyclicIntegerCoordinates (P := P) (w ∘ e) i.val)
  let F₀ (b : Fin n → Bool) := f (t + ∑ i ∈ univ.filter (fun i => b i),
    cyclicIntegerCoordinates (P := P) w i.val)
  have hφ : Measurable φ := measurable_of_finite _
  have hF : Measurable F := measurable_of_finite _
  have hmap : Measure.map φ μ = μ := by
    apply Measure.ext
    intro E hE
    rw [Measure.map_apply hφ hE]
    exact uniformOn_signSlice_comp_preimage e m E
  have hsum (b : Fin n → Bool) : F (φ b) = F₀ b := by
    have h : (∑ i ∈ univ.filter (fun i => b (e i)),
          cyclicIntegerCoordinates (P := P) (w ∘ e) i.val) =
        ∑ i ∈ univ.filter (fun i => b i), cyclicIntegerCoordinates (P := P) w i.val := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Fintype.sum_equiv e
      intro i
      simp [cyclicIntegerCoordinates]
    dsimp [F, F₀, φ]
    rw [h]
  have hI : (∫ b, F b ∂μ) = ∫ b, F₀ b ∂μ := by
    calc
      _ = ∫ b, F b ∂(Measure.map φ μ) := by rw [hmap]
      _ = ∫ b, F (φ b) ∂μ := integral_map hφ.aemeasurable hF.aestronglyMeasurable
      _ = _ := by simp_rw [hsum]
  exact (integral_signSlice_eq_sliceAverage m _ _ _).symm.trans
    (hI.trans (integral_signSlice_eq_sliceAverage m _ _ _))

end BooleanThreshold
