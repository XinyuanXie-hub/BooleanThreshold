module

public import BooleanThreshold.JSSConditionalSlice
public import BooleanThreshold.JSSConditionalLittlewoodOfford
public import Mathlib.MeasureTheory.Measure.Prod

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace BooleanThreshold

private noncomputable def pairSwapIndex {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (mask : Fin k → Bool) : Fin n → Fin n :=
  Function.extend e (fun ij => e (ij.1, ij.2 ^^ mask ij.1)) id

private theorem pairSwapIndex_apply {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (mask : Fin k → Bool) (ij : Fin k × Bool) :
    pairSwapIndex e mask (e ij) = e (ij.1, ij.2 ^^ mask ij.1) :=
  e.injective.extend_apply _ _ _

private theorem pairSwapIndex_eq_of_notMem {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (mask : Fin k → Bool) {j : Fin n} (hj : j ∉ Set.range e) : pairSwapIndex e mask j = j :=
  Function.extend_apply' _ _ _ hj

private theorem pairSwapIndex_involutive {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (mask : Fin k → Bool) : Function.Involutive (pairSwapIndex e mask) := by
  intro j
  by_cases hm : j ∈ Set.range e
  · obtain ⟨⟨i, b⟩, rfl⟩ := hm
    simp only [pairSwapIndex_apply, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · rw [pairSwapIndex_eq_of_notMem e mask hm, pairSwapIndex_eq_of_notMem e mask hm]

/-- Independently swapping prescribed disjoint pairs of sign coordinates. -/
noncomputable def swapSignPairs {n k : ℕ} (e : Fin k × Bool ↪ Fin n) (mask : Fin k → Bool)
    (b : Fin n → Bool) : Fin n → Bool := b ∘ pairSwapIndex e mask

theorem swapSignPairs_apply {n k : ℕ} (e : Fin k × Bool ↪ Fin n) (mask : Fin k → Bool)
    (b : Fin n → Bool) (j : Fin k) (ε : Bool) :
    swapSignPairs e mask b (e (j, ε)) = b (e (j, ε ^^ mask j)) :=
  congrArg b (pairSwapIndex_apply e mask (j, ε))

theorem swapSignPairs_eq_of_notMem {n k : ℕ} (e : Fin k × Bool ↪ Fin n) (mask : Fin k → Bool)
    (b : Fin n → Bool) {j : Fin n} (hj : j ∉ Set.range e) :
    swapSignPairs e mask b j = b j :=
  congrArg b (pairSwapIndex_eq_of_notMem e mask hj)

theorem swapSignPairs_signWeight {n k : ℕ} (e : Fin k × Bool ↪ Fin n) (mask : Fin k → Bool)
    (b : Fin n → Bool) : signWeight (swapSignPairs e mask b) = signWeight b := by
  let p : Fin n ≃ Fin n := ⟨pairSwapIndex e mask, pairSwapIndex e mask,
    pairSwapIndex_involutive e mask, pairSwapIndex_involutive e mask⟩
  have hsum : ∑ i, realSigns (swapSignPairs e mask b) i = ∑ i, realSigns b i := by
    exact Fintype.sum_equiv p _ _ (fun i => rfl)
  rw [sum_realSigns_eq_signWeight, sum_realSigns_eq_signWeight] at hsum
  apply Fin.ext
  exact_mod_cast (show ((signWeight (swapSignPairs e mask b)).val : ℝ) = ((signWeight b).val : ℝ) by
    linarith only [hsum])

/-- Pair swaps preserve each fixed-weight slice law. -/
theorem uniformOn_signSlice_swapSignPairs {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (mask : Fin k → Bool) (m : Fin (n + 1)) (E : Set (Fin n → Bool)) :
    uniformOn (signSlice n m) (swapSignPairs e mask ⁻¹' E) = uniformOn (signSlice n m) E := by
  have hh : Function.Involutive (swapSignPairs e mask) := fun b => funext fun i =>
    congrArg b (pairSwapIndex_involutive e mask i)
  have h := Set.ncard_preimage_of_injective_subset_range (s := signSlice n m ∩ E) hh.injective
    (by simp [hh.surjective.range_eq])
  have hset : swapSignPairs e mask ⁻¹' (signSlice n m ∩ E) =
      signSlice n m ∩ (swapSignPairs e mask ⁻¹' E) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_inter_iff, signSlice, Set.mem_ofPred_eq, swapSignPairs_signWeight]
  rw [hset] at h
  rw [uniformOn_finite_apply (signSlice n m).toFinite, uniformOn_finite_apply (signSlice n m).toFinite, h]

private noncomputable def swapPairCoefficient {n k : ℕ} (e : Fin k × Bool ↪ Fin n) (a : Fin n → ℝ)
    (b : Fin n → Bool) (j : Fin k) : ℝ :=
  (a (e (j, false)) - a (e (j, true))) *
    (realSigns b (e (j, true)) - realSigns b (e (j, false))) / 2

private theorem swapPairCoefficient_abs_of_ne {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (a : Fin n → ℝ) (b : Fin n → Bool) (j : Fin k)
    (hj : b (e (j, false)) ≠ b (e (j, true))) :
    |swapPairCoefficient e a b j| = |a (e (j, false)) - a (e (j, true))| := by
  cases h₀ : b (e (j, false)) <;> cases h₁ : b (e (j, true))
  all_goals simp_all [swapPairCoefficient, realSigns, abs_mul, abs_div]
  all_goals ring

private theorem swapSignPairs_signSum {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (a : Fin n → ℝ) (b : Fin n → Bool) (mask : Fin k → Bool) :
    signSum a (swapSignPairs e mask b) = signSum a b +
      ∑ j, (if mask j then 2 * swapPairCoefficient e a b j else 0) := by
  let c (i : Fin n) := a i * (realSigns (swapSignPairs e mask b) i - realSigns b i)
  have hout (i : Fin n) (hi : i ∉ (Finset.univ : Finset (Fin k × Bool)).map e) : c i = 0 := by
    have hi' : i ∉ Set.range e := by simpa using hi
    simp [c, realSigns, swapSignPairs, pairSwapIndex_eq_of_notMem e mask hi']
  have hsum : ∑ i, c i = ∑ j : Fin k × Bool, c (e j) := by
    rw [← Finset.sum_map (Finset.univ : Finset (Fin k × Bool)) e]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hout i hi)).symm
  have hdiff : signSum a (swapSignPairs e mask b) - signSum a b = ∑ i, c i := by
    simp only [signSum, ← Finset.sum_sub_distrib, c, mul_sub, realSigns]
  have hp : (∑ i, c i) = ∑ j, if mask j then 2 * swapPairCoefficient e a b j else 0 := by
    rw [hsum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Fintype.sum_bool]
    cases hm : mask j
    all_goals simp [c, swapSignPairs, pairSwapIndex_apply, hm, realSigns, swapPairCoefficient]
    all_goals ring
  rw [← hp, ← hdiff]
  ring

private theorem uniformOn_swapMasks_smallBall {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (a : Fin n → ℝ) (b : Fin n → Bool) (z r : ℝ)
    (hgap : ∀ j, r < |a (e (j, false)) - a (e (j, true))|) :
    (uniformOn Set.univ).real {mask : Fin k → Bool | |signSum a (swapSignPairs e mask b) - z| ≤ r} ≤
      4 / Real.sqrt (((Finset.univ.filter fun j => b (e (j, false)) ≠ b (e (j, true))).card : ℝ) + 1) := by
  let I := Finset.univ.filter fun j => b (e (j, false)) ≠ b (e (j, true))
  let c (j : Fin k) := swapPairCoefficient e a b j
  let z' := z - signSum a b - ∑ j ∈ I, c j
  let ι : I ↪ Fin k := ⟨Subtype.val, Subtype.val_injective⟩
  let E : Set (I → Bool) := {x | |signSum (fun j : I => c j) x - z'| ≤ r}
  have hrestrict : {mask : Fin k → Bool | |signSum a (swapSignPairs e mask b) - z| ≤ r} =
      (fun (mask : Fin k → Bool) (j : I) => mask (ι j)) ⁻¹' E := by
    ext mask
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, E]
    rw [swapSignPairs_signSum]
    have hx (j : Fin k) (hj : j ∉ I) : c j = 0 := by
      have he : b (e (j, false)) = b (e (j, true)) := by simpa [I] using hj
      simp only [c, swapPairCoefficient, realSigns, he, sub_self, mul_zero, zero_div]
    have hfull : (∑ j, if mask j then 2 * swapPairCoefficient e a b j else 0) =
        ∑ j ∈ I, if mask j then 2 * c j else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro j _ hj
      rw [hx j hj]
      simp
    rw [hfull]
    have hh (j : Fin k) : (if mask j then 2 * c j else 0) =
        c j + c j * (if mask j then (1 : ℝ) else -1) := by
      cases mask j
      all_goals simp
      all_goals ring
    simp_rw [hh]
    rw [Finset.sum_add_distrib]
    have hss : signSum (fun j : I => c j) (fun j => mask (ι j)) =
        ∑ j ∈ I, c j * (if mask j then (1 : ℝ) else -1) :=
      Finset.sum_coe_sort I (fun j => c j * (if mask j then (1 : ℝ) else -1))
    rw [hss]
    have heq : signSum a b + ((∑ j ∈ I, c j) + ∑ j ∈ I, c j * (if mask j then (1 : ℝ) else -1)) - z =
        (∑ j ∈ I, c j * (if mask j then (1 : ℝ) else -1)) - z' := by dsimp [z']; ring
    rw [heq]
  have hmap : (uniformOn Set.univ : Measure (Fin k → Bool)).map
      (fun (x : Fin k → Bool) (j : I) => x (ι j)) = uniformOn Set.univ := by
    rw [← pi_uniformOn_univ, pi_map_restrict_embedding _ ι, pi_uniformOn_univ]
  rw [hrestrict, measureReal_def, ← Measure.map_apply (measurable_of_finite _) E.toFinite.measurableSet,
    hmap, ← measureReal_def, ← Fintype.card_coe]
  refine signSum_smallBall_le_four_div_sqrt (fun j : I => c j) z' r ?_
  intro j
  have hj := (Finset.mem_filter.mp j.2).2
  change r < |swapPairCoefficient e a b j|
  rw [swapPairCoefficient_abs_of_ne e a b j hj]
  exact hgap j

/-- The small-ball probability on a slice is bounded by the probability of
too few discordant pairs and the Littlewood–Offord estimate for those swaps. -/
theorem signSlice_smallBall_le_of_pairs {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (m : Fin (n + 1)) (hm : (signSlice n m).Nonempty) (a : Fin n → ℝ) (z r : ℝ)
    (hgap : ∀ j, r < |a (e (j, false)) - a (e (j, true))|) (s : ℕ) :
    (uniformOn (signSlice n m)).real {b | |signSum a b - z| ≤ r} ≤
      (uniformOn (signSlice n m)).real {b |
        (Finset.univ.filter fun j => b (e (j, false)) ≠ b (e (j, true))).card < s} +
      4 / Real.sqrt ((s : ℝ) + 1) := by
  let μ := uniformOn (signSlice n m)
  let ν : Measure (Fin k → Bool) := uniformOn Set.univ
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOn (signSlice n m).toFinite hm
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let E : Set (Fin n → Bool) := {b | |signSum a b - z| ≤ r}
  let H : Set ((Fin n → Bool) × (Fin k → Bool)) := {p | swapSignPairs e p.2 p.1 ∈ E}
  let U : Set (Fin n → Bool) := {b |
    (Finset.univ.filter fun j => b (e (j, false)) ≠ b (e (j, true))).card < s}
  let C := 4 / Real.sqrt ((s : ℝ) + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hprod : (μ.prod ν) H = μ E := by
    rw [Measure.prod_apply_symm H.toFinite.measurableSet]
    change (∫⁻ mask, μ (swapSignPairs e mask ⁻¹' E) ∂ν) = μ E
    simp only [μ, uniformOn_signSlice_swapSignPairs, lintegral_const, measure_univ, mul_one]
  have hle : μ E ≤ μ U + ENNReal.ofReal C := by
    rw [← hprod, Measure.prod_apply H.toFinite.measurableSet]
    calc
      _ ≤ ∫⁻ b, U.indicator (fun _ => 1) b + ENNReal.ofReal C ∂μ := by
        apply lintegral_mono
        intro b
        change ν {mask | |signSum a (swapSignPairs e mask b) - z| ≤ r} ≤
          U.indicator (fun _ => 1) b + ENNReal.ofReal C
        by_cases hb : b ∈ U
        · exact (prob_le_one (μ := ν)).trans (by rw [Set.indicator_of_mem hb]; simp)
        have hh := uniformOn_swapMasks_smallBall e a b z r hgap
        have hs : (s : ℝ) ≤ ((Finset.univ.filter fun j => b (e (j, false)) ≠ b (e (j, true))).card : ℝ) :=
          by exact_mod_cast le_of_not_gt hb
        have hcomp : 4 / Real.sqrt (((Finset.univ.filter fun j => b (e (j, false)) ≠ b (e (j, true))).card : ℝ) + 1) ≤ C :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (Real.sqrt_le_sqrt (by linarith only [hs]))
        rw [Set.indicator_of_notMem hb, zero_add, ← ENNReal.ofReal_toReal (measure_ne_top ν _)]
        exact ENNReal.ofReal_le_ofReal (hh.trans hcomp)
      _ = _ := by
        rw [lintegral_add_left (measurable_of_finite _), lintegral_indicator_const U.toFinite.measurableSet,
          one_mul, lintegral_const, measure_univ, mul_one]
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ U, ENNReal.ofReal_ne_top⟩) hle
  rw [ENNReal.toReal_add (measure_ne_top μ U) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hC] at h
  exact h

end BooleanThreshold
