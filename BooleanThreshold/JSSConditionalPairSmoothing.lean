module

public import BooleanThreshold.JSSConditionalPairSwaps
public import BooleanThreshold.JSSConditionalFourierMoment
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel

public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace BooleanThreshold

/-- The subset sum selected by a Boolean vector. -/
@[expose] def selectedCoordinateSum {ι G : Type*} [Fintype ι] [AddCommMonoid G]
    (a : ι → G) (b : ι → Bool) : G :=
  ∑ j, if b j then a j else 0

/-- Pairs affected by a swap are those with different signs. -/
@[expose] def mixedPairIndices {n k : ℕ} (e : Fin k × Bool ↪ Fin n) (b : Fin n → Bool) :
    Finset (Fin k) :=
  univ.filter fun j => b (e (j, false)) ≠ b (e (j, true))

/-- The difference of the entering and leaving coefficient of a mixed pair. -/
@[expose] def pairedSubsetShift {n k : ℕ} {G : Type*} [AddCommGroup G]
    (e : Fin k × Bool ↪ Fin n) (a : Fin n → G) (b : Fin n → Bool) (j : Fin k) : G :=
  if b (e (j, false)) then a (e (j, true)) - a (e (j, false))
  else a (e (j, false)) - a (e (j, true))

theorem selectedCoordinateSum_swapSignPairs {n k : ℕ} {G : Type*} [AddCommGroup G]
    (e : Fin k × Bool ↪ Fin n) (a : Fin n → G) (b : Fin n → Bool) (mask : Fin k → Bool) :
    selectedCoordinateSum a (swapSignPairs e mask b) =
      selectedCoordinateSum a b +
        ∑ j ∈ mixedPairIndices e b, if mask j then pairedSubsetShift e a b j else 0 := by
  let c (i : Fin n) := (if swapSignPairs e mask b i then a i else 0) - (if b i then a i else 0)
  have hout (i : Fin n) (hi : i ∉ (univ : Finset (Fin k × Bool)).map e) : c i = 0 := by
    have hi' : i ∉ Set.range e := by simpa using hi
    simp [c, swapSignPairs_eq_of_notMem e mask b hi']
  have hsum : (∑ i, c i) = ∑ j : Fin k × Bool, c (e j) := by
    rw [← sum_map (univ : Finset (Fin k × Bool)) e]
    exact (sum_subset (subset_univ _) (fun i _ hi => hout i hi)).symm
  have hdiff : selectedCoordinateSum a (swapSignPairs e mask b) - selectedCoordinateSum a b =
      ∑ i, c i := by
    rw [selectedCoordinateSum, selectedCoordinateSum, ← sum_sub_distrib]
  have hp : (∑ i, c i) = ∑ j ∈ mixedPairIndices e b, if mask j then pairedSubsetShift e a b j else 0 := by
    rw [hsum, Fintype.sum_prod_type, mixedPairIndices, sum_filter]
    apply sum_congr rfl
    intro j _
    rw [Fintype.sum_bool]
    cases h₀ : b (e (j, false)) <;> cases h₁ : b (e (j, true)) <;> cases hm : mask j
    all_goals simp [c, swapSignPairs_apply, h₀, h₁, hm, pairedSubsetShift]
    all_goals abel
  rw [← hp, ← hdiff]
  abel

private theorem integral_uniformOn_bool_product {m : ℕ} (f : (Fin m → Bool) → ℂ) :
    (∫ b, f b ∂(uniformOn Set.univ)) = (∑ b, f b) / (2 : ℂ) ^ m := by
  have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
  have hf : Integrable f (uniformOn Set.univ) :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  rw [integral_fintype hf]
  simp only [uniformOn_univ_real_eq_card, Set.ncard_singleton, Nat.cast_one, hcard,
    Complex.real_smul]
  push_cast
  rw [← mul_sum]
  ring

/-- Independent fair shifts are the exact uniform average over their Boolean masks. -/
theorem cyclicShiftSmoothing_eq_mask_integral {P m : ℕ} (f : ZMod P → ℂ)
    (y : Fin m → ℤ) (t : ZMod P) :
    cyclicShiftSmoothing f y t =
      ∫ b : Fin m → Bool, f (t + (selectedCoordinateSum y b : ℤ)) ∂(uniformOn Set.univ) := by
  simp only [integral_uniformOn_bool_product]
  induction m generalizing t with
  | zero => simp [cyclicShiftSmoothing, selectedCoordinateSum]
  | succ m ih =>
    let e := Fin.consEquiv (fun _ : Fin (m + 1) => Bool)
    let F (b : Fin (m + 1) → Bool) := f (t + (selectedCoordinateSum y b : ℤ))
    change cyclicShiftSmoothing f y t = (∑ b, F b) / (2 : ℂ) ^ (m + 1)
    rw [← e.sum_comp F, Fintype.sum_prod_type, Fintype.sum_bool]
    have hsum (b : Fin m → Bool) (u : Bool) :
        selectedCoordinateSum y (e (u, b)) =
          (if u then y 0 else 0) + selectedCoordinateSum (Fin.tail y) b := by
      simp only [selectedCoordinateSum, Fin.sum_univ_succ, e, Fin.consEquiv_apply, Fin.cons_zero,
        Fin.cons_succ, Fin.tail]
    simp only [F, hsum, Bool.false_eq_true, ite_false, zero_add, ite_true, Int.cast_add]
    rw [cyclicShiftSmoothing, cyclicShiftAverage, ih, ih, pow_succ]
    simp only [← add_assoc]
    ring

/-- Concatenating two shift lists is the composition of their smoothing operators. -/
theorem cyclicShiftSmoothing_append {P m₁ m₂ : ℕ} (f : ZMod P → ℂ)
    (y₁ : Fin m₁ → ℤ) (y₂ : Fin m₂ → ℤ) :
    cyclicShiftSmoothing f (Fin.append y₂ y₁) =
      cyclicShiftSmoothing (cyclicShiftSmoothing f y₁) y₂ := by
  funext t
  simp_rw [cyclicShiftSmoothing_eq_mask_integral, integral_uniformOn_bool_product]
  have hsum (x₂ : Fin m₂ → Bool) (x₁ : Fin m₁ → Bool) :
      selectedCoordinateSum (Fin.append y₂ y₁) (Fin.append x₂ x₁) =
        selectedCoordinateSum y₂ x₂ + selectedCoordinateSum y₁ x₁ := by
    simp only [selectedCoordinateSum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  let e := Fin.appendEquiv (α := Bool) m₂ m₁
  rw [← e.sum_comp (fun b => f (t + (selectedCoordinateSum (Fin.append y₂ y₁) b : ℤ))),
    Fintype.sum_prod_type]
  simp only [e, Fin.appendEquiv, Equiv.coe_fn_mk, hsum, Int.cast_add, add_assoc]
  rw [← sum_div, div_div, pow_add (2 : ℂ) m₂ m₁, mul_comm ((2 : ℂ) ^ m₂)]

/-- Enumerate the mixed pairs by consecutive indices for the independent shift operations. -/
@[expose] noncomputable def mixedPairEmbedding {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (b : Fin n → Bool) : Fin (mixedPairIndices e b).card ↪ Fin k :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe (mixedPairIndices e b))).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

private theorem mixedPair_sum_reindex {n k : ℕ} {G : Type*} [AddCommMonoid G]
    (e : Fin k × Bool ↪ Fin n) (b : Fin n → Bool) (f : Fin k → G) :
    ∑ i : Fin (mixedPairIndices e b).card, f (mixedPairEmbedding e b i) =
      ∑ i ∈ mixedPairIndices e b, f i := by
  conv_rhs => rw [← sum_coe_sort]
  exact Fintype.sum_equiv
    (Fintype.equivFinOfCardEq (Fintype.card_coe (mixedPairIndices e b))).symm _ _ (fun _ => rfl)

private theorem integral_signSlice_swap_masks {n k : ℕ} (e : Fin k × Bool ↪ Fin n)
    (m : Fin (n + 1)) (F : (Fin n → Bool) → ℂ) :
    (∫ b, ∫ mask : Fin k → Bool, F (swapSignPairs e mask b) ∂(uniformOn Set.univ)
      ∂(uniformOn (signSlice n m))) = ∫ b, F b ∂(uniformOn (signSlice n m)) := by
  let μ := uniformOn (signSlice n m)
  let ν : Measure (Fin k → Bool) := uniformOn Set.univ
  let H (b : Fin n → Bool) (mask : Fin k → Bool) := F (swapSignPairs e mask b)
  have hH : Integrable (Function.uncurry H) (μ.prod ν) :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  change (∫ b, ∫ mask, H b mask ∂ν ∂μ) = ∫ b, F b ∂μ
  rw [integral_integral_swap hH]
  have hswap (mask : Fin k → Bool) : μ.map (swapSignPairs e mask) = μ := by
    ext E hE
    rw [Measure.map_apply (measurable_of_finite _) hE]
    exact uniformOn_signSlice_swapSignPairs e mask m E
  have hInt (mask : Fin k → Bool) : (∫ b, H b mask ∂μ) = ∫ b, F b ∂μ := by
    calc
      _ = ∫ b, F b ∂(μ.map (swapSignPairs e mask)) :=
        (integral_map (measurable_of_finite _).aemeasurable
          (measurable_of_finite F).aestronglyMeasurable).symm
      _ = _ := by rw [hswap mask]
  simp only [hInt, integral_const, probReal_univ, one_smul]

/-- The exact-slice average is a mixture of independent shift operators
supported on the mixed pairs of the sampled slice vector. -/
theorem integral_signSlice_subsetSum_eq_pair_smoothing {n k P : ℕ}
    (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1)) (a : Fin n → ℤ)
    (f : ZMod P → ℂ) (t : ZMod P) :
    (∫ b : Fin n → Bool, f (t + (selectedCoordinateSum a b : ℤ)) ∂(uniformOn (signSlice n m))) =
      ∫ b : Fin n → Bool,
        cyclicShiftSmoothing f (fun i => pairedSubsetShift e a b (mixedPairEmbedding e b i))
          (t + (selectedCoordinateSum a b : ℤ)) ∂(uniformOn (signSlice n m)) := by
  let F (b : Fin n → Bool) := f (t + (selectedCoordinateSum a b : ℤ))
  rw [← integral_signSlice_swap_masks e m F]
  apply integral_congr_ae
  filter_upwards with b
  let d := (mixedPairIndices e b).card
  let restriction (x : Fin k → Bool) (i : Fin d) := x (mixedPairEmbedding e b i)
  let y (i : Fin d) := pairedSubsetShift e a b (mixedPairEmbedding e b i)
  let u := t + (selectedCoordinateSum a b : ℤ)
  let G (x : Fin d → Bool) := f (u + (selectedCoordinateSum y x : ℤ))
  have he (mask : Fin k → Bool) : F (swapSignPairs e mask b) = G (restriction mask) := by
    have hsum : selectedCoordinateSum y (restriction mask) =
        ∑ i ∈ mixedPairIndices e b, if mask i then pairedSubsetShift e a b i else 0 :=
      mixedPair_sum_reindex e b (fun i => if mask i then pairedSubsetShift e a b i else 0)
    simp only [F, G, u, selectedCoordinateSum_swapSignPairs, hsum, Int.cast_add, add_assoc]
  have hmap : (uniformOn Set.univ : Measure (Fin k → Bool)).map restriction = uniformOn Set.univ := by
    rw [← pi_uniformOn_univ, pi_map_restrict_embedding _ (mixedPairEmbedding e b), pi_uniformOn_univ]
  change (∫ mask : Fin k → Bool, F (swapSignPairs e mask b) ∂(uniformOn Set.univ)) = cyclicShiftSmoothing f y u
  simp_rw [he]
  rw [cyclicShiftSmoothing_eq_mask_integral, show
    (∫ x : Fin d → Bool, f (u + (selectedCoordinateSum y x : ℤ)) ∂(uniformOn Set.univ)) =
      ∫ x : Fin d → Bool, G x ∂(uniformOn Set.univ) from rfl,
    ← hmap, integral_map (measurable_of_finite _).aemeasurable
      (measurable_of_finite G).aestronglyMeasurable]

end BooleanThreshold
