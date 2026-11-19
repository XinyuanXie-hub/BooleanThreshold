module

public import BooleanThreshold.JSSConditionalMixture
public import BooleanThreshold.JSSConditionalPreprocessPaths
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace BooleanThreshold

/-- The first block of a finite tuple. -/
def sliceTuplePrefix {X : Type*} {a b n : ℕ} (h : a + b = n) (x : Fin n → X) : Fin a → X :=
  fun i => x (Fin.cast h (i.castAdd b))

/-- The second block of a finite tuple. -/
def sliceTupleSuffix {X : Type*} {a b n : ℕ} (h : a + b = n) (x : Fin n → X) : Fin b → X :=
  fun i => x (Fin.cast h (i.natAdd a))

private theorem sliceTuple_split_injective {X : Type*} {a b n : ℕ} (h : a + b = n) :
    Function.Injective (fun x : Fin n → X => (sliceTuplePrefix h x, sliceTupleSuffix h x)) := by
  intro x y heq
  have hl := congrArg Prod.fst heq
  have hr := congrArg Prod.snd heq
  funext i
  obtain ⟨j, rfl⟩ := (Fin.castOrderIso h).surjective i
  refine Fin.addCases ?_ ?_ j
  · intro j
    exact congrFun hl j
  · intro j
    exact congrFun hr j

theorem sliceAverage_prefix_eq_of_tuple {G : Type*} [AddCommMonoid G] {a b n : ℕ}
    (h : a + b = n) (encode : ℤ → G) (x : Fin n → ℤ) (f : G → ℝ) (s : ℕ) (t : G) :
    sliceAverage (sliceCoefficientArray encode x) f a s t =
      sliceAverage (sliceCoefficientArray encode (sliceTuplePrefix h x)) f a s t := by
  apply sliceAverage_eq_of_prefix
  intro i hi
  have hin : i < n := by omega
  simp only [sliceCoefficientArray, hin, hi, dite_true, sliceTuplePrefix]
  rfl

theorem sliceAverage_suffix_eq_of_tuple {G : Type*} [AddCommMonoid G] {a b n : ℕ}
    (h : a + b = n) (encode : ℤ → G) (x : Fin n → ℤ) (f : G → ℝ) (s : ℕ) (t : G) :
    sliceAverage (fun i => sliceCoefficientArray encode x (a + i)) f b s t =
      sliceAverage (sliceCoefficientArray encode (sliceTupleSuffix h x)) f b s t := by
  apply sliceAverage_eq_of_prefix
  intro i hi
  have hin : a + i < n := by omega
  simp only [sliceCoefficientArray, hin, hi, dite_true, sliceTupleSuffix]
  rfl

/-- Bound a count on a full box by the counts on its prefix and suffix. -/
theorem card_sliceTuple_le_of_bad_split {a b n D : ℕ} (h : a + b = n)
    (P : Fin n → Finset ℤ) (hD : ∀ i, (P i).card ≤ D)
    (Bad : (Fin n → ℤ) → Prop) (E : (Fin a → ℤ) → Prop)
    (F : (Fin a → ℤ) → (Fin b → ℤ) → Prop) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hE : ((Fintype.piFinset (sliceTuplePrefix h P)).filter E).card ≤ u * (D : ℝ) ^ a)
    (hF : ∀ x ∈ Fintype.piFinset (sliceTuplePrefix h P), ¬ E x →
      ((Fintype.piFinset (sliceTupleSuffix h P)).filter (F x)).card ≤ v * (D : ℝ) ^ b)
    (hcover : ∀ x ∈ Fintype.piFinset P, Bad x →
      E (sliceTuplePrefix h x) ∨ F (sliceTuplePrefix h x) (sliceTupleSuffix h x)) :
    ((Fintype.piFinset P).filter Bad).card ≤ (u + v) * (D : ℝ) ^ n := by
  let A := Fintype.piFinset (sliceTuplePrefix h P)
  let B := Fintype.piFinset (sliceTupleSuffix h P)
  let C := @Finset.filter _ (fun y => E y.1 ∨ F y.1 y.2)
    (fun _ => Classical.propDecidable _) (A.product B)
  have hsub : ((Fintype.piFinset P).filter Bad).card ≤ C.card := by
    refine Finset.card_le_card_of_injOn
      (fun x => (sliceTuplePrefix h x, sliceTupleSuffix h x)) ?_
      (sliceTuple_split_injective h).injOn
    intro x hx
    obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx
    have hMem := Fintype.mem_piFinset.mp hx
    refine (@Finset.mem_filter _ (fun y => E y.1 ∨ F y.1 y.2)
      (fun _ => Classical.propDecidable _) (A.product B)
      (sliceTuplePrefix h x, sliceTupleSuffix h x)).mpr
        ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hcover x hx he⟩
    · exact Fintype.mem_piFinset.mpr fun i => hMem _
    · exact Fintype.mem_piFinset.mpr fun i => hMem _
  have hA : (A.card : ℝ) ≤ (D : ℝ) ^ a := by
    simp only [A, Fintype.card_piFinset, Nat.cast_prod]
    rw [← show (∏ _i : Fin a, (D : ℝ)) = (D : ℝ) ^ a by simp]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun i _ => Nat.cast_le.mpr (hD _)
  have hB : (B.card : ℝ) ≤ (D : ℝ) ^ b := by
    simp only [B, Fintype.card_piFinset, Nat.cast_prod]
    rw [← show (∏ _i : Fin b, (D : ℝ)) = (D : ℝ) ^ b by simp]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun i _ => Nat.cast_le.mpr (hD _)
  have hC : (C.card : ℝ) ≤ (u * (D : ℝ) ^ a) * B.card + (A.card : ℝ) * (v * (D : ℝ) ^ b) := by
    refine card_product_filter_le_of_slice_fibers (u := u * (D : ℝ) ^ a)
      (v := v * (D : ℝ) ^ b) A B (fun y => E y.1 ∨ F y.1 y.2) E (by positivity)
      (show ((A.filter E).card : ℝ) ≤ _ from hE) ?_
    intro x hx he
    simpa only [he, false_or] using hF x hx he
  calc
    _ ≤ (C.card : ℝ) := Nat.cast_le.mpr hsub
    _ ≤ _ := hC
    _ ≤ (u * (D : ℝ) ^ a) * (D : ℝ) ^ b + (D : ℝ) ^ a * (v * (D : ℝ) ^ b) :=
      add_le_add (mul_le_mul_of_nonneg_left hB (by positivity))
        (mul_le_mul_of_nonneg_right hA (by positivity))
    _ = _ := by rw [← h, pow_add]; ring

end BooleanThreshold
