module

public import BooleanThreshold.JSSConditionalSlice
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace BooleanThreshold

/-- The average of a translate over the subsets of the prefix with prescribed size. -/
@[expose] noncomputable def sliceAverage {G : Type*} [AddCommMonoid G]
    (X : ℕ → G) (f : G → ℝ) (ℓ s : ℕ) (t : G) : ℝ :=
  (∑ I ∈ (range ℓ).powersetCard s, f (t + ∑ i ∈ I, X i)) / (ℓ.choose s : ℝ)

@[simp]
theorem sliceAverage_zero {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    (ℓ : ℕ) (t : G) : sliceAverage X f ℓ 0 t = f t := by
  simp [sliceAverage]

theorem sliceAverage_eq_zero_of_lt {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    {ℓ s : ℕ} (hs : ℓ < s) (t : G) : sliceAverage X f ℓ s t = 0 := by
  simp [sliceAverage, Nat.choose_eq_zero_of_lt hs]

/-- Recover the subset sum by multiplying its average by the number of subsets. -/
theorem slice_sum_eq_mul_average {G : Type*} [AddCommMonoid G]
    (X : ℕ → G) (f : G → ℝ) (ℓ s : ℕ) (t : G) :
    (∑ I ∈ (range ℓ).powersetCard s, f (t + ∑ i ∈ I, X i)) =
      (ℓ.choose s : ℝ) * sliceAverage X f ℓ s t := by
  by_cases hs : s ≤ ℓ
  · rw [sliceAverage, mul_div_cancel₀]
    exact_mod_cast (Nat.choose_pos hs).ne'
  · have hm : (range ℓ).powersetCard s = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty, Finset.powersetCard_nonempty, Finset.card_range]
      exact hs
    rw [hm, sum_empty, Nat.choose_eq_zero_of_lt (lt_of_not_ge hs), Nat.cast_zero, zero_mul]

/-- Appending one coordinate splits the average according to whether that
coordinate belongs to the uniformly selected subset. -/
theorem sliceAverage_succ {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    {ℓ s : ℕ} (hs : s ≤ ℓ) (t : G) :
    sliceAverage X f (ℓ + 1) (s + 1) t =
      (1 - ((s + 1 : ℕ) : ℝ) / ((ℓ + 1 : ℕ) : ℝ)) * sliceAverage X f ℓ (s + 1) t +
        (((s + 1 : ℕ) : ℝ) / ((ℓ + 1 : ℕ) : ℝ)) * sliceAverage X f ℓ s (t + X ℓ) := by
  have hnot : ℓ ∉ range ℓ := notMem_range_self
  have hsplit :
      (∑ I ∈ (range (ℓ + 1)).powersetCard (s + 1), f (t + ∑ i ∈ I, X i)) =
      (∑ I ∈ (range ℓ).powersetCard (s + 1), f (t + ∑ i ∈ I, X i)) +
        ∑ I ∈ (range ℓ).powersetCard s, f (t + X ℓ + ∑ i ∈ I, X i) := by
    have hI {r : ℕ} {I : Finset ℕ} (hi : I ∈ (range ℓ).powersetCard r) : ℓ ∉ I :=
      fun h => hnot ((mem_powersetCard.mp hi).1 h)
    rw [range_add_one, powersetCard_succ_insert hnot]
    rw [Finset.sum_union (by
      refine Finset.disjoint_left.mpr fun I hi hj => hI hi ?_
      obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_insert_self _ _)]
    rw [Finset.sum_image (by
      intro I hi J hj h
      have hh := congrArg (fun A : Finset ℕ => A.erase ℓ) h
      simpa only [Finset.erase_insert (hI hi), Finset.erase_insert (hI hj)] using hh)]
    congr 1
    exact Finset.sum_congr rfl fun I hi => by rw [Finset.sum_insert (hI hi), ← add_assoc]
  let A : ℝ := ℓ.choose (s + 1)
  let B : ℝ := ℓ.choose s
  let D : ℝ := (ℓ + 1).choose (s + 1)
  let a : ℝ := (s + 1 : ℕ)
  let l : ℝ := (ℓ + 1 : ℕ)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos (Nat.succ_le_succ hs)
  have hl : 0 < l := by dsimp [l]; positivity
  have hA' : A * l = D * (l - a) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul_succ_eq ℓ (s + 1))
    simp only [Nat.cast_mul, Nat.add_sub_add_right, Nat.cast_sub hs] at h
    dsimp [A, D, l, a]
    push_cast at h ⊢
    rw [show (ℓ : ℝ) + 1 - ((s : ℝ) + 1) = (ℓ : ℝ) - s by ring]
    exact h
  have hA : A / D = 1 - a / l := by
    rw [show 1 - a / l = (l - a) / l by field_simp]
    apply (div_eq_div_iff hD.ne' hl.ne').mpr
    linarith only [hA']
  have hAB : A + B = D := by
    dsimp [A, B, D]
    rw [Nat.choose_succ_succ ℓ s, Nat.cast_add, add_comm]
  have hB : B / D = a / l := by
    have h := congrArg (fun v : ℝ => v / D) hAB
    rw [add_div, div_self hD.ne', hA] at h
    linarith only [h]
  rw [sliceAverage, hsplit, slice_sum_eq_mul_average X f, slice_sum_eq_mul_average X f]
  change (A * sliceAverage X f ℓ (s + 1) t + B * sliceAverage X f ℓ s (t + X ℓ)) / D =
    (1 - a / l) * sliceAverage X f ℓ (s + 1) t + (a / l) * sliceAverage X f ℓ s (t + X ℓ)
  rw [← hA, ← hB]
  ring


/-- A fixed-slice average of a nonnegative function is nonnegative. -/
theorem sliceAverage_nonneg {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    (hf : ∀ t, 0 ≤ f t) (ℓ s : ℕ) (t : G) :
    0 ≤ sliceAverage X f ℓ s t := by
  exact div_nonneg (sum_nonneg (fun I _ => hf _)) (Nat.cast_nonneg _)

/-- A fixed-slice average preserves a uniform pointwise bound. -/
theorem sliceAverage_le_of_le {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    {ℓ s : ℕ} (hs : s ≤ ℓ) {R : ℝ} (hf : ∀ t, f t ≤ R) (t : G) :
    sliceAverage X f ℓ s t ≤ R := by
  have h : 0 < (ℓ.choose s : ℝ) := by exact_mod_cast Nat.choose_pos hs
  apply (div_le_iff₀ h).mpr
  calc
    _ ≤ ∑ _I ∈ (range ℓ).powersetCard s, R := sum_le_sum (fun _ _ => hf _)
    _ = _ := by simp [card_powersetCard, nsmul_eq_mul, mul_comm]

/-- A bound for the mass on all translates of an interval or finite set
is preserved by a fixed-slice average. -/
theorem sum_sliceAverage_le_of_local_bound {G : Type*} [AddCommMonoid G]
    (X : ℕ → G) (f : G → ℝ) {ℓ s : ℕ} (hs : s ≤ ℓ) (W : Finset G) {R : ℝ}
    (hf : ∀ u, ∑ t ∈ W, f (t + u) ≤ R) :
    ∑ t ∈ W, sliceAverage X f ℓ s t ≤ R := by
  have h : 0 < (ℓ.choose s : ℝ) := by exact_mod_cast Nat.choose_pos hs
  simp only [sliceAverage]
  rw [← Finset.sum_div, Finset.sum_comm]
  apply (div_le_iff₀ h).mpr
  calc
    _ ≤ ∑ _I ∈ (range ℓ).powersetCard s, R := sum_le_sum (fun _ _ => hf _)
    _ = _ := by simp [card_powersetCard, nsmul_eq_mul, mul_comm]

/-- A fixed-slice average preserves the total mass with counting measure. -/
theorem sum_sliceAverage_eq_sum {G : Type*} [Fintype G] [AddCommGroup G]
    (X : ℕ → G) (f : G → ℝ) {ℓ s : ℕ} (hs : s ≤ ℓ) :
    ∑ t : G, sliceAverage X f ℓ s t = ∑ t : G, f t := by
  have h : (ℓ.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
  simp only [sliceAverage]
  rw [← Finset.sum_div, Finset.sum_comm]
  have he (u : G) : ∑ t : G, f (t + u) = ∑ t : G, f t :=
    Fintype.sum_equiv (Equiv.addRight u) _ _ (fun _ => rfl)
  simp only [he, sum_const, nsmul_eq_mul, card_powersetCard, card_range]
  exact mul_div_cancel_left₀ _ h

private def signSupport {n : ℕ} (b : Fin n → Bool) : Finset ℕ :=
  (univ.filter fun i => b i).map Fin.valEmbedding

private theorem mem_signSupport {n : ℕ} (b : Fin n → Bool) (i : Fin n) :
    i.val ∈ signSupport b ↔ b i = true := by
  rw [signSupport, mem_map]
  constructor
  · rintro ⟨j, hj, h⟩
    have he : j = i := Fin.ext h
    subst j
    exact (mem_filter.mp hj).2
  · intro h
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, h⟩, rfl⟩

private noncomputable def signSliceEquivPowersetCard (n : ℕ) (m : Fin (n + 1)) :
    signSlice n m ≃ ((range n).powersetCard m.val : Finset (Finset ℕ)) := by
  let S := signSlice n m
  let I := (range n).powersetCard m.val
  let toSet (b : S) : I := ⟨signSupport b.val, by
    apply mem_powersetCard.mpr
    constructor
    · intro j hj
      obtain ⟨i, _, hi⟩ := mem_map.mp hj
      exact mem_range.mpr (hi ▸ i.isLt)
    · have hb : signWeight b.val = m := b.prop
      exact (card_map _).trans (congrArg Fin.val hb)⟩
  apply Equiv.ofBijective toSet
  constructor
  · intro b c h
    have hS : signSupport b.val = signSupport c.val := congrArg Subtype.val h
    apply Subtype.ext
    funext i
    have hi : b.val i = true ↔ c.val i = true := by
      rw [← mem_signSupport, ← mem_signSupport, hS]
    cases hb : b.val i <;> cases hc : c.val i <;> simp_all
  · intro J
    let b (i : Fin n) := decide (i.val ∈ J.val)
    have hb : signSupport b = J.val := by
      ext j
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := mem_map.mp hj
        exact of_decide_eq_true (mem_filter.mp hi).2
      · intro hj
        have hJ : J.val ⊆ range n := (mem_powersetCard.mp J.prop).1
        have hi : j < n := mem_range.mp (hJ hj)
        exact (mem_signSupport b ⟨j, hi⟩).mpr (decide_eq_true hj)
    have hbS : b ∈ S := by
      apply Fin.ext
      change (univ.filter fun i => b i).card = m.val
      rw [← card_map Fin.valEmbedding, ← signSupport, hb]
      exact (mem_powersetCard.mp J.prop).2
    exact ⟨⟨b, hbS⟩, Subtype.ext hb⟩

private theorem integral_uniformOn_finset_average {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (S : Set α) (f : α → ℝ) :
    ∫ b, f b ∂(uniformOn S) = (∑ b : S, f b.val) / S.ncard := by
  classical
  let μ := uniformOn S
  let P := S.toFinite.toFinset
  have hμ (b : α) : μ.real {b} = if b ∈ S then (S.ncard : ℝ)⁻¹ else 0 := by
    rw [measureReal_def, uniformOn_finite_apply S.toFinite, ENNReal.toReal_div]
    by_cases hb : b ∈ S <;> simp [hb]
  have hf : Integrable f μ :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  rw [integral_fintype hf]
  simp_rw [hμ, smul_eq_mul, ite_mul, zero_mul]
  rw [← sum_filter]
  have hP : (univ.filter fun b => b ∈ S) = P := by ext b; simp [P]
  rw [hP, ← mul_sum, div_eq_mul_inv, mul_comm]
  congr 1
  exact sum_subtype P (fun x => S.toFinite.mem_toFinset) f

/-- The subset average equals the expectation over the corresponding sign slice. -/
theorem integral_signSlice_eq_sliceAverage {G : Type*} [AddCommMonoid G]
    {n : ℕ} (m : Fin (n + 1)) (X : ℕ → G) (f : G → ℝ) (t : G) :
    ∫ b : Fin n → Bool, f (t + ∑ i ∈ univ.filter (fun i => b i), X i.val)
      ∂(uniformOn (signSlice n m)) = sliceAverage X f n m.val t := by
  let e := signSliceEquivPowersetCard n m
  let A := (range n).powersetCard m.val
  have hcard : (signSlice n m).ncard = n.choose m.val := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_coe, card_powersetCard, card_range]
  rw [integral_uniformOn_finset_average, sliceAverage, hcard]
  congr 1
  rw [← Finset.sum_coe_sort (s := A) (f := fun I => f (t + ∑ i ∈ I, X i))]
  apply Fintype.sum_equiv e
  intro b
  change f (t + ∑ i ∈ univ.filter (fun i => b.val i), X i.val) =
    f (t + ∑ i ∈ signSupport b.val, X i)
  simp only [signSupport, Finset.sum_map, Fin.valEmbedding_apply]

/-- Signed coefficients give the subset coefficients `a+a`, with the common
translation given by the negative sum of the signed coefficients. -/
theorem signed_sum_eq_subset_sum {G : Type*} [AddCommGroup G]
    {n : ℕ} (a : Fin n → G) (b : Fin n → Bool) :
    (∑ i, if b i then a i else -a i) =
      -(∑ i, a i) + ∑ i ∈ univ.filter (fun i => b i), (a i + a i) := by
  rw [sum_filter, ← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases b i <;> simp

/-- Applying a kernel to a signed sum on one slice is the corresponding
convolution over a fixed-size subset of indices. -/
theorem integral_signSlice_signed_sum_eq_sliceAverage {G : Type*} [AddCommGroup G]
    {n : ℕ} (m : Fin (n + 1)) (a : Fin n → G) (f : G → ℝ) (t : G) :
    ∫ b : Fin n → Bool, f (t + ∑ i, if b i then a i else -a i)
      ∂(uniformOn (signSlice n m)) =
      sliceAverage (fun i => if hi : i < n then a ⟨i, hi⟩ + a ⟨i, hi⟩ else 0)
        f n m.val (t - ∑ i, a i) := by
  rw [← integral_signSlice_eq_sliceAverage]
  congr 1
  funext b
  rw [signed_sum_eq_subset_sum, sub_eq_add_neg, add_assoc]
  simp only [Fin.isLt, dite_eq_left, Fin.eta]

end BooleanThreshold
