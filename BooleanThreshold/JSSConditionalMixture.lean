module

public import BooleanThreshold.JSSConditionalSliceBlocks

public section

open scoped BigOperators Classical

namespace BooleanThreshold

/-- A split slice combines the bounds for the balanced suffix weights with
the total weight of the exceptional suffix sizes. -/
theorem sliceAverage_split_le_of_good_weights {G : Type*} [AddCommMonoid G]
    (X : ℕ → G) (f : G → ℝ) {a b s : ℕ} (hs : s ≤ a + b)
    {T A β : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (Good : ℕ → Prop)
    (hβ : (∑ j ∈ Finset.range (s + 1),
      if Good j then 0 else sliceSplitWeight a b s j) ≤ β)
    (hcap : ∀ j ≤ s, j ≤ b → s - j ≤ a → ∀ t, sliceAverage X f a (s - j) t ≤ A)
    (hgood : ∀ j ≤ s, j ≤ b → s - j ≤ a → Good j → ∀ t,
      sliceAverage (fun i => X (a + i)) (sliceAverage X f a (s - j)) b j t ≤ T)
    (t : G) : sliceAverage X f (a + b) s t ≤ T + A * β := by
  rw [sliceAverage_split]
  calc
    _ ≤ ∑ j ∈ Finset.range (s + 1), sliceSplitWeight a b s j *
        (T + if Good j then 0 else A) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hfeas : j ≤ b ∧ s - j ≤ a
      · rcases hfeas with ⟨hjb, hja⟩
        have hjs : j ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        apply mul_le_mul_of_nonneg_left _ (sliceSplitWeight_nonneg a b s j)
        by_cases hg : Good j
        · simpa only [hg, ite_true, add_zero] using hgood j hjs hjb hja hg t
        · simp only [hg, ite_false]
          refine (sliceAverage_le_of_le _ _ hjb (hcap j hjs hjb hja) _).trans ?_
          exact le_add_of_nonneg_left hT
      · have hzero : sliceSplitWeight a b s j = 0 := by
          by_cases h : j ≤ b
          · have h' : a < s - j := lt_of_not_ge fun h' => hfeas ⟨h, h'⟩
            simp [sliceSplitWeight, Nat.choose_eq_zero_of_lt h']
          · simp [sliceSplitWeight, Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]
        simp [hzero]
    _ = T + A * ∑ j ∈ Finset.range (s + 1), if Good j then 0 else sliceSplitWeight a b s j := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sliceSplitWeight_sum_eq_one hs,
        one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hg : Good j <;> simp [hg, mul_comm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hβ hA)

/-- A product sample is exceptional when its first part is exceptional or
the second part lies in the exceptional fiber of a good first part. -/
theorem card_product_filter_le_of_slice_fibers {X Y : Type*} (A : Finset X) (B : Finset Y)
    (Bad : X × Y → Prop) (E : X → Prop) {u v : ℝ} (hv : 0 ≤ v)
    (hE : ((A.filter E).card : ℝ) ≤ u)
    (hB : ∀ x ∈ A, ¬ E x → ((B.filter (fun y => Bad (x, y))).card : ℝ) ≤ v) :
    (((A.product B).filter Bad).card : ℝ) ≤ u * B.card + A.card * v := by
  let S := A.filter E
  let C (x : X) := (B.filter fun y => Bad (x, y)).image (Prod.mk x)
  have hsub : (A.product B).filter Bad ⊆
      (S.product B) ∪ (A \ S).biUnion C := by
    rintro ⟨x, y⟩ hz
    obtain ⟨hxy, hBad⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    by_cases he : E x
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hx, he⟩, hy⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_sdiff.mpr ⟨hx, fun hh => he (Finset.mem_filter.mp hh).2⟩,
          Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hBad⟩, rfl⟩⟩)
  have hcard : ((A \ S).biUnion C).card ≤ ∑ x ∈ A \ S, (C x).card := Finset.card_biUnion_le
  have hprod : (S.product B).card = S.card * B.card := Finset.card_product S B
  have hbound : (((A \ S).biUnion C).card : ℝ) ≤ (A.card : ℝ) * v := by
    calc
      _ ≤ ∑ x ∈ A \ S, ((C x).card : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ _x ∈ A \ S, v := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hx, hx'⟩ := Finset.mem_sdiff.mp hx
        have he : ¬ E x := fun h => hx' (Finset.mem_filter.mpr ⟨hx, h⟩)
        exact (Nat.cast_le.mpr Finset.card_image_le).trans (hB x hx he)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)) hv
  calc
    _ ≤ (S.card : ℝ) * B.card + ((A \ S).biUnion C).card := by
      have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [hprod] at h
      exact_mod_cast h
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg _)) hbound

/-- A finite family of exceptional conditions costs at most the sum of the
individual exceptional counts. -/
theorem card_filter_exists_le_of_each {X I : Type*}
    (A : Finset X) (J : Finset I) (Bad : I → X → Prop)
    {u : ℝ} (h : ∀ i ∈ J, ((A.filter (Bad i)).card : ℝ) ≤ u) :
    ((A.filter (fun x => ∃ i ∈ J, Bad i x)).card : ℝ) ≤ J.card * u := by
  have hsub : A.filter (fun x => ∃ i ∈ J, Bad i x) ⊆ J.biUnion (fun i => A.filter (Bad i)) := by
    intro x hx
    obtain ⟨hx, i, hi, hBad⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hx, hBad⟩⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ i ∈ J, ((A.filter (Bad i)).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _i ∈ J, u := Finset.sum_le_sum h
    _ = _ := by simp

end BooleanThreshold
