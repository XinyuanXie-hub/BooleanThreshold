module

public import BooleanThreshold.JSSConditionalSliceAverage
import Mathlib.Data.Nat.Choose.Vandermonde

public noncomputable section

open Finset
open scoped BigOperators Classical

namespace BooleanThreshold

private theorem slice_sum_split {G : Type*} [AddCommMonoid G]
    (X : ℕ → G) (f : G → ℝ) (a b s : ℕ) (t : G) :
    (∑ U ∈ (range (a + b)).powersetCard s, f (t + ∑ i ∈ U, X i)) =
      ∑ j ∈ range (s + 1), ∑ J ∈ (range b).powersetCard j,
        ∑ I ∈ (range a).powersetCard (s - j),
          f (t + (∑ u ∈ J, X (a + u)) + ∑ i ∈ I, X i) := by
  let e : ℕ ↪ ℕ := ⟨fun i => a + i, fun x y h => Nat.add_left_cancel h⟩
  let D := (range (s + 1)).sigma fun j =>
    ((range b).powersetCard j).product ((range a).powersetCard (s - j))
  let merge (z : Σ (_ : ℕ), Finset ℕ × Finset ℕ) := z.2.2 ∪ z.2.1.map e
  have hparts (z : Σ (_ : ℕ), Finset ℕ × Finset ℕ) (hz : z ∈ D) :
      z.1 ≤ s ∧ z.2.1 ⊆ range b ∧ z.2.1.card = z.1 ∧
        z.2.2 ⊆ range a ∧ z.2.2.card = s - z.1 := by
    obtain ⟨hj, hrest⟩ := mem_sigma.mp hz
    obtain ⟨hJ, hI⟩ := mem_product.mp hrest
    exact ⟨Nat.le_of_lt_succ (mem_range.mp hj), (mem_powersetCard.mp hJ).1,
      (mem_powersetCard.mp hJ).2, (mem_powersetCard.mp hI).1, (mem_powersetCard.mp hI).2⟩
  have hdisj {I J : Finset ℕ} (hI : I ⊆ range a) : Disjoint I (J.map e) := by
    apply disjoint_left.mpr
    intro x hx hJ
    have hxa := mem_range.mp (hI hx)
    obtain ⟨y, _, rfl⟩ := mem_map.mp hJ
    change a + y < a at hxa
    omega
  have hcombined (z : Σ (_ : ℕ), Finset ℕ × Finset ℕ) (hz : z ∈ D) :
      merge z ∈ (range (a + b)).powersetCard s := by
    obtain ⟨hj, hJ, hJc, hI, hIc⟩ := hparts z hz
    apply mem_powersetCard.mpr
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain hu | hu := mem_union.mp hu
      · exact mem_range.mpr ((mem_range.mp (hI hu)).trans_le (Nat.le_add_right _ _))
      · obtain ⟨v, hv, rfl⟩ := mem_map.mp hu
        exact mem_range.mpr (Nat.add_lt_add_left (mem_range.mp (hJ hv)) a)
    · dsimp only [merge]
      rw [card_union_of_disjoint (hdisj hI), card_map, hIc, hJc, Nat.sub_add_cancel hj]
  have hmerge_eq_left {I J : Finset ℕ} (hI : I ⊆ range a) :
      (I ∪ J.map e).filter (fun i => i < a) = I := by
    ext i
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hi | hi, ha⟩
      · exact hi
      · obtain ⟨j, _, rfl⟩ := mem_map.mp hi
        change a + j < a at ha
        omega
    · exact fun hi => ⟨Or.inl hi, mem_range.mp (hI hi)⟩
  have hmerge_eq_right {I J : Finset ℕ} (hI : I ⊆ range a) :
      (I ∪ J.map e).filter (fun i => a ≤ i) = J.map e := by
    ext i
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hi | hi, ha⟩
      · exact False.elim ((mem_range.mp (hI hi)).not_ge ha)
      · exact hi
    · intro hi
      refine ⟨Or.inr hi, ?_⟩
      obtain ⟨j, _, rfl⟩ := mem_map.mp hi
      exact Nat.le_add_right a j
  have hinj : Set.InjOn merge (D : Set (Σ (_ : ℕ), Finset ℕ × Finset ℕ)) := by
    rintro ⟨j, J, I⟩ hz ⟨j', J', I'⟩ hz' he
    obtain ⟨_, _, hj, hI, _⟩ := hparts ⟨j, J, I⟩ hz
    obtain ⟨_, _, hj', hI', _⟩ := hparts ⟨j', J', I'⟩ hz'
    have hle := congrArg (fun U : Finset ℕ => U.filter (fun i => i < a)) he
    have hre := congrArg (fun U : Finset ℕ => U.filter (fun i => a ≤ i)) he
    change (I ∪ J.map e).filter (fun i => i < a) = (I' ∪ J'.map e).filter (fun i => i < a) at hle
    change (I ∪ J.map e).filter (fun i => a ≤ i) = (I' ∪ J'.map e).filter (fun i => a ≤ i) at hre
    rw [hmerge_eq_left hI, hmerge_eq_left hI'] at hle
    rw [hmerge_eq_right hI, hmerge_eq_right hI'] at hre
    have hJ : J = J' := Finset.map_injective e hre
    change I = I' at hle
    change J.card = j at hj
    change J'.card = j' at hj'
    have hcount : j = j' := hj.symm.trans ((congrArg Finset.card hJ).trans hj')
    rw [← hcount, ← hJ, ← hle]
  have hsurj (U : Finset ℕ) (hU : U ∈ (range (a + b)).powersetCard s) :
      ∃ z ∈ D, merge z = U := by
    obtain ⟨hUsub, hUcard⟩ := mem_powersetCard.mp hU
    let I := U.filter (fun i => i < a)
    let V := U.filter (fun i => a ≤ i)
    let J := V.image (fun i => i - a)
    have hI : I ⊆ range a := fun i hi => mem_range.mpr (mem_filter.mp hi).2
    have hJ : J ⊆ range b := by
      intro j hj
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hj
      have hvlow := (mem_filter.mp hv).2
      have hvhigh := mem_range.mp (hUsub (mem_filter.mp hv).1)
      exact mem_range.mpr (by omega)
    have hV : J.map e = V := by
      ext v
      constructor
      · intro hv
        obtain ⟨j, hj, rfl⟩ := mem_map.mp hv
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hj
        have hwlow := (mem_filter.mp hw).2
        change a + (w - a) ∈ V
        rwa [Nat.add_sub_of_le hwlow]
      · intro hv
        refine mem_map.mpr ⟨v - a, mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
        exact Nat.add_sub_of_le (mem_filter.mp hv).2
    have hUV : I ∪ J.map e = U := by
      rw [hV]
      ext i
      simp only [I, V, mem_union, mem_filter]
      exact ⟨fun hi => hi.elim And.left And.left, fun hi =>
        (lt_or_ge i a).imp (fun h => ⟨hi, h⟩) (fun h => ⟨hi, h⟩)⟩
    have hcard : I.card + J.card = s := by
      have hc : (J.map e).card = J.card := card_map e
      rw [← hc, ← card_union_of_disjoint (hdisj hI), hUV, hUcard]
    have hjlt : J.card ∈ range (s + 1) := mem_range.mpr (by omega)
    have hiCard : I.card = s - J.card := by omega
    exact ⟨⟨J.card, J, I⟩, mem_sigma.mpr ⟨hjlt, mem_product.mpr
      ⟨mem_powersetCard.mpr ⟨hJ, rfl⟩, mem_powersetCard.mpr ⟨hI, hiCard⟩⟩⟩, hUV⟩
  calc
    _ = ∑ z ∈ D, f (t + ∑ i ∈ merge z, X i) := by
      symm
      refine Finset.sum_bij (fun z _ => merge z) hcombined
        (fun z hz z' hz' he => hinj hz hz' he) ?_ (fun _ _ => rfl)
      intro U hU
      obtain ⟨z, hz, he⟩ := hsurj U hU
      exact ⟨z, hz, he⟩
    _ = _ := by
      rw [show D = (range (s + 1)).sigma (fun j =>
        ((range b).powersetCard j).product ((range a).powersetCard (s - j))) from rfl, sum_sigma]
      apply sum_congr rfl
      intro j hj
      calc
        _ = ∑ J ∈ (range b).powersetCard j, ∑ I ∈ (range a).powersetCard (s - j),
            f (t + ∑ i ∈ merge ⟨j, (J, I)⟩, X i) :=
          sum_product ((range b).powersetCard j) ((range a).powersetCard (s - j))
            (fun z => f (t + ∑ i ∈ merge ⟨j, z⟩, X i))
        _ = _ := by
          apply sum_congr rfl
          intro J _
          apply sum_congr rfl
          intro I hi
          have hd := hdisj (J := J) (mem_powersetCard.mp hi).1
          change f (t + ∑ i ∈ I ∪ J.map e, X i) = _
          rw [sum_union hd, sum_map, ← add_assoc, add_right_comm t]
          rfl

/-- The conditional weight of choosing exactly `j` elements from the second block. -/
@[expose] def sliceSplitWeight (a b s j : ℕ) : ℝ :=
  (a.choose (s - j) : ℝ) * (b.choose j : ℝ) / ((a + b).choose s : ℝ)

theorem sliceSplitWeight_nonneg (a b s j : ℕ) : 0 ≤ sliceSplitWeight a b s j := by
  unfold sliceSplitWeight
  positivity

theorem sliceSplitWeight_eq_zero_of_not_feasible {a b s j : ℕ}
    (h : ¬ (s - j ≤ a ∧ j ≤ b)) : sliceSplitWeight a b s j = 0 := by
  by_cases h₁ : s - j ≤ a
  · have h₂ : b < j := lt_of_not_ge fun hj => h ⟨h₁, hj⟩
    simp [sliceSplitWeight, Nat.choose_eq_zero_of_lt h₂]
  · simp [sliceSplitWeight, Nat.choose_eq_zero_of_lt (lt_of_not_ge h₁)]

/-- Splitting a fixed-size subset between two contiguous blocks gives a mixture
of independent averages on the two blocks. -/
theorem sliceAverage_split {G : Type*} [AddCommMonoid G]
    (X : ℕ → G) (f : G → ℝ) (a b s : ℕ) (t : G) :
    sliceAverage X f (a + b) s t = ∑ j ∈ range (s + 1), sliceSplitWeight a b s j *
      sliceAverage (fun i => X (a + i)) (sliceAverage X f a (s - j)) b j t := by
  change (∑ I ∈ (range (a + b)).powersetCard s, f (t + ∑ i ∈ I, X i)) / _ = _
  rw [slice_sum_split X f a b s t]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  have hinner :
      (∑ J ∈ (range b).powersetCard j, ∑ I ∈ (range a).powersetCard (s - j),
          f (t + (∑ u ∈ J, X (a + u)) + ∑ i ∈ I, X i)) =
        ∑ J ∈ (range b).powersetCard j, (a.choose (s - j) : ℝ) *
          sliceAverage X f a (s - j) (t + ∑ u ∈ J, X (a + u)) :=
    sum_congr rfl fun J _ => slice_sum_eq_mul_average X f a (s - j) _
  have houter :
      (∑ J ∈ (range b).powersetCard j, sliceAverage X f a (s - j) (t + ∑ u ∈ J, X (a + u))) =
        (b.choose j : ℝ) * sliceAverage (fun i => X (a + i)) (sliceAverage X f a (s - j)) b j t :=
    slice_sum_eq_mul_average (fun i => X (a + i)) (sliceAverage X f a (s - j)) b j t
  rw [hinner, ← Finset.mul_sum, houter]
  unfold sliceSplitWeight
  ring

/-- The mixture can be summed over the pairs of counts that fit in the two blocks. -/
theorem sliceAverage_split_feasible {G : Type*} [AddCommMonoid G]
    (X : ℕ → G) (f : G → ℝ) (a b s : ℕ) (t : G) :
    sliceAverage X f (a + b) s t =
      ∑ j ∈ (range (s + 1)).filter (fun j => s - j ≤ a ∧ j ≤ b), sliceSplitWeight a b s j *
        sliceAverage (fun i => X (a + i)) (sliceAverage X f a (s - j)) b j t := by
  rw [sliceAverage_split]
  symm
  apply sum_subset (Finset.filter_subset _ _)
  intro j hj hnot
  rw [sliceSplitWeight_eq_zero_of_not_feasible (fun h => hnot (mem_filter.mpr ⟨hj, h⟩)), zero_mul]

theorem sliceSplitWeight_sum_eq_one {a b s : ℕ} (hs : s ≤ a + b) :
    (∑ j ∈ range (s + 1), sliceSplitWeight a b s j) = 1 := by
  unfold sliceSplitWeight
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have h : (∑ j ∈ range (s + 1), (a.choose (s - j) : ℝ) * (b.choose j : ℝ)) =
      ((a + b).choose s : ℝ) := by
    have hv := Nat.add_choose_eq b a s
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
    exact_mod_cast (by simpa only [mul_comm, add_comm b a] using hv.symm :
      (∑ j ∈ range (s + 1), a.choose (s - j) * b.choose j) = (a + b).choose s)
  rw [h, mul_inv_cancel₀]
  exact_mod_cast (Nat.choose_pos hs).ne'

theorem sliceSplitWeight_swap {a b s j : ℕ} (hj : j ≤ s) :
    sliceSplitWeight a b s j = sliceSplitWeight b a s (s - j) := by
  simp only [sliceSplitWeight, Nat.sub_sub_self hj, add_comm b a, mul_comm]

/-- A test on the first block count can be rewritten as a test on the second
block count after swapping the block lengths. -/
theorem sum_ite_sliceSplitWeight_swap (a b s : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ j ∈ range (s + 1), if Q (s - j) then sliceSplitWeight a b s j else 0) =
      ∑ j ∈ range (s + 1), if Q j then sliceSplitWeight b a s j else 0 := by
  refine Finset.sum_bij (fun j _ => s - j) ?_ ?_ ?_ ?_
  · intro j _
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  · intro j hj k hk h
    have hj' := mem_range.mp hj
    have hk' := mem_range.mp hk
    omega
  · intro j hj
    refine ⟨s - j, mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)), ?_⟩
    exact Nat.sub_sub_self (Nat.le_of_lt_succ (mem_range.mp hj))
  · intro j hj
    rw [sliceSplitWeight_swap (Nat.le_of_lt_succ (mem_range.mp hj))]

end BooleanThreshold
