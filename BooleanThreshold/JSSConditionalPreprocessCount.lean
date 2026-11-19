module

public import BooleanThreshold.JSSConditionalPathEntropy
public import BooleanThreshold.JSSConditionalPreprocessPaths

@[expose] public section

open scoped BigOperators Classical

namespace BooleanThreshold

/-- The coefficient tuples for which a prefix average has a high value. -/
noncomputable def highSliceAverages {G : Type*} [AddCommGroup G] {ℓ : ℕ}
    (encode : ℤ → G) (B : Fin ℓ → Finset ℤ) (f : G → ℝ) (s : ℕ) (τ : ℝ) : Finset (Fin ℓ → ℤ) :=
  (Fintype.piFinset B).filter fun x => ∃ t : G, τ ≤ sliceAverage (sliceCoefficientArray encode x) f ℓ s t

private def extendBitRecord {ℓ : ℕ} (w : Fin ℓ → Bool) (i : ℕ) : Bool :=
  if h : i < ℓ then w ⟨i, h⟩ else false

private theorem late_robustSteps_card {ℓ r k : ℕ} {G : Finset ℕ}
    (hsub : G ⊆ Finset.range ℓ) (hcard : r + k ≤ G.card) :
    ∃ I : Finset (Fin ℓ), I.card = k ∧ ∀ i ∈ I, r ≤ i.val ∧ i.val ∈ G := by
  let J := (Finset.univ : Finset (Fin ℓ)).filter (fun i => i.val ∈ G)
  have hJ : J.map Fin.valEmbedding = G := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      let j : Fin ℓ := ⟨i, Finset.mem_range.mp (hsub hi)⟩
      exact Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have hJcard : J.card = G.card := by rw [← hJ, Finset.card_map]
  let J₀ := J.filter (fun i => i.val < r)
  let J₁ := J.filter (fun i => r ≤ i.val)
  have hJ₀ : J₀.card ≤ r := by
    rw [← Finset.card_range r, ← Finset.card_map Fin.valEmbedding]
    apply Finset.card_le_card
    rintro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have hs : J₀.card + J₁.card = J.card := by
    simpa only [J₀, J₁, not_lt] using Finset.card_filter_add_card_filter_not (s := J) (fun i => i.val < r)
  obtain ⟨I, hI, hIcard⟩ := Finset.exists_subset_card_eq (show k ≤ J₁.card by omega)
  refine ⟨I, hIcard, fun i hi => ?_⟩
  have h := Finset.mem_filter.mp (hI hi)
  exact ⟨h.2, (Finset.mem_filter.mp h.1).2⟩

/-- Union over all initial points, bit records and prescribed test locations. -/
theorem highSliceAverages_card_le_of_local_average {G : Type*} [AddCommGroup G] [Fintype G]
    {ℓ s r k : ℕ} (hs : s ≤ ℓ) (encode : ℤ → G) (B : Fin ℓ → Finset ℤ)
    (hB : ∀ i, (B i).Nonempty) (f : G → ℝ) (hf : ∀ t, 0 ≤ f t)
    {ε γ τ C : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hr : 2 ≤ ε * (r : ℝ))
    (hlocal : ∀ i : Fin ℓ, r ≤ i.val → ∀ q ≤ i.val,
      (ε / 2) * (i.val : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ (1 - ε / 2) * (i.val : ℝ) →
      ∀ X : Fin ℓ → ℤ, (∀ j, X j ∈ B j) → ∀ (y : G) (b : Bool),
        ∑ x ∈ B i, sliceAverage (sliceCoefficientArray encode X) f i.val q
          (y + if b then -(encode x) else encode x) ≤ C * ((B i).card : ℝ))
    (hpath : ∀ x : Fin ℓ → ℤ, (∀ i, x i ∈ B i) → ∀ (t : G) (w : ℕ → Bool) (p : ℕ → G),
      IsSliceGreedyPath (sliceCoefficientArray encode x) f ℓ s t w p →
      τ ≤ sliceAverage (sliceCoefficientArray encode x) f ℓ s t →
      r + k ≤ (robustHighSiblingSteps w (fun i =>
        slicePathSibling (sliceCoefficientArray encode x) f w i (p i)) ℓ ε γ τ).card) :
    ((highSliceAverages encode B f s τ).card : ℝ) ≤
      (Fintype.card G : ℝ) * (4 : ℝ) ^ ℓ * (C / (γ * τ)) ^ k * ∏ i, ((B i).card : ℝ) := by
  let valid (p : (Fin ℓ → Bool) × Finset (Fin ℓ)) : Prop :=
    ∀ i ∈ p.2, r ≤ i.val ∧ ε ≤ slicePathWeight (extendBitRecord p.1) i.val ∧
      slicePathWeight (extendBitRecord p.1) i.val ≤ 1 - ε
  let locations := (Finset.univ : Finset (Fin ℓ)).powersetCard k
  let records := (Finset.univ : Finset (Fin ℓ → Bool)).product locations
  let choices := (records.filter valid).product (Finset.univ : Finset G)
  let E (p : ((Fin ℓ → Bool) × Finset (Fin ℓ)) × G) : Finset (Fin ℓ → ℤ) :=
    slicePathPattern encode B f (extendBitRecord p.1.1) p.1.2 p.2 (γ * τ)
  have hCover : highSliceAverages encode B f s τ ⊆ choices.biUnion E := by
    intro x hx
    simp only [highSliceAverages, Finset.mem_filter] at hx
    obtain ⟨hbox, t, ht⟩ := hx
    let X := sliceCoefficientArray encode x
    obtain ⟨w, p, hp⟩ := exists_sliceGreedyPath X f ℓ s hs t
    let w₀ : Fin ℓ → Bool := fun i => w i.val
    let w' := extendBitRecord w₀
    have hw' : ∀ i < ℓ, w' i = w i := by intro i hi; simp [w', extendBitRecord, w₀, hi]
    let v (i : ℕ) := slicePathSibling X f w i (p i)
    let good := robustHighSiblingSteps w v ℓ ε γ τ
    have hgood : r + k ≤ good.card := hpath x (Fintype.mem_piFinset.mp hbox) t w p hp ht
    obtain ⟨I, hIcard, hI⟩ := late_robustSteps_card (Finset.filter_subset _ _) hgood
    have hmem (i : Fin ℓ) (hi : i ∈ I) :
        r ≤ i.val ∧ ε ≤ slicePathWeight w i.val ∧ slicePathWeight w i.val ≤ 1 - ε ∧ γ * τ < v i.val :=
      ⟨(hI i hi).1, (Finset.mem_filter.mp (hI i hi).2).2⟩
    have hp₀ : ((w₀, I), p 0) ∈ choices := by
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hIcard⟩⟩, ?_⟩, Finset.mem_univ _⟩
      intro i hi
      have heq : slicePathWeight w' i.val = slicePathWeight w i.val := by
        unfold slicePathWeight
        rw [hw' _ i.isLt, prefixBitCount_congr _ (fun j hj => hw' j (hj.trans_le i.isLt))]
      exact ⟨(hmem i hi).1, heq ▸ (hmem i hi).2.1, heq ▸ (hmem i hi).2.2.1⟩
    refine Finset.mem_biUnion.mpr ⟨((w₀, I), p 0), hp₀, Finset.mem_filter.mpr ⟨hbox, ?_⟩⟩
    intro i hi
    change γ * τ < slicePathSibling X f w' i.val (sliceRecordPoint X w' (p 0) i.val)
    have hpoint : sliceRecordPoint X w' (p 0) i.val = p i.val := by
      rw [hp.point_eq_record i.isLt.le]
      unfold sliceRecordPoint
      congr 1
      exact Finset.sum_congr rfl fun j hj => by rw [hw' j ((Finset.mem_range.mp hj).trans i.isLt)]
    rw [hpoint, slicePathSibling_eq_sliceAverage, hw' _ i.isLt]
    have hcount : sliceSiblingCount w' i.val = sliceSiblingCount w i.val := by
      unfold sliceSiblingCount
      rw [hw' _ i.isLt, prefixBitCount_congr _ (fun j hj => hw' j (hj.trans i.isLt))]
    rw [hcount, ← slicePathSibling_eq_sliceAverage]
    exact (hmem i hi).2.2.2
  have hE (p : ((Fin ℓ → Bool) × Finset (Fin ℓ)) × G) (hp : p ∈ choices) :
      ((E p).card : ℝ) ≤ (C / (γ * τ)) ^ k * ∏ i, ((B i).card : ℝ) := by
    obtain ⟨hp', hvalid⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hp).1
    have hcard := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp').2).2
    let w := extendBitRecord p.1.1
    have he := card_slicePathPattern_le encode B hB f hf w p.1.2 p.2 (mul_pos hγ hτ) hC
      (fun i hi => ?_)
    · simpa only [E, hcard] using he
    obtain ⟨hir, hlow, hhi⟩ := hvalid i hi
    have hir' : (r : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hir
    have hsib := sliceSiblingCount_bounds w i.val hε (hr.trans (mul_le_mul_of_nonneg_left hir' hε.le)) hlow hhi
    exact fun X hX y => hlocal i hir _ hsib.2.2 hsib.1 hsib.2.1 X hX y (w i.val)
  have hchoices : (choices.card : ℝ) ≤ (Fintype.card G : ℝ) * (4 : ℝ) ^ ℓ := by
    have hn : choices.card ≤ Fintype.card G * 4 ^ ℓ := by
      dsimp [choices]
      rw [Finset.card_product, Finset.card_univ]
      have h := (Finset.card_filter_le records valid)
      have hrec : records.card ≤ 4 ^ ℓ := by
        have hh : records.card = 2 ^ ℓ * ℓ.choose k := by simp [records, locations, Finset.card_powersetCard]
        rw [hh, show (4 : ℕ) = 2 * 2 by rfl, mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.choose_le_two_pow ℓ k)
      rw [mul_comm (Fintype.card G)]
      exact Nat.mul_le_mul_right _ (h.trans hrec)
    exact_mod_cast hn
  calc
    _ ≤ (((choices.biUnion E).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_le_card hCover
    _ ≤ ∑ p ∈ choices, ((E p).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ choices, ((C / (γ * τ)) ^ k * ∏ i, ((B i).card : ℝ)) := Finset.sum_le_sum hE
    _ = (choices.card : ℝ) * ((C / (γ * τ)) ^ k * ∏ i, ((B i).card : ℝ)) := by simp
    _ ≤ _ := by rw [mul_assoc]; gcongr

end BooleanThreshold
