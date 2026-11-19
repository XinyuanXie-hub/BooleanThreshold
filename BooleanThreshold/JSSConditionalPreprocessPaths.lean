module

public import BooleanThreshold.JSSConditionalGreedyPath
public import BooleanThreshold.JSSConditionalAdaptive

@[expose] public section

open scoped BigOperators Classical

namespace BooleanThreshold

/-- Extend a finite integer coefficient vector by zero in an additive group. -/
def sliceCoefficientArray {G : Type*} [Zero G] {ℓ : ℕ} (encode : ℤ → G)
    (X : Fin ℓ → ℤ) (i : ℕ) : G :=
  if h : i < ℓ then encode (X ⟨i, h⟩) else 0

@[simp] theorem sliceCoefficientArray_apply {G : Type*} [Zero G] {ℓ : ℕ} (encode : ℤ → G)
    (X : Fin ℓ → ℤ) (i : Fin ℓ) : sliceCoefficientArray encode X i.val = encode (X i) := by
  simp [sliceCoefficientArray, i.isLt]

theorem sliceAverage_eq_of_prefix {G : Type*} [AddCommMonoid G] (X Y : ℕ → G) (f : G → ℝ)
    (i s : ℕ) (t : G) (h : ∀ j < i, X j = Y j) : sliceAverage X f i s t = sliceAverage Y f i s t := by
  unfold sliceAverage
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  congr 2
  exact Finset.sum_congr rfl fun j hj => h j (Finset.mem_range.mp ((Finset.mem_powersetCard.mp hJ).1 hj))

/-- The weight count of the alternate branch at the indicated step. -/
def sliceSiblingCount (w : ℕ → Bool) (i : ℕ) : ℕ :=
  if w i then prefixBitCount w true i + 1 else prefixBitCount w true i - 1

theorem slicePathSibling_eq_sliceAverage {G : Type*} [AddCommGroup G] (X : ℕ → G)
    (f : G → ℝ) (w : ℕ → Bool) (i : ℕ) (t : G) :
    slicePathSibling X f w i t = sliceAverage X f i (sliceSiblingCount w i)
      (t + if w i then -X i else X i) := by
  cases h : w i <;> simp [slicePathSibling, sliceSiblingCount, h, sub_eq_add_neg]

/-- A robust step has an alternate branch whose proportion of each bit is
bounded below, once the prefix is long enough. -/
theorem sliceSiblingCount_bounds (w : ℕ → Bool) (i : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hi : 2 ≤ ε * (i : ℝ))
    (hl : ε ≤ slicePathWeight w i) (hu : slicePathWeight w i ≤ 1 - ε) :
    (ε / 2) * (i : ℝ) ≤ (sliceSiblingCount w i : ℝ) ∧
      (sliceSiblingCount w i : ℝ) ≤ (1 - ε / 2) * (i : ℝ) ∧ sliceSiblingCount w i ≤ i := by
  let s := prefixBitCount w true (i + 1)
  let j := sliceSiblingCount w i
  have hsum : (prefixBitCount w false (i + 1) : ℝ) + (s : ℝ) = (i : ℝ) + 1 := by
    exact_mod_cast prefixBitCount_add w (i + 1)
  have hpos : 0 < (i : ℝ) + 1 := by positivity
  have hcount₀ := (le_div_iff₀ hpos).mp hl
  have hcount₁ := (div_le_iff₀ hpos).mp hu
  have hs : ε * ((i : ℝ) + 1) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (1 - ε) * ((i : ℝ) + 1) := by
    cases hwi : w i
    · rw [hwi] at hcount₀ hcount₁
      constructor <;> nlinarith only [hsum, hcount₀, hcount₁]
    · rw [hwi] at hcount₀ hcount₁
      exact ⟨hcount₀, hcount₁⟩
  have hsj : j ≤ s ∧ s ≤ j + 1 := by
    dsimp [j, s, sliceSiblingCount]
    rw [prefixBitCount_succ w true i]
    cases w i
    all_goals simp
    all_goals omega
  have hsj₀ : (j : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsj.1
  have hsj₁ : (s : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hsj.2
  have hj₀ : (ε / 2) * (i : ℝ) ≤ (j : ℝ) := by nlinarith only [hs.1, hsj₁, hi, hε]
  have hj₁ : (j : ℝ) ≤ (1 - ε / 2) * (i : ℝ) := by nlinarith only [hs.2, hsj₀, hi, hε]
  have hj₂ : (j : ℝ) ≤ (i : ℝ) := hj₁.trans (by nlinarith only [hi])
  exact ⟨hj₀, hj₁, by change j ≤ i; exact_mod_cast hj₂⟩

/-- The point reached by following a fixed record forward from its start. -/
def sliceRecordPoint {G : Type*} [AddCommGroup G] (X : ℕ → G) (w : ℕ → Bool)
    (t : G) (i : ℕ) : G := t - ∑ j ∈ Finset.range i, if w j then X j else 0

theorem sliceRecordPoint_succ {G : Type*} [AddCommGroup G] (X : ℕ → G) (w : ℕ → Bool)
    (t : G) (i : ℕ) : sliceRecordPoint X w t (i + 1) = sliceRecordPoint X w t i - if w i then X i else 0 := by
  simp only [sliceRecordPoint, Finset.sum_range_succ, sub_add_eq_sub_sub]

theorem IsSliceGreedyPath.point_eq_record {G : Type*} [AddCommGroup G]
    {X : ℕ → G} {f : G → ℝ} {n s : ℕ} {t : G} {w : ℕ → Bool} {p : ℕ → G}
    (h : IsSliceGreedyPath X f n s t w p) {i : ℕ} (hi : i ≤ n) :
    p i = sliceRecordPoint X w (p 0) i := by
  induction i with
  | zero => simp [sliceRecordPoint]
  | succ i ih =>
    rw [sliceRecordPoint_succ, ← ih (Nat.le_of_succ_le hi)]
    rw [h.step_eq i (by omega), add_sub_cancel_right]

private theorem acceptsAdaptivePath_of_trace {State Input : Type*} {ℓ : ℕ}
    (step : Fin ℓ → State → Input → State) (test : Fin ℓ → State → Input → Prop)
    (S : Fin (ℓ + 1) → State) (x : Fin ℓ → Input)
    (hstep : ∀ i, S i.succ = step i (S i.castSucc) (x i))
    (htest : ∀ i, test i (S i.castSucc) (x i)) :
    acceptsAdaptivePath step test (S 0) x := by
  induction ℓ with
  | zero => exact trivial
  | succ ℓ ih =>
    refine ⟨htest 0, ?_⟩
    have h := ih (Fin.tail step) (Fin.tail test) (Fin.tail S) (Fin.tail x)
      (fun i => hstep i.succ) (fun i => htest i.succ)
    change acceptsAdaptivePath (Fin.tail step) (Fin.tail test) (S (0 : Fin (ℓ + 1)).succ) (Fin.tail x) at h
    rw [hstep 0] at h
    exact h

/-- The tuples that pass the alternate-branch tests of a given record. -/
noncomputable def slicePathPattern {G : Type*} [AddCommGroup G] {ℓ : ℕ}
    (encode : ℤ → G) (B : Fin ℓ → Finset ℤ) (f : G → ℝ) (w : ℕ → Bool)
    (I : Finset (Fin ℓ)) (t : G) (a : ℝ) : Finset (Fin ℓ → ℤ) :=
  (Fintype.piFinset B).filter fun x => ∀ i ∈ I,
    a < slicePathSibling (sliceCoefficientArray encode x) f w i.val
      (sliceRecordPoint (sliceCoefficientArray encode x) w t i.val)

/-- Along a fixed record, local bounds on slice averages control the count
of coefficient tuples that pass the prescribed alternate-branch tests. -/
theorem card_slicePathPattern_le {G : Type*} [AddCommGroup G] {ℓ : ℕ}
    (encode : ℤ → G) (B : Fin ℓ → Finset ℤ) (hB : ∀ i, (B i).Nonempty)
    (f : G → ℝ) (hf : ∀ t, 0 ≤ f t) (w : ℕ → Bool) (I : Finset (Fin ℓ)) (t : G)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hlocal : ∀ i ∈ I, ∀ X : Fin ℓ → ℤ, (∀ j, X j ∈ B j) → ∀ y : G,
      ∑ q ∈ B i, sliceAverage (sliceCoefficientArray encode X) f i.val (sliceSiblingCount w i.val)
        (y + if w i.val then -(encode q) else encode q) ≤ C * ((B i).card : ℝ)) :
    ((slicePathPattern encode B f w I t a).card : ℝ) ≤ (C / a) ^ I.card * ∏ i, ((B i).card : ℝ) := by
  choose X₀ hX₀ using hB
  let State := (Fin ℓ → ℤ) × G
  let U (S : State) : Prop := ∀ j, S.1 j ∈ B j
  let step (i : Fin ℓ) (S : State) (q : ℤ) : State :=
    (Function.update S.1 i (if q ∈ B i then q else S.1 i), S.2 - if w i.val then encode q else 0)
  let F (i : Fin ℓ) (S : State) (q : ℤ) : ℝ :=
    sliceAverage (sliceCoefficientArray encode S.1) f i.val (sliceSiblingCount w i.val)
      (S.2 + if w i.val then -(encode q) else encode q)
  let test (i : Fin ℓ) (S : State) (q : ℤ) : Prop := i ∉ I ∨ a < F i S q
  let d (i : Fin ℓ) : ℕ := if i ∈ I then ⌊(C / a) * ((B i).card : ℝ)⌋₊ else (B i).card
  have hU (i : Fin ℓ) (S : State) (q : ℤ) (hS : U S) : U (step i S q) := by
    intro j
    change Function.update S.1 i (if q ∈ B i then q else S.1 i) j ∈ B j
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      split
      · assumption
      · exact hS i
    · rw [Function.update_of_ne hji]
      exact hS j
  have hF (i : Fin ℓ) (S : State) (q : ℤ) : 0 ≤ F i S q := sliceAverage_nonneg _ _ hf _ _ _
  have htest (i : Fin ℓ) (S : State) (hS : U S) :
      (@Finset.filter ℤ (test i S) (fun q => Classical.propDecidable (test i S q)) (B i)).card ≤ d i := by
    by_cases hi : i ∈ I
    · have he : (@Finset.filter ℤ (test i S) (fun q => Classical.propDecidable (test i S q)) (B i)) =
          (B i).filter (fun q => a < F i S q) := by ext q; simp [test, hi]
      have hdI : d i = ⌊(C / a) * ((B i).card : ℝ)⌋₊ := by simp [d, hi]
      rw [hdI, he]
      apply (Nat.le_floor_iff (by positivity)).mpr
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      calc
        _ = ∑ _q ∈ (B i).filter (fun q => a < F i S q), a := by simp [nsmul_eq_mul]
        _ ≤ ∑ q ∈ (B i).filter (fun q => a < F i S q), F i S q :=
          Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp hq).2.le
        _ ≤ ∑ q ∈ B i, F i S q := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun q _ _ => hF i S q)
        _ ≤ _ := hlocal i hi S.1 hS S.2
    · simp only [d, hi, ↓reduceIte]
      exact Finset.card_le_card (@Finset.filter_subset ℤ (test i S)
        (fun q => Classical.propDecidable (test i S q)) (B i))
  let S₀ : State := (X₀, t)
  have hIncl : slicePathPattern encode B f w I t a ⊆
      (Fintype.piFinset B).filter (acceptsAdaptivePath step test S₀) := by
    intro x hx
    obtain ⟨hxb, hpath⟩ := Finset.mem_filter.mp hx
    let Y := sliceCoefficientArray encode x
    let trace (i : Fin (ℓ + 1)) : State :=
      ((fun j => if j.val < i.val then x j else X₀ j), sliceRecordPoint Y w t i.val)
    have ht₀ : trace 0 = S₀ := by simp [trace, S₀, sliceRecordPoint]
    have htstep (i : Fin ℓ) : trace i.succ = step i (trace i.castSucc) (x i) := by
      apply Prod.ext
      · funext j
        have hxi := Fintype.mem_piFinset.mp hxb i
        change (if j.val < i.val + 1 then x j else X₀ j) =
          Function.update (fun j => if j.val < i.val then x j else X₀ j) i
            (if x i ∈ B i then x i else _) j
        simp only [hxi, ↓reduceIte]
        by_cases hji : j = i
        · subst j
          simp
        · have hjv : j.val ≠ i.val := fun he => hji (Fin.ext he)
          simp [Function.update_of_ne hji, show j.val < i.val + 1 ↔ j.val < i.val by omega]
      · change sliceRecordPoint Y w t (i.val + 1) =
          sliceRecordPoint Y w t i.val - if w i.val then encode (x i) else 0
        rw [sliceRecordPoint_succ, show Y i.val = encode (x i) from sliceCoefficientArray_apply _ _ _]
    have htest' (i : Fin ℓ) : test i (trace i.castSucc) (x i) := by
      by_cases hi : i ∈ I
      · refine Or.inr ?_
        have ht := hpath i hi
        rw [slicePathSibling_eq_sliceAverage, sliceCoefficientArray_apply] at ht
        change a < sliceAverage (sliceCoefficientArray encode (trace i.castSucc).1) f i.val
          (sliceSiblingCount w i.val) (sliceRecordPoint Y w t i.val + if w i.val then -(encode (x i)) else encode (x i))
        refine ht.trans_le (?_ : _ ≤ _)
        apply le_of_eq
        apply sliceAverage_eq_of_prefix
        intro j hj
        have hj' : j < ℓ := hj.trans i.isLt
        simp [sliceCoefficientArray, trace, hj', hj]
      · exact Or.inl hi
    refine Finset.mem_filter.mpr ⟨hxb, ?_⟩
    rw [← ht₀]
    exact acceptsAdaptivePath_of_trace step test trace x htstep htest'
  have hcard := (Finset.card_le_card hIncl).trans
    (card_acceptsAdaptivePath_le step test U hU B d htest S₀ hX₀)
  have hdf (i : Fin ℓ) : (d i : ℝ) ≤ (if i ∈ I then C / a else 1) * ((B i).card : ℝ) := by
    by_cases hi : i ∈ I
    · simpa only [d, hi, ↓reduceIte] using (Nat.floor_le (show 0 ≤ C / a * ((B i).card : ℝ) by positivity))
    · simp [d, hi]
  calc
    _ ≤ ∏ i, (d i : ℝ) := by exact_mod_cast hcard
    _ ≤ ∏ i : Fin ℓ, (if i ∈ I then C / a else 1) * ((B i).card : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hdf i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        Finset.filter_mem_eq_inter, Finset.univ_inter]

end BooleanThreshold
