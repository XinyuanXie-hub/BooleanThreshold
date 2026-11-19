module

public import BooleanThreshold.JSSConditionalSliceAverage
public import BooleanThreshold.JSSConditionalPathWeights

@[expose] public section

open scoped BigOperators

namespace BooleanThreshold

/-- The values of a fixed-weight average along a sequence of recorded branches. -/
noncomputable def slicePathHeight {G : Type*} [AddCommMonoid G] (X : ℕ → G)
    (f : G → ℝ) (w : ℕ → Bool) (p : ℕ → G) (i : ℕ) : ℝ :=
  sliceAverage X f i (prefixBitCount w true i) (p i)

/-- A path that follows a branch of at least the current average at each step. -/
structure IsSliceGreedyPath {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    (n s : ℕ) (t : G) (w : ℕ → Bool) (p : ℕ → G) : Prop where
  weight_eq : prefixBitCount w true n = s
  endpoint_eq : p n = t
  step_eq : ∀ i < n, p i = p (i + 1) + if w i then X i else 0
  height_le : ∀ i < n, slicePathHeight X f w p (i + 1) ≤ slicePathHeight X f w p i

theorem prefixBitCount_congr {u v : ℕ → Bool} (b : Bool) {j : ℕ}
    (h : ∀ i < j, u i = v i) : prefixBitCount u b j = prefixBitCount v b j := by
  unfold prefixBitCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun hi => by rw [h i hi])

private theorem IsSliceGreedyPath.extend {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    {n s : ℕ} (t : G) (b : Bool) {w : ℕ → Bool} {p : ℕ → G}
    (h : IsSliceGreedyPath X f n s (t + if b then X n else 0) w p)
    (hc : sliceAverage X f (n + 1) (s + if b then 1 else 0) t ≤
      sliceAverage X f n s (t + if b then X n else 0)) :
    ∃ w' p', IsSliceGreedyPath X f (n + 1) (s + if b then 1 else 0) t w' p' := by
  let w' i := if i = n then b else w i
  let p' i := if i = n + 1 then t else p i
  have hcount (j : ℕ) (hj : j ≤ n) : prefixBitCount w' true j = prefixBitCount w true j := by
    apply prefixBitCount_congr
    intro i hi
    simp [w', show i ≠ n by omega]
  have hpoint (j : ℕ) (hj : j ≤ n) : p' j = p j := by simp [p', show j ≠ n + 1 by omega]
  have hheight (j : ℕ) (hj : j ≤ n) : slicePathHeight X f w' p' j = slicePathHeight X f w p j := by
    unfold slicePathHeight
    rw [hcount _ hj, hpoint _ hj]
  have hcount' : prefixBitCount w' true (n + 1) = s + if b then 1 else 0 := by
    rw [prefixBitCount_succ, hcount n le_rfl, h.weight_eq]
    cases b <;> simp [w']
  have hpoint' : p' (n + 1) = t := by simp [p']
  refine ⟨w', p', ⟨hcount', hpoint', fun i hi => ?_, fun i hi => ?_⟩⟩
  · by_cases hin : i < n
    · rw [hpoint _ hin.le, hpoint _ (by omega), show w' i = w i by simp [w', show i ≠ n by omega]]
      exact h.step_eq i hin
    · have heq : i = n := by omega
      subst i
      rw [hpoint _ le_rfl, hpoint', show w' n = b by simp [w']]
      exact h.endpoint_eq
  · by_cases hin : i < n
    · rw [hheight _ (by omega), hheight _ hin.le]
      exact h.height_le i hin
    · have heq : i = n := by omega
      subst i
      rw [hheight _ le_rfl]
      unfold slicePathHeight
      rw [hcount', hpoint', h.weight_eq, h.endpoint_eq]
      exact hc

/-- A greedy path exists for each fixed-weight averaging endpoint. -/
theorem exists_sliceGreedyPath {G : Type*} [AddCommMonoid G] (X : ℕ → G) (f : G → ℝ)
    (n s : ℕ) (hs : s ≤ n) (t : G) : ∃ w p, IsSliceGreedyPath X f n s t w p := by
  induction n generalizing s t with
  | zero =>
    have heq : s = 0 := by omega
    subst s
    exact ⟨fun _ => false, fun _ => t, ⟨by simp [prefixBitCount], rfl, by simp, by simp⟩⟩
  | succ n ih =>
    cases s with
    | zero =>
      refine ⟨fun _ => false, fun _ => t, ⟨by simp [prefixBitCount], rfl, by simp, ?_⟩⟩
      simp [slicePathHeight, prefixBitCount]
    | succ s =>
      have hsn : s ≤ n := Nat.le_of_succ_le_succ hs
      let h := sliceAverage X f (n + 1) (s + 1) t
      let A := sliceAverage X f n (s + 1) t
      let B := sliceAverage X f n s (t + X n)
      let q := ((s : ℝ) + 1) / ((n : ℝ) + 1)
      have hq : 0 < q := by dsimp [q]; positivity
      have hq₁ : q ≤ 1 := by
        apply (div_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
        exact_mod_cast hs
      have hrec : h = (1 - q) * A + q * B := by
        simpa only [Nat.cast_add, Nat.cast_one] using sliceAverage_succ X f hsn t
      by_cases hA : s + 1 ≤ n ∧ h ≤ A
      · obtain ⟨w, p, hp⟩ := ih (s + 1) hA.1 t
        have hp' : IsSliceGreedyPath X f n (s + 1) (t + if false then X n else 0) w p := by simpa using hp
        simpa using hp'.extend X f t false (show sliceAverage X f (n + 1) ((s + 1) + if false then 1 else 0) t ≤
          sliceAverage X f n (s + 1) (t + if false then X n else 0) by simpa using hA.2)
      have hB : h ≤ B := by
        by_cases hS : s + 1 ≤ n
        · have hA' : A ≤ h := (lt_of_not_ge (fun hh => hA ⟨hS, hh⟩)).le
          apply le_of_not_gt
          intro hB'
          have h₁ := mul_le_mul_of_nonneg_left hA' (sub_nonneg.mpr hq₁)
          have h₂ := mul_lt_mul_of_pos_left hB' hq
          nlinarith only [hrec, h₁, h₂]
        · have hs₀ : s = n := by omega
          have hq' : q = 1 := by dsimp [q]; rw [hs₀, div_self (by positivity)]
          simpa only [hq', sub_self, zero_mul, one_mul, zero_add] using hrec.le
      obtain ⟨w, p, hp⟩ := ih s hsn (t + X n)
      exact hp.extend X f t true hB

/-- The other branch when a path is extended one step backwards. -/
noncomputable def slicePathSibling {G : Type*} [AddCommGroup G] (X : ℕ → G) (f : G → ℝ)
    (w : ℕ → Bool) (i : ℕ) (p : G) : ℝ :=
  if w i then sliceAverage X f i (prefixBitCount w true i + 1) (p - X i)
  else sliceAverage X f i (prefixBitCount w true i - 1) (p + X i)

theorem slicePathHeight_step {G : Type*} [AddCommGroup G] (X : ℕ → G) (f : G → ℝ)
    (w : ℕ → Bool) (p : ℕ → G) (i : ℕ)
    (h : p i = p (i + 1) + if w i then X i else 0) :
    slicePathHeight X f w p (i + 1) =
      slicePathWeight w i * slicePathHeight X f w p i +
        (1 - slicePathWeight w i) * slicePathSibling X f w i (p i) := by
  let a := prefixBitCount w true i
  have ha : a ≤ i := prefixBitCount_le w true i
  have hplus : prefixBitCount w false (i + 1) + prefixBitCount w true (i + 1) = i + 1 :=
    prefixBitCount_add w (i + 1)
  unfold slicePathHeight slicePathWeight slicePathSibling
  rw [prefixBitCount_succ w true]
  cases hw : w i
  · have hp : p i = p (i + 1) := by simpa only [hw, Bool.false_eq_true, ↓reduceIte, add_zero] using h
    have hcount : prefixBitCount w false (i + 1) = i + 1 - a := by
      rw [prefixBitCount_succ w true] at hplus
      simp only [hw, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplus
      dsimp [a]
      omega
    have hrat : (prefixBitCount w false (i + 1) : ℝ) / ((i : ℝ) + 1) =
        1 - (a : ℝ) / ((i : ℝ) + 1) := by
      rw [hcount, Nat.cast_sub (by omega : a ≤ i + 1), Nat.cast_add, Nat.cast_one]
      field_simp
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hp]
    rw [hrat]
    change sliceAverage X f (i + 1) a (p (i + 1)) =
      (1 - (a : ℝ) / ((i : ℝ) + 1)) * sliceAverage X f i a (p (i + 1)) +
        (1 - (1 - (a : ℝ) / ((i : ℝ) + 1))) * sliceAverage X f i (a - 1) (p (i + 1) + X i)
    rcases a with _ | j
    · simp
    · rw [sliceAverage_succ X f (by omega : j ≤ i), Nat.add_sub_cancel]
      push_cast
      ring
  · have hp : p i = p (i + 1) + X i := by simpa [hw] using h
    simp only [↓reduceIte, prefixBitCount_succ w true, hw, Nat.cast_add, Nat.cast_one,
      hp, add_sub_cancel_right]
    rw [sliceAverage_succ X f ha]
    push_cast
    ring

end BooleanThreshold
