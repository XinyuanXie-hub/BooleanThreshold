module

public import BooleanThreshold.JSSConditionalCyclicCount
public import BooleanThreshold.JSSConditionalSplitCount

public noncomputable section

open scoped BigOperators Classical

namespace BooleanThreshold

@[simp]
theorem cyclicIntegerCoordinates_eq_sliceCoefficientArray {n P : ℕ} (x : Fin n → ℤ) :
    cyclicIntegerCoordinates (P := P) x =
      sliceCoefficientArray (fun z : ℤ => (z : ZMod P)) x := rfl

private theorem card_filter_redecide {α : Type*} (s : Finset α) (p : α → Prop)
    {d d' : DecidablePred p} :
    ((@Finset.filter α p d s).card : ℝ) = ((@Finset.filter α p d' s).card : ℝ) := by
  rw [Subsingleton.elim d d']

theorem card_filter_le_redecide {α : Type*} (s : Finset α) (p : α → Prop)
    {d d' : DecidablePred p} {v : ℝ} (h : ((@Finset.filter α p d s).card : ℝ) ≤ v) :
    ((@Finset.filter α p d' s).card : ℝ) ≤ v :=
  (card_filter_redecide s p).le.trans h

set_option maxHeartbeats 1000000 in
/-- Control the full cyclic slice by the prefix preprocessing count, the
suffix smoothing count, and the total weight of the unbalanced suffix sizes. -/
theorem card_largeCyclicSliceBox_le_of_prefix_suffix {n a b P D : ℕ} [NeZero P]
    (h : a + b = n) (W : Fin n → Finset ℤ) (hD : ∀ i, (W i).card ≤ D)
    (g : ZMod P → ℝ) (m : Fin (n + 1))
    {U V T ε β : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hε : 0 ≤ ε)
    (hthreshold : V + U * β < T)
    (good : ℕ → Prop)
    (hweight : (∑ j ∈ Finset.range (m.val + 1),
      if good j then 0 else sliceSplitWeight a b m.val j) ≤ β)
    (hpre : ∀ j ≤ b,
      (((Fintype.piFinset (sliceTuplePrefix h W)).filter fun x =>
        ∃ t : ZMod P, U ≤ sliceAverage (cyclicIntegerCoordinates x) g a (m.val - j) t).card : ℝ) ≤
          ε * (D : ℝ) ^ a)
    (hsuffix : ∀ x ∈ Fintype.piFinset (sliceTuplePrefix h W), ∀ j ≤ b, good j →
      (∀ t : ZMod P, sliceAverage (cyclicIntegerCoordinates x) g a (m.val - j) t ≤ U) →
      (((Fintype.piFinset (sliceTupleSuffix h W)).filter fun y =>
        ∃ t : ZMod P, V ≤ sliceAverage (cyclicIntegerCoordinates y)
          (sliceAverage (cyclicIntegerCoordinates x) g a (m.val - j)) b j t).card : ℝ) ≤
          ε * (D : ℝ) ^ b) :
    ((largeCyclicSliceBox W m g T).card : ℝ) ≤
      (2 * ((b : ℝ) + 1) * ε) * (D : ℝ) ^ n := by
  classical
  let J := Finset.range (b + 1)
  let A := Fintype.piFinset (sliceTuplePrefix h W)
  let B := Fintype.piFinset (sliceTupleSuffix h W)
  let G (j : ℕ) (x : Fin a → ℤ) := sliceAverage (cyclicIntegerCoordinates (P := P) x) g a (m.val - j)
  let E (x : Fin a → ℤ) := ∃ j ∈ J, ∃ t, U ≤ G j x t
  let F (x : Fin a → ℤ) (y : Fin b → ℤ) := ∃ j ∈ J,
    good j ∧ ∃ t, V ≤ sliceAverage (cyclicIntegerCoordinates y) (G j x) b j t
  have hE : ((A.filter E).card : ℝ) ≤ ((b : ℝ) + 1) * ε * (D : ℝ) ^ a := by
    have hc₀ (j : ℕ) (hj : j ∈ J) :
        ((A.filter (fun x => ∃ t, U ≤ G j x t)).card : ℝ) ≤ ε * (D : ℝ) ^ a := by
      simpa only [A, G] using hpre j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hc := card_filter_exists_le_of_each (u := ε * (D : ℝ) ^ a) A J
      (fun j x => ∃ t, U ≤ G j x t)
      (fun j hj => card_filter_le_redecide A (fun x => ∃ t, U ≤ G j x t) (hc₀ j hj))
    refine card_filter_le_redecide A E (d := fun x => Classical.propDecidable (E x)) ?_
    simpa only [E, J, Finset.card_range, Nat.cast_succ, ← mul_assoc] using hc
  have hF (x : Fin a → ℤ) (hx : x ∈ A) (he : ¬ E x) :
      ((B.filter (F x)).card : ℝ) ≤ ((b : ℝ) + 1) * ε * (D : ℝ) ^ b := by
    have hCount (j : ℕ) (hj : j ∈ J) :
        ((B.filter (fun y => good j ∧ ∃ t,
        V ≤ sliceAverage (cyclicIntegerCoordinates y) (G j x) b j t)).card : ℝ) ≤ ε * (D : ℝ) ^ b := by
      by_cases hg : good j
      · simpa only [hg, true_and, B, G] using hsuffix x hx j
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hg
            (fun t => (lt_of_not_ge (fun ht => he ⟨j, hj, t, ht⟩)).le)
      · simp only [hg, false_and, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
        positivity
    have hc := card_filter_exists_le_of_each (u := ε * (D : ℝ) ^ b) B J
      (fun j y => good j ∧ ∃ t, V ≤ sliceAverage (cyclicIntegerCoordinates y) (G j x) b j t)
      (fun j hj => card_filter_le_redecide B
        (fun y => good j ∧ ∃ t, V ≤ sliceAverage (cyclicIntegerCoordinates y) (G j x) b j t)
        (hCount j hj))
    refine card_filter_le_redecide B (F x) (d := fun y => Classical.propDecidable (F x y)) ?_
    simpa only [F, J, Finset.card_range, Nat.cast_succ, ← mul_assoc] using hc
  let u := ((b : ℝ) + 1) * ε
  have hu : 0 ≤ u := by dsimp [u]; positivity
  let Bad (w : Fin n → ℤ) := ∃ t : ZMod P, T ≤ sliceAverage (cyclicIntegerCoordinates w) g n m.val t
  have hcover : ∀ w ∈ Fintype.piFinset W, Bad w →
      E (sliceTuplePrefix h w) ∨ F (sliceTuplePrefix h w) (sliceTupleSuffix h w) := by
    rintro w _ ⟨t, ht⟩
    by_contra! hb
    let x := sliceTuplePrefix h w
    let y := sliceTupleSuffix h w
    let X := cyclicIntegerCoordinates (P := P) w
    have hm : m.val ≤ a + b := (Nat.le_of_lt_succ m.isLt).trans_eq h.symm
    have hG (j : ℕ) (hjb : j ≤ b) (z : ZMod P) : G j x z ≤ U := by
      apply (lt_of_not_ge ?_).le
      intro hz
      exact hb.1 ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjb), z, hz⟩
    have hLp (j : ℕ) (z : ZMod P) : sliceAverage X g a (m.val - j) z = G j x z := by
      simpa only [G, X, x, cyclicIntegerCoordinates_eq_sliceCoefficientArray] using
        sliceAverage_prefix_eq_of_tuple h (fun w : ℤ => (w : ZMod P)) w g (m.val - j) z
    have hLs (j : ℕ) (z : ZMod P) :
        sliceAverage (fun i => X (a + i)) (sliceAverage X g a (m.val - j)) b j z =
          sliceAverage (cyclicIntegerCoordinates y) (G j x) b j z := by
      rw [funext (hLp j)]
      simpa only [X, y, cyclicIntegerCoordinates_eq_sliceCoefficientArray] using
        sliceAverage_suffix_eq_of_tuple h (fun w : ℤ => (w : ZMod P)) w (G j x) j z
    have hmix := sliceAverage_split_le_of_good_weights X g hm hV hU good hweight
      (fun j _ hjb _ z => (hLp j z).trans_le (hG j hjb z))
      (fun j _ hjb _ hg z => (hLs j z).trans_le ((lt_of_not_ge (fun hz =>
        hb.2 ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjb), hg, z, hz⟩)).le)) t
    rw [h] at hmix
    exact (not_le_of_gt (hmix.trans_lt hthreshold)) ht
  change (((Fintype.piFinset W).filter Bad).card : ℝ) ≤ _
  have hb := card_sliceTuple_le_of_bad_split (u := u) (v := u) h W hD Bad E F hu hu
    (card_filter_le_redecide A E hE)
    (fun x hx he => card_filter_le_redecide B (F x) (hF x hx he))
    hcover
  refine (le_trans ?_ hb).trans_eq ?_
  · exact (card_filter_redecide (Fintype.piFinset W) Bad).le
  · dsimp [u]
    ring

end BooleanThreshold
