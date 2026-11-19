module

public import BooleanThreshold.JSSConditionalLittlewoodOfford

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

private theorem card_signSum_smallBall_large {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) {θ : ℝ} (ha : ∀ i, θ < |a i|) (t : ℝ) :
    Nat.card {x : ι → Bool // |signSum a x - t| ≤ θ} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  let S : Set (ι → Bool) := {x | |signSum a x - t| ≤ θ}
  have h := signSum_smallBall_le_middle_binomial a t θ ha
  change (uniformOn Set.univ).real S ≤ _ at h
  rw [uniformOn_univ_real_eq_card, ← Nat.card_coe_set_eq, Fintype.card_fun, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat] at h
  have h' := (div_le_div_iff_of_pos_right (show 0 < (2 : ℝ) ^ Fintype.card ι by positivity)).mp h
  exact_mod_cast h'

set_option maxHeartbeats 500000 in
/-- Littlewood–Offord's interval bound using only coefficients whose
magnitudes exceed the interval radius. -/
theorem uniformOn_signSum_smallBall_le_choose {n : ℕ} (a : Fin n → ℝ) (I : Finset (Fin n))
    {θ : ℝ} (hI : ∀ i ∈ I, θ < |a i|) (t : ℝ) :
    uniformOn Set.univ {x : Fin n → Bool | |signSum a x - t| ≤ θ} ≤
      (I.card.choose (I.card / 2) : ℝ≥0∞) / 2 ^ I.card := by
  classical
  let p := fun i : Fin n => i ∈ I
  let : Fintype (Subtype p) := Subtype.fintype p
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bool)
  let s (y : Subtype (fun i => ¬ p i) → Bool) : ℝ :=
    t - signSum (fun i : Subtype (fun i => ¬ p i) => a i.val) y
  let S : Set (Fin n → Bool) := {x | |signSum a x - t| ≤ θ}
  let U (y : Subtype (fun i => ¬ p i) → Bool) : Set (Subtype p → Bool) :=
    {x | |signSum (fun i : Subtype p => a i.val) x - s y| ≤ θ}
  have he (x) : x ∈ S ↔ (e x).1 ∈ U (e x).2 := by
    have hsum : signSum a x =
        signSum (fun i : Subtype p => a i.val) (e x).1 +
        signSum (fun i : Subtype (fun i => ¬ p i) => a i.val) (e x).2 := by
      simpa only [signSum, e, Equiv.piEquivPiSubtypeProd_apply] using
        (Fintype.sum_subtype_add_sum_subtype p (fun i => a i * (if x i then 1 else -1))).symm
    change (|signSum a x - t| ≤ θ) ↔
      (|signSum (fun i : Subtype p => a i.val) (e x).1 - s (e x).2| ≤ θ)
    rw [hsum]
    dsimp only [s]
    ring_nf
  let fe : S ≃ {xy : (Subtype p → Bool) × (Subtype (fun i => ¬ p i) → Bool) //
      xy.1 ∈ U xy.2} := Equiv.subtypeEquiv e he
  let pe : {xy : (Subtype p → Bool) × (Subtype (fun i => ¬ p i) → Bool) //
      xy.1 ∈ U xy.2} ≃ (y : Subtype (fun i => ¬ p i) → Bool) × U y :=
    { toFun := fun xy => ⟨xy.val.2, ⟨xy.val.1, xy.prop⟩⟩
      invFun := fun y => ⟨(y.2.val, y.1), y.2.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcardp : Fintype.card (Subtype p) = I.card := by
    rw [Fintype.card_subtype]
    simp
  have hcardq : Fintype.card (Subtype (fun i => ¬ p i)) = n - I.card := by
    rw [Fintype.card_subtype_compl, hcardp, Fintype.card_fin]
  let B := I.card.choose (I.card / 2)
  have hfiber (y : Subtype (fun i => ¬ p i) → Bool) : Nat.card (U y) ≤ B := by
    simpa only [hcardp, U, B, Set.coe_ofPred] using
      card_signSum_smallBall_large (fun i : Subtype p => a i.val)
        (fun i => hI i.val i.prop) (s y)
  have hcard : Nat.card S ≤ B * 2 ^ (n - I.card) := by
    change Nat.card {x // x ∈ S} ≤ _
    rw [Nat.card_congr (fe.trans pe), Nat.card_eq_fintype_card, Fintype.card_sigma]
    calc
      _ ≤ ∑ _y : Subtype (fun i => ¬ p i) → Bool, B :=
        Finset.sum_le_sum fun y _ => (Nat.card_eq_fintype_card (α := U y)) ▸ hfiber y
      _ = _ := by simp [hcardq, mul_comm]
  have hle : I.card ≤ n := by simpa using Finset.card_le_univ I
  have hsplit : 2 ^ n = (2 : ℝ≥0∞) ^ I.card * 2 ^ (n - I.card) :=
    (congrArg (fun e => (2 : ℝ≥0∞) ^ e) (Nat.add_sub_of_le hle).symm).trans (pow_add _ _ _)
  change uniformOn Set.univ S ≤ _
  rw [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite S),
    ← Set.ncard_eq_toFinset_card, Fintype.card_pi_const, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, hsplit]
  calc
    _ ≤ (B * 2 ^ (n - I.card) : ℕ) / ((2 : ℝ≥0∞) ^ I.card * 2 ^ (n - I.card)) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast hcard
    _ = _ := by
      push_cast
      rw [ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

open scoped Classical in
/-- Three coefficients larger than the interval radius bound its mass by
`3/8`, regardless of the other coefficients. -/
theorem uniformOn_signSum_smallBall_le_three_eighths {n : ℕ} (a : Fin n → ℝ)
    {θ : ℝ}
    (ha : 3 ≤ (Finset.univ.filter fun i => θ < |a i|).card) (t : ℝ) :
    uniformOn Set.univ {x : Fin n → Bool | |signSum a x - t| ≤ θ} ≤ 3 / 8 := by
  obtain ⟨I, hsub, hI⟩ := Finset.exists_subset_card_eq ha
  have h := uniformOn_signSum_smallBall_le_choose a I
    (fun i hi => (Finset.mem_filter.mp (hsub hi)).2) t
  rw [hI, show (2 : ℝ≥0∞) ^ 3 = 8 by norm_num] at h
  simpa using h

end BooleanThreshold
