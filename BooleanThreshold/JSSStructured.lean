module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.JSSConditionalOperatorNorm
public import BooleanThreshold.JSSStructuredAway
public import BooleanThreshold.JSSStructuredAwayRate
public import BooleanThreshold.NonPairSquare

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

private theorem squarePair_of_signedPair_null {n : ℕ} {M : Fin n → Fin n → Bool}
    {i j : Fin n} (hij : i ≠ j) (b d : Bool)
    (hnull : signMatrixMap M (signedBasis b i + signedBasis d j) = 0) :
    M ∈ squarePairEvent n := by
  let v (k : Fin n) : Fin n → ℝ := fun r => realSigns (M r) k
  have hmap (s : Bool) (k : Fin n) : signMatrixMap M (signedBasis s k) =
      (if s then (-1 : ℝ) else 1) • v k := by
    rw [signedBasis, map_smul]
    congr 1
    funext r
    exact signMatrixMap_basis M k r
  rw [map_add, hmap, hmap] at hnull
  have heq : v i = v j ∨ v i = -v j := by
    cases b <;> cases d
    · right
      funext r
      have h := congrFun hnull r
      simp only [Bool.false_eq_true, ite_false, one_smul, Pi.add_apply, Pi.zero_apply] at h
      change v i r = -v j r
      linarith only [h]
    · left
      funext r
      have h := congrFun hnull r
      simp only [Bool.false_eq_true, ite_false, ite_true, one_smul, neg_smul, Pi.add_apply,
        Pi.neg_apply, Pi.zero_apply] at h
      linarith only [h]
    · left
      funext r
      have h := congrFun hnull r
      simp only [Bool.false_eq_true, ite_false, ite_true, one_smul, neg_smul, Pi.add_apply,
        Pi.neg_apply, Pi.zero_apply] at h
      linarith only [h]
    · right
      funext r
      have h := congrFun hnull r
      simp only [ite_true, neg_smul, one_smul, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at h
      change v i r = -v j r
      linarith only [h]
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, heq⟩
  · refine ⟨j, i, h, ?_⟩
    rcases heq with hh | hh
    · exact Or.inl hh.symm
    · exact Or.inr (by change v j = -v i; rw [hh, neg_neg])

private def nearSignedPairEvent (n : ℕ) (K ε : ℝ) : Set (Fin n → Fin n → Bool) :=
  ⋃ t : Fin n × Fin n × Bool × Bool,
    if t.1 ≠ t.2.1 then nonzeroNearSignedPair K ε t.1 t.2.1 t.2.2.1 t.2.2.2 else ∅

private theorem eventually_nearSignedPair_probability (K : ℝ) :
    ∃ ε > (0 : ℝ), ∃ a > (0 : ℝ), a < 1 / 2 ∧ ∃ D > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, (uniformOn Set.univ).real (nearSignedPairEvent n K ε) ≤ D * a ^ n := by
  obtain ⟨ε, hε, c, hc, C, hC, h⟩ := eventually_uniformOn_nonzeroNearColumnDifference K
  obtain ⟨D, hD, hpoly⟩ := polynomial_div_pow_bounded 2
    (Real.one_lt_exp_iff.mpr (show 0 < c / 2 by positivity))
  let a := Real.exp (-(c / 2)) * (1 / 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a < 1 / 2 := by
    apply mul_lt_of_lt_one_left (by norm_num)
    exact Real.exp_lt_one_iff.mpr (by linarith only [hc])
  refine ⟨ε, hε, a, ha, ha', 4 * C * D, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply eventually_atTop.mpr
  refine ⟨N + 2, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  let n := m + 2
  let q := C * Real.exp (-c * (n : ℝ)) * (1 / 2 : ℝ) ^ n
  have hterm (t : Fin n × Fin n × Bool × Bool) :
      (uniformOn Set.univ).real (if t.1 ≠ t.2.1 then
        nonzeroNearSignedPair K ε t.1 t.2.1 t.2.2.1 t.2.2.2 else ∅) ≤ q := by
    split
    · exact (uniformOn_nearSignedPair_le_nearDifference K ε _ _ ‹_› _ _).trans
        (hN m (by omega) _ _ ‹_›)
    · rw [measureReal_empty]
      dsimp [q]
      positivity
  have hsum : (uniformOn Set.univ).real (nearSignedPairEvent n K ε) ≤ 4 * (n : ℝ) ^ 2 * q := by
    calc
      _ ≤ ∑ t : Fin n × Fin n × Bool × Bool, (uniformOn Set.univ).real
          (if t.1 ≠ t.2.1 then nonzeroNearSignedPair K ε t.1 t.2.1 t.2.2.1 t.2.2.2 else ∅) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _t : Fin n × Fin n × Bool × Bool, q := Finset.sum_le_sum fun t _ => hterm t
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hp := (div_le_iff₀ (show 0 < Real.exp (c / 2) ^ n by positivity)).mp (hpoly n)
  refine hsum.trans ?_
  calc
    _ = 4 * C * ((n : ℝ) ^ 2 * (Real.exp (-c * (n : ℝ)) * (1 / 2 : ℝ) ^ n)) := by dsimp [q]; ring
    _ ≤ 4 * C * ((D * Real.exp (c / 2) ^ n) *
        (Real.exp (-c * (n : ℝ)) * (1 / 2 : ℝ) ^ n)) := by gcongr
    _ = 4 * C * D * a ^ n := by
      rw [show Real.exp (-c * (n : ℝ)) = (Real.exp (-c)) ^ n by rw [mul_comm (-c), Real.exp_nat_mul]]
      rw [mul_assoc D, ← mul_pow, ← mul_pow, ← mul_assoc (Real.exp (c / 2)), ← Real.exp_add]
      have heq : c / 2 + -c = -(c / 2) := by ring
      rw [heq]
      unfold a
      ring

private theorem opFailure_probability (K : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hop : ∀ n m : ℕ, 1 ≤ n → m ≤ n →
      (uniformOn Set.univ).real {M : Fin m → Fin n → Bool | ∃ a : Fin n → ℝ,
        K ^ 2 * (n : ℝ) * (∑ i, a i ^ 2) < ∑ j, (∑ i, a i * realSigns (M j) i) ^ 2}
        ≤ Real.exp (-2 * (n : ℝ))) :
    (uniformOn Set.univ).real {M : Fin n → Fin n → Bool | ¬ signOpBound K M} ≤ (1 / 4 : ℝ) ^ n := by
  have h := hop n n hn le_rfl
  simp only [signOpBound, not_forall, not_le, squaredNorm, signMatrixMap_apply]
  refine h.trans ?_
  rw [mul_comm (-2 : ℝ), Real.exp_nat_mul]
  apply pow_le_pow_left₀ (Real.exp_nonneg _)
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have hexp := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
  linarith only [hexp]

/-- The sign-matrix structured null event is bounded by the pair collision
term and an error with a geometric base strictly below one half. -/
theorem almostConstant_null_probability :
    ∃ δ > (0 : ℝ), δ < 1 ∧ ∃ ρ > (0 : ℝ), ρ < 1 ∧
      ∃ a ≥ (1 / 4 : ℝ), a < 1 / 2 ∧ ∃ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        (uniformOn Set.univ).real (structuredNullEvent n (almostConstantUnitVectors n δ ρ)) ≤
          2 * (n.choose 2 : ℝ) / 2 ^ n + D * a ^ n := by
  obtain ⟨K, hK, hop⟩ := signMatrix_norm_tail_exponential 2 (by norm_num)
  obtain ⟨ε₀, hε₀, aP, hPa, hPa', DP, hDP, hnear⟩ := eventually_nearSignedPair_probability K
  let ε := min ε₀ (1 / (2 * (1 + K)))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεsq : ε ^ 2 ≤ ε₀ ^ 2 := pow_le_pow_left₀ hε.le (min_le_left _ _) 2
  have hbudget : K ^ 2 * ε ^ 2 < 1 := by
    have hl : ε * (2 * (1 + K)) ≤ 1 :=
      (le_div_iff₀ (show 0 < 2 * (1 + K) by positivity)).mp (min_le_right ε₀ _)
    have hh : K * ε ≤ (1 / 2 : ℝ) := by nlinarith only [hl, hε]
    rw [← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) hh 2).trans_lt (by norm_num)
  let S (n : ℕ) : Set (Fin n → ℝ) := {a |
    (∀ i b, ε ^ 2 < squaredNorm (signedBasis b i - a)) ∧
    (∀ i j : Fin n, i ≠ j → ∀ b d,
      ε ^ 2 < squaredNorm (signedBasis b i + signedBasis d j - Real.sqrt 2 • a))}
  obtain ⟨θ, hθ, hgap⟩ := exists_signUnit_small_ball_away hε
  obtain ⟨δ, hδ, hδ', ρ, hρ, hρ', DA, hDA, haway⟩ :=
    eventually_uniformOn_awayAlmostConstantNull_le hK.le hθ S
      (fun n a hS ha => hgap n a ha hS.1 hS.2)
  let a := max aP (15 / 32)
  have ha : 1 / 4 ≤ a := (by norm_num : (1 / 4 : ℝ) ≤ 15 / 32).trans (le_max_right _ _)
  have ha' : a < 1 / 2 := max_lt hPa' (by norm_num)
  refine ⟨δ, hδ, hδ', ρ, hρ, hρ', a, ha, ha', 1 + DP + DA, by positivity, ?_⟩
  filter_upwards [hnear, haway, eventually_ge_atTop (1 : ℕ)] with n hP hA hn
  let μ : Measure (Fin n → Fin n → Bool) := uniformOn Set.univ
  let P := squarePairEvent n
  let N := nearSignedPairEvent n K ε₀
  let O : Set (Fin n → Fin n → Bool) := {M | ¬ signOpBound K M}
  let A : Set (Fin n → Fin n → Bool) := {M | signOpBound K M ∧
    ∃ a ∈ S n ∩ almostConstantUnitVectors n δ ρ, signMatrixMap M a = 0}
  have hcover : structuredNullEvent n (almostConstantUnitVectors n δ ρ) ⊆ P ∪ (O ∪ (N ∪ A)) := by
    rintro M ⟨v, hv, hnull⟩
    by_cases hpair : M ∈ P
    · exact Or.inl hpair
    by_cases hOp : signOpBound K M
    · have hvnull : signMatrixMap M v = 0 := by
        funext r
        rw [signMatrixMap_apply, Pi.zero_apply]
        exact hnull r
      have hAxis (i : Fin n) (b : Bool) : ε ^ 2 < squaredNorm (signedBasis b i - v) :=
        lt_of_not_ge (no_near_signedBasis_null_of_opBound (by omega) hOp hbudget i b hvnull)
      by_cases hNear : ∃ i j : Fin n, i ≠ j ∧ ∃ b d,
          squaredNorm (signedBasis b i + signedBasis d j - Real.sqrt 2 • v) ≤ ε ^ 2
      · obtain ⟨i, j, hij, b, d, hclose⟩ := hNear
        have hNon : signMatrixMap M (signedBasis b i + signedBasis d j) ≠ 0 :=
          fun hh => hpair (squarePair_of_signedPair_null hij b d hh)
        have hW : signMatrixMap M (Real.sqrt 2 • v) = 0 := by rw [map_smul, hvnull, smul_zero]
        refine Or.inr (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨(i, j, b, d), ?_⟩)))
        change M ∈ (if i ≠ j then nonzeroNearSignedPair K ε₀ i j b d else ∅)
        rw [ite_eq_left hij]
        exact ⟨hNon, hOp, Real.sqrt 2 • v, hW, hclose.trans hεsq⟩
      · refine Or.inr (Or.inr (Or.inr ⟨hOp, v, ⟨⟨hAxis, ?_⟩, hv⟩, hvnull⟩))
        exact fun i j hij b d => lt_of_not_ge (fun hh => hNear ⟨i, j, hij, b, d, hh⟩)
    · exact Or.inr (Or.inl hOp)
  have hpair : μ.real P ≤ 2 * (n.choose 2 : ℝ) / 2 ^ n := by
    change (uniformOn Set.univ).real (squarePairEvent n) ≤ _
    rw [squarePair_probability]
    exact sub_nonneg.mp (pairCollision_main_sub_probability_le n n le_rfl).1
  have hOp : μ.real O ≤ (1 / 4 : ℝ) ^ n := opFailure_probability K hn hop
  have hNN : μ.real N ≤ DP * aP ^ n := hP
  have hAA : μ.real A ≤ DA * (15 / 32 : ℝ) ^ n := hA
  calc
    _ ≤ μ.real (P ∪ (O ∪ (N ∪ A))) := measureReal_mono hcover
    _ ≤ μ.real P + (μ.real O + (μ.real N + μ.real A)) :=
      (measureReal_union_le P _).trans (add_le_add (le_refl (μ.real P))
        ((measureReal_union_le O _).trans (add_le_add (le_refl (μ.real O)) (measureReal_union_le N A))))
    _ ≤ 2 * (n.choose 2 : ℝ) / 2 ^ n + ((1 / 4 : ℝ) ^ n + (DP * aP ^ n + DA * (15 / 32 : ℝ) ^ n)) :=
      add_le_add hpair (add_le_add hOp (add_le_add hNN hAA))
    _ ≤ 2 * (n.choose 2 : ℝ) / 2 ^ n + (a ^ n + (DP * a ^ n + DA * a ^ n)) := by
      exact add_le_add (le_refl _) (add_le_add (pow_le_pow_left₀ (by norm_num) ha _)
        (add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hPa.le (le_max_left _ _) _) hDP.le)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (le_max_right _ _) _) hDA.le)))
    _ = _ := by ring

end BooleanThreshold
