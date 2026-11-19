module

public import BooleanThreshold.JSSConditionalNet
public import BooleanThreshold.JSSConditionalTail
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

open scoped BigOperators NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory WithLp

namespace BooleanThreshold

private theorem opNorm_le_of_unit_pairings {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : E →L[ℝ] F) (X : Finset E) (Y : Finset F)
    (hXnorm : ∀ x ∈ X, ‖x‖ = 1)
    (hXnet : ∀ x, ‖x‖ = 1 → ∃ p ∈ X, ‖x - p‖ ≤ 1 / 4)
    (hYnet : ∀ y, ‖y‖ = 1 → ∃ q ∈ Y, ‖y - q‖ ≤ 1 / 4)
    {u : ℝ} (hu : 0 ≤ u)
    (hxy : ∀ p ∈ X, ∀ q ∈ Y, |⟪L p, q⟫| ≤ u) :
    ‖L‖ ≤ 2 * u := by
  have hunit (x : E) (hx : ‖x‖ = 1) (y : F) (hy : ‖y‖ = 1) :
      |⟪L x, y⟫| ≤ u + ‖L‖ / 2 := by
    obtain ⟨p, hp, hxp⟩ := hXnet x hx
    obtain ⟨q, hq, hyq⟩ := hYnet y hy
    have hn : ‖L (x - p)‖ ≤ ‖L‖ / 4 := by
      calc
        _ ≤ ‖L‖ * ‖x - p‖ := L.le_opNorm _
        _ ≤ ‖L‖ * (1 / 4) := mul_le_mul_of_nonneg_left hxp (norm_nonneg _)
        _ = _ := by ring
    have hn' : ‖L p‖ ≤ ‖L‖ := by simpa [hXnorm p hp] using L.le_opNorm p
    have h₁ : |⟪L (x - p), y⟫| ≤ ‖L‖ / 4 := by
      simpa [hy] using (abs_real_inner_le_norm (L (x - p)) y).trans (by simpa [hy] using hn)
    have h₂ : |⟪L p, y - q⟫| ≤ ‖L‖ / 4 := by
      calc
        _ ≤ ‖L p‖ * ‖y - q‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖L‖ * (1 / 4) := mul_le_mul hn' hyq (norm_nonneg _) (norm_nonneg _)
        _ = _ := by ring
    have heq : ⟪L x, y⟫ = ⟪L p, q⟫ + ⟪L (x - p), y⟫ + ⟪L p, y - q⟫ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    rw [heq]
    calc
      _ ≤ (|⟪L p, q⟫| + |⟪L (x - p), y⟫|) + |⟪L p, y - q⟫| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith only [hxy p hp q hq, h₁, h₂]
  have hnunit (x : E) (hx : ‖x‖ = 1) : ‖L x‖ ≤ u + ‖L‖ / 2 := by
    by_cases hzero : L x = 0
    · simp only [hzero, norm_zero]
      positivity
    have hn := norm_pos_iff.mpr hzero
    let y : F := ‖L x‖⁻¹ • L x
    have hy : ‖y‖ = 1 := by simp [y, norm_smul, hn.ne']
    have heq : ⟪L x, y⟫ = ‖L x‖ := by
      rw [show y = ‖L x‖⁻¹ • L x by rfl, real_inner_smul_right,
        real_inner_self_eq_norm_sq, pow_two, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    simpa only [heq, abs_of_nonneg (norm_nonneg _)] using hunit x hx y hy
  have hbound : ‖L‖ ≤ u + ‖L‖ / 2 := by
    apply L.opNorm_le_bound' (by positivity)
    intro x hx
    let y : E := ‖x‖⁻¹ • x
    have hy : ‖y‖ = 1 := by simp [y, norm_smul, hx]
    have heq : x = ‖x‖ • y := by rw [show y = ‖x‖⁻¹ • x by rfl, smul_smul, mul_inv_cancel₀ hx, one_smul]
    calc
      ‖L x‖ = ‖x‖ * ‖L y‖ := by
        conv_lhs => rw [heq]
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ (u + ‖L‖ / 2) * ‖x‖ := by
        rw [mul_comm (u + ‖L‖ / 2)]
        exact mul_le_mul_of_nonneg_left (hnunit y hy) (norm_nonneg _)
  linarith only [hbound]

private noncomputable def signMatrixLinear {m n : ℕ} (A : Fin m → Fin n → Bool) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap).comp
    ((Matrix.of (fun i => realSigns (A i))).mulVecLin.comp
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap)).toContinuousLinearMap

private theorem signMatrixLinear_apply {m n : ℕ} (A : Fin m → Fin n → Bool)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    signMatrixLinear A x i = ∑ j, x j * realSigns (A i) j := by
  change (∑ j, realSigns (A i) j * x j) = _
  simp only [mul_comm]

private theorem signMatrix_pairing_tail_le {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (uniformOn Set.univ).real {A : Fin m → Fin n → Bool |
      u ≤ |⟪signMatrixLinear A x, y⟫|} ≤ 2 * Real.exp (-u ^ 2 / 2) := by
  let a (ij : Fin m × Fin n) := y ij.1 * x ij.2
  have ha : ∑ ij, a ij ^ 2 = 1 := by
    simp only [a, Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum]
    rw [← EuclideanSpace.real_norm_sq_eq, hx, one_pow]
    simp only [mul_one]
    rw [← EuclideanSpace.real_norm_sq_eq, hy, one_pow]
  let e := (Equiv.curry (Fin m) (Fin n) Bool).symm
  have hp := signSum_abs_tail_le a ha hu
  let test : Set (Fin m × Fin n → Bool) := {b | u ≤ |signSum a b|}
  have hmap :
      (uniformOn Set.univ) (e ⁻¹' test) = uniformOn Set.univ test := by
    rw [← Measure.map_apply (measurable_of_finite e) test.toFinite.measurableSet,
      map_uniformOn_univ_of_equiv e]
  have hevent : {A : Fin m → Fin n → Bool | u ≤ |⟪signMatrixLinear A x, y⟫|} =
      e ⁻¹' test := by
    ext A
    have heq : ⟪signMatrixLinear A x, y⟫ = signSum a (e A) := by
      change (∑ i, y i * (signMatrixLinear A x) i) =
        ∑ ij : Fin m × Fin n, y ij.1 * x ij.2 * (if A ij.1 ij.2 then 1 else -1)
      simp only [signMatrixLinear_apply, Finset.mul_sum, Fintype.sum_prod_type, realSigns, mul_assoc]
    change (u ≤ |⟪signMatrixLinear A x, y⟫|) ↔ (u ≤ |signSum a (e A)|)
    rw [heq]
  rw [hevent, measureReal_def, hmap, ← measureReal_def]
  exact hp

/-- An operator norm tail bound for a rectangular matrix of independent signs. -/
theorem signMatrix_norm_tail_le {m n : ℕ} {K : ℝ} (hK : 0 ≤ K) :
    (uniformOn Set.univ).real {M : Fin m → Fin n → Bool | ∃ a : Fin n → ℝ,
      K ^ 2 * (n : ℝ) * (∑ i, a i ^ 2) < ∑ j, (∑ i, a i * realSigns (M j) i) ^ 2}
      ≤ (9 : ℝ) ^ (n + m) * (2 * Real.exp (-K ^ 2 * (n : ℝ) / 8)) := by
  classical
  obtain ⟨X, hXnorm, hXnet, hXcard⟩ := exists_unit_sphere_net n (ε := 1 / 4) (by norm_num)
  obtain ⟨Y, hYnorm, hYnet, hYcard⟩ := exists_unit_sphere_net m (ε := 1 / 4) (by norm_num)
  norm_num at hXcard hYcard
  let μ : Measure (Fin m → Fin n → Bool) := uniformOn Set.univ
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let u := K * Real.sqrt (n : ℝ) / 2
  have hu : 0 ≤ u := by positivity
  let E (p : EuclideanSpace ℝ (Fin n)) (q : EuclideanSpace ℝ (Fin m)) :
      Set (Fin m → Fin n → Bool) := {A | u ≤ |⟪signMatrixLinear A p, q⟫|}
  have hsub : {M : Fin m → Fin n → Bool | ∃ a : Fin n → ℝ,
      K ^ 2 * (n : ℝ) * (∑ i, a i ^ 2) < ∑ j, (∑ i, a i * realSigns (M j) i) ^ 2} ⊆
      ⋃ p ∈ X, ⋃ q ∈ Y, E p q := by
    rintro M ⟨a, ha⟩
    by_contra! hfalse
    have hpair (p) (hp : p ∈ X) (q) (hq : q ∈ Y) :
        |⟪signMatrixLinear M p, q⟫| ≤ u := by
      by_contra! h
      exact hfalse (Set.mem_iUnion₂.mpr ⟨p, hp, Set.mem_iUnion₂.mpr ⟨q, hq, h.le⟩⟩)
    have hL := opNorm_le_of_unit_pairings (signMatrixLinear M) X Y hXnorm
      (by simpa using hXnet) (by simpa using hYnet) hu hpair
    have hL' : ‖signMatrixLinear M‖ ≤ K * Real.sqrt (n : ℝ) := by
      calc
        _ ≤ 2 * u := hL
        _ = _ := by dsimp [u]; ring
    have hb := (signMatrixLinear M).le_of_opNorm_le hL' (toLp 2 a)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), EuclideanSpace.real_norm_sq_eq,
      signMatrixLinear_apply] at hs
    exact (not_le_of_gt ha) hs
  have htail (p) (hp : p ∈ X) (q) (hq : q ∈ Y) :
      μ.real (E p q) ≤ 2 * Real.exp (-K ^ 2 * (n : ℝ) / 8) := by
    have heq : -u ^ 2 / 2 = -K ^ 2 * (n : ℝ) / 8 := by
      simp only [u, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    rw [← heq]
    exact signMatrix_pairing_tail_le p q (hXnorm p hp) (hYnorm q hq) hu
  calc
    _ ≤ μ.real (⋃ p ∈ X, ⋃ q ∈ Y, E p q) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ p ∈ X, μ.real (⋃ q ∈ Y, E p q) := measureReal_biUnion_finset_le X _
    _ ≤ ∑ p ∈ X, ∑ q ∈ Y, μ.real (E p q) :=
      Finset.sum_le_sum fun p _ => measureReal_biUnion_finset_le Y (E p)
    _ ≤ ∑ _p ∈ X, ∑ _q ∈ Y, 2 * Real.exp (-K ^ 2 * (n : ℝ) / 8) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => htail p hp q hq
    _ = (X.card : ℝ) * (Y.card : ℝ) * (2 * Real.exp (-K ^ 2 * (n : ℝ) / 8)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ _ := by
      rw [pow_add]
      gcongr

/-- The threshold can be chosen so that failure has any prescribed
exponential rate, uniformly over matrices with no more rows than columns. -/
theorem signMatrix_norm_tail_exponential (B : ℝ) (hB : 0 ≤ B) :
    ∃ K > (0 : ℝ), ∀ n m : ℕ, 1 ≤ n → m ≤ n →
      (uniformOn Set.univ).real {M : Fin m → Fin n → Bool | ∃ a : Fin n → ℝ,
        K ^ 2 * (n : ℝ) * (∑ i, a i ^ 2) < ∑ j, (∑ i, a i * realSigns (M j) i) ^ 2}
        ≤ Real.exp (-B * (n : ℝ)) := by
  let K := Real.sqrt (8 * (17 + B))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun n m hn hm => ?_⟩
  have hKsq : K ^ 2 = 8 * (17 + B) := Real.sq_sqrt (by positivity)
  have hcount : (9 : ℝ) ^ (n + m) ≤ Real.exp (16 * (n : ℝ)) := by
    calc
      _ ≤ Real.exp (8 : ℝ) ^ (n + m) := by
        apply pow_le_pow_left₀ (by norm_num)
        have h := Real.add_one_le_exp (8 : ℝ)
        norm_num at h ⊢
        exact h
      _ = Real.exp (8 * ((n + m : ℕ) : ℝ)) := by rw [mul_comm, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_monotone (by
        push_cast
        have hm' : (m : ℝ) ≤ n := by exact_mod_cast hm
        linarith only [hm'])
  have ht : (2 : ℝ) ≤ Real.exp (n : ℝ) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact (by linarith only [hn'] : (2 : ℝ) ≤ (n : ℝ) + 1).trans (Real.add_one_le_exp _)
  refine (signMatrix_norm_tail_le hK.le).trans ?_
  calc
    (9 : ℝ) ^ (n + m) * (2 * Real.exp (-K ^ 2 * (n : ℝ) / 8))
      ≤ Real.exp (16 * (n : ℝ)) * (Real.exp (n : ℝ) * Real.exp (-K ^ 2 * (n : ℝ) / 8)) := by
        gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, hKsq]; congr 1; ring

end BooleanThreshold
