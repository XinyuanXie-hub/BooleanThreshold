module

public import BooleanThreshold.JSSCorankSmallBall
public import BooleanThreshold.JSSCorankNet
public import BooleanThreshold.JSSStructuredGeometry
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open MeasureTheory ProbabilityTheory Module
open scoped BigOperators ENNReal NNReal

namespace BooleanThreshold

/-- All unit vectors in the common null space are close to sparse vectors. -/
def corankCompressibleEvent (m n s : ℕ) (ρ : ℝ) : Set (Fin m → Fin n → Bool) :=
  {M | ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 →
    signMatrixMap M (WithLp.ofLp a) = 0 → nearSparse s ρ a}

private theorem exists_orthogonal_unit_vectors (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hdim : 2 ≤ finrank ℝ V) :
    ∃ u v : V, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 := by
  let e := stdOrthonormalBasis ℝ V
  let i : Fin (finrank ℝ V) := ⟨0, by omega⟩
  let j : Fin (finrank ℝ V) := ⟨1, by omega⟩
  have hne : i ≠ j := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  exact ⟨e i, e j, e.orthonormal.norm_eq_one i, e.orthonormal.norm_eq_one j,
    e.orthonormal.inner_eq_zero hne⟩

private theorem exists_orthonormalPair_in_kernel {m n : ℕ} (hm : m + 2 ≤ n)
    (M : Fin m → Fin n → Bool) :
    ∃ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      orthonormalPair p ∧ signMatrixMap M (WithLp.ofLp p.1) = 0 ∧
        signMatrixMap M (WithLp.ofLp p.2) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : E →ₗ[ℝ] (Fin m → ℝ) := (signMatrixMap M).comp (WithLp.linearEquiv 2 ℝ _).toLinearMap
  let V := LinearMap.ker L
  have hdim : 2 ≤ finrank ℝ V := by
    have hrank := L.finrank_range_add_finrank_ker
    have hle : finrank ℝ (LinearMap.range L) ≤ m := by
      simpa only [Module.finrank_pi, Fintype.card_fin] using
        Submodule.finrank_le (LinearMap.range L)
    rw [finrank_euclideanSpace_fin] at hrank
    change 2 ≤ finrank ℝ (LinearMap.ker L)
    omega
  obtain ⟨u, v, hu, hv, hab⟩ := exists_orthogonal_unit_vectors V hdim
  have hker (x : V) : L x.1 = 0 := LinearMap.mem_ker.mp x.2
  have hi (x y : E) (hxy : inner ℝ x y = 0) : ∑ j, x j * y j = 0 := by
    have heq : inner ℝ x y = ∑ j, inner ℝ (x j) (y j) := PiLp.inner_apply x y
    rw [heq] at hxy
    simpa only [Real.inner_apply] using hxy
  refine ⟨(u.1, v.1), ⟨hu, hv, hi u.1 v.1 hab⟩, ?_, ?_⟩
  · change L u.1 = 0
    exact hker u
  · change L v.1 = 0
    exact hker v

private theorem uniform_rows_exception_real {m d : ℕ} (I : Finset (Fin m))
    (U : Set (Fin d → Bool)) :
    (uniformOn Set.univ).real {M : Fin m → Fin d → Bool | ∀ i ∉ I, M i ∈ U} =
      ((uniformOn Set.univ).real U) ^ (m - I.card) := by
  classical
  let μ : Measure (Fin d → Bool) := uniformOn Set.univ
  let U' (i : Fin m) := if i ∈ I then Set.univ else U
  have hset : {M : Fin m → Fin d → Bool | ∀ i ∉ I, M i ∈ U} = Set.univ.pi U' := by
    ext M
    change (∀ i ∉ I, M i ∈ U) ↔ (∀ i ∈ Set.univ, M i ∈ U' i)
    constructor
    · intro h i _
      by_cases hi : i ∈ I
      · simp [U', hi]
      · simpa [U', hi] using h i hi
    · intro h i hi
      simpa [U', hi] using h i (Set.mem_univ i)
  rw [← pi_uniformOn_univ, hset, measureReal_def, Measure.pi_pi]
  change (∏ i, μ (U' i)).toReal = _
  simp only [U', apply_ite, measure_univ, Finset.prod_ite, Finset.prod_const_one,
    one_mul, Finset.prod_const, Finset.filter_notMem_eq_sdiff,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow, ← measureReal_def]
  rfl

/-- Tensorization of the fixed two-direction small-ball bound, allowing an
energy budget of `e` times the squared row radius. -/
theorem fixed_orthonormal_pair_energy_probability_le {m d e : ℕ} (he : e ≤ m)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (hp : orthonormalPair p) :
    (uniformOn Set.univ).real {M : Fin m → Fin d → Bool |
      (∑ j, ((signSum (WithLp.ofLp p.1) (M j)) ^ 2 + (signSum (WithLp.ofLp p.2) (M j)) ^ 2)) ≤
        (e : ℝ) * (1 / 100 : ℝ) ^ 2} ≤ (m.choose e : ℝ) * (7 / 16 : ℝ) ^ (m - e) := by
  classical
  let θ₂ := (1 / 100 : ℝ) ^ 2
  let q := (7 / 16 : ℝ)
  let energy (b : Fin d → Bool) :=
    (signSum (WithLp.ofLp p.1) b) ^ 2 + (signSum (WithLp.ofLp p.2) b) ^ 2
  let U : Set (Fin d → Bool) := {b | energy b ≤ θ₂}
  let E (I : Finset (Fin m)) : Set (Fin m → Fin d → Bool) := {M | ∀ j ∉ I, M j ∈ U}
  let choices := (Finset.univ : Finset (Fin m)).powersetCard e
  let ν : Measure (Fin m → Fin d → Bool) := uniformOn Set.univ
  have hp₁ : ∑ i, (WithLp.ofLp p.1 i) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hp.1, one_pow]
  have hp₂ : ∑ i, (WithLp.ofLp p.2 i) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hp.2.1, one_pow]
  have hU : (uniformOn Set.univ).real U ≤ q :=
    orthonormal_signSum_small_ball_le _ _ hp₁ hp₂ hp.2.2
  have hCover : {M | ∑ j, energy (M j) ≤ (e : ℝ) * θ₂} ⊆ ⋃ I ∈ choices, E I := by
    intro M hM
    let J := Finset.univ.filter fun j => θ₂ < energy (M j)
    have henergy : (J.card : ℝ) * θ₂ ≤ ∑ j, energy (M j) := by
      calc
        _ = ∑ j ∈ J, θ₂ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ J, energy (M j) := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2.le
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by
          dsimp [energy]
          positivity)
    have hcard : J.card ≤ e := by
      have hle := le_of_mul_le_mul_right
        (henergy.trans (show ∑ j, energy (M j) ≤ (e : ℝ) * θ₂ from hM))
        (by positivity : 0 < θ₂)
      exact_mod_cast hle
    obtain ⟨I, hJI, _, hI⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ J)
      hcard (by simpa using he)
    refine Set.mem_iUnion₂.mpr ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hI⟩, ?_⟩
    intro j hj
    change energy (M j) ≤ θ₂
    by_contra h
    apply hj
    exact hJI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
  calc
    _ ≤ ν.real (⋃ I ∈ choices, E I) := measureReal_mono hCover (measure_ne_top _ _)
    _ ≤ ∑ I ∈ choices, ν.real (E I) := measureReal_biUnion_finset_le choices E
    _ ≤ ∑ _I ∈ choices, q ^ (m - e) := by
      apply Finset.sum_le_sum
      intro I hI
      rw [uniform_rows_exception_real, (Finset.mem_powersetCard.mp hI).2]
      exact pow_le_pow_left₀ (by positivity) hU _
    _ = _ := by simp [choices, q]

/-- Combine the sparse pair net, fixed-pair small-ball estimate, and a
matrix norm bound to control the compressible-kernel event. -/
theorem corankCompressible_probability_le {m n s e : ℕ} (hm : m + 2 ≤ n)
    (hs : s ≤ n) (he : e ≤ m) {K ρ : ℝ} (hρ : ρ < 1) {ε : ℝ≥0} (hε : 0 < ε)
    (hbudget : 8 * K ^ 2 * (n : ℝ) * ((ε : ℝ) + 2 * ρ) ^ 2 ≤
      (e : ℝ) * (1 / 100 : ℝ) ^ 2) :
    (uniformOn Set.univ).real (corankCompressibleEvent m n s ρ) ≤
      (uniformOn Set.univ).real {M : Fin m → Fin n → Bool | ∃ a : Fin n → ℝ,
        K ^ 2 * (n : ℝ) * squaredNorm a < squaredNorm (signMatrixMap M a)} +
      ((n.choose s : ℝ) * (1 + 2 / (ε : ℝ)) ^ s) ^ 2 *
        ((m.choose e : ℝ) * (7 / 16 : ℝ) ^ (m - e)) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure (Fin m → Fin n → Bool) := uniformOn Set.univ
  let B : Set (Fin m → Fin n → Bool) := {M | ∃ a : Fin n → ℝ,
    K ^ 2 * (n : ℝ) * squaredNorm a < squaredNorm (signMatrixMap M a)}
  let P (p : E × E) : Set (Fin m → Fin n → Bool) := {M |
    (∑ j, ((signSum (WithLp.ofLp p.1) (M j)) ^ 2 + (signSum (WithLp.ofLp p.2) (M j)) ^ 2)) ≤
      (e : ℝ) * (1 / 100 : ℝ) ^ 2}
  let b := (ε : ℝ) + 2 * ρ
  obtain ⟨T, hT, hcover, hcard⟩ := exists_nearSparse_pair_net n s hs hρ hε
  have hsub : corankCompressibleEvent m n s ρ ⊆ B ∪ ⋃ p ∈ T, P p := by
    intro M hM
    by_cases hB : M ∈ B
    · exact Or.inl hB
    right
    obtain ⟨x, hx, hx₁, hx₂⟩ := exists_orthonormalPair_in_kernel hm M
    obtain ⟨p, hp, hd₁, hd₂⟩ :=
      hcover x hx (hM _ hx.1 hx₁) (hM _ hx.2.1 hx₂)
    refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    have hbound (a c : E) (ha : signMatrixMap M (WithLp.ofLp a) = 0)
        (hd : ‖a - c‖ ≤ 2 * b) :
        squaredNorm (signMatrixMap M (WithLp.ofLp c)) ≤ K ^ 2 * (n : ℝ) * (2 * b) ^ 2 := by
      have hnorm : squaredNorm (signMatrixMap M (WithLp.ofLp (c - a))) ≤
          K ^ 2 * (n : ℝ) * squaredNorm (WithLp.ofLp (c - a)) :=
        le_of_not_gt fun h => hB ⟨WithLp.ofLp (c - a), h⟩
      have hmap : signMatrixMap M (WithLp.ofLp (c - a)) = signMatrixMap M (WithLp.ofLp c) := by
        change signMatrixMap M (WithLp.ofLp c - WithLp.ofLp a) = _
        rw [map_sub, ha, sub_zero]
      have hsq : squaredNorm (WithLp.ofLp (c - a)) = ‖c - a‖ ^ 2 :=
        (EuclideanSpace.real_norm_sq_eq _).symm
      rw [hmap, hsq] at hnorm
      refine hnorm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [norm_sub_rev c a]
      exact pow_le_pow_left₀ (by positivity) hd 2
    have h₁ := hbound x.1 p.1 hx₁ hd₁
    have h₂ := hbound x.2 p.2 hx₂ hd₂
    have henergy :
        (∑ j, ((signSum (WithLp.ofLp p.1) (M j)) ^ 2 + (signSum (WithLp.ofLp p.2) (M j)) ^ 2)) =
          squaredNorm (signMatrixMap M (WithLp.ofLp p.1)) +
            squaredNorm (signMatrixMap M (WithLp.ofLp p.2)) := by
      simp only [signSum, squaredNorm, signMatrixMap_apply, realSigns, Finset.sum_add_distrib]
    change (∑ j, ((signSum (WithLp.ofLp p.1) (M j)) ^ 2 +
      (signSum (WithLp.ofLp p.2) (M j)) ^ 2)) ≤ _
    rw [henergy]
    change 8 * K ^ 2 * (n : ℝ) * b ^ 2 ≤ _ at hbudget
    exact (add_le_add h₁ h₂).trans ((by ring :
      K ^ 2 * (n : ℝ) * (2 * b) ^ 2 + K ^ 2 * (n : ℝ) * (2 * b) ^ 2 =
        8 * K ^ 2 * (n : ℝ) * b ^ 2).trans_le hbudget)
  calc
    _ ≤ μ.real (B ∪ ⋃ p ∈ T, P p) := measureReal_mono hsub
    _ ≤ μ.real B + μ.real (⋃ p ∈ T, P p) := measureReal_union_le _ _
    _ ≤ μ.real B + ∑ p ∈ T, μ.real (P p) :=
      add_le_add (le_refl _) (measureReal_biUnion_finset_le T P)
    _ ≤ μ.real B + ∑ _p ∈ T, ((m.choose e : ℝ) * (7 / 16 : ℝ) ^ (m - e)) :=
      add_le_add (le_refl _) (Finset.sum_le_sum fun p hp =>
        fixed_orthonormal_pair_energy_probability_le he p (hT p hp))
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard (by positivity))

end BooleanThreshold
