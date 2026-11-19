module

public import BooleanThreshold.JSSConditionalNet
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

open Module
open scoped NNReal BigOperators

namespace BooleanThreshold

private def extendCoordinates {n : ℕ} (I : Finset (Fin n))
    (x : EuclideanSpace ℝ I) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if hi : i ∈ I then x ⟨i, hi⟩ else 0)

private theorem norm_extendCoordinates {n : ℕ} (I : Finset (Fin n))
    (x : EuclideanSpace ℝ I) : ‖extendCoordinates I x‖ = ‖x‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  let w : Fin n → ℝ := fun i => (extendCoordinates I x i) ^ 2
  change (∑ i, w i) = ∑ i : I, (x i) ^ 2
  have hw : (∑ i ∈ I, w i) = ∑ i, w i :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simp [w, extendCoordinates, hi]
  rw [← hw, ← Finset.sum_coe_sort I w]
  apply Finset.sum_congr rfl
  intro i _
  simp [w, extendCoordinates, i.2]

private theorem extendCoordinates_sub {n : ℕ} (I : Finset (Fin n))
    (x y : EuclideanSpace ℝ I) :
    extendCoordinates I (x - y) = extendCoordinates I x - extendCoordinates I y := by
  ext i
  by_cases hi : i ∈ I <;> simp [extendCoordinates, hi]

private theorem exists_support_sphere_net {n : ℕ} (I : Finset (Fin n)) {ε : ℝ≥0}
    (hε : 0 < ε) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ t ∈ T, ‖t‖ = 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → (∀ i ∉ I, x i = 0) →
        ∃ t ∈ T, ‖x - t‖ ≤ (ε : ℝ)) ∧ (T.card : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ I.card := by
  classical
  let V := EuclideanSpace ℝ I
  let e := (stdOrthonormalBasis ℝ V).repr
  obtain ⟨S, hS, hcover, hcard⟩ := exists_unit_sphere_net (finrank ℝ V) hε
  have hdim : finrank ℝ V = I.card := by
    rw [finrank_euclideanSpace, Fintype.card_coe]
  let T := S.image (fun t => extendCoordinates I (e.symm t))
  refine ⟨T, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [norm_extendCoordinates, e.symm.norm_map]
    exact hS u hu
  · intro x hx hsupp
    let y : V := WithLp.toLp 2 (fun i : I => x i)
    have hy : extendCoordinates I y = x := by
      ext i
      by_cases hi : i ∈ I
      · simp [extendCoordinates, y, hi]
      · simp [extendCoordinates, hi, hsupp i hi]
    have hnorm : ‖e y‖ = 1 := by rw [e.norm_map, ← norm_extendCoordinates I y, hy, hx]
    obtain ⟨t, ht, hdist⟩ := hcover (e y) hnorm
    refine ⟨extendCoordinates I (e.symm t), Finset.mem_image_of_mem _ ht, ?_⟩
    rw [← hy, ← extendCoordinates_sub, norm_extendCoordinates, ← e.norm_map,
      map_sub, e.apply_symm_apply]
    exact hdist
  · have hT : (T.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
    exact hT.trans (by simpa only [hdim] using hcard)

/-- The unit vectors supported on at most `s` coordinates have a small Euclidean net. -/
theorem exists_sparse_unit_sphere_net (n s : ℕ) (hs : s ≤ n) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ t ∈ T, ‖t‖ = 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
        (Finset.univ.filter fun i => x i ≠ 0).card ≤ s → ∃ t ∈ T, ‖x - t‖ ≤ (ε : ℝ)) ∧
      (T.card : ℝ) ≤ (n.choose s : ℝ) * (1 + 2 / (ε : ℝ)) ^ s := by
  classical
  choose g hgunit hgcover hgcard using fun I : Finset (Fin n) => exists_support_sphere_net I hε
  let choices := (Finset.univ : Finset (Fin n)).powersetCard s
  let T := choices.biUnion g
  refine ⟨T, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨I, _, hi⟩ := Finset.mem_biUnion.mp ht
    exact hgunit I t hi
  · intro x hx hsupp
    let J := Finset.univ.filter fun i => x i ≠ 0
    obtain ⟨I, hJI, _, hcard⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ J)
      hsupp (by simpa using hs)
    obtain ⟨t, ht, hd⟩ := hgcover I x hx (fun i hi => by
      by_contra hn
      exact hi (hJI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)))
    exact ⟨t, Finset.mem_biUnion.mpr ⟨I, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hcard⟩, ht⟩, hd⟩
  · calc
      (T.card : ℝ) ≤ ∑ I ∈ choices, ((g I).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _I ∈ choices, (1 + 2 / (ε : ℝ)) ^ s := by
        apply Finset.sum_le_sum
        intro I hI
        simpa only [(Finset.mem_powersetCard.mp hI).2] using hgcard I
      _ = _ := by simp [choices, Finset.card_powersetCard]

open scoped Classical in
/-- The vector is within Euclidean distance `ρ` of an `s`-sparse vector. -/
def nearSparse {n : ℕ} (s : ℕ) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ y : EuclideanSpace ℝ (Fin n),
    (Finset.univ.filter fun i => y i ≠ 0).card ≤ s ∧ ‖x - y‖ ≤ ρ

/-- A pair of orthogonal unit vectors in the Euclidean space on `Fin n`. -/
def orthonormalPair {n : ℕ} (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ ∑ i, p.1 i * p.2 i = 0

private theorem nearSparse_unit {n s : ℕ} {ρ : ℝ} (hρ : ρ < 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) (hc : nearSparse s ρ x) :
    ∃ y : EuclideanSpace ℝ (Fin n),
      ‖y‖ = 1 ∧ (Finset.univ.filter fun i => y i ≠ 0).card ≤ s ∧ ‖x - y‖ ≤ 2 * ρ := by
  classical
  obtain ⟨z, hs, hd⟩ := hc
  have hne : z ≠ 0 := by
    intro hz
    rw [hz, sub_zero, hx] at hd
    linarith only [hd, hρ]
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hne
  let y : EuclideanSpace ℝ (Fin n) := ‖z‖⁻¹ • z
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, hp.ne']
  refine ⟨y, hy, ?_, ?_⟩
  · refine (Finset.card_le_card ?_).trans hs
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    contrapose! hi
    change ‖z‖⁻¹ * z i = 0
    rw [hi, mul_zero]
  · have heq : ‖z‖ • y = z := by simp [y, smul_smul, hp.ne']
    have hzy : ‖z - y‖ ≤ ρ := by
      calc
        _ = ‖(‖z‖ - 1) • y‖ := by rw [sub_smul, one_smul, heq]
        _ = |‖z‖ - 1| := by simp [norm_smul, Real.norm_eq_abs, hy]
        _ ≤ ‖z - x‖ := by simpa only [hx] using abs_norm_sub_norm_le z x
        _ ≤ ρ := by simpa only [norm_sub_rev] using hd
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith only [hd, hzy]

/-- A net of orthonormal pairs whose two directions are close to sparse
vectors. The representatives remain orthonormal. -/
theorem exists_nearSparse_pair_net (n s : ℕ) (hs : s ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ p ∈ T, orthonormalPair p) ∧
      (∀ x, orthonormalPair x → nearSparse s ρ x.1 → nearSparse s ρ x.2 →
        ∃ p ∈ T, ‖x.1 - p.1‖ ≤ 2 * ((ε : ℝ) + 2 * ρ) ∧
          ‖x.2 - p.2‖ ≤ 2 * ((ε : ℝ) + 2 * ρ)) ∧
      (T.card : ℝ) ≤ ((n.choose s : ℝ) * (1 + 2 / (ε : ℝ)) ^ s) ^ 2 := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨S, _, hcover, hcard⟩ := exists_sparse_unit_sphere_net n s hs hε
  let choices := S ×ˢ S
  let b := (ε : ℝ) + 2 * ρ
  let N (p : E × E) : Set (E × E) :=
    {x | orthonormalPair x ∧ ‖x.1 - p.1‖ ≤ b ∧ ‖x.2 - p.2‖ ≤ b}
  let rep (p : E × E) : Finset (E × E) :=
    if h : (N p).Nonempty then {Classical.choose h} else ∅
  let T := choices.biUnion rep
  have ht (p x : E × E) (hx : x ∈ rep p) : x ∈ N p := by
    by_cases h : (N p).Nonempty
    · have heq : x = Classical.choose h := by simpa [rep, h] using hx
      rw [heq]
      exact Classical.choose_spec h
    · simp [rep, h] at hx
  refine ⟨T, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hp
    exact (ht z p hz).1
  · intro x hx hx₁ hx₂
    have hpoint (a : E) (ha : ‖a‖ = 1) (hc : nearSparse s ρ a) :
        ∃ p ∈ S, ‖a - p‖ ≤ b := by
      obtain ⟨z, hz, hzs, hzd⟩ := nearSparse_unit hρ ha hc
      obtain ⟨p, hp, hd⟩ := hcover z hz hzs
      refine ⟨p, hp, ?_⟩
      calc
        ‖a - p‖ = ‖(a - z) + (z - p)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖a - z‖ + ‖z - p‖ := norm_add_le _ _
        _ ≤ b := by dsimp [b]; linarith only [hzd, hd]
    obtain ⟨p₁, hp₁, hd₁⟩ := hpoint x.1 hx.1 hx₁
    obtain ⟨p₂, hp₂, hd₂⟩ := hpoint x.2 hx.2.1 hx₂
    let p : E × E := (p₁, p₂)
    have hp : p ∈ choices := Finset.mem_product.mpr ⟨hp₁, hp₂⟩
    have hn : (N p).Nonempty := ⟨x, hx, hd₁, hd₂⟩
    let z := Classical.choose hn
    have hz : z ∈ N p := Classical.choose_spec hn
    have hzT : z ∈ T := Finset.mem_biUnion.mpr ⟨p, hp, by simp [rep, hn, z]⟩
    have hdist (a c d : E) (ha : ‖a - c‖ ≤ b) (hd : ‖d - c‖ ≤ b) : ‖a - d‖ ≤ 2 * b := by
      calc
        ‖a - d‖ = ‖(a - c) + (c - d)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖a - c‖ + ‖c - d‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_sub_rev c d]; linarith only [ha, hd]
    exact ⟨z, hzT, hdist _ _ _ hd₁ hz.2.1, hdist _ _ _ hd₂ hz.2.2⟩
  · have hsize : T.card ≤ S.card ^ 2 := by
      calc
        _ ≤ ∑ p ∈ choices, (rep p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ choices, 1 := by
          apply Finset.sum_le_sum
          intro p _
          by_cases h : (N p).Nonempty <;> simp [rep, h]
        _ = _ := by simp [choices, pow_two]
    have hsize' : (T.card : ℝ) ≤ (S.card : ℝ) ^ 2 := by exact_mod_cast hsize
    exact hsize'.trans (pow_le_pow_left₀ (by positivity) hcard 2)

end BooleanThreshold
