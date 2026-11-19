module

public import BooleanThreshold.JSSStructuredGeometry

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace BooleanThreshold

open scoped Classical in
/-- If a row falls in an event with probability at most `q`, the probability
that all but at most `k` of the rows fall in it is at most
`choose m k * q^(m-k)`. -/
theorem uniformOn_rows_outside_le {m n k : ℕ} (hk : k ≤ m)
    (A : Set (Fin n → Bool)) {q : ℝ≥0∞} (hA : uniformOn Set.univ A ≤ q) :
    uniformOn Set.univ {M : Fin m → Fin n → Bool |
      (Finset.univ.filter fun i => M i ∉ A).card ≤ k} ≤
      (m.choose k : ℝ≥0∞) * q ^ (m - k) := by
  classical
  let μ : Measure (Fin n → Bool) := uniformOn Set.univ
  let Isets := (Finset.univ : Finset (Fin m)).powersetCard k
  let E (I : Finset (Fin m)) : Set (Fin m → Fin n → Bool) :=
    Set.univ.pi (fun i => if i ∈ I then Set.univ else A)
  let S : Set (Fin m → Fin n → Bool) :=
    {M | (Finset.univ.filter fun i => M i ∉ A).card ≤ k}
  have hcover : S ⊆ ⋃ I ∈ Isets, E I := by
    intro M hM
    let bad := Finset.univ.filter fun i => M i ∉ A
    have hbad : bad.card ≤ k := hM
    obtain ⟨I, hsub, _, hIcard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ bad) hbad (by simpa using hk)
    have hI : I ∈ Isets := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hIcard⟩
    refine Set.mem_iUnion₂.mpr ⟨I, hI, Set.mem_univ_pi.mpr fun i => ?_⟩
    by_cases hi : i ∈ I
    · simp [hi]
    · have hnotbad : i ∉ bad := fun hmem => hi (hsub hmem)
      have hgood : M i ∈ A := by simpa [bad] using hnotbad
      simpa only [ite_eq_right hi] using hgood
  have hprob (I : Finset (Fin m)) (hI : I ∈ Isets) : uniformOn Set.univ (E I) ≤ q ^ (m - k) := by
    change uniformOn Set.univ (Set.univ.pi fun i => if i ∈ I then Set.univ else A) ≤ _
    rw [← pi_uniformOn_univ, Measure.pi_pi]
    change (∏ i : Fin m, μ (if i ∈ I then Set.univ else A)) ≤ _
    have hcardI := (Finset.mem_powersetCard.mp hI).2
    simp only [apply_ite, measure_univ, Finset.prod_ite, Finset.prod_const_one, one_mul,
      ← Finset.sdiff_eq_filter, Finset.prod_const, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin, hcardI]
    gcongr
  calc
    uniformOn Set.univ S ≤ uniformOn Set.univ (⋃ I ∈ Isets, E I) := measure_mono hcover
    _ ≤ ∑ I ∈ Isets, uniformOn Set.univ (E I) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _I ∈ Isets, q ^ (m - k) := Finset.sum_le_sum hprob
    _ = _ := by simp [Isets]

private theorem sq_filter_large_le_squaredNorm {m : ℕ} (v : Fin m → ℝ) {t : ℝ}
    (ht : 0 ≤ t) : ((Finset.univ.filter fun j => t < |v j|).card : ℝ) * t ^ 2 ≤ squaredNorm v := by
  classical
  let bad := Finset.univ.filter fun j => t < |v j|
  calc
    _ = ∑ j ∈ bad, t ^ 2 := by simp [bad]
    _ ≤ ∑ j ∈ bad, v j ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [sq_abs] using pow_le_pow_left₀ ht (Finset.mem_filter.mp hj).2.le 2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

/-- A finite net of vectors with small row concentration bounds the kernel
event on the operator norm event. -/
theorem uniformOn_null_probability_le_of_net {m n k : ℕ} (hk : k ≤ m)
    {K radius θ : ℝ} (hθ : 0 < θ)
    (hbudget : K ^ 2 * (m : ℝ) * radius ^ 2 ≤ (k : ℝ) * θ ^ 2)
    (S : Set (Fin n → ℝ)) (T : Finset (Fin n → ℝ))
    (hcover : ∀ a ∈ S, ∃ b ∈ T, squaredNorm (b - a) ≤ radius ^ 2)
    {q : ℝ≥0∞}
    (hconc : ∀ b ∈ T, uniformOn Set.univ
      {row : Fin n → Bool | |∑ i, b i * realSigns row i| ≤ θ} ≤ q) :
    uniformOn Set.univ {M : Fin m → Fin n → Bool |
      signOpBound K M ∧ ∃ a ∈ S, signMatrixMap M a = 0} ≤
      (T.card : ℝ≥0∞) * (m.choose k : ℝ≥0∞) * q ^ (m - k) := by
  classical
  let A (b : Fin n → ℝ) : Set (Fin n → Bool) :=
    {row | |∑ i, b i * realSigns row i| ≤ θ}
  let E (b : Fin n → ℝ) : Set (Fin m → Fin n → Bool) :=
    {M | (Finset.univ.filter fun j => M j ∉ A b).card ≤ k}
  have hinc : {M : Fin m → Fin n → Bool |
      signOpBound K M ∧ ∃ a ∈ S, signMatrixMap M a = 0} ⊆ ⋃ b ∈ T, E b := by
    rintro M ⟨hM, a, haS, ha⟩
    obtain ⟨b, hb, hd⟩ := hcover a haS
    apply Set.mem_iUnion₂.mpr
    refine ⟨b, hb, ?_⟩
    have hbad := sq_filter_large_le_squaredNorm (signMatrixMap M b) hθ.le
    have hmat := squaredNorm_signMatrixMap_le_of_null hM (b := b) ha
    have hclose := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (sq_nonneg K) (Nat.cast_nonneg m))
    have hle := (hbad.trans (hmat.trans hclose)).trans hbudget
    have hcard := le_of_mul_le_mul_right hle (sq_pos_of_pos hθ)
    simpa only [E, A, Set.mem_ofPred_eq, not_le, signMatrixMap_apply] using (show
      (Finset.univ.filter fun j => θ < |signMatrixMap M b j|).card ≤ k by exact_mod_cast hcard)
  calc
    _ ≤ uniformOn Set.univ (⋃ b ∈ T, E b) := measure_mono hinc
    _ ≤ ∑ b ∈ T, uniformOn Set.univ (E b) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _b ∈ T, (m.choose k : ℝ≥0∞) * q ^ (m - k) :=
      Finset.sum_le_sum fun b hb => uniformOn_rows_outside_le hk (A b) (hconc b hb)
    _ = _ := by simp [mul_assoc]

end BooleanThreshold
