module

public import BooleanThreshold.JSSConditionalNet
public import BooleanThreshold.SignWindow
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open Module Submodule
open scoped BigOperators NNReal

namespace BooleanThreshold

noncomputable def constantOutsideGenerators {n : ℕ} (I : Finset (Fin n)) :
    Option I → EuclideanSpace ℝ (Fin n)
  | none => WithLp.toLp 2 (fun _ => 1)
  | some i => WithLp.toLp 2 (Pi.single i.val 1)

/-- The subspace of vectors allowed to vary on `I` and required to be
constant on its complement. -/
noncomputable def constantOutsideSubspace {n : ℕ} (I : Finset (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  span ℝ (Set.range (constantOutsideGenerators I))

theorem finrank_constantOutsideSubspace_le {n : ℕ} (I : Finset (Fin n)) :
    finrank ℝ (constantOutsideSubspace I) ≤ I.card + 1 := by
  classical
  let g := constantOutsideGenerators I
  let : Fintype (Set.range g) := Fintype.ofFinite _
  exact (finrank_span_le_card (R := ℝ) (Set.range g)).trans (by
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le g)

private theorem constantOutside_mem {n : ℕ} (a : Fin n → ℝ) (center : ℝ)
    (I : Finset (Fin n)) :
    WithLp.toLp 2 (fun i => if i ∈ I then a i else center) ∈ constantOutsideSubspace I := by
  classical
  let T := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  have hconst : T (fun _ => 1) ∈ constantOutsideSubspace I :=
    subset_span ⟨none, rfl⟩
  have hbasis (i : Fin n) (hi : i ∈ I) : T (Pi.single i 1) ∈ constantOutsideSubspace I :=
    subset_span ⟨some ⟨i, hi⟩, rfl⟩
  have hdecomp : (fun i => if i ∈ I then a i else center) =
      center • (fun _ => (1 : ℝ)) + ∑ i ∈ I, (a i - center) • Pi.single i 1 := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_apply,
      Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq]
    by_cases hj : j ∈ I <;> simp [hj]
  change T (fun i => if i ∈ I then a i else center) ∈ _
  rw [hdecomp, map_add, map_smul, map_sum]
  apply add_mem (smul_mem _ _ hconst)
  exact sum_mem fun i hi => by rw [map_smul]; exact smul_mem _ _ (hbasis i hi)

/-- An almost-constant unit vector lies within `ρ` of a vector of norm at most
`1 + ρ` in one of the subspaces indexed by its exceptional coordinates. -/
theorem almostConstant_near_constantOutside {n : ℕ} (hn : 0 < n) {δ ρ : ℝ} (hρ : 0 ≤ ρ)
    {a : Fin n → ℝ} (ha : a ∈ almostConstantUnitVectors n δ ρ) :
    ∃ I : Finset (Fin n), (I.card : ℝ) ≤ δ * (n : ℝ) ∧
      ∃ b ∈ constantOutsideSubspace I,
        ‖b‖ ≤ 1 + ρ ∧ ‖WithLp.toLp 2 a - b‖ ≤ ρ := by
  classical
  obtain ⟨haunit, center, hcount⟩ := ha
  let I := Finset.univ.filter (fun i : Fin n => ¬ |a i - center| ≤ ρ / Real.sqrt (n : ℝ))
  let b (i : Fin n) := if i ∈ I then a i else center
  have hsum : ((Finset.univ.filter fun i => |a i - center| ≤ ρ / Real.sqrt (n : ℝ)).card : ℝ) +
      (I.card : ℝ) = (n : ℝ) := by
    exact_mod_cast (show (Finset.univ.filter fun i => |a i - center| ≤ ρ /
      Real.sqrt (n : ℝ)).card + I.card = n by
        simpa only [I, Finset.card_univ, Fintype.card_fin] using
          (Finset.card_filter_add_card_filter_not (s := Finset.univ)
            (fun i => |a i - center| ≤ ρ / Real.sqrt (n : ℝ))))
  have hdist : ‖WithLp.toLp 2 a - WithLp.toLp 2 b‖ ≤ ρ := by
    apply (sq_le_sq₀ (norm_nonneg _) hρ).mp
    rw [← WithLp.toLp_sub, EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (a i - b i) ^ 2) ≤ ρ ^ 2
    have hloc (i : Fin n) : |a i - b i| ≤ ρ / Real.sqrt (n : ℝ) := by
      by_cases hi : i ∈ I
      · simp [b, hi, div_nonneg hρ (Real.sqrt_nonneg _)]
      · have h := mt (fun hh => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hh⟩) hi
        simpa only [b, ite_eq_right hi, not_not] using h
    calc
      _ ≤ ∑ _ : Fin n, (ρ / Real.sqrt (n : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hloc i) 2
      _ = (n : ℝ) * (ρ / Real.sqrt (n : ℝ)) ^ 2 := by simp
      _ = _ := by
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        field_simp
  have hunit : ‖WithLp.toLp 2 a‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa [EuclideanSpace.real_norm_sq_eq] using haunit
  refine ⟨I, by nlinarith only [hsum, hcount], WithLp.toLp 2 b,
    constantOutside_mem a center I, ?_, hdist⟩
  calc
    _ ≤ ‖WithLp.toLp 2 a‖ + ‖WithLp.toLp 2 a - WithLp.toLp 2 b‖ :=
      norm_le_insert _ _
    _ ≤ _ := by rw [hunit]; linarith only [hdist]

private theorem exists_internal_net {E : Type*} [NormedAddCommGroup E]
    (S : Set E) (T : Finset E) (ε : ℝ)
    (hcover : ∀ x ∈ S, ∃ t ∈ T, ‖x - t‖ ≤ ε) :
    ∃ U : Finset E, (↑U : Set E) ⊆ S ∧
      (∀ x ∈ S, ∃ u ∈ U, ‖x - u‖ ≤ 2 * ε) ∧ U.card ≤ T.card := by
  classical
  let T' := T.filter fun t => ∃ x ∈ S, ‖x - t‖ ≤ ε
  let center (t : T') : E := Classical.choose (Finset.mem_filter.mp t.prop).2
  have hcenter (t : T') : center t ∈ S ∧ ‖center t - t.val‖ ≤ ε :=
    Classical.choose_spec (Finset.mem_filter.mp t.prop).2
  refine ⟨T'.attach.image center, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp (show x ∈ T'.attach.image center from hx)
    exact (hcenter t).1
  · intro x hx
    obtain ⟨t, ht, hd⟩ := hcover x hx
    let t' : T' := ⟨t, Finset.mem_filter.mpr ⟨ht, x, hx, hd⟩⟩
    refine ⟨center t', Finset.mem_image.mpr ⟨t', Finset.mem_attach _ _, rfl⟩, ?_⟩
    have hdt : ‖t - center t'‖ ≤ ε := by rw [norm_sub_rev]; exact (hcenter t').2
    linarith only [norm_sub_le_norm_sub_add_norm_sub x t (center t'), hd, hdt]
  · exact Finset.card_image_le.trans (by simpa [T'] using Finset.card_filter_le _ _)

/-- Net of a subset of the almost-constant sphere, with entropy determined by
the exceptional coordinates and the dimension of their subspaces. -/
theorem exists_almostConstant_net {n k : ℕ} (hn : 0 < n) {δ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hδk : δ * (n : ℝ) ≤ (k : ℝ)) {ε : ℝ≥0} (hε : 0 < ε)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ x ∈ S, x.ofLp ∈ almostConstantUnitVectors n δ ρ) :
    ∃ U : Finset (EuclideanSpace ℝ (Fin n)), (↑U : Set _) ⊆ S ∧
      (∀ x ∈ S, ∃ u ∈ U, ‖x - u‖ ≤ 2 * (ρ + (ε : ℝ))) ∧
      (U.card : ℝ) ≤ ((∑ l ∈ Finset.range (k + 1), (n.choose l : ℝ))) *
        (1 + 2 * (1 + ρ) / (ε : ℝ)) ^ (k + 1) := by
  classical
  let indices := ((Finset.univ : Finset (Fin n)).powerset).filter (fun I => I.card ≤ k)
  let base := 1 + 2 * (1 + ρ) / (ε : ℝ)
  have hbase : 1 ≤ base := by
    dsimp [base]
    exact le_add_of_nonneg_right (by positivity)
  have hnet (I : Finset (Fin n)) :=
    exists_closedBall_net (E := constantOutsideSubspace I) (R := 1 + ρ)
      (by positivity) hε
  choose net hbound hcover hcard using hnet
  let netInSpace (I : Finset (Fin n)) :=
    (net I).image (fun t : constantOutsideSubspace I => t.val)
  let T := indices.biUnion netInSpace
  have hT : ∀ x ∈ S, ∃ t ∈ T, ‖x - t‖ ≤ ρ + (ε : ℝ) := by
    intro x hx
    obtain ⟨I, hI, b, hb, hnorm, hdist⟩ :=
      almostConstant_near_constantOutside hn hρ (hS x hx)
    have hIK : I.card ≤ k := by exact_mod_cast (hI.trans hδk)
    obtain ⟨t, ht, htclose⟩ := hcover I ⟨b, hb⟩ hnorm
    refine ⟨t.val, Finset.mem_biUnion.mpr ⟨I, by simp [indices, hIK],
      Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩, ?_⟩
    change ‖b - t.val‖ ≤ (ε : ℝ) at htclose
    linarith only [norm_sub_le_norm_sub_add_norm_sub x b t.val, hdist, htclose]
  have hcount : (indices.card : ℝ) ≤ ∑ l ∈ Finset.range (k + 1), (n.choose l : ℝ) := by
    have hsub : indices ⊆ (Finset.range (k + 1)).biUnion (fun l =>
        (Finset.univ : Finset (Fin n)).powersetCard l) := by
      intro I hI
      have hIc := (Finset.mem_filter.mp hI).2
      exact Finset.mem_biUnion.mpr ⟨I.card, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hIc),
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, rfl⟩⟩
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans_eq (by simp))
  have hsize : (T.card : ℝ) ≤ (indices.card : ℝ) * base ^ (k + 1) := by
    calc
      _ ≤ ∑ I ∈ indices, ((netInSpace I).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _I ∈ indices, base ^ (k + 1) := by
        apply Finset.sum_le_sum
        intro I hI
        have hIc := (Finset.mem_filter.mp hI).2
        have hm : ((netInSpace I).card : ℝ) ≤ ((net I).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
        have hrank := (finrank_constantOutsideSubspace_le I).trans (Nat.add_le_add_right hIc 1)
        exact hm.trans ((hcard I).trans (pow_le_pow_right₀ hbase hrank))
      _ = _ := by simp
  obtain ⟨U, hUS, hUcover, hUcard⟩ := exists_internal_net S T _ hT
  refine ⟨U, hUS, hUcover, ?_⟩
  have hcardcast : (U.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hUcard
  exact hcardcast.trans (hsize.trans (mul_le_mul_of_nonneg_right hcount (by positivity)))

end BooleanThreshold
