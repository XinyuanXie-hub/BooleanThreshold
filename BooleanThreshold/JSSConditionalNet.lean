module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.MetricSpace.CoveringNumbers

public section

open scoped NNReal ENNReal BigOperators
open MeasureTheory Metric Module

namespace BooleanThreshold

/-- A compact set in the ball of radius `R` has a finite `ε`-net whose size
is bounded by the ratio of the enclosing and disjoint packing ball volumes. -/
theorem exists_finset_net_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsCompact S) {R : ℝ} (hR : 0 ≤ R)
    (hbound : S ⊆ closedBall 0 R) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ T : Finset E, (T : Set E) ⊆ S ∧
      (∀ x ∈ S, ∃ t ∈ T, ‖x - t‖ ≤ (ε : ℝ)) ∧
      (T.card : ℝ) ≤ (1 + 2 * R / (ε : ℝ)) ^ finrank ℝ E := by
  classical
  let δ : ℝ≥0 := ε / 2
  have hδ : 0 < δ := by positivity
  have h2δ : 2 * δ = ε := by
    apply NNReal.eq
    simp [δ]
    ring
  obtain ⟨C, _, hfinite, hC⟩ :=
    exists_finite_isCover_of_isCompact (ε := δ) hδ.ne' hS
  have hpack : packingNumber ε S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hfinite)
    calc
      packingNumber ε S ≤ externalCoveringNumber δ S := by
        rw [← h2δ]
        exact packingNumber_two_mul_le_externalCoveringNumber δ S
      _ ≤ C.encard := hC.externalCoveringNumber_le_encard
  let N := maximalSeparatedSet ε S
  have hN : N ⊆ S := maximalSeparatedSet_subset
  have hNfinite : N.Finite := Set.encard_ne_top_iff.mp (encard_maximalSeparatedSet hpack ▸ hpack)
  have hsep : IsSeparated (ε : ℝ≥0∞) N := isSeparated_maximalSeparatedSet
  let T := hNfinite.toFinset
  have hT : (↑T : Set E) = N := Set.Finite.coe_toFinset _
  have hcover : IsCover ε S N := isCover_maximalSeparatedSet hpack
  have hTS : (↑T : Set E) ⊆ S := hT ▸ hN
  refine ⟨T, hTS, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, hdt⟩ := hcover hx
    refine ⟨t, by simpa [T] using ht, ?_⟩
    change edist x t ≤ (ε : ℝ≥0∞) at hdt
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hdt
    rw [← dist_eq_norm]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hdt
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := (Module.finBasis ℝ E).addHaar
  let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  let radius : ℝ := δ
  have hrad : 0 < radius := by exact_mod_cast hδ
  let balls (t : E) := ball t radius
  have hd : (↑T : Set E).PairwiseDisjoint balls := by
    intro x hx y hy hxy
    have hdx := hsep (hT ▸ hx) (hT ▸ hy) hxy
    apply ball_disjoint_ball
    change (ε : ℝ≥0∞) < edist x y at hdx
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hdx
    have hdist : (ε : ℝ) < dist x y :=
      lt_of_not_ge fun h => (not_le_of_gt hdx) (ENNReal.ofReal_le_ofReal h)
    have hsum : radius + radius = (ε : ℝ) := by
      change (δ : ℝ) + (δ : ℝ) = (ε : ℝ)
      exact_mod_cast (by simpa [two_mul] using h2δ : δ + δ = ε)
    exact hsum ▸ hdist.le
  have hsub : (⋃ t ∈ T, balls t) ⊆ ball (0 : E) (R + radius) := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    change dist x t < radius at hxt
    have hnorm := hbound (hTS ht)
    change dist t (0 : E) ≤ R at hnorm
    change dist x (0 : E) < R + radius
    linarith only [dist_triangle x t 0, hxt, hnorm]
  have hs :
      (T.card : ℝ) * μ.real (ball 0 radius) ≤ μ.real (ball 0 (R + radius)) := by
    calc
      _ = ∑ t ∈ T, μ.real (balls t) := by
        simp [balls, Measure.addHaar_real_ball_center μ]
      _ = μ.real (⋃ t ∈ T, balls t) := by
        symm
        exact measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)
      _ ≤ _ := measureReal_mono hsub measure_ball_lt_top.ne
  have hradius : (1 + 2 * R / (ε : ℝ)) * radius = R + radius := by
    dsimp [radius, δ]
    field_simp [show (ε : ℝ) ≠ 0 by exact_mod_cast hε.ne']
    ring
  have hratio : 0 < 1 + 2 * R / (ε : ℝ) := by positivity
  rw [← hradius] at hs
  simp only [measureReal_def, Measure.addHaar_ball_mul_of_pos μ 0 hratio, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 + 2 * R / (ε : ℝ)) ^ finrank ℝ E)] at hs
  have hball : 0 < μ.real (ball 0 radius) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hrad).ne' measure_ball_lt_top.ne
  exact le_of_mul_le_mul_right hs hball

/-- A finite net with the standard volumetric bound for a closed ball. -/
theorem exists_closedBall_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 ≤ R) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ T : Finset E, (∀ x ∈ T, ‖x‖ ≤ R) ∧
      (∀ x, ‖x‖ ≤ R → ∃ t ∈ T, ‖x - t‖ ≤ (ε : ℝ)) ∧
      (T.card : ℝ) ≤ (1 + 2 * R / (ε : ℝ)) ^ finrank ℝ E := by
  obtain ⟨T, hT, hcover, hcard⟩ := exists_finset_net_of_isCompact (isCompact_closedBall (0 : E) R)
    hR (Set.Subset.rfl) hε
  refine ⟨T, fun x hx => ?_, fun x hx => hcover x ?_, hcard⟩
  · simpa using hT hx
  · simpa using hx

/-- A finite net on the Euclidean unit sphere. -/
theorem exists_unit_sphere_net (n : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ T, ‖x‖ = 1) ∧
      (∀ x, ‖x‖ = 1 → ∃ t ∈ T, ‖x - t‖ ≤ (ε : ℝ)) ∧
      (T.card : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ n := by
  obtain ⟨T, hT, hcover, hcard⟩ := exists_finset_net_of_isCompact
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1) zero_le_one
    sphere_subset_closedBall hε
  refine ⟨T, fun x hx => ?_, fun x hx => hcover x ?_, ?_⟩
  · simpa using hT hx
  · simpa using hx
  · simpa [finrank_euclideanSpace_fin] using hcard

end BooleanThreshold
