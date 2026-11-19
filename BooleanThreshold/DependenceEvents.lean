module

public import BooleanThreshold.Pairs
public import Mathlib.Data.Fin.Embedding
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BooleanThreshold

open scoped Classical in
/-- A dependence witnessed by a relation using at least three columns. -/
def nonPairDependence {n r : ℕ} (v : Fin r → Fin n → ℝ) : Prop :=
  ∃ a : Fin r → ℝ, 2 < (Finset.univ.filter fun i => a i ≠ 0).card ∧
    ∑ i, a i • v i = 0

theorem sum_smul_eq_zero_iff {n r : ℕ} {v : Fin r → Fin n → ℝ} {a : Fin r → ℝ} :
    (∑ i, a i • v i) = 0 ↔ ∀ j, ∑ i, a i * v i j = 0 := by
  simp only [funext_iff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]

/-- In a sign matrix with at least one row, a nonzero relation using at most two
columns forces two columns to be equal or opposite. -/
private theorem pair_of_small_relation {n r : ℕ} (hn : 0 < n)
    {v : Fin r → Fin n → ℝ} (hv : ∀ i, v i ∈ signCube n)
    {a : Fin r → ℝ} (ha : ∑ i, a i • v i = 0) (ha0 : ∃ i, a i ≠ 0)
    (hcard : (Finset.univ.filter fun i => a i ≠ 0).card ≤ 2) :
    pairCollision v := by
  classical
  let j₀ : Fin n := ⟨0, hn⟩
  have hv₀ (i : Fin r) : v i ≠ 0 := by
    intro h
    have hzero : v i j₀ = 0 := congrFun h j₀
    rcases hv i j₀ with hsign | hsign <;> linarith only [hzero, hsign]
  let support := Finset.univ.filter fun i => a i ≠ 0
  have hmem (i : Fin r) : i ∈ support ↔ a i ≠ 0 := by simp [support]
  have hnonempty : support.Nonempty := by
    obtain ⟨i, hi⟩ := ha0
    exact ⟨i, (hmem i).mpr hi⟩
  have hsum : ∑ i ∈ support, a i • v i = 0 := by
    rw [← ha]
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have hz : a i = 0 := not_not.mp (fun hnz => hi ((hmem i).mpr hnz))
    rw [hz, zero_smul]
  have hpos := hnonempty.card_pos
  change support.card ≤ 2 at hcard
  rcases (show support.card = 1 ∨ support.card = 2 by omega) with hone | htwo
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    have hai : a i ≠ 0 := (hmem i).mp (hi.symm ▸ Finset.mem_singleton_self i)
    rw [hi, Finset.sum_singleton, smul_eq_zero] at hsum
    exact False.elim (hsum.elim hai (hv₀ i))
  · obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp htwo
    have hai : a i ≠ 0 := (hmem i).mp (hs.symm ▸ Finset.mem_insert_self i {j})
    rw [hs, Finset.sum_pair hij] at hsum
    let t := -a j / a i
    have hvec : v i = t • v j := by
      have hterm : a i • v i = -(a j • v j) := eq_neg_of_add_eq_zero_left hsum
      have hvec := (eq_inv_smul_iff₀ hai).mpr hterm
      simpa [t, smul_neg, smul_smul, div_eq_mul_inv, mul_comm] using hvec
    have hcoord : v i j₀ = t * v j j₀ := congrFun hvec j₀
    have ht : t = 1 ∨ t = -1 := by
      rcases hv i j₀ with hi | hi <;> rcases hv j j₀ with hj | hj <;>
        rw [hi, hj] at hcoord <;> first | (left; linarith) | (right; linarith)
    have hpair : v i = v j ∨ v i = -v j := by
      rcases ht with h | h
      · left
        simpa [h] using hvec
      · right
        simpa [h] using hvec
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨i, j, hlt, hpair⟩
    · refine ⟨j, i, hlt, ?_⟩
      rcases hpair with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])

theorem dependence_iff_pair_or_nonPair {n r : ℕ} (hn : 0 < n)
    {v : Fin r → Fin n → ℝ} (hv : ∀ i, v i ∈ signCube n) :
    (¬ LinearIndependent ℝ v) ↔
      pairCollision v ∨ nonPairDependence v := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha, ha0⟩ := Fintype.not_linearIndependent_iff.mp h
    by_cases hcard : 2 < (Finset.univ.filter fun i => a i ≠ 0).card
    · exact Or.inr ⟨a, hcard, ha⟩
    · exact Or.inl (pair_of_small_relation hn hv ha ha0 (le_of_not_gt hcard))
  · rintro (h | ⟨a, ha, hsum⟩)
    · exact pairCollision_not_linearIndependent h
    · apply Fintype.not_linearIndependent_iff.mpr
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega :
        0 < (Finset.univ.filter fun i => a i ≠ 0).card)
      exact ⟨a, hsum, i, (Finset.mem_filter.mp hi).2⟩

/-- The excess dependence probability over pair collisions is at most the mass
of the event that a relation uses three or more columns. -/
theorem dependence_sub_pair_abs_le {n r : ℕ} (hn : 0 < n) :
    |(signLaw n r).real {v | ¬ LinearIndependent ℝ v} -
      (signLaw n r).real {v | pairCollision v}| ≤ (signLaw n r).real {v | nonPairDependence v} := by
  let D : Set (Fin r → Fin n → ℝ) := {v | ¬ LinearIndependent ℝ v}
  let F : Set (Fin r → Fin n → ℝ) := {v | pairCollision v}
  let E : Set (Fin r → Fin n → ℝ) := {v | nonPairDependence v}
  change |(signLaw n r).real D - (signLaw n r).real F| ≤ (signLaw n r).real E
  have hFD : F ⊆ D := fun _ h => pairCollision_not_linearIndependent h
  have hcover : signLaw n r D = signLaw n r (F ∪ E) :=
    signLaw_apply_eq_of_on_cube fun _ hv => dependence_iff_pair_or_nonPair hn hv
  have hreal : (signLaw n r).real D = (signLaw n r).real (F ∪ E) :=
    congrArg ENNReal.toReal hcover
  rw [abs_of_nonneg (sub_nonneg.mpr (measureReal_mono hFD)), hreal]
  exact sub_le_iff_le_add'.mpr (measureReal_union_le F E)

theorem nonPairDependence_of_restrict {n r s : ℕ} (e : Fin r ↪ Fin s)
    {v : Fin s → Fin n → ℝ} (h : nonPairDependence (fun i => v (e i))) :
    nonPairDependence v := by
  classical
  obtain ⟨a, hcard, hrel⟩ := h
  let b := Function.extend e a (fun _ => 0)
  have hb (i : Fin r) : b (e i) = a i := e.injective.extend_apply _ _ i
  have hsupport :
      (Finset.univ.filter fun j => b j ≠ 0) =
        (Finset.univ.filter fun i => a i ≠ 0).map e := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simp only [hb, Function.Embedding.apply_eq_iff_eq, exists_eq_right]
    · have hb0 : b j = 0 := Function.extend_apply' a _ j hj
      rw [hb0]
      exact ⟨fun h => (h rfl).elim, fun ⟨i, _, hi⟩ => (hj ⟨i, hi⟩).elim⟩
  refine ⟨b, by simpa only [hsupport, Finset.card_map] using hcard, ?_⟩
  rw [← hrel]
  calc
    (∑ j, b j • v j) = ∑ j ∈ Finset.univ.filter (fun j => b j ≠ 0), b j • v j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hbj : b j = 0 := by simpa using hj
      rw [hbj, zero_smul]
    _ = ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i • v (e i) := by
      rw [hsupport, Finset.sum_map]
      simp only [hb]
    _ = ∑ i, a i • v (e i) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hai : a i = 0 := by simpa using hi
      rw [hai, zero_smul]

/-- Extra sampled columns can only increase the probability of a relation
whose support has size greater than two. -/
theorem nonPair_probability_mono {n r s : ℕ} (h : r ≤ s) :
    (signLaw n r).real {v | nonPairDependence v} ≤
      (signLaw n s).real {v | nonPairDependence v} := by
  let e := Fin.castLEEmb h
  have hrestrict := congrArg ENNReal.toReal
    (signLaw_restrict_rows (n := n) e {v | nonPairDependence v})
  change (signLaw n s).real ((fun v i => v (e i)) ⁻¹' {v | nonPairDependence v}) =
    (signLaw n r).real {v | nonPairDependence v} at hrestrict
  rw [← hrestrict]
  exact measureReal_mono fun _ hmem => nonPairDependence_of_restrict e hmem

end BooleanThreshold
