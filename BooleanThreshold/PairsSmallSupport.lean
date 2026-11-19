module

public import BooleanThreshold.PairsConcentration

public section

open MeasureTheory ProbabilityTheory Module
open scoped BigOperators ENNReal

namespace BooleanThreshold

private theorem signLaw_rows_fixed_support_le {n r : ℕ} (I : Finset (Fin r))
    (hI : 3 ≤ I.card) (hn : I.card - 1 ≤ n) :
    signLaw r n {rows | ∃ a : I → ℝ, (∀ i, a i ≠ 0) ∧
      ∀ j, ∑ i : I, a i * rows j i = 0} ≤
      (n.choose (I.card - 1) : ℝ≥0∞) * (3 / 8 : ℝ≥0∞) ^ (n - (I.card - 1)) := by
  classical
  let μ : Measure (Fin r → Bool) := uniformOn Set.univ
  let eval (row : Fin r → Bool) : Module.Dual ℝ (I → ℝ) :=
    dotProductBilin ℝ ℝ (fun i : I => realSigns row i)
  let S : Set (I → ℝ) := {a | ∀ i, a i ≠ 0}
  have hS (a : I → ℝ) (ha : a ∈ S) : a ≠ 0 := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    intro h
    apply ha ⟨i, hi⟩
    exact congrFun h ⟨i, hi⟩
  have hsum (row : Fin r → Bool) (a : I → ℝ) :
      eval row a = ∑ i : I, a i * realSigns row i := by
    simp [eval, dotProduct, mul_comm]
  have hconc (a : I → ℝ) (ha : a ∈ S) : μ {row | eval row a = 0} ≤ (3 / 8 : ℝ≥0∞) := by
    let b (i : Fin r) : ℝ := if hi : i ∈ I then a ⟨i, hi⟩ else 0
    have hcard : (Finset.univ.filter fun i => b i ≠ 0).card = I.card := by
      congr 1
      ext i
      by_cases hi : i ∈ I
      · simp [b, hi, ha ⟨i, hi⟩]
      · simp [b, hi]
    have hrestrict (row : Fin r → Bool) :
        (∑ i : I, a i * realSigns row i) = ∑ i, b i * realSigns row i := by
      calc
        _ = ∑ i ∈ I, b i * realSigns row i := by
          rw [← Finset.sum_coe_sort I (fun i => b i * realSigns row i)]
          apply Finset.sum_congr rfl
          intro i _
          simp [b, i.2]
        _ = _ := Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [b, hi])
    calc
      _ = μ {row | ∑ i, b i * realSigns row i = 0} := by simp only [hsum, hrestrict]
      _ = zeroAtom b := by rw [zeroAtom, uniformOn_signCube_apply]; rfl
      _ ≤ 3 / 8 := zeroAtom_le_three_eighths r b (hcard.symm ▸ hI)
  rw [signLaw_apply, ← pi_uniformOn_univ]
  change Measure.pi (fun _ : Fin n => μ)
    {rows | ∃ a ∈ S, ∀ j, ∑ i : I, a i * realSigns (rows j) i = 0} ≤ _
  simpa only [hsum, Module.finrank_pi, Fintype.card_coe] using
    measure_exists_null_vector_le (μ := μ) (m := n) eval S hS hconc (by simpa using hn)

/-- A union bound for homogeneous sign relations with a given support size. -/
theorem signLaw_null_vector_support_card_le {n r s : ℕ} (hs : 3 ≤ s) (hn : s - 1 ≤ n) :
    signLaw n r {v | ∃ a : Fin r → ℝ, (Finset.univ.filter fun i => a i ≠ 0).card = s ∧
      ∀ j, ∑ i, a i * v i j = 0} ≤
      (r.choose s : ℝ≥0∞) * (n.choose (s - 1) : ℝ≥0∞) * (3 / 8 : ℝ≥0∞) ^ (n - (s - 1)) := by
  classical
  let supportSets := (Finset.univ : Finset (Fin r)).powersetCard s
  let E (I : Finset (Fin r)) : Set (Fin n → Fin r → ℝ) :=
    {rows | ∃ a : I → ℝ, (∀ i, a i ≠ 0) ∧ ∀ j, ∑ i : I, a i * rows j i = 0}
  let event : Set (Fin n → Fin r → ℝ) :=
    {rows | ∃ a : Fin r → ℝ, (Finset.univ.filter fun i => a i ≠ 0).card = s ∧
      ∀ j, ∑ i, a i * rows j i = 0}
  change signLaw n r ((fun v j i => v i j) ⁻¹' event) ≤ _
  rw [signLaw_transpose]
  calc
    signLaw r n event ≤ signLaw r n (⋃ I ∈ supportSets, E I) := by
      apply measure_mono
      rintro rows ⟨a, ha, hzero⟩
      let I := Finset.univ.filter fun i => a i ≠ 0
      have hmem (i : Fin r) : i ∈ I ↔ a i ≠ 0 := by simp [I]
      have hI : I ∈ supportSets := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ha⟩
      refine Set.mem_iUnion₂.mpr ⟨I, hI, fun i : I => a i, fun i => (hmem i).mp i.2, ?_⟩
      intro j
      change (∑ i : I, (fun i : Fin r => a i * rows j i) i.1) = 0
      rw [Finset.sum_coe_sort I (fun i => a i * rows j i), ← hzero j]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [not_not.mp (mt (hmem i).mpr hi), zero_mul]
    _ ≤ ∑ I ∈ supportSets, signLaw r n (E I) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _I ∈ supportSets,
        (n.choose (s - 1) : ℝ≥0∞) * (3 / 8 : ℝ≥0∞) ^ (n - (s - 1)) := by
      apply Finset.sum_le_sum
      intro I hI
      have hc := (Finset.mem_powersetCard.mp hI).2
      simpa only [E, hc] using signLaw_rows_fixed_support_le I (hc.symm ▸ hs) (hc.symm ▸ hn)
    _ = _ := by simp [supportSets, mul_assoc]

end BooleanThreshold
