module

public import BooleanThreshold.KKSLargeShiftAtom

public section

open Filter Finset MeasureTheory ProbabilityTheory Module
open scoped ENNReal BigOperators Classical

namespace BooleanThreshold

/-- Row evaluation for a sign matrix translated by a fixed integer matrix. -/
@[expose] noncomputable def shiftedSignEval {n : ℕ} (D : Fin n → Fin n → ℤ)
    (i : Fin n) (x : Fin n → Bool) : Module.Dual ℝ (Fin n → ℝ) :=
  dotProductBilin ℝ ℝ (fun j => realSigns x j + (D i j : ℝ))

theorem shiftedSignEval_apply {n : ℕ} (D : Fin n → Fin n → ℤ)
    (i : Fin n) (x : Fin n → Bool) (a : Fin n → ℝ) :
    shiftedSignEval D i x a = ∑ j, a j * (realSigns x j + (D i j : ℝ)) := by
  simp [shiftedSignEval, dotProduct, mul_comm]

/-- The largest annihilation probability over the rows of a translated sign matrix. -/
@[expose] noncomputable def shiftedSignRowAtom {n : ℕ} (D : Fin n → Fin n → ℤ)
    (a : Fin n → ℝ) : ℝ≥0∞ :=
  univ.sup fun i => uniformOn Set.univ {x | shiftedSignEval D i x a = 0}

theorem shiftedSignRowAtom_ge {n : ℕ} (D : Fin n → Fin n → ℤ) (i : Fin n)
    (a : Fin n → ℝ) :
    uniformOn Set.univ {x | shiftedSignEval D i x a = 0} ≤ shiftedSignRowAtom D a :=
  le_sup (f := fun i => uniformOn Set.univ {x | shiftedSignEval D i x a = 0}) (mem_univ i)

theorem shiftedSignRowAtom_card_ratio {n : ℕ} (hn : 0 < n) (D : Fin n → Fin n → ℤ)
    (a : Fin n → ℝ) :
    ∃ j : ℕ, j ≤ 2 ^ n ∧ shiftedSignRowAtom D a = (j : ℝ≥0∞) / 2 ^ n := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup univ ⟨⟨0, hn⟩, mem_univ _⟩
    (fun i => uniformOn Set.univ {x | shiftedSignEval D i x a = 0})
  let E : Set (Fin n → Bool) := {x | shiftedSignEval D i x a = 0}
  refine ⟨E.ncard, ?_, ?_⟩
  · have h : E.ncard ≤ (Set.univ : Set (Fin n → Bool)).ncard := Set.ncard_le_ncard (by simp)
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h
  · change shiftedSignRowAtom D a = uniformOn Set.univ E at hi
    rw [hi, uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite E), ← Set.ncard_eq_toFinset_card]
    simp

private theorem shiftedSignRow_eq_target {n : ℕ} (D : Fin n → Fin n → ℤ)
    (i : Fin n) (a : Fin n → ℝ) :
    uniformOn Set.univ {x | shiftedSignEval D i x a = 0} =
      signAtomAt a (- ∑ j, a j * (D i j : ℝ)) := by
  unfold signAtomAt
  rw [uniformOn_signCube_apply]
  congr 1
  ext x
  change shiftedSignEval D i x a = 0 ↔ (∑ j, a j * realSigns x j) = - ∑ j, a j * (D i j : ℝ)
  rw [shiftedSignEval_apply, show (∑ j, a j * (realSigns x j + (D i j : ℝ))) =
    (∑ j, a j * realSigns x j) + ∑ j, a j * (D i j : ℝ) by simp [mul_add, sum_add_distrib]]
  exact add_eq_zero_iff_eq_neg

theorem shiftedSignRow_le_half {n : ℕ} (D : Fin n → Fin n → ℤ) (i : Fin n)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    uniformOn Set.univ {x | shiftedSignEval D i x a = 0} ≤ 1 / 2 := by
  rw [shiftedSignRow_eq_target]
  exact signAtomAt_le_half a ha _

theorem shiftedSignRowAtom_le_auxiliary {n : ℕ} (D : Fin n → Fin n → ℤ)
    (a : Fin n → ℤ) {μ τ : ℝ}
    (h : ∀ t : ℤ, signAtomAt (fun i => (a i : ℝ)) (t : ℝ) ≤ ENNReal.ofReal τ *
      auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ))) :
    shiftedSignRowAtom D (fun i => (a i : ℝ)) ≤ ENNReal.ofReal τ *
      auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ)) := by
  apply Finset.sup_le
  intro i _
  rw [shiftedSignRow_eq_target]
  convert h (-∑ j, a j * D i j) using 2
  push_cast
  rfl

/-- The probability of an annihilator whose row atoms are uniformly small. -/
theorem shiftedSignNull_low_le {n : ℕ} (hn : 0 < n) (D : Fin n → Fin n → ℤ)
    (q : ℝ≥0∞) :
    uniformOn Set.univ
        {X : Fin n → Fin n → Bool | ∃ a : Fin n → ℝ, a ≠ 0 ∧ shiftedSignRowAtom D a ≤ q ∧
          ∀ i, shiftedSignEval D i (X i) a = 0}
      ≤ (n : ℝ≥0∞) * q := by
  let ν : Measure (Fin n → Bool) := uniformOn Set.univ
  let S : Set (Fin n → ℝ) := {a | a ≠ 0 ∧ shiftedSignRowAtom D a ≤ q}
  have h := measure_exists_null_vector_rowwise_le (μ := ν) (shiftedSignEval D) S
    (fun a ha => ha.1) (fun i a ha => (shiftedSignRowAtom_ge D i a).trans ha.2)
    (by simp)
  rw [show Measure.pi (fun _ : Fin n => ν) = uniformOn Set.univ from pi_uniformOn_univ,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right,
    show n - (n - 1) = 1 by omega, pow_one] at h
  simpa only [S, Set.mem_ofPred_eq, and_assoc] using h

private noncomputable def extendCoefficients {n : ℕ} (I : Finset (Fin n)) :
    (I → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun a i := if hi : i ∈ I then a ⟨i, hi⟩ else 0
  map_add' := by
    intro a b
    funext i
    by_cases h : i ∈ I <;> simp [h]
  map_smul' := by
    intro c a
    funext i
    by_cases h : i ∈ I <;> simp [h]

private theorem extendCoefficients_restrict {n : ℕ} (I : Finset (Fin n))
    (a : Fin n → ℝ) (ha : ∀ i ∉ I, a i = 0) :
    extendCoefficients I (fun i => a i) = a := by
  funext i
  by_cases h : i ∈ I
  · simp [extendCoefficients, h]
  · simp [extendCoefficients, h, ha i h]

private theorem shiftedSignNull_fixedSupport_le {n : ℕ} (D : Fin n → Fin n → ℤ)
    (I : Finset (Fin n)) :
    uniformOn Set.univ
        {X : Fin n → Fin n → Bool | ∃ a : Fin n → ℝ, a ≠ 0 ∧ (∀ i ∉ I, a i = 0) ∧
          ∀ i, shiftedSignEval D i (X i) a = 0}
      ≤ (n.choose (I.card - 1) : ℝ≥0∞) * (1 / 2) ^ (n - (I.card - 1)) := by
  let ν : Measure (Fin n → Bool) := uniformOn Set.univ
  let eval (i : Fin n) (x : Fin n → Bool) := (shiftedSignEval D i x).comp (extendCoefficients I)
  let S : Set (I → ℝ) := {a | extendCoefficients I a ≠ 0}
  have h := measure_exists_null_vector_rowwise_le (μ := ν) eval S
    (fun a ha ha₀ => ha (ha₀.symm ▸ map_zero _))
    (fun i a ha => shiftedSignRow_le_half D i (extendCoefficients I a) ha)
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      exact (Nat.sub_le _ _).trans (by simpa using card_le_univ I))
  rw [show Measure.pi (fun _ : Fin n => ν) = uniformOn Set.univ from pi_uniformOn_univ,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  refine (measure_mono ?_).trans h
  rintro X ⟨a, ha, hs, hzero⟩
  have he := extendCoefficients_restrict I a hs
  refine ⟨fun i => a i, ?_, fun i => by simpa only [eval, LinearMap.comp_apply, he] using hzero i⟩
  change extendCoefficients I (fun i => a i) ≠ 0
  rwa [he]

/-- A union bound over the possible supports of a sparse annihilator. -/
theorem shiftedSignNull_smallSupport_le {n K : ℕ} (hK : K ≤ n) (D : Fin n → Fin n → ℤ) :
    uniformOn Set.univ
        {X : Fin n → Fin n → Bool | ∃ a : Fin n → ℝ,
          a ≠ 0 ∧ (univ.filter fun j => a j ≠ 0).card ≤ K ∧
          ∀ i, shiftedSignEval D i (X i) a = 0}
      ≤ (n.choose K : ℝ≥0∞) * (n.choose (K - 1) : ℝ≥0∞) * (1 / 2) ^ (n - (K - 1)) := by
  let choices := (univ : Finset (Fin n)).powersetCard K
  let E (I : Finset (Fin n)) : Set (Fin n → Fin n → Bool) :=
    {X | ∃ a : Fin n → ℝ, a ≠ 0 ∧ (∀ j ∉ I, a j = 0) ∧ ∀ i, shiftedSignEval D i (X i) a = 0}
  have hsubset : {X : Fin n → Fin n → Bool | ∃ a : Fin n → ℝ,
      a ≠ 0 ∧ (univ.filter fun j => a j ≠ 0).card ≤ K ∧
      ∀ i, shiftedSignEval D i (X i) a = 0} ⊆ ⋃ I ∈ choices, E I := by
    rintro X ⟨a, ha, hs, hzero⟩
    obtain ⟨I, hI, _, hcard⟩ := exists_subsuperset_card_eq (subset_univ _) hs (by simpa using hK)
    refine Set.mem_iUnion₂.mpr ⟨I, mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, a, ha, ?_, hzero⟩
    intro j hj
    by_contra hj'
    exact hj (hI (mem_filter.mpr ⟨mem_univ _, hj'⟩))
  calc
    _ ≤ uniformOn Set.univ (⋃ I ∈ choices, E I) := measure_mono hsubset
    _ ≤ ∑ I ∈ choices, uniformOn Set.univ (E I) := measure_biUnion_finset_le choices E
    _ ≤ ∑ _I ∈ choices, (n.choose (K - 1) : ℝ≥0∞) * (1 / 2) ^ (n - (K - 1)) := by
      apply sum_le_sum
      intro I hI
      rw [← (mem_powersetCard.mp hI).2]
      exact shiftedSignNull_fixedSupport_le D I
    _ = _ := by simp [choices, card_powersetCard, mul_assoc]

end BooleanThreshold
