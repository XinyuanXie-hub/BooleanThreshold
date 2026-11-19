module

public import BooleanThreshold.NonPairConcentration
public import BooleanThreshold.SignAtomSymmetry
public import Mathlib.LinearAlgebra.Matrix.Dual

@[expose] public section

open scoped ENNReal BigOperators Classical
open MeasureTheory ProbabilityTheory Module

namespace BooleanThreshold

theorem exists_nonzero_scalar_of_common_null {r : ℕ}
    (rows : Fin r → Fin (r + 1) → ℝ) (hind : LinearIndependent ℝ rows)
    {a b : Fin (r + 1) → ℝ} (han : a ≠ 0) (hbn : b ≠ 0)
    (ha : ∀ j, ∑ i, a i * rows j i = 0) (hb : ∀ j, ∑ i, b i * rows j i = 0) :
    ∃ t : ℝ, t ≠ 0 ∧ b = t • a := by
  let V := Fin (r + 1) → ℝ
  let L : Fin r → Module.Dual ℝ V := fun j => dotProductEquiv ℝ _ (rows j)
  let W := Submodule.span ℝ (Set.range L)
  have hWdim : finrank ℝ W = r := by
    have hL : LinearIndependent ℝ L :=
      hind.map' _ (LinearMap.ker_eq_bot.mpr (dotProductEquiv ℝ (Fin (r + 1))).injective)
    simpa [W] using finrank_span_eq_card hL
  have hv (x : V) (hx : ∀ j, ∑ i, x i * rows j i = 0) : x ∈ W.dualCoannihilator := by
    apply (Submodule.mem_dualCoannihilator x).mpr
    intro l hl
    have hker : W ≤ LinearMap.ker (Module.Dual.eval ℝ V x) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      apply LinearMap.mem_ker.mpr
      change (∑ i, rows j i * x i) = 0
      simpa only [mul_comm] using hx j
    exact LinearMap.mem_ker.mp (hker hl)
  have hdim : r + finrank ℝ W.dualCoannihilator = r + 1 := by
    simpa [hWdim, V] using Subspace.finrank_add_finrank_dualCoannihilator_eq W
  have hspan : (ℝ ∙ a) = W.dualCoannihilator := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (hv a ha)
    · rw [finrank_span_singleton han]
      exact Nat.le_of_add_le_add_left hdim.le
  have hbmem := hv b hb
  rw [← hspan] at hbmem
  obtain ⟨t, heq⟩ := Submodule.mem_span_singleton.mp hbmem
  refine ⟨t, ?_, heq.symm⟩
  intro ht
  exact hbn (by simpa [ht] using heq.symm)

/-- Coefficients with support larger than two and a zero atom above the cutoff. -/
def isLargeAtomVector {r : ℕ} (cutoff : ℝ≥0∞) (a : Fin r → ℝ) : Prop :=
  2 < (Finset.univ.filter fun j => a j ≠ 0).card ∧ cutoff < zeroAtom a

theorem isLargeAtomVector.ne_zero {r : ℕ} {cutoff : ℝ≥0∞} {a : Fin r → ℝ}
    (h : isLargeAtomVector cutoff a) : a ≠ 0 := by
  rintro rfl
  simp [isLargeAtomVector] at h

private theorem isLargeAtomVector_smul_iff {r : ℕ} {cutoff : ℝ≥0∞}
    (a : Fin r → ℝ) {t : ℝ} (ht : t ≠ 0) :
    isLargeAtomVector cutoff (t • a) ↔ isLargeAtomVector cutoff a := by
  have hz : zeroAtom (t • a) = zeroAtom a := by
    unfold zeroAtom
    congr 1
    ext x
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ht]
  simp [isLargeAtomVector, hz, Pi.smul_apply, smul_eq_mul, ht]

/-- The high-concentration event for a square matrix whose rows other than `i`
are linearly independent. -/
def independentRowsLargeAtomEvent {r : ℕ} (cutoff : ℝ≥0∞) (i : Fin (r + 1)) :
    Set (Fin (r + 1) → Fin (r + 1) → Bool) :=
  {v | LinearIndependent ℝ (fun j => realSigns (Fin.removeNth i v j)) ∧
    ∃ a, isLargeAtomVector cutoff a ∧ ∀ j, ∑ k, a k * realSigns (v j) k = 0}

theorem independentRowsLargeAtomEvent_flipInvariant {r : ℕ} (cutoff : ℝ≥0∞)
    (i : Fin (r + 1)) (mask : Fin (r + 1) → Bool) (v : Fin (r + 1) → Fin (r + 1) → Bool) :
    flipColumns mask v ∈ independentRowsLargeAtomEvent cutoff i ↔
      v ∈ independentRowsLargeAtomEvent cutoff i := by
  change (_ ∧ _) ↔ (_ ∧ _)
  refine and_congr (linearIndependent_realSigns_flipColumns_iff mask (Fin.removeNth i v)) ?_
  simpa only [isLargeAtomVector, and_assoc] using
    highConcentrationNull_flipColumns_iff cutoff mask v

private theorem mem_independentRowsLargeAtomEvent_insertNth_iff {r : ℕ}
    (cutoff : ℝ≥0∞) (i : Fin (r + 1)) (rows : Fin r → Fin (r + 1) → Bool)
    (row : Fin (r + 1) → Bool) {a : Fin (r + 1) → ℝ} (han : a ≠ 0)
    (ha : ∀ j, ∑ k, a k * realSigns (rows j) k = 0) :
    Fin.insertNth i row rows ∈ independentRowsLargeAtomEvent cutoff i ↔
      LinearIndependent ℝ (fun j => realSigns (rows j)) ∧
        isLargeAtomVector cutoff a ∧ ∑ k, a k * realSigns row k = 0 := by
  constructor
  · rintro ⟨hind, b, hb, hzero⟩
    have hind' : LinearIndependent ℝ (fun j => realSigns (rows j)) := by simpa using hind
    have hrows (j : Fin r) : ∑ k, b k * realSigns (rows j) k = 0 := by
      simpa using hzero (i.succAbove j)
    obtain ⟨t, ht, rfl⟩ := exists_nonzero_scalar_of_common_null _ hind' han hb.ne_zero ha hrows
    refine ⟨hind', (isLargeAtomVector_smul_iff _ ht).mp hb, ?_⟩
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ht] using hzero i
  · rintro ⟨hind, hlarge, hzero⟩
    refine ⟨by simpa using hind, a, hlarge, ?_⟩
    exact i.forall_iff_succAbove.mpr ⟨by simpa using hzero, fun j => by simpa using ha j⟩

/-- The conditional concentration estimate bounds the square high-atom event when
the remaining rows are independent. The comparison assumption is the
anti-concentration estimate for a normal chosen using only those remaining rows. -/
theorem independentRowsLargeAtom_probability_le {r : ℕ} (cutoff : ℝ≥0∞) (i : Fin (r + 1))
    (normal : (Fin r → Fin (r + 1) → Bool) → Fin (r + 1) → ℝ)
    (hnz : ∀ A, normal A ≠ 0)
    (horth : ∀ A j, ∑ k, normal A k * realSigns (A j) k = 0)
    (structured : Set (Fin (r + 1) → ℝ))
    (exceptional : Set (Fin r → Fin (r + 1) → Bool))
    (window : Set (Fin (r + 1) → Bool))
    {θ : ℝ≥0∞} (hθ : θ ≤ 1 / 2) (hW : 1 / 2 ≤ uniformOn Set.univ window)
    (hcomparison : ∀ A ∉ exceptional, normal A ∉ structured →
      uniformOn Set.univ {b | (∑ k, normal A k * realSigns b k = 0) ∧ b ∈ window} ≤
        θ * uniformOn Set.univ window * cutoff) :
    (uniformOn Set.univ).real (independentRowsLargeAtomEvent cutoff i) ≤
      2 * (uniformOn Set.univ).real exceptional +
      4 * (uniformOn Set.univ).real {v |
        v ∈ independentRowsLargeAtomEvent cutoff i ∧
        ∃ a ∈ structured, isLargeAtomVector cutoff a ∧
          ∀ j, ∑ k, a k * realSigns (v j) k = 0} := by
  let ν : Measure (Fin (r + 1) → Bool) := uniformOn Set.univ
  let event := independentRowsLargeAtomEvent cutoff i
  let structuredRows : Set (Fin r → Fin (r + 1) → Bool) := normal ⁻¹' structured
  have hprob (a : Fin (r + 1) → ℝ) :
      ν {b | ∑ k, a k * realSigns b k = 0} = zeroAtom a := by
    exact (realSigns_measurePreserving (r + 1)).measure_preimage_emb
      (realSigns_measurableEmbedding (r + 1))
      {x : Fin (r + 1) → ℝ | ∑ k, a k * x k = 0}
  have hcomp (A : Fin r → Fin (r + 1) → Bool) (hE : A ∉ exceptional)
      (hS : A ∉ structuredRows) :
      ν {b | Fin.insertNth i b A ∈ event ∧ b ∈ window} ≤
        θ * ν window * ν {b | Fin.insertNth i b A ∈ event} := by
    have hfiber (b : Fin (r + 1) → Bool) := mem_independentRowsLargeAtomEvent_insertNth_iff
      cutoff i A b (hnz A) (horth A)
    by_cases hgood : LinearIndependent ℝ (fun j => realSigns (A j)) ∧
        isLargeAtomVector cutoff (normal A)
    · have heq : {b | Fin.insertNth i b A ∈ event} = {b | ∑ k, normal A k * realSigns b k = 0} := by
        ext b
        simpa only [event, Set.mem_ofPred_eq, hgood.1, hgood.2, true_and] using hfiber b
      have heqW : {b | Fin.insertNth i b A ∈ event ∧ b ∈ window} =
          {b | (∑ k, normal A k * realSigns b k = 0) ∧ b ∈ window} := by
        ext b
        exact and_congr (Set.ext_iff.mp heq b) Iff.rfl
      rw [heqW, heq, hprob]
      exact (hcomparison A hE hS).trans (mul_le_mul_of_nonneg_left hgood.2.2.le zero_le)
    · have hempty : {b | Fin.insertNth i b A ∈ event ∧ b ∈ window} = ∅ := by
        ext b
        refine iff_false_intro fun hb => hgood ?_
        have h := (hfiber b).mp hb.1
        exact ⟨h.1, h.2.1⟩
      rw [hempty, measure_empty]
      exact zero_le
  have h := uniform_probability_le_exceptional_structured i event exceptional structuredRows window
    hθ hW (independentRowsLargeAtomEvent_flipInvariant cutoff i) hcomp
  refine h.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  rw [measureReal_def, measureReal_def]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro v hv
  obtain ⟨hJ, hS⟩ := hv
  let A := Fin.removeNth i v
  have hEq : Fin.insertNth i (v i) A = v := by
    simp [A]
  have hJ' : Fin.insertNth i (v i) A ∈ event := by rwa [hEq]
  have h := (mem_independentRowsLargeAtomEvent_insertNth_iff cutoff i A (v i)
    (hnz A) (horth A)).mp hJ'
  refine ⟨hJ, normal A, hS, h.2.1, ?_⟩
  exact i.forall_iff_succAbove.mpr ⟨h.2.2, horth A⟩

end BooleanThreshold
