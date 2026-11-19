module

public import BooleanThreshold.NonPair
public import BooleanThreshold.SignMeasure
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory Module

namespace BooleanThreshold

/-- The probability that a uniform sign row annihilates a coefficient vector. -/
noncomputable def zeroAtom {r : ℕ} (a : Fin r → ℝ) : ℝ≥0∞ :=
  uniformOn (signCube r) {x | ∑ i, a i * x i = 0}

/-- The common null vector bound applied to independent sign rows. -/
theorem signLaw_exists_null_vector_rows_le {n r : ℕ} (S : Set (Fin r → ℝ)) {q : ℝ≥0∞}
    (hS : ∀ a ∈ S, a ≠ 0) (hconc : ∀ a ∈ S, zeroAtom a ≤ q) (hr : r - 1 ≤ n) :
    signLaw r n {rows | ∃ a ∈ S, ∀ j, ∑ i, a i * rows j i = 0}
      ≤ (n.choose (r - 1) : ℝ≥0∞) * q ^ (n - (r - 1)) := by
  classical
  let μ : Measure (Fin r → Bool) := uniformOn Set.univ
  let eval (row : Fin r → Bool) : Module.Dual ℝ (Fin r → ℝ) :=
    dotProductBilin ℝ ℝ (realSigns row)
  have heval (row : Fin r → Bool) (a : Fin r → ℝ) :
      eval row a = ∑ i, a i * realSigns row i := by
    simp [eval, dotProduct, mul_comm]
  have hprob : μ.map (@realSigns r) = uniformOn (signCube r) := by
    rw [map_uniformOn_univ_eq_uniformOn_range (realSigns_injective r), range_realSigns]
  have hf : MeasurableEmbedding (@realSigns r) := ⟨realSigns_injective r,
    measurable_of_finite _, fun {_} _ => ((Set.toFinite _).image _).measurableSet⟩
  have hconc' (a : Fin r → ℝ) (ha : a ∈ S) : μ {row | eval row a = 0} ≤ q := by
    calc
      _ = μ {row | ∑ i, a i * realSigns row i = 0} := by simp only [heval]
      _ = zeroAtom a := by rw [zeroAtom, ← hprob, hf.map_apply]; rfl
      _ ≤ q := hconc a ha
  rw [signLaw_apply, ← pi_uniformOn_univ]
  change Measure.pi (fun _ : Fin n => μ)
    {rows | ∃ a ∈ S, ∀ j, ∑ i, a i * realSigns (rows j) i = 0} ≤ _
  simpa only [heval, Module.finrank_pi, Fintype.card_fin] using
    measure_exists_null_vector_le (μ := μ) (m := n) eval S hS hconc' (by simpa using hr)

/-- The common null vector bound for a matrix sampled as independent sign columns. -/
theorem signLaw_exists_null_vector_le {n r : ℕ} (S : Set (Fin r → ℝ)) {q : ℝ≥0∞}
    (hS : ∀ a ∈ S, a ≠ 0) (hconc : ∀ a ∈ S, zeroAtom a ≤ q) (hr : r - 1 ≤ n) :
    signLaw n r {v | ∃ a ∈ S, ∀ j, ∑ i, a i * v i j = 0}
      ≤ (n.choose (r - 1) : ℝ≥0∞) * q ^ (n - (r - 1)) := by
  let event : Set (Fin n → Fin r → ℝ) := {rows | ∃ a ∈ S, ∀ j, ∑ i, a i * rows j i = 0}
  change signLaw n r ((fun v j i => v i j) ⁻¹' event) ≤ _
  rw [signLaw_transpose]
  exact signLaw_exists_null_vector_rows_le S hS hconc hr

/-- The low-concentration contribution to the dependence estimate at the endpoint. -/
theorem signLaw_real_low_concentration_le {r : ℕ} (hr : 1 ≤ r) :
    (signLaw (r + 1) r).real
        {v | ∃ a : Fin r → ℝ, a ≠ 0 ∧ zeroAtom a ≤ (2 / 3 : ℝ≥0∞) ^ r ∧
          ∀ j, ∑ i, a i * v i j = 0}
      ≤ ((r + 1).choose 2 : ℝ) * (4 / 9 : ℝ) ^ r := by
  let S : Set (Fin r → ℝ) := {a | a ≠ 0 ∧ zeroAtom a ≤ (2 / 3 : ℝ≥0∞) ^ r}
  have h := signLaw_exists_null_vector_le (n := r + 1) S
    (fun a ha => ha.1) (fun a ha => ha.2) (by omega)
  have hi : r + 1 - (r - 1) = 2 := by omega
  have hc : (r + 1).choose (r - 1) = (r + 1).choose 2 := by
    rw [show r - 1 = r + 1 - 2 by omega, Nat.choose_symm (by omega : 2 ≤ r + 1)]
  rw [hi, hc] at h
  have hfin : (((r + 1).choose 2 : ℝ≥0∞) * ((2 / 3 : ℝ≥0∞) ^ r) ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp)
      (ENNReal.pow_ne_top (ENNReal.pow_ne_top (by simp [ENNReal.div_ne_top])))
  have hr' := ENNReal.toReal_mono hfin h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_div, ENNReal.toReal_ofNat] at hr'
  rw [← pow_mul, Nat.mul_comm, pow_mul] at hr'
  norm_num at hr'
  simpa only [measureReal_def, S, Set.mem_ofPred_eq, and_assoc] using hr'

end BooleanThreshold
