module

public import BooleanThreshold.NonPairSign
public import BooleanThreshold.SignSymmetry

public section

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory

namespace BooleanThreshold

theorem zeroAtom_flipVector {r : ℕ} (mask : Fin r → Bool) (a : Fin r → ℝ) :
    zeroAtom (flipVector mask a) = zeroAtom a := by
  let A : Set (Fin r → ℝ) := {x | ∑ i, a i * x i = 0}
  have hpre : {x | ∑ i, flipVector mask a i * x i = 0} = flipVector mask ⁻¹' A := by
    ext x
    change (∑ i, flipVector mask a i * x i = 0) ↔ (∑ i, a i * flipVector mask x i = 0)
    have h := dot_flipVector_flipVector mask a (flipVector mask x)
    rw [flipVector_involutive mask x] at h
    rw [h]
  unfold zeroAtom
  rw [hpre, uniformOn_signCube_flipVector]

/-- The existence of a kernel vector with more than two nonzero coordinates
and an atom above a given cutoff is invariant under coordinated column flips. -/
theorem highConcentrationNull_flipColumns_iff {n r : ℕ} (cutoff : ℝ≥0∞) (mask : Fin r → Bool)
    (v : Fin n → Fin r → Bool) :
    (∃ a : Fin r → ℝ, 2 < (Finset.univ.filter fun j => a j ≠ 0).card ∧
      cutoff < zeroAtom a ∧ ∀ i, ∑ j, a j * realSigns (flipColumns mask v i) j = 0) ↔
    (∃ a : Fin r → ℝ, 2 < (Finset.univ.filter fun j => a j ≠ 0).card ∧
      cutoff < zeroAtom a ∧ ∀ i, ∑ j, a j * realSigns (v i) j = 0) := by
  classical
  let A : Set (Fin r → ℝ) := {a | 2 < (Finset.univ.filter fun j => a j ≠ 0).card ∧
    cutoff < zeroAtom a}
  simpa only [A, Set.mem_ofPred_eq, and_assoc] using
    exists_null_row_flipColumns_iff mask v A (fun a => by
      change (2 < (Finset.univ.filter fun j => flipVector mask a j ≠ 0).card ∧
        cutoff < zeroAtom (flipVector mask a)) ↔
        (2 < (Finset.univ.filter fun j => a j ≠ 0).card ∧ cutoff < zeroAtom a)
      simp [zeroAtom_flipVector])

end BooleanThreshold
