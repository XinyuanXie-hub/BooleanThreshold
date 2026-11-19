module

public import BooleanThreshold.SpanNormalization
import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum

public section

open scoped Matrix
open Function Set Submodule Matrix

namespace BooleanThreshold

private theorem int_linearIndependent_iff_real {ι κ : Type*} [Finite κ]
    (v : ι → κ → ℤ) :
    LinearIndependent ℤ v ↔ LinearIndependent ℝ (fun i j => (v i j : ℝ)) := by
  exact linearIndependent_algebraMap_comp_iff.symm

/-- A real dependence of integer vectors admits integer coefficients whose
greatest common divisor is one, expressed as a Bézout identity. -/
theorem exists_primitive_int_relation {ι κ : Type*} [Fintype ι] [Finite κ]
    (A : Matrix κ ι ℤ) (h : ¬ LinearIndependent ℝ (fun i j => (A j i : ℝ))) :
    ∃ a : ι → ℤ, A *ᵥ a = 0 ∧ ∃ c : ι → ℤ, a ⬝ᵥ c = 1 := by
  classical
  have h' : ¬ LinearIndependent ℤ A.col := by
    exact fun hv => h ((int_linearIndependent_iff_real A.col).1 hv)
  obtain ⟨x, hx, i, hi⟩ := Fintype.not_linearIndependent_iff.1 h'
  let d := Finset.univ.gcd x
  have hd : d ≠ 0 := by
    intro hz
    exact hi ((Finset.gcd_eq_zero_iff.mp hz) i (Finset.mem_univ _))
  have hdvd (j : ι) : d ∣ x j := Finset.gcd_dvd (Finset.mem_univ _)
  choose a ha using hdvd
  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ x
  change d = _ at hc
  refine ⟨a, ?_, c, ?_⟩
  · funext j
    have hj := congrFun hx j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, col_apply,
      ha, mul_assoc, ← Finset.mul_sum] at hj
    have hj' := (mul_eq_zero.mp hj).resolve_left hd
    simpa only [mulVec, dotProduct, Pi.zero_apply, mul_comm] using hj'
  · apply mul_left_cancel₀ hd
    rw [mul_one, dotProduct, Finset.mul_sum]
    simpa only [ha, mul_assoc] using hc.symm

/-- The normalized binary matrix governing integer relations of sign columns. -/
@[expose] def normalizedBinaryMatrix {n r : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (r + 1)) Bool) : Matrix (Fin r) (Fin n) ℤ :=
  ((signMatrixCoordinates n r A).2.2.map zeroOneBit).transpose

/-- The finite cokernel condition forces independence of the original sign columns. -/
theorem linearIndependent_of_normalized_index_ne_zero {n r : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (r + 1)) Bool)
    (hindex : (LinearMap.range (normalizedBinaryMatrix A).mulVecLin).toAddSubgroup.index ≠ 0) :
    LinearIndependent ℝ (fun j i => (signedBit (A i j) : ℝ)) := by
  by_contra hdep
  obtain ⟨a, ha, c, hc⟩ := exists_primitive_int_relation (A.map signedBit) hdep
  have hdvd := dvd_index_of_primitive_sign_relation A a 0 (fun _ => true)
    (fun i => by
      have hi := congrFun ha i
      simpa [mulVec, dotProduct] using hi)
    ⟨c, 0, by simpa using hc⟩
  have heq := zero_dvd_iff.mp hdvd
  exact hindex (by exact_mod_cast heq)

/-- For an independent sign family, any sign in the real span has a primitive
integer relation with a nonzero coefficient on that sign. -/
theorem exists_primitive_sign_relation_of_mem_span {n r : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (r + 1)) Bool) (v : Fin (n + 1) → Bool)
    (hA : LinearIndependent ℝ (fun j i => (signedBit (A i j) : ℝ)))
    (hv : (fun i => (signedBit (v i) : ℝ)) ∈
      span ℝ (range (fun j i => (signedBit (A i j) : ℝ)))) :
    ∃ (a : Fin (r + 1) → ℤ) (b : ℤ), b ≠ 0 ∧
      (∀ i, (∑ j, signedBit (A i j) * a j) + b * signedBit (v i) = 0) ∧
      ∃ (c : Fin (r + 1) → ℤ) (d : ℤ), a ⬝ᵥ c + b * d = 1 := by
  let M : Matrix (Fin (n + 1)) (Fin (r + 2)) ℤ := fun i =>
    Fin.cons (signedBit (v i)) (fun j => signedBit (A i j))
  have hM : ¬ LinearIndependent ℝ (fun j i => (M i j : ℝ)) := by
    have heq : (fun j i => (M i j : ℝ)) =
        Fin.cons (fun i => (signedBit (v i) : ℝ)) (fun j i => (signedBit (A i j) : ℝ)) := by
      funext j i
      exact Fin.cases rfl (fun _ => rfl) j
    rw [heq, linearIndependent_finCons]
    exact fun h => h.2 hv
  obtain ⟨x, hx, c, hc⟩ := exists_primitive_int_relation M hM
  have hrel (i : Fin (n + 1)) : (∑ j : Fin (r + 1), signedBit (A i j) * x j.succ) +
      x 0 * signedBit (v i) = 0 := by
    have hi := congrFun hx i
    rw [mulVec, dotProduct, Fin.sum_univ_succ] at hi
    simpa only [M, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, add_comm, mul_comm (x 0)] using hi
  refine ⟨Fin.tail x, x 0, ?_, hrel, Fin.tail c, c 0, ?_⟩
  · intro hzero
    have hAi : LinearIndependent ℤ (fun j i => signedBit (A i j)) :=
      (int_linearIndependent_iff_real _).2 hA
    have hsum : (∑ j : Fin (r + 1), x j.succ • (fun i => signedBit (A i j))) = 0 := by
      funext i
      have hi := hrel i
      rw [hzero, zero_mul, add_zero] at hi
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using hi
    have hs := Fintype.linearIndependent_iff.1 hAi _ hsum
    rw [dotProduct, Fin.sum_univ_succ, hzero, zero_mul, zero_add] at hc
    simp [hs] at hc
  · rw [dotProduct, Fin.sum_univ_succ] at hc
    simpa only [dotProduct, Fin.tail, add_comm] using hc

end BooleanThreshold
