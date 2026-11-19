module

public import BooleanThreshold.SignMeasure
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

open scoped BigOperators

namespace BooleanThreshold

/-- Squared Euclidean norm of a vector specified by its coordinates. -/
def squaredNorm {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i ^ 2

/-- Matrix-vector multiplication for a matrix of signs encoded by Booleans. -/
noncomputable def signMatrixMap {m n : ℕ} (M : Fin m → Fin n → Bool) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  (Matrix.of fun j i => realSigns (M j) i).mulVecLin

theorem signMatrixMap_apply {m n : ℕ} (M : Fin m → Fin n → Bool) (a : Fin n → ℝ)
    (j : Fin m) : signMatrixMap M a j = ∑ i, a i * realSigns (M j) i := by
  simp [signMatrixMap, Matrix.mulVec, dotProduct, mul_comm]

/-- The upper operator norm bound with scaling `√m`. -/
def signOpBound {m n : ℕ} (K : ℝ) (M : Fin m → Fin n → Bool) : Prop :=
  ∀ a, squaredNorm (signMatrixMap M a) ≤ K ^ 2 * (m : ℝ) * squaredNorm a

theorem squaredNorm_signMatrixMap_le_of_null {m n : ℕ} {K : ℝ}
    {M : Fin m → Fin n → Bool} (hM : signOpBound K M)
    {a b : Fin n → ℝ} (ha : signMatrixMap M a = 0) :
    squaredNorm (signMatrixMap M b) ≤ K ^ 2 * (m : ℝ) * squaredNorm (b - a) := by
  simpa only [map_sub, ha, sub_zero] using hM (b - a)

theorem signMatrixMap_basis {m n : ℕ} (M : Fin m → Fin n → Bool) (i : Fin n) (j : Fin m) :
    signMatrixMap M (Pi.single i 1) j = realSigns (M j) i := by
  simp [signMatrixMap_apply, Pi.single_apply]

private theorem squaredNorm_signMatrixMap_basis {m n : ℕ} (M : Fin m → Fin n → Bool) (i : Fin n) :
    squaredNorm (signMatrixMap M (Pi.single i 1)) = m := by
  calc
    _ = ∑ _ : Fin m, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [signMatrixMap_basis]
      cases hj : M j i <;> norm_num [realSigns, hj]
    _ = _ := by simp

/-- In the operator norm event, a sign matrix with a nonempty row set has no
kernel vector close to a coordinate basis vector at radius below `1 / K`. -/
theorem no_near_basis_null_of_opBound {m n : ℕ} {K ε : ℝ}
    {M : Fin m → Fin n → Bool} (hm : 0 < m) (hM : signOpBound K M)
    (hε : K ^ 2 * ε ^ 2 < 1) (i : Fin n) {a : Fin n → ℝ}
    (ha : signMatrixMap M a = 0) :
    ¬ squaredNorm (Pi.single i 1 - a) ≤ ε ^ 2 := by
  intro hclose
  have h := squaredNorm_signMatrixMap_le_of_null hM (b := Pi.single i 1) ha
  rw [squaredNorm_signMatrixMap_basis] at h
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hle := mul_le_mul_of_nonneg_left hclose
    (mul_nonneg (sq_nonneg K) hm'.le)
  have hlt := mul_lt_mul_of_pos_right hε hm'
  nlinarith only [h, hle, hlt]

/-- A vector in the kernel near the difference of two basis vectors forces
the two corresponding columns to differ in only a small number of rows. -/
theorem column_diff_support_le_of_near_null {m n : ℕ} {K ε : ℝ}
    {M : Fin m → Fin n → Bool} (hM : signOpBound K M) (i j : Fin n) {a : Fin n → ℝ}
    (ha : signMatrixMap M a = 0)
    (hclose : squaredNorm (Pi.single i 1 - Pi.single j 1 - a) ≤ ε ^ 2) :
    4 * ((Finset.univ.filter fun k => M k i ≠ M k j).card : ℝ)
      ≤ K ^ 2 * (m : ℝ) * ε ^ 2 := by
  have hsq : squaredNorm (signMatrixMap M (Pi.single i 1 - Pi.single j 1)) =
      4 * ((Finset.univ.filter fun k => M k i ≠ M k j).card : ℝ) := by
    calc
      _ = ∑ k : Fin m, if M k i ≠ M k j then (4 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [map_sub, Pi.sub_apply, signMatrixMap_basis, signMatrixMap_basis]
        cases hi : M k i <;> cases hj : M k j <;> norm_num [realSigns, hi, hj]
      _ = ∑ k ∈ Finset.univ.filter (fun k => M k i ≠ M k j), (4 : ℝ) := by
        rw [Finset.sum_filter]
      _ = _ := by simp [mul_comm]
  rw [← hsq]
  apply (squaredNorm_signMatrixMap_le_of_null hM ha).trans
  exact mul_le_mul_of_nonneg_left hclose (mul_nonneg (sq_nonneg K) (Nat.cast_nonneg _))

/-- Coefficient vectors assigning equal coefficients to two selected columns. -/
def equalCoefficientSubspace {n : ℕ} (i j : Fin n) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker ((LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j)

/-- A kernel vector near a two-column difference places that difference in
the span of the remaining columns and the sum of the two selected columns. -/
theorem column_diff_mem_span_of_near_null {m n : ℕ} {ε : ℝ}
    {M : Fin m → Fin n → Bool} {i j : Fin n} (hij : i ≠ j)
    (hε : ε ^ 2 < 1) {a : Fin n → ℝ} (ha : signMatrixMap M a = 0)
    (hclose : squaredNorm (Pi.single i 1 - Pi.single j 1 - a) ≤ ε ^ 2) :
    signMatrixMap M (Pi.single i 1 - Pi.single j 1) ∈
      (equalCoefficientSubspace i j).map (signMatrixMap M) := by
  let d : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
  have hcoord (k : Fin n) : (d k - a k) ^ 2 < 1 := by
    exact (Finset.single_le_sum (f := fun l => (d l - a l) ^ 2)
      (fun l _ => sq_nonneg (d l - a l)) (Finset.mem_univ k)).trans_lt
      (hclose.trans_lt hε)
  have hi : 0 < a i := by
    have hi' : (1 - a i) ^ 2 < 1 := by
      simpa [d, Pi.sub_apply, Pi.single_apply, hij] using hcoord i
    nlinarith only [hi', sq_nonneg (a i)]
  have hj : a j < 0 := by
    have hj' : (-1 - a j) ^ 2 < 1 := by
      simpa [d, Pi.sub_apply, Pi.single_apply, Ne.symm hij] using hcoord j
    nlinarith only [hj', sq_nonneg (a j)]
  let t := (a i - a j) / 2
  let b := a - t • d
  have ht : t ≠ 0 := ne_of_gt (div_pos (sub_pos.mpr (hj.trans hi)) two_pos)
  have hb : b ∈ equalCoefficientSubspace i j := by
    rw [equalCoefficientSubspace, LinearMap.mem_ker]
    change b i - b j = 0
    simp [b, d, t, Pi.sub_apply, Pi.smul_apply, hij, Ne.symm hij, smul_eq_mul]
    ring
  have hmap : signMatrixMap M b = (-t) • signMatrixMap M d := by
    simp [b, ha]
  refine ⟨(-t)⁻¹ • b, (equalCoefficientSubspace i j).smul_mem _ hb, ?_⟩
  rw [map_smul, hmap, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr ht), one_smul]

end BooleanThreshold
