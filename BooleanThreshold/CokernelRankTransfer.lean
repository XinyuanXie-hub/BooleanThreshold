module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Rat.Cast.CharZero

public section

open Function Set Matrix Submodule

namespace BooleanThreshold

/-- A matrix over a field has a nonsingular minor of order equal to its rank. -/
theorem exists_rank_minor {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (A : Matrix m n K) :
    ∃ (rows : Fin A.rank ↪ m) (columns : Fin A.rank ↪ n),
      (A.submatrix rows columns).det ≠ 0 := by
  classical
  have hcols : ∃ f : Fin A.rank → m → K, (∀ i, f i ∈ range A.col) ∧ LinearIndependent K f := by
    rw [A.rank_eq_finrank_span_cols]
    obtain ⟨f, hf, _, hInd⟩ := Submodule.exists_fun_fin_finrank_span_eq K (range A.col)
    exact ⟨f, hf, hInd⟩
  obtain ⟨f, hf, hfInd⟩ := hcols
  choose columns hc using hf
  have hc_inj : Injective columns := fun i j h => hfInd.injective <| by rw [← hc i, ← hc j, h]
  let C : Matrix m (Fin A.rank) K := A.submatrix id columns
  have hcCol : C.col = f := funext fun i => hc i
  have hCrank : C.rank = A.rank := by
    rw [C.rank_eq_finrank_span_cols, hcCol, finrank_span_eq_card hfInd, Fintype.card_fin]
  have hCrank' : Module.finrank K (span K (range C.row)) = A.rank :=
    C.rank_eq_finrank_span_row.symm.trans hCrank
  obtain ⟨g, hg, _, hgInd⟩ := Submodule.exists_fun_fin_finrank_span_eq K (range C.row)
  let e := finCongr hCrank'.symm
  choose rows hr using (fun i => hg (e i))
  have hr_inj : Injective rows := fun i j h =>
    e.injective (hgInd.injective (by rw [← hr i, ← hr j, h]))
  refine ⟨⟨rows, hr_inj⟩, ⟨columns, hc_inj⟩, ?_⟩
  have hrows : (A.submatrix rows columns).row = g ∘ e := funext fun i => hr i
  change (A.submatrix rows columns).det ≠ 0
  rw [← Matrix.nonsingular_iff_det_ne_zero, ← Matrix.linearIndependent_row_iff, hrows]
  exact hgInd.comp e e.injective

/-- The pattern of which square minors vanish determines the rank. -/
theorem rank_eq_of_minor_nonzero_iff {m n K L : Type*} [Fintype m] [Fintype n] [Field K] [Field L]
    (A : Matrix m n K) (B : Matrix m n L)
    (h : ∀ (k : ℕ) (r : Fin k ↪ m) (c : Fin k ↪ n),
      (A.submatrix r c).det ≠ 0 ↔ (B.submatrix r c).det ≠ 0) :
    A.rank = B.rank := by
  apply le_antisymm
  · obtain ⟨r, c, hA⟩ := exists_rank_minor A
    have hB := (h _ r c).mp hA
    simpa only [rank_of_det_ne_zero hB, Fintype.card_fin] using B.rank_submatrix_le r c
  · obtain ⟨r, c, hB⟩ := exists_rank_minor B
    have hA := (h _ r c).mpr hB
    simpa only [rank_of_det_ne_zero hA, Fintype.card_fin] using A.rank_submatrix_le r c

/-- If the modulus is larger than the absolute values of all minors,
reducing modulo a prime preserves the rational rank. -/
theorem rank_zmod_eq_rat_of_minors_lt {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) {p : ℕ} [Fact p.Prime]
    (h : ∀ (k : ℕ) (r : Fin k ↪ m) (c : Fin k ↪ n), |(A.submatrix r c).det| < (p : ℤ)) :
    (A.map (fun x : ℤ => (x : ZMod p))).rank = (A.map (fun x : ℤ => (x : ℚ))).rank := by
  apply rank_eq_of_minor_nonzero_iff
  intro k r c
  let M := A.submatrix r c
  change (M.map (fun x : ℤ => (x : ZMod p))).det ≠ 0 ↔
    (M.map (fun x : ℤ => (x : ℚ))).det ≠ 0
  rw [← Int.cast_det, ← Int.cast_det, ne_eq, ne_eq,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_eq_zero]
  exact not_congr ⟨fun hp => Int.eq_zero_of_abs_lt_dvd hp (h k r c), fun hz => hz ▸ dvd_zero _⟩

/-- An entry bound gives a uniform bound on each square minor by expanding the determinant. -/
theorem abs_minor_le_factorial_mul_pow {m n : Type*} (A : Matrix m n ℤ) {M : ℤ}
    (h : ∀ i j, |A i j| ≤ M) {k : ℕ} (r : Fin k → m) (c : Fin k → n) :
    |(A.submatrix r c).det| ≤ (k.factorial : ℤ) * M ^ k := by
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using
    (Matrix.det_le (A := A.submatrix r c) (abv := AbsoluteValue.abs) (fun i j => h (r i) (c j)))


/-- Rank loss under a matrix product produces a nonzero vector in the
image of the right matrix which the left matrix kills. -/
theorem exists_mulVec_witness_of_rank_mul_lt {l m n K : Type*}
    [Fintype l] [Fintype m] [Fintype n] [Field K] (U : Matrix l m K) (T : Matrix m n K)
    (h : (U * T).rank < T.rank) :
    ∃ v : n → K, T *ᵥ v ≠ 0 ∧ U *ᵥ (T *ᵥ v) = 0 := by
  by_contra hw
  let f := T.mulVecLin
  let g := U.mulVecLin
  have hk : (g.comp f).ker = f.ker := by
    apply le_antisymm
    · intro v hv
      by_contra hv'
      exact hw ⟨v, hv', hv⟩
    · intro v hv
      change g (f v) = 0
      rw [LinearMap.mem_ker.mp hv, map_zero]
  have hf := f.finrank_range_add_finrank_ker
  have hgf := (g.comp f).finrank_range_add_finrank_ker
  rw [hk] at hgf
  rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul] at h
  change Module.finrank K (LinearMap.range (g.comp f)) < Module.finrank K (LinearMap.range f) at h
  omega

/-- Rank loss and its nonzero witness transfer between primes that exceed
the absolute values of the minors of both matrices. -/
theorem exists_mulVec_witness_at_second_prime {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n] (U : Matrix l m ℤ) (T : Matrix m n ℤ)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpT : ∀ (k : ℕ) (r : Fin k ↪ m) (c : Fin k ↪ n), |(T.submatrix r c).det| < (p : ℤ))
    (hqT : ∀ (k : ℕ) (r : Fin k ↪ m) (c : Fin k ↪ n), |(T.submatrix r c).det| < (q : ℤ))
    (hpUT : ∀ (k : ℕ) (r : Fin k ↪ l) (c : Fin k ↪ n), |((U * T).submatrix r c).det| < (p : ℤ))
    (hqUT : ∀ (k : ℕ) (r : Fin k ↪ l) (c : Fin k ↪ n), |((U * T).submatrix r c).det| < (q : ℤ))
    (h : ((U * T).map (fun x : ℤ => (x : ZMod p))).rank <
      (T.map (fun x : ℤ => (x : ZMod p))).rank) :
    ∃ v : n → ZMod q,
      (T.map (fun x : ℤ => (x : ZMod q))) *ᵥ v ≠ 0 ∧
      (U.map (fun x : ℤ => (x : ZMod q))) *ᵥ ((T.map (fun x : ℤ => (x : ZMod q))) *ᵥ v) = 0 := by
  rw [rank_zmod_eq_rat_of_minors_lt _ hpUT, rank_zmod_eq_rat_of_minors_lt _ hpT] at h
  have h' : ((U * T).map (Int.castRingHom (ZMod q))).rank <
      (T.map (Int.castRingHom (ZMod q))).rank := by
    change ((U * T).map (fun x : ℤ => (x : ZMod q))).rank <
      (T.map (fun x : ℤ => (x : ZMod q))).rank
    rwa [rank_zmod_eq_rat_of_minors_lt _ hqUT, rank_zmod_eq_rat_of_minors_lt _ hqT]
  rw [Matrix.map_mul] at h'
  exact exists_mulVec_witness_of_rank_mul_lt _ _ h'

/-- An entry bound for the product used in the prime transfer. -/
theorem abs_mul_entry_le {l m n : Type*} [Fintype m]
    (U : Matrix l m ℤ) (T : Matrix m n ℤ) {M : ℤ}
    (hU : ∀ i j, |U i j| ≤ 1) (hT : ∀ i j, |T i j| ≤ M) (i : l) (j : n) :
    |(U * T) i j| ≤ (Fintype.card m : ℤ) * M := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, |U i k * T k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : m, M := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [abs_mul, ← one_mul M]
      exact mul_le_mul (hU i k) (hT k j) (abs_nonneg _) (by decide)
    _ = _ := by simp

end BooleanThreshold
