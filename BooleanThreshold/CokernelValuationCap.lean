module

public import BooleanThreshold.CokernelModulo
public import BooleanThreshold.CokernelRankTransfer
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

public section

open Matrix

namespace BooleanThreshold

/-- A finite integral cokernel forces full row rank over the rationals. -/
theorem rank_rat_eq_height_of_index_ne_zero {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (hidx : (LinearMap.range A.mulVecLin).toAddSubgroup.index ≠ 0) :
    (A.map (Int.castRingHom ℚ)).rank = n := by
  classical
  let H := (LinearMap.range A.mulVecLin).toAddSubgroup
  let f := Int.castRingHom ℚ
  have hpreimage (j : Fin n) :
      ∃ v : Fin m → ℤ, A *ᵥ v = H.index • Pi.single j (1 : ℤ) :=
    H.nsmul_index_mem (Pi.single j 1)
  choose v hv using hpreimage
  let C : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => v j i
  have hprod : A * C = (H.index : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    ext i j
    have h := congrFun (hv j) i
    simp only [mulVec, dotProduct, Pi.single_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply] at h
    simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, C, eq_comm] using h
  have hprodQ : (A.map f) * (C.map f) = (H.index : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    rw [← Matrix.map_mul, hprod]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, f, Int.coe_castRingHom]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hlo := Matrix.rank_mul_le_left (A.map f) (C.map f)
  have hnz : (H.index : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hidx
  rw [hprodQ, Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hnz),
    Matrix.rank_one, Fintype.card_fin] at hlo
  have hhi := (A.map f).rank_le_card_height
  rw [Fintype.card_fin] at hhi
  exact le_antisymm hhi hlo

/-- The cokernel index of an integral square matrix equals the absolute determinant. -/
theorem square_matrix_index_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (LinearMap.range A.mulVecLin).toAddSubgroup.index = A.det.natAbs := by
  by_cases hdet : A.det = 0
  · rw [hdet, Int.natAbs_zero]
    by_contra! hidx
    let B := A.map (Int.castRingHom ℚ)
    have hrank : B.rank = Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      exact rank_rat_eq_height_of_index_ne_zero A hidx
    have hsurj : Function.Surjective B.mulVecLin :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr hrank
    have hdetQ : LinearMap.det B.mulVecLin = 0 := by
      rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
      change (A.map fun (x : ℤ) => (x : ℚ)).det = 0
      rw [← Int.cast_det, hdet, Int.cast_zero]
    exact (LinearMap.range_lt_top_of_det_eq_zero hdetQ).ne
      (LinearMap.range_eq_top.mpr hsurj)
  · let T := LinearMap.range A.mulVecLin
    let e := (LinearEquiv.ofInjective A.mulVecLin
      (Matrix.mulVec_injective_of_det_ne_zero hdet)).toAddEquiv
    have he : T.subtype ∘ₗ (e : (Fin n → ℤ) →+ T).toIntLinearMap = A.mulVecLin := by
      ext x i
      rfl
    have h := Submodule.natAbs_det_equiv T e
    rw [he, ← Matrix.toLin'_apply', LinearMap.det_toLin'] at h
    exact h.symm

/-- A finite integral cokernel of a matrix with entries of absolute value at
most one has index bounded by a factorial. -/
theorem matrix_index_le_factorial {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    (LinearMap.range A.mulVecLin).toAddSubgroup.index ≤ n.factorial := by
  classical
  let H := (LinearMap.range A.mulVecLin).toAddSubgroup
  change H.index ≤ _
  by_cases hidx : H.index = 0
  · simp [hidx]
  let f := Int.castRingHom ℚ
  let F := A.map f
  have hrank : F.rank = n := rank_rat_eq_height_of_index_ne_zero A hidx
  have hminor := exists_rank_minor F
  rw [hrank] at hminor
  obtain ⟨r, j, hminor⟩ := hminor
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective r
    ⟨r.injective, Finite.surjective_of_injective r.injective⟩
  have hperm : F.submatrix r j = (F.submatrix id j).submatrix σ id := rfl
  rw [hperm, Matrix.det_permute] at hminor
  have hdetQ : (F.submatrix id j).det ≠ 0 := fun h => hminor (by simp [h])
  let D : Matrix (Fin n) (Fin n) ℤ := A.submatrix id j
  have hdetQ' : ((D.det : ℤ) : ℚ) ≠ 0 := by
    rw [Int.cast_det]
    exact hdetQ
  have hdet : D.det ≠ 0 := Int.cast_ne_zero.mp hdetQ'
  let C : Matrix (Fin m) (Fin n) ℤ := (1 : Matrix (Fin m) (Fin m) ℤ).submatrix id j
  have hC : A * C = D := by
    simpa only [C, D, Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] using
      Matrix.mul_submatrix_one (Equiv.refl (Fin m)) j A
  have hD : (LinearMap.range D.mulVecLin).toAddSubgroup ≤ H := by
    rintro _ ⟨x, rfl⟩
    refine ⟨C *ᵥ x, ?_⟩
    change A *ᵥ (C *ᵥ x) = D *ᵥ x
    rw [Matrix.mulVec_mulVec, hC]
  have hdvd := AddSubgroup.index_dvd_of_le hD
  rw [square_matrix_index_eq_det] at hdvd
  have hpos : 0 < D.det.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hdet)
  have hbound : D.det.natAbs ≤ n.factorial := by
    have h := abs_minor_le_factorial_mul_pow A hA id j
    rw [one_pow, mul_one, ← Int.natCast_natAbs] at h
    exact_mod_cast h
  exact (Nat.le_of_dvd hpos hdvd).trans hbound

/-- The binary cokernel index is bounded by the factorial of the number of rows. -/
theorem binaryCokernelIndex_le_factorial {N : ℕ} (B : Fin N → Fin (N + 1) → Bool) :
    binaryCokernelIndex B ≤ N.factorial := by
  apply matrix_index_le_factorial
  intro i j
  change |zeroOneBit (B i j)| ≤ 1
  cases B i j <;> norm_num [zeroOneBit]

private theorem two_pow_binaryCokernelIndex_factorization_le {N p : ℕ} (hp : p.Prime)
    (B : Fin N → Fin (N + 1) → Bool) :
    2 ^ (binaryCokernelIndex B).factorization p ≤ N.factorial := by
  let q := binaryCokernelIndex B
  change 2 ^ q.factorization p ≤ N.factorial
  by_cases hq : q = 0
  · simp only [hq, Nat.factorization_zero, Finsupp.zero_apply, pow_zero]
    exact Nat.factorial_pos N
  calc
    2 ^ q.factorization p ≤ p ^ q.factorization p := Nat.pow_le_pow_left hp.two_le _
    _ ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.ordProj_dvd q p)
    _ ≤ N.factorial := binaryCokernelIndex_le_factorial B

/-- Every prime valuation of the binary cokernel index is at most the
base-two logarithm of the factorial of its number of rows. -/
theorem binaryCokernelIndex_factorization_le_log_factorial {N p : ℕ} (hp : p.Prime)
    (B : Fin N → Fin (N + 1) → Bool) :
    (binaryCokernelIndex B).factorization p ≤ Nat.log 2 N.factorial :=
  Nat.le_log_of_pow_le (by decide) (two_pow_binaryCokernelIndex_factorization_le hp B)

/-- A polynomial cutoff for every prime valuation of the binary cokernel index. -/
theorem binaryCokernelIndex_factorization_le {N p : ℕ} (hp : p.Prime)
    (B : Fin N → Fin (N + 1) → Bool) :
    (binaryCokernelIndex B).factorization p ≤ N ^ 3 := by
  apply (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp
  calc
    _ ≤ N.factorial := two_pow_binaryCokernelIndex_factorization_le hp B
    _ ≤ N ^ N := Nat.factorial_le_pow N
    _ ≤ (2 ^ N) ^ N := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (N ^ 2) := by rw [← pow_mul, pow_two]
    _ ≤ 2 ^ (N ^ 3) := by
      apply (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mpr
      by_cases hn : N = 0
      · simp [hn]
      · exact pow_le_pow_right₀ (Nat.pos_of_ne_zero hn) (by decide)

/-- Deleting the first row of a square integral matrix gives an image whose
index divides the absolute determinant of the square matrix. -/
theorem tail_matrix_index_dvd_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    (LinearMap.range (A.submatrix Fin.succ id).mulVecLin).toAddSubgroup.index ∣
      A.det.natAbs := by
  let f : (Fin (n + 1) → ℤ) →+ (Fin n → ℤ) :=
    { toFun := Fin.tail
      map_zero' := rfl
      map_add' := by
        intros
        rfl }
  have hf : Function.Surjective f := by
    intro v
    refine ⟨Fin.cons 0 v, ?_⟩
    change @Fin.tail n (fun _ => ℤ) (@Fin.cons n (fun _ => ℤ) 0 v) = v
    exact @Fin.tail_cons n (fun _ => ℤ) 0 v
  let H := (LinearMap.range A.mulVecLin).toAddSubgroup
  have hmap : H.map f =
      (LinearMap.range (A.submatrix Fin.succ id).mulVecLin).toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨A *ᵥ z, ⟨z, rfl⟩, rfl⟩
  rw [← hmap, ← square_matrix_index_eq_det]
  exact H.index_map_dvd hf

/-- The rectangular binary cokernel index divides the determinant of any
square binary extension obtained by prepending one row. -/
theorem binaryCokernelIndex_tail_dvd_det {N : ℕ} (A : Fin (N + 1) → Fin (N + 1) → Bool) :
    binaryCokernelIndex (Fin.tail A) ∣ ((Matrix.of A).map zeroOneBit).det.natAbs :=
  tail_matrix_index_dvd_det ((Matrix.of A).map zeroOneBit)

end BooleanThreshold
