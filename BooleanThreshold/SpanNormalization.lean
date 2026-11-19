module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

open scoped Matrix
open Matrix

namespace BooleanThreshold

/-- Interpret a sign bit as an integer. -/
@[expose] def signedBit (b : Bool) : ℤ := if b then 1 else -1

/-- Encode a negative sign as one and a positive sign as zero. -/
@[expose] def zeroOneBit (b : Bool) : ℤ := if b then 0 else 1

theorem signedBit_eq_one_sub (b : Bool) : signedBit b = 1 - 2 * zeroOneBit b := by
  cases b <;> decide

@[simp] theorem signedBit_mul_self (b : Bool) : signedBit b * signedBit b = 1 := by
  cases b <;> decide

@[expose] def normalizeBit (x row col corner : Bool) : Bool :=
  !(x ^^ (row ^^ (col ^^ corner)))

@[simp] private theorem normalizeBit_twice (x row col corner : Bool) :
    normalizeBit (normalizeBit x row col corner) row col corner = x := by
  cases x <;> cases row <;> cases col <;> cases corner <;> rfl

private theorem signedBit_normalizeBit (x row col corner : Bool) :
    signedBit (normalizeBit x row col corner) =
      signedBit x * signedBit row * (signedBit col * signedBit corner) := by
  cases x <;> cases row <;> cases col <;> cases corner <;> decide

/-- A sign matrix is specified by its first column, the rest of its first
row, and its interior after making that first row and column positive. -/
@[expose] def signMatrixCoordinates (m n : ℕ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) Bool ≃
      (Fin (m + 1) → Bool) × (Fin n → Bool) × Matrix (Fin m) (Fin n) Bool where
  toFun A := (fun i => A i 0, fun j => A 0 j.succ, fun i j =>
    normalizeBit (A i.succ j.succ) (A i.succ 0) (A 0 j.succ) (A 0 0))
  invFun data := Fin.cases (Fin.cons (data.1 0) data.2.1) fun i =>
    Fin.cons (data.1 i.succ) fun j =>
      normalizeBit (data.2.2 i j) (data.1 i.succ) (data.2.1 j) (data.1 0)
  left_inv A := by
    funext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl
    · rfl
    · exact normalizeBit_twice _ _ _ _
  right_inv data := by
    obtain ⟨firstCol, firstRow, interior⟩ := data
    apply Prod.ext
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
    · apply Prod.ext
      · rfl
      · funext i j
        exact normalizeBit_twice _ _ _ _

theorem signedBit_signMatrixCoordinates {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) Bool) (i : Fin m) (j : Fin n) :
    signedBit ((signMatrixCoordinates m n A).2.2 i j) =
      signedBit (A i.succ j.succ) * signedBit (A i.succ 0) *
        (signedBit (A 0 j.succ) * signedBit (A 0 0)) :=
  signedBit_normalizeBit _ _ _ _

/-- Every event on the normalized interior has the same number of choices
of first-row and first-column signs. -/
theorem card_normalizedInterior_preimage (m n : ℕ)
    (s : Set (Matrix (Fin m) (Fin n) Bool)) :
    Nat.card {A // (signMatrixCoordinates m n A).2.2 ∈ s} =
      2 ^ (m + 1 + n) * Nat.card s := by
  let e := signMatrixCoordinates m n
  let e' : {A // (e A).2.2 ∈ s} ≃
      (Fin (m + 1) → Bool) × (Fin n → Bool) × s :=
    { toFun := fun A => ((e A).1, (e A).2.1, ⟨(e A).2.2, A.2⟩)
      invFun := fun b => ⟨e.symm (b.1, b.2.1, b.2.2), by simp⟩
      left_inv := by intro A; simp
      right_inv := by rintro ⟨col, row, val, hval⟩; simp }
  rw [Nat.card_congr e', Nat.card_prod, Nat.card_prod, ← mul_assoc]
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin]
  norm_num [Nat.card_eq_fintype_card, pow_add]

/-- A denominator in a primitive integer relation on the rows divides the
index of the column lattice. The index is zero for an infinite cokernel. -/
theorem dvd_index_of_primitive_row_relation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ ℤ) (a : ι → ℤ) (b : ℤ) (v : κ → ℤ)
    (h : a ᵥ* B = b • v)
    (hprim : ∃ (c : ι → ℤ) (d : ℤ), a ⬝ᵥ c + b * d = 1) :
    b ∣ ((LinearMap.range B.mulVecLin).toAddSubgroup.index : ℤ) := by
  classical
  let G := (LinearMap.range B.mulVecLin).toAddSubgroup
  let q : ℤ := G.index
  have hdvd (i : ι) : b ∣ a i * q := by
    obtain ⟨y, hy⟩ := show G.index • Pi.single i (1 : ℤ) ∈ LinearMap.range B.mulVecLin from
      G.nsmul_index_mem (Pi.single i 1)
    change B *ᵥ y = G.index • Pi.single i 1 at hy
    calc
      b ∣ (b • v) ⬝ᵥ y := by
        rw [smul_dotProduct, smul_eq_mul]
        exact dvd_mul_right _ _
      _ = a i * q := by
        rw [← h, ← dotProduct_mulVec, hy, ← Nat.cast_smul_eq_nsmul ℤ,
          dotProduct_smul, dotProduct_single_one, smul_eq_mul, mul_comm]
  obtain ⟨c, d, hcd⟩ := hprim
  calc
    b ∣ (∑ i, a i * q * c i) + b * (d * q) :=
      dvd_add (Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (hdvd i) _) (dvd_mul_right _ _)
    _ = (a ⬝ᵥ c + b * d) * q := by
      simp only [dotProduct, add_mul, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => by ring
      · ring
    _ = q := by rw [hcd, one_mul]


private theorem dvd_index_of_primitive_normalized_relation {n m : ℕ}
    (U : Matrix (Fin n) (Fin m) Bool) (a : Fin (m + 1) → ℤ) (b : ℤ)
    (v : Fin (n + 1) → Bool)
    (hfirst : (∑ j, a j) + b * signedBit (v 0) = 0)
    (hrest : ∀ i : Fin n, a 0 + (∑ j : Fin m, signedBit (U i j) * a j.succ) +
      b * signedBit (v i.succ) = 0)
    (hprim : ∃ (c : Fin (m + 1) → ℤ) (d : ℤ), a ⬝ᵥ c + b * d = 1) :
    b ∣ ((LinearMap.range ((U.map zeroOneBit).transpose).mulVecLin).toAddSubgroup.index : ℤ) := by
  rw [Fin.sum_univ_succ] at hfirst
  have ha : a 0 = -(∑ j : Fin m, a j.succ) - b * signedBit (v 0) := by omega
  refine dvd_index_of_primitive_row_relation _ (fun j : Fin m => a j.succ) b
    (fun i : Fin n => zeroOneBit (v 0) - zeroOneBit (v i.succ)) ?_ ?_
  · funext i
    have hi := hrest i
    simp only [signedBit_eq_one_sub, sub_mul, one_mul, mul_assoc,
      Finset.sum_sub_distrib, ← Finset.mul_sum, mul_sub] at hfirst hi
    change (∑ j : Fin m, a j.succ * zeroOneBit (U i j)) =
      b * (zeroOneBit (v 0) - zeroOneBit (v i.succ))
    simp only [mul_comm (a _)]
    linarith
  · obtain ⟨c, d, hcd⟩ := hprim
    refine ⟨fun j => c j.succ - c 0, d - signedBit (v 0) * c 0, ?_⟩
    calc
      _ = a ⬝ᵥ c + b * d := by
        simp only [dotProduct]
        rw [Fin.sum_univ_succ (fun j => a j * c j), ha]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = 1 := hcd

private theorem signedBit_not_xor (x y : Bool) :
    signedBit (!(x ^^ y)) = signedBit x * signedBit y := by
  cases x <;> cases y <;> decide

/-- The last coefficient in a primitive sign-vector relation divides the
cokernel order of the transposed, normalized zero-one interior. -/
theorem dvd_index_of_primitive_sign_relation {n m : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (m + 1)) Bool) (a : Fin (m + 1) → ℤ)
    (b : ℤ) (v : Fin (n + 1) → Bool)
    (h : ∀ i, (∑ j, signedBit (A i j) * a j) + b * signedBit (v i) = 0)
    (hprim : ∃ (c : Fin (m + 1) → ℤ) (d : ℤ), a ⬝ᵥ c + b * d = 1) :
    let B := (((signMatrixCoordinates n m A).2.2).map zeroOneBit).transpose
    b ∣ ((LinearMap.range B.mulVecLin).toAddSubgroup.index : ℤ) := by
  let col (j : Fin (m + 1)) := signedBit (A 0 j) * signedBit (A 0 0)
  let a' (j : Fin (m + 1)) := col j * a j
  let v' (i : Fin (n + 1)) := !(v i ^^ A i 0)
  have hcol (j : Fin (m + 1)) : col j * col j = 1 := by
    dsimp only [col]
    rw [mul_mul_mul_comm, signedBit_mul_self, signedBit_mul_self, one_mul]
  have hrow (i : Fin (n + 1)) :
      (∑ j, (signedBit (A i j) * signedBit (A i 0) * col j) * a' j) +
        b * signedBit (v' i) = 0 := by
    calc
      _ = signedBit (A i 0) * ((∑ j, signedBit (A i j) * a j) + b * signedBit (v i)) := by
        simp only [v', signedBit_not_xor, mul_add, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          calc
            _ = (signedBit (A i 0) * (signedBit (A i j) * a j)) * (col j * col j) := by
              dsimp only [a']
              ring
            _ = _ := by rw [hcol, mul_one]
        · ring
      _ = 0 := by rw [h i, mul_zero]
  refine dvd_index_of_primitive_normalized_relation (signMatrixCoordinates n m A).2.2 a' b v'
    ?_ ?_ ?_
  · simpa only [show ∀ j, signedBit (A 0 j) * signedBit (A 0 0) * col j = 1 from hcol,
      one_mul] using hrow 0
  · intro i
    have hi := hrow i.succ
    rw [Fin.sum_univ_succ] at hi
    simpa only [col, signedBit_mul_self, one_mul, ← signedBit_signMatrixCoordinates] using hi
  · obtain ⟨c, d, hcd⟩ := hprim
    refine ⟨fun j => col j * c j, d, ?_⟩
    convert hcd using 1
    simp only [dotProduct]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    calc
      _ = a j * c j * (col j * col j) := by
        dsimp only [a']
        ring
      _ = _ := by rw [hcol, mul_one]

end BooleanThreshold
