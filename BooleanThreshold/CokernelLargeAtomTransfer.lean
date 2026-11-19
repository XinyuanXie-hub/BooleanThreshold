module

public import BooleanThreshold.CokernelLargeFourier
public import BooleanThreshold.CokernelLargeTransfer
public import Mathlib.Data.Nat.Prime.Factorial

public section

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Pointwise

namespace BooleanThreshold

private theorem cast_zeroOneBit_binaryColumn {R : Type*} [Ring R] {N : ℕ}
    (x : Fin N → Bool) (i : Fin N) :
    (zeroOneBit (x i) : R) = binaryColumn R x i := by
  cases h : x i <;> simp [h, zeroOneBit, binaryColumn]

/-- A bounded integer description of a nonzero normal can be transferred
together with every equality between its binary evaluations at a maximal atom. -/
theorem transfer_binary_annihilation_and_concentration {p q N m V : ℕ}
    [Fact p.Prime] [Fact q.Prime] {J : Type*} [Fintype J]
    (hN : 1 ≤ N) (R : Fin m → Fin N → Bool)
    (T : Matrix (Fin N) J ℤ) (hT : ∀ i j, |T i j| ≤ (V : ℤ))
    (hminor : ∀ k ≤ Fintype.card J, (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (p : ℤ) ∧
      (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (q : ℤ))
    (y : J → ZMod p) {a : Fin N → ZMod p}
    (hy : (T.map (fun x : ℤ => (x : ZMod p))) *ᵥ y = a) (ha : a ≠ 0)
    (hpos : 0 < binaryConcentration a)
    (hnull : ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0) :
    ∃ b : Fin N → ZMod q, b ≠ 0 ∧ binaryConcentration a ≤ binaryConcentration b ∧
      ∀ i, b ⬝ᵥ binaryColumn (ZMod q) (R i) = 0 := by
  classical
  obtain ⟨z, hz⟩ := exists_binary_atom_eq_concentration a
  let S := {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z}
  have hmass : (uniformOn Set.univ).real S = binaryConcentration a := hz
  obtain ⟨x₀, hx₀⟩ : S.Nonempty := by
    by_contra! h
    rw [h, measureReal_empty] at hmass
    linarith
  let U : Matrix (Fin m ⊕ S) (Fin N) ℤ := Matrix.of fun i j =>
    Sum.elim (fun k => zeroOneBit (R k j))
      (fun x : S => zeroOneBit (x.val j) - zeroOneBit (x₀ j)) i
  have hU (i : Fin m ⊕ S) (j : Fin N) : |U i j| ≤ 1 := by
    cases i with
    | inl i => cases h : R i j <;> norm_num [U, h, zeroOneBit]
    | inr x => cases hx : x.val j <;> cases h₀ : x₀ j <;> norm_num [U, hx, h₀, zeroOneBit]
  have hUeval (r : ℕ) (v : Fin N → ZMod r) (i : Fin m ⊕ S) :
      ((U.map (fun x : ℤ => (x : ZMod r))) *ᵥ v) i =
        Sum.elim (fun k => v ⬝ᵥ binaryColumn (ZMod r) (R k))
          (fun x : S => v ⬝ᵥ binaryColumn (ZMod r) x.val -
            v ⬝ᵥ binaryColumn (ZMod r) x₀) i := by
    cases i with
    | inl i =>
      rw [Matrix.mulVec, dotProduct_comm]
      simp only [U, Matrix.map_apply, Matrix.of_apply, Sum.elim_inl]
      exact Finset.sum_congr rfl fun j _ =>
        congrArg (fun z : ZMod r => v j * z) (cast_zeroOneBit_binaryColumn (R i) j)
    | inr x =>
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, U, Matrix.of_apply, Sum.elim_inr,
        Int.cast_sub, cast_zeroOneBit_binaryColumn, sub_mul, Finset.sum_sub_distrib]
      congr 1 <;> exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hUnull : (U.map (fun x : ℤ => (x : ZMod p))) *ᵥ a = 0 := by
    ext i
    rw [hUeval]
    cases i with
    | inl i => exact hnull i
    | inr x =>
      change a ⬝ᵥ binaryColumn (ZMod p) x.val - a ⬝ᵥ binaryColumn (ZMod p) x₀ = 0
      rw [show a ⬝ᵥ binaryColumn (ZMod p) x.val = z from x.prop,
        show a ⬝ᵥ binaryColumn (ZMod p) x₀ = z from hx₀, sub_self]
  obtain ⟨v, hv, hUv⟩ := transfer_bounded_integer_normal hN U hU T hT hminor y
    (by rwa [hy]) (by rwa [hy])
  let b := (T.map (fun x : ℤ => (x : ZMod q))) *ᵥ v
  let z' := b ⬝ᵥ binaryColumn (ZMod q) x₀
  have hsubset : S ⊆ {x : Fin N → Bool | b ⬝ᵥ binaryColumn (ZMod q) x = z'} := by
    intro x hx
    have h := congrFun hUv (Sum.inr (⟨x, hx⟩ : S))
    rw [hUeval] at h
    exact sub_eq_zero.mp h
  exact ⟨b, hv, hmass ▸ (measureReal_mono hsubset).trans
    (binary_atom_le_concentration b z'), fun i => by
      have h := congrFun hUv (Sum.inl i)
      rwa [hUeval] at h⟩

/-- Clearing the common denominator in a bounded-height expansion yields
one integer coefficient matrix, with free coordinates for the exceptions. -/
theorem exists_integer_normal_matrix {p N L : ℕ} [Fact p.Prime]
    {A G : Finset (ZMod p)} {E : Finset (Fin N)} {a : Fin N → ZMod p} (hp : L < p)
    (hE : ∀ i ∉ E, a i ∈ A)
    (hG : ∀ x ∈ A, ∃ z : G → ℤ, (∀ g, |z g| ≤ (L.factorial : ℤ) * (L + 1)) ∧
      (∑ g : G, (z g : ZMod p) * g.val) = (L.factorial : ZMod p) * x) :
    ∃ T : Matrix (Fin N) (G ⊕ E) ℤ, (∀ i j, |T i j| ≤ (L.factorial : ℤ) * (L + 1)) ∧
      ∃ y : G ⊕ E → ZMod p, (T.map (fun x : ℤ => (x : ZMod p))) *ᵥ y = a := by
  classical
  have hrepr (i : Fin N) (hi : i ∉ E) := hG (a i) (hE i hi)
  choose z hz heval using hrepr
  let T : Matrix (Fin N) (G ⊕ E) ℤ := Matrix.of fun i j =>
    if hi : i ∈ E then Sum.elim (fun _ => 0) (fun e : E => if e.val = i then 1 else 0) j
    else Sum.elim (fun g => z i hi g) (fun _ => 0) j
  have hfac : (L.factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial]
    exact not_le_of_gt hp
  let y : G ⊕ E → ZMod p := Sum.elim (fun g : G => g.val / (L.factorial : ZMod p))
    (fun e : E => a e.val)
  refine ⟨T, fun i j => ?_, y, ?_⟩
  · have h₁ : (1 : ℤ) ≤ (L.factorial : ℤ) * (L + 1) := by
      have h := Nat.factorial_pos L
      have h' : (1 : ℤ) ≤ L.factorial := by exact_mod_cast h
      exact h'.trans (le_mul_of_one_le_right (by positivity) (by omega))
    by_cases hi : i ∈ E
    · cases j with
      | inl g => simp [T, hi]
      | inr e => by_cases he : e.val = i <;> simp [T, hi, he, h₁]
    · cases j with
      | inl g => simpa only [T, Matrix.of_apply, dite_eq_right hi, Sum.elim_inl] using hz i hi g
      | inr e => simp [T, hi]
  · funext i
    change (∑ j : G ⊕ E, (T i j : ZMod p) * y j) = a i
    rw [Fintype.sum_sum_type]
    by_cases hi : i ∈ E
    · have he (j : E) : j.val = i ↔ j = ⟨i, hi⟩ :=
        (Subtype.coe_inj : j.val = (⟨i, hi⟩ : E).val ↔ j = ⟨i, hi⟩)
      simp [T, hi, y, he, apply_ite]
    · simp only [T, Matrix.of_apply, dite_eq_right hi, Sum.elim_inl, Sum.elim_inr,
        y, Int.cast_zero, zero_mul, sum_const_zero, add_zero]
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div, heval i hi, mul_div_cancel_left₀ _ hfac]

end BooleanThreshold
