module

public import BooleanThreshold.CokernelBounds
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Order.Interval.Finset.Nat

public section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- The index of the integral image divides a power of the determinant of
any square right product. -/
theorem matrix_index_dvd_det_mul_pow {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (C : Matrix (Fin m) (Fin n) ℤ) :
    (LinearMap.range A.mulVecLin).toAddSubgroup.index ∣ (A * C).det.natAbs ^ n := by
  let H := (LinearMap.range A.mulVecLin).toAddSubgroup
  let D := A * C
  have hmem (x : Fin n → ℤ) : D.det • x ∈ H := by
    refine ⟨C *ᵥ (D.adjugate *ᵥ x), ?_⟩
    change A *ᵥ (C *ᵥ (D.adjugate *ᵥ x)) = D.det • x
    rw [mulVec_mulVec, ← show D = A * C from rfl, mulVec_mulVec, mul_adjugate,
      smul_mulVec, one_mulVec]
  have hsub : (nsmulAddMonoidHom (α := Fin n → ℤ) D.det.natAbs).range ≤ H := by
    rintro _ ⟨x, rfl⟩
    change D.det.natAbs • x ∈ H
    rw [← Nat.cast_smul_eq_nsmul ℤ, Int.natCast_natAbs]
    by_cases hd : 0 ≤ D.det
    · simpa only [abs_of_nonneg hd] using hmem x
    · rw [abs_of_neg (lt_of_not_ge hd), neg_smul]
      exact H.neg_mem (hmem x)
  have hind := AddSubgroup.index_dvd_of_le hsub
  rwa [AddSubgroup.index_range_nsmul, Module.finrank_pi, Fintype.card_fin] at hind

/-- An integral matrix has a cokernel whose index is divisible by `p` exactly
when its reduction modulo `p` fails to have full row rank. -/
theorem prime_dvd_index_iff_not_surjective_mod {m n p : ℕ} (hp : p.Prime)
    (A : Matrix (Fin n) (Fin m) ℤ) :
    p ∣ (LinearMap.range A.mulVecLin).toAddSubgroup.index ↔
      ¬ Function.Surjective ((A.map (Int.castRingHom (ZMod p))).mulVecLin) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let f := Int.castRingHom (ZMod p)
  let H := (LinearMap.range A.mulVecLin).toAddSubgroup
  change p ∣ H.index ↔ ¬ Function.Surjective (A.map f).mulVecLin
  constructor
  · intro hdiv hs
    choose v hv using fun j : Fin n => hs (Pi.single j 1)
    let C : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => ((v j i).val : ℤ)
    let D := A * C
    have hC : C.map f = Matrix.of (fun i j => v j i) := by
      ext i j
      simpa only [C, Matrix.map_apply, Matrix.of_apply, f, Int.coe_castRingHom, Int.cast_natCast]
        using ZMod.natCast_zmod_val (v j i)
    have hD : D.map f = 1 := by
      dsimp [D]
      rw [Matrix.map_mul, hC]
      ext i j
      have hij := congrFun (hv j) i
      simpa only [mulVecLin_apply, mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, Pi.single_apply, eq_comm] using hij
    have hdet : f D.det = 1 := by
      rw [f.map_det]
      change (D.map f).det = 1
      rw [hD, Matrix.det_one]
    have hndiv : ¬ p ∣ D.det.natAbs := by
      intro hd
      have hz : (p : ℤ) ∣ D.det := Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 hd)
      have hf0 : f D.det = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hz
      exact one_ne_zero (hdet.symm.trans hf0)
    exact hndiv (hp.dvd_of_dvd_pow (hdiv.trans (matrix_index_dvd_det_mul_pow A C)))
  · intro hs
    let T := LinearMap.range (A.map f).mulVecLin
    have hT : T < ⊤ := lt_top_iff_ne_top.mpr (fun h => hs (LinearMap.range_eq_top.mp h))
    obtain ⟨ψ, hψ, hψT⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hT inferInstance
    let red : (Fin n → ℤ) →+ (Fin n → ZMod p) :=
      { toFun := fun x i => f (x i)
        map_zero' := by ext i; simp
        map_add' := by intro x y; ext i; simp }
    have hred : Function.Surjective red := by
      intro x
      refine ⟨fun i => ((x i).val : ℤ), ?_⟩
      funext i
      change (((x i).val : ℤ) : ZMod p) = x i
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    let g := ψ.toAddMonoidHom.comp red
    have hψsurj : Function.Surjective ψ :=
      LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hψ)
    have hg : Function.Surjective g := hψsurj.comp hred
    have hindex : g.ker.index = p := by
      rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hg]
      simp
    have hsub : H ≤ g.ker := by
      rintro _ ⟨x, rfl⟩
      have hmap : red (A *ᵥ x) = A.map f *ᵥ (f ∘ x) :=
        funext (f.map_mulVec A x)
      change ψ (red (A *ᵥ x)) = 0
      rw [hmap]
      have hm : ψ (A.map f *ᵥ (f ∘ x)) ∈ T.map ψ :=
        Submodule.mem_map.mpr ⟨_, ⟨f ∘ x, rfl⟩, rfl⟩
      rwa [hψT, Submodule.mem_bot] at hm
    exact hindex ▸ AddSubgroup.index_dvd_of_le hsub

private theorem sum_Ioc_inv_sq_le (a b : ℕ) (ha : 0 < a) :
    ∑ p ∈ Finset.Ioc a b, 1 / (p : ℝ) ^ 2 ≤ 1 / (a : ℝ) := by
  classical
  have htail (b : ℕ) (hab : a ≤ b) :
      ∑ p ∈ Finset.Ioc a b, 1 / (p : ℝ) ^ 2 ≤ 1 / (a : ℝ) - 1 / (b : ℝ) := by
    induction b with
    | zero => omega
    | succ b ih =>
      by_cases h : a ≤ b
      · have hbp : 0 < (b : ℝ) := by exact_mod_cast ha.trans_le h
        have hs : Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
          ext p
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          omega
        have hstep : (1 : ℝ) / ((b : ℝ) + 1) ^ 2 ≤ 1 / (b : ℝ) - 1 / ((b : ℝ) + 1) := by
          calc
            _ ≤ 1 / ((b : ℝ) * ((b : ℝ) + 1)) := by
              apply one_div_le_one_div_of_le (by positivity)
              nlinarith
            _ = _ := by field_simp; ring
        rw [hs, Finset.sum_insert (by simp), Nat.cast_add, Nat.cast_one]
        linarith only [ih h, hstep]
      · have heq : a = b + 1 := by omega
        simp [heq]
  by_cases h : a ≤ b
  · exact (htail b h).trans (sub_le_self _ (by positivity))
  · have hempty : Finset.Ioc a b = ∅ := by
      ext p
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.sum_empty]
    positivity

/-- Failure of full row rank after reduction of a binary matrix modulo `p`. -/
@[expose] def modularRankDeficient {N : ℕ} (p : ℕ) (B : Fin N → Fin (N + 1) → Bool) : Prop :=
  ¬ Function.Surjective (((Matrix.of B).map (fun e => ((zeroOneBit e : ℤ) : ZMod p))).mulVecLin)

/-- The union bound for the intermediate primes in Lemma 9, under the
per-prime finite-field estimate. -/
theorem intermediate_prime_probability_le {N a b : ℕ} (ha : 0 < a) {C E : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hp : ∀ p : ℕ, p.Prime → a < p → p ≤ b →
      (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool | modularRankDeficient p B} ≤
        C / (p : ℝ) ^ 2 + E) :
    (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
      ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b ∧ p ∣ binaryCokernelIndex B} ≤
        C / (a : ℝ) + (b : ℝ) * E := by
  classical
  let s := (Finset.Ioc a b).filter Nat.Prime
  let μ := uniformOn (Set.univ : Set (Fin N → Fin (N + 1) → Bool))
  let F (p : ℕ) : Set (Fin N → Fin (N + 1) → Bool) := {B | p ∣ binaryCokernelIndex B}
  have heq : {B | ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b ∧ p ∣ binaryCokernelIndex B} =
      ⋃ p ∈ s, F p := by
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, s, F, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨p, hprime, hlt, hle, hd⟩
      exact ⟨p, ⟨⟨hlt, hle⟩, hprime⟩, hd⟩
    · rintro ⟨p, ⟨⟨hlt, hle⟩, hprime⟩, hd⟩
      exact ⟨p, hprime, hlt, hle, hd⟩
  have hsub (p : ℕ) (hs : p ∈ s) : μ.real (F p) ≤ C / (p : ℝ) ^ 2 + E := by
    have hm := Finset.mem_filter.mp hs
    have hj := Finset.mem_Ioc.mp hm.1
    apply (measureReal_mono ?_).trans (hp p hm.2 hj.1 hj.2)
    intro B hB
    exact (prime_dvd_index_iff_not_surjective_mod hm.2 ((Matrix.of B).map zeroOneBit)).mp hB
  rw [heq]
  calc
    μ.real (⋃ p ∈ s, F p) ≤ ∑ p ∈ s, μ.real (F p) := measureReal_biUnion_finset_le s F
    _ ≤ ∑ p ∈ s, (C / (p : ℝ) ^ 2 + E) := Finset.sum_le_sum hsub
    _ ≤ ∑ p ∈ Finset.Ioc a b, (C / (p : ℝ) ^ 2 + E) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = C * (∑ p ∈ Finset.Ioc a b, 1 / (p : ℝ) ^ 2) + ((b - a : ℕ) : ℝ) * E := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp [div_eq_mul_inv]
    _ ≤ C * (1 / (a : ℝ)) + (b : ℝ) * E :=
      add_le_add (mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le a b ha) hC)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le b a) hE)
    _ = C / (a : ℝ) + (b : ℝ) * E := by ring

end BooleanThreshold
