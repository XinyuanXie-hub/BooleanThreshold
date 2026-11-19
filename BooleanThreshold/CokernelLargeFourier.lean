module

public import BooleanThreshold.CokernelLargeProgressions
public import BooleanThreshold.KKSLargeRadius

public section

open AddChar Complex Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Pointwise

namespace BooleanThreshold

/-- The largest binary atom is attained at a finite-field target. -/
theorem exists_binary_atom_eq_concentration {p N : ℕ} [Fact p.Prime]
    (a : Fin N → ZMod p) :
    ∃ z : ZMod p, (uniformOn Set.univ).real
      {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z} =
        binaryConcentration a := by
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun z : ZMod p => (uniformOn Set.univ).real
      {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z})
  exact ⟨z, hz.symm⟩

theorem binaryAtom_eq_fourier {p N : ℕ} [NeZero p] (a : Fin N → ZMod p)
    (z : ZMod p) :
    (p : ℂ) * ((uniformOn Set.univ).real
      {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z} : ℂ) =
      ∑ t : ZMod p, ZMod.stdAddChar (-z * t) *
        ∏ i, (1 + ZMod.stdAddChar (a i * t)) / 2 := by
  classical
  let A : Finset (Fin N → Bool) := univ.filter
    (fun x => a ⬝ᵥ binaryColumn (ZMod p) x = z)
  have hAtom :
      (uniformOn Set.univ).real {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z} =
        (A.card : ℝ) / 2 ^ N := by
    rw [uniformOn_univ_real_eq_card]
    have he : ({x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z} : Set _) = A := by
      ext x
      simp [A]
    rw [he, Set.ncard_coe_finset]
    simp
  have hMean (i : Fin N) (t : ZMod p) :
      (1 + ZMod.stdAddChar (a i * t)) / 2 =
        ∑ b : Bool, (2 : ℂ)⁻¹ * ZMod.stdAddChar
          (a i * (zeroOneBit b : ZMod p) * t) := by
    rw [Fintype.sum_bool]
    simp [zeroOneBit, div_eq_mul_inv]
    ring
  have hChar (x : Fin N → Bool) (t : ZMod p) :
      ZMod.stdAddChar (-z * t) *
        (∏ i, ZMod.stdAddChar (a i * (zeroOneBit (x i) : ZMod p) * t)) =
      ZMod.stdAddChar ((a ⬝ᵥ binaryColumn (ZMod p) x - z) * t) := by
    rw [← map_sum_standard, ← map_add_eq_mul]
    congr 1
    rw [sub_mul, dotProduct, Finset.sum_mul, neg_mul, sub_eq_add_neg, add_comm (- (z * t))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases h : x i <;> simp [binaryColumn, zeroOneBit, h]
  rw [hAtom]
  push_cast
  simp_rw [hMean, Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hExpand (t : ZMod p) (x : Fin N → Bool) :
      ZMod.stdAddChar (-z * t) *
        ((2 : ℂ)⁻¹ ^ N * ∏ i, ZMod.stdAddChar (a i * (zeroOneBit (x i) : ZMod p) * t)) =
      (2 : ℂ)⁻¹ ^ N * ZMod.stdAddChar ((a ⬝ᵥ binaryColumn (ZMod p) x - z) * t) := by
    rw [mul_left_comm, hChar]
  simp_rw [Finset.mul_sum, hExpand, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_standard_mul_character, sub_eq_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [A, inv_pow, div_eq_mul_inv]
  ring

theorem norm_binary_character_le_exp {p : ℕ} [NeZero p] (b : ZMod p) :
    ‖(1 + ZMod.stdAddChar b) / 2‖ ≤
      Real.exp (-(1 - (ZMod.stdAddChar b).re) / 4) := by
  let z := ZMod.stdAddChar b
  have hz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by simp [z]
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [pow_two] using h
  have hSq : ‖(1 + z) / 2‖ ^ 2 = 1 - (1 - z.re) / 2 := by
    rw [norm_div, div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    norm_num
    nlinarith only [hz]
  change ‖(1 + z) / 2‖ ≤ Real.exp (-(1 - z.re) / 4)
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _), hSq, ← Real.exp_nat_mul]
  convert Real.add_one_le_exp (-(1 - z.re) / 2) using 1 <;> ring_nf

/-- The character-energy bound for a binary atom in a finite cyclic group. -/
theorem binaryAtom_le_energy_mean {p N : ℕ} [NeZero p]
    (a : Fin N → ZMod p) (z : ZMod p) :
    (p : ℝ) * (uniformOn Set.univ).real {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z} ≤
      ∑ t : ZMod p, Real.exp (-characterEnergy a t) := by
  have hfourier := binaryAtom_eq_fourier a z
  have hf : (p : ℝ) * (uniformOn Set.univ).real {x : Fin N → Bool |
      a ⬝ᵥ binaryColumn (ZMod p) x = z} = ‖∑ t : ZMod p,
      ZMod.stdAddChar (-z * t) * (∏ i, (1 + ZMod.stdAddChar (a i * t)) / 2)‖ := by
    rw [← hfourier, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg measureReal_nonneg]
  rw [hf]
  apply (norm_sum_le _ _).trans
  refine sum_le_sum fun t _ => ?_
  rw [norm_mul, norm_standard_character, one_mul, norm_prod]
  calc
    _ ≤ ∏ i, Real.exp (-(1 - (ZMod.stdAddChar (a i * t)).re) / 4) :=
      prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => norm_binary_character_le_exp (a i * t))
    _ = _ := by
      rw [← Real.exp_sum, characterEnergy]
      congr 1
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib, neg_mul]

theorem binaryConcentration_le_energy_mean {p N : ℕ} [Fact p.Prime]
    (a : Fin N → ZMod p) :
    (p : ℝ) * binaryConcentration a ≤ ∑ t : ZMod p, Real.exp (-characterEnergy a t) := by
  obtain ⟨z, hz⟩ := exists_binary_atom_eq_concentration a
  exact hz ▸ binaryAtom_le_energy_mean a z

private theorem binaryEnergy_level_card_aux {p N : ℕ} [NeZero p] {a : Fin N → ZMod p}
    {M ρ : ℝ} (h : (p : ℝ) * ρ ≤ ∑ t : ZMod p, Real.exp (-characterEnergy a t))
    (hM : Real.exp (-M) ≤ ρ / 2) :
    (p : ℝ) * ρ / 2 ≤
      ((univ.filter fun t : ZMod p => characterEnergy a t ≤ M).card : ℝ) := by
  classical
  let S : Finset (ZMod p) := univ.filter (fun t => characterEnergy a t ≤ M)
  have hs : (∑ t : ZMod p, Real.exp (-characterEnergy a t)) ≤
      S.card + (p : ℝ) * Real.exp (-M) := by
    have hsum : (∑ t : ZMod p, Real.exp (-characterEnergy a t)) ≤
        ∑ t : ZMod p, ((if t ∈ S then 1 else 0) + Real.exp (-M)) := by
      apply sum_le_sum
      intro t _
      by_cases ht : t ∈ S
      · simp only [ite_eq_left ht]
        exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (characterEnergy_nonneg a t))).trans
          (le_add_of_nonneg_right (Real.exp_nonneg _))
      · simp only [ite_eq_right ht, zero_add]
        apply Real.exp_le_exp.mpr
        have hlt : M < characterEnergy a t := by simpa [S] using ht
        exact neg_le_neg hlt.le
    simpa [sum_add_distrib, ← sum_filter, ZMod.card, S] using hsum
  have hm := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg p)
  linarith

/-- A high atom provides a large set of frequencies whose total row energy
at each frequency is small. -/
theorem binaryEnergy_level_card_at_target {p N : ℕ} [NeZero p] {a : Fin N → ZMod p}
    (z : ZMod p) {M : ℝ}
    (hM : Real.exp (-M) ≤ (uniformOn Set.univ).real {x : Fin N → Bool |
      a ⬝ᵥ binaryColumn (ZMod p) x = z} / 2) :
    (p : ℝ) * (uniformOn Set.univ).real {x : Fin N → Bool |
      a ⬝ᵥ binaryColumn (ZMod p) x = z} / 2 ≤
      ((univ.filter fun t : ZMod p => characterEnergy a t ≤ M).card : ℝ) :=
  binaryEnergy_level_card_aux (binaryAtom_le_energy_mean a z) hM

theorem binaryEnergy_level_card {p N : ℕ} [Fact p.Prime] {a : Fin N → ZMod p}
    {M : ℝ} (hM : Real.exp (-M) ≤ binaryConcentration a / 2) :
    (p : ℝ) * binaryConcentration a / 2 ≤
      ((univ.filter fun t : ZMod p => characterEnergy a t ≤ M).card : ℝ) :=
  binaryEnergy_level_card_aux (binaryConcentration_le_energy_mean a) hM

end BooleanThreshold
