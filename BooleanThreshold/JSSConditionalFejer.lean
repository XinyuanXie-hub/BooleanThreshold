module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

open scoped BigOperators

namespace BooleanThreshold

/-- The Fejér kernel of positive bandwidth `M` on the cyclic group of order `P`,
normalized with counting measure. -/
noncomputable def fejerKernel {P : ℕ} [NeZero P] (M : ℕ) (t : ZMod P) : ℝ :=
  ‖∑ j ∈ Finset.range M, ZMod.stdAddChar ((j : ZMod P) * t)‖ ^ 2 / ((M : ℝ) * (P : ℝ))

/-- The de la Vallée Poussin kernel that preserves frequencies below `M`. -/
noncomputable def vpKernel {P : ℕ} [NeZero P] (M : ℕ) (t : ZMod P) : ℝ :=
  2 * fejerKernel (2 * M) t - fejerKernel M t

/-- A cyclic interval of `N` consecutive residues, starting at `a`. -/
def cyclicInterval (P N : ℕ) (a : ZMod P) : Finset (ZMod P) :=
  (Finset.range N).image (fun i : ℕ => a + (i : ZMod P))

/-- Convolution on the cyclic group, with counting measure. -/
noncomputable def cyclicConvolution {R : Type*} [Semiring R] {P : ℕ} [NeZero P]
    (f g : ZMod P → R) (t : ZMod P) : R :=
  ∑ u : ZMod P, f u * g (t - u)

private theorem norm_stdAddChar {P : ℕ} [NeZero P] (t : ZMod P) : ‖ZMod.stdAddChar t‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem fejerKernel_nonneg {P : ℕ} [NeZero P] (M : ℕ) (t : ZMod P) : 0 ≤ fejerKernel M t := by
  unfold fejerKernel
  positivity

theorem fejerKernel_le_bandwidth_div_modulus {P : ℕ} [NeZero P] {M : ℕ} (hM : 0 < M)
    (t : ZMod P) : fejerKernel M t ≤ (M : ℝ) / (P : ℝ) := by
  have hsum : ‖∑ j ∈ Finset.range M, ZMod.stdAddChar ((j : ZMod P) * t)‖ ≤ (M : ℝ) := by
    refine (norm_sum_le _ _).trans_eq ?_
    simp only [norm_stdAddChar, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  unfold fejerKernel
  calc
    _ ≤ (M : ℝ) ^ 2 / ((M : ℝ) * (P : ℝ)) := by
      apply div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsum 2)
      positivity
    _ = _ := by
      have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      rw [pow_two, mul_div_mul_left _ _ hm]

private theorem norm_stdAddChar_sub_one_ge {P : ℕ} [NeZero P] (t : ZMod P) :
    4 * (t.valMinAbs.natAbs : ℝ) / (P : ℝ) ≤ ‖ZMod.stdAddChar t - 1‖ := by
  have hP : 0 < (P : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  let d := (t.valMinAbs.natAbs : ℝ)
  have hhalf : 2 * d ≤ (P : ℝ) := by
    have h := (Nat.le_div_two_iff_mul_two_le.mp (ZMod.natAbs_valMinAbs_le t))
    dsimp [d]
    exact_mod_cast (by omega : 2 * t.valMinAbs.natAbs ≤ P)
  let x := Real.pi * (t.valMinAbs : ℝ) / (P : ℝ)
  have hxabs : |x| = Real.pi * d / (P : ℝ) := by
    dsimp [x, d]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hP,
      ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hx : |x| ≤ Real.pi / 2 := by
    rw [hxabs, div_le_iff₀ hP]
    have h := mul_le_mul_of_nonneg_left hhalf Real.pi_pos.le
    linarith only [h]
  have heq : ZMod.stdAddChar t = Complex.exp (Complex.I * ((2 * x : ℝ) : ℂ)) := by
    rw [← ZMod.coe_valMinAbs t, ZMod.stdAddChar_coe]
    dsimp only [x]
    push_cast
    ring_nf
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show 2 * x / 2 = x by ring, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hsin := Real.mul_abs_le_abs_sin hx
  rw [hxabs] at hsin
  have hh : 2 / Real.pi * (Real.pi * d / (P : ℝ)) = 2 * d / (P : ℝ) := by
    field_simp [Real.pi_pos.ne', hP.ne']
  rw [hh] at hsin
  change 4 * d / (P : ℝ) ≤ _
  calc
    _ = 2 * (2 * d / (P : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsin (by norm_num)

/-- Fejér's kernel decays quadratically in the cyclic distance from zero. -/
theorem fejerKernel_le_inv_cyclic_distance_sq {P : ℕ} [NeZero P] {M : ℕ} (hM : 0 < M)
    {t : ZMod P} (ht : t ≠ 0) :
    fejerKernel M t ≤ (P : ℝ) / (4 * (M : ℝ) * (t.valMinAbs.natAbs : ℝ) ^ 2) := by
  let d := (t.valMinAbs.natAbs : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Nat.pos_of_ne_zero (fun he => ht ((ZMod.valMinAbs_eq_zero t).mp (Int.natAbs_eq_zero.mp he)))
  have hP : 0 < (P : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  let q := ZMod.stdAddChar t
  let S := ∑ j ∈ Finset.range M, q ^ j
  have hS : ∑ j ∈ Finset.range M, ZMod.stdAddChar ((j : ZMod P) * t) = S := by
    apply Finset.sum_congr rfl
    intro j _
    simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j t
  have hq : ‖q‖ = 1 := norm_stdAddChar t
  have hboundary : ‖S‖ * ‖q - 1‖ ≤ 2 := by
    rw [← norm_mul, show S * (q - 1) = q ^ M - 1 from geom_sum_mul q M]
    exact (norm_sub_le _ _).trans_eq (by rw [norm_pow, hq, one_pow, norm_one]; norm_num)
  have hr : ‖S‖ * (4 * d / (P : ℝ)) ≤ 2 :=
    (mul_le_mul_of_nonneg_left (norm_stdAddChar_sub_one_ge t) (norm_nonneg _)).trans hboundary
  have hnorm : ‖S‖ ≤ (P : ℝ) / (2 * d) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := (div_le_iff₀ hP).mp (by
      simpa only [← mul_div_assoc] using hr : ‖S‖ * (4 * d) / (P : ℝ) ≤ 2)
    nlinarith only [hh]
  unfold fejerKernel
  rw [hS]
  calc
    _ ≤ ((P : ℝ) / (2 * d)) ^ 2 / ((M : ℝ) * (P : ℝ)) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (by positivity)
    _ = _ := by change _ = (P : ℝ) / (4 * (M : ℝ) * d ^ 2); field_simp; ring

end BooleanThreshold
