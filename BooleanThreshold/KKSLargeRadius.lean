module

public import BooleanThreshold.KKSLargeFourier
public import BooleanThreshold.KKSLargeSublevel
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open Finset AddChar Complex
open scoped BigOperators

namespace BooleanThreshold

@[expose] noncomputable def charError {P n : ℕ} [NeZero P] (a : Fin n → ZMod P) (t : ZMod P) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => 1 - ZMod.stdAddChar (a i * t))

@[expose] noncomputable def charRadius {P n : ℕ} [NeZero P] (a : Fin n → ZMod P) (t : ZMod P) : ℝ :=
  ‖charError a t‖

/-- The Fourier energy whose sublevel sets are used in the Halász comparison. -/
@[expose] noncomputable def characterEnergy {P n : ℕ} [NeZero P]
    (a : Fin n → ZMod P) (t : ZMod P) : ℝ :=
  (∑ i, (1 - (ZMod.stdAddChar (a i * t)).re)) / 4

theorem norm_standard_character {P : ℕ} [NeZero P] (t : ZMod P) :
    ‖ZMod.stdAddChar t‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

theorem characterEnergy_eq_radius_sq {P n : ℕ} [NeZero P]
    (a : Fin n → ZMod P) (t : ZMod P) :
    characterEnergy a t = charRadius a t ^ 2 / 8 := by
  rw [characterEnergy, charRadius, EuclideanSpace.norm_sq_eq]
  rw [show ((∑ i, (1 - (ZMod.stdAddChar (a i * t)).re)) / 4 : ℝ) =
    (∑ i, (1 - (ZMod.stdAddChar (a i * t)).re) / 4) from by
      rw [div_eq_mul_inv, sum_mul]
      simp only [div_eq_mul_inv]]
  rw [div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro i _
  let z := ZMod.stdAddChar (a i * t)
  have hz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have hh : ‖z‖ ^ 2 = 1 := by simp [z]
    rw [Complex.sq_norm, Complex.normSq_apply] at hh
    simpa [pow_two] using hh
  change (1 - z.re) / 4 = ‖1 - z‖ ^ 2 * 8⁻¹
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith

theorem characterEnergy_nonneg {P n : ℕ} [NeZero P] (a : Fin n → ZMod P) (t : ZMod P) :
    0 ≤ characterEnergy a t := by rw [characterEnergy_eq_radius_sq]; positivity

theorem charRadius_zero {P n : ℕ} [NeZero P] (a : Fin n → ZMod P) :
    charRadius a 0 = 0 := by simp [charRadius, charError, Pi.zero_def]

theorem charRadius_add_le {P n : ℕ} [NeZero P]
    (a : Fin n → ZMod P) (u v : ZMod P) :
    charRadius a (u + v) ≤ charRadius a u + charRadius a v := by
  let y : EuclideanSpace ℂ (Fin n) :=
    WithLp.toLp 2 (fun i => ZMod.stdAddChar (a i * u) * (1 - ZMod.stdAddChar (a i * v)))
  have hy : ‖y‖ = ‖charError a v‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    simp [y, charError]
  have hsum : charError a (u + v) = charError a u + y := by
    ext i
    change 1 - ZMod.stdAddChar (a i * (u + v)) =
      (1 - ZMod.stdAddChar (a i * u)) +
        ZMod.stdAddChar (a i * u) * (1 - ZMod.stdAddChar (a i * v))
    rw [mul_add, map_add_eq_mul]
    ring
  change ‖charError a (u + v)‖ ≤ ‖charError a u‖ + ‖charError a v‖
  rw [hsum, ← hy]
  exact norm_add_le _ _

private theorem sum_characterEnergy {P n : ℕ} [NeZero P] (a : Fin n → ZMod P) :
    (∑ t : ZMod P, characterEnergy a t) = (P : ℝ) *
      (((univ.filter fun i => a i ≠ 0).card : ℝ) / 4) := by
  have hsum (i : Fin n) :
      (∑ t : ZMod P, (ZMod.stdAddChar (a i * t)).re) = if a i = 0 then (P : ℝ) else 0 := by
    have h := congrArg Complex.re (sum_standard_mul_character (a i))
    split_ifs at h ⊢ <;> simpa using h
  have hterm (i : Fin n) :
      (∑ t : ZMod P, (1 - (ZMod.stdAddChar (a i * t)).re)) =
        if a i ≠ 0 then (P : ℝ) else 0 := by
    rw [sum_sub_distrib, hsum]
    by_cases h : a i = 0 <;> simp [h, ZMod.card]
  simp only [characterEnergy, div_eq_mul_inv, ← sum_mul]
  rw [sum_comm]
  simp_rw [hterm]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-- The dilated sublevel estimate for the Fourier energy, while the radius is
below the average energy of the cycle. -/
theorem characterEnergy_sublevel_le {P n : ℕ} [NeZero P] (hP : P.Prime)
    (a : Fin n → ZMod P) (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 0 < k)
    (hsupp : (k : ℝ) ^ 2 * x < ((univ.filter fun i => a i ≠ 0).card : ℝ) / 4) :
    sublevelFraction (characterEnergy a) x ≤
      sublevelFraction (characterEnergy a) ((k : ℝ) ^ 2 * x) / k + 1 / P := by
  let r := charRadius a
  let s := Real.sqrt (8 * x)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = 8 * x := Real.sq_sqrt (by positivity)
  have hkS : 0 ≤ ((k : ℝ) * s) := by positivity
  have hR (t : ZMod P) : 0 ≤ r t := norm_nonneg _
  have hlo (t : ZMod P) : r t ≤ s ↔ characterEnergy a t ≤ x := by
    rw [← sq_le_sq₀ (hR t) hs, hsSq, characterEnergy_eq_radius_sq]
    change r t ^ 2 ≤ 8 * x ↔ r t ^ 2 / 8 ≤ x
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8), mul_comm 8 x]
  have hhi (t : ZMod P) : r t ≤ (k : ℝ) * s ↔ characterEnergy a t ≤ (k : ℝ) ^ 2 * x := by
    rw [← sq_le_sq₀ (hR t) hkS, mul_pow, hsSq, characterEnergy_eq_radius_sq]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
    change r t ^ 2 ≤ (k : ℝ) ^ 2 * (8 * x) ↔ r t ^ 2 ≤ (k : ℝ) ^ 2 * x * 8
    ring_nf
  have hproper : ∃ t, (k : ℝ) * s < r t := by
    by_contra! h
    have hsum : (∑ t : ZMod P, characterEnergy a t) ≤
        ∑ _t : ZMod P, (k : ℝ) ^ 2 * x :=
      sum_le_sum fun t _ => (hhi t).mp (h t)
    rw [sum_characterEnergy] at hsum
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hsum
    have hP' : 0 < (P : ℝ) := by exact_mod_cast hP.pos
    exact (not_le_of_gt hsupp) ((mul_le_mul_iff_of_pos_left hP').mp hsum)
  have h := sublevel_card_le_dilated hP r (charRadius_zero a) (charRadius_add_le a) s hs k hk hproper
  simpa only [hlo, hhi, sublevelFraction] using h

end BooleanThreshold
