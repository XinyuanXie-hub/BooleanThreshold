module

public import BooleanThreshold.CokernelMaplesFourier
public import BooleanThreshold.KKSLargeRadius

@[expose] public noncomputable section

open AddChar Complex
open scoped BigOperators

namespace BooleanThreshold

variable {q : ℕ} [NeZero q]

/-- The deficit in the squared Fourier magnitude of one binary coordinate. -/
def bitFourierDeficit (a : ZMod q) : ℝ :=
  (1 - (ZMod.stdAddChar a).re) / 2

theorem bitFourierDeficit_nonneg (a : ZMod q) : 0 ≤ bitFourierDeficit a := by
  have h := (Complex.re_le_norm (ZMod.stdAddChar a)).trans_eq (norm_standard_character a)
  unfold bitFourierDeficit
  linarith

theorem bitFourierDeficit_le_one (a : ZMod q) : bitFourierDeficit a ≤ 1 := by
  have h := Complex.abs_re_le_norm (ZMod.stdAddChar a)
  rw [norm_standard_character] at h
  unfold bitFourierDeficit
  linarith [(abs_le.mp h).1]

theorem bitFourierCoefficient_norm_sq (a : ZMod q) :
    ‖bitFourierCoefficient a‖ ^ 2 = 1 - bitFourierDeficit a := by
  let z := ZMod.stdAddChar a
  have hz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by simp [z]
    rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at h
  change ‖(1 + z) / 2‖ ^ 2 = 1 - (1 - z.re) / 2
  rw [norm_div, Complex.norm_two, div_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add, ← sq]
  nlinarith only [hz]

theorem bitFourierCoefficient_norm_le_one (a : ZMod q) : ‖bitFourierCoefficient a‖ ≤ 1 := by
  rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one, bitFourierCoefficient_norm_sq]
  linarith [bitFourierDeficit_nonneg a]

theorem bitFourierCoefficient_norm_le_exp (a : ZMod q) :
    ‖bitFourierCoefficient a‖ ≤ Real.exp (-(bitFourierDeficit a) / 2) := by
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _), bitFourierCoefficient_norm_sq,
    ← Real.exp_nat_mul]
  rw [show ((2 : ℕ) : ℝ) * (-bitFourierDeficit a / 2) = -bitFourierDeficit a by push_cast; ring]
  linarith [Real.add_one_le_exp (-bitFourierDeficit a)]

private theorem bitFourierDeficit_eq_norm_sq (a : ZMod q) :
    bitFourierDeficit a = ‖1 - ZMod.stdAddChar a‖ ^ 2 / 4 := by
  let z := ZMod.stdAddChar a
  have hz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by simp [z]
    rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at h
  change (1 - z.re) / 2 = ‖1 - z‖ ^ 2 / 4
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, ← sq]
  nlinarith only [hz]

private theorem bitFourierDeficit_add_le (a b : ZMod q) :
    bitFourierDeficit (a + b) ≤ 2 * (bitFourierDeficit a + bitFourierDeficit b) := by
  have hsum : 1 - ZMod.stdAddChar (a + b) =
      (1 - ZMod.stdAddChar a) + ZMod.stdAddChar a * (1 - ZMod.stdAddChar b) := by
    rw [map_add_eq_mul]
    ring
  have h := norm_add_le (1 - ZMod.stdAddChar a)
      (ZMod.stdAddChar a * (1 - ZMod.stdAddChar b))
  rw [← hsum, norm_mul, norm_standard_character, one_mul] at h
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [bitFourierDeficit_eq_norm_sq]
  nlinarith only [h', sq_nonneg (‖1 - ZMod.stdAddChar a‖ - ‖1 - ZMod.stdAddChar b‖)]

/-- Uniform sampling on thirty copies of zero and one copy of each sign. -/
def maplesLazySample (b : Fin 32) : ZMod q :=
  if b.val = 0 then 1 else if b.val = 1 then -1 else 0

/-- The real Fourier coefficient of the lazy comparison distribution. -/
def maplesLazyFourier (a : ZMod q) : ℝ :=
  1 - bitFourierDeficit a / 8

theorem maplesLazyFourier_nonneg (a : ZMod q) : 0 ≤ maplesLazyFourier a := by
  unfold maplesLazyFourier
  linarith [bitFourierDeficit_le_one a]

theorem maplesLazyFourier_le_one (a : ZMod q) : maplesLazyFourier a ≤ 1 := by
  unfold maplesLazyFourier
  linarith [bitFourierDeficit_nonneg a]

theorem maplesLazyFourier_le_exp (a : ZMod q) :
    maplesLazyFourier a ≤ Real.exp (-(bitFourierDeficit a) / 8) := by
  unfold maplesLazyFourier
  linarith only [Real.add_one_le_exp (-(bitFourierDeficit a) / 8)]

private theorem standard_character_neg (a : ZMod q) :
    ZMod.stdAddChar (-a) = star (ZMod.stdAddChar a) := by
  have h : ZMod.stdAddChar a ≠ 0 := by
    intro hz
    simpa [hz] using norm_standard_character a
  apply mul_left_cancel₀ h
  rw [← map_add_eq_mul, add_neg_cancel, map_zero_eq_one]
  change 1 = ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar a)
  rw [Complex.mul_conj', norm_standard_character]
  norm_num

theorem bitFourierCoefficient_norm_neg (a : ZMod q) :
    ‖bitFourierCoefficient (-a)‖ = ‖bitFourierCoefficient a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), bitFourierCoefficient_norm_sq,
    bitFourierCoefficient_norm_sq]
  simp [bitFourierDeficit, standard_character_neg]

theorem maplesLazyFourier_eq_character_average (a : ZMod q) :
    (maplesLazyFourier a : ℂ) =
      (∑ b : Fin 32, ZMod.stdAddChar (a * maplesLazySample b)) / (Fintype.card (Fin 32) : ℂ) := by
  have hsum : (∑ b : Fin 30, ZMod.stdAddChar
      (a * maplesLazySample b.succ.succ)) = 30 := by
    simp [maplesLazySample]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hsum]
  norm_num [maplesLazySample, maplesLazyFourier, bitFourierDeficit, standard_character_neg]
  apply Complex.ext <;> simp <;> ring

/-- The lazy distribution dominates a fourth root of the binary magnitude. -/
theorem bitFourierCoefficient_le_lazy_fourth (a : ZMod q) :
    ‖bitFourierCoefficient a‖ ≤ maplesLazyFourier a ^ 4 := by
  let u := ‖bitFourierCoefficient a‖
  let v := maplesLazyFourier a
  have hu : u ≤ 1 := bitFourierCoefficient_norm_le_one a
  have hv : 0 ≤ v := maplesLazyFourier_nonneg a
  have h₁ : v ^ 2 ≥ 2 * v - 1 := by nlinarith only [sq_nonneg (v - 1)]
  have h₂ : v ^ 4 ≥ 2 * v ^ 2 - 1 := by nlinarith only [sq_nonneg (v ^ 2 - 1)]
  have hv' : 4 * v - 3 = (1 + u ^ 2) / 2 := by
    dsimp [v, u, maplesLazyFourier]
    rw [bitFourierCoefficient_norm_sq]
    ring
  change u ≤ v ^ 4
  linarith only [h₁, h₂, hv', sq_nonneg (u - 1)]

/-- Products at two frequencies are bounded by the lazy coefficient of their sum. -/
theorem bitFourierCoefficient_mul_le_lazy_sq (a b : ZMod q) :
    ‖bitFourierCoefficient a‖ * ‖bitFourierCoefficient b‖ ≤ maplesLazyFourier (a + b) ^ 2 := by
  have h := bitFourierDeficit_add_le a b
  have ha := bitFourierCoefficient_norm_sq a
  have hb := bitFourierCoefficient_norm_sq b
  have hc := sq_nonneg (‖bitFourierCoefficient a‖ - ‖bitFourierCoefficient b‖)
  have hd := sq_nonneg (bitFourierDeficit (a + b) / 8)
  unfold maplesLazyFourier
  nlinarith only [h, ha, hb, hc, hd]

end BooleanThreshold
