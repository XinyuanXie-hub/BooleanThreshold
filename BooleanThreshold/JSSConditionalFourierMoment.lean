module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

open scoped BigOperators Classical ZMod

namespace BooleanThreshold

/-- One average of a function and an integral translate on a finite cycle. -/
def cyclicShiftAverage {P : ℕ} (y : ℤ) (f : ZMod P → ℂ) (t : ZMod P) : ℂ :=
  (f t + f (t + (y : ZMod P))) / 2

/-- Independent fair averages over integral shifts. -/
def cyclicShiftSmoothing {P : ℕ} (f : ZMod P → ℂ) :
    {m : ℕ} → (Fin m → ℤ) → ZMod P → ℂ
  | 0, _ => f
  | _m + 1, y => cyclicShiftAverage (y 0) (cyclicShiftSmoothing f (Fin.tail y))

/-- The Fourier multiplier of one fair integral shift. -/
def cyclicShiftMultiplier {P : ℕ} [NeZero P] (k : ZMod P) (y : ℤ) : ℂ :=
  (1 + ZMod.stdAddChar ((y : ZMod P) * k)) / 2

theorem dft_cyclicTranslate {P : ℕ} [NeZero P] (f : ZMod P → ℂ) (k y : ZMod P) :
    𝓕 (fun t => f (t + y)) k = ZMod.stdAddChar (y * k) * 𝓕 f k := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight y) _ _ fun t => ?_
  change ZMod.stdAddChar (-(t * k)) * f (t + y) =
    ZMod.stdAddChar (y * k) * (ZMod.stdAddChar (-((t + y) * k)) * f (t + y))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem dft_cyclicShiftAverage {P : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (k : ZMod P) (y : ℤ) :
    𝓕 (cyclicShiftAverage y f) k = cyclicShiftMultiplier k y * 𝓕 f k := by
  have h : cyclicShiftAverage y f = (2 : ℂ)⁻¹ • (f + (fun t => f (t + (y : ZMod P)))) := by
    funext t
    simp only [cyclicShiftAverage, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [h, map_smul, map_add]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, dft_cyclicTranslate, cyclicShiftMultiplier]
  ring

theorem dft_cyclicShiftSmoothing {P m : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (k : ZMod P) (y : Fin m → ℤ) :
    𝓕 (cyclicShiftSmoothing f y) k = (∏ i, cyclicShiftMultiplier k (y i)) * 𝓕 f k := by
  induction m with
  | zero => simp [cyclicShiftSmoothing]
  | succ m ih =>
    rw [cyclicShiftSmoothing, dft_cyclicShiftAverage, ih, Fin.prod_univ_succ, ← mul_assoc]
    rfl

/-- The sum of squared Fourier coefficients over the selected frequencies. -/
def cyclicFourierEnergy {P : ℕ} [NeZero P] (S : Finset (ZMod P)) (f : ZMod P → ℂ) : ℝ :=
  ∑ k ∈ S, ‖𝓕 f k‖ ^ 2

/-- A uniform bound for the moments of the individual multipliers gives an
exponentially decreasing moment bound for the retained Fourier energy. -/
theorem cyclicShiftSmoothing_energy_moment_le {P m p : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (S : Finset (ZMod P)) (B : Fin m → Finset ℤ) {q : ℝ}
    (hf : 0 < cyclicFourierEnergy S f)
    (hmul : ∀ i k, k ∈ S →
      ∑ y ∈ B i, ‖cyclicShiftMultiplier k y‖ ^ (2 * p) ≤ q * (B i).card) :
    (∑ y ∈ Fintype.piFinset B,
      (cyclicFourierEnergy S (cyclicShiftSmoothing f y) / cyclicFourierEnergy S f) ^ p) ≤
      q ^ m * ∏ i, ((B i).card : ℝ) := by
  classical
  let E := cyclicFourierEnergy S f
  let w (k : ZMod P) := ‖𝓕 f k‖ ^ 2 / E
  let a (k : ZMod P) (y : Fin m → ℤ) := ∏ i, ‖cyclicShiftMultiplier k (y i)‖ ^ 2
  have hw (k : ZMod P) : 0 ≤ w k := by dsimp [w, E]; positivity
  have hw' : ∑ k ∈ S, w k = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self hf.ne'
  have ha (k : ZMod P) (y : Fin m → ℤ) : 0 ≤ a k y := by dsimp [a]; positivity
  have hs (y : Fin m → ℤ) :
      cyclicFourierEnergy S (cyclicShiftSmoothing f y) / E = ∑ k ∈ S, w k * a k y := by
    simp only [cyclicFourierEnergy, dft_cyclicShiftSmoothing, norm_mul, norm_prod, mul_pow,
      w, a, ← Finset.prod_pow, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hp (y : Fin m → ℤ) :
      (cyclicFourierEnergy S (cyclicShiftSmoothing f y) / E) ^ p ≤
        ∑ k ∈ S, w k * ∏ i, ‖cyclicShiftMultiplier k (y i)‖ ^ (2 * p) := by
    rw [hs]
    simpa only [smul_eq_mul, Finset.prod_pow, ← pow_mul, a] using
      (convexOn_pow (𝕜 := ℝ) p).map_sum_le (fun k _ => hw k) hw'
        (fun k (_ : k ∈ S) => ha k y)
  calc
    _ ≤ ∑ y ∈ Fintype.piFinset B, ∑ k ∈ S, w k * ∏ i, ‖cyclicShiftMultiplier k (y i)‖ ^ (2 * p) :=
      Finset.sum_le_sum fun y _ => hp y
    _ = ∑ k ∈ S, w k * (∏ i, ∑ y ∈ B i, ‖cyclicShiftMultiplier k y‖ ^ (2 * p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum, Finset.prod_univ_sum]
    _ ≤ ∑ k ∈ S, w k * (∏ i, q * (B i).card) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (fun i _ => hmul i k hk)) (hw k)
    _ = _ := by
      rw [← Finset.sum_mul, hw', one_mul, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

/-- The number of shift choices that retain a given fraction of the energy
is bounded by the moment of that energy fraction. -/
theorem cyclicShiftSmoothing_card_energy_ge_le {P m p : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (S : Finset (ZMod P)) (B : Fin m → Finset ℤ) {q ε : ℝ} (hε : 0 < ε)
    (hf : 0 < cyclicFourierEnergy S f)
    (hmul : ∀ i k, k ∈ S →
      ∑ y ∈ B i, ‖cyclicShiftMultiplier k y‖ ^ (2 * p) ≤ q * (B i).card) :
    (((Fintype.piFinset B).filter (fun y => ε * cyclicFourierEnergy S f ≤
      cyclicFourierEnergy S (cyclicShiftSmoothing f y))).card : ℝ) ≤
      q ^ m / ε ^ p * ∏ i, ((B i).card : ℝ) := by
  let X := Fintype.piFinset B
  let J (y : Fin m → ℤ) := cyclicFourierEnergy S (cyclicShiftSmoothing f y) / cyclicFourierEnergy S f
  let T := X.filter (fun y => ε * cyclicFourierEnergy S f ≤
    cyclicFourierEnergy S (cyclicShiftSmoothing f y))
  have h : (T.card : ℝ) * ε ^ p ≤ q ^ m * ∏ i, ((B i).card : ℝ) := by
    calc
      _ = ∑ _y ∈ T, ε ^ p := by simp
      _ ≤ ∑ y ∈ T, J y ^ p := by
        refine Finset.sum_le_sum fun y hy => pow_le_pow_left₀ hε.le ?_ _
        exact (le_div_iff₀ hf).mpr (Finset.mem_filter.mp hy).2
      _ ≤ ∑ y ∈ X, J y ^ p := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun y _ _ => by dsimp only [J, cyclicFourierEnergy]; positivity)
      _ ≤ _ := cyclicShiftSmoothing_energy_moment_le f S B hf hmul
  change (T.card : ℝ) ≤ _
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (pow_pos hε _)).mpr h

theorem conj_stdAddChar {P : ℕ} [NeZero P] (x : ZMod P) :
    starRingEnd ℂ (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have h : ‖ZMod.stdAddChar x‖ = 1 := Circle.norm_coe (ZMod.toCircle x)
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj h]

/-- Parseval's identity for the unnormalized discrete Fourier transform. -/
theorem cyclicFourierEnergy_univ {P : ℕ} [NeZero P] (f : ZMod P → ℂ) :
    cyclicFourierEnergy Finset.univ f = (P : ℝ) * ∑ t, ‖f t‖ ^ 2 := by
  have hc (k : ZMod P) : starRingEnd ℂ (𝓕 f k) =
      ∑ t, ZMod.stdAddChar (t * k) * starRingEnd ℂ (f t) := by
    rw [ZMod.dft_apply, map_sum]
    simp only [smul_eq_mul, map_mul, conj_stdAddChar, neg_neg]
  have hi (t : ZMod P) : (∑ k, ZMod.stdAddChar (t * k) * 𝓕 f k) = (P : ℂ) * f t := by
    have h := congrFun (ZMod.dft_dft f) (-t)
    rw [ZMod.dft_apply] at h
    simpa only [mul_neg, neg_neg, smul_eq_mul, mul_comm _ t] using h
  unfold cyclicFourierEnergy
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow]
  calc
    (∑ k, (↑(‖𝓕 f k‖ ^ 2) : ℂ)) = ∑ k, 𝓕 f k * starRingEnd ℂ (𝓕 f k) := by
      simp only [Complex.mul_conj, Complex.sq_norm]
    _ = ∑ k, ∑ t, 𝓕 f k * (ZMod.stdAddChar (t * k) * starRingEnd ℂ (f t)) := by
      simp only [hc, Finset.mul_sum]
    _ = ∑ t, starRingEnd ℂ (f t) * (∑ k, ZMod.stdAddChar (t * k) * 𝓕 f k) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (P : ℂ) * ∑ t, (↑(‖f t‖ ^ 2) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [hi, Complex.sq_norm, ← Complex.mul_conj]
      ring

end BooleanThreshold
