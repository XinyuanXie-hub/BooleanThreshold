module

public import BooleanThreshold.JSSConditionalTail
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Variance

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory unitInterval

namespace BooleanThreshold

/-- The probability of rounding the given coordinate up. -/
noncomputable def roundingParameter (v : ℝ) : unitInterval :=
  ⟨v - (⌊v⌋ : ℝ), sub_nonneg.mpr (Int.floor_le v), by linarith [Int.lt_floor_add_one v]⟩

/-- The rounded vector has each coordinate at the floor or one above the floor. -/
noncomputable def roundedVector {n : ℕ} (v : Fin n → ℝ) (b : Fin n → Bool) : Fin n → ℤ :=
  fun i => ⌊v i⌋ + if b i then 1 else 0

/-- Independent unbiased rounding on each coordinate. -/
noncomputable def roundingLaw {n : ℕ} (v : Fin n → ℝ) : Measure (Fin n → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (roundingParameter (v i)))

instance {n : ℕ} (v : Fin n → ℝ) : IsProbabilityMeasure (roundingLaw v) := by
  unfold roundingLaw
  infer_instance

theorem roundedVector_coordinate_bound {n : ℕ} (v : Fin n → ℝ) (b : Fin n → Bool) (i : Fin n) :
    |(roundedVector v b i : ℝ) - v i| ≤ 1 := by
  have hl := Int.floor_le (v i)
  have hu := Int.lt_floor_add_one (v i)
  cases hbit : b i <;> simp only [roundedVector, hbit, Bool.false_eq_true, ↓reduceIte,
    Int.add_zero, Int.cast_add, Int.cast_one] <;> rw [abs_le] <;>
    constructor <;> linarith only [hl, hu]

/-- Chebyshev bound for a signed or bounded weighted sum of rounding errors. -/
theorem rounding_error_tail_le {n : ℕ} (v a : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ 1) {t : ℝ} (ht : 0 < t) :
    (roundingLaw v).real {b | t ≤ |∑ i, a i * ((roundedVector v b i : ℝ) - v i)|}
      ≤ (n : ℝ) / (4 * t ^ 2) := by
  let p (i : Fin n) := roundingParameter (v i)
  let ν (i : Fin n) : Measure Bool := bernoulliMeasure true false (p i)
  let : ∀ i, IsProbabilityMeasure (ν i) := by intro i; dsimp [ν]; infer_instance
  let μ := roundingLaw v
  let X (i : Fin n) (x : Bool) : ℝ := a i * ((if x then 1 else 0) - (p i : ℝ))
  let Y (b : Fin n → Bool) := ∑ i, X i (b i)
  have hpi : μ = Measure.pi ν := rfl
  have hX (i : Fin n) : MemLp (X i) 2 (ν i) := by
    apply MemLp.of_bound (measurable_of_finite (X i)).aestronglyMeasurable (|a i|)
    apply ae_of_all
    intro x
    rw [show X i x = a i * ((if x then 1 else 0) - (p i : ℝ)) by rfl, Real.norm_eq_abs, abs_mul]
    have ht' : |((if x then 1 else 0) : ℝ) - (p i : ℝ)| ≤ 1 := by
      cases x <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_le] <;>
        constructor <;> linarith only [(p i).2.1, (p i).2.2]
    calc
      _ ≤ |a i| * 1 := mul_le_mul_of_nonneg_left ht' (abs_nonneg _)
      _ = _ := mul_one _
  have hXs (i : Fin n) : MemLp (fun b : Fin n → Bool => X i (b i)) 2 μ := by
    rw [hpi]
    exact (hX i).comp_measurePreserving (measurePreserving_eval ν i)
  have hY : MemLp Y 2 μ := by
    unfold Y
    exact memLp_finsetSum _ (fun i _ => hXs i)
  have hmean (i : Fin n) : (∫ x, X i x ∂ν i) = 0 := by
    rw [show ν i = bernoulliMeasure true false (p i) by rfl, integral_bernoulliMeasure]
    simp only [X, ↓reduceIte, Bool.false_eq_true, smul_eq_mul]
    ring
  have hYfun : (∑ i, fun b : Fin n → Bool => X i (b i)) = Y := by
    funext b
    simp only [Y, Finset.sum_apply]
  have hYmean : (∫ b, Y b ∂μ) = 0 := by
    dsimp [Y]
    rw [integral_finsetSum _ (fun i _ => (hXs i).integrable (by norm_num))]
    apply Finset.sum_eq_zero
    intro i _
    change (∫ b : Fin n → Bool, X i (b i) ∂μ) = 0
    rw [hpi, ← integral_map_of_stronglyMeasurable (measurable_pi_apply i)
      (measurable_of_finite (X i)).stronglyMeasurable, (measurePreserving_eval ν i).map_eq, hmean]
  have hVar (i : Fin n) : variance (X i) (ν i) ≤ 1 / 4 := by
    rw [variance_eq_sub (hX i), hmean]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
    change (∫ x, (X i x) ^ 2 ∂ν i) ≤ _
    rw [show ν i = bernoulliMeasure true false (p i) by rfl, integral_bernoulliMeasure]
    simp only [X, ↓reduceIte, Bool.false_eq_true, smul_eq_mul]
    have hp₁ : 0 ≤ (p i : ℝ) := (p i).2.1
    have hp₂ : 0 ≤ 1 - (p i : ℝ) := sub_nonneg.mpr (p i).2.2
    have hsq : a i ^ 2 ≤ 1 := by
      rw [← sq_abs (a i)]
      exact (pow_le_pow_left₀ (abs_nonneg _) (ha i) 2).trans_eq (one_pow 2)
    calc
      _ = a i ^ 2 * ((p i : ℝ) * (1 - (p i : ℝ))) := by ring
      _ ≤ 1 * ((p i : ℝ) * (1 - (p i : ℝ))) := mul_le_mul_of_nonneg_right hsq (mul_nonneg hp₁ hp₂)
      _ ≤ _ := by nlinarith [sq_nonneg ((p i : ℝ) - 1 / 2)]
  have hYVar : variance Y μ ≤ (n : ℝ) / 4 := by
    rw [← hYfun, hpi]
    rw [variance_sum_pi hX]
    calc
      _ ≤ ∑ _i : Fin n, (1 / 4 : ℝ) := Finset.sum_le_sum fun i _ => hVar i
      _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]
  have herror (b : Fin n → Bool) :
      Y b = ∑ i, a i * ((roundedVector v b i : ℝ) - v i) := by
    unfold Y
    apply Finset.sum_congr rfl
    intro i _
    change a i * ((if b i then (1 : ℝ) else 0) - (v i - ↑⌊v i⌋)) =
      a i * ((roundedVector v b i : ℝ) - v i)
    cases h : b i <;> simp only [roundedVector, h, Bool.false_eq_true, ↓reduceIte, Int.add_zero,
      Int.cast_add, Int.cast_one] <;> ring
  have hcheb := meas_ge_le_variance_div_sq hY ht
  rw [hYmean] at hcheb
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
  have hnn : 0 ≤ variance Y μ / t ^ 2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  simp only [sub_zero, ← measureReal_def, ENNReal.toReal_ofReal hnn, herror] at h
  refine h.trans ?_
  rw [← div_div]
  exact div_le_div_of_nonneg_right hYVar (sq_nonneg _)

end BooleanThreshold
