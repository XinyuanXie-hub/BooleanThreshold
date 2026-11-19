module

public import BooleanThreshold.KKSLargeFourier
public import BooleanThreshold.KKSLargeTransfer
public import BooleanThreshold.SpanNormalization
public import Mathlib.MeasureTheory.Measure.Sum

public section

open Finset MeasureTheory ProbabilityTheory Complex AddChar
open scoped BigOperators ENNReal Classical

namespace BooleanThreshold

/-- The three-valued alphabet as `−1, 0, 1`. -/
@[expose] def lazyBit (j : Fin 3) : ℤ := (j.val : ℤ) - 1

/-- The same alphabet embedded into the reals. -/
@[expose] def lazyBitEmbedding : Fin 3 ↪ ℝ where
  toFun j := lazyBit j
  inj' := by
    intro i j h
    apply Fin.ext
    change (lazyBit i : ℝ) = (lazyBit j : ℝ) at h
    have hi : lazyBit i = lazyBit j := by exact_mod_cast h
    dsimp [lazyBit] at hi
    omega

/-- Atom weights for the coordinate distribution that stays at zero with probability
`1 - μ` and otherwise chooses a uniform sign. -/
@[expose] noncomputable def lazyBitWeight (μ : ℝ) (j : Fin 3) : ℝ :=
  if j = 1 then 1 - μ else μ / 2

theorem lazyBitWeight_nonneg {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (j : Fin 3) :
    0 ≤ lazyBitWeight μ j := by
  unfold lazyBitWeight
  split
  · linarith
  · positivity

/-- The coordinate law of a lazy sign row. -/
@[expose] noncomputable def lazyCoordinateLaw (μ : ℝ) : Measure (Fin 3) :=
  Measure.sum fun j => ENNReal.ofReal (lazyBitWeight μ j) • Measure.dirac j

@[simp]
theorem lazyCoordinateLaw_singleton (μ : ℝ) (j : Fin 3) :
    lazyCoordinateLaw μ {j} = ENNReal.ofReal (lazyBitWeight μ j) := by
  rw [lazyCoordinateLaw, Measure.sum_apply _ (measurableSet_singleton _), tsum_fintype]
  simp [Measure.smul_apply, Measure.dirac_apply', Pi.single_apply]

theorem lazyCoordinateLaw_probability {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) :
    IsProbabilityMeasure (lazyCoordinateLaw μ) := by
  refine ⟨?_⟩
  rw [← coe_univ (α := Fin 3), ← sum_measure_singleton, Fin.sum_univ_three]
  simp only [lazyCoordinateLaw_singleton, lazyBitWeight]
  norm_num
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ μ / 2) (by linarith : 0 ≤ 1 - μ),
    ← ENNReal.ofReal_add (by linarith : 0 ≤ μ / 2 + (1 - μ)) (by positivity : 0 ≤ μ / 2)]
  ring_nf
  exact ENNReal.ofReal_one

theorem lazyCoordinateLaw_atom_le {μ : ℝ} (hμ : μ ≤ 1 / 2) (j : Fin 3) :
    lazyCoordinateLaw μ {j} ≤ ENNReal.ofReal (1 - μ) := by
  rw [lazyCoordinateLaw_singleton]
  apply ENNReal.ofReal_le_ofReal
  unfold lazyBitWeight
  split <;> linarith

/-- On a finite product, probabilities of an event are the sum of the
products of the corresponding coordinate masses. -/
theorem pi_measureReal_eq_weighted_sum {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (s : Set (Fin n → Ω)) :
    (Measure.pi (fun _ : Fin n => μ)).real s =
      ∑ x : Fin n → Ω, if x ∈ s then ∏ i, μ.real {x i} else 0 := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  have h (x : Fin n → Ω) : ν.real {x} = ∏ i, μ.real {x i} := by
    rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  rw [← sum_filter]
  have heq : (↑(univ.filter fun x => x ∈ s) : Set (Fin n → Ω)) = s := by ext x; simp
  simp_rw [← h]
  rw [sum_measureReal_singleton, heq]

private theorem faithful_mod_large_prime {P n : ℕ}
    {Ω : Type*} (a : Fin n → ℤ) (z : Ω → ℤ) (hz : ∀ x, (z x).natAbs ≤ 1)
    (hP : ∑ i, (a i).natAbs < P) (x : Fin n → Ω) :
    ((∑ i, a i * z (x i) : ℤ) : ZMod P) = 0 ↔ ∑ i, a i * z (x i) = 0 := by
  have hterm (i : Fin n) : |a i * z (x i)| ≤ |a i| := by
    have hzx : |z (x i)| ≤ 1 := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hz (x i)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hzx
  have hsum : (∑ i, a i * z (x i) : ℤ).natAbs ≤ ∑ i, (a i).natAbs := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, Nat.cast_sum]
    simp only [Int.natCast_natAbs]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hterm i)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hsum.trans_lt hP)
  · rintro h
    rw [h]
    exact dvd_zero _

/-- An atom of the independent-sign sum as the cycle mean of the corresponding
real characteristic-function product. -/
theorem auxiliaryAtom_eq_cycle_product {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {P n : ℕ} [NeZero P] (a : Fin n → ℤ) (z : Ω → ℤ)
    (hP : ∑ i, (a i).natAbs < P) (hz : ∀ x, (z x).natAbs ≤ 1)
    (φ : ZMod P → ℝ)
    (hφ : ∀ t, (∑ x, (ν.real {x} : ℂ) * ZMod.stdAddChar ((z x : ZMod P) * t)) = (φ t : ℂ)) :
    (auxiliaryAtom ν (fun x => (z x : ℝ)) (fun i => (a i : ℝ))).toReal =
      (∑ t : ZMod P, ∏ i, φ ((a i : ZMod P) * t)) / (P : ℝ) := by
  classical
  have h := weighted_zero_sum_fourier a z (fun x => (ν.real {x} : ℂ))
    (faithful_mod_large_prime a z hz hP)
  have hmul (i : Fin n) (x : Ω) (t : ZMod P) :
      (((a i * z x : ℤ) : ZMod P) * t) = (z x : ZMod P) * ((a i : ZMod P) * t) := by
    rw [Int.cast_mul]
    ring
  simp_rw [hmul, hφ, ← Complex.ofReal_prod, ← Complex.ofReal_sum] at h
  have hreal := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.natCast_re] at hreal
  have hr : 0 < (P : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  rw [auxiliaryAtom, ← measureReal_def, pi_measureReal_eq_weighted_sum]
  apply (eq_div_iff hr.ne').mpr
  rw [mul_comm]
  convert hreal.symm using 2
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro x _
  have hx : (∑ i, (a i : ℝ) * (z (x i) : ℝ)) = 0 ↔ ∑ i, a i * z (x i) = 0 := by
    exact_mod_cast Iff.rfl
  simp only [Set.mem_ofPred_eq, hx]
  by_cases he : ∑ i, a i * z (x i) = 0
  · rw [ite_eq_left he, ite_eq_left he, Complex.ofReal_re]
  · simp [he]

private theorem faithful_target_mod_large_prime {P n : ℕ}
    {Ω : Type*} (a : Fin n → ℤ) (z : Ω → ℤ) (hz : ∀ x, (z x).natAbs ≤ 1)
    (s : ℤ) (hP : (∑ i, (a i).natAbs) + s.natAbs < P) (x : Fin n → Ω) :
    ((∑ i, a i * z (x i) : ℤ) : ZMod P) - (s : ZMod P) = 0 ↔
      ∑ i, a i * z (x i) = s := by
  have hterm (i : Fin n) : |a i * z (x i)| ≤ |a i| := by
    have hzx : |z (x i)| ≤ 1 := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hz (x i)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hzx
  have hsumR : |∑ i, a i * z (x i)| ≤ ∑ i, |a i| :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hterm i)
  have hsum : ((∑ i, a i * z (x i) : ℤ) - s).natAbs ≤ (∑ i, (a i).natAbs) + s.natAbs := by
    rw [← Nat.cast_le (α := ℤ), Nat.cast_add, Int.natCast_natAbs, Nat.cast_sum]
    simp only [Int.natCast_natAbs]
    exact (abs_sub _ _).trans (add_le_add hsumR le_rfl)
  rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, ← sub_eq_zero]
  constructor
  · intro h
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hsum.trans_lt hP)
  · rintro h
    rw [h]
    exact dvd_zero _

/-- The probability of an integer target as a finite Fourier mean. -/
theorem measureReal_sum_eq_cycle_product {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {P n : ℕ} [NeZero P] (a : Fin n → ℤ) (z : Ω → ℤ) (s : ℤ)
    (hP : (∑ i, (a i).natAbs) + s.natAbs < P) (hz : ∀ x, (z x).natAbs ≤ 1)
    (φ : ZMod P → ℝ)
    (hφ : ∀ t, (∑ x, (ν.real {x} : ℂ) * ZMod.stdAddChar ((z x : ZMod P) * t)) = (φ t : ℂ)) :
    (Measure.pi (fun _ : Fin n => ν)).real {x | ∑ i, (a i : ℝ) * (z (x i) : ℝ) = (s : ℝ)} =
      (∑ t : ZMod P, (ZMod.stdAddChar (-(s : ZMod P) * t)).re *
        ∏ i, φ ((a i : ZMod P) * t)) / (P : ℝ) := by
  classical
  have h := weighted_sum_at_fourier a z (fun x => (ν.real {x} : ℂ)) s
    (faithful_target_mod_large_prime a z hz s hP)
  have hmul (i : Fin n) (x : Ω) (t : ZMod P) :
      (((a i * z x : ℤ) : ZMod P) * t) = (z x : ZMod P) * ((a i : ZMod P) * t) := by
    rw [Int.cast_mul]
    ring
  simp_rw [hmul, hφ, ← Complex.ofReal_prod] at h
  have hreal := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.natCast_im,
    zero_mul, mul_zero, sub_zero, Complex.natCast_re] at hreal
  have hr : 0 < (P : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  rw [pi_measureReal_eq_weighted_sum]
  apply (eq_div_iff hr.ne').mpr
  rw [mul_comm]
  convert hreal.symm using 2
  apply sum_congr rfl
  intro x _
  have hx : (∑ i, (a i : ℝ) * (z (x i) : ℝ)) = (s : ℝ) ↔ ∑ i, a i * z (x i) = s := by
    exact_mod_cast Iff.rfl
  simp only [Set.mem_ofPred_eq, hx]
  by_cases he : ∑ i, a i * z (x i) = s
  · simp only [ite_eq_left he, ← Complex.ofReal_prod, Complex.ofReal_re]
  · simp [he]

end BooleanThreshold
