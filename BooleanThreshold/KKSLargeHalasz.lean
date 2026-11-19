module

public import BooleanThreshold.KKSLargeAtom
public import BooleanThreshold.KKSLargeRadius
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Nat.Prime.Infinite

public section

open Finset MeasureTheory ProbabilityTheory AddChar Complex
open scoped BigOperators ENNReal

namespace BooleanThreshold

private theorem standard_character_neg {P : ℕ} [NeZero P] (t : ZMod P) :
    ZMod.stdAddChar (-t) = star (ZMod.stdAddChar t) := by
  have h : ZMod.stdAddChar t ≠ 0 := by
    intro h
    simpa [h] using norm_standard_character t
  apply mul_left_cancel₀ h
  rw [← map_add_eq_mul, add_neg_cancel, map_zero_eq_one]
  change 1 = ZMod.stdAddChar t * (starRingEnd ℂ) (ZMod.stdAddChar t)
  rw [Complex.mul_conj', norm_standard_character]
  norm_num

private theorem zeroAtom_eq_cycle_product {P n : ℕ} [NeZero P] (a : Fin n → ℤ)
    (hP : ∑ i, (a i).natAbs < P) :
    (zeroAtom (fun i => (a i : ℝ))).toReal =
      (∑ t : ZMod P, ∏ i, (ZMod.stdAddChar ((a i : ZMod P) * t)).re) / P := by
  let ν : Measure Bool := uniformOn Set.univ
  have hν (b : Bool) : ν.real {b} = 1 / 2 := by
    rw [uniformOn_univ_real_eq_card]
    simp
  have hφ (t : ZMod P) :
      (∑ x : Bool, (ν.real {x} : ℂ) * ZMod.stdAddChar ((signedBit x : ZMod P) * t)) =
        ((ZMod.stdAddChar t).re : ℂ) := by
    rw [Fintype.sum_bool, hν, hν]
    simp [signedBit, standard_character_neg]
    apply Complex.ext <;> simp <;> ring
  have hcast (b : Bool) : (signedBit b : ℝ) = if b then 1 else -1 := by
    cases b <;> norm_num [signedBit]
  have heq : auxiliaryAtom ν (fun x => (signedBit x : ℝ)) (fun i => (a i : ℝ)) =
      zeroAtom (fun i => (a i : ℝ)) := by
    rw [auxiliaryAtom, zeroAtom, uniformOn_signCube_apply, pi_uniformOn_univ]
    simp [realSigns, hcast]
  rw [← heq]
  exact auxiliaryAtom_eq_cycle_product ν a signedBit hP
    (fun x => by cases x <;> decide) _ hφ

private theorem lazyAtom_eq_cycle_product {P n : ℕ} [NeZero P] (a : Fin n → ℤ)
    (hP : ∑ i, (a i).natAbs < P) {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) :
    (auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ))).toReal =
      (∑ t : ZMod P, ∏ i, (1 - μ + μ * (ZMod.stdAddChar ((a i : ZMod P) * t)).re)) / P := by
  let _ := lazyCoordinateLaw_probability hμ₀ hμ₁
  have hν (b : Fin 3) : (lazyCoordinateLaw μ).real {b} = lazyBitWeight μ b := by
    rw [measureReal_def, lazyCoordinateLaw_singleton, ENNReal.toReal_ofReal
      (lazyBitWeight_nonneg hμ₀ hμ₁ b)]
  refine auxiliaryAtom_eq_cycle_product (lazyCoordinateLaw μ) a lazyBit hP (by decide)
    (fun t : ZMod P => 1 - μ + μ * (ZMod.stdAddChar t).re) ?_
  intro t
  rw [Fin.sum_univ_three]
  simp [hν, lazyBitWeight, lazyBit, standard_character_neg]
  apply Complex.ext <;> simp <;> ring

private theorem abs_le_exp_variance (x : ℝ) :
    |x| ≤ Real.exp ((x ^ 2 - 1) / 2) := by
  rw [← sq_le_sq₀ (abs_nonneg _) (Real.exp_nonneg _), sq_abs]
  calc
    _ ≤ Real.exp (x ^ 2 - 1) := by linarith only [Real.add_one_le_exp (x ^ 2 - 1)]
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

private theorem standard_character_two_re {P : ℕ} [NeZero P] (t : ZMod P) :
    (ZMod.stdAddChar (2 * t)).re = 2 * (ZMod.stdAddChar t).re ^ 2 - 1 := by
  have h := congrArg (fun r : ℝ => r ^ 2) (norm_standard_character t)
  rw [Complex.sq_norm, Complex.normSq_apply] at h
  rw [two_mul, map_add_eq_mul, Complex.mul_re]
  nlinarith only [h]

private theorem sign_product_le_exp_energy {P n : ℕ} [NeZero P] (b : Fin n → ZMod P) (t : ZMod P) :
    (∏ i, (ZMod.stdAddChar (b i * t)).re) ≤ Real.exp (-characterEnergy b (2 * t)) := by
  calc
    _ ≤ |∏ i, (ZMod.stdAddChar (b i * t)).re| := le_abs_self _
    _ = ∏ i, |(ZMod.stdAddChar (b i * t)).re| := by simp only [abs_prod]
    _ ≤ ∏ i, Real.exp (-(1 - (ZMod.stdAddChar (b i * (2 * t))).re) / 4) := by
      apply prod_le_prod₀ (fun i _ => abs_nonneg _)
      intro i _
      rw [show b i * (2 * t) = 2 * (b i * t) by ring, standard_character_two_re]
      convert abs_le_exp_variance ((ZMod.stdAddChar (b i * t)).re) using 2
      ring
    _ = _ := by
      rw [← Real.exp_sum, characterEnergy]
      congr 1
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib, neg_mul]

/-- A Fourier upper bound on the dense sign atom. -/
theorem zeroAtom_le_exp_energy_mean {P n : ℕ} [NeZero P] (hP : P.Prime)
    (hP₂ : 2 < P) (a : Fin n → ℤ) (hsize : ∑ i, (a i).natAbs < P) :
    (zeroAtom (fun i => (a i : ℝ))).toReal ≤
      (∑ t : ZMod P, Real.exp (-characterEnergy (fun i => (a i : ZMod P)) t)) / P := by
  let _ := Fact.mk hP
  let b (i : Fin n) : ZMod P := a i
  have h2 : (2 : ZMod P) ≠ 0 := by
    intro hz
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 P).mp (by exact_mod_cast hz)
    have hh := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hP₂)
    norm_num at hh
  rw [zeroAtom_eq_cycle_product a hsize]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ t : ZMod P, Real.exp (-characterEnergy b (2 * t)) :=
      sum_le_sum fun t _ => sign_product_le_exp_energy b t
    _ = _ := Fintype.sum_equiv (Equiv.mulLeft₀ 2 h2) _ _ (fun _ => rfl)

private theorem exp_le_lazy_chord (β y : ℝ) (hy₀ : -1 ≤ y) (hy₁ : y ≤ 1) :
    let μ := (1 - Real.exp (-β / 2)) / 2
    Real.exp (-β * (1 - y) / 4) ≤ 1 - μ + μ * y := by
  let t := (1 - y) / 2
  have ht₀ : 0 ≤ t := by dsimp [t]; linarith
  have ht₁ : t ≤ 1 := by dsimp [t]; linarith
  have hh := convexOn_exp.2
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-β / 2))
      (show 0 ≤ 1 - t by linarith) ht₀ (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hh
  let μ := (1 - Real.exp (-β / 2)) / 2
  change Real.exp (-β * (1 - y) / 4) ≤ 1 - μ + μ * y
  calc
    _ = Real.exp (t * (-β / 2)) := by
      congr 1
      dsimp [t]
      ring
    _ ≤ 1 - t + t * Real.exp (-β / 2) := hh
    _ = _ := by dsimp [t, μ]; ring

private theorem exp_energy_le_lazy_product {P n : ℕ} [NeZero P]
    (β : ℝ) (b : Fin n → ZMod P) (t : ZMod P) :
    let μ := (1 - Real.exp (-β / 2)) / 2
    Real.exp (-β * characterEnergy b t) ≤
      ∏ i, (1 - μ + μ * (ZMod.stdAddChar (b i * t)).re) := by
  intro μ
  have hsum : -β * characterEnergy b t =
      ∑ i, -β * (1 - (ZMod.stdAddChar (b i * t)).re) / 4 := by
    simp only [characterEnergy, div_eq_mul_inv, ← sum_mul, ← mul_sum, mul_assoc]
  rw [hsum, Real.exp_sum]
  apply prod_le_prod₀ (fun _ _ => Real.exp_nonneg _)
  intro i _
  have hre := Complex.abs_re_le_norm (ZMod.stdAddChar (b i * t))
  rw [norm_standard_character, abs_le] at hre
  exact exp_le_lazy_chord β _ hre.1 hre.2

/-- Chernoff's estimate on the volume of sublevel sets in the Halász argument. -/
theorem characterEnergy_sublevel_le_lazyAtom {P n : ℕ} [NeZero P] (hP : 0 < P)
    (a : Fin n → ℤ) (hsize : ∑ i, (a i).natAbs < P)
    (β : ℝ) (hβ : 0 ≤ β) (x : ℝ) :
    let μ := (1 - Real.exp (-β / 2)) / 2
    sublevelFraction (characterEnergy (fun i => (a i : ZMod P))) x ≤
      Real.exp (β * x) *
        (auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ))).toReal := by
  classical
  intro μ
  let b (i : Fin n) : ZMod P := a i
  let f := characterEnergy b
  let A := (univ : Finset (ZMod P)).filter fun t => f t ≤ x
  let q := (auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ))).toReal
  have hμ₀ : 0 ≤ μ := by
    dsimp [μ]
    have hh := Real.exp_le_one_iff.mpr (show -β / 2 ≤ 0 by linarith)
    linarith
  have hμ₁ : μ ≤ 1 := by dsimp [μ]; linarith [Real.exp_pos (-β / 2)]
  have hP' : 0 < (P : ℝ) := by exact_mod_cast hP
  have hsum : (A.card : ℝ) * Real.exp (-β * x) ≤ q * (P : ℝ) := by
    calc
      _ = ∑ _t ∈ A, Real.exp (-β * x) := by simp
      _ ≤ ∑ t ∈ A, Real.exp (-β * f t) := by
        apply sum_le_sum
        intro t ht
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (mem_filter.mp ht).2 (by linarith))
      _ ≤ ∑ t : ZMod P, Real.exp (-β * f t) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Real.exp_nonneg _)
      _ ≤ ∑ t : ZMod P, ∏ i, (1 - μ + μ * (ZMod.stdAddChar (b i * t)).re) :=
        sum_le_sum fun t _ => exp_energy_le_lazy_product β b t
      _ = _ := by
        change _ = (auxiliaryAtom (lazyCoordinateLaw μ) _ _).toReal * _
        rw [lazyAtom_eq_cycle_product a hsize hμ₀ hμ₁, div_mul_cancel₀ _ hP'.ne']
  change (A.card : ℝ) / P ≤ Real.exp (β * x) * q
  rw [neg_mul, Real.exp_neg] at hsum
  have hdiv : (A.card : ℝ) / Real.exp (β * x) ≤ q * (P : ℝ) := by
    simpa [div_eq_mul_inv] using hsum
  apply (div_le_iff₀ hP').mpr
  simpa [mul_assoc, mul_left_comm, mul_comm] using (div_le_iff₀ (Real.exp_pos (β * x))).mp hdiv

/-- For integer coefficients with sufficiently large support, the ordinary sign
atom is bounded by an arbitrarily small multiple of a fixed lazy-sign atom. -/
theorem exists_lazy_atom_comparison_int {τ : ℝ} (hτ : 0 < τ) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 / 2 ∧ ∃ K : ℕ, ∀ n (a : Fin n → ℤ),
      K < (univ.filter fun i => a i ≠ 0).card →
      zeroAtom (fun i => (a i : ℝ)) ≤
        ENNReal.ofReal τ * auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ)) := by
  let G := 1 - Real.exp (-(1 / 4 : ℝ))
  let C := Real.exp (1 / 2) / G
  have hG : 0 < G := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hC : 0 < C := div_pos (Real.exp_pos _) hG
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (4 * C / τ))
  have hkR : 0 < (k : ℝ) := zero_lt_one.trans ((le_max_left _ _).trans_lt hk)
  have hkN : 0 < k := by exact_mod_cast hkR
  have hfit_k : C / (k : ℝ) ≤ τ / 4 := by
    have hh := (div_lt_iff₀ hτ).mp ((le_max_right _ _).trans_lt hk)
    apply (div_le_iff₀ hkR).mpr
    linarith
  obtain ⟨S, hS⟩ := exists_nat_ge (4 * Real.log (4 * C / τ))
  have hfit_S : C * Real.exp (-(S : ℝ) / 4) ≤ τ / 4 := by
    have he : Real.exp (-(S : ℝ) / 4) ≤ Real.exp (-Real.log (4 * C / τ)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by positivity)] at he
    have hh := mul_le_mul_of_nonneg_left he hC.le
    have hc : C * (4 * C / τ)⁻¹ = τ / 4 := by field_simp
    exact hh.trans_eq hc
  let β := 1 / (2 * (k : ℝ) ^ 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβk : β * (k : ℝ) ^ 2 ≤ 1 / 2 := by
    have hh : β * (k : ℝ) ^ 2 = 1 / 2 := by
      dsimp [β]
      field_simp [hkR.ne']
    exact hh.le
  let μ := (1 - Real.exp (-β / 2)) / 2
  have hμpos : 0 < μ := by
    have he := Real.exp_lt_one_iff.mpr (show -β / 2 < 0 by linarith)
    dsimp [μ]
    linarith
  have hμhalf : μ ≤ 1 / 2 := by dsimp [μ]; linarith [Real.exp_pos (-β / 2)]
  let _ := lazyCoordinateLaw_probability hμpos.le (by linarith : μ ≤ 1)
  let K := 4 * k ^ 2 * (S + 1)
  refine ⟨μ, hμpos, hμhalf, K, fun n a ha => ?_⟩
  let p := (zeroAtom (fun i => (a i : ℝ))).toReal
  let q := (auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ))).toReal
  have hpTop : zeroAtom (fun i => (a i : ℝ)) ≠ ⊤ := by
    rw [zeroAtom, uniformOn_signCube_apply]
    exact measure_ne_top _ _
  have hqTop : auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ)) ≠ ⊤ := by
    rw [auxiliaryAtom]
    exact measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal hpTop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqTop)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ.le]
  change p ≤ τ * q
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  by_cases hp : p = 0
  · rw [hp]
    positivity
  have hp' : 0 < p := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp)
  obtain ⟨H, hH⟩ := exists_nat_ge (2 / (G * p))
  obtain ⟨P, hPsize, hP⟩ :=
    Nat.exists_infinite_primes (max H (max 3 ((∑ i, (a i).natAbs) + 1)))
  let _ : NeZero P := ⟨hP.ne_zero⟩
  have hHle : H ≤ P := (le_max_left _ _).trans hPsize
  have hP₂ : 2 < P := by
    have hh : 3 ≤ P := (le_max_left _ _).trans ((le_max_right _ _).trans hPsize)
    omega
  have hsize : (∑ i, (a i).natAbs) < P :=
    lt_of_lt_of_le (Nat.lt_succ_self _)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hPsize))
  let b (i : Fin n) : ZMod P := a i
  have hsupp : (univ.filter fun i => b i ≠ 0) = (univ.filter fun i => a i ≠ 0) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, not_iff_not]
    change ((a i : ZMod P) = 0) ↔ a i = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨fun hi => Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hi ?_, fun hi => hi ▸ dvd_zero _⟩
    simpa using (single_le_sum (fun j _ => Nat.zero_le (a j).natAbs) (mem_univ i)).trans_lt hsize
  have hGrow (j : ℕ) (hj : j < S) :
      sublevelFraction (characterEnergy b) ((j : ℝ) + 1) ≤
        sublevelFraction (characterEnergy b) ((k : ℝ) ^ 2 * ((j : ℝ) + 1)) / k + 1 / P := by
    apply characterEnergy_sublevel_le hP b _ (by positivity) k hkN
    rw [hsupp]
    have hjR : (j : ℝ) + 1 ≤ (S : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hj.le 1
    have haR : 4 * (k : ℝ) ^ 2 * ((S : ℝ) + 1) <
        ((univ.filter fun i => a i ≠ 0).card : ℝ) := by exact_mod_cast ha
    have hh := mul_le_mul_of_nonneg_left hjR (show 0 ≤ (k : ℝ) ^ 2 by positivity)
    linarith
  have hMarkov (x : ℝ) :
      sublevelFraction (characterEnergy b) x ≤ Real.exp (β * x) * q :=
    characterEnergy_sublevel_le_lazyAtom hP.pos a hsize β hβ.le x
  have hpmean := zeroAtom_le_exp_energy_mean hP hP₂ a hsize
  have hlevels := mean_exp_bound_from_levels hP.pos (characterEnergy b)
    (characterEnergy_nonneg b) β q hβ.le hq k hkN hβk S hMarkov hGrow
  have hP' : 0 < (P : ℝ) := by exact_mod_cast hP.pos
  have herror : 1 / ((P : ℝ) * G) ≤ p / 2 := by
    have hh' : (H : ℝ) ≤ P := by exact_mod_cast hHle
    have hh := (div_le_iff₀ (mul_pos hG hp')).mp (hH.trans hh')
    apply (div_le_iff₀ (mul_pos hP' hG)).mpr
    linarith
  have hcoef : C / (k : ℝ) + C * Real.exp (-(S : ℝ) / 4) ≤ τ / 2 := by linarith
  have hpbound : p ≤ τ / 2 * q + p / 2 := by
    calc
      _ ≤ _ := hpmean
      _ ≤ _ := hlevels
      _ = (C / (k : ℝ) + C * Real.exp (-(S : ℝ) / 4)) * q + 1 / ((P : ℝ) * G) := by
        dsimp [C, G]
        have hg : 1 - Real.exp (-(1 / 4 : ℝ)) ≠ 0 := hG.ne'
        field_simp [hg, hP'.ne', hkR.ne']
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoef hq) herror
  linarith

end BooleanThreshold
