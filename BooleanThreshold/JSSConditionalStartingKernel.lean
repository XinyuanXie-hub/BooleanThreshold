module

public import BooleanThreshold.JSSConditionalFejer
public import BooleanThreshold.JSSConditionalSliceAverage
import BooleanThreshold.JSSConditionalFourierMoment
import Mathlib.Analysis.Real.Pi.Bounds

public section

open Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- Small integer displacements remain in the central peak of the Fejér kernel. -/
theorem fejerKernel_intCast_ge {P M : ℕ} [NeZero P] (hM : 0 < M)
    {z : ℤ} (hz : 16 * (M : ℝ) * |(z : ℝ)| ≤ (P : ℝ)) :
    (M : ℝ) / (4 * (P : ℝ)) ≤ fejerKernel M (z : ZMod P) := by
  have hP : 0 < (P : ℝ) := by exact_mod_cast NeZero.pos P
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hphase (j : ℕ) (hj : j ∈ range M) :
      1 / 2 ≤ (ZMod.stdAddChar ((j : ZMod P) * (z : ZMod P))).re := by
    let u := 2 * Real.pi * (j : ℝ) * (z : ℝ) / (P : ℝ)
    have harg : |u| ≤ 1 / 2 := by
      have harg' : |u| = (2 * Real.pi * (j : ℝ) * |(z : ℝ)|) / (P : ℝ) := by
        dsimp [u]
        simp only [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos, abs_of_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j),
          abs_of_pos hP]
      rw [harg', div_le_iff₀ hP]
      calc
        _ ≤ 8 * (M : ℝ) * |(z : ℝ)| := by
          have hj' : (j : ℝ) ≤ M := by exact_mod_cast (mem_range.mp hj).le
          have hπ : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul hπ hj' (Nat.cast_nonneg _) (by norm_num)
        _ ≤ _ := by linarith only [hz]
    have heq : ZMod.stdAddChar ((j : ZMod P) * (z : ZMod P)) =
        Complex.exp ((u : ℂ) * Complex.I) := by
      rw [show (j : ZMod P) * (z : ZMod P) = (((j : ℤ) * z : ℤ) : ZMod P) by push_cast; rfl,
        ZMod.stdAddChar_coe]
      congr 1
      dsimp [u]
      push_cast
      ring
    rw [heq, Complex.exp_ofReal_mul_I_re]
    have hu : u ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) harg 2
    linarith only [hu, Real.one_sub_sq_div_two_le_cos (x := u)]
  let S := ∑ j ∈ range M, ZMod.stdAddChar ((j : ZMod P) * (z : ZMod P))
  have hS : (M : ℝ) / 2 ≤ S.re := by
    dsimp [S]
    rw [Complex.re_sum]
    calc
      _ = ∑ _j ∈ range M, (1 / 2 : ℝ) := by simp [nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ _ := sum_le_sum hphase
  have hNorm : (M : ℝ) / 2 ≤ ‖S‖ := hS.trans (Complex.re_le_norm _)
  unfold fejerKernel
  calc
    _ = ((M : ℝ) / 2) ^ 2 / ((M : ℝ) * (P : ℝ)) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hNorm 2) (by positivity)

private theorem exists_starting_bandwidth {n P : ℕ} [NeZero P] (hn : 0 < n)
    (hSize : 2 ≤ (P : ℝ) / (64 * Real.sqrt (n : ℝ))) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ (P : ℝ) / (64 * Real.sqrt (n : ℝ)) ∧
      ∀ z : ℤ, |(z : ℝ)| ≤ 3 * Real.sqrt (n : ℝ) →
        1 / (512 * Real.sqrt (n : ℝ)) ≤ fejerKernel M (z : ZMod P) := by
  let R := Real.sqrt (n : ℝ)
  let x := (P : ℝ) / (64 * R)
  let M := ⌊x⌋₊
  have hR : 0 < R := by dsimp [R]; positivity
  have hP : 0 < (P : ℝ) := by exact_mod_cast NeZero.pos P
  have hx : (0 : ℝ) ≤ x := by dsimp [x]; positivity
  have hM : 0 < M := by
    apply Nat.floor_pos.mpr
    exact (by norm_num : (1 : ℝ) ≤ 2).trans hSize
  have hMhi : (M : ℝ) ≤ x := Nat.floor_le hx
  have hMlo : x / 2 ≤ (M : ℝ) := by
    have h := Nat.lt_floor_add_one x
    change 2 ≤ x at hSize
    linarith
  refine ⟨M, hM, hMhi, fun z hz => ?_⟩
  have hMz : 16 * (M : ℝ) * |(z : ℝ)| ≤ P := by
    calc
      _ ≤ 16 * x * (3 * R) := by gcongr
      _ = (3 / 4 : ℝ) * (P : ℝ) := by dsimp [x]; field_simp; ring
      _ ≤ _ := by linarith
  refine le_trans ?_ (fejerKernel_intCast_ge hM hMz)
  calc
    _ = (x / 2) / (4 * (P : ℝ)) := by
      change 1 / (512 * R) = _
      dsimp [x]
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hMlo (by positivity)

/-- A cyclic Fejér kernel can be both band-limited to a prescribed small
frequency proportion and bounded below on all displacements needed to
represent an integer small ball of radius twice the square root. -/
theorem eventually_exists_starting_fejer_bandwidth {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : ℕ) [NeZero P], 4 * n ^ 2 ≤ P →
      ∃ M : ℕ, 0 < M ∧ 2 * M ≤ P ∧ (M : ℝ) ≤ β * (P : ℝ) ∧
        ∀ z : ℤ, |(z : ℝ)| ≤ 3 * Real.sqrt (n : ℝ) →
          1 / (512 * Real.sqrt (n : ℝ)) ≤ fejerKernel M (z : ZMod P) := by
  have hs := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 32, hs.eventually (eventually_ge_atTop (1 / (64 * β)))]
    with n hn hRoot
  intro P _ hP
  have hN₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hR₁ : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hN₁
  have hR : 0 < Real.sqrt (n : ℝ) := zero_lt_one.trans_le hR₁
  have hN : 0 < n := by omega
  have hP' : (4 : ℝ) * (n : ℝ) ^ 2 ≤ P := by exact_mod_cast hP
  have hSize : (2 : ℝ) ≤ (P : ℝ) / (64 * Real.sqrt (n : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hNs : Real.sqrt (n : ℝ) ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr hN₁)
    have h32 : (32 : ℝ) ≤ n := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_right h32 (Nat.cast_nonneg n)
    nlinarith only [hNs, hh, hP']
  obtain ⟨M, hM, hMhi, hMlo⟩ := exists_starting_bandwidth hN hSize
  have hden : 0 < 64 * Real.sqrt (n : ℝ) := by positivity
  have hM₁ : 2 * M ≤ P := by
    have hMhalf : (M : ℝ) ≤ (P : ℝ) / 2 := hMhi.trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith))
    exact_mod_cast (show 2 * (M : ℝ) ≤ (P : ℝ) by linarith)
  have hM₂ : (M : ℝ) ≤ β * (P : ℝ) := by
    change 1 / (64 * β) ≤ Real.sqrt (n : ℝ) at hRoot
    refine hMhi.trans ((div_le_iff₀ hden).mpr ?_)
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * β)).mp hRoot
    have hh := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg P)
    nlinarith only [hh]
  exact ⟨M, hM, hM₁, hM₂, hMlo⟩

/-- Extend a finite list of integer coordinates by zero after taking residues. -/
@[expose] def cyclicIntegerCoordinates {n P : ℕ} (w : Fin n → ℤ) (i : ℕ) : ZMod P :=
  if hi : i < n then (w ⟨i, hi⟩ : ZMod P) else 0

/-- A small ball for signed integer coefficients forces a large translate of
the cyclic subset average with the Fejér starting kernel. The common translation
and the factor two in a signed sum are absorbed into the center and radius. -/
theorem exists_fejer_sliceAverage_ge_smallBall {n P M : ℕ} [NeZero P] (hn : 0 < n)
    (hker : ∀ z : ℤ, |(z : ℝ)| ≤ 3 * Real.sqrt (n : ℝ) →
      1 / (512 * Real.sqrt (n : ℝ)) ≤ fejerKernel M (z : ZMod P))
    (m : Fin (n + 1)) (w : Fin n → ℤ) (z : ℝ) :
    ∃ t : ZMod P, ((uniformOn (signSlice n m)).real
      {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * Real.sqrt (n : ℝ)}) /
      (512 * Real.sqrt (n : ℝ)) ≤
        sliceAverage (cyclicIntegerCoordinates (P := P) w)
          (fejerKernel M) n m.val t := by
  classical
  let z₀ := (z + ∑ i, (w i : ℝ)) / 2
  let z₁ : ℤ := ⌊z₀⌋
  let y : ZMod P := -(z₁ : ZMod P)
  let a := cyclicIntegerCoordinates (P := P) w
  let U : Set (Fin n → Bool) := {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * Real.sqrt (n : ℝ)}
  let μ := uniformOn (signSlice n m)
  let R := Real.sqrt (n : ℝ)
  let f (b : Fin n → Bool) := fejerKernel M (y + ∑ i ∈ univ.filter (fun i => b i), a i.val)
  let c := 1 / (512 * R)
  have hs : |z₀ - (z₁ : ℝ)| ≤ 1 := by
    have hlo : (z₁ : ℝ) ≤ z₀ := Int.floor_le _
    have hhi : z₀ < (z₁ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  have hR₁ : 1 ≤ R := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
  have hpoint (b : Fin n → Bool) : U.indicator (fun _ => c) b ≤ f b := by
    by_cases hb : b ∈ U
    · rw [Set.indicator_of_mem hb]
      let h : ℤ := ∑ i ∈ univ.filter (fun i => b i), w i
      have hSigned : signSum (fun i => (w i : ℝ)) b = 2 * (h : ℝ) - ∑ i, (w i : ℝ) := by
        have he : signSum (fun i => (w i : ℝ)) b = ∑ i, if b i then (w i : ℝ) else -(w i : ℝ) := by
          unfold signSum
          exact sum_congr rfl fun i _ => by cases b i <;> simp
        rw [he, signed_sum_eq_subset_sum]
        dsimp [h]
        simp_rw [Int.cast_sum, mul_sum, two_mul]
        ring
      have hCyc : (h : ZMod P) = ∑ i ∈ univ.filter (fun i => b i), a i.val := by
        dsimp [h]
        rw [Int.cast_sum]
        exact sum_congr rfl fun i _ => by simp [a, cyclicIntegerCoordinates]
      have hb' : |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * R := hb
      have hh : |(h : ℝ) - z₀| ≤ R := by
        rw [hSigned, show 2 * (h : ℝ) - (∑ i, (w i : ℝ)) - z = 2 * ((h : ℝ) - z₀) by
          dsimp [z₀]
          ring, abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))] at hb'
        linarith only [hb']
      have hloc : |((h - z₁ : ℤ) : ℝ)| ≤ 3 * R := by
        rw [Int.cast_sub, show (h : ℝ) - (z₁ : ℝ) = ((h : ℝ) - z₀) + (z₀ - z₁) by ring]
        exact (abs_add_le _ _).trans (by linarith only [hh, hs, hR₁])
      have hf : f b = fejerKernel M ((h - z₁ : ℤ) : ZMod P) := by
        dsimp [f, y]
        rw [Int.cast_sub, hCyc, sub_eq_add_neg, add_comm]
      rw [hf]
      exact hker _ hloc
    · rw [Set.indicator_of_notMem hb]
      exact fejerKernel_nonneg _ _
  have hfI : Integrable f μ := integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  have hgI : Integrable (U.indicator (fun _ => c)) μ :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  have hAvg := integral_mono hgI hfI hpoint
  rw [integral_indicator_const c U.toFinite.measurableSet, smul_eq_mul] at hAvg
  change μ.real U * c ≤ ∫ b, fejerKernel M (y + ∑ i ∈ univ.filter (fun i => b i), a i.val) ∂μ at hAvg
  rw [show μ = uniformOn (signSlice n m) by rfl, integral_signSlice_eq_sliceAverage] at hAvg
  exact ⟨y, by simpa only [a, c, mul_one_div] using hAvg⟩

/-- Taking a fixed-size subset average of translates cannot create a
frequency outside the support of the starting function. -/
theorem dft_sliceAverage_eq_zero {P : ℕ} [NeZero P] (X : ℕ → ZMod P)
    (f : ZMod P → ℝ) (ℓ s : ℕ) (k : ZMod P)
    (hk : ZMod.dft (fun t => (f t : ℂ)) k = 0) :
    ZMod.dft (fun t => (sliceAverage X f ℓ s t : ℂ)) k = 0 := by
  have hshift (v : ZMod P) : ZMod.dft (fun t => (f (t + v) : ℂ)) k = 0 := by
    rw [dft_cyclicTranslate (fun t => (f t : ℂ)) k v, hk, mul_zero]
  let E := (range ℓ).powersetCard s
  have he : (fun t => (sliceAverage X f ℓ s t : ℂ)) =
      ((ℓ.choose s : ℂ)⁻¹) • ∑ I ∈ E, (fun t => (f (t + ∑ i ∈ I, X i) : ℂ)) := by
    funext t
    simp only [sliceAverage, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, E]
    push_cast
    ring
  rw [he, map_smul, map_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, hshift, sum_const_zero, smul_zero]

end BooleanThreshold
