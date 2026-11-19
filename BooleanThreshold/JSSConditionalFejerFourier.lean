module

public import BooleanThreshold.JSSConditionalFejer
public import BooleanThreshold.JSSConditionalFourierMoment
public import BooleanThreshold.KKSLargeFourier
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators Classical ZMod

namespace BooleanThreshold

private theorem fejer_sum_square {P : ℕ} [NeZero P] (M : ℕ) (t : ZMod P) :
    (↑(‖∑ i ∈ Finset.range M, ZMod.stdAddChar ((i : ZMod P) * t)‖ ^ 2) : ℂ) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, ZMod.stdAddChar (((i : ZMod P) - (j : ZMod P)) * t) := by
  rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [conj_stdAddChar, ← AddChar.map_add_eq_mul, sub_mul, sub_eq_add_neg]

private theorem dft_fejerKernel_eq_pair_count {P M : ℕ} [NeZero P] (hM : 0 < M) (k : ZMod P) :
    𝓕 (fun t : ZMod P => (fejerKernel M t : ℂ)) k =
      (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, if (i : ZMod P) - j = k then (1 : ℂ) else 0) /
        (M : ℂ) := by
  let F (t : ZMod P) (i j : ℕ) :=
    ZMod.stdAddChar (-(t * k)) * ZMod.stdAddChar (((i : ZMod P) - (j : ZMod P)) * t)
  have hs (t : ZMod P) :
      ZMod.stdAddChar (-(t * k)) * (fejerKernel M t : ℂ) =
        (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, F t i j) / ((M : ℂ) * (P : ℂ)) := by
    simp only [fejerKernel, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
      fejer_sum_square, ← mul_div_assoc, Finset.mul_sum, F]
  have hswap :
      (∑ t : ZMod P, ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, F t i j) =
        ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, ∑ t : ZMod P, F t i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hf (i j : ℕ) :
      (∑ t : ZMod P, F t i j) = (if (i : ZMod P) - j = k then (1 : ℂ) else 0) * (P : ℂ) := by
    simp only [F, ← AddChar.map_add_eq_mul]
    have he (t : ZMod P) :
        -(t * k) + ((i : ZMod P) - j) * t = ((i : ZMod P) - j - k) * t := by ring
    simp_rw [he]
    simp only [sum_standard_mul_character, sub_eq_zero]
    split <;> simp
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, hs, ← Finset.sum_div, hswap, hf, ← Finset.sum_mul]
  have hP : (P : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne P
  have hM₀ : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hP, hM₀]

private theorem sum_pair_integer_difference {M : ℕ} (d : ℤ) :
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, if (i : ℤ) - j = d then (1 : ℂ) else 0) =
      ((M - d.natAbs : ℕ) : ℂ) := by
  let A := Finset.range M
  let T := (A ×ˢ A).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = d)
  let J := Finset.Ico (max 0 (-d)) (min (M : ℤ) ((M : ℤ) - d))
  have hT : T.card = J.card := by
    symm
    refine Finset.card_bij (fun j _ => ((j + d).toNat, j.toNat)) ?_ ?_ ?_
    · intro j hj
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hj
      have h₀ : 0 ≤ j := (le_max_left _ _).trans hlo
      have h₁ : 0 ≤ j + d := by have h := (le_max_right (0 : ℤ) (-d)).trans hlo; omega
      have h₂ : j < (M : ℤ) := hhi.trans_le (min_le_left _ _)
      have h₃ : j + d < (M : ℤ) := by have h := hhi.trans_le (min_le_right (M : ℤ) _); omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩, ?_⟩
      rw [Int.toNat_of_nonneg h₀, Int.toNat_of_nonneg h₁]
      omega
    · intro j hj j' hj' heq
      have hj₀ := (le_max_left (0 : ℤ) (-d)).trans (Finset.mem_Ico.mp hj).1
      have hj'₀ := (le_max_left (0 : ℤ) (-d)).trans (Finset.mem_Ico.mp hj').1
      have hh := congrArg Prod.snd heq
      omega
    · rintro ⟨i, j⟩ hp
      obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hp
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hm
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      refine ⟨(j : ℤ), Finset.mem_Ico.mpr ⟨max_le ?_ ?_, lt_min ?_ ?_⟩, ?_⟩
      · exact Int.natCast_nonneg _
      · omega
      · exact_mod_cast hj'
      · omega
      · have heq : (j : ℤ) + d = i := by omega
        simp only [heq, Int.toNat_natCast]
  have hJ : J.card = M - d.natAbs := by
    rw [show J = Finset.Ico (max 0 (-d)) (min (M : ℤ) ((M : ℤ) - d)) by rfl, Int.card_Ico]
    by_cases hg : 0 ≤ d
    · rw [max_eq_left (by omega), min_eq_right (by omega)]
      omega
    · rw [max_eq_right (by omega), min_eq_left (by omega)]
      omega
  change (∑ i ∈ A, ∑ j ∈ A, if (i : ℤ) - j = d then (1 : ℂ) else 0) = _
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ => if (p.1 : ℤ) - (p.2 : ℤ) = d then (1 : ℂ) else 0),
    Finset.sum_boole]
  change (T.card : ℂ) = _
  exact congrArg (fun x : ℕ => (x : ℂ)) (hT.trans hJ)

/-- The discrete Fourier coefficients of the normalized Fejér kernel
form the triangular profile on the central frequencies. -/
theorem dft_fejerKernel {P M : ℕ} [NeZero P] (hM : 0 < M) (hband : 2 * M ≤ P) (k : ZMod P) :
    𝓕 (fun t : ZMod P => (fejerKernel M t : ℂ)) k =
      ((M - k.valMinAbs.natAbs : ℕ) : ℂ) / (M : ℂ) := by
  rw [dft_fejerKernel_eq_pair_count hM]
  congr 1
  have he (i j : ℕ) (hi : i ∈ Finset.range M) (hj : j ∈ Finset.range M) :
      (i : ZMod P) - (j : ZMod P) = k ↔ (i : ℤ) - (j : ℤ) = k.valMinAbs := by
      constructor
      · intro h
        apply ((ZMod.valMinAbs_spec k _).mpr ?_).symm
        have hi' := Finset.mem_range.mp hi
        have hj' := Finset.mem_range.mp hj
        refine ⟨?_, ?_⟩
        · push_cast
          exact h.symm
        · exact ⟨by omega, by omega⟩
      · intro h
        have hh := congrArg (fun x : ℤ => (x : ZMod P)) h
        simpa only [Int.cast_sub, Int.cast_natCast, ZMod.coe_valMinAbs] using hh
  calc
    _ = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        if (i : ℤ) - (j : ℤ) = k.valMinAbs then (1 : ℂ) else 0 := by
      exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by simp only [he i j hi hj]
    _ = _ := sum_pair_integer_difference _

/-- The normalized Fejér kernel has unit mass with counting measure. -/
theorem fejerKernel_sum_eq_one {P M : ℕ} [NeZero P] (hM : 0 < M) (hband : 2 * M ≤ P) :
    (∑ t : ZMod P, fejerKernel M t) = 1 := by
  have h := dft_fejerKernel hM hband (0 : ZMod P)
  have hM₀ : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [ZMod.dft_apply_zero, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.sub_zero, div_self hM₀] at h
  exact_mod_cast h

theorem dft_fejerKernel_eq_zero_of_band {P M : ℕ} [NeZero P] (hM : 0 < M) (hband : 2 * M ≤ P)
    (k : ZMod P) (hk : M ≤ k.valMinAbs.natAbs) :
    𝓕 (fun t => (fejerKernel M (P := P) t : ℂ)) k = 0 := by
  rw [dft_fejerKernel hM hband, Nat.sub_eq_zero_of_le hk, Nat.cast_zero, zero_div]

/-- The de la Vallée Poussin kernel preserves every frequency up to `M`. -/
theorem dft_vpKernel_eq_one {P M : ℕ} [NeZero P] (hM : 0 < M) (hband : 4 * M ≤ P)
    (k : ZMod P) (hk : k.valMinAbs.natAbs ≤ M) :
    𝓕 (fun t => (vpKernel M (P := P) t : ℂ)) k = 1 := by
  have hfun : (fun t : ZMod P => (vpKernel M t : ℂ)) =
      (2 : ℂ) • (fun t : ZMod P => (fejerKernel (2 * M) t : ℂ)) -
        (fun t : ZMod P => (fejerKernel M t : ℂ)) := by
    funext t
    simp only [vpKernel, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, map_sub, map_smul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [dft_fejerKernel (by omega : 0 < 2 * M) (by omega : 2 * (2 * M) ≤ P),
    dft_fejerKernel hM (by omega : 2 * M ≤ P)]
  have hk' : k.valMinAbs.natAbs ≤ 2 * M := by omega
  push_cast [Nat.cast_sub hk, Nat.cast_sub hk']
  have hM₀ : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hM₀]
  ring

theorem dft_cyclicConvolution {P : ℕ} [NeZero P] (f g : ZMod P → ℂ) (k : ZMod P) :
    𝓕 (cyclicConvolution f g) k = 𝓕 f k * 𝓕 g k := by
  calc
    _ = ∑ t : ZMod P, ∑ u : ZMod P,
        f u * (ZMod.stdAddChar (-(t * k)) * g (t - u)) := by
      rw [ZMod.dft_apply]
      simp only [cyclicConvolution, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ u : ZMod P, f u * 𝓕 (fun t => g (t + -u)) k := by
      rw [Finset.sum_comm]
      simp only [ZMod.dft_apply, smul_eq_mul, sub_eq_add_neg, Finset.mul_sum]
    _ = _ := by
      simp only [dft_cyclicTranslate, ZMod.dft_apply f, smul_eq_mul, Finset.sum_mul, neg_mul]
      apply Finset.sum_congr rfl
      intro u _
      ring

theorem ofReal_cyclicConvolution {P : ℕ} [NeZero P] (f g : ZMod P → ℝ) (k : ZMod P) :
    (cyclicConvolution (R := ℝ) f g k : ℂ) =
      cyclicConvolution (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) k := by
  simp only [cyclicConvolution, Complex.ofReal_sum, Complex.ofReal_mul]

end BooleanThreshold
