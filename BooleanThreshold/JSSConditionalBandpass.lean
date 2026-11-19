module

public import BooleanThreshold.JSSConditionalFejerFourier
public import BooleanThreshold.JSSConditionalLowpass
public import BooleanThreshold.JSSConditionalFourierMoment

public noncomputable section

open scoped BigOperators Classical ZMod

namespace BooleanThreshold

private theorem dft_vpKernel_real_le_one {P M : ℕ} [NeZero P]
    (hM : 0 < M) (hP : 4 * M ≤ P) (k : ZMod P) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ 𝓕 (fun t => (vpKernel M (P := P) t : ℂ)) k = (w : ℂ) := by
  by_cases hk : k.valMinAbs.natAbs ≤ M
  · exact ⟨1, zero_le_one, le_rfl, by simpa using dft_vpKernel_eq_one hM hP k hk⟩
  let w := ((2 * M - k.valMinAbs.natAbs : ℕ) : ℝ) / (M : ℝ)
  have hM' : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw' : w ≤ 1 := (div_le_one hM').mpr (by
    exact_mod_cast (show 2 * M - k.valMinAbs.natAbs ≤ M by omega))
  refine ⟨w, hw, hw', ?_⟩
  have hfun : (fun t : ZMod P => (vpKernel M t : ℂ)) =
      (2 : ℂ) • (fun t : ZMod P => (fejerKernel (2 * M) t : ℂ)) -
        (fun t : ZMod P => (fejerKernel M t : ℂ)) := by
    funext t
    simp only [vpKernel, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, map_sub, map_smul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [dft_fejerKernel (by omega : 0 < 2 * M) (by omega : 2 * (2 * M) ≤ P),
    dft_fejerKernel_eq_zero_of_band hM (by omega : 2 * M ≤ P) k (le_of_not_ge hk), sub_zero]
  dsimp [w]
  push_cast
  have hc : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  field_simp

private theorem frequency_eq_natAbs {P : ℕ} (k : ZMod P) :
    |(k.valMinAbs : ℝ) / (P : ℝ)| = (k.valMinAbs.natAbs : ℝ) / (P : ℝ) := by
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) P), ← Int.cast_abs,
    Int.abs_eq_natAbs, Int.cast_natCast]

/-- Low frequencies contribute at most the local interval mass divided
by the interval length. The residual keeps the original energy bound. -/
theorem cyclic_bandpass_decomposition {P N : ℕ} [NeZero P] (hN : 8 ≤ N) (hPN : N ≤ P)
    {A Q b : ℝ} (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (g : ZMod P → ℝ) (hg : ∀ t, 0 ≤ g t) (hmass : ∑ t, g t ≤ 1)
    (hcap : ∀ t, g t ≤ A) (hlocal : ∀ t, ∑ u ∈ cyclicInterval P N t, g u ≤ Q)
    (hband : ∀ k : ZMod P, b < |(k.valMinAbs : ℝ) / (P : ℝ)| →
      𝓕 (fun t => (g t : ℂ)) k = 0) :
    ∃ low f : ZMod P → ℂ,
      (fun t => (g t : ℂ)) = low + f ∧ (∀ t, |(low t).re| ≤ 24 * Q / (N : ℝ)) ∧
      (∀ t, (f t).re ≤ A + 24 * Q / (N : ℝ)) ∧ (∑ t, ‖f t‖ ^ 2 ≤ A) ∧
      (∀ k : ZMod P, ¬ (1 ≤ (N : ℝ) * |(k.valMinAbs : ℝ) / (P : ℝ)| ∧
          |(k.valMinAbs : ℝ) / (P : ℝ)| ≤ b) → 𝓕 f k = 0) := by
  let M := (P + N - 1) / N
  have hn : 0 < N := by omega
  have hp : 0 < P := NeZero.pos P
  have hmlo : P ≤ M * N := by
    have hmod := Nat.mod_lt (P + N - 1) hn
    have hdiv := Nat.mod_add_div (P + N - 1) N
    change (P + N - 1) % N + N * M = P + N - 1 at hdiv
    rw [Nat.mul_comm N M] at hdiv
    omega
  have hmhi : M * N ≤ 2 * P := by
    unfold M
    exact (Nat.div_mul_le_self _ _).trans (by omega)
  have hm : 0 < M := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, zero_mul] at hmlo
    omega
  have hmp : 4 * M ≤ P := by
    apply Nat.le_of_mul_le_mul_right (c := N) _ hn
    calc
      _ = 4 * (M * N) := by rw [Nat.mul_assoc]
      _ ≤ 4 * (2 * P) := Nat.mul_le_mul_left _ hmhi
      _ = P * 8 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hN
  let G (t : ZMod P) : ℂ := g t
  let L (t : ZMod P) : ℂ := ((cyclicConvolution g (vpKernel M) t : ℝ) : ℂ)
  let f := G - L
  have hlow (t : ZMod P) : |(L t).re| ≤ 24 * Q / (N : ℝ) := by
    simpa only [L, Complex.ofReal_re] using
      abs_cyclicConvolution_vp_le_of_local_mass hn hm hmlo hmhi g hg hQ hlocal t
  have hres (t : ZMod P) : (f t).re ≤ A + 24 * Q / (N : ℝ) := by
    have hl := (abs_le.mp (hlow t)).1
    change ((g t : ℂ) - L t).re ≤ _
    rw [Complex.sub_re, Complex.ofReal_re]
    linarith only [hl, hcap t]
  have hdft (k : ZMod P) :
      𝓕 f k = 𝓕 G k * (1 - 𝓕 (fun t => (vpKernel M (P := P) t : ℂ)) k) := by
    rw [show f = G - L from rfl, map_sub, Pi.sub_apply]
    have hL : L = cyclicConvolution G (fun t => (vpKernel M (P := P) t : ℂ)) := by
      funext t
      exact ofReal_cyclicConvolution g (vpKernel M) t
    rw [hL, dft_cyclicConvolution]
    ring
  have hfE : cyclicFourierEnergy Finset.univ f ≤ cyclicFourierEnergy Finset.univ G := by
    apply Finset.sum_le_sum
    intro k _
    obtain ⟨w, h₀, h₁, hw⟩ := dft_vpKernel_real_le_one hm hmp k
    rw [hdft, hw, norm_mul]
    have h : ‖1 - (w : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr h₁)]
      linarith only [h₀]
    exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (norm_nonneg _) h) _
  have hfenergy : ∑ t, ‖f t‖ ^ 2 ≤ A := by
    rw [cyclicFourierEnergy_univ, cyclicFourierEnergy_univ] at hfE
    refine ((mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr hp)).mp hfE).trans ?_
    calc
      _ = ∑ t, (g t) ^ 2 := by simp [G]
      _ ≤ ∑ t, A * g t := Finset.sum_le_sum fun t _ => by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hcap t) (hg t)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass hA
  refine ⟨L, f, ?_, hlow, hres, hfenergy, ?_⟩
  · funext t
    simp only [f, Pi.add_apply, Pi.sub_apply]
    ring
  · intro k hk
    by_cases hkb : |(k.valMinAbs : ℝ) / (P : ℝ)| ≤ b
    · have hlo : (N : ℝ) * |(k.valMinAbs : ℝ) / (P : ℝ)| < 1 := by
        by_contra! hl
        exact hk ⟨hl, hkb⟩
      rw [frequency_eq_natAbs, ← mul_div_assoc, div_lt_one (Nat.cast_pos.mpr hp)] at hlo
      have hlo' : N * k.valMinAbs.natAbs < P := by exact_mod_cast hlo
      have hmk : k.valMinAbs.natAbs ≤ M := by
        apply Nat.le_of_mul_le_mul_right (c := N) _ hn
        rw [Nat.mul_comm k.valMinAbs.natAbs N]
        exact hlo'.le.trans hmlo
      rw [hdft, dft_vpKernel_eq_one hm hmp k hmk, sub_self, mul_zero]
    · rw [hdft, hband k (lt_of_not_ge hkb), zero_mul]

end BooleanThreshold
