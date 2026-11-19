module

public import BooleanThreshold.JSSConditionalBandpass
public import BooleanThreshold.JSSConditionalDecrementDecay
public import BooleanThreshold.JSSConditionalTwoBlocks

public noncomputable section

open Filter
open scoped BigOperators Classical Topology ZMod

namespace BooleanThreshold

/-- Independent uniform interval shifts reduce the supremum to the local
mass bound with arbitrarily large exponential probability. -/
theorem eventually_cyclic_independent_decrement {A R L c M : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hL : 0 < L) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ b > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ N P : ℕ, ∀ [NeZero P],
      Real.sqrt (n : ℝ) ≤ N → N ≤ P → P ≤ 2 ^ n →
      ∀ g : ZMod P → ℝ, (∀ t, 0 ≤ g t) → (∑ t, g t) ≤ 1 →
      (∀ t, g t ≤ A / ((N : ℝ) * Real.sqrt (n : ℝ))) →
      (∀ t, ∑ u ∈ cyclicInterval P N t, g u ≤ R / Real.sqrt (n : ℝ)) →
      (∀ k : ZMod P, b < |(k.valMinAbs : ℝ) / (P : ℝ)| → 𝓕 (fun t => (g t : ℂ)) k = 0) →
      ∀ (m₁ m₂ : ℕ), c * (n : ℝ) ≤ m₁ → c * (n : ℝ) ≤ m₂ → m₂ ≤ n →
      ∀ (s₁ : Fin m₁ → ℤ) (s₂ : Fin m₂ → ℤ),
        let B₁ i := Finset.Ico (s₁ i) (s₁ i + (N : ℤ))
        let B₂ i := Finset.Ico (s₂ i) (s₂ i + (N : ℤ))
        (((Fintype.piFinset B₁).product (Fintype.piFinset B₂)).filter fun y =>
          ∃ t : ZMod P, (24 * R + L) / ((N : ℝ) * Real.sqrt (n : ℝ)) ≤
            (cyclicShiftSmoothing (cyclicShiftSmoothing (fun u => (g u : ℂ)) y.1) y.2 t).re).card ≤
            Real.exp (-M * (n : ℝ)) * (N : ℝ) ^ (m₁ + m₂) := by
  obtain ⟨q, hq, κ, hκ, hdecay⟩ := exists_twoBlock_decrement_decay hM hc
  obtain ⟨b, hb, p, hmult⟩ := exists_cyclicShiftMultiplier_interval_moment_le hq.1
  let j := ⌈2 * (A + 24 * R) / L⌉₊
  let T := (8 * A / (κ * L ^ 2)) ^ 2
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge T
  refine ⟨b, hb, ?_⟩
  filter_upwards [hdecay p j, eventually_ge_atTop (max N₀ 64)] with n hdecay hn
  intro N P _ hN hPN hP g hg hmass hcap hlocal hband m₁ m₂ hm₁ hm₂ hm₂n s₁ s₂
  let B₁ i := Finset.Ico (s₁ i) (s₁ i + (N : ℤ))
  let B₂ i := Finset.Ico (s₂ i) (s₂ i + (N : ℤ))
  let d := ⌊κ * (N : ℝ)⌋₊
  let θ := 1 / (n : ℝ)
  let S := Finset.univ.filter fun k : ZMod P =>
    1 ≤ (N : ℝ) * |(k.valMinAbs : ℝ) / (P : ℝ)| ∧ |(k.valMinAbs : ℝ) / (P : ℝ)| ≤ b
  obtain ⟨hd₀, _, hd, hj, hrate⟩ := hdecay N P m₁ m₂ hN hP hm₁ hm₂ hm₂n
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn₀
  have hN₈ : 8 ≤ N := by
    have h : (8 : ℝ) ≤ Real.sqrt (n : ℝ) := (Real.le_sqrt (by norm_num) hn₀.le).mpr
      (by norm_num; exact_mod_cast (show 64 ≤ n by omega))
    exact_mod_cast h.trans hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let a := L / ((N : ℝ) * Real.sqrt (n : ℝ))
  let v := 24 * (R / Real.sqrt (n : ℝ)) / (N : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨low, f, hgf, hlow, hf, he, hfband⟩ := cyclic_bandpass_decomposition hN₈ hPN
      (A := A / ((N : ℝ) * Real.sqrt (n : ℝ))) (Q := R / Real.sqrt (n : ℝ))
      (by positivity) (by positivity) g hg hmass hcap hlocal hband
  have hB₁ (i : Fin m₁) : (B₁ i).card = N := by
    simp [B₁, Int.card_Ico]
  have hB₂ (i : Fin m₂) : (B₂ i).card = N := by
    simp [B₂, Int.card_Ico]
  have hmin (k : ZMod P) (hk : k ∈ S) :
      1 ≤ (N : ℝ) * |(k.valMinAbs : ℝ) / (P : ℝ)| ∧ |(k.valMinAbs : ℝ) / (P : ℝ)| ≤ b :=
    (Finset.mem_filter.mp hk).2
  have hinj (i : Fin m₂) : Set.InjOn (fun x : ℤ => (x : ZMod P)) (B₂ i) :=
    intCast_injOn_Ico_zmod (s₂ i) hPN
  have hmul (i : Fin m₁) (k : ZMod P) (hk : k ∈ S) :
      ∑ z ∈ B₁ i, ‖cyclicShiftMultiplier k z‖ ^ (2 * p) ≤ q * (B₁ i).card := by
    rw [hB₁]
    exact hmult P N k (s₁ i) (hmin k hk).1 (hmin k hk).2
  have hbandf (k : ZMod P) (hk : k ∉ S) : 𝓕 f k = 0 := by
    apply hfband k
    exact fun hh => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
  have hfe : cyclicFourierEnergy S f ≤ (P : ℝ) * (A / ((N : ℝ) * Real.sqrt (n : ℝ))) := by
    calc
      _ ≤ cyclicFourierEnergy Finset.univ f :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ = (P : ℝ) * ∑ t, ‖f t‖ ^ 2 := cyclicFourierEnergy_univ f
      _ ≤ _ := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
  have htheta : 0 < θ := by dsimp [θ]; positivity
  have hs : 8 * A ≤ κ * L ^ 2 * Real.sqrt (n : ℝ) := by
    have hκ' : 0 < κ := hκ.1
    rw [mul_comm (κ * L ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < κ * L ^ 2)).mp
    apply (Real.le_sqrt (by positivity) hn₀.le).mpr
    exact hN₀.trans (by exact_mod_cast (show N₀ ≤ n by omega))
  have hE : θ * cyclicFourierEnergy S f ≤ (P : ℝ) * (d : ℝ) * (a / 2) ^ 2 := by
    have hsq := Real.sq_sqrt hn₀.le
    refine (mul_le_mul_of_nonneg_left hfe htheta.le).trans ?_
    rw [mul_left_comm θ, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _ = A / ((N : ℝ) * Real.sqrt (n : ℝ) ^ 3) := by
        dsimp [θ]
        conv_lhs => arg 1; rw [← hsq]
        field_simp
      _ ≤ (κ * L ^ 2 * Real.sqrt (n : ℝ) / 8) /
          ((N : ℝ) * Real.sqrt (n : ℝ) ^ 3) :=
        div_le_div_of_nonneg_right (by linarith only [hs]) (by positivity)
      _ = (κ * (N : ℝ) / 2) * (a / 2) ^ 2 := by
        dsimp [a]
        field_simp
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hd₀ (sq_nonneg _)
  have hfa (t : ZMod P) : (f t).re ≤ a + (j : ℝ) * (a / 2) := by
    have hjl : A + 24 * R ≤ (j : ℝ) * (L / 2) := by
      have hh := (div_le_iff₀ hL).mp (Nat.le_ceil (2 * (A + 24 * R) / L))
      change 2 * (A + 24 * R) ≤ (j : ℝ) * L at hh
      linarith only [hh]
    have hh := div_le_div_of_nonneg_right hjl (by positivity : 0 ≤ (N : ℝ) * Real.sqrt (n : ℝ))
    have h₁ : A / ((N : ℝ) * Real.sqrt (n : ℝ)) + v =
        (A + 24 * R) / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
      dsimp [v]
      field_simp
    have h₂ : (j : ℝ) * (L / 2) / ((N : ℝ) * Real.sqrt (n : ℝ)) = (j : ℝ) * (a / 2) := by
      dsimp [a]
      ring
    rw [← h₁, h₂] at hh
    linarith only [hf t, hh, ha]
  have hcount := two_block_cyclic_smoothing_card_le (p := p) ha htheta hq.1.le
    (show 0 < N by omega) hd (show j ≤ m₂ by omega) f S B₁ B₂ hB₁ hB₂ hinj hmul hbandf hE hfa
  refine (show ((((Fintype.piFinset B₁).product (Fintype.piFinset B₂)).filter _).card : ℝ) ≤ _ from
    Nat.cast_le.mpr (Finset.card_le_card ?_)).trans
      (hcount.trans (mul_le_mul_of_nonneg_right hrate (by positivity)))
  intro y hy
  obtain ⟨hyB, t, ht⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hyB, t, ?_⟩
  change (24 * R + L) / ((N : ℝ) * Real.sqrt (n : ℝ)) ≤
    (cyclicShiftSmoothing (cyclicShiftSmoothing (fun u => (g u : ℂ)) y.1) y.2 t).re at ht
  rw [hgf, cyclicShiftSmoothing_add, cyclicShiftSmoothing_add, Pi.add_apply, Complex.add_re] at ht
  have hlt := cyclicShiftSmoothing_re_le
    (cyclicShiftSmoothing_re_le (fun u => (le_abs_self _).trans (hlow u)) y.1) y.2 t
  have heq : (24 * R + L) / ((N : ℝ) * Real.sqrt (n : ℝ)) = v + a := by
    dsimp [v, a]
    field_simp
    <;> ring
  rw [heq] at ht
  linarith only [ht, hlt]

end BooleanThreshold
