module

public import BooleanThreshold.JSSConditionalSuffixTools
public import BooleanThreshold.JSSConditionalIndependentDecrement
public import BooleanThreshold.JSSConditionalBandPairs
public import BooleanThreshold.JSSConditionalMixed

public section

open Filter Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology ZMod

namespace BooleanThreshold

set_option maxHeartbeats 1200000 in
/-- A balanced slice of a linearly long fresh suffix lowers the maximum
of a band-limited kernel to the local-mass scale outside exponentially few boxes. -/
theorem eventually_cyclic_slice_suffix_decrement {A R η σ M : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hη : 0 < η) (hσ : 0 < σ) (hM : 0 ≤ M)
    (W : ℕ) (hW : 1 ≤ W) :
    ∃ b > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ N P : ℕ, ∀ [NeZero P],
      Real.sqrt (n : ℝ) ≤ N → N ≤ P → P ≤ 2 ^ n →
      ∀ g : ZMod P → ℝ, (∀ t, 0 ≤ g t) → (∑ t, g t) ≤ 1 →
      (∀ t, g t ≤ A / ((N : ℝ) * Real.sqrt (n : ℝ))) →
      (∀ t, ∑ u ∈ cyclicInterval P N t, g u ≤ R / Real.sqrt (n : ℝ)) →
      (∀ j : ZMod P, b < |(j.valMinAbs : ℝ) / (P : ℝ)| → 𝓕 (fun u => (g u : ℂ)) j = 0) →
      ∀ k : ℕ, σ * (n : ℝ) ≤ (k : ℝ) → 2 * k ≤ n →
      ∀ m : Fin (2 * k + 1),
        η * (2 * (k : ℝ)) ≤ (m.val : ℝ) →
        (m.val : ℝ) ≤ (1 - η) * (2 * (k : ℝ)) →
      ∀ B : Fin (2 * k) → Finset ℤ,
        (∀ i, (∃ l u : ℤ, B i = Ico l u) ∧ N ≤ (B i).card ∧ (B i).card ≤ W * N) →
        (((Fintype.piFinset B).filter (fun a => ∃ t,
          (24 * R + 2) / ((N : ℝ) * Real.sqrt (n : ℝ)) ≤
            sliceAverage (fun i => if hi : i < 2 * k then (a ⟨i, hi⟩ : ZMod P) else 0)
              g (2 * k) m.val t)).card : ℝ) ≤
          Real.exp (-M * (n : ℝ)) * ((W : ℝ) * (N : ℝ)) ^ (2 * k) := by
  obtain ⟨τ, hτ, c, hc, hmixEv⟩ :=
    slice_pairs_many_mixed_eventually hη (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨K₀, hmix⟩ := eventually_atTop.mp hmixEv
  let α := τ * σ / 2
  have hα : 0 < α := by dsimp [α]; positivity
  let D := M + Real.log (2 * (W : ℝ))
  have hWR : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := zero_lt_one.trans_le hWR
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg hM (Real.log_nonneg (by linarith))
  obtain ⟨b, hb, hdec⟩ := eventually_cyclic_independent_decrement hA hR
    (show (0 : ℝ) < 1 by norm_num) hα hD
  let θ := 2 * c * σ
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hx :
      Tendsto (fun n : ℕ => Real.exp (- (θ * (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_const_mul_atTop_of_pos hθ).mpr tendsto_natCast_atTop_atTop)
  have hsmall : ∀ᶠ n : ℕ in atTop, A * Real.exp (- (θ * (n : ℝ))) < 1 := by
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have h := hconst.mul hx
    rw [mul_zero] at h
    exact h.eventually_lt_const (by norm_num)
  have hK₀ : ∀ᶠ n : ℕ in atTop, (K₀ : ℝ) ≤ σ * (n : ℝ) :=
    ((tendsto_const_mul_atTop_of_pos hσ).mpr tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have hSize : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (τ * σ) * (n : ℝ) :=
    ((tendsto_const_mul_atTop_of_pos (mul_pos hτ hσ)).mpr tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  refine ⟨b, hb, ?_⟩
  filter_upwards [hdec, hsmall, hK₀, hSize, eventually_ge_atTop (1 : ℕ)]
    with n hDec hSmall hK hSizeN hn
  intro N P _ hN hNP hP g hnn hMass hCap hLocal hBand k hk hkn m hlo hhi B hB
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le hn
  have hNr : 0 < (N : ℝ) := (Real.sqrt_pos_of_pos hnpos).trans_le hN
  have hN' : 0 < N := by exact_mod_cast hNr
  let e : Fin k × Bool ↪ Fin (2 * k) := prefixAdjacentPairEmbedding le_rfl
  let μ : Measure (Fin (2 * k) → Bool) := uniformOn (signSlice (2 * k) m)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOn
    (signSlice (2 * k) m).toFinite (signSlice_nonempty m)
  let f (t : ZMod P) : ℂ := g t
  let scale := (N : ℝ) * Real.sqrt (n : ℝ)
  have hScale : 0 < scale := by dsimp [scale]; positivity
  let a₁ := (24 * R + 1) / scale
  let a₂ := (24 * R + 2) / scale
  have ha₁ : 0 ≤ a₁ := by dsimp [a₁]; positivity
  let Bad : Set (Fin (2 * k) → Bool) :=
    {x | ((mixedPairIndices e x).card : ℝ) < τ * (2 * (k : ℝ))}
  let Good : Finset (Fin (2 * k) → Bool) := univ.filter (fun x => x ∉ Bad)
  have hBad : μ.real Bad ≤ Real.exp (- (θ * (n : ℝ))) := by
    have hTwoK : K₀ ≤ 2 * k := by
      have h : (K₀ : ℝ) ≤ (2 : ℝ) * (k : ℝ) := by linarith only [hK, hk, Nat.cast_nonneg (α := ℝ) k]
      exact_mod_cast h
    have hhalf : (1 / 2 : ℝ) * ((2 * k : ℕ) : ℝ) ≤ (k : ℝ) := by push_cast; linarith
    have ht := hmix (2 * k) hTwoK k e m hhalf (by simpa using hlo) (by simpa using hhi)
    refine (show μ.real Bad ≤ Real.exp (-c * ((2 * k : ℕ) : ℝ)) by
      simpa only [μ, Bad, mixedPairIndices, Nat.cast_mul, Nat.cast_ofNat] using ht).trans ?_
    apply Real.exp_le_exp.mpr
    dsimp [θ]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hk hc.le]
  let T := Fintype.piFinset B
  let E (x : Fin (2 * k) → Bool) :=
    T.filter (fun a => ∃ t, a₁ ≤
      (cyclicShiftSmoothing f (fun i => pairedSubsetShift e a x (mixedPairEmbedding e x i)) t).re)
  let F := Good.biUnion E
  let C := Real.exp (-D * (n : ℝ)) * (W : ℝ) ^ n
  have hCount (x : Fin (2 * k) → Bool) (hx : x ∈ Good) :
      ((E x).card : ℝ) ≤ C * (T.card : ℝ) := by
    let d := (mixedPairIndices e x).card
    let d₂ := d / 2
    let d₁ := d - d₂
    have hd : d₂ + d₁ = d := by dsimp [d₁, d₂]; omega
    have hdx : τ * (2 * (k : ℝ)) ≤ (d : ℝ) := le_of_not_gt (mem_filter.mp hx).2
    have hdlow : 2 * (τ * σ) * (n : ℝ) ≤ (d : ℝ) := by
      nlinarith only [hdx, mul_le_mul_of_nonneg_left hk hτ.le]
    have hdlte : d ≤ 2 * d₂ + 1 := by dsimp [d₂]; omega
    have hdlteR : (d : ℝ) ≤ 2 * (d₂ : ℝ) + 1 := by exact_mod_cast hdlte
    have hd₂ : α * (n : ℝ) ≤ (d₂ : ℝ) := by
      dsimp [α]
      nlinarith only [hdlow, hdlteR, hSizeN]
    have hd₂₁ : d₂ ≤ d₁ := by dsimp [d₁, d₂]; omega
    have hd₁ : α * (n : ℝ) ≤ (d₁ : ℝ) := hd₂.trans (by exact_mod_cast hd₂₁)
    have hdk : d ≤ k := by simpa only [Fintype.card_fin] using card_le_univ (mixedPairIndices e x)
    have hkn' : k ≤ n := (Nat.le_mul_of_pos_left k (by decide : 0 < 2)).trans hkn
    have hdn : d ≤ n := hdk.trans hkn'
    have hdn₂ : d₂ ≤ n := (Nat.div_le_self d 2).trans hdn
    let p (y : Fin d → ℤ) : Prop := ∃ t, a₁ ≤ (cyclicShiftSmoothing f y t).re
    let Eclass := @Finset.filter (Fin (2 * k) → ℤ)
      (fun a => p (fun i => pairedSubsetShift e a x (mixedPairEmbedding e x i)))
      (fun _ => Classical.propDecidable _) (Fintype.piFinset B)
    suffices h : (Eclass.card : ℝ) ≤ C * ((Fintype.piFinset B).card : ℝ) by
      have hEclass : E x = Eclass := by
        ext a
        simp only [Eclass, E, p, T, mem_filter]
        rfl
      rw [hEclass]
      exact h
    refine card_filter_piFinset_le_of_mixed_shift_sections e x B p (C := C) fun fixed => ?_
    let B₀ (i : Fin d) := B (e (mixedPairEmbedding e x i, true))
    let B' (i : Fin d) :=
      (B₀ i).map (pairedShiftEquiv (x (e (mixedPairEmbedding e x i, false))) (fixed i)).toEmbedding
    have hB' (i : Fin d) : ∃ l u : ℤ, B' i = Ico l u ∧ (B' i).card ≤ W * N := by
      obtain ⟨⟨l, u, hI⟩, _, hwidth⟩ := hB (e (mixedPairEmbedding e x i, true))
      have hc : (B' i).card ≤ W * N := by simpa only [B', B₀, card_map] using hwidth
      have hh : B₀ i = Ico l u := hI
      have he := map_Ico_pairedShiftEquiv (x (e (mixedPairEmbedding e x i, false))) (fixed i) l u
      by_cases hi : x (e (mixedPairEmbedding e x i, false)) = true
      · exact ⟨_, _, by simpa only [B', hh, hi, ite_true] using he, hc⟩
      · exact ⟨_, _, by simpa only [B', hh, hi, Bool.false_eq_true, ite_false] using he, hc⟩
    have hWidth : ((@Finset.filter (Fin d → ℤ) p (fun _ => Classical.propDecidable _)
        (Fintype.piFinset B')).card : ℝ) ≤
        Real.exp (-D * (n : ℝ)) * ((W : ℝ) * (N : ℝ)) ^ d :=
      card_filter_shift_smoothing_le_of_two_interval_grids hN' hd B' hB' f a₁
        (fun s₁ s₂ => by
          have hs := hDec N P hN hNP hP g hnn hMass hCap hLocal hBand d₁ d₂ hd₁ hd₂ hdn₂ s₁ s₂
          dsimp only at hs ⊢
          convert hs using 1
          congr 1
          apply congrArg Finset.card
          ext y
          simp only [mem_filter, f, a₁, scale])
    have hBase : (N : ℝ) ^ d ≤ ((Fintype.piFinset B₀).card : ℝ) := by
      rw [show (N : ℝ) ^ d = ∏ _i : Fin d, (N : ℝ) by simp,
        Fintype.card_piFinset, Nat.cast_prod]
      exact prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => by exact_mod_cast
        (hB (e (mixedPairEmbedding e x i, true))).2.1
    refine hWidth.trans ?_
    rw [mul_pow, ← mul_assoc]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hWR hdn) (Real.exp_nonneg _)) hBase
      (by positivity) (by dsimp [C]; positivity)
  have hsub : (T.filter (fun a => ∃ t, a₂ ≤
      sliceAverage (fun i => if hi : i < 2 * k then (a ⟨i, hi⟩ : ZMod P) else 0) g (2 * k) m.val t)) ⊆ F := by
    intro a h
    obtain ⟨ha, t, ht⟩ := mem_filter.mp h
    by_contra hfa
    let V (x : Fin (2 * k) → Bool) : ℝ :=
      (cyclicShiftSmoothing f (fun i => pairedSubsetShift e a x (mixedPairEmbedding e x i))
        (t + (selectedCoordinateSum a x : ℤ))).re
    let cap := A / scale
    have hV (x : Fin (2 * k) → Bool) : V x ≤ a₁ + Bad.indicator (fun _ => cap) x := by
      by_cases hx : x ∈ Bad
      · have hh : V x ≤ cap := cyclicShiftSmoothing_re_le (fun u => by simpa only [f, Complex.ofReal_re] using hCap u)
          (fun i => pairedSubsetShift e a x (mixedPairEmbedding e x i)) _
        rw [Set.indicator_of_mem hx]
        exact hh.trans (le_add_of_nonneg_left ha₁)
      · rw [Set.indicator_of_notMem hx, add_zero]
        apply le_of_not_gt
        intro hlt
        exact hfa (mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩, mem_filter.mpr
          ⟨ha, t + (selectedCoordinateSum a x : ℤ), hlt.le⟩⟩)
    have hInt : (∫ x, V x ∂μ) ≤ a₁ + μ.real Bad * cap := by
      refine (integral_mono ?_ ?_ hV).trans_eq ?_
      · exact integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
      · exact integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
      · rw [integral_add, integral_const, probReal_univ, one_smul,
          integral_indicator_const cap Bad.toFinite.measurableSet, smul_eq_mul]
        · exact integrable_const _
        · exact integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
    have hBadSmall : μ.real Bad * cap < 1 / scale := by
      dsimp [cap]
      rw [← mul_div_assoc]
      apply div_lt_div_of_pos_right _ hScale
      exact (mul_le_mul_of_nonneg_right hBad hA).trans_lt (by simpa only [mul_comm] using hSmall)
    rw [sliceAverage_eq_integral_pair_smoothing_re e m a g t] at ht
    change a₂ ≤ (∫ x, V x ∂μ) at ht
    have hs : (∫ x, V x ∂μ) < a₁ + 1 / scale := hInt.trans_lt (by linarith only [hBadSmall])
    have he : a₁ + 1 / scale = a₂ := by dsimp [a₁, a₂]; ring
    exact (not_lt_of_ge ht) (he ▸ hs)
  have hGood : (Good.card : ℝ) ≤ (2 : ℝ) ^ n := by
    have hcard : (Good.card : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      exact_mod_cast (show Good.card ≤ 2 ^ (2 * k) by simpa using card_le_univ Good)
    exact hcard.trans (pow_le_pow_right₀ (by norm_num) hkn)
  have hT : (T.card : ℝ) ≤ ((W : ℝ) * (N : ℝ)) ^ (2 * k) := by
    dsimp only [T]
    rw [Fintype.card_piFinset, Nat.cast_prod]
    calc
      _ ≤ ∏ _i : Fin (2 * k), (W : ℝ) * (N : ℝ) :=
        prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => by exact_mod_cast (hB i).2.2
      _ = _ := by simp
  have hRate : (2 : ℝ) ^ n * C = Real.exp (-M * (n : ℝ)) := by
    dsimp [C]
    rw [mul_left_comm, ← mul_pow, ← Real.exp_log (show 0 < 2 * (W : ℝ) by positivity),
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [D]
    ring
  calc
    _ ≤ (F.card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ x ∈ Good, ((E x).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _x ∈ Good, C * (T.card : ℝ) := sum_le_sum hCount
    _ = (Good.card : ℝ) * (C * (T.card : ℝ)) := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ n * (C * (T.card : ℝ)) := mul_le_mul_of_nonneg_right hGood (by dsimp [C]; positivity)
    _ = Real.exp (-M * (n : ℝ)) * (T.card : ℝ) := by rw [← mul_assoc, hRate]
    _ ≤ _ := mul_le_mul_of_nonneg_left hT (Real.exp_nonneg _)

end BooleanThreshold
