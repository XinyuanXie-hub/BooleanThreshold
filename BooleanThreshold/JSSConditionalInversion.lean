module

public import BooleanThreshold.JSSConditionalBoxes
public import BooleanThreshold.JSSConditionalEstimate
public import BooleanThreshold.JSSConditionalSlice

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

namespace BooleanThreshold

/-- Points of one integer box that have a large small ball on a prescribed slice. -/
noncomputable def largeSliceBox (n : ℕ) (m : Fin (n + 1))
    (P : Fin n → Finset ℤ) (h : ℝ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset P).filter fun w => ∃ z : ℝ,
    h ≤ (uniformOn (signSlice n m)).real
      {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * Real.sqrt (n : ℝ)}

/-- Fixed-weight inverse small-ball estimate for opposite-sign admissible
boxes. This is the opposite-sign case of the slice smoothing estimate
in Jain, Sah, and Sawhney, arXiv:2010.06553, Corollary 3.3. -/
def OppositeBandSliceEstimate : Prop :=
  ∀ (α : ℝ) (B : ℕ), 0 < α → α < 1 / 4 → 4 ≤ B →
    ∃ γ > (0 : ℝ), ∃ H ≥ (1 : ℝ), ∀ M ≥ (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ (5 / 3 : ℝ) ^ n →
      ∀ P : Fin n → Finset ℤ, oppositeBandBox n N B α P →
      ∀ m : Fin (n + 1), |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ * (n : ℝ) →
        ((largeSliceBox n m P (H / (N : ℝ))).card : ℝ) ≤
          Real.exp (-M * (n : ℝ)) * (((B : ℝ) + 1) * (N : ℝ)) ^ n

/-- The fixed-slice estimate supplies the lattice counting input. A common
integer translation puts the separated bands on opposite sides of zero. -/
theorem conditionalSmallBallCountEstimate_of_slice
    (hSlice : OppositeBandSliceEstimate) : ConditionalSmallBallCountEstimate := by
  intro δ ρ hδ hd hρ hr
  obtain ⟨c, hc, hcdef, A, B, hB, hgeom⟩ := roundedUnit_geometry_eventually hδ hd hρ
  let α := δ / 16
  obtain ⟨γ, hγ, H, hH, hsmooth⟩ := hSlice α B (by dsimp [α]; positivity)
    (by dsimp [α]; linarith only [hd]) hB
  let L := 1 + 8 * H / c
  have hL : 1 ≤ L := le_add_of_nonneg_right (by positivity)
  have hL₀ := zero_lt_one.trans_le hL
  let C := ((2 : ℝ) * B + 1) * (12 * 2 ^ (A + 1)) * ((B : ℝ) + 1) * 2
  have hC : 1 ≤ C := by
    dsimp [C]
    refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le ?_ ?_) ?_) (by norm_num)
    · have hb : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
      linarith only [hb]
    · exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))
    · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hc₁ : c ≤ 1 := by rw [hcdef]; linarith only [hr]
  obtain ⟨N₀, hN₀⟩ := balancedWindow_mass_ge_half hγ
  refine ⟨γ, hγ, L, hL, C, hC, fun M hM => ?_⟩
  filter_upwards [hgeom, oppositeBandBox_cover (A := A) hB α, hsmooth M hM,
    eventually_ge_atTop (max N₀ 1)] with n hgeon hcover hsmoothn hn
  intro u hu hupper
  let W := balancedSignWindow n γ
  let β := (3 / 5 : ℝ) ^ n
  have hu₀ : 0 < u := (show 0 < β by dsimp [β]; positivity).trans_le hu
  have hW : W.Nonempty := by
    by_contra! h
    have hp : 1 / 2 ≤ (uniformOn Set.univ).real W := hN₀ n ((le_max_left _ _).trans hn)
    rw [h, measureReal_empty] at hp
    norm_num at hp
  let N := ⌊c / u⌋₊
  have hNhi : (N : ℝ) ≤ c / u := Nat.floor_le (by positivity)
  have hLc : 8 * H ≤ L * c := by
    dsimp [L]
    field_simp [hc.ne']
    nlinarith only [hc.le]
  have hcu : 2 ≤ c / u := by
    refine (le_div_iff₀ hu₀).mpr ?_
    have hul := (le_div_iff₀ hL₀).mp hupper
    have htwo : 2 ≤ L * c := by linarith only [hLc, hH]
    have hh := mul_le_mul_of_nonneg_right htwo hu₀.le
    have hh' := mul_le_mul_of_nonneg_left hul hc.le
    nlinarith only [hh, hh']
  have hNlo : c / (2 * u) ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one (c / u)
    change c / u < (N : ℝ) + 1 at h
    rw [show c / (2 * u) = (c / u) / 2 by ring]
    linarith only [h, hcu]
  have hN : 0 < N := by
    exact_mod_cast ((show 0 < c / (2 * u) by positivity).trans_le hNlo)
  have hN₁ : (N : ℝ) ≤ 1 / u := hNhi.trans (div_le_div_of_nonneg_right hc₁ hu₀.le)
  have hNinv : (N : ℝ) ≤ (5 / 3 : ℝ) ^ n := by
    have hinv : 1 / u ≤ 1 / β := one_div_le_one_div_of_le (by dsimp [β]; positivity) hu
    apply (hN₁.trans hinv).trans_eq
    dsimp [β]
    rw [one_div, ← inv_pow]
    norm_num
  have hHN : H / (N : ℝ) ≤ L * u / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < N)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * u)).mp hNlo
    have hh' := mul_le_mul_of_nonneg_left hh hL₀.le
    nlinarith only [hh', hLc]
  obtain ⟨D, hD, hDvalid, hDcover⟩ := hcover N hN
  let F (p : ℤ × (Fin n → Finset ℤ)) (m : Fin (n + 1)) : Finset (Fin n → ℤ) :=
    if |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ * (n : ℝ) then
      (largeSliceBox n m p.2 (H / (N : ℝ))).image (fun v i => v i + p.1)
    else ∅
  let G : Finset (Fin n → ℤ) := D.biUnion (fun p => (Finset.univ : Finset (Fin (n + 1))).biUnion (F p))
  have hset : roundedConditionalCandidates n (uniformOn W) δ ρ L u ⊆ (G : Set (Fin n → ℤ)) := by
    rintro w ⟨⟨a, ha, ha', T, hTu, hT, _, hw⟩, _, z, hz⟩
    obtain ⟨hnorm, hband⟩ := hgeon hu₀ hTu hT hN hNlo hNhi a ha ha' w hw
    obtain ⟨p, hp, hw'⟩ := hDcover w hnorm hband
    obtain ⟨m, hm, _, hmprob⟩ := exists_signSlice_real_ge hW
      {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * Real.sqrt (n : ℝ)}
    let v : Fin n → ℤ := fun i => w i - p.1
    have hv : v ∈ largeSliceBox n m p.2 (H / (N : ℝ)) := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hw',
        z - (p.1 : ℝ) * (2 * (m.val : ℝ) - n), ?_⟩
      rw [signSlice_real_smallBall_sub_const]
      exact hHN.trans (hz.trans hmprob)
    have hf : w ∈ F p m := by
      simp only [F, hm, ↓reduceIte]
      refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
      funext i
      exact sub_add_cancel _ _
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hf⟩⟩
  have hFcard (p : ℤ × (Fin n → Finset ℤ)) (hp : p ∈ D) (m : Fin (n + 1)) :
      ((F p m).card : ℝ) ≤ Real.exp (-M * (n : ℝ)) * (((B : ℝ) + 1) * (N : ℝ)) ^ n := by
    by_cases hm : |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ * (n : ℝ)
    · simp only [F, hm, ↓reduceIte]
      refine le_trans ?_ (hsmoothn N hN hNinv p.2 (hDvalid p hp) m hm)
      exact_mod_cast Finset.card_image_le
    · simp only [F, hm, ↓reduceIte, Finset.card_empty, Nat.cast_zero]
      positivity
  have hG : (G.card : ℝ) ≤ (D.card : ℝ) * (n + 1 : ℝ) * (Real.exp (-M * (n : ℝ)) *
      (((B : ℝ) + 1) * (N : ℝ)) ^ n) := by
    calc
      _ ≤ ∑ p ∈ D, (((Finset.univ : Finset (Fin (n + 1))).biUnion (F p)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ D, ∑ m : Fin (n + 1), ((F p m).card : ℝ) := by
        exact Finset.sum_le_sum fun p _ => by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ D, ∑ _m : Fin (n + 1), Real.exp (-M * (n : ℝ)) *
          (((B : ℝ) + 1) * (N : ℝ)) ^ n :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun m _ => hFcard p hp m
      _ = _ := by simp [nsmul_eq_mul, Nat.cast_add, mul_assoc]
  have hn₁ := (le_max_right N₀ 1).trans hn
  have hBpow : (2 : ℝ) * (B : ℝ) + 1 ≤ (2 * (B : ℝ) + 1) ^ n := by
    have hb₀ : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hb₀] : 1 ≤ 2 * (B : ℝ) + 1) hn₁
  have hnend : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))
  have hD' : (D.card : ℝ) ≤ (2 * (B : ℝ) + 1) ^ n * (12 * 2 ^ (A + 1) : ℝ) ^ n := by
    have hcast : (D.card : ℝ) ≤ (2 * (B : ℝ) + 1) * (12 * 2 ^ (A + 1) : ℝ) ^ n := by exact_mod_cast hD
    exact hcast.trans (mul_le_mul_of_nonneg_right hBpow (by positivity))
  have hN' : (((B : ℝ) + 1) * (N : ℝ)) ^ n ≤ (((B : ℝ) + 1) / u) ^ n := by
    apply pow_le_pow_left₀ (by positivity) _ _
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hN₁ (by positivity : 0 ≤ (B : ℝ) + 1)
  calc
    _ ≤ (G.card : ℝ) := by
      rw [← Set.ncard_coe_finset]
      exact_mod_cast Set.ncard_le_ncard hset G.finite_toSet
    _ ≤ _ := hG
    _ ≤ ((2 * (B : ℝ) + 1) ^ n * (12 * 2 ^ (A + 1) : ℝ) ^ n) * (2 : ℝ) ^ n *
        (Real.exp (-M * (n : ℝ)) * (((B : ℝ) + 1) / u) ^ n) := by gcongr
    _ = _ := by
      have he : C / u = (2 * (B : ℝ) + 1) * (12 * 2 ^ (A + 1)) * 2 * (((B : ℝ) + 1) / u) := by
        dsimp [C]
        ring
      simp only [he, mul_pow]
      ring

end BooleanThreshold
