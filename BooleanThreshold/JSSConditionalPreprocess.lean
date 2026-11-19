module

public import BooleanThreshold.JSSConditionalPreprocessCount
public import BooleanThreshold.JSSConditionalBinomial

public section

open Filter
open scoped BigOperators Topology Classical

namespace BooleanThreshold

/-- The preprocessing estimate for fixed-weight averaging. The Lipschitz or
Fourier properties of the input are not needed at this stage. -/
theorem eventually_sliceAverage_preprocess :
    ∃ η > (0 : ℝ), ∃ σ > (0 : ℝ), ∃ β > (0 : ℝ), β < 1 / 2 ∧
      ∀ C ≥ (0 : ℝ), ∀ M ≥ (0 : ℝ), ∃ L ≥ (1 : ℝ), ∀ᶠ n : ℕ in atTop,
        ∀ ℓ ≤ n, 0 < ℓ → (1 - η) * (n : ℝ) ≤ (ℓ : ℝ) →
        ∀ s ≤ ℓ, |2 * (s : ℝ) - (ℓ : ℝ)| ≤ 2 * η * (ℓ : ℝ) →
        ∀ N : ℕ, 0 < N → (N : ℝ) ≤ (5 / 3 : ℝ) ^ n →
        ∀ (G : Type) [AddCommGroup G] [Fintype G], (Fintype.card G : ℝ) ≤ (2 : ℝ) ^ n →
        ∀ (encode : ℤ → G) (B : Fin ℓ → Finset ℤ), (∀ i, (B i).Nonempty) →
        ∀ f : G → ℝ, (∀ t, 0 ≤ f t) → (∀ t, f t ≤ 1) →
        (∀ i : Fin ℓ, σ * (n : ℝ) ≤ (i.val : ℝ) → ∀ q ≤ i.val,
          β * (i.val : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ (1 - β) * (i.val : ℝ) →
          ∀ X : Fin ℓ → ℤ, (∀ j, X j ∈ B j) → ∀ (y : G) (b : Bool),
            ∑ x ∈ B i, sliceAverage (sliceCoefficientArray encode X) f i.val q
              (y + if b then -(encode x) else encode x) ≤
                C / ((N : ℝ) * Real.sqrt (n : ℝ)) * ((B i).card : ℝ)) →
        ((highSliceAverages encode B f s (L / ((N : ℝ) * Real.sqrt (n : ℝ)))).card : ℝ) ≤
          Real.exp (-M * (n : ℝ)) * ∏ i, ((B i).card : ℝ) := by
  obtain ⟨η, hη, hbinom⟩ := eventually_near_middle_choose_lower (b := (7 / 4 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨ε, hε, hε₁, γ, hγ, κ, hκ, hentropy⟩ :=
    eventually_many_robustHighSiblingSteps (b := (7 / 4 : ℝ)) (by norm_num)
  let σ := κ / 8
  let β := ε / 2
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ' : β < 1 / 2 := by dsimp [β]; linarith only [hε₁]
  refine ⟨η, hη, σ, hσ, β, hβ, hβ', fun C hC M hM => ?_⟩
  let u := Real.exp (-4 * (M + 3) / κ)
  have hu : 0 < u := Real.exp_pos _
  let L := 1 + C / (γ * u)
  have hL : 1 ≤ L := le_add_of_nonneg_right (by positivity)
  have hL₀ := zero_lt_one.trans_le hL
  have hLu : C / (γ * L) ≤ u := by
    apply (div_le_iff₀ (by positivity : 0 < γ * L)).mpr
    have he : u * (γ * L) = u * γ + C := by dsimp [L]; field_simp
    rw [he]
    exact le_add_of_nonneg_left (by positivity)
  obtain ⟨T, hT⟩ := exists_nat_ge (max (4 / κ) (2 / (ε * σ)))
  refine ⟨L, hL, ?_⟩
  filter_upwards [hbinom, hentropy, eventually_ge_atTop T] with n hbin hent hnT
  intro ℓ hℓ hℓ₀ hℓn s hs hsbal N hN hNhi G hG₁ hG₂ hG encode B hB f hf hf₁ hlocal
  let r := ⌈σ * (n : ℝ)⌉₊
  let k := ⌊κ * (n : ℝ) / 2⌋₊
  let T₀ := (N : ℝ) * Real.sqrt (n : ℝ)
  let τ := L / T₀
  have hn : 0 < n := hℓ₀.trans_le hℓ
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  have hτ : 0 < τ := div_pos hL₀ hT₀
  have hτ' : 1 / ((5 / 3 : ℝ) ^ n * Real.sqrt (n : ℝ)) ≤ τ :=
    (one_div_le_one_div_of_le hT₀ (mul_le_mul_of_nonneg_right hNhi (Real.sqrt_nonneg _))).trans
      (div_le_div_of_nonneg_right hL hT₀.le)
  have hN₀ : max (4 / κ) (2 / (ε * σ)) ≤ (n : ℝ) := hT.trans (by exact_mod_cast hnT)
  have hnκ : 4 ≤ κ * (n : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hκ).mp ((le_max_left _ _).trans hN₀)
  have hnσ : 2 ≤ ε * (σ * (n : ℝ)) := by
    rw [← mul_assoc, mul_comm (ε * σ)]
    exact (div_le_iff₀ (by positivity : 0 < ε * σ)).mp ((le_max_right _ _).trans hN₀)
  have hr₀ : σ * (n : ℝ) ≤ (r : ℝ) := Nat.le_ceil _
  have hr₁ : (r : ℝ) ≤ σ * (n : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hr : 2 ≤ ε * (r : ℝ) := hnσ.trans (mul_le_mul_of_nonneg_left hr₀ hε.le)
  have hk₀ : κ * (n : ℝ) / 4 ≤ (k : ℝ) := by
    have h := Nat.lt_floor_add_one (κ * (n : ℝ) / 2)
    change κ * (n : ℝ) / 2 < (k : ℝ) + 1 at h
    linarith only [h, hnκ]
  have hk₁ : (k : ℝ) ≤ κ * (n : ℝ) / 2 := Nat.floor_le (by positivity)
  have hrk : ((r + k : ℕ) : ℝ) ≤ κ * (n : ℝ) := by
    rw [Nat.cast_add]
    dsimp [σ] at hr₁
    linarith only [hr₁, hk₁, hnκ]
  have hchoose := hbin ℓ hℓ hℓn s hs hsbal
  have hcount : ((highSliceAverages encode B f s τ).card : ℝ) ≤
      (Fintype.card G : ℝ) * (4 : ℝ) ^ ℓ * ((C / T₀) / (γ * τ)) ^ k * ∏ i, ((B i).card : ℝ) := by
    refine highSliceAverages_card_le_of_local_average (r := r) (k := k) hs encode B hB f hf hε hγ hτ
      (by positivity) hr ?_ ?_
    · intro i hi q hq hq₀ hq₁ X hX y b
      have hir : (r : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hi
      exact hlocal i (hr₀.trans hir) q hq hq₀ hq₁ X hX y b
    · intro x hx t w p hp ht
      let X := sliceCoefficientArray encode x
      let H := slicePathHeight X f w p
      let V (j : ℕ) := slicePathSibling X f w j (p j)
      have hstart : H 0 ≤ 1 := by
        change sliceAverage X f 0 (prefixBitCount w true 0) (p 0) ≤ 1
        have hz : prefixBitCount w true 0 = 0 := Nat.eq_zero_of_le_zero (prefixBitCount_le w true 0)
        rw [hz, sliceAverage_zero]
        exact hf₁ _
      have hstop : τ ≤ H ℓ := by
        change τ ≤ sliceAverage X f ℓ (prefixBitCount w true ℓ) (p ℓ)
        rw [hp.weight_eq, hp.endpoint_eq]
        exact ht
      have hh := hent ℓ hℓ hℓ₀ w (hp.weight_eq.symm ▸ hchoose) H V τ hτ' hstart hstop hp.height_le
        (fun i hi => slicePathHeight_step X f w p i (hp.step_eq i hi))
      exact_mod_cast hrk.trans hh
  have heq : (C / T₀) / (γ * τ) = C / (γ * L) := by dsimp [τ]; field_simp
  have hdrop : ((C / T₀) / (γ * τ)) ^ k ≤ Real.exp (-(M + 3) * (n : ℝ)) := by
    rw [heq]
    refine (pow_le_pow_left₀ (by positivity) hLu _).trans ?_
    dsimp [u]
    rw [← Real.exp_nat_mul]
    apply Real.exp_monotone
    have h := mul_le_mul_of_nonneg_right hk₀ (show 0 ≤ 4 * (M + 3) / κ by positivity)
    rw [show κ * (n : ℝ) / 4 * (4 * (M + 3) / κ) = (M + 3) * (n : ℝ) by field_simp] at h
    rw [show -4 * (M + 3) / κ = -(4 * (M + 3) / κ) by ring, mul_neg, neg_mul]
    exact neg_le_neg h
  have hcard : (Fintype.card G : ℝ) * (4 : ℝ) ^ ℓ ≤ Real.exp (3 * (n : ℝ)) := by
    have h₄ : (4 : ℝ) ^ ℓ ≤ (4 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hℓ
    calc
      _ ≤ (2 : ℝ) ^ n * (4 : ℝ) ^ n := by gcongr
      _ = (8 : ℝ) ^ n := by rw [← mul_pow]; norm_num
      _ ≤ _ := by
        have h₂ : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
        have h₈ : (8 : ℝ) ≤ Real.exp 3 := by
          have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h₂ 3
          rw [← Real.exp_nat_mul] at hh
          norm_num at hh
          exact hh
        rw [mul_comm (3 : ℝ), Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by norm_num) h₈ _
  refine hcount.trans ?_
  calc
    _ ≤ (Real.exp (3 * (n : ℝ)) * Real.exp (-(M + 3) * (n : ℝ))) * ∏ i, ((B i).card : ℝ) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end BooleanThreshold
