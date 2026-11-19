module

public import BooleanThreshold.JSSConditionalSparsePeaks
public import BooleanThreshold.JSSConditionalFourierShift

public noncomputable section

open scoped BigOperators Classical ZMod

namespace BooleanThreshold

theorem cyclicShiftSmoothing_re_le {P m : ℕ} {f : ZMod P → ℂ} {c : ℝ}
    (hf : ∀ t, (f t).re ≤ c) (y : Fin m → ℤ) (t : ZMod P) :
    (cyclicShiftSmoothing f y t).re ≤ c := by
  induction m generalizing t with
  | zero => exact hf t
  | succ m ih =>
    rw [cyclicShiftSmoothing, cyclicShiftAverage, div_eq_mul_inv]
    have h₁ := ih (Fin.tail y) t
    have h₂ := ih (Fin.tail y) (t + (y 0 : ZMod P))
    norm_num [Complex.mul_re, Complex.add_re]
    linarith only [h₁, h₂]

theorem cyclicShiftSmoothing_add {P m : ℕ} (f g : ZMod P → ℂ) (y : Fin m → ℤ) :
    cyclicShiftSmoothing (f + g) y =
      cyclicShiftSmoothing f y + cyclicShiftSmoothing g y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cyclicShiftSmoothing, ih, cyclicShiftSmoothing, cyclicShiftSmoothing]
    funext t
    simp only [cyclicShiftAverage, Pi.add_apply]
    ring

private theorem cyclicShiftMultiplier_norm_le_one {P : ℕ} [NeZero P] (k : ZMod P) (y : ℤ) :
    ‖cyclicShiftMultiplier k y‖ ≤ 1 := by
  rw [cyclicShiftMultiplier, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_one (by norm_num)]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar ((y : ZMod P) * k)‖ := norm_add_le _ _
    _ = _ := by norm_num

private theorem cyclicFourierEnergy_smoothing_le {P m : ℕ} [NeZero P]
    (S : Finset (ZMod P)) (f : ZMod P → ℂ) (y : Fin m → ℤ) :
    cyclicFourierEnergy S (cyclicShiftSmoothing f y) ≤ cyclicFourierEnergy S f := by
  apply Finset.sum_le_sum
  intro k _
  rw [dft_cyclicShiftSmoothing, norm_mul, norm_prod]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_left (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun i _ => cyclicShiftMultiplier_norm_le_one k (y i)))

/-- After one block of shifts has reduced the high-frequency energy, a
second block must repeatedly land on a small peak set to preserve a large value. -/
theorem two_block_cyclic_smoothing_card_le {P m₁ m₂ N d j p : ℕ} [NeZero P]
    {a θ q : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hq : 0 ≤ q) (hN : 0 < N)
    (hd : d ≤ N) (hj : j ≤ m₂)
    (f : ZMod P → ℂ) (S : Finset (ZMod P))
    (B₁ : Fin m₁ → Finset ℤ) (B₂ : Fin m₂ → Finset ℤ)
    (hB₁ : ∀ i, (B₁ i).card = N) (hB₂ : ∀ i, (B₂ i).card = N)
    (hinj : ∀ i, Set.InjOn (fun x : ℤ => (x : ZMod P)) (B₂ i))
    (hmul : ∀ i k, k ∈ S →
      ∑ y ∈ B₁ i, ‖cyclicShiftMultiplier k y‖ ^ (2 * p) ≤ q * (B₁ i).card)
    (hband : ∀ k ∉ S, 𝓕 f k = 0)
    (henergy : θ * cyclicFourierEnergy S f ≤ (P : ℝ) * (d : ℝ) * (a / 2) ^ 2)
    (hcap : ∀ t, (f t).re ≤ a + (j : ℝ) * (a / 2)) :
    (((Fintype.piFinset B₁).product (Fintype.piFinset B₂)).filter fun y =>
      ∃ t, a ≤ (cyclicShiftSmoothing (cyclicShiftSmoothing f y.1) y.2 t).re).card ≤
        (q ^ m₁ / θ ^ p + (P : ℝ) * (4 : ℝ) ^ m₂ * ((d : ℝ) / (N : ℝ)) ^ (m₂ - j)) *
          (N : ℝ) ^ (m₁ + m₂) := by
  let A₁ := Fintype.piFinset B₁
  let A₂ := Fintype.piFinset B₂
  let g (y₁ : Fin m₁ → ℤ) := cyclicShiftSmoothing f y₁
  let E := cyclicFourierEnergy S f
  let C (y₁ : Fin m₁ → ℤ) :=
    A₂.filter fun y₂ => ∃ t, a ≤ (cyclicShiftSmoothing (g y₁) y₂ t).re
  let A₀ := A₁.filter fun y₁ => (P : ℝ) * (d : ℝ) * (a / 2) ^ 2 < cyclicFourierEnergy S (g y₁)
  have hA₁ : A₁.card = N ^ m₁ := by simp [A₁, Fintype.card_piFinset, hB₁]
  have hA₂ : A₂.card = N ^ m₂ := by simp [A₂, Fintype.card_piFinset, hB₂]
  have hA₀ : (A₀.card : ℝ) ≤ (q ^ m₁ / θ ^ p) * (N : ℝ) ^ m₁ := by
    by_cases hpos : 0 < E
    · have hsub : A₀ ⊆ A₁.filter (fun y₁ => θ * E ≤ cyclicFourierEnergy S (g y₁)) := by
        intro y₁ hy₁
        obtain ⟨hA, hE⟩ := Finset.mem_filter.mp hy₁
        exact Finset.mem_filter.mpr ⟨hA, henergy.trans hE.le⟩
      refine (show (A₀.card : ℝ) ≤ _ from Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ?_
      simpa only [A₁, E, g, hB₁, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        cyclicShiftSmoothing_card_energy_ge_le (p := p) f S B₁ hθ hpos hmul
    · have hE : E = 0 := le_antisymm (le_of_not_gt hpos)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hEmpty : A₀ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun y₁ hy₁ => by
        have h := cyclicFourierEnergy_smoothing_le S f y₁
        change cyclicFourierEnergy S (g y₁) ≤ E at h
        rw [hE] at h
        exact (not_lt_of_ge (h.trans (by positivity))) (Finset.mem_filter.mp hy₁).2
      rw [hEmpty, Finset.card_empty, Nat.cast_zero]
      positivity
  have hC (y₁ : Fin m₁ → ℤ) (hy₁ : y₁ ∈ A₁ \ A₀) :
      (C y₁).card ≤ P * 4 ^ m₂ * (d ^ (m₂ - j) * N ^ j) := by
    have h := Finset.mem_sdiff.mp hy₁
    have hE : cyclicFourierEnergy S (g y₁) ≤ (P : ℝ) * (d : ℝ) * (a / 2) ^ 2 :=
      le_of_not_gt fun hlt => h.2 (Finset.mem_filter.mpr ⟨h.1, hlt⟩)
    have hfull : cyclicFourierEnergy Finset.univ (g y₁) = cyclicFourierEnergy S (g y₁) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro k _ hk
      simp [g, dft_cyclicShiftSmoothing, hband k hk]
    have hsum := (cyclicFourierEnergy_univ (g y₁)).symm.trans hfull
    rw [mul_assoc] at hE
    have hP : (0 : ℝ) < P := Nat.cast_pos.mpr (NeZero.pos P)
    have hE' : ∑ t, ‖g y₁ t‖ ^ 2 ≤ (d : ℝ) * (a / 2) ^ 2 := by
      apply (mul_le_mul_iff_of_pos_left hP).mp
      rw [hsum]
      exact hE
    exact cyclicShiftSmoothing_card_high_re_le ha B₂ hB₂ hinj hd hj (g y₁) hE'
      (cyclicShiftSmoothing_re_le hcap y₁)
  let X := (A₁.product A₂).filter fun y =>
    ∃ t, a ≤ (cyclicShiftSmoothing (g y.1) y.2 t).re
  have hcover : X ⊆ (A₀.product A₂) ∪ (A₁ \ A₀).biUnion (fun x => (C x).image (Prod.mk x)) := by
    rintro ⟨x, y⟩ hz
    obtain ⟨hxy, ht⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    by_cases h : x ∈ A₀
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨h, hy⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, h⟩,
        Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, ht⟩, rfl⟩⟩)
  have hcount : X.card ≤ A₀.card * A₂.card +
      A₁.card * (P * 4 ^ m₂ * (d ^ (m₂ - j) * N ^ j)) := by
    refine (Finset.card_le_card hcover).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have hprod : (A₀.product A₂).card = A₀.card * A₂.card := Finset.card_product A₀ A₂
    rw [hprod]
    apply Nat.add_le_add_left
    refine Finset.card_biUnion_le.trans ?_
    calc
      _ ≤ ∑ _x ∈ A₁ \ A₀, P * 4 ^ m₂ * (d ^ (m₂ - j) * N ^ j) :=
        Finset.sum_le_sum fun x hx => Finset.card_image_le.trans (hC x hx)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
  change (X.card : ℝ) ≤ _
  have hN₀ : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  calc
    _ ≤ (A₀.card : ℝ) * (N : ℝ) ^ m₂ +
        (N : ℝ) ^ m₁ * ((P : ℝ) * 4 ^ m₂ * ((d : ℝ) ^ (m₂ - j) * (N : ℝ) ^ j)) := by
      rw [hA₁, hA₂] at hcount
      exact_mod_cast hcount
    _ ≤ (q ^ m₁ / θ ^ p) * (N : ℝ) ^ m₁ * (N : ℝ) ^ m₂ +
        (N : ℝ) ^ m₁ * ((P : ℝ) * 4 ^ m₂ * ((d : ℝ) ^ (m₂ - j) * (N : ℝ) ^ j)) :=
      add_le_add (mul_le_mul_of_nonneg_right hA₀ (by positivity)) le_rfl
    _ = _ := by
      rw [add_mul, div_pow, pow_add]
      have hmul' : ((d : ℝ) ^ (m₂ - j) / (N : ℝ) ^ (m₂ - j)) * (N : ℝ) ^ m₂ =
          (d : ℝ) ^ (m₂ - j) * (N : ℝ) ^ j := by
        have hpow := pow_add (N : ℝ) (m₂ - j) j
        rw [Nat.sub_add_cancel hj] at hpow
        rw [hpow]
        field_simp
      rw [← hmul']
      ring

end BooleanThreshold
