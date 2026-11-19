module

public import BooleanThreshold.JSSConditionalPreprocess
public import BooleanThreshold.JSSConditionalPrefixMass
public import BooleanThreshold.JSSConditionalPathLocalMass
public import BooleanThreshold.JSSConditionalSplitCount

public section

open Filter
open scoped BigOperators Topology

namespace BooleanThreshold

/-- A single coordinate order supplies the preprocessing count and local mass
estimate for every balanced weight on the retained prefix. -/
theorem eventual_prefix_preprocessing_on_opposite_band {α : ℝ} (hα : 0 < α) (B : ℕ) :
    ∃ η > (0 : ℝ), ∃ R > (0 : ℝ), ∀ M ≥ (0 : ℝ), ∃ A ≥ (1 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (a b : ℕ) (hab : a + b = n), 3 / 4 * (n : ℝ) ≤ (a : ℝ) → (1 - η) * (n : ℝ) ≤ (a : ℝ) →
      ∀ (N P : ℕ) [NeZero P], 0 < N → (N : ℝ) ≤ (5 / 3 : ℝ) ^ n → 4 * n ^ 2 * N < P → P ≤ 2 ^ n →
      ∀ W : Fin n → Finset ℤ, oppositeBandBox n N B α W →
      ∃ π : Equiv.Perm (Fin n), ∀ q ≤ a, |2 * (q : ℝ) - (a : ℝ)| ≤ 2 * η * (a : ℝ) →
        ∀ f : ZMod P → ℝ, (∀ u, 0 ≤ f u) → (∑ u, f u) ≤ 1 →
        let D := sliceTuplePrefix hab (W ∘ π)
        ((highSliceAverages (fun z : ℤ => (z : ZMod P)) D f q (A / ((N : ℝ) * Real.sqrt (n : ℝ)))).card : ℝ) ≤
          Real.exp (-M * (n : ℝ)) * (((B : ℝ) + 1) * (N : ℝ)) ^ a ∧
        ∀ X ∈ Fintype.piFinset D, ∀ u : ZMod P,
          (∑ t ∈ cyclicInterval P N u,
            sliceAverage (sliceCoefficientArray (fun z : ℤ => (z : ZMod P)) X) f a q t) ≤
              R / Real.sqrt (n : ℝ) := by
  obtain ⟨η₀, hη₀, σ₀, hσ₀, β, hβ, hβ₁, hpre⟩ := eventually_sliceAverage_preprocess
  let η := min η₀ (1 / 2 - β)
  have hη : 0 < η := lt_min hη₀ (sub_pos.mpr hβ₁)
  have hηp : η ≤ η₀ := min_le_left _ _
  have hηq : η ≤ 1 / 2 - β := min_le_right _ _
  let σ := min σ₀ (1 / 2 : ℝ)
  have hσ : 0 < σ := lt_min hσ₀ (by norm_num)
  have hσ₀' : σ ≤ σ₀ := min_le_left _ _
  have hσ₁ : σ ≤ 1 / 2 := min_le_right _ _
  let c := min α (σ / 2)
  have hc : 0 < c := lt_min hα (by positivity)
  have hcα : c ≤ α := min_le_left _ _
  have hcσ : c ≤ σ / 2 := min_le_right _ _
  obtain ⟨R, hR, hmass⟩ := oppositeBandBox_prefix_local_mass_eventually hβ (by positivity : 0 < c / 2) hσ
  let C := ((B : ℝ) + 1) * R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨K, hK⟩ := exists_nat_ge (2 / c)
  refine ⟨η, hη, R, hR, fun M hM => ?_⟩
  obtain ⟨A, hA, hAev⟩ := hpre C hC M hM
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAev, hmass, eventually_ge_atTop (max K (B + 1))] with n hpren hmassn hnK
  intro a b hab ha haNear N P _ hN hNhi hP hP₂ W hW
  let k := ⌊c * (n : ℝ)⌋₊
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcn : 2 ≤ c * (n : ℝ) := by
    rw [mul_comm]
    apply (div_le_iff₀ hc).mp
    exact hK.trans (by exact_mod_cast (le_max_left _ _).trans hnK)
  have hklo : (c / 2) * (n : ℝ) ≤ (k : ℝ) := by
    have h := Nat.lt_floor_add_one (c * (n : ℝ))
    change c * (n : ℝ) < (k : ℝ) + 1 at h
    linarith only [h, hcn]
  have hkhi : (k : ℝ) ≤ c * (n : ℝ) := Nat.floor_le (by positivity)
  have hkα := hkhi.trans (mul_le_mul_of_nonneg_right hcα hnR)
  have hkσ : (2 : ℝ) * (k : ℝ) ≤ σ * (n : ℝ) := by
    have h := hkhi.trans (mul_le_mul_of_nonneg_right hcσ hnR)
    linarith only [h]
  have hBN : (B + 1) * N ≤ P := by
    have hB : B + 1 ≤ n := (le_max_right _ _).trans hnK
    refine (Nat.mul_le_mul_right N hB).trans ?_
    have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    exact ((Nat.mul_le_mul_right N (hnn.trans (by omega : n ^ 2 ≤ 4 * n ^ 2))).trans hP.le)
  obtain ⟨π, hπ⟩ := hmassn N B k α W hN hW hklo hkα
  refine ⟨π, fun q hq hqbal f hf hsum => ?_⟩
  let D := sliceTuplePrefix hab (W ∘ π)
  let e (z : ℤ) : ZMod P := z
  have ha₀ : 0 < a := by
    exact_mod_cast ((show 0 < 3 / 4 * (n : ℝ) by positivity).trans_le ha)
  have ha₁ : a ≤ n := by omega
  have ha₂ : σ * (n : ℝ) ≤ (a : ℝ) := (mul_le_mul_of_nonneg_right hσ₁ hnR).trans (by linarith only [ha, hnR])
  have haNear' : (1 - η₀) * (n : ℝ) ≤ (a : ℝ) :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hηp 1) hnR).trans haNear
  have hqbal' : |2 * (q : ℝ) - (a : ℝ)| ≤ 2 * η₀ * (a : ℝ) := by
    refine hqbal.trans ?_
    gcongr
  have hq₀ : β * (a : ℝ) ≤ (q : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hηq (show (0 : ℝ) ≤ a from Nat.cast_nonneg a)
    nlinarith only [(abs_le.mp hqbal).1, hh]
  have hq₁ : (q : ℝ) ≤ (1 - β) * (a : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hηq (show (0 : ℝ) ≤ a from Nat.cast_nonneg a)
    nlinarith only [(abs_le.mp hqbal).2, hh]
  have hf₁ (t : ZMod P) : f t ≤ 1 :=
    (Finset.single_le_sum (fun i _ => hf i) (Finset.mem_univ t)).trans hsum
  have hcardG : (Fintype.card (ZMod P) : ℝ) ≤ (2 : ℝ) ^ n := by
    rw [ZMod.card]
    exact_mod_cast hP₂
  have hD (i : Fin a) : (∃ l u : ℤ, D i = Finset.Ico l u) ∧
      2 * N + 1 ≤ (D i).card ∧ (D i).card ≤ (B + 1) * N := ⟨(hW.1 _).1, (hW.1 _).2.1, (hW.1 _).2.2.1⟩
  have hDne (i : Fin a) : (D i).Nonempty := Finset.card_pos.mp (by have := (hD i).2.1; omega)
  have hLocal (ℓ : ℕ) (hℓ : ℓ ≤ a) (hℓn : σ * (n : ℝ) ≤ (ℓ : ℝ)) (s : ℕ) (hs : s ≤ ℓ)
      (hslow : β * (ℓ : ℝ) ≤ s) (hshi : (s : ℝ) ≤ (1 - β) * (ℓ : ℝ))
      (X : Fin a → ℤ) (hX : ∀ j, X j ∈ D j) (u : ZMod P) :
      (∑ t ∈ cyclicInterval P N u, sliceAverage (sliceCoefficientArray e X) f ℓ s t) ≤ R / Real.sqrt (n : ℝ) := by
    let z := sliceCoefficientArray id X
    let s₀ : Fin (ℓ + 1) := ⟨s, Nat.lt_succ_of_le hs⟩
    have hkℓ : 2 * k ≤ ℓ := by exact_mod_cast hkσ.trans hℓn
    have hcoef (j : Fin ℓ) : z j.val ∈ W (π (Fin.castLEEmb (hℓ.trans ha₁) j)) := by
      let j₀ : Fin a := Fin.castLEEmb hℓ j
      have hj : z j.val = X j₀ := sliceCoefficientArray_apply id X j₀
      rw [hj]
      exact hX j₀
    have hcast : (fun i => (z i : ZMod P)) = sliceCoefficientArray e X := by
      funext i
      by_cases hi : i < a <;> simp [z, sliceCoefficientArray, e, hi]
    simpa only [hcast] using hπ ℓ (hℓ.trans ha₁) hℓn hkℓ s₀ hslow hshi P hP z hcoef f hf hsum u
  refine ⟨?_, fun X hX u => hLocal a le_rfl ha₂ q hq hq₀ hq₁ X (Fintype.mem_piFinset.mp hX) u⟩
  have hCount := hpren a ha₁ ha₀ haNear' q hq hqbal' N hN hNhi (ZMod P) hcardG e D hDne f hf hf₁
    (fun i hi s hs hslow hshi X hX y b' => ?_)
  · refine hCount.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
    rw [← show (∏ _i : Fin a, (((B : ℝ) + 1) * (N : ℝ))) = (((B : ℝ) + 1) * (N : ℝ)) ^ a by simp]
    exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => by exact_mod_cast (hD i).2.2
  have hℓn : σ * (n : ℝ) ≤ (i.val : ℝ) := (mul_le_mul_of_nonneg_right hσ₀' hnR).trans hi
  have hMass := hLocal i.val i.isLt.le hℓn s hs hslow hshi X hX
  have hWidth := (hD i).2.1
  have hNlo : N ≤ (D i).card := by omega
  have hP' : (D i).card ≤ P := (hD i).2.2.trans hBN
  simpa only [C, Nat.cast_add, Nat.cast_one, e] using
    sliceAverage_preprocess_local_bound (K := B + 1) hN (D i) (hD i).1 hNlo (hD i).2.2 hP'
      (sliceCoefficientArray e X) f hf i.val s hR.le hMass y b'

end BooleanThreshold
