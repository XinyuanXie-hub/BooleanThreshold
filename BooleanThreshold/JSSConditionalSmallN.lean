module

public import BooleanThreshold.JSSConditionalLocalBound
public import BooleanThreshold.JSSConditionalBandPairs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- For interval widths at most `√n`, the separated-pair estimate at radius
`N` also bounds the small ball at radius `2√n`, after covering that larger
interval by intervals at radius `N`. -/
theorem signSlice_smallBall_smallN_eventually {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (k : ℕ) (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1)),
        σ * (n : ℝ) ≤ (k : ℝ) → η * (n : ℝ) ≤ (m.val : ℝ) →
        (m.val : ℝ) ≤ (1 - η) * (n : ℝ) →
        ∀ (a : Fin n → ℝ) (N z : ℝ), 0 < N → N ≤ Real.sqrt (n : ℝ) →
          (∀ j, N < |a (e (j, false)) - a (e (j, true))|) →
          (uniformOn (signSlice n m)).real {x | |signSum a x - z| ≤ 2 * Real.sqrt (n : ℝ)} ≤ C / N := by
  obtain ⟨C, hC, hsmall⟩ := signSlice_smallBall_le_of_linear_pairs_eventually hη hσ
  refine ⟨5 * C, by positivity, hsmall.mono ?_⟩
  intro n hn k e m hk hlow hhigh a N z hN hNs hsep
  let μ := uniformOn (signSlice n m)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOn (signSlice n m).toFinite (signSlice_nonempty m)
  let s := Real.sqrt (n : ℝ)
  let B := ⌊4 * s / N⌋₊ + 1
  let w (i : ℕ) := z - 2 * s + (i : ℝ) * N
  let E (i : ℕ) : Set (Fin n → Bool) := {x | |signSum a x - w i| ≤ N}
  have hs : 0 < s := hN.trans_le hNs
  have hsubset : {x | |signSum a x - z| ≤ 2 * s} ⊆ ⋃ i ∈ Finset.range B, E i := by
    intro x hx
    have hx' : |signSum a x - z| ≤ 2 * s := hx
    obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx'
    let t := signSum a x - (z - 2 * s)
    have ht₀ : 0 ≤ t := by dsimp [t]; linarith only [hx₁]
    have ht₁ : t ≤ 4 * s := by dsimp [t]; linarith only [hx₂]
    let i := ⌊t / N⌋₊
    have hi : i ∈ Finset.range B := by
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right ht₁ hN.le))
    have hilow : (i : ℝ) * N ≤ t :=
      (le_div_iff₀ hN).mp (Nat.floor_le (by positivity))
    have hihi : t < ((i : ℝ) + 1) * N := (div_lt_iff₀ hN).mp (Nat.lt_floor_add_one _)
    refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    change |signSum a x - w i| ≤ N
    have hEq : signSum a x - w i = t - (i : ℝ) * N := by dsimp [w, t]; ring
    rw [hEq, abs_of_nonneg (sub_nonneg.mpr hilow)]
    linarith only [hihi]
  have hB : (B : ℝ) ≤ 5 * s / N := by
    have hf : (⌊4 * s / N⌋₊ : ℝ) ≤ 4 * s / N := Nat.floor_le (by positivity)
    have hn' : (1 : ℝ) ≤ s / N := (le_div_iff₀ hN).mpr (by simpa only [one_mul] using hNs)
    dsimp only [B]
    push_cast
    linarith only [hf, hn', show 4 * s / N = 4 * (s / N) by ring,
      show 5 * s / N = 5 * (s / N) by ring]
  change μ.real {x | |signSum a x - z| ≤ 2 * s} ≤ _
  calc
    _ ≤ μ.real (⋃ i ∈ Finset.range B, E i) := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.range B, μ.real (E i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range B, C / s := Finset.sum_le_sum fun i _ => hn k e m hk hlow hhigh a (w i) N hsep
    _ = (B : ℝ) * (C / s) := by simp
    _ ≤ (5 * s / N) * (C / s) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = _ := by field_simp

theorem oppositeBand_signSlice_smallBall_smallN_eventually {η α : ℝ}
    (hη : 0 < η) (hα : 0 < α) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (N B : ℕ) (P : Fin n → Finset ℤ), 0 < N → (N : ℝ) ≤ Real.sqrt (n : ℝ) →
        oppositeBandBox n N B α P → ∀ m : Fin (n + 1),
        η * (n : ℝ) ≤ (m.val : ℝ) → (m.val : ℝ) ≤ (1 - η) * (n : ℝ) →
        ∀ (a : Fin n → ℤ), (∀ i, a i ∈ P i) → ∀ z : ℝ,
        (uniformOn (signSlice n m)).real
          {x | |signSum (fun i => (a i : ℝ)) x - z| ≤ 2 * Real.sqrt (n : ℝ)} ≤ C / (N : ℝ) := by
  obtain ⟨C, hC, hsmall⟩ := signSlice_smallBall_smallN_eventually hη (show 0 < α / 2 by positivity)
  obtain ⟨A, hA⟩ := exists_nat_ge (2 / α)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsmall, eventually_ge_atTop A] with n hn hnA
  intro N B P hN hNs hbox m hml hmu a ha z
  let k := ⌊α * (n : ℝ)⌋₊
  have hk₀ : (k : ℝ) ≤ α * (n : ℝ) := Nat.floor_le (by positivity)
  have hαn : (2 : ℝ) ≤ α * n := by
    rw [mul_comm α]
    exact (div_le_iff₀ hα).mp (hA.trans (by exact_mod_cast hnA))
  have hk₁ : (α / 2) * (n : ℝ) ≤ k := by
    have hklo := Nat.lt_floor_add_one (α * (n : ℝ))
    change α * (n : ℝ) < (k : ℝ) + 1 at hklo
    linarith only [hklo, hαn]
  obtain ⟨e, heL, heR⟩ := oppositeBandBox_exists_pairs hbox hk₀
  refine hn k e m hk₁ hml hmu (fun i => (a i : ℝ)) N z (by exact_mod_cast hN) hNs ?_
  intro j
  have hL : (a (e (j, false)) : ℝ) ≤ -2 * (N : ℝ) := by exact_mod_cast heL j _ (ha _)
  have hR : (2 : ℝ) * (N : ℝ) ≤ a (e (j, true)) := by exact_mod_cast heR j _ (ha _)
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  exact (show (N : ℝ) < -((a (e (j, false)) : ℝ) - (a (e (j, true)) : ℝ)) by
    linarith only [hL, hR, hp]).trans_le (neg_le_abs _)

end BooleanThreshold
