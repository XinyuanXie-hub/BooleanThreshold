module

public import BooleanThreshold.JSSStructuredConditioning
public import BooleanThreshold.KKSLargeShift
public import BooleanThreshold.SignSymmetry
public import Mathlib.Order.Filter.AtTopBot.Finset

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

/-- A null vector close to a two-column difference whose image is nonzero. -/
def nonzeroNearColumnDifference {n : ℕ} (K ε : ℝ) (i j : Fin n) :
    Set (Fin n → Fin n → Bool) :=
  {M | (∃ r, M r i ≠ M r j) ∧ signOpBound K M ∧ ∃ a, signMatrixMap M a = 0 ∧
    squaredNorm (Pi.single i 1 - Pi.single j 1 - a) ≤ ε ^ 2}

theorem uniformOn_nonzeroNearColumnDifference_le {n k : ℕ} {K ε q : ℝ}
    (hε : ε ^ 2 < 1) (hsparse : K ^ 2 * ((n + 2 : ℕ) : ℝ) * ε ^ 2 ≤ 4 * (k : ℝ))
    (i j : Fin (n + 2)) (hij : i ≠ j) (hq : 0 ≤ q)
    (hshift : ∀ D : Fin (n + 1) → Fin (n + 1) → ℤ,
      (uniformOn Set.univ).real {X : Fin (n + 1) → Fin (n + 1) → Bool |
        ∃ a : Fin (n + 1) → ℝ, a ≠ 0 ∧
          ∀ r, ∑ j, a j * (realSigns (X r) j + (D r j : ℝ)) = 0} ≤ q) :
    (uniformOn Set.univ).real (nonzeroNearColumnDifference K ε i j) ≤
      q * 2 ^ k * ((1 / 2 : ℝ) ^ (n + 2) *
        ∑ l ∈ Finset.range (k + 1), ((n + 2).choose l : ℝ)) := by
  let E : Set (Fin (n + 2) → Fin (n + 2) → Bool) := {M |
    (fun r => differenceCode (M r i) (M r j)) ≠ (fun _ => none) ∧
    signOpBound K M ∧ ∃ a, signMatrixMap M a = 0 ∧
      squaredNorm (Pi.single i 1 - Pi.single j 1 - a) ≤ ε ^ 2}
  have hE : E = nonzeroNearColumnDifference K ε i j := by
    ext M
    change ((fun r => differenceCode (M r i) (M r j)) ≠ (fun _ => none) ∧ _) ↔
      ((∃ r, M r i ≠ M r j) ∧ _)
    refine and_congr ?_ Iff.rfl
    constructor
    · intro hp
      by_contra! hn
      exact hp (funext fun r => by simp [differenceCode, hn r])
    · rintro ⟨r, hr⟩ hp
      exact (differenceCode_ne_none_iff _ _).mpr hr (congrFun hp r)
  have h := uniformOn_nonzeroNearPair_le_of_conditional hε hsparse i j hij
    (fun d hd hk => uniformOn_targetSpan_le_of_shifted i j hij d hd hk hq hshift)
  have hhalf : (1 / 2 : ℝ≥0∞) ≠ ∞ := ENNReal.div_ne_top (by simp) (by simp)
  have hfin : ENNReal.ofReal (q * 2 ^ k) * ((1 / 2 : ℝ≥0∞) ^ (n + 2) *
      ∑ l ∈ Finset.range (k + 1), ((n + 2).choose l : ℝ≥0∞)) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top hhalf)
        (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.natCast_ne_top _))
  have hr := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_sum (fun _ _ => ENNReal.natCast_ne_top _)] at hr
  simpa only [← measureReal_def, ← hE, E, ENNReal.toReal_natCast] using hr

/-- A uniform exponential bound for shifted squares gives an exponentially
smaller than `2⁻ⁿ` error for the null event near a fixed column difference. -/
theorem eventually_uniformOn_nonzeroNearColumnDifference_le {c C K : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C)
    (hshift : ∀ᶠ n : ℕ in atTop, ∀ D : Fin (n + 1) → Fin (n + 1) → ℤ,
      (uniformOn Set.univ).real {X : Fin (n + 1) → Fin (n + 1) → Bool |
        ∃ a : Fin (n + 1) → ℝ, a ≠ 0 ∧
          ∀ r, ∑ j, a j * (realSigns (X r) j + (D r j : ℝ)) = 0} ≤
        C * Real.exp (-c * ((n + 1 : ℕ) : ℝ))) :
    ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ i j : Fin (n + 2), i ≠ j →
      (uniformOn Set.univ).real (nonzeroNearColumnDifference K ε i j) ≤
        C * Real.exp (-(c / 4) * ((n + 2 : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ (n + 2) := by
  obtain ⟨δ, hδ, hcount⟩ := exists_sparse_count_growth_bound (B := 2)
    (R := Real.exp (c / 4)) (by norm_num) (Real.one_lt_exp_iff.mpr (by positivity))
  let b := min δ 1
  have hb : 0 < b := lt_min hδ zero_lt_one
  let ε := min (1 / 2) (Real.sqrt b / (1 + |K|))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε₂ : ε ^ 2 < 1 := by
    have h := pow_le_pow_left₀ hε.le (min_le_left (1 / 2 : ℝ) (Real.sqrt b / (1 + |K|))) 2
    linarith only [h]
  have hKε : K ^ 2 * ε ^ 2 ≤ b := by
    have h := (le_div_iff₀ (show 0 < 1 + |K| by positivity)).mp
      (min_le_right (1 / 2 : ℝ) (Real.sqrt b / (1 + |K|)))
    calc
      _ = (ε * |K|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ ≤ (Real.sqrt b) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        calc
          _ ≤ ε * (1 + |K|) := by linarith only [hε]
          _ ≤ _ := h
      _ = _ := Real.sq_sqrt hb.le
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / b)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hshift, Filter.eventually_ge_atTop N] with n hs hn i j hij
  let k := ⌊b * ((n + 2 : ℕ) : ℝ)⌋₊
  have hnm : (N : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn.trans (by omega : n ≤ n + 2)
  have hbm : 2 ≤ b * ((n + 2 : ℕ) : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hb).mp (hN.trans hnm)
  have hk : (k : ℝ) ≤ b * ((n + 2 : ℕ) : ℝ) := Nat.floor_le (by positivity)
  have hk' := Nat.lt_floor_add_one (b * ((n + 2 : ℕ) : ℝ))
  have hsparse : K ^ 2 * ((n + 2 : ℕ) : ℝ) * ε ^ 2 ≤ 4 * (k : ℝ) := by
    calc
      _ = K ^ 2 * ε ^ 2 * ((n + 2 : ℕ) : ℝ) := by ring
      _ ≤ b * ((n + 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hKε (Nat.cast_nonneg _)
      _ ≤ _ := by change b * ((n + 2 : ℕ) : ℝ) < (k : ℝ) + 1 at hk'; linarith
  have hkn : k ≤ n + 2 := by
    have hh : (k : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := hk.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right δ 1)
        (Nat.cast_nonneg (n + 2)))
    exact_mod_cast hh
  have hkδ := hk.trans (mul_le_mul_of_nonneg_right (min_le_left δ 1) (Nat.cast_nonneg (n + 2)))
  have h := uniformOn_nonzeroNearColumnDifference_le hε₂ hsparse i j hij (by positivity) hs
  refine h.trans ?_
  calc
    _ = C * Real.exp (-c * ((n + 1 : ℕ) : ℝ)) *
        ((∑ l ∈ Finset.range (k + 1), ((n + 2).choose l : ℝ)) * 2 ^ k) *
        (1 / 2 : ℝ) ^ (n + 2) := by ring
    _ ≤ C * Real.exp (-c * ((n + 1 : ℕ) : ℝ)) * Real.exp (c / 4) ^ (n + 2) *
        (1 / 2 : ℝ) ^ (n + 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcount (n + 2) k hkn hkδ) (by positivity)) (by positivity)
    _ ≤ _ := by
      rw [← Real.exp_nat_mul, mul_assoc C, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hC
      push_cast
      nlinarith only [show (n : ℝ) * c ≥ 0 by positivity]

/-- The shifted-square estimate supplies the near-column-difference rate uniformly in the pair. -/
theorem eventually_uniformOn_nonzeroNearColumnDifference (K : ℝ) :
    ∃ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, ∀ i j : Fin (n + 2), i ≠ j →
        (uniformOn Set.univ).real (nonzeroNearColumnDifference K ε i j) ≤
          C * Real.exp (-c * ((n + 2 : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ (n + 2) := by
  obtain ⟨c, hc, C, hC, hshift⟩ := kks_shifted_sign_singularity
  obtain ⟨N, hN⟩ := eventually_atTop.mp hshift
  obtain ⟨ε, hε, h⟩ := eventually_uniformOn_nonzeroNearColumnDifference_le (K := K) hc hC.le
    (eventually_atTop.mpr ⟨N, fun n hn => hN (n + 1) (by omega)⟩)
  exact ⟨ε, hε, c / 4, by positivity, C, hC, h⟩

end BooleanThreshold
