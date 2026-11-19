module

public import BooleanThreshold.JSSConditionalMixed
public import BooleanThreshold.JSSConditionalPairSwaps

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace BooleanThreshold

/-- Linearly many disjoint pairs with coefficients separated beyond the
interval radius give a square-root concentration bound on a fixed-weight slice. -/
theorem signSlice_smallBall_le_of_linear_pairs_eventually {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (k : ℕ) (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1)),
        σ * (n : ℝ) ≤ (k : ℝ) → η * (n : ℝ) ≤ (m.val : ℝ) →
        (m.val : ℝ) ≤ (1 - η) * (n : ℝ) →
        ∀ (a : Fin n → ℝ) (z r : ℝ),
          (∀ j, r < |a (e (j, false)) - a (e (j, true))|) →
        (uniformOn (signSlice n m)).real {x | |signSum a x - z| ≤ r} ≤ C / Real.sqrt (n : ℝ) := by
  obtain ⟨τ, hτ, c, hc, h⟩ := slice_pairs_many_mixed_eventually hη hσ
  let C := 1 + 4 / Real.sqrt τ
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hlimit := tendsto_pow_const_div_const_pow_of_one_lt 1 (Real.one_lt_exp_iff.mpr hc)
  filter_upwards [h, hlimit.eventually_le_const (show (0 : ℝ) < 1 from zero_lt_one),
    eventually_ge_atTop (1 : ℕ)] with n hn hpoly hn₁ k e m hk hml hmu a z r hgap
  let s := ⌊τ * (n : ℝ)⌋₊
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : (s : ℝ) ≤ τ * (n : ℝ) := Nat.floor_le (by positivity)
  have hs' : τ * (n : ℝ) < (s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsmall := signSlice_smallBall_le_of_pairs e m (signSlice_nonempty m) a z r hgap s
  have hmixed : (uniformOn (signSlice n m)).real {x : Fin n → Bool |
      (Finset.univ.filter fun j => x (e (j, false)) ≠ x (e (j, true))).card < s} ≤
        Real.exp (-c * (n : ℝ)) := by
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hn k e m hk hml hmu)
    intro x hx
    have hh : (((Finset.univ.filter fun j => x (e (j, false)) ≠ x (e (j, true))).card : ℕ) : ℝ) <
        (s : ℝ) := by exact_mod_cast hx
    exact hh.trans_le hs
  have hpow : (n : ℝ) * Real.exp (-c * (n : ℝ)) ≤ 1 := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, mul_comm c, Real.exp_nat_mul, ← pow_one (n : ℝ)]
    exact hpoly
  have hExp : Real.exp (-c * (n : ℝ)) ≤ 1 / Real.sqrt (n : ℝ) := by
    apply (le_div_iff₀ (Real.sqrt_pos_of_pos hn₀)).mpr
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)).trans hpow
    exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hn₁))
  have hroot : 4 / Real.sqrt ((s : ℝ) + 1) ≤ (4 / Real.sqrt τ) / Real.sqrt (n : ℝ) := by
    rw [div_div, ← Real.sqrt_mul hτ.le]
    exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos_of_pos (by positivity))
      (Real.sqrt_le_sqrt hs'.le)
  refine hsmall.trans ((add_le_add (hmixed.trans hExp) hroot).trans_eq ?_)
  rw [← add_div]

end BooleanThreshold
