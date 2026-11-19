module

public import BooleanThreshold.CokernelBounds
public import BooleanThreshold.SpanCokernelReduction
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Filter MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- The finite sign-span bound divided by the size of the sample space. -/
theorem sign_span_failure_fraction_le (N B : ℕ) :
    (Nat.card {R : Fin (N + 1) → Fin (N + 2) → Bool // ¬ SignSpanGood R} : ℝ) /
        ((2 : ℝ) ^ (N + 2)) ^ (N + 1) ≤
      3 * (uniformOn Set.univ).real
        {A : Fin N → Fin (N + 1) → Bool |
          binaryCokernelIndex A = 0 ∨ B < binaryCokernelIndex A} +
      (Nat.card {R : Fin (N + 1) → Fin (N + 2) → Bool //
        HasSmallSignRelation B R} : ℝ) / ((2 : ℝ) ^ (N + 2)) ^ (N + 1) := by
  let S := {R : Fin (N + 1) → Fin (N + 2) → Bool // HasSmallSignRelation B R}
  let D := {A : Fin N → Fin (N + 1) → Bool |
    binaryCokernelIndex A = 0 ∨ B < binaryCokernelIndex A}
  have h := card_bad_signSpan_le_cokernel (N + 1) N B
  rw [card_bad_signCokernelIndex] at h
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  change _ ≤ 3 * ((2 : ℝ) ^ (N + 2 + N) * (D.ncard : ℝ)) + (Nat.card S : ℝ) at h
  have hQ : (uniformOn Set.univ).real D = (D.ncard : ℝ) / ((2 : ℝ) ^ (N + 1)) ^ N := by
    rw [uniformOn_univ_real_eq_card]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  have hscale : ((2 : ℝ) ^ (N + 2)) ^ (N + 1) =
      (2 : ℝ) ^ (N + 2 + N) * ((2 : ℝ) ^ (N + 1)) ^ N := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hdiv : ((2 : ℝ) ^ (N + 2 + N) * (D.ncard : ℝ)) / ((2 : ℝ) ^ (N + 2)) ^ (N + 1) =
      (uniformOn Set.univ).real D := by
    rw [hQ, hscale, mul_div_mul_left]
    positivity
  calc
    _ ≤ (3 * ((2 : ℝ) ^ (N + 2 + N) * (D.ncard : ℝ)) + (Nat.card S : ℝ)) /
        ((2 : ℝ) ^ (N + 2)) ^ (N + 1) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by rw [add_div, mul_div_assoc, hdiv]

/-- The endpoint of the sign-span estimate follows from Proposition 2 and
the bound on small-coefficient extra relations. -/
theorem sign_span_bound_of_cokernel_and_small_relations {b : ℝ} (hb : 0 < b)
    (cokernel_bound : ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {A : Fin N → Fin (N + 1) → Bool |
          binaryCokernelIndex A = 0 ∨ Real.exp (b * (N : ℝ)) < (binaryCokernelIndex A : ℝ)} ≤
        C / (N : ℝ) ^ 99)
    (small_relation_bound : ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (Nat.card {R : Fin n → Fin (n + 1) → Bool //
        HasSmallSignRelation ⌊Real.exp (b * ((n + 1 : ℕ) : ℝ))⌋₊ R} : ℝ) /
        ((2 : ℝ) ^ (n + 1)) ^ n ≤ C / (n : ℝ) ^ 99) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Nat.card {v : Fin n → Fin (n + 1) → Bool // ¬ SignSpanGood v} : ℝ) ≤
        (C / (n : ℝ) ^ 99) * ((2 : ℝ) ^ (n + 1)) ^ n := by
  obtain ⟨A, hA, htA⟩ := cokernel_bound
  obtain ⟨D, hD, htD⟩ := small_relation_bound
  obtain ⟨a, ha⟩ := eventually_atTop.mp htA
  obtain ⟨d, hd⟩ := eventually_atTop.mp htD
  refine ⟨3 * A * (2 : ℝ) ^ 99 + D, eventually_atTop.mpr ⟨max (a + 1) (max d 2), ?_⟩⟩
  intro n hn
  cases n with
  | zero => omega
  | succ N =>
    let B := ⌊Real.exp (b * ((N + 2 : ℕ) : ℝ))⌋₊
    have hN : 1 ≤ N := by omega
    have hP :
        (uniformOn Set.univ).real
          {A : Fin N → Fin (N + 1) → Bool |
            binaryCokernelIndex A = 0 ∨ B < binaryCokernelIndex A} ≤ A / (N : ℝ) ^ 99 := by
      apply (measureReal_mono ?_).trans (ha N (by omega))
      intro M hM
      rcases hM with hM | hM
      · exact Or.inl hM
      · right
        have hsmall : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ N + 2 by omega)
        exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsmall hb.le)).trans_lt
          (Nat.lt_of_floor_lt hM)
    have hscale : ((N + 1 : ℕ) : ℝ) ^ 99 ≤ (2 : ℝ) ^ 99 * (N : ℝ) ^ 99 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show N + 1 ≤ 2 * N by omega)
    have hA' : A / (N : ℝ) ^ 99 ≤ A * (2 : ℝ) ^ 99 / ((N + 1 : ℕ) : ℝ) ^ 99 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hscale hA.le
    apply (div_le_iff₀ (by positivity)).1
    calc
      _ ≤ _ := sign_span_failure_fraction_le N B
      _ ≤ 3 * (A / (N : ℝ) ^ 99) + D / ((N + 1 : ℕ) : ℝ) ^ 99 :=
        add_le_add (mul_le_mul_of_nonneg_left hP (by positivity)) (hd (N + 1) (by omega))
      _ ≤ 3 * (A * (2 : ℝ) ^ 99 / ((N + 1 : ℕ) : ℝ) ^ 99) + D / ((N + 1 : ℕ) : ℝ) ^ 99 :=
        add_le_add (mul_le_mul_of_nonneg_left hA' (show (0 : ℝ) ≤ 3 by norm_num)) le_rfl
      _ = _ := by ring

end BooleanThreshold
