module

public import BooleanThreshold.SignMeasure
public import BooleanThreshold.SpanNormalization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- The cardinality of the integral cokernel, with zero denoting an infinite cokernel. -/
noncomputable def binaryCokernelIndex {N : ℕ} (B : Fin N → Fin (N + 1) → Bool) : ℕ :=
  (LinearMap.range ((Matrix.of B).map zeroOneBit).mulVecLin).toAddSubgroup.index

/-- The contribution from primes at most `x` to the logarithm of an index. -/
noncomputable def smallPrimeLog (x m : ℕ) : ℝ :=
  ∑ p ∈ m.primeFactors.filter (fun p => p ≤ x), (m.factorization p : ℝ) * Real.log p

/-- This includes infinite cokernels, since every prime divides their index of zero. -/
def hasLargePrimeDivisor (x m : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ x < p ∧ p ∣ m

theorem smallPrimeLog_nonneg (x m : ℕ) : 0 ≤ smallPrimeLog x m :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))

theorem smallPrimeLog_eq_log {x m : ℕ} (h : ¬ hasLargePrimeDivisor x m) :
    m ≠ 0 ∧ smallPrimeLog x m = Real.log (m : ℝ) := by
  have hm : m ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp, hp'⟩ := Nat.exists_infinite_primes (x + 1)
    exact h ⟨p, hp', by omega, dvd_zero _⟩
  have hall : m.primeFactors.filter (fun p => p ≤ x) = m.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact le_of_not_gt (fun hlt => h ⟨p, hprime, hlt, hdvd⟩)
  refine ⟨hm, ?_⟩
  rw [smallPrimeLog, hall]
  have hprod : ∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p = (m : ℝ) := by
    exact_mod_cast (Nat.prod_factorization_pow_eq_self hm :
      ∏ p ∈ m.primeFactors, p ^ m.factorization p = m)
  rw [← hprod, Real.log_prod (fun p hp => pow_ne_zero _
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
  exact Finset.sum_congr rfl (fun p _ => (Real.log_pow _ _).symm)

private theorem uniform_markov {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (z : Ω → ℝ) (hz : ∀ ω, 0 ≤ z ω) {t : ℝ} (ht : 0 < t) :
    (uniformOn Set.univ).real {ω | t < z ω} ≤ (∑ ω, z ω) / Fintype.card Ω / t := by
  classical
  let s := Finset.univ.filter fun ω => t < z ω
  have hs : {ω | t < z ω} = (s : Set Ω) := by ext ω; simp [s]
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos (α := Ω)
  rw [uniformOn_univ_real_eq_card, hs, Set.ncard_coe_finset]
  apply (le_div_iff₀ ht).2
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hcard).2
  calc
    (s.card : ℝ) * t = ∑ _ω ∈ s, t := by simp
    _ ≤ ∑ ω ∈ s, z ω := Finset.sum_le_sum fun ω hω => (Finset.mem_filter.mp hω).2.le
    _ ≤ ∑ ω, z ω := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun ω _ _ => hz ω)

/-- The 102nd moment in Lemma 8, under the uniform law on binary matrices. -/
noncomputable def smallPrimeLogMoment (N K : ℕ) : ℝ :=
  (∑ B : Fin N → Fin (N + 1) → Bool,
    smallPrimeLog (N ^ K) (binaryCokernelIndex B) ^ 102) /
    Fintype.card (Fin N → Fin (N + 1) → Bool)

/-- Large prime divisibility and a tail of the small-prime log moment cover the
two ways the cokernel conclusion can fail. -/
theorem cokernel_failure_le {N K : ℕ} (hn : 0 < N) {b : ℝ} (hb : 0 < b) :
    (uniformOn Set.univ).real
      {B : Fin N → Fin (N + 1) → Bool | binaryCokernelIndex B = 0 ∨
        Real.exp (b * (N : ℝ)) < (binaryCokernelIndex B : ℝ)} ≤
      (uniformOn Set.univ).real
        {B : Fin N → Fin (N + 1) → Bool | hasLargePrimeDivisor (N ^ K) (binaryCokernelIndex B)} +
        smallPrimeLogMoment N K / (b * (N : ℝ)) ^ 102 := by
  let Ω := Fin N → Fin (N + 1) → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let z := fun B : Ω => smallPrimeLog (N ^ K) (binaryCokernelIndex B) ^ 102
  let t := (b * (N : ℝ)) ^ 102
  let D : Set Ω := {B | binaryCokernelIndex B = 0 ∨
      Real.exp (b * (N : ℝ)) < (binaryCokernelIndex B : ℝ)}
  let P : Set Ω := {B | hasLargePrimeDivisor (N ^ K) (binaryCokernelIndex B)}
  have ht : 0 < t := pow_pos (mul_pos hb (by exact_mod_cast hn)) _
  have hcover : D ⊆ P ∪ {B | t < z B} := by
    intro B hB
    by_cases hP : B ∈ P
    · exact Or.inl hP
    · right
      obtain ⟨hidx, hlog⟩ := smallPrimeLog_eq_log hP
      have hlarge : Real.exp (b * (N : ℝ)) < (binaryCokernelIndex B : ℝ) := hB.resolve_left hidx
      have hloglarge := Real.log_lt_log (Real.exp_pos _) hlarge
      rw [Real.log_exp, ← hlog] at hloglarge
      exact pow_lt_pow_left₀ hloglarge (by positivity) (by decide)
  calc
    μ.real D ≤ μ.real (P ∪ {B | t < z B}) := measureReal_mono hcover
    _ ≤ μ.real P + μ.real {B | t < z B} := measureReal_union_le _ _
    _ ≤ μ.real P + smallPrimeLogMoment N K / (b * (N : ℝ)) ^ 102 :=
      add_le_add le_rfl (uniform_markov z (fun _ => by positivity) ht)

private theorem log_pow_le_constant_mul_nat (N : ℕ) :
    Real.log (N : ℝ) ^ 102 ≤ (102 : ℝ) ^ 102 * (N : ℝ) := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hlog := Real.log_le_rpow_div hn (show (0 : ℝ) < 1 / 102 by norm_num)
  calc
    Real.log (N : ℝ) ^ 102 ≤ ((N : ℝ) ^ (1 / 102 : ℝ) / (1 / 102)) ^ 102 :=
      pow_le_pow_left₀ (Real.log_natCast_nonneg N) hlog _
    _ = (102 : ℝ) ^ 102 * (N : ℝ) := by
      rw [div_pow, ← Real.rpow_mul_natCast hn]
      norm_num [Real.rpow_one, div_eq_mul_inv, inv_pow]
      ring

/-- The conclusion of Proposition 2 follows from the logarithmic moment
in Lemma 8 and the large-prime bounds in Lemmas 9 and 10. -/
theorem cokernel_bound_of_log_moment_and_large_primes {K : ℕ} {b : ℝ} (hb : 0 < b)
    (hMoment : ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      smallPrimeLogMoment N K ≤ C * Real.log (N : ℝ) ^ 102)
    (hPrimes : ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {B : Fin N → Fin (N + 1) → Bool | hasLargePrimeDivisor (N ^ K) (binaryCokernelIndex B)} ≤
          C / (N : ℝ) ^ 99) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {B : Fin N → Fin (N + 1) → Bool | binaryCokernelIndex B = 0 ∨
          Real.exp (b * (N : ℝ)) < (binaryCokernelIndex B : ℝ)} ≤ C / (N : ℝ) ^ 99 := by
  obtain ⟨A, hApos, hA⟩ := hMoment
  obtain ⟨D, hDpos, hD⟩ := hPrimes
  let C := A * (102 : ℝ) ^ 102 / b ^ 102
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨D + C, by positivity, ((hA.and hD).and (eventually_ge_atTop 1)).mono ?_⟩
  intro N h
  have hnpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one h.2
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h.2
  have hn' : 0 < (N : ℝ) := zero_lt_one.trans_le hn
  have hscale : (N : ℝ) / (N : ℝ) ^ 102 ≤ 1 / (N : ℝ) ^ 99 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    rw [one_mul, ← pow_succ']
    exact pow_le_pow_right₀ hn (by decide)
  have hmoment : smallPrimeLogMoment N K / (b * (N : ℝ)) ^ 102 ≤ C / (N : ℝ) ^ 99 := by
    calc
      smallPrimeLogMoment N K / (b * (N : ℝ)) ^ 102 ≤
          A * ((102 : ℝ) ^ 102 * (N : ℝ)) / (b * (N : ℝ)) ^ 102 := by
        gcongr
        exact h.1.1.trans (mul_le_mul_of_nonneg_left (log_pow_le_constant_mul_nat N) hApos.le)
      _ = C * ((N : ℝ) / (N : ℝ) ^ 102) := by
        rw [mul_pow, div_mul_eq_div_div]
        unfold C
        ring
      _ ≤ C * (1 / (N : ℝ) ^ 99) := mul_le_mul_of_nonneg_left hscale hCpos.le
      _ = C / (N : ℝ) ^ 99 := by ring
  exact (cokernel_failure_le hnpos hb).trans
    ((add_le_add h.1.2 hmoment).trans_eq (by ring))

end BooleanThreshold
