module

public import BooleanThreshold.CokernelCRT
public import BooleanThreshold.CokernelSquareMoment
public import BooleanThreshold.CokernelUniformDeterminant

public noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Function

namespace BooleanThreshold

theorem finiteEventProbability_eq_fraction {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    finiteEventProbability P = finiteUniformFraction P := by
  unfold finiteEventProbability finiteAverage finiteUniformFraction
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

@[expose] def primePowerModuli {N K : ℕ} (s : Finset (Nat.primesLE (N ^ K))) (j : s → ℕ) (i : s) : ℕ :=
  i.val.val ^ j i

instance primePowerModuli_neZero {N K : ℕ} (s : Finset (Nat.primesLE (N ^ K)))
    (j : s → ℕ) (i : s) : NeZero (primePowerModuli s j i) :=
  ⟨pow_ne_zero _ (Nat.prime_of_mem_primesLE i.val.2).ne_zero⟩

instance primePowerModuli_prod_neZero {N K : ℕ} (s : Finset (Nat.primesLE (N ^ K)))
    (j : s → ℕ) : NeZero (∏ i, primePowerModuli s j i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (primePowerModuli s j i))⟩

theorem primePowerModuli_pairwise_coprime {N K : ℕ} (s : Finset (Nat.primesLE (N ^ K)))
    (j : s → ℕ) : Pairwise (Nat.Coprime on primePowerModuli s j) := by
  intro i i' h
  exact Nat.coprime_pow_primes (j i) (j i') (Nat.prime_of_mem_primesLE i.val.2)
    (Nat.prime_of_mem_primesLE i'.val.2) (fun heq => h (Subtype.ext (Subtype.ext heq)))

theorem primeFactors_product_prime_powers_card_le {I : Type*} [Fintype I]
    (p a : I → ℕ) (hp : ∀ i, (p i).Prime) :
    (∏ i, p i ^ a i).primeFactors.card ≤ Fintype.card I := by
  have hsub : (∏ i, p i ^ a i).primeFactors ⊆ Finset.univ.image p := by
    intro q hq
    have hprime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨i, hi, hd⟩ := (hprime.prime.dvd_finsetProd_iff (fun i => p i ^ a i)).mp
      (Nat.dvd_of_mem_primeFactors hq)
    exact Finset.mem_image.mpr
      ⟨i, hi, ((Nat.prime_dvd_prime_iff_eq hprime (hp i)).mp (hprime.dvd_of_dvd_pow hd)).symm⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans Finset.card_univ.le)

theorem finiteEventProbability_uniform_det_zero_le (n p a : ℕ) (hp : p.Prime) (hn : 0 < n) :
    letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
    finiteEventProbability (fun X : Fin n → Fin n → ZMod (p ^ a) => (Matrix.of X).det = 0) ≤
      2 / (p : ℝ) ^ a := by
  let : Fact p.Prime := ⟨hp⟩
  rw [finiteEventProbability_equiv Matrix.of (fun X => X.det = 0), finiteEventProbability_eq_fraction]
  exact uniformDeterminantTail_le n p a hn

/-- A comparison of the binary and uniform laws for intersections of
complements of the selected prime-power divisibility events. -/
@[expose] def squareDetComplementComparison (N K : ℕ) (s : Finset (Nat.primesLE (N ^ K))) (j : s → ℕ)
    (ε : ℝ) : Prop :=
  let q := primePowerModuli s j
  let crt := ZMod.prodEquivPi q (primePowerModuli_pairwise_coprime s j)
  ∀ t : Finset s,
    |finiteEventProbability (fun X : Fin (N + 1) → Fin (N + 1) → Bool =>
      ∀ i ∈ t, ¬ q i ∣ ((Matrix.of X).map zeroOneBit).det.natAbs) -
     finiteEventProbability (fun X : Fin (N + 1) → Fin (N + 1) → ZMod (∏ i, q i) =>
      ∀ i ∈ t, crt (Matrix.of X).det i ≠ 0)| ≤ ε

theorem squareDetJointProbability_le_of_comparison {N K : ℕ}
    (s : Finset (Nat.primesLE (N ^ K))) (j : s → ℕ) {ε : ℝ}
    (h : squareDetComplementComparison N K s j ε) :
    squareDetJointProbability N K s j ≤
      (2 : ℝ) ^ s.card * (∏ i : s, 1 / (i.val.val : ℝ) ^ j i) + (2 : ℝ) ^ s.card * ε := by
  let q := primePowerModuli s j
  have hb := binary_det_joint_le_uniform_reference q (primePowerModuli_pairwise_coprime s j) (N + 1) h
  let P (X : Fin (N + 1) → Fin (N + 1) → Bool) :=
    ∀ i, q i ∣ ((Matrix.of X).map zeroOneBit).det.natAbs
  have heq : finiteEventProbability P = squareDetJointProbability N K s j :=
    finiteAverage_indicator {X | P X}
  have hRef (i : s) :
      finiteEventProbability (fun X : Fin (N + 1) → Fin (N + 1) → ZMod (q i) => (Matrix.of X).det = 0) ≤
        2 * (1 / (i.val.val : ℝ) ^ j i) := by
    rw [mul_one_div]
    exact finiteEventProbability_uniform_det_zero_le (N + 1) i.val.val (j i)
      (Nat.prime_of_mem_primesLE i.val.2) (by omega)
  change finiteEventProbability P ≤ _ at hb
  rw [heq, Fintype.card_coe] at hb
  refine hb.trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ ∏ i : s, 2 * (1 / (i.val.val : ℝ) ^ j i) :=
      Finset.prod_le_prod₀ (fun i _ => by
        unfold finiteEventProbability finiteAverage
        exact div_nonneg (Finset.sum_nonneg fun _ _ => by split <;> norm_num)
          (Nat.cast_nonneg _)) (fun i _ => hRef i)
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- The small-prime logarithmic moment follows from exponentially accurate
comparisons for intersections of complements of determinant divisibility events. -/
theorem smallPrimeLogMoment_of_determinant_comparisons {K : ℕ} (hK : 1 ≤ K)
    {E c : ℝ} (hE : 0 ≤ E) (hc : 0 < c)
    (hcompare : ∀ᶠ N : ℕ in atTop, ∀ s : Finset (Nat.primesLE (N ^ K)), s.card ≤ 102 →
      ∀ j : s → Fin (N ^ 3), (∀ i : s, (j i : ℕ) + 1 ≤ Nat.log 2 N.factorial) →
        squareDetComplementComparison N K s (fun i => (j i : ℕ) + 1) (E * Real.exp (-c * (N : ℝ)))) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, smallPrimeLogMoment N K ≤ C * Real.log (N : ℝ) ^ 102 := by
  apply smallPrimeLogMoment_of_joint_divisibility hK
    (A := (2 : ℝ) ^ 102) (E := (2 : ℝ) ^ 102 * E) (by positivity) (by positivity) hc
  filter_upwards [hcompare] with N h s hs j
  by_cases hj : ∀ i : s, (j i : ℕ) + 1 ≤ Nat.log 2 N.factorial
  · apply (smallPrimeJointProbability_le_square N K s _).trans
    refine (squareDetJointProbability_le_of_comparison s (fun i => (j i : ℕ) + 1) (h s hs j hj)).trans ?_
    rw [mul_assoc]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (Finset.prod_nonneg fun _ _ => by positivity))
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (by positivity))
  · have hempty : {B : Fin N → Fin (N + 1) → Bool |
        ∀ i : s, (j i : ℕ) + 1 ≤ (binaryCokernelIndex B).factorization i.val.val} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro B hB
      exact hj (fun i => (hB i).trans
        (binaryCokernelIndex_factorization_le_log_factorial (Nat.prime_of_mem_primesLE i.val.2) B))
    rw [smallPrimeJointProbability, hempty, measureReal_empty]
    positivity

end BooleanThreshold
