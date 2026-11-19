module

public import BooleanThreshold.CokernelMaplesReduction

public noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Function

namespace BooleanThreshold

/-- Comparing the determinant-zero probabilities of binary and uniform matrices
over a single residue ring. -/
@[expose] def binaryModularDetZeroComparison (n q : ℕ) [NeZero q] (ε : ℝ) : Prop :=
  |finiteEventProbability (fun X : Fin n → Fin n → Bool =>
    (((Matrix.of X).map zeroOneBit).map (Int.castRingHom (ZMod q))).det = 0) -
    finiteEventProbability (fun X : Fin n → Fin n → ZMod q => (Matrix.of X).det = 0)| ≤ ε

private theorem binaryDet_zero_mod_iff {n q : ℕ} (X : Fin n → Fin n → Bool) :
    (((Matrix.of X).map zeroOneBit).map (Int.castRingHom (ZMod q))).det = 0 ↔
      q ∣ ((Matrix.of X).map zeroOneBit).det.natAbs := by
  simp only [Int.coe_castRingHom]
  rw [← Int.cast_det, ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.dvd_natAbs,
    Int.natCast_dvd_natCast]

private theorem finiteEventProbability_binary_det_dvd_le {n q : ℕ} [NeZero q] {ε : ℝ}
    (h : binaryModularDetZeroComparison n q ε) :
    finiteEventProbability (fun X : Fin n → Fin n → Bool =>
      q ∣ ((Matrix.of X).map zeroOneBit).det.natAbs) ≤
      finiteEventProbability (fun X : Fin n → Fin n → ZMod q => (Matrix.of X).det = 0) + ε := by
  have heq : (fun X : Fin n → Fin n → Bool =>
      q ∣ ((Matrix.of X).map zeroOneBit).det.natAbs) = (fun X =>
        (((Matrix.of X).map zeroOneBit).map (Int.castRingHom (ZMod q))).det = 0) :=
    funext fun X => propext (binaryDet_zero_mod_iff X).symm
  rw [heq]
  unfold binaryModularDetZeroComparison at h
  exact sub_le_iff_le_add'.mp ((le_abs_self _).trans h)

private theorem prod_primePower_dvd_iff {N K : ℕ} (s : Finset (Nat.primesLE (N ^ K)))
    (a : s → ℕ) (z : ℤ) :
    (∏ i, primePowerModuli s a i) ∣ z.natAbs ↔ ∀ i, primePowerModuli s a i ∣ z.natAbs := by
  let q := primePowerModuli s a
  let e := ZMod.prodEquivPi q (primePowerModuli_pairwise_coprime s a)
  have he (i : s) : e (z : ZMod (∏ i, q i)) i = (z : ZMod (q i)) := by
    simp only [e, ZMod.prodEquivPi_apply, map_intCast]
  simp_rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (z : ZMod (∏ i, q i)) = 0 ↔ ∀ i, (z : ZMod (q i)) = 0
  constructor
  · intro hz i
    rw [← he, hz, map_zero, Pi.zero_apply]
  · intro hz
    apply e.injective
    rw [map_zero]
    funext i
    exact (he i).trans (hz i)

private theorem squareDetJointProbability_eq_product_dvd {N K : ℕ}
    (s : Finset (Nat.primesLE (N ^ K))) (a : s → ℕ) :
    squareDetJointProbability N K s a = finiteEventProbability (fun X : Fin (N + 1) →
      Fin (N + 1) → Bool => (∏ i, primePowerModuli s a i) ∣ ((Matrix.of X).map zeroOneBit).det.natAbs) := by
  unfold squareDetJointProbability
  let P : Set (Fin (N + 1) → Fin (N + 1) → Bool) :=
    {X | (∏ i, primePowerModuli s a i) ∣ ((Matrix.of X).map zeroOneBit).det.natAbs}
  have hP : finiteEventProbability (fun X => X ∈ P) = (uniformOn Set.univ).real P :=
    finiteAverage_indicator P
  change _ = finiteEventProbability (fun X => X ∈ P)
  rw [hP]
  congr 1
  ext X
  exact (prod_primePower_dvd_iff s a _).symm

private theorem uniformDetZero_prod_primePower_le {N K : ℕ}
    (s : Finset (Nat.primesLE (N ^ K))) (a : s → ℕ) :
    finiteEventProbability (fun X : Fin (N + 1) → Fin (N + 1) → ZMod (∏ i, primePowerModuli s a i) =>
      (Matrix.of X).det = 0) ≤ (2 : ℝ) ^ s.card * ∏ i : s, 1 / (i.val.val : ℝ) ^ a i := by
  let q := primePowerModuli s a
  let e := ZMod.prodEquivPi q (primePowerModuli_pairwise_coprime s a)
  have heq : (fun X : Fin (N + 1) → Fin (N + 1) → ZMod (∏ i, q i) => (Matrix.of X).det = 0) =
      (fun X => ∀ i, e (Matrix.of X).det i = 0) := by
    funext X
    apply propext
    constructor
    · intro hx i
      rw [hx, map_zero, Pi.zero_apply]
    · intro hx
      apply e.injective
      rw [map_zero]
      exact funext hx
  change finiteEventProbability (fun X : Fin (N + 1) → Fin (N + 1) → ZMod (∏ i, q i) =>
    (Matrix.of X).det = 0) ≤ _
  rw [heq, uniformCRT_det_zero_probability q (primePowerModuli_pairwise_coprime s a)]
  calc
    _ ≤ ∏ i : s, 2 * (1 / (i.val.val : ℝ) ^ a i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        unfold finiteEventProbability finiteAverage
        exact div_nonneg (Finset.sum_nonneg fun _ _ => by split <;> norm_num) (Nat.cast_nonneg _)
      · intro i _
        rw [mul_one_div]
        exact finiteEventProbability_uniform_det_zero_le (N + 1) i.val.val (a i)
          (Nat.prime_of_mem_primesLE i.val.2) (by omega)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

private theorem squareDetJointProbability_le_primePower {N K : ℕ}
    (s : Finset (Nat.primesLE (N ^ K))) (a : s → ℕ) (i : s) {t : ℕ} (ht : t ≤ a i)
    {ε : ℝ} (h : letI : NeZero (i.val.val ^ t) :=
      ⟨pow_ne_zero _ (Nat.prime_of_mem_primesLE i.val.2).ne_zero⟩
      binaryModularDetZeroComparison (N + 1) (i.val.val ^ t) ε) :
    squareDetJointProbability N K s a ≤ 2 / (i.val.val : ℝ) ^ t + ε := by
  let p := i.val.val
  have hp : p.Prime := Nat.prime_of_mem_primesLE i.val.2
  let : NeZero (p ^ t) := ⟨pow_ne_zero _ hp.ne_zero⟩
  calc
    _ ≤ finiteEventProbability (fun X : Fin (N + 1) → Fin (N + 1) → Bool =>
        p ^ t ∣ ((Matrix.of X).map zeroOneBit).det.natAbs) := by
      let P : Set (Fin (N + 1) → Fin (N + 1) → Bool) :=
        {X | p ^ t ∣ ((Matrix.of X).map zeroOneBit).det.natAbs}
      have hP : finiteEventProbability (fun X => X ∈ P) = (uniformOn Set.univ).real P :=
        finiteAverage_indicator P
      change squareDetJointProbability N K s a ≤ finiteEventProbability (fun X => X ∈ P)
      rw [hP, squareDetJointProbability]
      exact measureReal_mono (fun X hX => (pow_dvd_pow p ht).trans (hX i)) (measure_ne_top _ _)
    _ ≤ _ := (finiteEventProbability_binary_det_dvd_le h).trans
      (add_le_add (finiteEventProbability_uniform_det_zero_le (N + 1) p t hp (by omega)) le_rfl)

private theorem squareDetJointProbability_le_of_polynomial_comparisons {N K D : ℕ}
    (hN : 1 ≤ N) (s : Finset (Nat.primesLE (N ^ K))) (a : s → ℕ) (hs : s.card ≤ 102)
    (hc : ∀ (q : ℕ) [NeZero q], q ≤ N ^ ((D + K) * 102) → q.primeFactors.card ≤ 102 →
      binaryModularDetZeroComparison (N + 1) q (1 / (N : ℝ) ^ D)) :
    squareDetJointProbability N K s a ≤
      (2 : ℝ) ^ 102 * (∏ i : s, 1 / (i.val.val : ℝ) ^ a i) + 3 / (N : ℝ) ^ D := by
  let cap := N ^ (D + K)
  have hN₀ : 0 < N := by omega
  have hcap₀ : 0 < cap := Nat.pow_pos hN₀
  have hcap₁ : 1 ≤ cap := by omega
  by_cases hall : ∀ i : s, primePowerModuli s a i ≤ cap
  · let q := ∏ i, primePowerModuli s a i
    have hq : q ≤ N ^ ((D + K) * 102) := by
      calc
        _ ≤ ∏ _i : s, cap := Finset.prod_le_prod (fun i _ => hall i)
        _ = cap ^ s.card := by simp
        _ ≤ cap ^ 102 := Nat.pow_le_pow_right hcap₀ hs
        _ = _ := by rw [pow_mul]
    have hqcard : q.primeFactors.card ≤ 102 := by
      refine (primeFactors_product_prime_powers_card_le (fun i : s => i.val.val) a
        (fun i => Nat.prime_of_mem_primesLE i.val.2)).trans ?_
      simpa only [Fintype.card_coe] using hs
    rw [squareDetJointProbability_eq_product_dvd]
    refine (finiteEventProbability_binary_det_dvd_le (hc q hq hqcard)).trans ?_
    refine add_le_add ((uniformDetZero_prod_primePower_le s a).trans ?_) ?_
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (by positivity)
    · exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    let p := i.val.val
    have hp : p.Prime := Nat.prime_of_mem_primesLE i.val.2
    have hple : p ≤ N ^ K := Nat.le_of_mem_primesLE i.val.2
    let t := Nat.log p cap
    let q := p ^ t
    let : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hql : q ≤ cap := Nat.pow_log_le_self p hcap₀.ne'
    have hqcap : cap < q * p := by simpa only [q, t, pow_succ] using Nat.lt_pow_succ_log_self hp.one_lt cap
    have hta : t ≤ a i := by
      apply Nat.le_of_lt
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (hql.trans_lt hi)
    have hqd : N ^ D ≤ q := by
      apply Nat.le_of_lt
      refine Nat.lt_of_mul_lt_mul_right (a := N ^ K) ?_
      rw [← pow_add]
      exact hqcap.trans_le (Nat.mul_le_mul_left q hple)
    have hqsize : q ≤ N ^ ((D + K) * 102) := by
      rw [pow_mul]
      exact hql.trans (by simpa using Nat.pow_le_pow_right hcap₀ (by decide : 1 ≤ 102))
    have hqcard : q.primeFactors.card ≤ 102 := by
      by_cases ht : t = 0
      · simp [q, ht]
      · change (p ^ t).primeFactors.card ≤ 102
        rw [Nat.primeFactors_prime_pow ht hp]
        simp
    refine (squareDetJointProbability_le_primePower s a i hta (hc q hqsize hqcard)).trans ?_
    have hpow : (N : ℝ) ^ D ≤ (p : ℝ) ^ t := by exact_mod_cast hqd
    have hpow₀ : 0 < (N : ℝ) ^ D := by positivity
    calc
      _ ≤ 2 / (N : ℝ) ^ D + 1 / (N : ℝ) ^ D :=
        add_le_add (div_le_div_of_nonneg_left (by norm_num) hpow₀ hpow) le_rfl
      _ = 3 / (N : ℝ) ^ D := by rw [← add_div]; norm_num
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- For the logarithmic moment it suffices to compare determinant-zero probabilities
at polynomial moduli with at most 102 prime factors. -/
theorem smallPrimeLogMoment_of_polynomial_det_zero_comparisons {K : ℕ} (hK : 1 ≤ K)
    (hcompare : ∀ᶠ N : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
      q ≤ N ^ (((3 + K) * 102 + K) * 102) → q.primeFactors.card ≤ 102 →
      binaryModularDetZeroComparison (N + 1) q (1 / (N : ℝ) ^ ((3 + K) * 102))) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, smallPrimeLogMoment N K ≤ C * Real.log (N : ℝ) ^ 102 := by
  apply smallPrimeLogMoment_of_joint_divisibility_polynomial hK (A := (2 : ℝ) ^ 102) (E := 3)
    (by positivity) (by positivity)
  filter_upwards [hcompare, eventually_ge_atTop 1] with N hN hN₀ s hs j
  exact (smallPrimeJointProbability_le_square N K s _).trans
    (squareDetJointProbability_le_of_polynomial_comparisons hN₀ s _ hs hN)

end BooleanThreshold
