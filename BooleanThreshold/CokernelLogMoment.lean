module

public import BooleanThreshold.CokernelValuationCap
public import BooleanThreshold.CokernelWeightedMoment

public noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace BooleanThreshold

/-- The probability of simultaneous prime-power divisibility of the finite
binary cokernel, with valuation zero when the cokernel is infinite. -/
@[expose] def smallPrimeJointProbability (N K : ℕ) (s : Finset (Nat.primesLE (N ^ K))) (j : s → ℕ) : ℝ :=
  (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
    ∀ i : s, j i ≤ (binaryCokernelIndex B).factorization i.val.val}

private theorem smallPrimeLog_eq_sum_primes (x m : ℕ) :
    smallPrimeLog x m =
      ∑ p : Nat.primesLE x, (m.factorization p : ℝ) * Real.log (p : ℝ) := by
  unfold smallPrimeLog
  refine (Finset.sum_subset ?_ ?_).trans
    (Finset.sum_attach (Nat.primesLE x) (fun p : ℕ => (m.factorization p : ℝ) * Real.log (p : ℝ))).symm
  · intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Finset.mem_filter.mp hp).2, Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩
  · intro p hp hn
    have hfac : m.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rw [Nat.support_factorization]
      exact fun h => hn (Finset.mem_filter.mpr ⟨h, Nat.le_of_mem_primesLE hp⟩)
    simp [hfac]

set_option maxHeartbeats 600000 in
/-- A polynomially small remainder in the joint divisibility estimate suffices
to bound the small-prime logarithmic moment. -/
theorem smallPrimeLogMoment_of_joint_divisibility_polynomial {K : ℕ} (hK : 1 ≤ K)
    {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (htail : ∀ᶠ N : ℕ in atTop, ∀ s : Finset (Nat.primesLE (N ^ K)), s.card ≤ 102 →
      ∀ j : s → Fin (N ^ 3),
        smallPrimeJointProbability N K s (fun i => (j i : ℕ) + 1) ≤
          A * (∏ i : s, 1 / (i.val.val : ℝ) ^ ((j i : ℕ) + 1)) + E / (N : ℝ) ^ ((3 + K) * 102)) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      smallPrimeLogMoment N K ≤ C * Real.log (N : ℝ) ^ 102 := by
  obtain ⟨M, hM, hmoment⟩ := finiteAverage_weighted_power_le_of_joint_tails 102
  let C₀ := A * (102 + M * 2) ^ 102 + E * (2 : ℝ) ^ 102
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨(C₀ + 1) * (K : ℝ) ^ 102, by positivity, (htail.and (eventually_ge_atTop 2)).mono ?_⟩
  intro N h
  let x := N ^ K
  have hNx : N ≤ x := by
    dsimp [x]
    conv_lhs => rw [← pow_one N]
    exact Nat.pow_le_pow_right (by omega : 0 < N) hK
  have hx : 2 ≤ x := h.2.trans hNx
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  let P := (Nat.primesLE x : Type)
  let Ω := Fin N → Fin (N + 1) → Bool
  let p (i : P) := i.val
  let w (i : P) := Real.log (p i : ℝ) / Real.log (x : ℝ)
  let ν (B : Ω) (i : P) := (binaryCokernelIndex B).factorization (p i)
  have hp (i : P) : 2 ≤ p i := Nat.two_le_of_mem_primesLE i.2
  have hw₀ (i : P) : 0 ≤ w i := div_nonneg (Real.log_natCast_nonneg _) hlogx.le
  have hw₁ (i : P) : w i ≤ 1 := by
    apply (div_le_one hlogx).mpr
    exact Real.log_le_log (by exact_mod_cast (show 0 < p i by have := hp i; omega))
      (by exact_mod_cast Nat.le_of_mem_primesLE i.2)
  have hsum : (∑ i : P, w i / (p i : ℝ)) ≤ 2 := by
    change (∑ i : Nat.primesLE x, (Real.log (i : ℝ) / Real.log (x : ℝ)) / (i : ℝ)) ≤ 2
    have heq (i : Nat.primesLE x) :
        (Real.log (i : ℝ) / Real.log (x : ℝ)) / (i : ℝ) =
          (Real.log (i : ℝ) / (i : ℝ)) / Real.log (x : ℝ) := by ring
    simp_rw [heq, div_eq_mul_inv, ← Finset.sum_mul]
    apply (div_le_iff₀ hlogx).mpr
    change ∑ i ∈ (Nat.primesLE x).attach, Real.log (i : ℝ) * (i : ℝ)⁻¹ ≤ _
    exact (Finset.sum_attach (Nat.primesLE x)
      (fun i : ℕ => Real.log (i : ℝ) * (i : ℝ)⁻¹)).trans_le (by
        simpa only [div_eq_mul_inv] using sum_log_div_primes_le x (by omega))
  have hν (B : Ω) (i : P) : ν B i ≤ N ^ 3 :=
    binaryCokernelIndex_factorization_le (Nat.prime_of_mem_primesLE i.2) B
  have hweights : finiteAverage (fun B : Ω => (∑ i : P, w i * (ν B i : ℝ)) ^ 102) ≤ C₀ := by
    have hbound := hmoment (N ^ 3) p hp w hw₀ hw₁ ν hν A
      (E / (N : ℝ) ^ ((3 + K) * 102)) hA (by positivity)
      (fun s hs j =>
        (finiteAverage_event (fun B : Ω => ∀ i : s, (j i : ℕ) < ν B i)).trans_le
          (h.1 s hs j))
    simp only [Nat.cast_ofNat] at hbound
    have hcard : (Fintype.card P : ℝ) ≤ 2 * (N : ℝ) ^ K := by
      change (Fintype.card (Nat.primesLE x) : ℝ) ≤ _
      rw [Fintype.card_coe, ← Nat.cast_pow]
      exact_mod_cast (show (Nat.primesLE x).card ≤ 2 * x from by
        rw [Nat.primesLE_eq_filter_range]
        have h := Finset.card_filter_le (Finset.range (x + 1)) Nat.Prime
        rw [Finset.card_range] at h
        omega)
    calc
      _ ≤ _ := hbound
      _ ≤ A * (102 + M * 2) ^ 102 +
          (E / (N : ℝ) ^ ((3 + K) * 102)) * (2 * (N : ℝ) ^ (3 + K)) ^ 102 := by
        apply add_le_add
        · have hs₀ : 0 ≤ ∑ i : P, w i / (p i : ℝ) :=
            Finset.sum_nonneg (fun i _ => div_nonneg (hw₀ i) (Nat.cast_nonneg _))
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity)
              (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hM.le)) _) hA
        · have hpow : ((N ^ 3 : ℕ) : ℝ) * (2 * (N : ℝ) ^ K) =
              2 * (N : ℝ) ^ (3 + K) := by push_cast; rw [pow_add]; ring
          rw [← hpow]
          gcongr
      _ = C₀ := by
        have hpow : 0 < (N : ℝ) ^ ((3 + K) * 102) :=
          pow_pos (by exact_mod_cast (show 0 < N by omega)) _
        dsimp only [C₀]
        rw [mul_pow, ← pow_mul]
        field_simp [hpow.ne']
  have hlog : Real.log (x : ℝ) = (K : ℝ) * Real.log (N : ℝ) := by
    dsimp [x]
    rw [Nat.cast_pow, Real.log_pow]
  have hsum_scale (B : Ω) :
      smallPrimeLog x (binaryCokernelIndex B) = Real.log (x : ℝ) * (∑ i : P, w i * (ν B i : ℝ)) := by
    rw [smallPrimeLog_eq_sum_primes, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w, ν, p]
    have heq : Real.log (x : ℝ) * (Real.log (i : ℝ) / Real.log (x : ℝ)) = Real.log (i : ℝ) :=
      by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hlogx.ne']
    rw [← mul_assoc, heq, mul_comm]
  have hscale : smallPrimeLogMoment N K =
      Real.log (x : ℝ) ^ 102 * finiteAverage (fun B : Ω => (∑ i : P, w i * (ν B i : ℝ)) ^ 102) := by
    rw [← finiteAverage_const_mul]
    change finiteAverage (fun B : Ω => smallPrimeLog x (binaryCokernelIndex B) ^ 102) = _
    exact congrArg finiteAverage (funext fun B => by rw [hsum_scale, mul_pow])
  rw [hscale, hlog, mul_pow]
  calc
    _ ≤ ((K : ℝ) ^ 102 * Real.log (N : ℝ) ^ 102) * C₀ :=
      mul_le_mul_of_nonneg_left hweights (by positivity)
    _ ≤ ((K : ℝ) ^ 102 * Real.log (N : ℝ) ^ 102) * (C₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only []) (by positivity)
    _ = _ := by ring

/-- The logarithmic moment estimate in Lemma 8 follows from its joint
divisibility estimate in equation (32). -/
theorem smallPrimeLogMoment_of_joint_divisibility {K : ℕ} (hK : 1 ≤ K)
    {A E c : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) (hc : 0 < c)
    (htail : ∀ᶠ N : ℕ in atTop, ∀ s : Finset (Nat.primesLE (N ^ K)), s.card ≤ 102 →
      ∀ j : s → Fin (N ^ 3),
        smallPrimeJointProbability N K s (fun i => (j i : ℕ) + 1) ≤
          A * (∏ i : s, 1 / (i.val.val : ℝ) ^ ((j i : ℕ) + 1)) + E * Real.exp (-c * (N : ℝ))) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      smallPrimeLogMoment N K ≤ C * Real.log (N : ℝ) ^ 102 := by
  obtain ⟨B, hB, hdecay⟩ := exp_neg_nat_mul_le_inv_pow ((3 + K) * 102) hc
  apply smallPrimeLogMoment_of_joint_divisibility_polynomial hK hA (E := E * B) (by positivity)
  filter_upwards [htail, eventually_ge_atTop 1] with N hN hN₀ s hs j
  refine (hN s hs j).trans (add_le_add le_rfl ?_)
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hdecay N hN₀) hE

end BooleanThreshold
