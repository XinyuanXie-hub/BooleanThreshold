module

public import BooleanThreshold.Asymptotics
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.BigOperators.Ring.Finset

public section

open scoped BigOperators

namespace BooleanThreshold

/-- A sum over tuples with a weight for each distinct value, counted once. -/
theorem sum_distinct_tuple_weights_le {P : Type*} [Fintype P] [DecidableEq P]
    (w : P → ℝ) (hw : ∀ p, 0 ≤ w p) (k : ℕ) :
    (∑ f : Fin k → P, ∏ p ∈ Finset.univ.image f, w p) ≤
      ((k : ℝ) + ∑ p, w p) ^ k := by
  classical
  let W := ∑ p, w p
  have hW : 0 ≤ W := Finset.sum_nonneg fun p _ => hw p
  induction k with
  | zero =>
    simp
  | succ k ih =>
    let V (f : Fin k → P) := ∏ p ∈ Finset.univ.image f, w p
    have hcons (p : P) (f : Fin k → P) :
        Finset.univ.image (Fin.cons p f) = insert p (Finset.univ.image f) := by
      ext q
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
      rw [Fin.exists_fin_succ]
      simp [eq_comm]
    have hstep (f : Fin k → P) :
        (∑ p : P, ∏ q ∈ Finset.univ.image (Fin.cons p f), w q) ≤
          ((k : ℝ) + W) * V f := by
      let s := Finset.univ.image f
      have hV : 0 ≤ V f := Finset.prod_nonneg fun p _ => hw p
      have hcard : (s.card : ℝ) ≤ (k : ℝ) := by
        have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := f)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        exact_mod_cast h
      have hf (p : P) : (∏ q ∈ Finset.univ.image (Fin.cons p f), w q) =
          if p ∈ s then V f else w p * V f := by
        rw [hcons]
        by_cases hp : p ∈ s
        · rw [ite_eq_left hp, Finset.insert_eq_of_mem hp]
        · rw [ite_eq_right hp, Finset.prod_insert hp]
      simp_rw [hf]
      rw [Finset.sum_ite]
      have hsum : ∑ p ∈ Finset.univ.filter (fun p => p ∉ s), w p ≤ W :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => hw p)
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right (add_le_add hcard hsum) hV
    have he : (∑ f : Fin (k + 1) → P, ∏ p ∈ Finset.univ.image f, w p) =
        ∑ f : Fin k → P, ∑ p : P, ∏ q ∈ Finset.univ.image (Fin.cons p f), w q := by
      let e := (Equiv.prodComm (Fin k → P) P).trans (Fin.consEquiv (fun _ : Fin (k + 1) => P))
      calc
        _ = ∑ x : (Fin k → P) × P, ∏ q ∈ Finset.univ.image (Fin.cons x.2 x.1), w q :=
          Fintype.sum_equiv e.symm _ _ fun f => by simp [e]
        _ = _ := Fintype.sum_prod_type _
    rw [he]
    calc
      _ ≤ ∑ f : Fin k → P, ((k : ℝ) + W) * V f := Finset.sum_le_sum fun f _ => hstep f
      _ = ((k : ℝ) + W) * ∑ f : Fin k → P, V f := by rw [Finset.mul_sum]
      _ ≤ ((k : ℝ) + W) * ((k : ℝ) + W) ^ k :=
        mul_le_mul_of_nonneg_left ih (add_nonneg (Nat.cast_nonneg _) hW)
      _ = ((k : ℝ) + W) ^ (k + 1) := by rw [pow_succ']
      _ ≤ ((↑(k + 1) : ℝ) + W) ^ (k + 1) := by
        gcongr
        exact Nat.le_succ _

/-- A prime contributes at least the number of its multiples to the valuation of a factorial. -/
private theorem div_le_factorization_factorial {n p : ℕ} (hp : p.Prime) :
    n / p ≤ n.factorial.factorization p := by
  let b := max (Nat.log p n + 1) 2
  have hb : Nat.log p n < b := (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hmem : 1 ∈ Finset.Ico 1 b := by
    apply Finset.mem_Ico.mpr
    exact ⟨by rfl, (by decide : 1 < 2).trans_le (le_max_right _ _)⟩
  rw [Nat.factorization_factorial hp hb]
  simpa using Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem

/-- The reciprocal prime weights in the logarithmic moment are bounded by a
constant times the logarithm of the cutoff. -/
theorem sum_log_div_primes_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) / (p : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsum : ∑ p ∈ Nat.primesLE n, (n / p : ℕ) * Real.log (p : ℝ) ≤ Real.log (n.factorial : ℝ) := by
    have heq : (∏ p ∈ n.factorial.primeFactors, (p : ℝ) ^ n.factorial.factorization p) =
        (n.factorial : ℝ) := by
      exact_mod_cast (Nat.prod_factorization_pow_eq_self n.factorial_ne_zero :
        ∏ p ∈ n.factorial.primeFactors, p ^ n.factorial.factorization p = n.factorial)
    rw [← heq, Real.log_prod (fun p hp => pow_ne_zero _
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
    simp only [Real.log_pow]
    have hs : Nat.primesLE n ⊆ n.factorial.primeFactors := by
      intro p hp
      obtain ⟨hpn, hprime⟩ := Nat.mem_primesLE.mp hp
      exact hprime.mem_primeFactors (Nat.dvd_factorial hprime.pos hpn) n.factorial_ne_zero
    exact (Finset.sum_le_sum (fun p hp =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast
        div_le_factorization_factorial (Nat.prime_of_mem_primesLE hp)) (Real.log_natCast_nonneg p))).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)))
  have hlogfac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
      (by exact_mod_cast Nat.factorial_le_pow n)
  have hpoint (p : ℕ) (hp : p ∈ Nat.primesLE n) :
      (n : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) ≤ 2 * ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    obtain ⟨hpn, hprime⟩ := Nat.mem_primesLE.mp hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hdiv : 1 ≤ n / p := (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa)
    have hnle : (n : ℝ) / (p : ℝ) ≤ 2 * ((n / p : ℕ) : ℝ) := by
      apply (div_le_iff₀ hp0).mpr
      exact_mod_cast (show n ≤ 2 * (n / p) * p from by
        have hmod := Nat.mod_lt n hprime.pos
        have he := Nat.mod_add_div n p
        have hmul := Nat.mul_le_mul_left p hdiv
        nlinarith)
    rw [mul_div_left_comm, mul_comm (Real.log (p : ℝ))]
    exact mul_le_mul_of_nonneg_right hnle (Real.log_natCast_nonneg p)
  apply (mul_le_mul_iff_of_pos_left hnpos).mp
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE n, 2 * ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = 2 * ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ 2 * ((n : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsum.trans hlogfac) (by norm_num)
    _ = _ := by ring

end BooleanThreshold
