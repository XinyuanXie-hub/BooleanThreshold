module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.DependenceEvents
public import BooleanThreshold.NonPairSign

@[expose] public section

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

open scoped Classical in
/-- A null vector using at least three columns and with a large atom at zero. -/
def largeAtomDependence {n r : ℕ} (v : Fin r → Fin n → ℝ) : Prop :=
  ∃ a : Fin r → ℝ, 2 < (Finset.univ.filter fun i => a i ≠ 0).card ∧
    (2 / 3 : ℝ≥0∞) ^ r < zeroAtom a ∧ ∀ j, ∑ i, a i * v i j = 0

/-- At the rectangular endpoint, split the event by its witness's concentration.
The large-atom event only needs to be bounded on a square restriction. -/
theorem nonPair_endpoint_le {r : ℕ} (hr : 1 ≤ r) :
    (signLaw (r + 1) r).real {v | nonPairDependence v} ≤
      ((r + 1).choose 2 : ℝ) * (4 / 9 : ℝ) ^ r +
        (signLaw r r).real {v | largeAtomDependence v} := by
  classical
  let low : Set (Fin r → Fin (r + 1) → ℝ) :=
    {v | ∃ a : Fin r → ℝ, a ≠ 0 ∧ zeroAtom a ≤ (2 / 3 : ℝ≥0∞) ^ r ∧
      ∀ j, ∑ i, a i * v i j = 0}
  let high : Set (Fin r → Fin (r + 1) → ℝ) := {v | largeAtomDependence v}
  have hcover : {v | nonPairDependence v} ⊆ low ∪ high := by
    intro v hv
    obtain ⟨a, hcard, hsum⟩ := hv
    have hrow := sum_smul_eq_zero_iff.mp hsum
    by_cases ha : zeroAtom a ≤ (2 / 3 : ℝ≥0∞) ^ r
    · have hne : a ≠ 0 := by
        intro hz
        subst a
        simp at hcard
      exact Or.inl ⟨a, hne, ha, hrow⟩
    · exact Or.inr ⟨a, hcard, lt_of_not_ge ha, hrow⟩
  let e := Fin.castLEEmb (Nat.le_succ r)
  let s : Set (Fin r → Fin r → ℝ) := {v | largeAtomDependence v}
  have hres : (signLaw (r + 1) r).real ((fun v i j => v i (e j)) ⁻¹' s) = (signLaw r r).real s :=
    congrArg ENNReal.toReal (signLaw_restrict_columns e s)
  have hsubset : high ⊆ (fun v i j => v i (e j)) ⁻¹' s := by
    intro v hv
    obtain ⟨a, hc, ha, hrow⟩ := hv
    exact ⟨a, hc, ha, fun j => hrow (e j)⟩
  calc
    (signLaw (r + 1) r).real {v | nonPairDependence v} ≤
        (signLaw (r + 1) r).real (low ∪ high) := measureReal_mono hcover
    _ ≤ (signLaw (r + 1) r).real low + (signLaw (r + 1) r).real high :=
      measureReal_union_le _ _
    _ ≤ ((r + 1).choose 2 : ℝ) * (4 / 9 : ℝ) ^ r + (signLaw r r).real s :=
      add_le_add (signLaw_real_low_concentration_le hr) ((measureReal_mono hsubset).trans_eq hres)

private theorem low_atom_exponential_gain :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n.choose 2 : ℝ) * (4 / 9 : ℝ) ^ (n - 1) ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  obtain ⟨c, hc, A, hA, hpoly⟩ := polynomial_mul_pow_exponential_gain 2
    (show (0 : ℝ) < 4 / 9 by norm_num) (show (4 / 9 : ℝ) < 1 / 2 by norm_num)
  refine ⟨c, hc, (9 / 4) * A, by positivity, (eventually_ge_atTop 1).mono ?_⟩
  intro n hn
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow n 2
  have hpow : (4 / 9 : ℝ) ^ (n - 1) = (9 / 4) * (4 / 9 : ℝ) ^ n := by
    calc
      (4 / 9 : ℝ) ^ (n - 1) = (9 / 4) * ((4 / 9 : ℝ) ^ (n - 1) * (4 / 9)) := by ring
      _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow]
  calc
    (n.choose 2 : ℝ) * ((9 / 4) * (4 / 9 : ℝ) ^ n) ≤
        (n : ℝ) ^ 2 * ((9 / 4) * (4 / 9 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ = (9 / 4) * ((n : ℝ) ^ 2 * (4 / 9 : ℝ) ^ n) := by ring
    _ ≤ (9 / 4) * (A * Real.exp (-c * (n : ℝ)) / 2 ^ n) :=
      mul_le_mul_of_nonneg_left (hpoly n) (by positivity)
    _ = (9 / 4) * A * Real.exp (-c * (n : ℝ)) / 2 ^ n := by ring

private theorem large_atom_bound_shift
    (h : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ r : ℕ in atTop,
      (signLaw r r).real {v | largeAtomDependence v} ≤ C * Real.exp (-c * (r : ℝ)) / 2 ^ r) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (signLaw (n - 1) (n - 1)).real {v | largeAtomDependence v} ≤
        C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  obtain ⟨c, hc, A, hA, hbound⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  refine ⟨c, hc, 2 * A * Real.exp c, by positivity, (eventually_ge_atTop (N + 1)).mono ?_⟩
  intro n hn
  have hn₁ : 1 ≤ n := by omega
  have hpow : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn₁]
  have harg : -c * ((n - 1 : ℕ) : ℝ) = -c * (n : ℝ) + c := by
    rw [Nat.cast_sub hn₁]
    push_cast
    ring
  calc
    (signLaw (n - 1) (n - 1)).real {v | largeAtomDependence v} ≤
      A * Real.exp (-c * ((n - 1 : ℕ) : ℝ)) / 2 ^ (n - 1) :=
        hN (n - 1) (by omega)
    _ = 2 * A * Real.exp c * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
      rw [harg, Real.exp_add, ← hpow, div_mul_eq_div_div]
      ring

/-- Theorem 7 follows from Lemma 13's square-matrix estimate for large atoms. -/
theorem dependence_asymptotic_of_large_atom_bound
    (large_atom_bound : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ r : ℕ in atTop,
      (signLaw r r).real {v | largeAtomDependence v} ≤ C * Real.exp (-c * (r : ℝ)) / 2 ^ r) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n r : ℕ, 1 ≤ r → r < n →
      |(signLaw n r).real {v | ¬ LinearIndependent ℝ v} -
        2 * (r.choose 2 : ℝ) / 2 ^ n| ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  let low (n : ℕ) : ℝ := (n.choose 2 : ℝ) * (4 / 9 : ℝ) ^ (n - 1)
  let high (n : ℕ) : ℝ := (signLaw (n - 1) (n - 1)).real {v | largeAtomDependence v}
  let pairsError (n : ℕ) : ℝ := 2 * (n : ℝ) ^ 4 / 4 ^ n
  have hpairs : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      pairsError n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
    obtain ⟨c, hc, A, hA, h⟩ := polynomial_div_four_pow_bound 4
    refine ⟨c, hc, 2 * A, by positivity, Eventually.of_forall fun n => ?_⟩
    simpa only [pairsError, mul_div_assoc, ← mul_assoc] using mul_le_mul_of_nonneg_left (h n) (by norm_num : (0 : ℝ) ≤ 2)
  have hlow : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      low n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := low_atom_exponential_gain
  have hhigh : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      high n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := large_atom_bound_shift large_atom_bound
  obtain ⟨c, hc, A, _, hA⟩ := add_exponential_gains (add_exponential_gains hlow hhigh) hpairs
  let scale (n : ℕ) : ℝ := Real.exp (-c * (n : ℝ)) / 2 ^ n
  have hscale (n : ℕ) (_ : 1 ≤ n) : 0 < scale n :=
    div_pos (Real.exp_pos _) (by positivity)
  obtain ⟨C, hC, h⟩ := relative_bound_of_eventually hscale
    (f := fun n => low n + high n + pairsError n) ⟨A, by
      simpa only [scale, mul_div_assoc] using hA⟩
  refine ⟨c, hc, C, hC, fun n r hr hnr => ?_⟩
  have hmono := nonPair_probability_mono (n := n) (r := r) (s := n - 1) (by omega)
  have hendpoint : (signLaw n (n - 1)).real {v | nonPairDependence v} ≤ low n + high n := by
    cases n with
    | zero => omega
    | succ k =>
      have hk : 1 ≤ k := by omega
      simpa only [low, high, Nat.succ_sub_one, Nat.succ_eq_add_one] using nonPair_endpoint_le hk
  calc
    |(signLaw n r).real {v | ¬ LinearIndependent ℝ v} - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤
        |(signLaw n r).real {v | ¬ LinearIndependent ℝ v} -
          (signLaw n r).real {v | pairCollision v}| +
          |(signLaw n r).real {v | pairCollision v} - 2 * (r.choose 2 : ℝ) / 2 ^ n| :=
      abs_sub_le _ _ _
    _ ≤ (signLaw n r).real {v | nonPairDependence v} + pairsError n :=
      add_le_add (dependence_sub_pair_abs_le (by omega)) (pairCollision_probability_error n r hnr)
    _ ≤ low n + high n + pairsError n := add_le_add (hmono.trans hendpoint) le_rfl
    _ ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
      simpa only [scale, mul_div_assoc] using h n (by omega)

end BooleanThreshold
