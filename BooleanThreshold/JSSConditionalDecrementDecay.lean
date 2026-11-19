module

public import BooleanThreshold.Asymptotics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open Filter
open scoped Topology

namespace BooleanThreshold

/-- Two blocks of a fixed positive fraction of the coordinates suffice to
absorb the polynomial factors and the cyclic-group count in the decrement
estimate. -/
theorem exists_twoBlock_decrement_decay {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, ∃ κ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ p j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ N P m₁ m₂ : ℕ,
        Real.sqrt (n : ℝ) ≤ N → P ≤ 2 ^ n →
        c * (n : ℝ) ≤ m₁ → c * (n : ℝ) ≤ m₂ → m₂ ≤ n →
        let d := ⌊κ * (N : ℝ)⌋₊
        κ * (N : ℝ) / 2 ≤ d ∧ (d : ℝ) ≤ κ * N ∧ d ≤ N ∧ 2 * j ≤ m₂ ∧
          q ^ m₁ / (1 / (n : ℝ)) ^ p + (P : ℝ) * 4 ^ m₂ *
            ((d : ℝ) / (N : ℝ)) ^ (m₂ - j) ≤ Real.exp (-M * (n : ℝ)) := by
  let q := Real.exp (-2 * (M + 4) / c)
  have hq₀ : 0 < q := Real.exp_pos _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith only [hM]) hc)
  refine ⟨q, ⟨hq₀, hq₁⟩, q, ⟨hq₀, hq₁⟩, fun p j => ?_⟩
  obtain ⟨A, hA⟩ := exists_nat_ge ((2 / q : ℝ) ^ 2)
  obtain ⟨B, hB⟩ := exists_nat_ge ((2 * (j : ℝ)) / c)
  have hpoly : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ p ≤ Real.exp (n : ℝ) := by
    filter_upwards [(tendsto_pow_const_div_const_pow_of_one_lt p
      (Real.one_lt_exp_iff.mpr zero_lt_one)).eventually_le_const (show (0 : ℝ) < 1 by norm_num)] with n hn
    have h := (div_le_iff₀ (pow_pos (Real.exp_pos 1) n)).mp hn
    rw [one_mul, ← Real.exp_nat_mul, mul_one] at h
    exact h
  filter_upwards [hpoly, eventually_ge_atTop A, eventually_ge_atTop B, eventually_ge_atTop 1] with n hpn hnA hnB hn₀
  intro N P m₁ m₂ hN hP hm₁ hm₂ hm₂n
  let d := ⌊q * (N : ℝ)⌋₊
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn
  have hN' : 2 / q ≤ (N : ℝ) := by
    refine ((Real.le_sqrt (by positivity) (Nat.cast_nonneg n)).mpr ?_).trans hN
    exact hA.trans (by exact_mod_cast hnA)
  have hNpos : (0 : ℝ) < N := (by positivity : 0 < 2 / q).trans_le hN'
  have hqN : 2 ≤ q * (N : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hq₀).mp hN'
  have hd₀ : q * (N : ℝ) / 2 ≤ d := by
    have hf := Nat.lt_floor_add_one (q * (N : ℝ))
    change q * (N : ℝ) < (d : ℝ) + 1 at hf
    linarith only [hf, hqN]
  have hd₁ : (d : ℝ) ≤ q * N := Nat.floor_le (by positivity)
  have hdN : d ≤ N := by
    exact_mod_cast hd₁.trans (mul_le_of_le_one_left hNpos.le hq₁.le)
  have hj : 2 * j ≤ m₂ := by
    have h : 2 * (j : ℝ) ≤ c * (n : ℝ) := by
      rw [mul_comm c]
      exact (div_le_iff₀ hc).mp (hB.trans (by exact_mod_cast hnB))
    exact_mod_cast h.trans hm₂
  refine ⟨hd₀, hd₁, hdN, hj, ?_⟩
  have hqpow {k : ℕ} (hk : c * (n : ℝ) / 2 ≤ k) :
      q ^ k ≤ Real.exp (-(M + 4) * (n : ℝ)) := by
    have hcn : (n : ℝ) ≤ 2 * (k : ℝ) / c := by
      apply (le_div_iff₀ hc).mpr
      linarith only [hk]
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      _ = -(M + 4) * (2 * (k : ℝ) / c) := by ring
      _ ≤ _ := mul_le_mul_of_nonpos_left hcn (by linarith only [hM])
  have hpow₁ := hqpow (k := m₁) (by linarith only [hm₁, mul_nonneg hc.le hnpos.le])
  have hpow₂ := hqpow (k := m₂ - j) (by
    have hh : (m₂ : ℝ) ≤ 2 * ((m₂ - j : ℕ) : ℝ) := by exact_mod_cast (show m₂ ≤ 2 * (m₂ - j) by omega)
    linarith only [hm₂, hh])
  have hcoeff₁ : q ^ m₁ / (1 / (n : ℝ)) ^ p ≤ Real.exp (-(M + 1) * (n : ℝ)) := by
    rw [one_div, inv_pow, div_inv_eq_mul]
    calc
      _ ≤ Real.exp (-(M + 4) * (n : ℝ)) * Real.exp (n : ℝ) := by gcongr
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith only [hnpos]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have height : (8 : ℝ) ≤ Real.exp 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 3
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have hP4 : (P : ℝ) * 4 ^ m₂ ≤ Real.exp (3 * (n : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ n * 4 ^ n := mul_le_mul (by exact_mod_cast hP)
        (pow_le_pow_right₀ (by norm_num) hm₂n) (by positivity) (by positivity)
      _ = (8 : ℝ) ^ n := by rw [← mul_pow]; norm_num
      _ ≤ Real.exp 3 ^ n := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) height _
      _ = _ := by rw [← Real.exp_nat_mul, mul_comm]
  have hdq : (d : ℝ) / (N : ℝ) ≤ q := (div_le_iff₀ hNpos).mpr hd₁
  have hcoeff₂ : (P : ℝ) * 4 ^ m₂ * ((d : ℝ) / (N : ℝ)) ^ (m₂ - j) ≤ Real.exp (-(M + 1) * (n : ℝ)) := by
    have hr := (pow_le_pow_left₀ (by positivity : 0 ≤ (d : ℝ) / (N : ℝ)) hdq (m₂ - j)).trans hpow₂
    calc
      _ ≤ Real.exp (3 * (n : ℝ)) * Real.exp (-(M + 4) * (n : ℝ)) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (-(M + 1) * (n : ℝ)) + Real.exp (-(M + 1) * (n : ℝ)) := add_le_add hcoeff₁ hcoeff₂
    _ = Real.exp (-M * (n : ℝ)) * (2 / Real.exp (n : ℝ)) := by
      rw [show -(M + 1) * (n : ℝ) = -M * (n : ℝ) + -(n : ℝ) by ring, Real.exp_add, Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_of_le_one_right (Real.exp_nonneg _)
      exact (div_le_one (Real.exp_pos _)).mpr (htwo.trans (Real.exp_le_exp.mpr hn))

/-- A polynomial multiple of the maximum lattice scale is eventually below
the cyclic-group size allowed by the decrement estimate. -/
theorem polynomial_multiple_of_cyclic_scale_eventually_le_two_pow (A d : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, (N : ℝ) ≤ (5 / 3 : ℝ) ^ n → A * n ^ d * N + 1 ≤ 2 ^ n := by
  have hlimit := tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 6 / 5)
  have htol : 0 < 1 / ((A : ℝ) + 1) := by positivity
  filter_upwards [hlimit.eventually_le_const htol, eventually_ge_atTop 1] with n hsmall hn N hN
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly₀ : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ hn'
  have hgeom₀ : (1 : ℝ) ≤ (5 / 3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hsize := (div_le_div_iff₀ (by positivity : 0 < (6 / 5 : ℝ) ^ n)
    (by positivity : 0 < (A : ℝ) + 1)).mp hsmall
  rw [one_mul] at hsize
  have h : (A : ℝ) * (n : ℝ) ^ d * N + 1 ≤ (2 : ℝ) ^ n := calc
    _ ≤ (A : ℝ) * ((n : ℝ) ^ d * (5 / 3 : ℝ) ^ n) + ((n : ℝ) ^ d * (5 / 3 : ℝ) ^ n) := by
      rw [← mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left hN (by positivity))
        (one_le_mul_of_one_le_of_one_le hpoly₀ hgeom₀)
    _ = ((n : ℝ) ^ d * ((A : ℝ) + 1)) * (5 / 3 : ℝ) ^ n := by ring
    _ ≤ (6 / 5 : ℝ) ^ n * (5 / 3 : ℝ) ^ n := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num
  exact_mod_cast h

end BooleanThreshold
