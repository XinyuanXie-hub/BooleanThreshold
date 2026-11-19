module

public import BooleanThreshold.JSSCorankFrame
public import BooleanThreshold.JSSConditionalOperatorNorm
public import Mathlib.Data.Nat.Choose.Sum

public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace BooleanThreshold

private theorem weighted_choose_bound {z y : ℝ} (hz : 0 < z) (hy : 0 ≤ y)
    {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) * y ^ k ≤ (1 + z) ^ n * (y / z) ^ k := by
  have h := Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => z ^ j * (1 : ℝ) ^ (n - j) * (n.choose j : ℝ))
    (fun j _ => by positivity) (Finset.mem_range.mpr (by omega : k < n + 1))
  rw [← add_pow] at h
  have h₀ : (n.choose k : ℝ) * z ^ k ≤ (1 + z) ^ n := by
    simpa [add_comm, mul_comm] using h
  calc
    _ = ((n.choose k : ℝ) * z ^ k) * (y / z) ^ k := by
      rw [mul_assoc, ← mul_pow, show z * (y / z) = y by field_simp [hz.ne']]
    _ ≤ _ := mul_le_mul_of_nonneg_right h₀ (by positivity)

private theorem weighted_choose_thin {z y γ : ℝ} (hz : 0 < z) (hy : 0 ≤ y) (hγ : 1 < γ) :
    ∃ J : ℕ, 0 < J ∧ ∀ n : ℕ,
      (n.choose (n / J) : ℝ) * y ^ (n / J) ≤ ((1 + z) * γ) ^ n := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (y / z) hγ
  let J := j + 1
  have hJ : y / z ≤ γ ^ J := hj.le.trans (pow_le_pow_right₀ hγ.le (by dsimp [J]; omega))
  refine ⟨J, by simp [J], fun n => ?_⟩
  calc
    _ ≤ (1 + z) ^ n * (y / z) ^ (n / J) := weighted_choose_bound hz hy (Nat.div_le_self _ _)
    _ ≤ (1 + z) ^ n * (γ ^ J) ^ (n / J) := by gcongr
    _ ≤ (1 + z) ^ n * γ ^ n := by
      rw [← pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hγ.le (Nat.mul_div_le _ _))
        (by positivity)
    _ = _ := (mul_pow _ _ _).symm

private theorem smallRowFailures_thin :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ,
      (m.choose (m / N) : ℝ) * (7 / 16 : ℝ) ^ (m - m / N) ≤
        ((101 / 100 : ℝ) ^ 2 * (7 / 16)) ^ m := by
  let q := (7 / 16 : ℝ)
  have hq : 0 < q := by norm_num [q]
  obtain ⟨N, hN, hthin⟩ := weighted_choose_thin
    (show (0 : ℝ) < 1 / 100 by norm_num) (inv_nonneg.mpr hq.le)
    (show (1 : ℝ) < 101 / 100 by norm_num)
  refine ⟨N, hN, fun m => ?_⟩
  change (m.choose (m / N) : ℝ) * q ^ (m - m / N) ≤ ((101 / 100 : ℝ) ^ 2 * q) ^ m
  calc
    _ = ((m.choose (m / N) : ℝ) * q⁻¹ ^ (m / N)) * q ^ m := by
      have hpow : q ^ (m - m / N) = q ^ m / q ^ (m / N) := by
        apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
        rw [← pow_add, Nat.sub_add_cancel (Nat.div_le_self _ _)]
      rw [hpow, inv_pow, div_eq_mul_inv]
      ring
    _ ≤ ((101 / 100 : ℝ) ^ 2) ^ m * q ^ m := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have heq : (1 + (1 / 100 : ℝ)) * (101 / 100) = (101 / 100) ^ 2 := by norm_num
      simpa only [heq] using hthin m
    _ = _ := (mul_pow _ _ _).symm

private theorem energyBudget_for_thin_rows {K : ℝ} (hK : 0 < K) {N : ℕ} (hN : 0 < N)
    {m : ℕ} (hmN : N ≤ m) (hm : 2 ≤ m)
    (ε : ℝ) (hε : ε = 1 / (2000 * (K + 1) * (N : ℝ))) :
    8 * K ^ 2 * ((m + 2 : ℕ) : ℝ) * (ε + 2 * ε) ^ 2 ≤
      ((m / N : ℕ) : ℝ) * (1 / 100 : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hK1 : 0 < K + 1 := by positivity
  have hscaled : K * ε ≤ 1 / (2000 * (N : ℝ)) := by
    rw [hε, show K * (1 / (2000 * (K + 1) * (N : ℝ))) =
      (K / (K + 1)) * (1 / (2000 * (N : ℝ))) by
        field_simp [hK1.ne', hNpos.ne']]
    exact (mul_le_mul_of_nonneg_right ((div_le_one hK1).2 (by linarith))
      (by positivity)).trans_eq (one_mul _)
  have hscaled₂ := pow_le_pow_left₀ (by rw [hε]; positivity : 0 ≤ K * ε) hscaled 2
  have hnum : 72 * (1 / (2000 * (N : ℝ))) ^ 2 ≤ 1 / (4 * (N : ℝ)) * (1 / 100 : ℝ) ^ 2 := by
    field_simp [hNpos.ne']
    nlinarith only [hN1]
  have hdivN : 1 ≤ m / N := (Nat.le_div_iff_mul_le hN).2 (by simpa using hmN)
  have hmulN : N ≤ N * (m / N) := by
    simpa using Nat.mul_le_mul_left N hdivN
  have hmd : m + 2 ≤ 4 * (N * (m / N)) := by
    have hr := Nat.mod_lt m hN
    have h := Nat.mod_add_div m N
    omega
  have hd : ((m + 2 : ℕ) : ℝ) / (4 * (N : ℝ)) ≤ ((m / N : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    rw [mul_comm (((m / N : ℕ) : ℝ)), mul_assoc]
    exact_mod_cast hmd
  calc
    _ = ((m + 2 : ℕ) : ℝ) * (72 * (K * ε) ^ 2) := by ring
    _ ≤ ((m + 2 : ℕ) : ℝ) * (72 * (1 / (2000 * (N : ℝ))) ^ 2) := by gcongr
    _ ≤ ((m + 2 : ℕ) : ℝ) * (1 / (4 * (N : ℝ)) * (1 / 100 : ℝ) ^ 2) := by gcongr
    _ = ((m + 2 : ℕ) : ℝ) / (4 * (N : ℝ)) * (1 / 100 : ℝ) ^ 2 := by ring
    _ ≤ _ := by gcongr

/-- The compressible-kernel contribution to square corank two is exponentially
smaller than `2⁻ⁿ`. This is the sign-matrix, two-dimensional version of the
compressible estimate in Jain–Sah–Sawhney, with a fixed rate sufficient here. -/
theorem corankCompressible_probability_geometric :
    ∃ ρ > (0 : ℝ), ρ < 1 ∧ ∃ J : ℕ, 0 < J ∧ ∃ C > (0 : ℝ), ∀ᶠ m : ℕ in atTop,
      (uniformOn Set.univ).real (corankCompressibleEvent m (m + 2) ((m + 2) / J) ρ) ≤
        C * (15 / 32 : ℝ) ^ (m + 2) := by
  obtain ⟨K, hK, hop⟩ := signMatrix_norm_tail_exponential 2 (by norm_num)
  obtain ⟨N, hN, hrows⟩ := smallRowFailures_thin
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let ε : ℝ≥0 := ⟨1 / (2000 * (K + 1) * (N : ℝ)), by positivity⟩
  have hε : 0 < ε := by
    change (0 : ℝ) < (ε : ℝ)
    exact div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) (by linarith)) hNpos)
  have hρ : (ε : ℝ) < 1 := by
    change 1 / (2000 * (K + 1) * (N : ℝ)) < 1
    rw [div_lt_iff₀ (by positivity), one_mul]
    nlinarith only [hN1, hK, mul_nonneg hK.le (sub_nonneg.mpr hN1)]
  obtain ⟨J, hJ, hnet⟩ := weighted_choose_thin
    (show (0 : ℝ) < 1 / 100 by norm_num)
    (show (0 : ℝ) ≤ 1 + 2 / (ε : ℝ) by positivity)
    (show (1 : ℝ) < 101 / 100 by norm_num)
  let rowBase := (101 / 100 : ℝ) ^ 2 * (7 / 16)
  let netBase := (101 / 100 : ℝ) ^ 2
  have hrb : 0 < rowBase := by norm_num [rowBase]
  have hNB : netBase ^ 2 * rowBase ≤ (15 / 32 : ℝ) := by norm_num [netBase, rowBase]
  have hOne : Real.exp (-2) ≤ 1 / 4 := by
    rw [Real.exp_neg, ← one_div]
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨(ε : ℝ), by exact_mod_cast hε, hρ, J, hJ, 1 + (rowBase ^ 2)⁻¹,
    by positivity, ?_⟩
  refine eventually_atTop.mpr ⟨max N 2, fun m hm => ?_⟩
  let d := m + 2
  let s := d / J
  let e := m / N
  have hbudget := energyBudget_for_thin_rows hK hN
    ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm) (ε : ℝ) rfl
  have hprob := corankCompressible_probability_le (m := m) (n := d) (s := s) (e := e)
    le_rfl (Nat.div_le_self _ _) (Nat.div_le_self _ _) hρ hε hbudget
  have hnet' : (d.choose s : ℝ) * (1 + 2 / (ε : ℝ)) ^ s ≤ netBase ^ d := by
    have heq : (1 + (1 / 100 : ℝ)) * (101 / 100) = (101 / 100) ^ 2 := by norm_num
    simpa only [s, netBase, heq] using hnet d
  have hop' := hop d m (by dsimp [d]; omega) (by dsimp [d]; omega)
  have hnorm : (uniformOn Set.univ).real {M : Fin m → Fin d → Bool |
      ∃ a : Fin d → ℝ, K ^ 2 * (d : ℝ) * squaredNorm a < squaredNorm (signMatrixMap M a)} ≤
      (15 / 32 : ℝ) ^ d := by
    calc
      _ ≤ Real.exp (-2 * (d : ℝ)) := by simpa only [squaredNorm, signMatrixMap_apply] using hop'
      _ = Real.exp (-2) ^ d := by rw [mul_comm, Real.exp_nat_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (hOne.trans (by norm_num)) _
  have hnetrow :
      (netBase ^ d) ^ 2 * rowBase ^ m ≤ (rowBase ^ 2)⁻¹ * (15 / 32 : ℝ) ^ d := by
    calc
      _ = (rowBase ^ 2)⁻¹ * (netBase ^ 2 * rowBase) ^ d := by
        have hn : (netBase ^ d) ^ 2 = (netBase ^ 2) ^ d := by
          rw [← pow_mul netBase d 2, ← pow_mul netBase 2 d, Nat.mul_comm d 2]
        rw [hn, mul_pow (netBase ^ 2) rowBase d, show rowBase ^ d = rowBase ^ m * rowBase ^ 2
          from pow_add rowBase m 2]
        field_simp [hrb.ne']
      _ ≤ _ := by gcongr
  calc
    _ ≤ _ := hprob
    _ ≤ (15 / 32 : ℝ) ^ d + (netBase ^ d) ^ 2 * rowBase ^ m := by
      exact add_le_add hnorm (mul_le_mul (pow_le_pow_left₀ (by positivity) hnet' 2)
        (hrows m) (by positivity) (by positivity))
    _ ≤ (15 / 32 : ℝ) ^ d + (rowBase ^ 2)⁻¹ * (15 / 32 : ℝ) ^ d :=
      add_le_add (le_refl _) hnetrow
    _ = _ := by ring

end BooleanThreshold
