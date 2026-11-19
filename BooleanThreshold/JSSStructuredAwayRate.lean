module

public import BooleanThreshold.JSSStructuredBounds
public import BooleanThreshold.JSSStructuredPairs

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanThreshold

private theorem eventually_floor_fraction_bounds {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) :
    ∀ᶠ n : ℕ in atTop, let k := ⌊b * (n : ℝ)⌋₊
      k ≤ n ∧ b / 2 * (n : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ b * (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / b)
  filter_upwards [eventually_ge_atTop N] with n hn
  let k := ⌊b * (n : ℝ)⌋₊
  have hhi : (k : ℝ) ≤ b * (n : ℝ) := Nat.floor_le (by positivity)
  have hlt : b * (n : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlarge : 2 ≤ b * (n : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hb).mp (hN.trans (by exact_mod_cast hn))
  have hkn : (k : ℝ) ≤ (n : ℝ) := hhi.trans (by
    simpa using mul_le_mul_of_nonneg_right hb₁ (Nat.cast_nonneg n))
  exact ⟨by exact_mod_cast hkn, by linarith only [hlt, hlarge], hhi⟩

/-- An almost-constant null vector in a family with row concentration at most
`7/16` contributes only an exponentially smaller error than `2⁻ⁿ`. -/
theorem eventually_uniformOn_awayAlmostConstantNull_le {K θ : ℝ}
    (hK : 0 ≤ K) (hθ : 0 < θ) (S : ∀ n : ℕ, Set (Fin n → ℝ))
    (hconc : ∀ n a, a ∈ S n → squaredNorm a = 1 →
      uniformOn Set.univ {row : Fin n → Bool | |signSum a row| ≤ θ} ≤ 7 / 16) :
    ∃ δ > (0 : ℝ), δ < 1 ∧ ∃ ρ > (0 : ℝ), ρ < 1 ∧ ∃ D > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, (uniformOn Set.univ).real {M : Fin n → Fin n → Bool |
        signOpBound K M ∧ ∃ a ∈ S n ∩ almostConstantUnitVectors n δ ρ, signMatrixMap M a = 0} ≤
        D * (15 / 32 : ℝ) ^ n := by
  let q : ℝ := 7 / 16
  let R : ℝ := 101 / 100
  have hq : 0 < q := by norm_num [q]
  have hR : 1 < R := by norm_num [R]
  obtain ⟨γ, hγ, hrowCount⟩ := exists_sparse_count_growth_bound (B := q⁻¹) (R := R)
    (by norm_num [q]) hR
  let b := min γ (1 / 2)
  have hb : 0 < b := lt_min hγ (by norm_num)
  have hb₁ : b ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let ρ := min (1 / 2) (θ * Real.sqrt (b / 2) / (4 * (1 + K)))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ₁ : ρ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  let ε : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hε : 0 < ε := hρ
  let A := 1 + 2 * (1 + ρ) / ρ
  have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  obtain ⟨η, hη, hnetCount⟩ := exists_sparse_count_growth_bound (B := A) (R := R) hA hR
  let b' := min η (1 / 2)
  have hb' : 0 < b' := lt_min hη (by norm_num)
  have hb'₁ : b' ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let δ := b' / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ < 1 := by dsimp [δ]; linarith only [hb'₁]
  refine ⟨δ, hδ, hδ₁, ρ, hρ, hρ₁, A, zero_lt_one.trans_le hA, ?_⟩
  filter_upwards [eventually_floor_fraction_bounds hb hb₁, eventually_floor_fraction_bounds hb' hb'₁,
    eventually_ge_atTop (1 : ℕ)] with n hrow hnet hn
  let l := ⌊b * (n : ℝ)⌋₊
  let k := ⌊b' * (n : ℝ)⌋₊
  obtain ⟨hl, hl₀, hl₁⟩ : l ≤ n ∧ b / 2 * (n : ℝ) ≤ (l : ℝ) ∧ (l : ℝ) ≤ b * (n : ℝ) := hrow
  obtain ⟨hk, hk₀, hk₁⟩ : k ≤ n ∧ δ * (n : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ b' * (n : ℝ) := hnet
  have hρbudget : 4 * K * ρ ≤ θ * Real.sqrt (b / 2) := by
    calc
      _ ≤ 4 * (1 + K) * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ.le
      _ ≤ _ := by
        rw [mul_comm]
        exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have henergy : K ^ 2 * (n : ℝ) * (2 * (ρ + (ε : ℝ))) ^ 2 ≤ (l : ℝ) * θ ^ 2 := by
    have hs := pow_le_pow_left₀ (show 0 ≤ 4 * K * ρ by positivity) hρbudget 2
    rw [mul_pow θ, Real.sq_sqrt (by positivity)] at hs
    calc
      _ = (4 * K * ρ) ^ 2 * (n : ℝ) := by change _ * (2 * (ρ + ρ)) ^ 2 = _; ring
      _ ≤ (θ ^ 2 * (b / 2)) * (n : ℝ) := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)
      _ = (b / 2 * (n : ℝ)) * θ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hl₀ (sq_nonneg _)
  let T := S n ∩ almostConstantUnitVectors n δ ρ
  have hprob := uniformOn_cons_null_le_of_smallBall (show 0 < n by omega)
    hl hρ.le hθ hε hk₀ henergy T Set.inter_subset_right (q := (7 / 16 : ℝ≥0∞))
      (ENNReal.div_ne_top (by simp) (by simp)) (fun a ha => hconc n a ha.1 ha.2.1)
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at hprob
  change (uniformOn Set.univ).real _ ≤
    (∑ s ∈ Finset.range (k + 1), (n.choose s : ℝ)) * A ^ (k + 1) *
      (n.choose l : ℝ) * q ^ (n - l) at hprob
  have hnet' : (∑ s ∈ Finset.range (k + 1), (n.choose s : ℝ)) * A ^ (k + 1) ≤ A * R ^ n := by
    rw [pow_succ, ← mul_assoc, mul_comm _ A]
    exact mul_le_mul_of_nonneg_left
      (hnetCount n k hk (hk₁.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))))
      (zero_lt_one.trans_le hA).le
  have hrow' : (n.choose l : ℝ) * q ^ (n - l) ≤ (R * q) ^ n := by
    have hchoose : (n.choose l : ℝ) ≤ ∑ s ∈ Finset.range (l + 1), (n.choose s : ℝ) :=
      Finset.single_le_sum (fun s _ => Nat.cast_nonneg (n.choose s)) (Finset.mem_range_succ_iff.mpr le_rfl)
    have hcount := (mul_le_mul_of_nonneg_right hchoose (pow_nonneg (inv_nonneg.mpr hq.le) _)).trans
        (hrowCount n l hl (hl₁.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))))
    have hpow : q ^ (n - l) = q⁻¹ ^ l * q ^ n := by
      have hp : q ^ n = q ^ (n - l) * q ^ l := by rw [← pow_add, Nat.sub_add_cancel hl]
      rw [hp, inv_pow, mul_left_comm (q ^ l)⁻¹, inv_mul_cancel₀ (pow_ne_zero _ hq.ne'), mul_one]
    rw [hpow, ← mul_assoc, mul_pow]
    exact mul_le_mul_of_nonneg_right hcount (pow_nonneg hq.le _)
  refine hprob.trans ?_
  calc
    _ = ((∑ s ∈ Finset.range (k + 1), (n.choose s : ℝ)) * A ^ (k + 1)) *
          ((n.choose l : ℝ) * q ^ (n - l)) := mul_assoc _ _ _
    _ ≤ (A * R ^ n) * (R * q) ^ n :=
      mul_le_mul hnet' hrow' (by positivity) (by positivity)
    _ = A * (R ^ 2 * q) ^ n := by rw [mul_assoc, ← mul_pow]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by norm_num [R, q]) _)
      (zero_lt_one.trans_le hA).le

end BooleanThreshold
