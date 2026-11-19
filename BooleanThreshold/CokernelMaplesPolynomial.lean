module

public import BooleanThreshold.CokernelMaplesBadNormal
public import BooleanThreshold.CokernelMaplesHighConcentrationAsymptotic
public import BooleanThreshold.CokernelMaplesProjectionComparison
public import BooleanThreshold.CokernelMaplesRates
public import BooleanThreshold.CokernelMaplesSemisaturated
public import BooleanThreshold.CokernelPolynomialMoment

public noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Matrix

namespace BooleanThreshold

/-- The determinant comparison at polynomial moduli follows from excluding
dense prefix normals of large row concentration. -/
theorem eventually_binaryModularDetZeroComparison_of_large_atoms (B M : ℕ)
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q ≤ n ^ B → 0 < q →
      (uniformOn Set.univ).real {R : Fin (n - maplesSuffixLength (((M : ℝ) + 2) / Real.log 2) n) →
          Fin n → Bool |
        ∃ a : Fin n → ZMod q, DenseCyclicNormal a ∧ 16 / (q : ℝ) < binaryZeroAtom a ∧
          ∀ j, a ⬝ᵥ binaryColumn (ZMod q) (R j) = 0} ≤ (1 / 2 : ℝ) ^ n) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : ℕ) [NeZero q], q ≤ n ^ B → q.primeFactors.card ≤ 102 →
      binaryModularDetZeroComparison n q (1 / (n : ℝ) ^ M) := by
  let L := ((M : ℝ) + 2) / Real.log 2
  have hL : 0 ≤ L := maplesSuffixLength_nonneg_factor M
  obtain ⟨d, hd, hsmall⟩ := maples_semisaturated_exclusion (D := 16) (by norm_num) hL B
  filter_upwards [hlarge, hsmall, eventually_maplesSuffixLength_le_half hL,
    eventually_maples_comparison_error_le hd B M] with n hlarge hsmall hk herr
  intro q _ hq hs
  let k := maplesSuffixLength L n
  let m := n - k
  let ε := Real.exp (-d * (n : ℝ))
  let Ω := Fin m → Fin n → Bool
  let Good (R : Ω) := binaryPrefixIndependent q R ∧ ¬ HasLargeBinaryFourierNormal (q := q) ε R
  let μ : Measure Ω := uniformOn Set.univ
  have hm : m + k = n := by dsimp [m, k] at *; omega
  have hm' : m ≤ n := by omega
  have hε : 0 ≤ ε := Real.exp_nonneg _
  have hbadFourier := bad_prefix_Fourier_probability_le (q := q) (m := m)
    (ε := ε) (β := (1 / 2 : ℝ) ^ n) (by positivity)
      (fun r hr _ => hsmall r ((Nat.le_of_dvd (NeZero.pos q) (Nat.dvd_of_mem_divisors hr)).trans hq))
      (fun r hr => hlarge r ((Nat.le_of_dvd (NeZero.pos q) (Nat.dvd_of_mem_divisors hr)).trans hq)
        (Nat.pos_of_mem_divisors hr))
  have hSparse := sparseBinaryNormal_probability_geometric (q := q) (m := m)
    (N := n) hm' (by dsimp [m, k] at *; omega)
  have hs' : (q.primeFactors.card : ℝ) ≤ 102 := by exact_mod_cast hs
  have hSparse' := hSparse.trans (mul_le_mul_of_nonneg_right hs' (by positivity))
  have hGood (R : Ω) (hR : Good R) :
      ∃ P : (Fin n → ZMod q) →ₗ[ZMod q] (Fin k → ZMod q),
        (∀ X : Fin k → Fin n → ZMod q,
          (appendMatrixColumns hm ((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))) X).det = 0 ↔
            (Matrix.of (fun i j => P (X j) i)).det = 0) ∧
        (∀ y, |finiteEventProbability (fun x : Fin n → Bool => P (binaryColumn (ZMod q) x) = y) -
          1 / (q : ℝ) ^ k| ≤ ε) := by
    obtain ⟨P, hP, hker, hDet⟩ := binaryMatrixPrefixProjection hm R hR.1
    exact ⟨P, hDet, projected_binary_probability_abs_sub_le hε hR.2 P hP hker⟩
  let F := {R : Ω | ¬ binaryPrefixIndependent q R}
  let G := {R : Ω | HasLargeBinaryFourierNormal (q := q) ε R}
  have hrank : (q.primeFactors.card : ℝ) * (m : ℝ) * (1 / 2 : ℝ) ^ (n + 1 - m) ≤
      102 * (n : ℝ) * (1 / 2 : ℝ) ^ k := by
    rw [show n + 1 - m = k + 1 by omega, pow_succ]
    have h₁ : (m : ℝ) ≤ n := by exact_mod_cast hm'
    have h₂ : (q.primeFactors.card : ℝ) * (m : ℝ) ≤ 102 * (n : ℝ) :=
      mul_le_mul hs' h₁ (by positivity) (by norm_num)
    exact mul_le_mul h₂ (mul_le_of_le_one_right (by positivity) (by norm_num))
      (by positivity) (by positivity)
  have hbadGood : finiteEventProbability (fun R => ¬ Good R) ≤
      102 * (n : ℝ) * (1 / 2 : ℝ) ^ k +
        (102 * (14739 / 16384 : ℝ) ^ n + 2 * (q : ℝ) * (1 / 2 : ℝ) ^ n) := by
    have hmeasure : finiteEventProbability (fun R => ¬ Good R) =
        μ.real {R | ¬ Good R} := finiteAverage_indicator {R | ¬ Good R}
    rw [hmeasure]
    have heq : {R | ¬ Good R} = F ∪ G := by
      ext R
      change ¬ (binaryPrefixIndependent q R ∧ ¬ HasLargeBinaryFourierNormal (q := q) ε R) ↔
        ¬ binaryPrefixIndependent q R ∨ HasLargeBinaryFourierNormal (q := q) ε R
      tauto
    rw [heq]
    exact (measureReal_union_le F G).trans (add_le_add
      ((binaryPrefixIndependent_failure_probability_le (q := q) hm').trans hrank)
      (hbadFourier.trans (add_le_add hSparse' le_rfl)))
  have hcmp := binary_uniform_det_zero_comparison_of_projected_suffix hm Good hε hGood
  unfold binaryModularDetZeroComparison
  refine hcmp.trans ?_
  calc
    _ ≤ (k : ℝ) * (q : ℝ) ^ (k * k) * ε +
        (102 * (n : ℝ) * (1 / 2 : ℝ) ^ k +
          (102 * (14739 / 16384 : ℝ) ^ n + 2 * (q : ℝ) * (1 / 2 : ℝ) ^ n)) +
        102 * (n : ℝ) * (1 / 2 : ℝ) ^ k :=
      add_le_add (add_le_add le_rfl hbadGood) hrank
    _ = (k : ℝ) * (q : ℝ) ^ (k * k) * ε +
        (102 * (14739 / 16384 : ℝ) ^ n + 2 * (q : ℝ) * (1 / 2 : ℝ) ^ n) +
        204 * (n : ℝ) * (1 / 2 : ℝ) ^ k := by ring
    _ ≤ _ := herr q hq

/-- Binary and uniform determinant-zero probabilities agree up to any
inverse power, uniformly for polynomial moduli with bounded prime support. -/
theorem eventually_binaryModularDetZeroComparison (B M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : ℕ) [NeZero q], q ≤ n ^ B → q.primeFactors.card ≤ 102 →
      binaryModularDetZeroComparison n q (1 / (n : ℝ) ^ M) := by
  apply eventually_binaryModularDetZeroComparison_of_large_atoms B M
  filter_upwards [maples_high_concentration_exclusion (maplesSuffixLength_nonneg_factor M) B]
    with n hn q hq hqpos
  let : NeZero q := ⟨hqpos.ne'⟩
  exact hn q hq

theorem eventually_binaryModularDetZeroComparison_succ (B M : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (q : ℕ) [NeZero q], q ≤ N ^ B → q.primeFactors.card ≤ 102 →
      binaryModularDetZeroComparison (N + 1) q (1 / (N : ℝ) ^ M) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_binaryModularDetZeroComparison B M)
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN q _ hq hs
  have hN' : N₀ ≤ N + 1 := (le_max_left _ _).trans (hN.trans N.le_succ)
  have hq' : q ≤ (N + 1) ^ B := hq.trans (Nat.pow_le_pow_left N.le_succ B)
  have hcmp := hN₀ (N + 1) hN' q hq' hs
  unfold binaryModularDetZeroComparison at hcmp ⊢
  apply hcmp.trans
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact one_div_le_one_div_of_le (pow_pos hpos _)
    (pow_le_pow_left₀ hpos.le (by exact_mod_cast N.le_succ) M)

end BooleanThreshold
