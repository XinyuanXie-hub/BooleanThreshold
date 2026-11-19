module

public import BooleanThreshold.JSSConditionalTail
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Data.Nat.Choose.Central

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace BooleanThreshold

/-- The Littlewood–Offord bound for a sign sum on an interval narrower than
every individual sign change. -/
theorem signSum_smallBall_le_middle_binomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (z r : ℝ) (ha : ∀ i, r < |a i|) :
    (uniformOn Set.univ).real {b : ι → Bool | |signSum a b - z| ≤ r} ≤
      ((Fintype.card ι).choose (Fintype.card ι / 2) : ℝ) / 2 ^ Fintype.card ι := by
  let f (b : ι → Bool) := Finset.univ.filter (fun i => if 0 ≤ a i then b i else !b i)
  have hf : Function.Injective f := by
    intro b d h
    funext i
    have he := Finset.ext_iff.mp h i
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at he
    by_cases hi : 0 ≤ a i <;> cases hb : b i <;> cases hd : d i <;> simp_all
  have hsum (b : ι → Bool) : signSum a b = 2 * (∑ i ∈ f b, |a i|) - ∑ i, |a i| := by
    have hpoint (i : ι) : a i * (if b i then (1 : ℝ) else -1) =
        2 * (if (if 0 ≤ a i then b i else !b i) then |a i| else 0) - |a i| := by
      by_cases hi : 0 ≤ a i <;> cases hb : b i
      all_goals simp [hi, abs_of_nonneg, abs_of_neg, lt_of_not_ge]
      all_goals ring
    simp only [signSum]
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  let E : Set (ι → Bool) := {b | |signSum a b - z| ≤ r}
  let S := E.toFinite.toFinset.image f
  have hanti : IsAntichain (· ⊆ ·) (S : Set (Finset ι)) := by
    intro I hI J hJ hij hsub
    obtain ⟨b, hb, hib⟩ := Finset.mem_image.mp hI
    obtain ⟨d, hd, hjd⟩ := Finset.mem_image.mp hJ
    obtain ⟨i, hiJ, hiI⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hij⟩))
    have hi : i ∈ J \ I := Finset.mem_sdiff.mpr ⟨hiJ, hiI⟩
    have hpart : ∑ j ∈ J \ I, |a j| + ∑ j ∈ I, |a j| = ∑ j ∈ J, |a j| :=
      Finset.sum_sdiff hsub
    have hgap := (ha i).trans_le (Finset.single_le_sum (f := fun j => |a j|)
      (fun _ _ => abs_nonneg _) hi)
    have hb' : |signSum a b - z| ≤ r := E.toFinite.mem_toFinset.mp hb
    have hd' : |signSum a d - z| ≤ r := E.toFinite.mem_toFinset.mp hd
    have hb₀ := (abs_le.mp hb').1
    have hd₀ := (abs_le.mp hd').2
    rw [hsum, hib] at hb₀
    rw [hsum, hjd] at hd₀
    linarith only [hpart, hgap, hb₀, hd₀]
  have h := hanti.sperner
  have hc : E.ncard = S.card := by
    rw [Set.ncard_eq_toFinset_card E E.toFinite, show S = E.toFinite.toFinset.image f by rfl,
      Finset.card_image_of_injective _ hf]
  change (uniformOn Set.univ).real E ≤ _
  rw [uniformOn_univ_real_eq_card, hc, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

private theorem centralBinom_sq_div_pow_le (k : ℕ) :
    ((k.centralBinom : ℝ) / (4 : ℝ) ^ k) ^ 2 ≤ 1 / ((k : ℝ) + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hrec : ((k : ℝ) + 1) * ((k + 1).centralBinom : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (k.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hcoef : ((k + 1).centralBinom : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (k.centralBinom : ℝ) / ((k : ℝ) + 1) := by
      apply (eq_div_iff (by positivity : (k : ℝ) + 1 ≠ 0)).mpr
      rw [mul_comm]
      exact hrec
    have hrate : ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2 ≤
        ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
      rw [div_pow]
      apply (div_le_iff₀ (by positivity)).mpr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [hk, sq_nonneg (k : ℝ)]
    rw [Nat.cast_succ, pow_succ (4 : ℝ), hcoef]
    have he : 2 * (2 * (k : ℝ) + 1) * (k.centralBinom : ℝ) / ((k : ℝ) + 1) /
        ((4 : ℝ) ^ k * 4) = (2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1)) *
          ((k.centralBinom : ℝ) / (4 : ℝ) ^ k) := by field_simp; ring
    rw [he, mul_pow]
    calc
      _ ≤ (((k : ℝ) + 1) / ((k : ℝ) + 2)) * (1 / ((k : ℝ) + 1)) := by gcongr
      _ = _ := by field_simp; ring

/-- A uniform square-root bound on the largest mass of a fair binomial law. -/
theorem middle_binomial_div_pow_le (n : ℕ) :
    (n.choose (n / 2) : ℝ) / (2 : ℝ) ^ n ≤ 4 / Real.sqrt ((n : ℝ) + 1) := by
  let k := (n + 1) / 2
  have hkn : n ≤ 2 * k := by dsimp [k]; omega
  have hkn' : 2 * k ≤ n + 1 := by dsimp [k]; omega
  have hc : (n.choose (n / 2) : ℝ) ≤ (k.centralBinom : ℝ) := by
    exact_mod_cast (((Nat.choose_mono (n / 2) hkn).trans (Nat.choose_le_centralBinom _ k)) :
      n.choose (n / 2) ≤ k.centralBinom)
  have hpow : (4 : ℝ) ^ k ≤ 2 * (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) hkn'
  have hs : (k.centralBinom : ℝ) / (4 : ℝ) ^ k ≤ 1 / Real.sqrt ((k : ℝ) + 1) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow (1 : ℝ), Real.sq_sqrt (by positivity), one_pow]
    exact centralBinom_sq_div_pow_le k
  have hscale : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt ((k : ℝ) + 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hn : n + 1 ≤ 4 * (k + 1) := by omega
    norm_num
    exact_mod_cast hn
  calc
    _ ≤ 2 * ((n.choose (n / 2) : ℝ) / (4 : ℝ) ^ k) := by
      have h := div_le_div_of_nonneg_left (Nat.cast_nonneg (n.choose (n / 2))) (by positivity) hpow
      calc
        _ = 2 * ((n.choose (n / 2) : ℝ) / (2 * (2 : ℝ) ^ n)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 2 * ((k.centralBinom : ℝ) / (4 : ℝ) ^ k) := by gcongr
    _ ≤ 2 * (1 / Real.sqrt ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = 4 / (2 * Real.sqrt ((k : ℝ) + 1)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hscale

/-- A square-root Littlewood–Offord bound for independent fair signs. -/
theorem signSum_smallBall_le_four_div_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (z r : ℝ) (ha : ∀ i, r < |a i|) :
    (uniformOn Set.univ).real {b : ι → Bool | |signSum a b - z| ≤ r} ≤
      4 / Real.sqrt ((Fintype.card ι : ℝ) + 1) :=
  (signSum_smallBall_le_middle_binomial a z r ha).trans (middle_binomial_div_pow_le _)

end BooleanThreshold
