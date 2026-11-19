module

public import Mathlib.Combinatorics.Additive.CauchyDavenport
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Field.GeomSum

public section

open Finset
open scoped Pointwise BigOperators

namespace BooleanThreshold

private theorem pointwise_nsmul_nonempty {P : ℕ} (A : Finset (ZMod P)) (hA : A.Nonempty) :
    ∀ k : ℕ, (k • A).Nonempty := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul]; exact ih.add hA

theorem card_pointwise_nsmul_ge {P : ℕ} [NeZero P] (hP : P.Prime)
    (A : Finset (ZMod P)) (hA : A.Nonempty) (k : ℕ) :
    min P (k * (A.card - 1) + 1) ≤ (k • A).card := by
  have hApos := hA.card_pos
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul]
    have hCD := ZMod.cauchy_davenport hP (pointwise_nsmul_nonempty A hA k) hA
    by_cases hk : P ≤ k * (A.card - 1) + 1
    · rw [min_eq_left hk] at ih
      have hsum : P ≤ (k • A).card + A.card - 1 := by omega
      exact (min_le_left _ _).trans (by rwa [min_eq_left hsum] at hCD)
    · rw [min_eq_right (le_of_not_ge hk)] at ih
      refine (min_le_min_left _ ?_).trans hCD
      rw [Nat.succ_mul]
      omega

theorem radius_mem_pointwise_nsmul_les {P : ℕ} (r : ZMod P → ℝ)
    (hr₀ : r 0 = 0) (hadd : ∀ x y, r (x + y) ≤ r x + r y)
    (A : Finset (ZMod P)) (s : ℝ) (hA : ∀ x ∈ A, r x ≤ s) (k : ℕ) :
    ∀ x ∈ k • A, r x ≤ (k : ℝ) * s := by
  induction k with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    simp [hx0, hr₀]
  | succ k ih =>
    intro x hx
    rw [succ_nsmul] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_add.mp hx
    calc
      r (y + z) ≤ r y + r z := hadd y z
      _ ≤ (k : ℝ) * s + s := add_le_add (ih y hy) (hA z hz)
      _ = _ := by push_cast; ring

/-- If dilating a radius has not exhausted the group, its sublevel set has
grown at least as much as an iterated sumset. -/
theorem sublevel_card_le_dilated {P : ℕ} [NeZero P] (hP : P.Prime)
    (r : ZMod P → ℝ) (hr₀ : r 0 = 0) (hadd : ∀ x y, r (x + y) ≤ r x + r y)
    (s : ℝ) (hs : 0 ≤ s) (k : ℕ) (hk : 0 < k)
    (hproper : ∃ x, (k : ℝ) * s < r x) :
    ((univ.filter fun x => r x ≤ s).card : ℝ) / P ≤
      ((univ.filter fun x => r x ≤ (k : ℝ) * s).card : ℝ) / P / k + 1 / P := by
  let A := (univ : Finset (ZMod P)).filter (fun x => r x ≤ s)
  let B := (univ : Finset (ZMod P)).filter (fun x => r x ≤ (k : ℝ) * s)
  have hA : A.Nonempty := ⟨0, by simp [A, hr₀, hs]⟩
  have hAB : k • A ⊆ B :=
    fun x hx => mem_filter.mpr ⟨mem_univ x,
      radius_mem_pointwise_nsmul_les r hr₀ hadd A s (fun z hz => (mem_filter.mp hz).2) k x hx⟩
  have hB : B.card < P := by
    obtain ⟨z, hz⟩ := hproper
    have hss : B ⊂ univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ B, fun he =>
        hz.not_ge ((mem_filter.mp (he ▸ mem_univ z : z ∈ B)).2)⟩
    simpa [ZMod.card] using card_lt_card hss
  have hc := (card_pointwise_nsmul_ge hP A hA k).trans (card_le_card hAB)
  have hc' : k * A.card ≤ B.card + k := by
    have h : k * (A.card - 1) + 1 ≤ B.card := by omega
    have hA' : A.card - 1 + 1 = A.card := Nat.sub_add_cancel hA.card_pos
    rw [← hA', Nat.mul_add, Nat.mul_one]
    omega
  have hcR : (k : ℝ) * (A.card : ℝ) ≤ (B.card : ℝ) + k := by exact_mod_cast hc'
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hPR : 0 < (P : ℝ) := by exact_mod_cast hP.pos
  change (A.card : ℝ) / P ≤ (B.card : ℝ) / P / k + 1 / P
  calc
    _ ≤ (((B.card : ℝ) + k) / k) / P :=
      div_le_div_of_nonneg_right
        ((le_div_iff₀ hkR).mpr (by simpa [mul_comm] using hcR)) hPR.le
    _ = _ := by
      field_simp [hPR.ne', hkR.ne']

/-- The normalized size of a sublevel set of a function on a prime cycle. -/
@[expose] noncomputable def sublevelFraction {P : ℕ} [NeZero P]
    (f : ZMod P → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ((univ.filter fun t => f t ≤ x).card : ℝ) / P

private theorem mean_exp_le_layers {P : ℕ} [NeZero P]
    (hP : 0 < P) (f : ZMod P → ℝ) (hf : ∀ t, 0 ≤ f t) :
    ∃ L : ℕ, (∑ t, Real.exp (-f t)) / (P : ℝ) ≤
      ∑ j ∈ range L, Real.exp (-(j : ℝ)) * sublevelFraction f ((j : ℝ) + 1) := by
  classical
  let L := ⌊∑ t, f t⌋₊ + 1
  refine ⟨L, ?_⟩
  have hPR : 0 < (P : ℝ) := by exact_mod_cast hP
  have hs (t : ZMod P) : Real.exp (-f t) ≤
      ∑ j ∈ range L, if f t ≤ (j : ℝ) + 1 then Real.exp (-j) else 0 := by
    let j := ⌊f t⌋₊
    have hj : j ∈ range L := by
      refine mem_range.mpr (Nat.lt_succ_of_le ?_)
      exact Nat.floor_mono (single_le_sum (fun u _ => hf u) (mem_univ t))
    have hjLo : (j : ℝ) ≤ f t := Nat.floor_le (hf t)
    have hjHi : f t ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    calc
      _ ≤ Real.exp (-(j : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg hjLo)
      _ = (if f t ≤ (j : ℝ) + 1 then Real.exp (-j) else 0) := (ite_eq_left hjHi).symm
      _ ≤ _ := single_le_sum
        (f := fun i : ℕ => if f t ≤ (i : ℝ) + 1 then Real.exp (-i) else 0)
        (fun i _ => by split <;> positivity) hj
  calc
    _ ≤ (∑ t, ∑ j ∈ range L, if f t ≤ (j : ℝ) + 1 then Real.exp (-j) else 0) / P :=
      div_le_div_of_nonneg_right (sum_le_sum fun t _ => hs t) hPR.le
    _ = _ := by
      rw [sum_comm, div_eq_mul_inv, sum_mul]
      apply sum_congr rfl
      intro j _
      rw [← sum_filter, sum_const, nsmul_eq_mul, sublevelFraction]
      ring

private theorem geometric_sum_le_inverse {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) (L : ℕ) :
    ∑ j ∈ range L, r ^ j ≤ (1 - r)⁻¹ := by
  rw [geom_sum_eq hr₁.ne, inv_eq_one_div]
  calc
    _ = (1 - r ^ L) / (1 - r) := by rw [← neg_div_neg_eq]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg hr _)) (by linarith)

/-- A finite layer-sum version of the exponential estimate in the Halász argument. -/
theorem mean_exp_bound_from_levels {P : ℕ} [NeZero P]
    (hP : 0 < P) (f : ZMod P → ℝ) (hf : ∀ t, 0 ≤ f t)
    (β Q : ℝ) (hβ : 0 ≤ β) (hQ : 0 ≤ Q) (k : ℕ) (hk : 0 < k)
    (hβk : β * (k : ℝ) ^ 2 ≤ 1 / 2) (S : ℕ)
    (hMarkov : ∀ x : ℝ, sublevelFraction f x ≤ Real.exp (β * x) * Q)
    (hGrow : ∀ j : ℕ, j < S → sublevelFraction f ((j : ℝ) + 1) ≤
      sublevelFraction f ((k : ℝ) ^ 2 * ((j : ℝ) + 1)) / k + 1 / P) :
    (∑ t, Real.exp (-f t)) / (P : ℝ) ≤
      (Real.exp (1 / 2) * (1 / (k : ℝ) + Real.exp (-(S : ℝ) / 4)) * Q + 1 / P) /
        (1 - Real.exp (-(1 / 4 : ℝ))) := by
  let r := Real.exp (-(1 / 4 : ℝ))
  let C := Real.exp (1 / 2) * (1 / (k : ℝ) + Real.exp (-(S : ℝ) / 4)) * Q + 1 / P
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hP' : 0 < (P : ℝ) := by exact_mod_cast hP
  have hβhalf : β ≤ 1 / 2 := by
    have h' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have hsq : 1 ≤ (k : ℝ) ^ 2 := by nlinarith only [h', sq_nonneg ((k : ℝ) - 1)]
    exact (le_mul_of_one_le_right hβ hsq).trans hβk
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (j : ℕ) :
      Real.exp (-(j : ℝ)) * sublevelFraction f ((j : ℝ) + 1) ≤ C * r ^ j := by
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    have hrPow : r ^ j = Real.exp (-(j : ℝ) / 4) := by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hjexp : Real.exp (-(j : ℝ)) ≤ r ^ j := by
      rw [hrPow]
      exact Real.exp_le_exp.mpr (by linarith)
    by_cases h : j < S
    · have hg := (hGrow j h).trans (add_le_add_left
        (div_le_div_of_nonneg_right (hMarkov _) hkR.le) _)
      have he : Real.exp (-(j : ℝ)) * Real.exp (β * ((k : ℝ) ^ 2 * ((j : ℝ) + 1))) ≤
          Real.exp (1 / 2) * r ^ j := by
        rw [hrPow, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hβk (show 0 ≤ (j : ℝ) + 1 by positivity)
        rw [mul_assoc] at hm
        linarith
      calc
        _ ≤ Real.exp (-(j : ℝ)) *
            (Real.exp (β * ((k : ℝ) ^ 2 * ((j : ℝ) + 1))) * Q / k + 1 / P) :=
          mul_le_mul_of_nonneg_left hg (Real.exp_nonneg _)
        _ = (Real.exp (-(j : ℝ)) * Real.exp (β * ((k : ℝ) ^ 2 * ((j : ℝ) + 1)))) * (Q / k) +
            Real.exp (-(j : ℝ)) * (1 / P) := by ring
        _ ≤ (Real.exp (1 / 2) * r ^ j) * (Q / k) + r ^ j * (1 / P) :=
          add_le_add (mul_le_mul_of_nonneg_right he (by positivity))
            (mul_le_mul_of_nonneg_right hjexp (by positivity))
        _ ≤ (Real.exp (1 / 2) * (1 / (k : ℝ)) * Q + 1 / P) * r ^ j := by
          ring_nf
          exact le_rfl
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
          dsimp [C]
          gcongr
          exact le_add_of_nonneg_right (Real.exp_pos _).le
    · have hSj : (S : ℝ) ≤ j := by exact_mod_cast le_of_not_gt h
      have he : Real.exp (-(j : ℝ)) * Real.exp (β * ((j : ℝ) + 1)) ≤
          Real.exp (1 / 2) * Real.exp (-(S : ℝ) / 4) * r ^ j := by
        rw [hrPow, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hβhalf (show 0 ≤ (j : ℝ) + 1 by positivity)
        linarith
      calc
        _ ≤ Real.exp (-(j : ℝ)) * (Real.exp (β * ((j : ℝ) + 1)) * Q) :=
          mul_le_mul_of_nonneg_left (hMarkov _) (Real.exp_nonneg _)
        _ = (Real.exp (-(j : ℝ)) * Real.exp (β * ((j : ℝ) + 1))) * Q := by ring
        _ ≤ (Real.exp (1 / 2) * Real.exp (-(S : ℝ) / 4) * r ^ j) * Q :=
          mul_le_mul_of_nonneg_right he hQ
        _ = (Real.exp (1 / 2) * Real.exp (-(S : ℝ) / 4) * Q) * r ^ j := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
          dsimp [C]
          have he' : Real.exp (-(S : ℝ) / 4) ≤ 1 / (k : ℝ) + Real.exp (-(S : ℝ) / 4) :=
            le_add_of_nonneg_left (by positivity)
          exact (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he' (Real.exp_nonneg _)) hQ).trans
              (le_add_of_nonneg_right (by positivity))
  obtain ⟨L, hL⟩ := mean_exp_le_layers hP f hf
  calc
    _ ≤ _ := hL
    _ ≤ ∑ j ∈ range L, C * r ^ j := sum_le_sum fun j _ => hpoint j
    _ = C * ∑ j ∈ range L, r ^ j := (mul_sum ..).symm
    _ ≤ C * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left (geometric_sum_le_inverse hr.le hr₁ _) hC
    _ = _ := by rw [div_eq_mul_inv]

end BooleanThreshold
