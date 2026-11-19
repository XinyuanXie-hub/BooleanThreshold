module

public import BooleanThreshold.JSSConditionalSeparation
public import BooleanThreshold.JSSConditionalGrid

public section

open Filter
open scoped BigOperators Topology

namespace BooleanThreshold

private theorem roundedUnit_l2_bound {n N A : ℕ} (hN : 0 < N) {D c : ℝ}
    (hD₀ : 0 ≤ D) (hD : D ≤ Real.sqrt (n : ℝ) * (N : ℝ) / c)
    (hA : 2 * (1 / c) ^ 2 + 2 ≤ (A : ℝ) ^ 2)
    {a : Fin n → ℝ} (ha : ∑ i, a i ^ 2 = 1)
    {w : Fin n → ℤ} (hw : ∀ i, |(w i : ℝ) - D * a i| ≤ 1) :
    ∑ i, (w i : ℝ) ^ 2 ≤ ((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ) := by
  have hs (i : Fin n) : (w i : ℝ) ^ 2 ≤ 2 * D ^ 2 * (a i) ^ 2 + 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hw i)
    rw [sq_abs, one_pow] at h
    nlinarith only [h, sq_nonneg ((w i : ℝ) - 2 * D * a i)]
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD' : D ^ 2 ≤ (1 / c) ^ 2 * (N : ℝ) ^ 2 * (n : ℝ) := by
    refine (pow_le_pow_left₀ hD₀ hD 2).trans_eq ?_
    rw [div_pow, mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
    ring
  calc
    _ ≤ ∑ i, (2 * D ^ 2 * (a i) ^ 2 + 2) := Finset.sum_le_sum (fun i _ => hs i)
    _ = 2 * D ^ 2 + 2 * (n : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha]
      simp [mul_comm]
    _ ≤ (2 * (1 / c) ^ 2 + 2) * ((N : ℝ) ^ 2 * (n : ℝ)) := by
      have hp := (sq_le_sq₀ zero_le_one (by positivity : 0 ≤ (N : ℝ))).mpr hN₁
      rw [one_pow] at hp
      nlinarith only [hD', mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    _ ≤ (A : ℝ) ^ 2 * ((N : ℝ) ^ 2 * (n : ℝ)) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

/-- At each relevant lattice scale, rounded unstructured normals have two
separated coordinate groups that can be translated into opposite sign bands. -/
theorem roundedUnit_geometry_eventually {δ ρ : ℝ} (hδ : 0 < δ) (hd : δ < 1) (hρ : 0 < ρ) :
    ∃ c > (0 : ℝ), c = ρ / 64 ∧ ∃ A B : ℕ, 4 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {u T : ℝ} {N : ℕ}, 0 < u → u ≤ T → T ≤ 2 * u → 0 < N →
        c / (2 * u) ≤ (N : ℝ) → (N : ℝ) ≤ c / u →
      ∀ a : Fin n → ℝ, (∑ i, a i ^ 2) = 1 → a ∉ almostConstantUnitVectors n δ ρ →
      ∀ w : Fin n → ℤ, (∀ i, |(w i : ℝ) - Real.sqrt (n : ℝ) / (2 * T) * a i| ≤ 1) →
        (∑ i, (w i : ℝ) ^ 2 ≤ ((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ)) ∧
        ∃ I J : Finset (Fin n), (δ / 16) * (n : ℝ) ≤ I.card ∧
          (δ / 16) * (n : ℝ) ≤ J.card ∧ Disjoint I J ∧
          ∃ q : ℤ, |q| ≤ (B : ℤ) ∧
            (∀ i ∈ I, -(B : ℤ) * (N : ℤ) ≤ w i - q * (N : ℤ) ∧
              w i - q * (N : ℤ) ≤ -2 * (N : ℤ)) ∧
            ∀ j ∈ J, 2 * (N : ℤ) ≤ w j - q * (N : ℤ) ∧
              w j - q * (N : ℤ) ≤ (B : ℤ) * (N : ℤ) := by
  let c := ρ / 64
  have hc : 0 < c := by dsimp [c]; positivity
  let R := Real.sqrt (32 / δ)
  obtain ⟨A, hA⟩ := exists_nat_ge (Real.sqrt (2 * (1 / c) ^ 2 + 2))
  obtain ⟨B₀, hB₀⟩ := exists_nat_ge (R / c + 1)
  let B := 2 * B₀ + 7
  refine ⟨c, hc, rfl, A, B, by dsimp [B]; omega, ?_⟩
  filter_upwards [exists_bounded_separated_groups_eventually (ρ := ρ) hδ hd,
    eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  intro u T N hu hT hTu hN huN hNu a ha ha' w hw
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn₁
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn₀
  have hT₀ := hu.trans_le hT
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast hN
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let D := Real.sqrt (n : ℝ) / (2 * T)
  have hD₀ : 0 < D := by dsimp [D]; positivity
  have hscale : 1 / (2 * T) ≤ (N : ℝ) / c := by
    calc
      _ ≤ 1 / (2 * u) := one_div_le_one_div_of_le (by positivity) (by linarith only [hT])
      _ ≤ _ := by
        apply (le_div_iff₀ hc).mpr
        rw [div_mul_eq_mul_div, one_mul]
        exact huN
  have hD : D ≤ Real.sqrt (n : ℝ) * (N : ℝ) / c := by
    simpa only [D, mul_one_div, mul_div_assoc] using mul_le_mul_of_nonneg_left hscale hs.le
  refine ⟨roundedUnit_l2_bound hN hD₀.le hD ?_ ha hw, ?_⟩
  · rw [← Real.sq_sqrt (show 0 ≤ 2 * (1 / c) ^ 2 + 2 by positivity)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hA _
  obtain ⟨I, J, hI, hJ, hIJ, hcoord, hsep⟩ := hn a ha ha'
  have hcoordw (i : Fin n) (hi : i ∈ I ∪ J) : |(w i : ℝ)| ≤ (B₀ : ℝ) * (N : ℝ) := by
    have hpart : D * |a i| ≤ (R / c) * (N : ℝ) := by
      calc
        _ ≤ D * (R / Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_left (hcoord i hi) hD₀.le
        _ = R / (2 * T) := by dsimp [D]; field_simp
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_left hscale (show 0 ≤ R from Real.sqrt_nonneg _)
          rw [mul_one_div] at h
          exact h.trans_eq (by ring)
    calc
      _ = |(w i : ℝ) - D * a i + D * a i| := by rw [sub_add_cancel]
      _ ≤ |(w i : ℝ) - D * a i| + |D * a i| := abs_add_le _ _
      _ ≤ 1 + (R / c) * (N : ℝ) := by
        rw [abs_mul, abs_of_pos hD₀]
        exact add_le_add (hw i) hpart
      _ ≤ (R / c + 1) * (N : ℝ) := by nlinarith only [hN₁]
      _ ≤ _ := mul_le_mul_of_nonneg_right hB₀ hN₀.le
  have hgap (i : Fin n) (hi : i ∈ I) (j : Fin n) (hj : j ∈ J) :
      30 * (N : ℤ) ≤ w j - w i := by
    have hg := mul_lt_mul_of_pos_left (hsep i hi j hj) hD₀
    have hg' : D * (2 * (ρ / Real.sqrt (n : ℝ))) = ρ / T := by dsimp [D]; field_simp
    rw [hg'] at hg
    have hup : 32 * (N : ℝ) ≤ ρ / (2 * u) := by
      have h := mul_le_mul_of_nonneg_left hNu (by norm_num : (0 : ℝ) ≤ 32)
      refine h.trans_eq ?_
      dsimp [c]
      ring
    have hmid : ρ / (2 * u) ≤ ρ / T := div_le_div_of_nonneg_left hρ.le hT₀ hTu
    have hiw := (abs_le.mp (hw i)).2
    have hjw := (abs_le.mp (hw j)).1
    have hlast : 30 * (N : ℝ) ≤ (w j : ℝ) - (w i : ℝ) := by
      linarith only [hup, hmid, hg, hiw, hjw, hN₁]
    exact_mod_cast hlast
  have hI₀ : I.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast (show (0 : ℝ) < I.card from (by positivity : 0 < (δ / 16) * (n : ℝ)).trans_le hI)
  let M := (I.image w).max' (hI₀.image w)
  obtain ⟨i, hi, hwi⟩ := Finset.mem_image.mp ((I.image w).max'_mem (hI₀.image w))
  have hwi' : w i = M := hwi
  let q := M / (N : ℤ) + 3
  let d := q * (N : ℤ)
  have hquot := integer_mem_gridInterval hN M
  simp only [integerGridInterval, Finset.mem_Ico] at hquot
  have hdlo : M + 2 * (N : ℤ) ≤ d := by
    dsimp [d, q]
    rw [add_mul]
    omega
  have hdhi : d ≤ M + 3 * (N : ℤ) := by
    dsimp [d, q]
    rw [add_mul]
    omega
  have hdabs : |d| ≤ ((B₀ : ℤ) + 3) * (N : ℤ) := by
    have hm : |M| ≤ (B₀ : ℤ) * (N : ℤ) := by
      rw [← hwi']
      exact_mod_cast hcoordw i (Finset.mem_union_left _ hi)
    rw [abs_le] at hm ⊢
    have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
    rw [add_mul]
    omega
  have hq : |q| ≤ (B : ℤ) := by
    have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
    have hh : |q| * (N : ℤ) ≤ ((B₀ : ℤ) + 3) * (N : ℤ) := by
      simpa only [d, abs_mul, abs_of_pos hNpos] using hdabs
    refine (le_of_mul_le_mul_right hh hNpos).trans ?_
    dsimp [B]
    omega
  have hband (j : Fin n) (hj : j ∈ I ∪ J) : |w j - d| ≤ (B : ℤ) * (N : ℤ) := by
    have hh : |w j| ≤ (B₀ : ℤ) * (N : ℤ) := by exact_mod_cast hcoordw j hj
    calc
      _ ≤ |w j| + |d| := abs_sub _ _
      _ ≤ (B₀ : ℤ) * (N : ℤ) + ((B₀ : ℤ) + 3) * (N : ℤ) := add_le_add hh hdabs
      _ ≤ _ := by
        dsimp [B]
        have hNpos : (0 : ℤ) ≤ N := by exact_mod_cast hN.le
        nlinarith only [hNpos]
  refine ⟨I, J, hI, hJ, hIJ, q, hq, ?_, ?_⟩
  · intro j hj
    refine ⟨(abs_le.mp (hband j (Finset.mem_union_left _ hj))).1, ?_⟩
    have hm : w j ≤ M := Finset.le_max' _ _ (Finset.mem_image_of_mem _ hj)
    change w j - d ≤ _
    omega
  · intro j hj
    refine ⟨?_, (abs_le.mp (hband j (Finset.mem_union_right _ hj))).2⟩
    have hh := hgap i hi j hj
    rw [hwi'] at hh
    change _ ≤ w j - d
    have hNpos : (0 : ℤ) ≤ N := by exact_mod_cast hN.le
    omega

end BooleanThreshold
