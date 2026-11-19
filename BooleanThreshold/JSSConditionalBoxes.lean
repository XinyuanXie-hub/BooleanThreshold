module

public import BooleanThreshold.JSSConditionalBands

@[expose] public section

open Filter
open scoped BigOperators Classical Topology

namespace BooleanThreshold

/-- Integer product intervals with linearly many coordinates in each of two
fixed, opposite sign bands. These are the opposite-sign admissible boxes
for the fixed-weight sign model. -/
def oppositeBandBox (n N B : ℕ) (α : ℝ) (P : Fin n → Finset ℤ) : Prop :=
  (∀ i, (∃ a b : ℤ, P i = Finset.Ico a b) ∧
    2 * N + 1 ≤ (P i).card ∧ (P i).card ≤ (B + 1) * N ∧
    ∀ x ∈ P i, |x| ≤ (n : ℤ) * (N : ℤ)) ∧
  ∃ I J : Finset (Fin n), α * (n : ℝ) ≤ I.card ∧ α * (n : ℝ) ≤ J.card ∧ Disjoint I J ∧
    (∀ i ∈ I, ∀ x ∈ P i, -(B : ℤ) * (N : ℤ) ≤ x ∧ x ≤ -2 * (N : ℤ)) ∧
    ∀ j ∈ J, ∀ x ∈ P j, 2 * (N : ℤ) ≤ x ∧ x ≤ (B : ℤ) * (N : ℤ)

private theorem oppositeBandBox_dimensions_eventually (A B : ℕ) :
    ∀ᶠ n : ℕ in atTop, (A : ℝ) * Real.sqrt (n : ℝ) + (B : ℝ) + 3 ≤ n := by
  refine (eventually_ge_atTop (max (4 * A ^ 2) (2 * (B + 3)))).mono ?_
  intro n hn
  have hA : (4 : ℝ) * (A : ℝ) ^ 2 ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hB : (2 : ℝ) * ((B : ℝ) + 3) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hs : 2 * (A : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
    nlinarith only [hA]
  have hh := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (n : ℝ))
  rw [← pow_two (Real.sqrt (n : ℝ)), Real.sq_sqrt (Nat.cast_nonneg n)] at hh
  nlinarith only [hh, hB]

private theorem abs_coordinate_le_of_sum_sq {n N A : ℕ} (w : Fin n → ℤ)
    (hw : ∑ i, (w i : ℝ) ^ 2 ≤ ((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ)) (i : Fin n) :
    |(w i : ℝ)| ≤ ((A : ℝ) * (N : ℝ)) * Real.sqrt (n : ℝ) := by
  have hs := (Finset.single_le_sum (f := fun i => (w i : ℝ) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)).trans hw
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using hs

/-- A uniform family of translated opposite-sign boxes covers all the
rounded points with the specified geometry. -/
theorem oppositeBandBox_cover {A B : ℕ} (hB : 4 ≤ B) (α : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, 0 < N →
      ∃ D : Finset (ℤ × (Fin n → Finset ℤ)),
        D.card ≤ (2 * B + 1) * (12 * 2 ^ (A + 1)) ^ n ∧
        (∀ p ∈ D, oppositeBandBox n N B α p.2) ∧
        ∀ w : Fin n → ℤ, (∑ i, (w i : ℝ) ^ 2 ≤ ((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ)) →
          (∃ I J : Finset (Fin n), α * (n : ℝ) ≤ I.card ∧ α * (n : ℝ) ≤ J.card ∧ Disjoint I J ∧
            ∃ q : ℤ, |q| ≤ (B : ℤ) ∧
              (∀ i ∈ I, -(B : ℤ) * (N : ℤ) ≤ w i - q * (N : ℤ) ∧ w i - q * (N : ℤ) ≤ -2 * (N : ℤ)) ∧
              ∀ j ∈ J, 2 * (N : ℤ) ≤ w j - q * (N : ℤ) ∧ w j - q * (N : ℤ) ≤ (B : ℤ) * (N : ℤ)) →
          ∃ p ∈ D, ∀ i, w i - p.1 ∈ p.2 i := by
  refine (oppositeBandBox_dimensions_eventually A B).mono ?_
  intro n hdim N hN
  let N₃ := 3 * N
  have hN₃ : 0 < N₃ := by dsimp [N₃]; omega
  obtain ⟨G, hG, hcover⟩ := exists_integer_grid_cover n N₃ A hN₃
  let H := Finset.Icc (-(B : ℤ)) (B : ℤ)
  let all := ((Finset.univ : Finset (Fin n → Fin 3)).product G).product H
  let low := Finset.Ico (-(B : ℤ) * (N : ℤ)) (-2 * (N : ℤ) + 1)
  let high := Finset.Ico (2 * (N : ℤ)) ((B : ℤ) * (N : ℤ) + 1)
  let box (x : (Fin n → Fin 3) × (Fin n → ℤ) × ℤ) : Fin n → Finset ℤ := fun i =>
    if x.1 i = 1 then low else if x.1 i = 2 then high else
      Finset.Ico (x.2.1 i * (N₃ : ℤ) - x.2.2 * (N : ℤ))
        (x.2.1 i * (N₃ : ℤ) - x.2.2 * (N : ℤ) + (N₃ : ℤ))
  let F (x : ((Fin n → Fin 3) × (Fin n → ℤ)) × ℤ) : ℤ × (Fin n → Finset ℤ) :=
    (x.2 * (N : ℤ), box (x.1.1, x.1.2, x.2))
  let D := (all.image F).filter (fun p => oppositeBandBox n N B α p.2)
  have hH : H.card = 2 * B + 1 := by
    simp only [H, Int.card_Icc]
    have he : (B : ℤ) + 1 - -(B : ℤ) = (↑(2 * B + 1) : ℤ) := by push_cast; ring
    rw [he, Int.toNat_natCast]
  refine ⟨D, ?_, fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  · refine ((Finset.card_filter_le _ _).trans Finset.card_image_le).trans ?_
    change all.card ≤ _
    rw [show all.card = 3 ^ n * G.card * (2 * B + 1) by simp [all, hH]]
    calc
      _ ≤ (3 ^ n * (4 * 2 ^ (A + 1)) ^ n) * (2 * B + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hG)
      _ = _ := by
        rw [← mul_pow, show 3 * (4 * 2 ^ (A + 1)) = 12 * 2 ^ (A + 1) by ring, mul_comm]
  rintro w hw ⟨I, J, hI, hJ, hIJ, q, hq, hlo, hhi⟩
  have hw₃ : ∑ i, (w i : ℝ) ^ 2 ≤ ((A : ℝ) * (N₃ : ℝ)) ^ 2 * (n : ℝ) := by
    refine hw.trans ?_
    have hNle : N ≤ N₃ := by dsimp [N₃]; omega
    gcongr
  obtain ⟨g, hg, hgw⟩ := hcover w hw₃
  let t (i : Fin n) : Fin 3 := if i ∈ I then 1 else if i ∈ J then 2 else 0
  let x := ((t, g), q)
  let d := q * (N : ℤ)
  let P := box (t, g, q)
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hBint : (4 : ℤ) ≤ B := by exact_mod_cast hB
  have hwidth : (2 : ℤ) * (N : ℤ) + 1 ≤ ((B : ℤ) - 2) * (N : ℤ) + 1 := by
    nlinarith only [mul_nonneg (show (0 : ℤ) ≤ (B : ℤ) - 4 by omega) hNpos.le]
  have hwupper : ((B : ℤ) - 2) * (N : ℤ) + 1 ≤ ((B : ℤ) + 1) * (N : ℤ) := by
    nlinarith only [hNpos, show (1 : ℤ) ≤ N by omega]
  have hlcard : (low.card : ℤ) = ((B : ℤ) - 2) * (N : ℤ) + 1 := by
    dsimp [low]
    have hl : -(B : ℤ) * (N : ℤ) ≤ -2 * (N : ℤ) + 1 := by nlinarith only [hwidth, hNpos]
    rw [Int.card_Ico_of_le _ _ hl]
    ring
  have hhcard : (high.card : ℤ) = ((B : ℤ) - 2) * (N : ℤ) + 1 := by
    dsimp [high]
    have hl : 2 * (N : ℤ) ≤ (B : ℤ) * (N : ℤ) + 1 := by nlinarith only [hwidth, hNpos]
    rw [Int.card_Ico_of_le _ _ hl]
    ring
  have hBdim : (B : ℤ) ≤ n := by
    have hb : (B : ℝ) ≤ n := by
      linarith only [hdim, show 0 ≤ (A : ℝ) * Real.sqrt (n : ℝ) by positivity]
    exact_mod_cast hb
  have hshift : |d| ≤ (B : ℤ) * (N : ℤ) := by
    dsimp [d]
    rw [abs_mul, abs_of_pos hNpos]
    exact mul_le_mul_of_nonneg_right hq hNpos.le
  have hI' (i : Fin n) (hi : i ∈ I) : P i = low := by simp [P, box, t, hi]
  have hJ' (i : Fin n) (hi : i ∈ J) : P i = high := by
    have hnot : i ∉ I := fun h => Finset.disjoint_left.mp hIJ h hi
    simp [P, box, t, hnot, hi]
  have hrest (i : Fin n) (hi : i ∉ I) (hj : i ∉ J) : P i =
      Finset.Ico (g i * (N₃ : ℤ) - d) (g i * (N₃ : ℤ) - d + (N₃ : ℤ)) := by
    simp [P, box, t, d, hi, hj]
  have hlo' {z : ℤ} (hz : z ∈ low) : -(B : ℤ) * (N : ℤ) ≤ z ∧ z ≤ -2 * (N : ℤ) := by
    simp only [low, Finset.mem_Ico] at hz
    omega
  have hhi' {z : ℤ} (hz : z ∈ high) : 2 * (N : ℤ) ≤ z ∧ z ≤ (B : ℤ) * (N : ℤ) := by
    simp only [high, Finset.mem_Ico] at hz
    omega
  have hcert : oppositeBandBox n N B α P := by
    refine ⟨fun i => ?_, I, J, hI, hJ, hIJ, fun i hi z hz => hlo' (hI' i hi ▸ hz),
      fun j hj z hz => hhi' (hJ' j hj ▸ hz)⟩
    by_cases hi : i ∈ I
    · rw [hI' i hi]
      refine ⟨⟨_, _, rfl⟩, ?_, ?_, fun z hz => ?_⟩
      · exact_mod_cast hwidth.trans_eq hlcard.symm
      · exact_mod_cast hlcard.trans_le hwupper
      · have h := hlo' hz
        have hs := mul_le_mul_of_nonneg_right hBdim hNpos.le
        rw [neg_mul] at h
        apply abs_le.mpr
        omega
    by_cases hj : i ∈ J
    · rw [hJ' i hj]
      refine ⟨⟨_, _, rfl⟩, ?_, ?_, fun z hz => ?_⟩
      · exact_mod_cast hwidth.trans_eq hhcard.symm
      · exact_mod_cast hhcard.trans_le hwupper
      · have h := hhi' hz
        have hs := mul_le_mul_of_nonneg_right hBdim hNpos.le
        apply abs_le.mpr
        omega
    rw [hrest i hi hj]
    have hcard : (Finset.Ico (g i * (N₃ : ℤ) - d) (g i * (N₃ : ℤ) - d + (N₃ : ℤ))).card = N₃ := by
      rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]
    refine ⟨⟨_, _, rfl⟩, by rw [hcard]; dsimp [N₃]; omega, ?_, fun z hz => ?_⟩
    · rw [hcard]
      dsimp [N₃]
      exact Nat.mul_le_mul_right _ (by omega)
    have hwg := hgw i
    simp only [integerGridInterval, Finset.mem_Ico] at hwg
    rw [Finset.mem_Ico] at hz
    have hnear : |z - (w i - d)| ≤ (N₃ : ℤ) := abs_le.mpr (by omega)
    have habs : |z| ≤ (N₃ : ℤ) + |w i| + |d| := by
      calc
        _ = |z - (w i - d) + (w i - d)| := by rw [sub_add_cancel]
        _ ≤ |z - (w i - d)| + |w i - d| := abs_add_le _ _
        _ ≤ (N₃ : ℤ) + (|w i| + |d|) := add_le_add hnear (abs_sub _ _)
        _ = _ := by ring
    have hz' : |(z : ℝ)| ≤ (N₃ : ℝ) + |(w i : ℝ)| + |(d : ℝ)| := by exact_mod_cast habs
    have hshift' : |(d : ℝ)| ≤ (B : ℝ) * (N : ℝ) := by exact_mod_cast hshift
    have hh := abs_coordinate_le_of_sum_sq w hw i
    have hbound : |(z : ℝ)| ≤ (n : ℝ) * (N : ℝ) := by
      have hdim' := mul_le_mul_of_nonneg_right hdim (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      dsimp [N₃] at hz'
      push_cast at hz'
      nlinarith only [hz', hshift', hh, hdim']
    exact_mod_cast hbound
  have hall : x ∈ all := Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hg⟩, Finset.mem_Icc.mpr (abs_le.mp hq)⟩
  refine ⟨F x, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hall, rfl⟩, hcert⟩, fun i => ?_⟩
  change w i - d ∈ P i
  by_cases hi : i ∈ I
  · rw [hI' i hi]
    exact Finset.mem_Ico.mpr ⟨(hlo i hi).1, by have h := (hlo i hi).2; omega⟩
  by_cases hj : i ∈ J
  · rw [hJ' i hj]
    exact Finset.mem_Ico.mpr ⟨(hhi i hj).1, by have h := (hhi i hj).2; omega⟩
  rw [hrest i hi hj]
  have hwg := hgw i
  simp only [integerGridInterval, Finset.mem_Ico] at hwg ⊢
  omega

end BooleanThreshold
