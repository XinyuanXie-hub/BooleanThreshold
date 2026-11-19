module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace BooleanThreshold

/-- A block of `N` consecutive integers in the grid with spacing `N`. -/
def integerGridInterval (N : ℕ) (q : ℤ) : Finset ℤ :=
  Finset.Ico (q * (N : ℤ)) (q * (N : ℤ) + (N : ℤ))

@[simp] theorem integerGridInterval_card (N : ℕ) (q : ℤ) :
    (integerGridInterval N q).card = N := by
  rw [integerGridInterval, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]

theorem integer_mem_gridInterval {N : ℕ} (hN : 0 < N) (z : ℤ) :
    z ∈ integerGridInterval N (z / (N : ℤ)) := by
  rw [integerGridInterval, Finset.mem_Ico, ← Int.ediv_eq_iff_of_pos (by exact_mod_cast hN)]

private theorem natAbs_div_mul_le {N : ℕ} (hN : 0 < N) (z : ℤ) :
    (z / (N : ℤ)).natAbs * N ≤ z.natAbs + N := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have heq : z / (N : ℤ) * N = z - z % N := by
    have h := Int.ediv_mul_add_emod z (N : ℤ)
    omega
  have habs : (z / (N : ℤ)).natAbs * N = (z - z % N).natAbs := by
    rw [← heq, Int.natAbs_mul, Int.natAbs_natCast]
  rw [habs]
  refine (Int.natAbs_sub_le _ _).trans (Nat.add_le_add_left ?_ _)
  have hrem := Int.emod_lt_of_pos z hN'
  have hrem0 := Int.emod_nonneg z hN'.ne'
  rw [← Int.ofNat_le, Int.natAbs_of_nonneg hrem0]
  exact hrem.le

private theorem natAbs_sum_of_l2 {n N A : ℕ} (z : Fin n → ℤ)
    (hz : (∑ i, (z i : ℝ) ^ 2) ≤ ((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ)) :
    (∑ i, (z i).natAbs) ≤ A * N * n := by
  let a (i : Fin n) := ((z i).natAbs : ℝ)
  have hs (i : Fin n) : a i ^ 2 = (z i : ℝ) ^ 2 := by
    have hi : (((z i).natAbs : ℤ) ^ 2) = (z i) ^ 2 := by simp [pow_two]
    simpa only [Int.cast_pow, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi
  have h := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n)))
    (f := a) (fun _ _ => by dsimp [a]; positivity) 1
  simp only [Nat.reduceAdd, Finset.card_univ, Fintype.card_fin, pow_one, hs] at h
  have hsq : (∑ i, a i) ^ 2 ≤ ((A : ℝ) * (N : ℝ) * (n : ℝ)) ^ 2 := by
    calc
      _ ≤ (n : ℝ) * ∑ i, (z i : ℝ) ^ 2 := h
      _ ≤ (n : ℝ) * (((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      _ = _ := by ring
  have hle := (sq_le_sq₀ (by dsimp [a]; positivity) (by positivity)).1 hsq
  exact_mod_cast (by simpa only [a] using hle :
    (∑ i, ((z i).natAbs : ℝ)) ≤ (A : ℝ) * (N : ℝ) * (n : ℝ))

private theorem grid_quotient_abs_sum {n N A : ℕ} (hN : 0 < N) (z : Fin n → ℤ)
    (hz : (∑ i, (z i : ℝ) ^ 2) ≤ ((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ)) :
    (∑ i, (z i / (N : ℤ)).natAbs) ≤ (A + 1) * n := by
  apply Nat.le_of_mul_le_mul_right _ hN
  calc
    _ = ∑ i, (z i / (N : ℤ)).natAbs * N := Finset.sum_mul _ _ _
    _ ≤ ∑ i, ((z i).natAbs + N) := Finset.sum_le_sum fun i _ => natAbs_div_mul_le hN (z i)
    _ = (∑ i, (z i).natAbs) + n * N := by simp [Finset.sum_add_distrib]
    _ ≤ A * N * n + n * N := Nat.add_le_add_right (natAbs_sum_of_l2 z hz) _
    _ = _ := by ring

private theorem one_coordinate_weight_sum_le (L : ℕ) :
    (∑ z ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), (1 / 2 : ℝ) ^ z.natAbs) ≤ 4 := by
  classical
  let I := Finset.Icc (-(L : ℤ)) (L : ℤ)
  let w (k : ℕ) := (1 / 2 : ℝ) ^ k
  have hmap (z : ℤ) (hz : z ∈ I) : z.natAbs ∈ Finset.range (L + 1) := by
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    have hb : |z| ≤ (L : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hz)
    simpa only [Int.abs_eq_natAbs, Int.ofNat_le] using hb
  have hcard (k : ℕ) : (I.filter (fun z => z.natAbs = k)).card ≤ 2 := by
    refine (Finset.card_le_card (t := {(k : ℤ), -(k : ℤ)}) ?_).trans ?_
    · intro z hz
      have hk := (Finset.mem_filter.mp hz).2
      have hk' : z.natAbs = (k : ℤ).natAbs := by simpa using hk
      exact Finset.mem_insert.mpr
        ((Int.natAbs_eq_natAbs_iff.mp hk').imp_right Finset.mem_singleton.mpr)
    · exact (Finset.card_insert_le _ _).trans (by simp)
  have hgeom (m : ℕ) : (∑ k ∈ Finset.range m, w k) + 2 * w m = 2 := by
    induction m with
    | zero => simp [w]
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hs : w (m + 1) = w m / 2 := by
        dsimp [w]
        rw [pow_succ]
        ring
      rw [hs]
      linarith only [ih]
  have hs : (∑ k ∈ Finset.range (L + 1), w k) ≤ 2 := by
    linarith [hgeom (L + 1), show 0 ≤ w (L + 1) by dsimp [w]; positivity]
  calc
    _ = ∑ k ∈ Finset.range (L + 1), ∑ z ∈ I with z.natAbs = k, w k :=
      (Finset.sum_fiberwise_of_maps_to' hmap w).symm
    _ ≤ ∑ k ∈ Finset.range (L + 1), 2 * w k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard k) (by dsimp [w]; positivity)
    _ ≤ _ := by rw [← Finset.mul_sum]; linarith only [hs]

private theorem grid_cutoff_card_le (n A : ℕ) :
    let L := (A + 1) * n
    let grid := (Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
      (fun q => ∑ i, (q i).natAbs ≤ L)
    grid.card ≤ (4 * 2 ^ (A + 1)) ^ n := by
  classical
  dsimp only
  let L := (A + 1) * n
  let I := Finset.Icc (-(L : ℤ)) (L : ℤ)
  let all := Fintype.piFinset (fun _ : Fin n => I)
  let grid := all.filter (fun q => ∑ i, (q i).natAbs ≤ L)
  let w (z : ℤ) := (1 / 2 : ℝ) ^ z.natAbs
  have hw (q : Fin n → ℤ) (hq : q ∈ grid) : (1 / 2 : ℝ) ^ L ≤ ∏ i, w (q i) := by
    dsimp [w]
    rw [Finset.prod_pow_eq_pow_sum]
    simp only [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Finset.mem_filter.mp hq).2)
  have hsum : (grid.card : ℝ) * (1 / 2) ^ L ≤ (4 : ℝ) ^ n := by
    calc
      _ = ∑ _q ∈ grid, (1 / 2 : ℝ) ^ L := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ grid, ∏ i, w (q i) := Finset.sum_le_sum hw
      _ ≤ ∑ q ∈ all, ∏ i, w (q i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by
          apply Finset.prod_nonneg
          intro i _
          dsimp [w]
          positivity)
      _ = (∑ z ∈ I, w z) ^ n := by
        rw [show (∑ q ∈ all, ∏ i, w (q i)) = ∏ _i : Fin n, ∑ z ∈ I, w z
          from Finset.sum_prod_piFinset I (fun _ => w), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity))
        (one_coordinate_weight_sum_le L) n
  have hreal : (grid.card : ℝ) ≤ (4 * 2 ^ (A + 1) : ℝ) ^ n := by
    calc
      _ ≤ (4 : ℝ) ^ n / (1 / 2 : ℝ) ^ L :=
        (le_div_iff₀ (by positivity)).2 hsum
      _ = _ := by
        rw [mul_pow, ← pow_mul, div_eq_mul_inv, ← inv_pow, one_div, inv_inv]
  exact_mod_cast hreal

/-- The integer points with squared norm at most `(A*N)^2*n` are covered
by exponentially many Cartesian products of `N`-point integer intervals. -/
theorem exists_integer_grid_cover (n N A : ℕ) (hN : 0 < N) :
    ∃ Q : Finset (Fin n → ℤ), Q.card ≤ (4 * 2 ^ (A + 1)) ^ n ∧
      ∀ z : Fin n → ℤ, (∑ i, (z i : ℝ) ^ 2) ≤ ((A : ℝ) * (N : ℝ)) ^ 2 * (n : ℝ) →
        ∃ q ∈ Q, ∀ i, z i ∈ integerGridInterval N (q i) := by
  classical
  let L := (A + 1) * n
  let Q := (Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
    (fun q => ∑ i, (q i).natAbs ≤ L)
  refine ⟨Q, grid_cutoff_card_le n A, fun z hz => ?_⟩
  let q (i : Fin n) := z i / (N : ℤ)
  have hsum : (∑ i, (q i).natAbs) ≤ L := grid_quotient_abs_sum hN z hz
  refine ⟨q, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, hsum⟩, ?_⟩
  · intro i
    have hi : (q i).natAbs ≤ L :=
      (Finset.single_le_sum (fun (j : Fin n) _ => Nat.zero_le (q j).natAbs)
        (Finset.mem_univ i)).trans hsum
    apply Finset.mem_Icc.mpr
    apply abs_le.mp
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hi
  · intro i
    exact integer_mem_gridInterval hN (z i)

end BooleanThreshold
