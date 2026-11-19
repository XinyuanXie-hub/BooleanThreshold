module

public import BooleanThreshold.SignWindow
public import Mathlib.Data.Fin.Tuple.Sort

public section

open scoped BigOperators Topology
open Filter

namespace BooleanThreshold

/-- Non-almost-constant vectors have separated lower and upper quantiles. -/
theorem exists_separated_quantile_groups {n k : ℕ} (hk : 2 * k + 1 ≤ n)
    {δ ρ : ℝ} {a : Fin n → ℝ} (ha : ∑ i, a i ^ 2 = 1)
    (hc : a ∉ almostConstantUnitVectors n δ ρ)
    (hk' : (1 - δ) * (n : ℝ) ≤ ((n - 2 * k : ℕ) : ℝ)) :
    ∃ I J : Finset (Fin n), I.card = k ∧ J.card = k ∧ Disjoint I J ∧
      ∀ i ∈ I, ∀ j ∈ J, 2 * (ρ / Real.sqrt (n : ℝ)) < a j - a i := by
  classical
  let e := Tuple.sort a
  let L : Finset (Fin n) := Finset.univ.filter (fun i => i.val < k)
  let H : Finset (Fin n) := Finset.univ.filter (fun i => i.val < n - k)
  let p : Fin n := ⟨k, by omega⟩
  let q : Fin n := ⟨n - k - 1, by omega⟩
  have hmono : Monotone (a ∘ e) := Tuple.monotone_sort a
  have hHL : L ⊆ H := by
    intro i hi
    simp only [L, H, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  have hLc : L.card = k := by simp [L, Fin.card_filter_val_lt, min_eq_right (by omega : k ≤ n)]
  have hHc : H.card = n - k := by
    simp [H, Fin.card_filter_val_lt]
  have hdiff : 2 * (ρ / Real.sqrt (n : ℝ)) < a (e q) - a (e p) := by
    by_contra! hgap
    let mid := (a (e q) + a (e p)) / 2
    let C : Finset (Fin n) := (H \ L).map e.toEmbedding
    have hC : C.card = n - 2 * k := by
      rw [Finset.card_map, Finset.card_sdiff_of_subset hHL, hHc, hLc]
      omega
    have hsubset : C ⊆ Finset.univ.filter (fun i => |a i - mid| ≤ ρ / Real.sqrt (n : ℝ)) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      have hj₁ := (Finset.mem_sdiff.mp hj).1
      have hj₂ := (Finset.mem_sdiff.mp hj).2
      simp only [H, L, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
      have hpj : p ≤ j := by change k ≤ j.val; omega
      have hjq : j ≤ q := by change j.val ≤ n - k - 1; omega
      have hleft := hmono hpj
      have hright := hmono hjq
      simp only [Function.comp_apply] at hleft hright
      simp only [Equiv.toEmbedding_apply, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [abs_le]
      dsimp [mid]
      constructor <;> linarith only [hleft, hright, hgap]
    have hcard := Finset.card_le_card hsubset
    rw [hC] at hcard
    exact hc ⟨ha, mid, hk'.trans (by exact_mod_cast hcard)⟩
  refine ⟨L.map e.toEmbedding, (Finset.univ \ H).map e.toEmbedding, ?_, ?_, ?_, ?_⟩
  · rwa [Finset.card_map]
  · rw [Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ H), hHc,
      Finset.card_univ, Fintype.card_fin]
    omega
  · rw [Finset.disjoint_left]
    intro i hi hj
    obtain ⟨j, hjL, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨l, hl, eq⟩ := Finset.mem_map.mp hj
    have : l = j := e.injective eq
    subst l
    exact (Finset.mem_sdiff.mp hl).2 (hHL hjL)
  · intro i hi j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hj
    have ht' := (Finset.mem_sdiff.mp ht).2
    simp only [L, H, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht'
    have hsp : s ≤ p := by change s.val ≤ k; omega
    have hqt : q ≤ t := by change n - k - 1 ≤ t.val; omega
    exact hdiff.trans_le (sub_le_sub (hmono hqt) (hmono hsp))

/-- A unit vector has few coordinates above a given absolute threshold. -/
theorem unit_large_coordinates_bound {n : ℕ} {a : Fin n → ℝ}
    (ha : ∑ i, a i ^ 2 = 1) {B : ℝ} (hB : 0 ≤ B) :
    ((Finset.univ.filter fun i => B < |a i|).card : ℝ) * B ^ 2 ≤ 1 := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun i => B < |a i|)
  calc
    _ = ∑ i ∈ U, B ^ 2 := by simp [U, nsmul_eq_mul]
    _ ≤ ∑ i ∈ U, a i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← sq_abs (a i)]
      exact pow_le_pow_left₀ hB (Finset.mem_filter.mp hi).2.le 2
    _ ≤ ∑ i, a i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = _ := ha

/-- Coordinate bands of linear size, separated at the natural Euclidean scale,
for unit vectors outside the almost-constant class. -/
theorem exists_bounded_separated_groups_eventually {δ ρ : ℝ} (hδ : 0 < δ) (hd : δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ a : Fin n → ℝ, (∑ i, a i ^ 2) = 1 →
      a ∉ almostConstantUnitVectors n δ ρ →
      ∃ I J : Finset (Fin n), ((δ / 16) * (n : ℝ) ≤ I.card) ∧
        ((δ / 16) * (n : ℝ) ≤ J.card) ∧ Disjoint I J ∧
        (∀ i ∈ I ∪ J, |a i| ≤ Real.sqrt (32 / δ) / Real.sqrt (n : ℝ)) ∧
        ∀ i ∈ I, ∀ j ∈ J, 2 * (ρ / Real.sqrt (n : ℝ)) < a j - a i := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (8 / δ : ℝ)
  apply eventually_atTop.mpr
  refine ⟨max N 1, fun n hn a ha hnc => ?_⟩
  have hn₀ : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_right N 1).trans hn)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn₀
  have hnδ : (8 : ℝ) ≤ δ * (n : ℝ) := by
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    exact mul_comm (n : ℝ) δ ▸ (div_le_iff₀ hδ).mp (hN.trans (by exact_mod_cast hnN))
  let k := ⌊δ * (n : ℝ) / 4⌋₊
  have hkUp : (k : ℝ) ≤ δ * (n : ℝ) / 4 := Nat.floor_le (by positivity)
  have hkLo : δ * (n : ℝ) / 8 ≤ (k : ℝ) := by
    have h := Nat.lt_floor_add_one (δ * (n : ℝ) / 4)
    change δ * (n : ℝ) / 4 < (k : ℝ) + 1 at h
    linarith only [h, hnδ]
  have hkDim : 2 * k + 1 ≤ n := by
    apply Nat.succ_le_of_lt
    have hMul : δ * (n : ℝ) < n := by simpa using mul_lt_mul_of_pos_right hd hnR
    exact_mod_cast (show 2 * (k : ℝ) < (n : ℝ) by linarith only [hkUp, hMul, hnR])
  have hkCard : (1 - δ) * (n : ℝ) ≤ ((n - 2 * k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ n), Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hkUp, hnδ]
  obtain ⟨I, J, hI, hJ, hdij, hsep⟩ := exists_separated_quantile_groups hkDim ha hnc hkCard
  let B := Real.sqrt (32 / δ) / Real.sqrt (n : ℝ)
  let U : Finset (Fin n) := Finset.univ.filter (fun i => B < |a i|)
  have hB : 0 ≤ B := by positivity
  have hBsq : B ^ 2 = 32 / (δ * (n : ℝ)) := by
    simp only [B, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 32 / δ),
      Real.sq_sqrt hnR.le]
    rw [div_div]
  have hU : (U.card : ℝ) ≤ δ * (n : ℝ) / 32 := by
    have h := unit_large_coordinates_bound ha hB
    change (U.card : ℝ) * B ^ 2 ≤ 1 at h
    rw [hBsq, ← mul_div_assoc] at h
    have h' := (div_le_iff₀ (by positivity : 0 < δ * (n : ℝ))).mp h
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    simpa [mul_one] using h'
  let I' := I \ U
  let J' := J \ U
  have hsize (S : Finset (Fin n)) (hS : S.card = k) :
      (δ / 16) * (n : ℝ) ≤ ((S \ U).card : ℝ) := by
    have hcounts : (S.card : ℝ) ≤ ((S \ U).card : ℝ) + U.card := by
      exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := S) (t := U))
    rw [hS] at hcounts
    nlinarith only [hcounts, hU, hkLo, hnδ]
  refine ⟨I', J', hsize I hI, hsize J hJ, hdij.mono Finset.sdiff_subset Finset.sdiff_subset, ?_, ?_⟩
  · intro i hi
    apply le_of_not_gt
    intro hz
    have hu : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_sdiff.mp hi).2 hu
    · exact (Finset.mem_sdiff.mp hi).2 hu
  · intro i hi j hj
    exact hsep i (Finset.sdiff_subset hi) j (Finset.sdiff_subset hj)

end BooleanThreshold
