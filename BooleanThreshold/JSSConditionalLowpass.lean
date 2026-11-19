module

public import BooleanThreshold.JSSConditionalFejer

public section

open scoped BigOperators

namespace BooleanThreshold

private theorem cyclic_shell_mass_le {P N : ℕ} [NeZero P] (hN : 0 < N)
    (g : ZMod P → ℝ) (hg : ∀ t, 0 ≤ g t) {Q : ℝ}
    (hQ : ∀ a, ∑ u ∈ cyclicInterval P N a, g u ≤ Q) (t : ZMod P) (j : ℕ) :
    (∑ u ∈ Finset.univ.filter (fun u => (t - u).valMinAbs.natAbs / N = j), g u) ≤ 2 * Q := by
  let A := cyclicInterval P N (t - (↑(N * j) : ZMod P) - (↑(N - 1) : ZMod P))
  let B := cyclicInterval P N (t + (↑(N * j) : ZMod P))
  have hsub : (Finset.univ.filter (fun u : ZMod P => (t - u).valMinAbs.natAbs / N = j)) ⊆ A ∪ B := by
    intro u hu
    let z := (t - u).valMinAbs
    let d := z.natAbs
    let s := d % N
    have hj : d / N = j := (Finset.mem_filter.mp hu).2
    have hs : s < N := Nat.mod_lt _ hN
    have hd : d = s + N * j := by
      have h := Nat.mod_add_div d N
      rw [hj] at h
      exact h.symm
    have hd' : (d : ZMod P) = (s : ZMod P) + (↑(N * j) : ZMod P) := by
      simpa only [Nat.cast_add] using congrArg (fun m : ℕ => (m : ZMod P)) hd
    rw [Finset.mem_union]
    rcases z.natAbs_eq with h | h
    · left
      have hc := congrArg (fun z : ℤ => (z : ZMod P)) h.symm
      change (((d : ℕ) : ℤ) : ZMod P) = ((t - u).valMinAbs : ZMod P) at hc
      rw [Int.cast_natCast, ZMod.coe_valMinAbs] at hc
      apply Finset.mem_image.mpr
      refine ⟨N - 1 - s, Finset.mem_range.mpr (by omega), ?_⟩
      calc
        _ = t - (d : ZMod P) := by
          rw [Nat.cast_sub (by omega : s ≤ N - 1), hd']
          ring
        _ = u := by rw [hc]; ring
    · right
      have hc := congrArg (fun z : ℤ => (z : ZMod P)) h
      change ((t - u).valMinAbs : ZMod P) = ((-(d : ℤ) : ℤ) : ZMod P) at hc
      rw [ZMod.coe_valMinAbs, Int.cast_neg, Int.cast_natCast] at hc
      have hc' : (d : ZMod P) = -(t - u) := by rw [hc, neg_neg]
      apply Finset.mem_image.mpr
      refine ⟨s, Finset.mem_range.mpr hs, ?_⟩
      calc
        _ = t + (d : ZMod P) := by rw [hd']; ring
        _ = u := by rw [hc']; ring
  calc
    _ ≤ ∑ u ∈ A ∪ B, g u := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hg u)
    _ ≤ (∑ u ∈ A, g u) + ∑ u ∈ B, g u := by
      rw [← Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := g)]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun u _ => hg u)
    _ ≤ Q + Q := add_le_add (hQ _) (hQ _)
    _ = _ := by ring

private noncomputable def shellWeight (N j : ℕ) : ℝ :=
  if j = 0 then 10 / (N : ℝ) else 1 / ((j : ℝ) ^ 2 * (N : ℝ))

private theorem shellWeight_nonneg (N j : ℕ) : 0 ≤ shellWeight N j := by
  unfold shellWeight
  split <;> positivity

private theorem shellWeight_sum_le {N : ℕ} (hN : 0 < N) (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), shellWeight N j) ≤ 12 / (N : ℝ) := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have htel (j : ℕ) (hj : 0 < j) : shellWeight N j ≤
      (2 / (N : ℝ)) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) := by
    have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
    rw [shellWeight, ite_eq_right hj.ne',
      show (2 / (N : ℝ)) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) =
        2 / ((j : ℝ) * ((j : ℝ) + 1) * (N : ℝ)) by
          field_simp [hN'.ne', hj'.ne', show (j : ℝ) + 1 ≠ 0 by positivity]; ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hnat : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hh := mul_le_mul_of_nonneg_right (show (j : ℝ) + 1 ≤ 2 * (j : ℝ) by linarith only [hnat])
      (show 0 ≤ (j : ℝ) * (N : ℝ) by positivity)
    nlinarith only [hh]
  have hh (K : ℕ) : (∑ j ∈ Finset.range (K + 1), shellWeight N j) ≤
      10 / (N : ℝ) + 2 / (N : ℝ) * (1 - 1 / ((K : ℝ) + 1)) := by
    induction K with
    | zero => simp [shellWeight]
    | succ K ih =>
      rw [Finset.sum_range_succ]
      refine (add_le_add ih (htel (K + 1) (by omega))).trans_eq ?_
      push_cast
      ring
  refine (hh L).trans ?_
  calc
    _ ≤ 10 / (N : ℝ) + 2 / (N : ℝ) * 1 :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity))
    _ = _ := by ring

private theorem fejerKernel_shell_tail {P N M : ℕ} [NeZero P] (hN : 0 < N) (hM : 0 < M)
    (hMN : P ≤ M * N) (t : ZMod P) (hj : 0 < t.valMinAbs.natAbs / N) :
    fejerKernel M t ≤ 1 / (4 * ((t.valMinAbs.natAbs / N : ℕ) : ℝ) ^ 2 * (N : ℝ)) := by
  let j := t.valMinAbs.natAbs / N
  let d := t.valMinAbs.natAbs
  have ht : t ≠ 0 := by rintro rfl; simp [ZMod.valMinAbs_zero] at hj
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hd : (j : ℝ) * (N : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.mul_comm (d / N) N ▸ Nat.mul_div_le d N)
  have hd' : 0 < (d : ℝ) := (mul_pos hj' hN').trans_le hd
  calc
    _ ≤ (P : ℝ) / (4 * (M : ℝ) * (d : ℝ) ^ 2) := fejerKernel_le_inv_cyclic_distance_sq hM ht
    _ ≤ ((M : ℝ) * (N : ℝ)) / (4 * (M : ℝ) * (d : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hMN) (by positivity)
    _ = (N : ℝ) / (4 * (d : ℝ) ^ 2) := by field_simp
    _ ≤ (N : ℝ) / (4 * ((j : ℝ) * (N : ℝ)) ^ 2) :=
      div_le_div_of_nonneg_left hN'.le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hd 2) (by norm_num))
    _ = _ := by change _ = 1 / (4 * (j : ℝ) ^ 2 * (N : ℝ)); field_simp

private theorem abs_vpKernel_le_shellWeight {P N M : ℕ} [NeZero P] (hN : 0 < N) (hM : 0 < M)
    (hl : P ≤ M * N) (hu : M * N ≤ 2 * P) (t : ZMod P) :
    |vpKernel M t| ≤ shellWeight N (t.valMinAbs.natAbs / N) := by
  have hM₂ : 0 < 2 * M := by omega
  have htri : |vpKernel M t| ≤ 2 * fejerKernel (2 * M) t + fejerKernel M t := by
    unfold vpKernel
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (mul_nonneg (by norm_num) (fejerKernel_nonneg (2 * M) t)),
      abs_of_nonneg (fejerKernel_nonneg M t)])
  refine htri.trans ?_
  let j := t.valMinAbs.natAbs / N
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hP : 0 < (P : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  by_cases hj : j = 0
  · rw [show t.valMinAbs.natAbs / N = 0 from hj, shellWeight, ite_eq_left rfl]
    have hM' : (M : ℝ) / (P : ℝ) ≤ 2 / (N : ℝ) := by
      apply (div_le_div_iff₀ hP hN').mpr
      exact_mod_cast hu
    have h₁ := fejerKernel_le_bandwidth_div_modulus hM t
    have h₂ := fejerKernel_le_bandwidth_div_modulus hM₂ t
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] at h₂
    have hE : 10 / (N : ℝ) = 5 * (2 / (N : ℝ)) := by ring
    rw [hE]
    linarith only [h₁, h₂, hM']
  · have hj' : 0 < j := Nat.pos_of_ne_zero hj
    have hl₂ : P ≤ (2 * M) * N := hl.trans (Nat.mul_le_mul_right N (by omega))
    have h₁ := fejerKernel_shell_tail hN hM hl t hj'
    have h₂ := fejerKernel_shell_tail hN hM₂ hl₂ t hj'
    change _ ≤ shellWeight N j
    rw [shellWeight, ite_eq_right hj]
    let V := (j : ℝ) ^ 2 * (N : ℝ)
    have hjr : 0 < (j : ℝ) := by exact_mod_cast hj'
    have hv : 0 < V := by dsimp [V]; positivity
    change _ ≤ 1 / V
    have hq : 1 / (4 * (j : ℝ) ^ 2 * (N : ℝ)) = (1 / 4 : ℝ) * (1 / V) := by dsimp [V]; ring
    change fejerKernel M t ≤ _ at h₁
    change fejerKernel (2 * M) t ≤ _ at h₂
    rw [hq] at h₁ h₂
    linarith only [h₁, h₂, show 0 ≤ 1 / V by positivity]

/-- A nonnegative function with local mass at most `Q` on every length-`N`
cyclic interval has pointwise low-pass convolution at most `24 Q / N`. -/
theorem abs_cyclicConvolution_vp_le_of_local_mass {P N M : ℕ} [NeZero P]
    (hN : 0 < N) (hM : 0 < M) (hl : P ≤ M * N) (hu : M * N ≤ 2 * P)
    (g : ZMod P → ℝ) (hg : ∀ t, 0 ≤ g t) {Q : ℝ} (hQ₀ : 0 ≤ Q)
    (hQ : ∀ a, ∑ u ∈ cyclicInterval P N a, g u ≤ Q) (t : ZMod P) :
    |cyclicConvolution g (vpKernel M) t| ≤ 24 * Q / (N : ℝ) := by
  let r (u : ZMod P) := (t - u).valMinAbs.natAbs / N
  have hr (u : ZMod P) : r u ∈ Finset.range (P + 1) := by
    apply Finset.mem_range.mpr
    have h := Nat.div_le_self (t - u).valMinAbs.natAbs N
    have he := ZMod.natAbs_valMinAbs_le (t - u)
    have hp := Nat.div_le_self P 2
    dsimp [r]
    omega
  unfold cyclicConvolution
  calc
    _ ≤ ∑ u : ZMod P, |g u * vpKernel M (t - u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u : ZMod P, g u * shellWeight N (r u) := by
      apply Finset.sum_le_sum
      intro u _
      rw [abs_mul, abs_of_nonneg (hg u)]
      exact mul_le_mul_of_nonneg_left (abs_vpKernel_le_shellWeight hN hM hl hu _) (hg u)
    _ = ∑ j ∈ Finset.range (P + 1), ∑ u ∈ Finset.univ.filter (fun u => r u = j),
          g u * shellWeight N (r u) :=
      (Finset.sum_fiberwise_of_maps_to (fun u _ => hr u) _).symm
    _ ≤ ∑ j ∈ Finset.range (P + 1), (2 * Q) * shellWeight N j := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = (∑ u ∈ Finset.univ.filter (fun u => r u = j), g u) * shellWeight N j := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun u hu' => ?_
          rw [(Finset.mem_filter.mp hu').2]
        _ ≤ _ := mul_le_mul_of_nonneg_right (cyclic_shell_mass_le hN g hg hQ t j) (shellWeight_nonneg _ _)
    _ = (2 * Q) * ∑ j ∈ Finset.range (P + 1), shellWeight N j := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * Q) * (12 / (N : ℝ)) := mul_le_mul_of_nonneg_left (shellWeight_sum_le hN P) (by positivity)
    _ = _ := by ring

end BooleanThreshold
