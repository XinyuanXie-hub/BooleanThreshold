module

public import BooleanThreshold.CokernelJointMoments

public noncomputable section

open scoped BigOperators Classical

namespace BooleanThreshold

universe u v

/-- The moment of a weighted sum of bounded nonnegative integer random variables
follows from joint tails on distinct indices. Each weight is at most one. -/
theorem finiteAverage_weighted_power_le_of_joint_tails (k : ℕ) :
    ∃ M > (0 : ℝ), ∀ {Ω : Type u} {P : Type v} [Fintype Ω] [Fintype P] [DecidableEq P]
      (D : ℕ) (p : P → ℕ) (_ : ∀ i, 2 ≤ p i)
      (w : P → ℝ) (_ : ∀ i, 0 ≤ w i) (_ : ∀ i, w i ≤ 1)
      (ν : Ω → P → ℕ) (_ : ∀ x i, ν x i ≤ D)
      (A E : ℝ) (_ : 0 ≤ A) (_ : 0 ≤ E)
      (_ : ∀ s : Finset P, s.card ≤ k → ∀ j : s → Fin D,
        finiteAverage (fun x => if ∀ i : s, (j i : ℕ) < ν x i then 1 else 0) ≤
          A * (∏ i : s, 1 / (p i : ℝ) ^ ((j i : ℕ) + 1)) + E),
      finiteAverage (fun x => (∑ i, w i * (ν x i : ℝ)) ^ k) ≤
        A * ((k : ℝ) + M * ∑ i, w i / (p i : ℝ)) ^ k +
          E * ((D : ℝ) * Fintype.card P) ^ k := by
  obtain ⟨M, hM, hgeom⟩ := powerIncrement_geometric_bound k
  refine ⟨M, hM, ?_⟩
  intro Ω P _ _ _ D p hp w hw₀ hw₁ ν hν A E hA hE hTail
  let v (i : P) := M * w i / (p i : ℝ)
  have hv (i : P) : 0 ≤ v i := div_nonneg (mul_nonneg hM.le (hw₀ i)) (Nat.cast_nonneg _)
  have hterm (f : Fin k → P) :
      finiteAverage (fun x => ∏ i, w (f i) * (ν x (f i) : ℝ)) ≤
        A * (∏ i ∈ Finset.univ.image f, v i) + E * (D : ℝ) ^ k := by
    let s := Finset.univ.image f
    let m (i : s) := ((Finset.univ : Finset (Fin k)).filter fun j => f j = i).card
    have hs : s.card ≤ k := by
      have hs := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := f)
      simpa only [Finset.card_univ, Fintype.card_fin] using hs
    have hm₀ (i : s) : 0 < m i := by
      obtain ⟨j, hj⟩ := Finset.mem_image.mp i.2
      exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj.1, hj.2⟩⟩
    have hm₁ (i : s) : m i ≤ k := by
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    have hdegree : (∑ i : s, m i) = k := by
      have hsum := Finset.card_eq_sum_card_image (s := (Finset.univ : Finset (Fin k))) f
      change ∑ i ∈ s.attach, ((Finset.univ : Finset (Fin k)).filter (fun j => f j = i)).card = k
      exact (Finset.sum_attach s (fun i : P =>
        ((Finset.univ : Finset (Fin k)).filter (fun j => f j = i)).card)).trans (by
          simpa only [s, Finset.card_univ, Fintype.card_fin] using hsum.symm)
    let a := ∏ i : s, w i ^ m i
    have ha₀ : 0 ≤ a := Finset.prod_nonneg fun i _ => pow_nonneg (hw₀ i) _
    have ha₁ : a ≤ 1 := Finset.prod_le_one₀ (fun i _ => pow_nonneg (hw₀ i) _)
      (fun i _ => pow_le_one₀ (hw₀ i) (hw₁ i))
    have hfactor (x : Ω) : (∏ i, w (f i) * (ν x (f i) : ℝ)) =
        a * (∏ i : s, (ν x i : ℝ) ^ m i) := by
      let z (i : P) := (w i * (ν x i : ℝ)) ^
        ((Finset.univ : Finset (Fin k)).filter (fun j => f j = i)).card
      calc
        _ = ∏ i ∈ s, z i := by
          simpa only [Finset.prod_const, z] using
            (Finset.prod_fiberwise_of_maps_to' (g := f) (s := (Finset.univ : Finset (Fin k)))
              (t := s) (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))
              (fun i : P => w i * (ν x i : ℝ))).symm
        _ = ∏ i : s, z i := (Finset.prod_attach s z).symm
        _ = _ := by simp only [z, m, mul_pow, Finset.prod_mul_distrib, a]
    have hTail' := joint_power_moment_le D (fun x (i : s) => ν x i)
      (fun x i => hν x i) m hm₀ (fun (i : s) j => 1 / (p i : ℝ) ^ ((j : ℕ) + 1))
      A E (hTail s hs)
    have hmbound : finiteAverage (fun x => ∏ i : s, (ν x i : ℝ) ^ m i) ≤
        A * (∏ i : s, M / (p i : ℝ)) + E * (D : ℝ) ^ k := by
      have hD : (∏ i : s, (D : ℝ) ^ m i) = (D : ℝ) ^ k := by
        rw [Finset.prod_pow_eq_pow_sum, hdegree]
      rw [hD] at hTail'
      refine hTail'.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ hA) le_rfl)
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg fun j _ => mul_nonneg (powerIncrement_nonneg _ _)
          (by positivity)
      · intro i _
        exact hgeom (m i) D (p i) (hm₁ i) (hp i)
    have hweighted : a * (∏ i : s, M / (p i : ℝ)) ≤ ∏ i ∈ s, v i := by
      calc
        _ = ∏ i : s, w i ^ m i * (M / (p i : ℝ)) := by
          simp only [Finset.prod_mul_distrib, a]
        _ ≤ ∏ i : s, v i := by
          apply Finset.prod_le_prod₀
          · intro i _
            exact mul_nonneg (pow_nonneg (hw₀ i) _) (by positivity)
          · intro i _
            calc
              _ ≤ w i * (M / (p i : ℝ)) :=
                mul_le_mul_of_nonneg_right
                  (by simpa only [pow_one] using pow_le_pow_of_le_one (hw₀ i) (hw₁ i) (hm₀ i)) (by positivity)
              _ = _ := by dsimp [v]; ring
        _ = _ := Finset.prod_attach s v
    simp_rw [hfactor, finiteAverage_const_mul]
    calc
      _ ≤ a * (A * (∏ i : s, M / (p i : ℝ)) + E * (D : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hmbound ha₀
      _ = A * (a * (∏ i : s, M / (p i : ℝ))) + a * (E * (D : ℝ) ^ k) := by ring
      _ ≤ A * (∏ i ∈ s, v i) + 1 * (E * (D : ℝ) ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left hweighted hA)
          (mul_le_mul_of_nonneg_right ha₁ (by positivity))
      _ = _ := by rw [one_mul]
  have hExpand (x : Ω) :
      (∑ i, w i * (ν x i : ℝ)) ^ k = ∑ f : Fin k → P, ∏ i, w (f i) * (ν x (f i) : ℝ) := by
    simpa only [Fintype.piFinset_univ] using
      Finset.sum_pow' Finset.univ (fun i => w i * (ν x i : ℝ)) k
  simp_rw [hExpand]
  rw [finiteAverage_sum]
  calc
    _ ≤ ∑ f : Fin k → P, (A * (∏ i ∈ Finset.univ.image f, v i) + E * (D : ℝ) ^ k) :=
      Finset.sum_le_sum fun f _ => hterm f
    _ = A * (∑ f : Fin k → P, ∏ i ∈ Finset.univ.image f, v i) +
        E * ((D : ℝ) * Fintype.card P) ^ k := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, mul_pow]
      ring
    _ ≤ A * ((k : ℝ) + ∑ i, v i) ^ k + E * ((D : ℝ) * Fintype.card P) ^ k :=
      add_le_add (mul_le_mul_of_nonneg_left (sum_distinct_tuple_weights_le v hv k) hA) le_rfl
    _ = _ := by
      simp only [v, Finset.mul_sum, mul_div_assoc]

end BooleanThreshold
