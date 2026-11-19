module

public import BooleanThreshold.JSSConditionalFejer
public import Mathlib.Data.Int.Interval

public section

open scoped BigOperators

namespace BooleanThreshold

private theorem sum_biUnion_le_sum_sums {ι G : Type*} [DecidableEq G]
    (g : G → ℝ) (hg : ∀ u, 0 ≤ g u) (B : ι → Finset G) (s : Finset ι) :
    (∑ u ∈ s.biUnion B, g u) ≤ ∑ j ∈ s, ∑ u ∈ B j, g u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    calc
      _ ≤ (∑ u ∈ B j, g u) + ∑ u ∈ s.biUnion B, g u := by
        rw [← Finset.sum_union_inter (s₁ := B j) (s₂ := s.biUnion B) (f := g)]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun u _ => hg u)
      _ ≤ _ := add_le_add (le_refl _) ih

/-- A length-`L` cyclic interval with `L ≤ K*N` carries at most `K` times
the mass bound on a length-`N` interval. -/
theorem cyclicInterval_mass_le_multiple {P N L K : ℕ}
    (hN : 0 < N) (hL : L ≤ K * N) (g : ZMod P → ℝ) (hg : ∀ t, 0 ≤ g t)
    {Q : ℝ} (hQ : ∀ a, ∑ t ∈ cyclicInterval P N a, g t ≤ Q) (a : ZMod P) :
    (∑ t ∈ cyclicInterval P L a, g t) ≤ (K : ℝ) * Q := by
  let B (j : ℕ) := cyclicInterval P N (a + ((j * N : ℕ) : ZMod P))
  have hcover : cyclicInterval P L a ⊆ (Finset.range K).biUnion B := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hi' : i < K * N := (Finset.mem_range.mp hi).trans_le hL
    have hj : i / N < K := (Nat.div_lt_iff_lt_mul hN).mpr hi'
    have hr : i % N < N := Nat.mod_lt _ hN
    have hs : i / N * N + i % N = i := by
      simpa only [Nat.mul_comm (i / N) N, Nat.add_comm] using Nat.mod_add_div i N
    refine Finset.mem_biUnion.mpr ⟨i / N, Finset.mem_range.mpr hj, ?_⟩
    exact Finset.mem_image.mpr ⟨i % N, Finset.mem_range.mpr hr, by
      rw [add_assoc, ← Nat.cast_add, hs]⟩
  calc
    _ ≤ ∑ u ∈ (Finset.range K).biUnion B, g u :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun u _ _ => hg u)
    _ ≤ ∑ j ∈ Finset.range K, ∑ u ∈ B j, g u := sum_biUnion_le_sum_sums g hg B _
    _ ≤ ∑ _j ∈ Finset.range K, Q := Finset.sum_le_sum fun j _ => hQ _
    _ = _ := by simp [nsmul_eq_mul]

/-- An integer interval shorter than the modulus enumerates its cyclic
image without repetitions. -/
theorem sum_integer_interval_eq_cyclicInterval {P L : ℕ} (hL : L ≤ P)
    {R : Type*} [AddCommMonoid R] (g : ZMod P → R) (l : ℤ) (t : ZMod P) :
    (∑ z ∈ Finset.Ico l (l + (L : ℤ)), g (t + (z : ZMod P))) =
      ∑ u ∈ cyclicInterval P L (t + (l : ZMod P)), g u := by
  let f (j : ℕ) := l + (j : ℤ)
  have hf : Function.Injective f := fun a b h => by
    have hh := add_left_cancel (show l + (a : ℤ) = l + (b : ℤ) from h)
    exact_mod_cast hh
  have hI : Finset.Ico l (l + (L : ℤ)) = (Finset.range L).image f := by
    ext z
    rw [Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨h₁, h₂⟩
      have hdiff : 0 ≤ z - l := sub_nonneg.mpr h₁
      have heq : ((z - l).toNat : ℤ) = z - l := Int.toNat_of_nonneg hdiff
      refine ⟨(z - l).toNat, Finset.mem_range.mpr ?_, ?_⟩
      · have h : ((z - l).toNat : ℤ) < (L : ℤ) := by rw [heq]; omega
        exact_mod_cast h
      · simp only [f, heq]; omega
    · rintro ⟨i, hi, rfl⟩
      have hi' : (i : ℤ) < (L : ℤ) := by exact_mod_cast Finset.mem_range.mp hi
      simp only [f]
      have hi₀ : 0 ≤ (i : ℤ) := by positivity
      omega
  let h (i : ℕ) := (t + (l : ZMod P)) + (i : ZMod P)
  have hh : Set.InjOn h (Finset.range L : Set ℕ) := by
    intro i hi j hj hij
    have heq : (i : ZMod P) = (j : ZMod P) := add_left_cancel hij
    have hij' := (ZMod.natCast_eq_natCast_iff' i j P).mp heq
    exact (Nat.mod_eq_of_lt ((Finset.mem_range.mp hi).trans_le hL)).symm.trans
      (hij'.trans (Nat.mod_eq_of_lt ((Finset.mem_range.mp hj).trans_le hL)))
  rw [hI, Finset.sum_image hf.injOn, cyclicInterval, Finset.sum_image hh]
  apply Finset.sum_congr rfl
  intro i _
  simp only [f, h, Int.cast_add, Int.cast_natCast, add_assoc]

/-- Either sign of an integer interval translates to a cyclic interval of
the same length. -/
theorem sum_signed_integer_interval_eq_cyclicInterval {P L : ℕ} (hL : L ≤ P)
    {R : Type*} [AddCommMonoid R] (g : ZMod P → R) (l : ℤ) (t : ZMod P) (b : Bool) :
    ∃ a : ZMod P, (∑ z ∈ Finset.Ico l (l + (L : ℤ)),
      g (t + if b then -(z : ZMod P) else (z : ZMod P))) =
      ∑ u ∈ cyclicInterval P L a, g u := by
  cases b
  · exact ⟨_, sum_integer_interval_eq_cyclicInterval hL g l t⟩
  · let a : ℤ := 1 - l - (L : ℤ)
    refine ⟨t + (a : ZMod P), ?_⟩
    let e := (Equiv.neg ℤ).toEmbedding
    have he : (Finset.Ico l (l + (L : ℤ))).map e = Finset.Ico a (a + (L : ℤ)) := by
      ext z
      simp only [Finset.mem_map, Finset.mem_Ico]
      constructor
      · rintro ⟨w, hw, h⟩
        change -w = z at h
        dsimp [a]
        omega
      · intro hz
        refine ⟨-z, ?_, by change -(-z) = z; simp⟩
        dsimp [a] at hz
        omega
    calc
      _ = ∑ z ∈ (Finset.Ico l (l + (L : ℤ))).map e, g (t + (z : ZMod P)) := by
        simp [e]
      _ = _ := by rw [he, sum_integer_interval_eq_cyclicInterval hL]

/-- A cyclic interval mass bound controls the average over either sign of
an integer coefficient interval. -/
theorem sum_signed_integer_interval_le_of_cyclic_mass {P N K : ℕ} (hN : 0 < N)
    (A : Finset ℤ) (hA : ∃ l u : ℤ, A = Finset.Ico l u)
    (hLo : N ≤ A.card) (hHi : A.card ≤ K * N) (hP : A.card ≤ P)
    (g : ZMod P → ℝ) (hg : ∀ t, 0 ≤ g t) {Q : ℝ} (hQ₀ : 0 ≤ Q)
    (hQ : ∀ u, ∑ t ∈ cyclicInterval P N u, g t ≤ Q) (t : ZMod P) (b : Bool) :
    (∑ z ∈ A, g (t + if b then -(z : ZMod P) else (z : ZMod P))) ≤
      ((K : ℝ) * Q / (N : ℝ)) * (A.card : ℝ) := by
  obtain ⟨l, u, hlu⟩ := hA
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (hN.trans_le hLo)
  rw [hlu] at hz
  have hlu' : l ≤ u := (Finset.mem_Ico.mp hz).1.trans (Finset.mem_Ico.mp hz).2.le
  have hL : (A.card : ℤ) = u - l := by rw [hlu, Int.card_Ico_of_le _ _ hlu']
  have hA' : A = Finset.Ico l (l + (A.card : ℤ)) := by
    rw [hL]
    calc
      _ = Finset.Ico l u := hlu
      _ = _ := by congr 1; ring
  obtain ⟨u₀, hu₀⟩ := sum_signed_integer_interval_eq_cyclicInterval hP g l t b
  have hsum : (∑ z ∈ A, g (t + if b then -(z : ZMod P) else (z : ZMod P))) =
      ∑ v ∈ cyclicInterval P A.card u₀, g v := by
    exact (Finset.sum_congr hA' (fun _ _ => rfl)).trans hu₀
  rw [hsum]
  refine (cyclicInterval_mass_le_multiple hN hHi g hg hQ u₀).trans ?_
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hLow : (N : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hLo
  calc
    _ = ((K : ℝ) * Q / (N : ℝ)) * (N : ℝ) := (div_mul_cancel₀ _ hN'.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hLow (by positivity)

end BooleanThreshold
