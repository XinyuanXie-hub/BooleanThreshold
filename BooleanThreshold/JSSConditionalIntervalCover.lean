module

public import BooleanThreshold.JSSConditionalGridFibers

public section

open Finset
open scoped BigOperators Classical

namespace BooleanThreshold

private theorem mem_Ico_of_width_cover {N W : ℕ} (hN : 0 < N) {l u x : ℤ}
    (hwidth : (Ico l u).card ≤ W * N) (hx : x ∈ Ico l u) :
    ∃ j : Fin W, x ∈ Ico (l + (j.val : ℤ) * (N : ℤ)) (l + (j.val : ℤ) * (N : ℤ) + N) := by
  obtain ⟨hxl, hxu⟩ := mem_Ico.mp hx
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hwidthZ : u - l ≤ (W : ℤ) * (N : ℤ) := by
    have h := Int.card_Ico_of_le l u (hxl.trans hxu.le)
    have hh : ((Ico l u).card : ℤ) ≤ ((W * N : ℕ) : ℤ) := by exact_mod_cast hwidth
    rwa [h, Nat.cast_mul] at hh
  let j := (x - l) / (N : ℤ)
  have hj₀ : 0 ≤ j := Int.ediv_nonneg (sub_nonneg.mpr hxl) hNpos.le
  have hjW : j < (W : ℤ) := (Int.ediv_lt_iff_lt_mul hNpos).mpr (by omega)
  have hcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj₀
  let i : Fin W := ⟨j.toNat, by exact_mod_cast hcast ▸ hjW⟩
  refine ⟨i, mem_Ico.mpr ?_⟩
  have hleft : j * (N : ℤ) ≤ x - l := Int.ediv_mul_le _ hNpos.ne'
  have hright : x - l < (j + 1) * (N : ℤ) :=
    (Int.ediv_lt_iff_lt_mul hNpos).mp (by change j < j + 1; omega)
  change l + (j.toNat : ℤ) * (N : ℤ) ≤ x ∧ x < l + (j.toNat : ℤ) * (N : ℤ) + N
  rw [hcast]
  rw [add_mul, one_mul] at hright
  omega

/-- Apply a count for fixed-width integer boxes to the product of bounded-width
intervals by covering each coordinate with consecutive fixed-width intervals. -/
theorem card_filter_two_grids_le_of_interval_cover {N W d₁ d₂ : ℕ} (hN : 0 < N)
    (B₁ : Fin d₁ → Finset ℤ) (B₂ : Fin d₂ → Finset ℤ)
    (hB₁ : ∀ i, ∃ l u : ℤ, B₁ i = Ico l u ∧ (B₁ i).card ≤ W * N)
    (hB₂ : ∀ i, ∃ l u : ℤ, B₂ i = Ico l u ∧ (B₂ i).card ≤ W * N)
    (P : ((Fin d₁ → ℤ) × (Fin d₂ → ℤ)) → Prop) {C : ℝ}
    (h : ∀ (s₁ : Fin d₁ → ℤ) (s₂ : Fin d₂ → ℤ),
      let A₁ := Fintype.piFinset (fun i => Ico (s₁ i) (s₁ i + (N : ℤ)))
      let A₂ := Fintype.piFinset (fun i => Ico (s₂ i) (s₂ i + (N : ℤ)))
      (((A₁.product A₂).filter P).card : ℝ) ≤ C * (N : ℝ) ^ (d₁ + d₂)) :
    ((((Fintype.piFinset B₁).product (Fintype.piFinset B₂)).filter P).card : ℝ) ≤
      C * ((W : ℝ) * (N : ℝ)) ^ (d₁ + d₂) := by
  choose l₁ u₁ h₁ hwidth₁ using hB₁
  choose l₂ u₂ h₂ hwidth₂ using hB₂
  let J := (Fin d₁ → Fin W) × (Fin d₂ → Fin W)
  let s₁ (j : J) (i : Fin d₁) := l₁ i + ((j.1 i).val : ℤ) * (N : ℤ)
  let s₂ (j : J) (i : Fin d₂) := l₂ i + ((j.2 i).val : ℤ) * (N : ℤ)
  let A₁ (j : J) := Fintype.piFinset (fun i => Ico (s₁ j i) (s₁ j i + (N : ℤ)))
  let A₂ (j : J) := Fintype.piFinset (fun i => Ico (s₂ j i) (s₂ j i + (N : ℤ)))
  let G (j : J) := ((A₁ j).product (A₂ j)).filter P
  let E := ((Fintype.piFinset B₁).product (Fintype.piFinset B₂)).filter P
  have hcover : E ⊆ univ.biUnion G := by
    rintro ⟨x₁, x₂⟩ hx
    obtain ⟨hmem, hP⟩ := mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := mem_product.mp hmem
    have he₁ (i : Fin d₁) : ∃ j : Fin W,
        x₁ i ∈ Ico (l₁ i + (j.val : ℤ) * (N : ℤ)) (l₁ i + (j.val : ℤ) * (N : ℤ) + N) :=
      mem_Ico_of_width_cover hN (h₁ i ▸ hwidth₁ i) (h₁ i ▸ Fintype.mem_piFinset.mp hx₁ i)
    have he₂ (i : Fin d₂) : ∃ j : Fin W,
        x₂ i ∈ Ico (l₂ i + (j.val : ℤ) * (N : ℤ)) (l₂ i + (j.val : ℤ) * (N : ℤ) + N) :=
      mem_Ico_of_width_cover hN (h₂ i ▸ hwidth₂ i) (h₂ i ▸ Fintype.mem_piFinset.mp hx₂ i)
    choose j₁ hj₁ using he₁
    choose j₂ hj₂ using he₂
    exact mem_biUnion.mpr ⟨(j₁, j₂), mem_univ _, mem_filter.mpr
      ⟨mem_product.mpr ⟨Fintype.mem_piFinset.mpr hj₁, Fintype.mem_piFinset.mpr hj₂⟩, hP⟩⟩
  calc
    _ ≤ ((univ.biUnion G).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ j, ((G j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _j : J, C * (N : ℝ) ^ (d₁ + d₂) := sum_le_sum fun j _ => h (s₁ j) (s₂ j)
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, J, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
      rw [← pow_add (W : ℝ), mul_left_comm, ← mul_pow]

end BooleanThreshold
