module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

public section

open Finset
open scoped Pointwise BigOperators Classical

namespace BooleanThreshold

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private theorem nsmul_mono_of_zero_mem (A : Finset G) (h₀ : 0 ∈ A) :
    Monotone (fun j : ℕ => j • A) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  rw [succ_nsmul]
  exact mem_add.mpr ⟨x, hx, 0, h₀, add_zero x⟩

private theorem mem_some_nsmul_of_closure_eq_top (A : Finset G)
    (hneg : ∀ x ∈ A, -x ∈ A) (htop : AddSubgroup.closure (A : Set G) = ⊤) (x : G) :
    ∃ j : ℕ, x ∈ j • A := by
  have hneg' (j : ℕ) : ∀ x ∈ j • A, -x ∈ j • A := by
    induction j with
    | zero => simp
    | succ j ih =>
      rintro x hx
      rw [succ_nsmul] at hx ⊢
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hx
      exact mem_add.mpr ⟨-u, ih u hu, -v, hneg v hv, by abel⟩
  let H : AddSubgroup G :=
    { carrier := {x | ∃ j : ℕ, x ∈ j • A}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨j, hj⟩ ⟨k, hk⟩
        exact ⟨j + k, by rw [add_nsmul]; exact mem_add.mpr ⟨x, hj, y, hk, rfl⟩⟩
      neg_mem' := by
        rintro x ⟨j, hj⟩
        exact ⟨j, hneg' j x hj⟩ }
  have hsub : AddSubgroup.closure (A : Set G) ≤ H := by
    rw [AddSubgroup.closure_le]
    exact fun x hx => ⟨1, by simpa using hx⟩
  rw [htop] at hsub
  exact hsub (AddSubgroup.mem_top x)

private theorem nsmul_mem_iff_sum {A : Finset G} (h₀ : 0 ∈ A) {j : ℕ} {x : G}
    (hx : x ∈ j • A) :
    ∃ f : ℕ → G, (∀ i, f i ∈ A) ∧ (∑ i ∈ range j, f i) = x := by
  induction j generalizing x with
  | zero =>
      have hx₀ : x = 0 := by simpa using hx
      exact ⟨fun _ => 0, fun _ => h₀, by simp [hx₀]⟩
  | succ j ih =>
      rw [succ_nsmul] at hx
      obtain ⟨v, hv, u, hu, rfl⟩ := mem_add.mp hx
      obtain ⟨f, hf, hsum⟩ := ih hv
      let g (i : ℕ) := if i = j then u else f i
      have hg : ∀ i, g i ∈ A := by
        intro i
        by_cases h : i = j <;> simp [g, h, hu, hf]
      have hfirst : (∑ i ∈ range j, g i) = v := by
        rw [← hsum]
        exact sum_congr rfl fun i hi => ite_eq_right (mem_range.mp hi).ne
      refine ⟨g, hg, ?_⟩
      rw [sum_range_succ, hfirst]
      simp [g]

private theorem sum_range_mem_nsmul {A : Finset G} (f : ℕ → G) (hf : ∀ i, f i ∈ A) (n : ℕ) :
    (∑ i ∈ range n, f i) ∈ n • A := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, succ_nsmul]
    exact mem_add.mpr ⟨_, ih, f n, hf n, rfl⟩

/-- A proper iterated sumset of a symmetric generating set contains disjoint
translates of that set at every third step of a shortest path. -/
theorem symmetric_generating_sumset_card_le [Fintype G] (A : Finset G)
    (h₀ : 0 ∈ A) (hneg : ∀ x ∈ A, -x ∈ A)
    (htop : AddSubgroup.closure (A : Set G) = ⊤) {k : ℕ} (hk : 0 < k)
    (hproper : (k • A).card < Fintype.card G) :
    (A.card : ℝ) ≤ 3 * ((k • A).card : ℝ) / k := by
  have hn : ∃ x : G, x ∉ k • A := by
    by_contra! h
    have he : k • A = univ := eq_univ_of_forall h
    rw [he, card_univ] at hproper
    exact (lt_irrefl _ hproper).elim
  obtain ⟨x, hx⟩ := hn
  have hex := mem_some_nsmul_of_closure_eq_top A hneg htop x
  let l := Nat.find hex
  have hxl : x ∈ l • A := Nat.find_spec hex
  have hl : k < l := by
    by_contra! h
    exact hx (nsmul_mono_of_zero_mem A h₀ h hxl)
  obtain ⟨f, hf, hfx⟩ := nsmul_mem_iff_sum h₀ hxl
  let v (i : ℕ) := ∑ j ∈ range i, f j
  have hv (i : ℕ) : v i ∈ i • A := sum_range_mem_nsmul f hf i
  have hdiff {i j : ℕ} (hij : i + 3 ≤ j) (hjl : j ≤ l) :
      v j - v i ∉ (2 : ℕ) • A := by
    intro h
    let w := ∑ t ∈ range (l - j), f (j + t)
    have hw : w ∈ (l - j) • A := sum_range_mem_nsmul _ (fun t => hf (j + t)) _
    have he : x = v j + w := by
      rw [← hfx]
      change (∑ t ∈ range l, f t) = (∑ t ∈ range j, f t) + ∑ t ∈ range (l - j), f (j + t)
      have hs := sum_range_add f j (l - j)
      rw [Nat.add_sub_of_le hjl] at hs
      simpa only [Nat.add_comm j] using hs
    have hx' : x ∈ (i + 2 + (l - j)) • A := by
      rw [he, show v j = v i + (v j - v i) by abel, add_nsmul, add_nsmul]
      exact mem_add.mpr ⟨_, mem_add.mpr ⟨_, hv i, _, h, rfl⟩, w, hw, rfl⟩
    exact Nat.find_min hex (by omega : i + 2 + (l - j) < l) hx'
  let R := range ((k + 2) / 3)
  let U (r : ℕ) := A.image (fun a => v (3 * r) + a)
  have hR (r : ℕ) (hr : r ∈ R) : 3 * r + 1 ≤ k := by
    have hh := mem_range.mp hr
    omega
  have hdisj {r s : ℕ} (hr : r ∈ R) (hs : s ∈ R) (hrs : r < s) : Disjoint (U r) (U s) := by
    rw [disjoint_left]
    intro y hy hz
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    obtain ⟨b, hb, hb'⟩ := mem_image.mp hz
    have h := hdiff (i := 3 * r) (j := 3 * s) (by omega) (by have hh := hR s hs; omega)
    apply h
    have hh : v (3 * s) - v (3 * r) = a + (-b) := by
      rw [sub_eq_add_neg]
      calc
        _ = (v (3 * s) + b) + (-v (3 * r) + -b) := by abel
        _ = _ := by rw [hb']; abel
    rw [hh, show (2 : ℕ) = 1 + 1 from rfl, add_nsmul, one_nsmul]
    exact mem_add.mpr ⟨a, ha, -b, hneg b hb, rfl⟩
  have hcover : R.biUnion U ⊆ k • A := by
    intro y hy
    obtain ⟨r, hr, hmem⟩ := mem_biUnion.mp hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hmem
    apply nsmul_mono_of_zero_mem A h₀ (hR r hr)
    change v (3 * r) + a ∈ (3 * r + 1) • A
    rw [add_nsmul, one_nsmul]
    exact mem_add.mpr ⟨_, hv (3 * r), a, ha, rfl⟩
  have hc : (R.biUnion U).card = ((k + 2) / 3) * A.card := by
    rw [card_biUnion]
    · have hU (r : ℕ) : (U r).card = A.card :=
        card_image_of_injective _ (add_right_injective _)
      simp [hU, R]
    · intro r hr s hs hrs
      rcases hrs.lt_or_gt with h | h
      · exact hdisj hr hs h
      · exact (hdisj hs hr h).symm
  have hcard : ((k + 2) / 3) * A.card ≤ (k • A).card := hc ▸ card_le_card hcover
  have hceil : k ≤ 3 * ((k + 2) / 3) := by omega
  have hmul : k * A.card ≤ 3 * (k • A).card := by
    have h := Nat.mul_le_mul_right A.card hceil
    rw [Nat.mul_assoc] at h
    exact h.trans (Nat.mul_le_mul_left 3 hcard)
  apply (le_div_iff₀ (by exact_mod_cast hk : 0 < (k : ℝ))).mpr
  rw [mul_comm (A.card : ℝ)]
  exact_mod_cast hmul

end BooleanThreshold
