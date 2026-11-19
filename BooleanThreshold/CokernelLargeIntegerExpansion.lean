module

public import BooleanThreshold.CokernelLargeProgressions
public import Mathlib.Combinatorics.Additive.CauchyDavenport
public import Mathlib.Data.Nat.Prime.Factorial

public section

open Finset
open scoped BigOperators Pointwise

namespace BooleanThreshold

private def boundedRelationsFree {p : ℕ} (G : Finset (ZMod p)) (L : ℕ) : Prop :=
  ∀ z : ZMod p → ℤ, (∀ j ∈ G, |z j| ≤ (L : ℤ)) →
    (∑ j ∈ G, (z j : ZMod p) * j) = 0 → ∀ j ∈ G, z j = 0

private theorem boundedRelationsFree.mono {p L : ℕ} [Fact p.Prime]
    {G H : Finset (ZMod p)} (hG : boundedRelationsFree G L) (hHG : H ⊆ G) :
    boundedRelationsFree H L := by
  classical
  intro z hz hsum j hj
  let z' (c : ZMod p) := if c ∈ H then z c else 0
  have hsum' : (∑ c ∈ G, (z' c : ZMod p) * c) = 0 := by
    rw [← Finset.sum_subset hHG (fun c _ hc => by simp [z', hc])]
    simpa only [z', Finset.sum_ite, Int.cast_ite] using
      (show (∑ c ∈ H, (z' c : ZMod p) * c) = 0 by
        refine (Finset.sum_congr rfl (fun c hc => ?_)).trans hsum
        simp [z', hc])
  have hb (c : ZMod p) (hc : c ∈ G) : |z' c| ≤ (L : ℤ) := by
    by_cases he : c ∈ H
    · simpa [z', he] using hz c he
    · simp [z', he]
  simpa only [z', ite_eq_left hj] using hG z' hb hsum' j (hHG hj)

private theorem nsmul_mem_sumset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} {x : G} (hx : x ∈ A) (k : ℕ) : k • x ∈ k • A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, succ_nsmul]
    exact Finset.mem_add.mpr ⟨_, ih, _, hx, rfl⟩

private theorem weighted_sum_mem_sumset {p : ℕ} [Fact p.Prime] {A G : Finset (ZMod p)}
    (hG : G ⊆ A) (z : ZMod p → ℕ) :
    (∑ g ∈ G, (z g : ZMod p) * g) ∈ (∑ g ∈ G, z g) • A := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | insert g G hg ih =>
    rw [Finset.sum_insert hg, Finset.sum_insert hg, add_nsmul]
    apply Finset.mem_add.mpr
    exact ⟨_, by simpa only [nsmul_eq_mul] using nsmul_mem_sumset (hG (mem_insert_self _ _)) (z g),
      _, ih fun x hx => hG (mem_insert_of_mem hx), rfl⟩

private theorem card_le_sumset_of_boundedRelationsFree {p L k : ℕ} [Fact p.Prime]
    {A G : Finset (ZMod p)} (h0 : 0 ∈ A) (hGA : G ⊆ A) (hG : boundedRelationsFree G L)
    (hk : G.card * L ≤ k) : (L + 1) ^ G.card ≤ (k • A).card := by
  classical
  let ofBox (z : G → Fin (L + 1)) (g : ZMod p) := if hg : g ∈ G then (z ⟨g, hg⟩).val else 0
  let eval (z : G → Fin (L + 1)) := ∑ g ∈ G, (ofBox z g : ZMod p) * g
  have hm (z : G → Fin (L + 1)) : eval z ∈ k • A := by
    have hz := weighted_sum_mem_sumset hGA (ofBox z)
    have hsum : ∑ g ∈ G, ofBox z g ≤ G.card * L := by
      calc
        _ ≤ ∑ _g ∈ G, L := Finset.sum_le_sum (fun g hg => by
          simpa only [ofBox, dite_eq_left hg] using Nat.lt_succ_iff.mp (z ⟨g, hg⟩).isLt)
        _ = _ := by simp
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hsum.trans hk)
    rw [hd, add_nsmul]
    exact Finset.mem_add.mpr ⟨eval z, hz, 0, by simpa using nsmul_mem_sumset h0 d, add_zero _⟩
  have hi : Function.Injective eval := by
    intro u v huv
    let z (g : ZMod p) : ℤ := (ofBox u g : ℤ) - (ofBox v g : ℤ)
    have hz (g : ZMod p) (hg : g ∈ G) : |z g| ≤ (L : ℤ) := by
      have hu : (ofBox u g : ℤ) ≤ (L : ℤ) := by
        exact_mod_cast (show ofBox u g ≤ L from by
          simpa only [ofBox, dite_eq_left hg] using Nat.lt_succ_iff.mp (u ⟨g, hg⟩).isLt)
      have hv : (ofBox v g : ℤ) ≤ (L : ℤ) := by
        exact_mod_cast (show ofBox v g ≤ L from by
          simpa only [ofBox, dite_eq_left hg] using Nat.lt_succ_iff.mp (v ⟨g, hg⟩).isLt)
      rw [abs_le]
      dsimp [z]
      omega
    have hrel : (∑ g ∈ G, (z g : ZMod p) * g) = 0 := by
      simp only [z, Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib]
      change eval u - eval v = 0
      rw [huv, sub_self]
    funext g
    apply Fin.ext
    have hg := hG z hz hrel g.val g.prop
    simpa [z, ofBox, g.prop, sub_eq_zero] using hg
  let f (z : G → Fin (L + 1)) : (k • A : Finset (ZMod p)) := ⟨eval z, hm z⟩
  have hf : Function.Injective f := fun u v h => hi (congrArg Subtype.val h)
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

/-- A small iterated sumset gives bounded integer coordinates after clearing
denominators in a maximal family with no relation of bounded height. -/
theorem exists_integer_expansion_of_small_sumset {p k D L : ℕ} [Fact p.Prime]
    {A : Finset (ZMod p)} (h0 : 0 ∈ A) (hk : D * L ≤ k)
    (hsmall : (k • A).card < (L + 1) ^ D) :
    ∃ G : Finset (ZMod p), G ⊆ A ∧ G.card < D ∧
      ∀ x ∈ A, ∃ z : G → ℤ, (∀ g, |z g| ≤ (L.factorial : ℤ) * (L + 1)) ∧
        (∑ g : G, (z g : ZMod p) * g.val) = (L.factorial : ZMod p) * x := by
  classical
  let sets := A.powerset.filter (fun G => boundedRelationsFree G L)
  have hsets : sets.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨mem_powerset.mpr (empty_subset _), fun _ _ _ _ h => False.elim (Finset.notMem_empty _ h)⟩⟩
  obtain ⟨G, hG, hmax⟩ := Finset.exists_max_image sets Finset.card hsets
  obtain ⟨hGA, hGfree⟩ := mem_filter.mp hG
  have hsub : G ⊆ A := mem_powerset.mp hGA
  have hD : G.card < D := by
    by_contra! hle
    obtain ⟨H, hHG, hH⟩ := Finset.exists_subset_card_eq hle
    have hb := card_le_sumset_of_boundedRelationsFree (k := k) h0 (hHG.trans hsub)
      (hGfree.mono hHG) (by rw [hH]; exact hk)
    rw [hH] at hb
    exact hsmall.not_ge hb
  refine ⟨G, hsub, hD, fun x hx => ?_⟩
  by_cases hxG : x ∈ G
  · let z (g : G) : ℤ := if g.val = x then L.factorial else 0
    refine ⟨z, fun g => ?_, ?_⟩
    · unfold z
      split
      · rw [abs_of_nonneg (Int.natCast_nonneg _)]
        exact le_mul_of_one_le_right (Int.natCast_nonneg _) (by omega)
      · simp
    · rw [Finset.sum_eq_single (⟨x, hxG⟩ : G)]
      · simp [z]
      · intro g hg hne
        have hnx : g.val ≠ x := fun h => hne (Subtype.ext h)
        simp [z, hnx]
      · simp
  · have hfree : ¬ boundedRelationsFree (insert x G) L := by
      intro h
      have hmem : insert x G ∈ sets :=
        mem_filter.mpr ⟨mem_powerset.mpr (by simp only [Finset.insert_subset_iff, hx, hsub, and_self]), h⟩
      have hc := hmax (insert x G) hmem
      rw [card_insert_of_notMem hxG] at hc
      omega
    unfold boundedRelationsFree at hfree
    push Not at hfree
    obtain ⟨u, hu, hu₀, g, hg, hgn⟩ := hfree
    rw [Finset.sum_insert hxG] at hu₀
    have hux : u x ≠ 0 := by
      intro hzero
      have hrest : (∑ g ∈ G, (u g : ZMod p) * g) = 0 := by simpa [hzero] using hu₀
      rcases mem_insert.mp hg with rfl | hg
      · exact hgn hzero
      · exact hgn (hGfree u (fun j hj => hu j (mem_insert_of_mem hj)) hrest g hg)
    have hdvd : u x ∣ (L.factorial : ℤ) := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      apply Nat.dvd_factorial (Int.natAbs_pos.mpr hux)
      have h := hu x (mem_insert_self _ _)
      exact_mod_cast (Int.natCast_natAbs (u x) ▸ h)
    obtain ⟨b, hb⟩ := hdvd
    have hbabs : |b| ≤ (L.factorial : ℤ) := by
      have h := congrArg (fun n : ℤ => |n|) hb
      simp only [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)] at h
      have huone : 1 ≤ |u x| := Int.add_one_le_iff.mpr (abs_pos.mpr hux)
      exact h.symm ▸ le_mul_of_one_le_left (abs_nonneg b) huone
    let z (g : G) : ℤ := (-b) * u g.val
    refine ⟨z, fun g => ?_, ?_⟩
    · rw [show z g = (-b) * u g.val from rfl, abs_mul, abs_neg]
      apply mul_le_mul hbabs _ (abs_nonneg _) (Int.natCast_nonneg _)
      exact (hu g.val (mem_insert_of_mem g.prop)).trans (by omega)
    · have huc : (∑ g ∈ G, (u g : ZMod p) * g) = -((u x : ZMod p) * x) :=
        eq_neg_of_add_eq_zero_right hu₀
      have huG : (∑ g : G, (u g.val : ZMod p) * g.val) = -((u x : ZMod p) * x) := by
        rw [Finset.sum_coe_sort (f := fun g : ZMod p => (u g : ZMod p) * g)]
        exact huc
      calc
        _ = (-b : ZMod p) * ∑ g : G, (u g.val : ZMod p) * g.val := by
          simp only [z, Int.cast_mul, Int.cast_neg, Finset.mul_sum, mul_assoc]
        _ = (L.factorial : ZMod p) * x := by
          have hb' : (L.factorial : ZMod p) = (u x : ZMod p) * (b : ZMod p) := by
            simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun n : ℤ => (n : ZMod p)) hb
          rw [huG, hb']
          ring

end BooleanThreshold
