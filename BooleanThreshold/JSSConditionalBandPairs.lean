module

public import BooleanThreshold.JSSConditionalBoxes
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace BooleanThreshold

private theorem exists_disjoint_pair_embedding {α : Type*} (I J : Finset α) (h : Disjoint I J)
    (k : ℕ) (hI : k ≤ I.card) (hJ : k ≤ J.card) :
    ∃ e : Fin k × Bool ↪ α, (∀ i, e (i, false) ∈ I) ∧ ∀ i, e (i, true) ∈ J := by
  classical
  obtain ⟨l, hl⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin k) (s := I) (by simpa using hI)
  obtain ⟨r, hr⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin k) (s := J) (by simpa using hJ)
  have hL (i : Fin k) : l i ∈ I := hl ⟨i, rfl⟩
  have hR (i : Fin k) : r i ∈ J := hr ⟨i, rfl⟩
  let f (x : Fin k × Bool) : α := if x.2 then r x.1 else l x.1
  have hf : Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,b'⟩ hF
    cases b <;> cases b'
    · exact Prod.ext (l.injective hF) rfl
    · change l i = r j at hF
      exact (Finset.disjoint_left.mp h (hL i) (hF.symm ▸ hR j)).elim
    · change r i = l j at hF
      exact (Finset.disjoint_left.mp h (hL j) (hF ▸ hR i)).elim
    · exact Prod.ext (r.injective hF) rfl
  exact ⟨⟨f, hf⟩, hL, hR⟩

/-- Select as many disjoint opposite-band pairs as the box guarantees. -/
theorem oppositeBandBox_exists_pairs {n N B k : ℕ} {α : ℝ} {P : Fin n → Finset ℤ}
    (hbox : oppositeBandBox n N B α P) (hk : (k : ℝ) ≤ α * (n : ℝ)) :
    ∃ e : Fin k × Bool ↪ Fin n,
      (∀ i, ∀ u ∈ P (e (i, false)), u ≤ -2 * (N : ℤ)) ∧
      ∀ i, ∀ v ∈ P (e (i, true)), 2 * (N : ℤ) ≤ v := by
  obtain ⟨I, J, hI, hJ, h, hl, hr⟩ := hbox.2
  obtain ⟨e, heL, heR⟩ := exists_disjoint_pair_embedding I J h k
    (by exact_mod_cast hk.trans hI) (by exact_mod_cast hk.trans hJ)
  exact ⟨e, fun i u hu => (hl _ (heL i) u hu).2, fun i v hv => (hr _ (heR i) v hv).1⟩

/-- The adjacent positions of the pairs in a block of length `2 * k`. -/
def adjacentPairIndex (k : ℕ) : Fin k × Bool ≃ Fin (2 * k) :=
  ((Equiv.refl (Fin k)).prodCongr finTwoEquiv.symm).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2)))

@[simp] theorem adjacentPairIndex_val (k : ℕ) (i : Fin k) (b : Bool) :
    (adjacentPairIndex k (i,b)).val = 2 * i.val + (if b then 1 else 0) := by
  cases b <;> simp [adjacentPairIndex, finProdFinEquiv, finTwoEquiv, add_comm]

/-- A permutation moves any family of disjoint pairs into adjacent positions
at the beginning of the coordinate sequence. -/
theorem exists_pair_prefix_permutation {n k : ℕ} (e : Fin k × Bool ↪ Fin n) :
    ∃ h : 2 * k ≤ n, ∃ σ : Equiv.Perm (Fin n),
      ∀ i : Fin k × Bool, σ (Fin.castLEEmb h (adjacentPairIndex k i)) = e i := by
  have h : 2 * k ≤ n := by
    simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm] using
      Fintype.card_le_of_embedding e
  let f := (adjacentPairIndex k).toEmbedding.trans (Fin.castLEEmb h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f e f.injective e.injective
  exact ⟨h, σ, hσ⟩

/-- The reserved adjacent pairs, viewed in any prefix containing them. -/
def prefixAdjacentPairEmbedding {k ℓ : ℕ} (hk : 2 * k ≤ ℓ) : Fin k × Bool ↪ Fin ℓ :=
  (adjacentPairIndex k).toEmbedding.trans (Fin.castLEEmb hk)

/-- Adjacent pairs drawn from the coordinates after a chosen prefix. -/
def suffixAdjacentPairEmbedding {n ℓ k : ℕ} (hk : ℓ + 2 * k ≤ n) : Fin k × Bool ↪ Fin n :=
  (adjacentPairIndex k).toEmbedding.trans ((Fin.natAddEmb ℓ).trans (Fin.castLEEmb hk))

@[simp] theorem suffixAdjacentPairEmbedding_val {n ℓ k : ℕ} (hk : ℓ + 2 * k ≤ n)
    (i : Fin k) (b : Bool) :
    (suffixAdjacentPairEmbedding hk (i,b)).val = ℓ + (2 * i.val + (if b then 1 else 0)) := by
  change ℓ + (adjacentPairIndex k (i,b)).val = _
  rw [adjacentPairIndex_val]

theorem disjoint_prefix_suffixAdjacentPairs {n ℓ k : ℕ} (hk : ℓ + 2 * k ≤ n) :
    Disjoint (Set.range (Fin.castLEEmb (show ℓ ≤ n by omega)))
      (Set.range (suffixAdjacentPairEmbedding hk)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨i, rfl⟩ ⟨⟨j, b⟩, h⟩
  have hv := congrArg Fin.val h
  simp only [suffixAdjacentPairEmbedding_val, Fin.castLEEmb_apply, Fin.val_castLE] at hv
  omega

/-- Order a box so every sufficiently long prefix retains all the reserved
opposite-band pairs, together with the ambient coordinate bound. -/
theorem oppositeBandBox_exists_ordered_prefix {n N B k : ℕ} {α : ℝ} {P : Fin n → Finset ℤ}
    (hbox : oppositeBandBox n N B α P) (hN : 0 < N) (hk : (k : ℝ) ≤ α * (n : ℝ)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (ℓ : ℕ) (hℓ : ℓ ≤ n) (hkℓ : 2 * k ≤ ℓ) (a : ℕ → ℤ),
      (∀ i : Fin ℓ, a i.val ∈ P (σ (Fin.castLEEmb hℓ i))) →
      (∀ i : Fin ℓ, |a i.val| ≤ (n : ℤ) * (N : ℤ)) ∧
        ∀ j, 2 * (N : ℝ) <
          |(a (prefixAdjacentPairEmbedding hkℓ (j, false)).val : ℝ) -
            (a (prefixAdjacentPairEmbedding hkℓ (j, true)).val : ℝ)| := by
  obtain ⟨e, heL, heR⟩ := oppositeBandBox_exists_pairs hbox hk
  obtain ⟨hkn, σ, hσ⟩ := exists_pair_prefix_permutation e
  refine ⟨σ, fun ℓ hℓ hkℓ a ha => ⟨fun i => (hbox.1 _).2.2.2 _ (ha i), ?_⟩⟩
  intro j
  have he (i : Fin k × Bool) : σ (Fin.castLEEmb hℓ (prefixAdjacentPairEmbedding hkℓ i)) = e i := by
    have hi : Fin.castLEEmb hℓ (prefixAdjacentPairEmbedding hkℓ i) =
        Fin.castLEEmb hkn (adjacentPairIndex k i) := Fin.ext rfl
    rw [hi, hσ]
  have hL := ha (prefixAdjacentPairEmbedding hkℓ (j, false))
  have hR := ha (prefixAdjacentPairEmbedding hkℓ (j, true))
  rw [he] at hL hR
  have hL' : (a (prefixAdjacentPairEmbedding hkℓ (j, false)).val : ℝ) ≤ -2 * (N : ℝ) := by
    exact_mod_cast heL j _ hL
  have hR' : 2 * (N : ℝ) ≤ (a (prefixAdjacentPairEmbedding hkℓ (j, true)).val : ℝ) := by
    exact_mod_cast heR j _ hR
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact (show (2 : ℝ) * N < -((a (prefixAdjacentPairEmbedding hkℓ (j, false)).val : ℝ) -
      (a (prefixAdjacentPairEmbedding hkℓ (j, true)).val : ℝ)) by
    linarith only [hL', hR', hN']).trans_le (neg_le_abs _)

end BooleanThreshold
