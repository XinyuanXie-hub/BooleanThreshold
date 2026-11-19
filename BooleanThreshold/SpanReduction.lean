module

public import BooleanThreshold.SignMeasure
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

public section

open Function Set Submodule

namespace BooleanThreshold

abbrev realSignVector {n : ℕ} := @realSigns n

/-- A family has closed sign span if it is independent and its only sign
vectors in the span are the family members and their negatives. -/
@[expose] def SignSpanGood {ι : Type*} {n : ℕ} (v : ι → Fin n → Bool) : Prop :=
  LinearIndependent ℝ (realSigns ∘ v) ∧
    ∀ x : Fin n → Bool, realSigns x ∈ span ℝ (range (realSigns ∘ v)) →
      ∃ i, realSigns x = realSigns (v i) ∨
        realSigns x = -realSigns (v i)

/-- Restricting an independent family preserves the absence of extra signs. -/
theorem SignSpanGood.comp {ι κ : Type*} {n : ℕ} {v : ι → Fin n → Bool} (e : κ ↪ ι)
    (h : SignSpanGood v) : SignSpanGood (v ∘ e) := by
  refine ⟨h.1.comp e e.injective, fun x hx => ?_⟩
  have hm : span ℝ (range (realSigns ∘ v ∘ e)) ≤
      span ℝ (range (realSigns ∘ v)) :=
    span_mono (range_comp_subset_range e (realSigns ∘ v))
  obtain ⟨i, hi⟩ := h.2 x (hm hx)
  have hm' : realSigns (v i) ∈ span ℝ (range (realSigns ∘ v ∘ e)) := by
    rcases hi with hi | hi
    · rwa [hi] at hx
    · rw [hi] at hx
      simpa using neg_mem hx
  have hi' : i ∈ range e := by
    by_contra hnot
    change realSigns (v i) ∈ span ℝ (range ((realSigns ∘ v) ∘ e)) at hm'
    rw [range_comp] at hm'
    exact h.1.notMem_span_image hnot hm'
  obtain ⟨j, rfl⟩ := hi'
  exact ⟨j, hi⟩

/-- Discard the first coordinate after multiplying all coordinates by it. -/
@[expose] def normalizeVertex {n : ℕ} (x : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun j => !(x 0 ^^ x j.succ)

/-- The real vector obtained by adding a leading positive sign. -/
@[expose] def liftSignVertex {n : ℕ} (x : Fin n → Bool) : Fin (n + 1) → ℝ :=
  Fin.cons 1 (realSigns x)

theorem liftSignVertex_injective (n : ℕ) : Injective (@liftSignVertex n) := by
  intro x y h
  apply realSigns_injective n
  exact congrArg Fin.tail h

theorem liftSignVertex_normalizeVertex {n : ℕ} (x : Fin (n + 1) → Bool) :
    liftSignVertex (normalizeVertex x) = realSigns x 0 • realSigns x := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · cases h : x 0 <;> norm_num [liftSignVertex, realSigns, h]
  · cases h : x 0 <;> cases hi : x i.succ <;>
      norm_num [liftSignVertex, normalizeVertex, realSigns, h, hi]

private theorem normalizeVertex_cons {n : ℕ} (x : Fin n → Bool) :
    normalizeVertex (Fin.cons true x) = x := by
  funext i
  cases hi : x i <;> simp [normalizeVertex, hi]

/-- The first-coordinate normalization takes a good sign family to a
linearly independent family which contains every lifted vertex in its span. -/
theorem SignSpanGood.normalize {ι : Type*} {n : ℕ} {v : ι → Fin (n + 1) → Bool}
    (h : SignSpanGood v) :
    let w := normalizeVertex ∘ v
    LinearIndependent ℝ (liftSignVertex ∘ w) ∧
      ∀ x : Fin n → Bool, liftSignVertex x ∈ span ℝ (range (liftSignVertex ∘ w)) ↔
        x ∈ range w := by
  let w := normalizeVertex ∘ v
  let a (i : ι) := realSigns (v i) 0
  have ha (i : ι) : a i * a i = 1 := by
    cases h' : v i 0 <;> norm_num [a, realSigns, h']
  let u (i : ι) : ℝˣ := Units.mk0 (a i) (fun h' => by
    have hi := ha i
    rw [h', zero_mul] at hi
    exact zero_ne_one hi)
  have hw (i : ι) : liftSignVertex (w i) = a i • realSigns (v i) :=
    liftSignVertex_normalizeVertex (v i)
  have hs : span ℝ (range (liftSignVertex ∘ w)) = span ℝ (range (realSigns ∘ v)) := by
    apply le_antisymm <;> rw [span_le] <;> rintro _ ⟨i, rfl⟩
    · change liftSignVertex (w i) ∈ _
      rw [hw]
      exact smul_mem _ _ (subset_span (mem_range_self i))
    · change realSigns (v i) ∈ _
      have hv : a i • liftSignVertex (w i) = realSigns (v i) := by
        rw [hw, ← mul_smul, ha, one_smul]
      rw [← hv]
      exact smul_mem _ _ (subset_span (mem_range_self i))
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · have hLI := h.1.units_smul u
    convert hLI using 1
    funext i
    exact hw i
  · intro hx
    have he : realSigns (Fin.cons true x) = liftSignVertex x := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [realSigns, liftSignVertex]
    rw [hs, ← he] at hx
    obtain ⟨i, hi⟩ := h.2 _ hx
    refine ⟨i, liftSignVertex_injective n ?_⟩
    change liftSignVertex (normalizeVertex (v i)) = liftSignVertex x
    rw [← normalizeVertex_cons x, liftSignVertex_normalizeVertex, liftSignVertex_normalizeVertex]
    rcases hi with hi | hi
    · rw [hi]
    · simp [hi]
  · rintro ⟨i, rfl⟩
    exact subset_span (mem_range_self i)

private theorem not_xor_not_xor (b x : Bool) : (!(b ^^ !(b ^^ x))) = x := by
  cases b <;> cases x <;> rfl

/-- Conditioning on the signs of the first coordinates leaves the normalized
tails unconstrained. -/
@[expose] def signFamilyCoordinates (n r : ℕ) :
    (Fin r → Fin (n + 1) → Bool) ≃ (Fin r → Bool) × (Fin r → Fin n → Bool) where
  toFun v := (fun i => v i 0, fun i => normalizeVertex (v i))
  invFun z i := Fin.cons (z.1 i) (fun j => !(z.1 i ^^ z.2 i j))
  left_inv v := by
    funext i j
    refine Fin.cases rfl (fun k => ?_) j
    exact not_xor_not_xor _ _
  right_inv z := by
    apply Prod.ext
    · rfl
    · funext i j
      exact not_xor_not_xor _ _

/-- The preimage of an event for normalized families has a constant factor
of two choices per vector. -/
theorem card_normalizedFamily_preimage (n r : ℕ) (s : Set (Fin r → Fin n → Bool)) :
    Nat.card {v : Fin r → Fin (n + 1) → Bool // (fun i => normalizeVertex (v i)) ∈ s} = 2 ^ r * Nat.card s := by
  let e := signFamilyCoordinates n r
  let e' : {v // (e v).2 ∈ s} ≃ (Fin r → Bool) × s :=
    { toFun := fun v => ((e v).1, ⟨(e v).2, v.2⟩)
      invFun := fun z => ⟨e.symm (z.1, z.2), by simp⟩
      left_inv := by intro v; simp
      right_inv := by rintro ⟨z, x, hx⟩; simp }
  change Nat.card {v // (e v).2 ∈ s} = 2 ^ r * Nat.card s
  rw [Nat.card_congr e', Nat.card_prod, Nat.card_fun, Nat.card_fin]
  norm_num [Nat.card_eq_fintype_card]


/-- Normalization can only lower the proportion of families with bad sign span. -/
theorem card_badNormalized_mul_le (n r : ℕ) :
    2 ^ r * Nat.card {w : Fin r → Fin n → Bool //
      ¬ (LinearIndependent ℝ (liftSignVertex ∘ w) ∧
        ∀ x : Fin n → Bool, liftSignVertex x ∈ span ℝ (range (liftSignVertex ∘ w)) →
          x ∈ range w)} ≤
      Nat.card {v : Fin r → Fin (n + 1) → Bool // ¬ SignSpanGood v} := by
  let s : Set (Fin r → Fin n → Bool) := {w |
    ¬ (LinearIndependent ℝ (liftSignVertex ∘ w) ∧
      ∀ x : Fin n → Bool, liftSignVertex x ∈ span ℝ (range (liftSignVertex ∘ w)) →
        x ∈ range w)}
  change 2 ^ r * Nat.card s ≤ _
  rw [← card_normalizedFamily_preimage n r s]
  let f : {v : Fin r → Fin (n + 1) → Bool // (fun i => normalizeVertex (v i)) ∈ s} →
      {v : Fin r → Fin (n + 1) → Bool // ¬ SignSpanGood v} := fun v =>
    ⟨v.1, fun h => v.2 ⟨h.normalize.1, fun x => (h.normalize.2 x).1⟩⟩
  apply Nat.card_le_card_of_injective f
  intro _ _ h
  exact Subtype.ext (congrArg (fun z : {v : Fin r → Fin (n + 1) → Bool // ¬ SignSpanGood v} =>
    z.val) h)

end BooleanThreshold
