module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Union

@[expose] public section

open scoped BigOperators Classical

namespace BooleanThreshold

/-- At each step test the next input and update the state using only the inputs
seen so far. -/
def acceptsAdaptivePath {State Input : Type*} :
    {m : ℕ} → (Fin m → State → Input → State) → (Fin m → State → Input → Prop) →
      State → (Fin m → Input) → Prop
  | 0, _, _, _, _ => True
  | _m + 1, step, test, s, x =>
    test 0 s (x 0) ∧ acceptsAdaptivePath (Fin.tail step) (Fin.tail test) (step 0 s (x 0)) (Fin.tail x)

private def consEmbedding {m : ℕ} {Input : Type*} (z : Input) :
    (Fin m → Input) ↪ (Fin (m + 1) → Input) :=
  ⟨Fin.cons (α := fun _ : Fin (m + 1) => Input) z, fun _ _ h => by
    simpa only [Fin.tail_cons] using congrArg (fun v : Fin (m + 1) → Input => Fin.tail v) h⟩

/-- If the test on each coordinate accepts at most a prescribed number of
inputs after any admissible prefix, those numbers bound the total by their
product. -/
theorem card_acceptsAdaptivePath_le {State Input : Type*} [DecidableEq Input] {m : ℕ}
    (step : Fin m → State → Input → State) (test : Fin m → State → Input → Prop)
    (U : State → Prop) (hU : ∀ i s x, U s → U (step i s x))
    (B : Fin m → Finset Input) (d : Fin m → ℕ)
    (htest : ∀ i s, U s → ((B i).filter (test i s)).card ≤ d i)
    (s : State) (hs : U s) :
    ((Fintype.piFinset B).filter (acceptsAdaptivePath step test s)).card ≤ ∏ i, d i := by
  induction m generalizing s with
  | zero =>
    rw [Fin.prod_univ_zero]
    refine (Finset.card_le_card (Finset.subset_univ _)).trans ?_
    simp
  | succ m ih =>
    let B₀ := (B 0).filter (test 0 s)
    let A (z : Input) := (Fintype.piFinset (Fin.tail B)).filter
      (acceptsAdaptivePath (Fin.tail step) (Fin.tail test) (step 0 s z))
    have hsub : ((Fintype.piFinset B).filter (acceptsAdaptivePath step test s)) ⊆
        B₀.biUnion (fun z => (A z).map (consEmbedding z)) := by
      intro y hy
      obtain ⟨hy₀, hy'⟩ := Finset.mem_filter.mp hy
      obtain ⟨hfirst, htail⟩ := by simpa only [acceptsAdaptivePath] using hy'
      refine Finset.mem_biUnion.mpr ⟨y 0, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hy₀ 0, hfirst⟩, ?_⟩
      refine Finset.mem_map.mpr ⟨Fin.tail y, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, htail⟩,
        Fin.cons_self_tail y⟩
      exact fun i => Fintype.mem_piFinset.mp hy₀ i.succ
    have hA (z : Input) : (A z).card ≤ ∏ i : Fin m, d i.succ :=
      ih (Fin.tail step) (Fin.tail test) (fun i => hU i.succ) (Fin.tail B) (Fin.tail d) (fun i => htest i.succ)
        (step 0 s z) (hU 0 s z hs)
    rw [Fin.prod_univ_succ]
    calc
      _ ≤ (B₀.biUnion (fun z => (A z).map (consEmbedding z))).card := Finset.card_le_card hsub
      _ ≤ ∑ z ∈ B₀, (A z).card := by
        simpa only [Finset.card_map] using
          (Finset.card_biUnion_le (s := B₀) (t := fun z => (A z).map (consEmbedding z)))
      _ ≤ ∑ _z ∈ B₀, ∏ i : Fin m, d i.succ := Finset.sum_le_sum fun z _ => hA z
      _ = B₀.card * ∏ i : Fin m, d i.succ := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (htest 0 s hs)

end BooleanThreshold
