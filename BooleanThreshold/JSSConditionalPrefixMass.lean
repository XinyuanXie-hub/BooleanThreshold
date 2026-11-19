module

public import BooleanThreshold.JSSConditionalBandPairs
public import BooleanThreshold.JSSConditionalLocalMass

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace BooleanThreshold

/-- A single coordinate order makes the local slice mass bound hold at every
long prefix, uniformly in the box points used by the prefix. -/
theorem oppositeBandBox_prefix_local_mass_eventually {η τ σ : ℝ}
    (hη : 0 < η) (hτ : 0 < τ) (hσ : 0 < σ) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (N B k : ℕ) (α : ℝ) (W : Fin n → Finset ℤ), 0 < N →
        oppositeBandBox n N B α W → τ * (n : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ α * (n : ℝ) →
        ∃ π : Equiv.Perm (Fin n),
          ∀ (ℓ : ℕ) (hℓ : ℓ ≤ n), σ * (n : ℝ) ≤ (ℓ : ℝ) → 2 * k ≤ ℓ →
          ∀ m : Fin (ℓ + 1), η * (ℓ : ℝ) ≤ m.val → (m.val : ℝ) ≤ (1 - η) * (ℓ : ℝ) →
          ∀ (P : ℕ) [NeZero P], 4 * n ^ 2 * N < P →
          ∀ a : ℕ → ℤ, (∀ i : Fin ℓ, a i.val ∈ W (π (Fin.castLEEmb hℓ i))) →
          ∀ f : ZMod P → ℝ, (∀ z, 0 ≤ f z) → (∑ z, f z) ≤ 1 → ∀ u : ZMod P,
          (∑ t ∈ cyclicInterval P N u, sliceAverage (fun i => (a i : ZMod P)) f ℓ m.val t) ≤
            C / Real.sqrt (n : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := sliceAverage_cyclic_local_mass_eventually hη hτ
  obtain ⟨L, hL⟩ := eventually_atTop.mp hlocal
  obtain ⟨A, hA⟩ := exists_nat_ge ((L : ℝ) / σ)
  refine ⟨C / Real.sqrt σ, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max A 1)] with n hn
  intro N B k α W hN hbox hkn hk
  obtain ⟨π, hπ⟩ := oppositeBandBox_exists_ordered_prefix hbox hN hk
  refine ⟨π, fun ℓ hℓ hℓn hkℓ m hml hmu P _ hP a ha f hf hf₁ u => ?_⟩
  have hℓL : L ≤ ℓ := by
    have hh : (L : ℝ) ≤ (n : ℝ) * σ :=
      (div_le_iff₀ hσ).mp (hA.trans (by exact_mod_cast (le_max_left A 1).trans hn))
    rw [mul_comm] at hh
    exact_mod_cast hh.trans hℓn
  have hk' : τ * (ℓ : ℝ) ≤ k :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hℓ) hτ.le).trans hkn
  obtain ⟨ha₁, ha₂⟩ := hπ ℓ hℓ hkℓ a ha
  have h := hL ℓ hℓL k (prefixAdjacentPairEmbedding hkℓ) m hk' hml hmu n P N hℓ hN hP a ha₁ ha₂
    f hf hf₁ u
  have hRoot : Real.sqrt σ * Real.sqrt (n : ℝ) ≤ Real.sqrt (ℓ : ℝ) := by
    rw [← Real.sqrt_mul hσ.le]
    exact Real.sqrt_le_sqrt hℓn
  refine h.trans ?_
  rw [div_div]
  have hn' : 0 < n := by omega
  exact div_le_div_of_nonneg_left hC.le (by positivity) hRoot

end BooleanThreshold
