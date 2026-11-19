module

public import BooleanThreshold.JSSConditionalTail
public import BooleanThreshold.JSSStructuredNet
public import BooleanThreshold.JSSStructuredTensor

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

namespace BooleanThreshold

/-- For almost-constant kernel vectors with a uniform constant-radius small
ball bound, the net and independent row probabilities yield an explicit bound. -/
theorem uniformOn_cons_null_le_of_smallBall {m n k l : ℕ}
    (hn : 0 < n) (hl : l ≤ m) {δ ρ K θ : ℝ}
    (hρ : 0 ≤ ρ) (hθ : 0 < θ) {ε : ℝ≥0} (hε : 0 < ε)
    (hδk : δ * (n : ℝ) ≤ (k : ℝ))
    (hbudget : K ^ 2 * (m : ℝ) * (2 * (ρ + (ε : ℝ))) ^ 2 ≤ (l : ℝ) * θ ^ 2)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ almostConstantUnitVectors n δ ρ)
    {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hconc : ∀ a ∈ S, uniformOn Set.univ
      {row : Fin n → Bool | |signSum a row| ≤ θ} ≤ q) :
    (uniformOn Set.univ).real {M : Fin m → Fin n → Bool |
      signOpBound K M ∧ ∃ a ∈ S, signMatrixMap M a = 0} ≤
      (∑ s ∈ Finset.range (k + 1), (n.choose s : ℝ)) *
        (1 + 2 * (1 + ρ) / (ε : ℝ)) ^ (k + 1) *
        (m.choose l : ℝ) * q.toReal ^ (m - l) := by
  classical
  let E : Set (EuclideanSpace ℝ (Fin n)) := WithLp.ofLp ⁻¹' S
  obtain ⟨U, hUS, hcover, hUcard⟩ := exists_almostConstant_net hn hρ hδk hε E
    (fun _ ha => hS ha)
  let T : Finset (Fin n → ℝ) := U.image WithLp.ofLp
  have hTS (a : Fin n → ℝ) (ha : a ∈ T) : a ∈ S := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact hUS hx
  have hTcover (a : Fin n → ℝ) (ha : a ∈ S) :
      ∃ b ∈ T, squaredNorm (b - a) ≤ (2 * (ρ + (ε : ℝ))) ^ 2 := by
    obtain ⟨u, hu, hdist⟩ := hcover (WithLp.toLp 2 a) ha
    refine ⟨u.ofLp, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    rw [norm_sub_rev, EuclideanSpace.real_norm_sq_eq] at hsq
    exact hsq
  have h := uniformOn_null_probability_le_of_net hl hθ hbudget S T hTcover
    (fun a ha => hconc a (hTS a ha))
  have hfinite : (T.card : ℝ≥0∞) * (m.choose l : ℝ≥0∞) * q ^ (m - l) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (ENNReal.pow_ne_top hq)
  have habs := ENNReal.toReal_mono hfinite h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow] at habs
  refine habs.trans ?_
  have hTU : (T.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_image_le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hTU.trans hUcard) (Nat.cast_nonneg _)) (by positivity)

end BooleanThreshold
