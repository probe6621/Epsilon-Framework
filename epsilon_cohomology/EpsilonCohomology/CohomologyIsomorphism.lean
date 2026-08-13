import EpsilonCohomology.ZeroDefectCohomologyDescent

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

/-- The comparison map from doubled-space cohomology to base cohomology under zero defect. -/
def comparisonLinearMap (k : ℕ) :
    CohomologyClass k (X × ℝ × ℝ) → CohomologyClass k X :=
  inducedCohomologyMap (X := X) k

/-- The comparison map is the pullback along the canonical embedding. -/
theorem zero_defect_comparison_preserves_classes (k : ℕ) (f : X × ℝ × ℝ → ℝ) :
    comparisonLinearMap (X := X) k ⟦f⟧ = ⟦pullbackForm (X := X) f⟧ := by
  rfl

/-- Injectivity under the class-equivalence hypothesis. -/
lemma comparison_map_injective (k : ℕ)
    (h_eq : ∀ {ω η : X × ℝ × ℝ → ℝ},
      comparisonLinearMap (X := X) k ⟦ω⟧ = comparisonLinearMap (X := X) k ⟦η⟧ →
        FormRelation (X × ℝ × ℝ) ω η) :
    Function.Injective (comparisonLinearMap (X := X) k) := by
  intro a b hab
  rcases Quotient.exists_rep a with ⟨ω, rfl⟩
  rcases Quotient.exists_rep b with ⟨η, rfl⟩
  exact Quotient.sound (h_eq hab)

/-- Surjectivity under the representative hypothesis. -/
lemma comparison_map_surjective_rep (k : ℕ)
    (hSurj : ∀ (η : X → ℝ), ∃ ω : X × ℝ × ℝ → ℝ, pullbackForm (X := X) ω = η) :
    Function.Surjective (comparisonLinearMap (X := X) k) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro η
  obtain ⟨ω, hw⟩ := hSurj η
  refine ⟨⟦ω⟧, ?_⟩
  change ⟦pullbackForm (X := X) ω⟧ = ⟦η⟧
  rw [hw]

/-- Unified bijectivity statement for the comparison map. -/
theorem zero_defect_comparison_bijective (k : ℕ)
    (hEq : ∀ {ω η : X × ℝ × ℝ → ℝ},
      comparisonLinearMap (X := X) k ⟦ω⟧ = comparisonLinearMap (X := X) k ⟦η⟧ →
      FormRelation (X × ℝ × ℝ) ω η)
    (hSurj : ∀ (η : X → ℝ), ∃ ω : X × ℝ × ℝ → ℝ, pullbackForm (X := X) ω = η) :
    Function.Bijective (comparisonLinearMap (X := X) k) := by
  constructor
  · exact comparison_map_injective (X := X) k hEq
  · exact comparison_map_surjective_rep (X := X) k hSurj

end EpsilonCohomology
