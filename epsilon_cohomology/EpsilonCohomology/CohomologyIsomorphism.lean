import Mathlib
import EpsilonCohomology.ZeroDefectCohomologyDescent

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

abbrev Xε := X × ℝ × ℝ

/-- The comparison linear map from doubled-space cohomology to base cohomology under zero defect. -/
def comparisonLinearMap (k : ℕ) : CohomologyClass k Xε → CohomologyClass k X :=
  inducedCohomologyMap (X := X) k

/-- The comparison map is just the pullback along the canonical embedding. -/
theorem zero_defect_comparison_preserves_classes (k : ℕ) (f : Xε → ℝ) :
    comparisonLinearMap (X := X) k ⟦f⟧ = ⟦pullbackForm (X := X) f⟧ := by
  rfl

/-- Injectivity lemma for the comparison map under the zero-defect class-equivalence hypothesis. -/
lemma comparison_map_injective (k : ℕ)
    (h_eq : ∀ {ω η : Xε → ℝ},
      comparisonLinearMap (X := X) k ⟦ω⟧ = comparisonLinearMap (X := X) k ⟦η⟧ →
        FormRelation Xε ω η) :
    Function.Injective (comparisonLinearMap (X := X) k) := by
  intro a b hab
  refine Quotient.inductionOn₂ a b ?_
  intro ω η h
  exact Quotient.sound (h_eq h)

/-- Surjectivity representative lemma for the comparison map under the pullback hypothesis. -/
lemma comparison_map_surjective_rep (k : ℕ)
    (hSurj : ∀ (η : X → ℝ), ∃ ω : Xε → ℝ, pullbackForm (X := X) ω = η) :
    Function.Surjective (comparisonLinearMap (X := X) k) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro η
  obtain ⟨ω, hw⟩ := hSurj η
  refine ⟨⟦ω⟧, ?_⟩
  simpa [comparisonLinearMap, inducedCohomologyMap, pullbackForm, hw]

end EpsilonCohomology

/-- Unified bijectivity statement for the comparison map under the explicit zero-defect support
hypotheses. -/
theorem zero_defect_comparison_bijective (k : ℕ)
    (hEq : ∀ {ω η : Xε → ℝ},
      comparisonLinearMap (X := X) k ⟦ω⟧ = comparisonLinearMap (X := X) k ⟦η⟧ →
      FormRelation Xε ω η)
    (hSurj : ∀ (η : X → ℝ), ∃ ω : Xε → ℝ, pullbackForm (X := X) ω = η) :
    Function.Bijective (comparisonLinearMap (X := X) k) := by
  constructor
  · exact comparison_map_injective (X := X) k hEq
  · exact comparison_map_surjective_rep (X := X) k hSurj

end EpsilonCohomology
