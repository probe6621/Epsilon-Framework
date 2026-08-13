import EpsilonCohomology.ManifoldEmbedding

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

/-- Convenience alias for the canonical embedding used throughout the doubled-space framework. -/
def doubleCoverEmbedding (x : X) : Xε X := embedding_ι X x

/-- The canonical pullback is the one already defined in `ManifoldEmbedding`. -/
theorem pullback_ι_comp (f : Xε X → ℝ) :
    pullback_ι X f = fun x => f (embedding_ι X x) := by
  rfl

end EpsilonCohomology
