import EpsilonCohomology.ManifoldEmbedding

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

abbrev Xε := X × ℝ × ℝ

def doubleCoverEmbedding (x : X) : Xε X := embedding_ι X x

def pullback_ι {A : Type*} (f : Xε X → A) : X → A :=
  fun x => f (doubleCoverEmbedding X x)

theorem pullback_ι_comp (f : Xε X → ℝ) :
    pullback_ι X f = fun x => f (embedding_ι X x) := by
  rfl

end EpsilonCohomology
