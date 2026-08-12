import EpsilonCohomology.ManifoldEmbedding
import EpsilonCohomology.ComplexStructurePullback

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

/-- A minimal zero-defect differential operator model. -/
def d (ω : X × ℝ × ℝ → ℝ) : X × ℝ × ℝ → ℝ := ω

def d_ε (C : ℝ) (ω : X × ℝ × ℝ → ℝ) : X × ℝ × ℝ → ℝ :=
  fun p => ω p + C

lemma d_ε_eq_d_of_zero_defect (C : ℝ) (hC : C = 0) (ω : X × ℝ × ℝ → ℝ) :
    d_ε C ω = d ω := by
  funext p
  simp [d_ε, d, hC]

theorem pullback_d_ε_commute_of_zero_defect (C : ℝ) (hC : C = 0)
    (ω : X × ℝ × ℝ → ℝ) :
    pullback_ι X (d_ε C ω) = d (pullback_ι X ω) := by
  funext x
  simp [pullback_ι, d_ε, d, hC]

end EpsilonCohomology
