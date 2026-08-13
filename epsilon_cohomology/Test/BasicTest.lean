import EpsilonCohomology.PlenumConstraints
import Mathlib.Testing.SlimCheck
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

open EpsilonCohomology

namespace EpsilonCohomology.Test

/-- Test that plenum floor axiom holds for toroidal coordinates -/
example : ∃ ε > 0, ∀ (Q : ToroidalCoords), ‖Q‖ ≥ ε := by
  have := plenum_floor ToroidalCoords
  simp [this]

/-- Test fractal scaling preserves harmonic forms -/
example (ω : GradedForm ToroidalCoords) (hω : isFractalHarmonic 0 1 ω) :
    isFractalHarmonic 0 1 (fractalScale 1 ω) := by
  apply fractalScale_preserves_harmonic 0 1 ω hω
  exact plenum_floor ToroidalCoords

end EpsilonCohomology.Test
