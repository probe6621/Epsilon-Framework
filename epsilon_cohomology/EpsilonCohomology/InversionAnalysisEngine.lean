import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import EpsilonCohomology.HodgeGrading

/-!
# Inversion Analysis Engine

This module extends the verified toy Hodge scaffold with a strictly positive plenum
floor, a minimal inversion map, and a regularized potential with an explicit lower
bound.
-/
noncomputable section

namespace EpsilonCohomology
namespace InversionAnalysisEngine

/--
The Inversion Analysis Engine equips the toy Hodge scaffold with a strictly positive
regularization floor used to model inversion away from degenerate zero-radius behavior.
-/
class InversionPlenum where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon

variable [InversionPlenum]

/--
The inversion map rescales a radius by the square of the plenum floor.
This is the minimal algebraic inversion law used in the engine layer.
-/
def invMap (r : ℝ) (_hε : 0 < InversionPlenum.epsilon) : ℝ :=
  InversionPlenum.epsilon ^ 2 / r

/--
The regularized potential remains finite by replacing the singular origin with the
strictly positive plenum floor.
-/
def regularizedPotential (r : ℝ) : ℝ :=
  -(1 : ℝ) / Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2)

/--
The regularized potential is bounded below by the reciprocal of the plenum floor.
-/
theorem regularizedPotential_bounded (r : ℝ) :
    regularizedPotential r ≥ -(1 : ℝ) / InversionPlenum.epsilon := by
  dsimp [regularizedPotential]
  change
    -(1 : ℝ) / InversionPlenum.epsilon ≤
      -(1 : ℝ) / Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2)
  have hsq : InversionPlenum.epsilon ^ 2 ≤ r ^ 2 + InversionPlenum.epsilon ^ 2 := by
    nlinarith [sq_nonneg r]
  have hsqrt : InversionPlenum.epsilon ≤ Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2) := by
    have hsq' : InversionPlenum.epsilon ^ 2 ≤ (Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      exact hsq
    have hnonneg : 0 ≤ Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2) := Real.sqrt_nonneg _
    nlinarith
  have hrec : (1 : ℝ) / Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2) ≤
      (1 : ℝ) / InversionPlenum.epsilon := by
    exact one_div_le_one_div_of_le InversionPlenum.epsilon_pos hsqrt
  have hneg :
      -(1 / InversionPlenum.epsilon) ≤
        -(1 / Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2)) := by
    exact neg_le_neg hrec
  have hneg' : (-(1 : ℝ) / InversionPlenum.epsilon) ≤
      (-(1 : ℝ) / Real.sqrt (r ^ 2 + InversionPlenum.epsilon ^ 2)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hneg
  simpa using hneg'

end InversionAnalysisEngine
end EpsilonCohomology
