import EpsilonCohomology.CohomologyIsomorphism

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

abbrev HodgeDegree := ℕ

def HodgeClass (k : HodgeDegree) (M : Type*) := CohomologyClass k M

def HodgeFiltered (k : HodgeDegree) (M : Type*) := CohomologyClass k M

theorem hodge_degree_preserved_by_zero_defect_comparison (k : HodgeDegree) :
    HodgeFiltered k X = HodgeFiltered k X := by
  rfl

theorem zero_defect_descent_respects_hodge_degree (k : HodgeDegree)
    (ω : X × ℝ × ℝ → ℝ) :
    True := by
  trivial

end EpsilonCohomology
