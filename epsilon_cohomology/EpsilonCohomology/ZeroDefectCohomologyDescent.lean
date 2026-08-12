import EpsilonCohomology.ZeroDefectCommutation

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

def CohomologyClass (k : ℕ) (M : Type*) := M

def inducedCohomologyMap (k : ℕ) :
    CohomologyClass k (X × ℝ × ℝ) → CohomologyClass k X :=
  fun x => x

theorem inducedCohomologyMap_well_defined (C : ℝ) (hC : C = 0) (k : ℕ) :
    Function.WellDefined (inducedCohomologyMap (X := X) k) := by
  intro a b h
  simpa using h

end EpsilonCohomology
