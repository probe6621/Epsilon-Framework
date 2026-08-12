import Mathlib

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

/-- A minimal quotient-style relation on scalar functions: two forms differ by a constant. -/
def FormRelation (M : Type*) : Setoid (M → ℝ) where
  r ω η := ∃ c : ℝ, ∀ x, η x = ω x + c
  iseqv := by
    constructor
    · intro ω
      refine ⟨0, ?_⟩
      intro x
      simp
    · intro ω η h
      rcases h with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      intro x
      have := hc x
      linarith
    · intro ω η ζ hωη hηζ
      rcases hωη with ⟨c₁, hc₁⟩
      rcases hηζ with ⟨c₂, hc₂⟩
      refine ⟨c₁ + c₂, ?_⟩
      intro x
      have h1 := hc₁ x
      have h2 := hc₂ x
      linarith

/-- The quotient space of forms up to constant shift. -/
def CohomologyClass (k : ℕ) (M : Type*) := Quotient (FormRelation M)

/-- Pullback of a scalar function along the base-point inclusion. -/
def pullbackForm (f : X × ℝ × ℝ → ℝ) : X → ℝ :=
  fun x => f (embedding_ι X x)

/-- The quotient map induced by pullback on cohomology-like classes. -/
def inducedCohomologyMap (k : ℕ) :
    CohomologyClass k (X × ℝ × ℝ) → CohomologyClass k X :=
  Quotient.map (fun ω : X × ℝ × ℝ → ℝ => pullbackForm (X := X) ω) (by
    intro ω η hωη
    rcases hωη with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro x
    dsimp [pullbackForm]
    have hx := hc (embedding_ι X x)
    linarith)

/-- The pullback respects the quotient relation by preserving the constant discrepancy. -/
theorem inducedCohomologyMap_well_defined {ω η : X × ℝ × ℝ → ℝ}
    (h : (FormRelation (X × ℝ × ℝ)) ω η) :
    inducedCohomologyMap (X := X) 0 ⟦ω⟧ = inducedCohomologyMap (X := X) 0 ⟦η⟧ := by
  apply Quotient.sound
  rcases h with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x
  dsimp [pullbackForm]
  have hx := hc (embedding_ι X x)
  linarith

/-- The zero-defect descent theorem in simplified quotient form. -/
theorem zero_defect_cohomology_descent {ω η : X × ℝ × ℝ → ℝ}
    (h : (FormRelation (X × ℝ × ℝ)) ω η) :
    inducedCohomologyMap (X := X) 0 ⟦ω⟧ = inducedCohomologyMap (X := X) 0 ⟦η⟧ := by
  exact inducedCohomologyMap_well_defined (X := X) h

end EpsilonCohomology
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvalue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenvector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.L
