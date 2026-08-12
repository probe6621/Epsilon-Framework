import Mathlib

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

abbrev T2 := ℝ × ℝ
abbrev iT2 := T2
abbrev Xε := X × ℝ × ℝ

def embedding_ι (x : X) : Xε X := (x, 0, 0)

def J_ε (p : Xε X) : Xε X :=
  let x := p.1
  let a := p.2.1
  let b := p.2.2
  (x, -b, a)

theorem J_ε_sq (p : Xε X) :
    J_ε X (J_ε X p) = (p.1, -p.2.1, -p.2.2) := by
  rcases p with ⟨x, a, b⟩
  simp [J_ε]

def pullback_ι {A : Type*} (f : Xε X → A) : X → A :=
  fun x => f (embedding_ι X x)

end EpsilonCohomology
