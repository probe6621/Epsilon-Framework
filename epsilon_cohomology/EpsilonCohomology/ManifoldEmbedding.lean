import Mathlib

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

abbrev T2 := ℝ × ℝ
abbrev iT2 := T2
abbrev Xε := X × ℝ × ℝ

/-- The canonical base-point embedding into the doubled product space. -/
def embedding_ι (x : X) : Xε X := (x, 0, 0)

private lemma embedding_ι_apply (x : X) :
    embedding_ι (X := X) x = (x, 0, 0) := by
  rfl

/-- A minimal formal almost-complex action on the second factor. -/
def J_ε (p : Xε X) : Xε X :=
  let x := p.1
  let a := p.2.1
  let b := p.2.2
  (x, -b, a)

private lemma J_ε_step (p : Xε X) :
    J_ε X p = (p.1, -p.2.2, p.2.1) := by
  rcases p with ⟨x, a, b⟩
  simp [J_ε]

/-- The almost-complex square is the expected negative identity on the product coordinates. -/
theorem J_ε_sq (p : Xε X) :
    J_ε X (J_ε X p) = (p.1, -p.2.1, -p.2.2) := by
  rcases p with ⟨x, a, b⟩
  simp [J_ε, J_ε_step]

/-- Pullback along the embedding is evaluation on the base-point fiber. -/
def pullback_ι {A : Type*} (f : Xε X → A) : X → A :=
  fun x => f (embedding_ι X x)

private lemma pullback_ι_apply {A : Type*} (f : Xε X → A) (x : X) :
    pullback_ι (X := X) f x = f (embedding_ι X x) := by
  rfl

end EpsilonCohomology
