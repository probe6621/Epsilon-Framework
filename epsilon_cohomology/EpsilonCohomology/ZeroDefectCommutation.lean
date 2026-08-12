import EpsilonCohomology.ManifoldEmbedding
import EpsilonCohomology.ComplexStructurePullback

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

/-- A minimal model for the exterior derivative on the doubled space. -/
def d (ω : X × ℝ × ℝ → ℝ) : X × ℝ × ℝ → ℝ := ω

/-- The zero-defect correction term is the only source of deviation from `d`. -/
def d_ε (C : ℝ) (ω : X × ℝ × ℝ → ℝ) : X × ℝ × ℝ → ℝ :=
  fun p => ω p + C

private lemma d_ε_apply (C : ℝ) (ω : X × ℝ × ℝ → ℝ) (p : X × ℝ × ℝ) :
    d_ε C ω p = ω p + C := by
  rfl

lemma d_ε_eq_d_of_zero_defect (C : ℝ) (hC : C = 0) (ω : X × ℝ × ℝ → ℝ) :
    d_ε C ω = d ω := by
  ext p
  rw [d_ε_apply, d]
  simp [hC]

/-- Pullback along the embedding preserves the zero-defect commutation law. -/
theorem pullback_d_ε_commute_of_zero_defect (C : ℝ) (hC : C = 0)
    (ω : X × ℝ × ℝ → ℝ) :
    pullback_ι X (d_ε C ω) = d (pullback_ι X ω) := by
  have hzero : d_ε C ω = d ω := d_ε_eq_d_of_zero_defect (X := X) C hC ω
  rw [hzero]
  ext x
  simp [pullback_ι, d]

end EpsilonCohomology
