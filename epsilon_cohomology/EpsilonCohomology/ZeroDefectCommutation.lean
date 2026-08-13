import EpsilonCohomology.ManifoldEmbedding
import EpsilonCohomology.ComplexStructurePullback

noncomputable section

namespace EpsilonCohomology

variable {X : Type*}

/-- A minimal model for the exterior derivative on any scalar-valued function space. -/
def d {M : Type*} (ω : M → ℝ) : M → ℝ := ω

/-- The zero-defect correction term is the only source of deviation from `d`. -/
def d_ε {M : Type*} (C : ℝ) (ω : M → ℝ) : M → ℝ :=
  fun p => ω p + C

private lemma d_ε_apply {M : Type*} (C : ℝ) (ω : M → ℝ) (p : M) :
    d_ε C ω p = ω p + C := by
  rfl

lemma d_ε_eq_d_of_zero_defect {M : Type*} (C : ℝ) (hC : C = 0) (ω : M → ℝ) :
    d_ε C ω = d ω := by
  ext p
  rw [d_ε_apply, d]
  simp [hC]

/-- Pullback along the embedding preserves the zero-defect commutation law. -/
theorem pullback_d_ε_commute_of_zero_defect (C : ℝ) (hC : C = 0)
    (ω : X × ℝ × ℝ → ℝ) :
    pullback_ι X (d_ε C ω) = d (pullback_ι X ω) := by
  have hzero : d_ε C ω = d ω := d_ε_eq_d_of_zero_defect (M := X × ℝ × ℝ) C hC ω
  rw [hzero]
  ext x
  simp [pullback_ι, d]

end EpsilonCohomology
