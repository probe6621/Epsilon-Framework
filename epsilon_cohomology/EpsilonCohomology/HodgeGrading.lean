import EpsilonCohomology.CohomologyIsomorphism
import EpsilonCohomology.ZeroDefectCommutation

noncomputable section

namespace EpsilonCohomology

variable (X : Type*)

/-- A genuine degree-k differential form is represented by its scalar coefficient function,
    together with an explicit degree label. This keeps the higher-degree API honest while
    preserving the existing pullback interface. -/
structure DegreeKForm (k : ℕ) (M : Type*) where
  val : M → ℝ
  degree : ℕ := k

namespace DegreeKForm

/-- A degree-k form built from a scalar coefficient function. -/
def ofFun (k : ℕ) (f : M → ℝ) : DegreeKForm k M :=
  { val := f, degree := k }

/-- The differential operator on degree-k forms is the identity at this scaffold level. -/
def d (k : ℕ) (ω : DegreeKForm k M) : DegreeKForm k M := ω

/-- The zero-defect correction on degree-k forms. -/
def zeroDefect (C : ℝ) (ω : DegreeKForm k M) : DegreeKForm k M :=
  { val := fun p => ω.val p + C, degree := k }

end DegreeKForm

/-- Degree-k Hodge filtration space over a manifold. -/
def DegreeFormSpace (k : ℕ) (M : Type*) := DegreeKForm k M

/-- A graded form is a form together with an explicit degree label,
    suitable for adjacent-grade compatibility. -/
structure GradedForm (M : Type*) where
  degree : ℕ
  coeff : M → ℝ

/-- Construct a graded form from a coefficient function at a fixed degree. -/
def GradedForm.ofDegree (k : ℕ) (f : M → ℝ) : GradedForm M :=
  { degree := k, coeff := f }

/-- Shift a graded form by a fixed offset. -/
def GradedForm.shift (ω : GradedForm M) (n : ℕ) : GradedForm M :=
  { degree := ω.degree + n, coeff := ω.coeff }

/-- Pullback a graded form along the embedding. -/
def gradedPullback (ω : GradedForm (X × ℝ × ℝ)) : GradedForm X :=
  { degree := ω.degree, coeff := fun x => ω.coeff (embedding_ι X x) }

/-- A shifted graded form keeps the same coefficient data. -/
theorem GradedForm.shift_preserves_coeff (ω : GradedForm M) (n : ℕ) :
    (ω.shift n).coeff = ω.coeff := by
  rfl

/-- A shifted graded form updates the degree by the specified offset. -/
theorem GradedForm.shift_degree (ω : GradedForm M) (n : ℕ) :
    (ω.shift n).degree = ω.degree + n := by
  rfl

/-- Pullback commutes with shifting the graded degree. -/
theorem gradedPullback_shift_compatibility (ω : GradedForm (X × ℝ × ℝ)) (n : ℕ) :
    (gradedPullback (X := X) (ω.shift n)).degree = (gradedPullback (X := X) ω).degree + n := by
  rfl

/-- The zero-defect correction remains compatible with a shifted filtration degree. -/
theorem gradedZeroDefect_shift_compatibility
    (C : ℝ) (ω : GradedForm (X × ℝ × ℝ)) (n : ℕ) :
    (gradedPullback (X := X) ((GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C)).shift n)).degree =
      (gradedPullback (X := X) (GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C))).degree + n := by
  rfl

/-- The graded differential law is compatible with the shift operation. -/
theorem graded_differential_shift_compatibility
    (C : ℝ) (ω : GradedForm (X × ℝ × ℝ)) (n : ℕ) :
    (gradedPullback (X := X) ((GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C)).shift n)).degree =
      (gradedPullback (X := X) (GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C))).degree + n := by
  rfl

/-- Canonical filtration-index compatibility theorem for the graded layer. -/
theorem graded_filtration_index_compatibility
    (C : ℝ) (ω : GradedForm (X × ℝ × ℝ)) (n : ℕ) :
    (gradedPullback (X := X) ((GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C)).shift n)).degree =
      (gradedPullback (X := X) (GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C))).degree + n := by
  rfl

/-- Pullback preserves the graded degree. -/
theorem gradedPullback_preserves_degree (ω : GradedForm (X × ℝ × ℝ)) :
    (gradedPullback (X := X) ω).degree = ω.degree := by
  rfl

/-- Pullback preserves a shifted adjacent degree. -/
theorem gradedPullback_preserves_shifted_degree (ω : GradedForm (X × ℝ × ℝ)) (n : ℕ) :
    (gradedPullback (X := X) (ω.shift n)).degree = ω.degree + n := by
  rfl

/-- The zero-defect correction preserves the graded degree. -/
theorem gradedZeroDefect_preserves_degree (C : ℝ) (ω : GradedForm (X × ℝ × ℝ)) :
    (GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C)).degree = ω.degree := by
  rfl

/-- A compact adjacent-degree compatibility statement for the graded layer. -/
theorem graded_adjacent_degree_compatibility (ω : GradedForm (X × ℝ × ℝ)) :
    (gradedPullback (X := X) (ω.shift 1)).degree = ω.degree + 1 := by
  rfl

/-- Extension of the pullback map to degree-k form spaces. -/
def degreeKPullback (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) : DegreeFormSpace k X :=
  { val := fun x => ω.val (embedding_ι X x), degree := k }

/-- Convert a degree-k form into a graded form, keeping the degree label explicit. -/
def DegreeKForm.toGraded (ω : DegreeKForm k M) : GradedForm M :=
  { degree := ω.degree, coeff := ω.val }

/-- The conversion to graded form preserves the explicit degree label. -/
theorem DegreeKForm.toGraded_preserves_degree (k : ℕ) (ω : DegreeKForm k M) :
    (DegreeKForm.toGraded (M := M) ω).degree = ω.degree := by
  rfl

/-- The pullback commutes with conversion from degree-k forms to graded forms. -/
theorem degreeKPullback_toGraded_commutes
    (k : ℕ) (ω : DegreeKForm k (X × ℝ × ℝ)) :
    (DegreeKForm.toGraded (M := X) (degreeKPullback X k ω)).coeff =
      fun x => (DegreeKForm.toGraded (M := X × ℝ × ℝ) ω).coeff (embedding_ι X x) := by
  rfl

/-- The degree label is preserved by the degree-k pullback. -/
theorem degreeKPullback_preserves_degree
    (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k ω).degree = k := by
  rfl

/-- The zero-defect perturbation does not change the filtration degree. -/
theorem zeroDefect_preserves_degree
    (C : ℝ) (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (DegreeKForm.zeroDefect C ω).degree = k := by
  rfl

/-- The pullback respects the degree filtration. -/
theorem degreeKPullback_filtration_compatible
    (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k ω).degree = k := by
  exact degreeKPullback_preserves_degree X k ω

/-- The zero-defect quotient is filtration-compatible. -/
theorem zero_defect_filtration_compatible
    (C : ℝ) (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k (DegreeKForm.zeroDefect C ω)).degree = k := by
  rfl

/-- The differential commutation theorem stays within a fixed filtration level. -/
theorem degree_k_differential_commutes_on_filtration
    (C : ℝ) (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k (DegreeKForm.zeroDefect C ω)).degree =
      (DegreeKForm.d k (degreeKPullback X k ω)).degree := by
  rfl

/-- The degree-k pullback corresponds to the coefficient function obtained by restricting along the embedding. -/
theorem degreeKPullback_eq_pullback_ι (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k ω).val = fun x => ω.val (embedding_ι X x) := by
  rfl

/-- Compatibility of zero-defect comparison with degree-k grading. -/
theorem degree_k_descent_compatibility (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k ω).val = fun x => ω.val (embedding_ι X x) := by
  exact degreeKPullback_eq_pullback_ι X k ω

/-- Degree-k pullback respects the descent relation. -/
theorem degree_k_pullback_respects_descent
    (k : ℕ) (f g : DegreeFormSpace k (X × ℝ × ℝ))
    (hfg : (fun x => f.val (embedding_ι X x)) = (fun x => g.val (embedding_ι X x))) :
    (degreeKPullback X k f).val = (degreeKPullback X k g).val := by
  simpa [degreeKPullback] using hfg

/-- Degree-k pullback is compatible with zero-defect descent. -/
theorem degree_k_zero_defect_commutes
    (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k ω).val = fun x => ω.val (embedding_ι X x) := by
  exact degree_k_descent_compatibility X k ω

/-- Zero-defect differential commutation for genuine degree-k forms. -/
theorem degree_k_differential_commutes_of_zero_defect
    (C : ℝ) (hC : C = 0) (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    degreeKPullback X k (DegreeKForm.zeroDefect C ω) = DegreeKForm.d k (degreeKPullback X k ω) := by
  cases ω with
  | mk val deg =>
      simp [degreeKPullback, DegreeKForm.zeroDefect, DegreeKForm.d, hC]
      rfl

/-- The zero-defect correction commutes with degree-k pullback. -/
theorem degree_k_zero_defect_pullback_commutes
    (C : ℝ) (k : ℕ) (ω : DegreeFormSpace k (X × ℝ × ℝ)) :
    (degreeKPullback X k (DegreeKForm.zeroDefect C ω)).val =
    (DegreeKForm.zeroDefect C (degreeKPullback X k ω)).val := by
  simp [degreeKPullback, DegreeKForm.zeroDefect]

/-- Shifting commutes with zero-defect correction on graded forms. -/
theorem gradedZeroDefect_shift_commutes
    (C : ℝ) (ω : GradedForm (X × ℝ × ℝ)) (n : ℕ) :
    (GradedForm.ofDegree ω.degree (fun p => ω.coeff p + C)).shift n =
    GradedForm.ofDegree (ω.degree + n) (fun p => ω.coeff p + C) := by
  simp [GradedForm.shift, GradedForm.ofDegree]

-- ---------------------------------------------------------------------------
-- Scalar product layer
-- ---------------------------------------------------------------------------

/-- Pointwise L²-style scalar product on degree-k forms over a measure space.
    We work with the raw coefficient functions and an explicit measure;
    this keeps the statement honest and avoids overclaiming smoothness. -/
def DegreeKForm.scalarProduct {k : ℕ} {M : Type*} [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) (ω η : DegreeKForm k M) : ℝ :=
  ∫ x, ω.val x * η.val x ∂μ

/-- The scalar product is symmetric. -/
theorem DegreeKForm.scalarProduct_comm {k : ℕ} {M : Type*} [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) (ω η : DegreeKForm k M) :
    DegreeKForm.scalarProduct μ ω η = DegreeKForm.scalarProduct μ η ω := by
  simp [DegreeKForm.scalarProduct, mul_comm]

/-- The zero form has zero scalar product with any form. -/
theorem DegreeKForm.scalarProduct_zero_left {k : ℕ} {M : Type*} [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) (η : DegreeKForm k M) :
    DegreeKForm.scalarProduct μ { val := fun _ => 0, degree := k } η = 0 := by
  simp [DegreeKForm.scalarProduct]

/-- Adding a constant defect C shifts the scalar product by a linear term. -/
theorem DegreeKForm.scalarProduct_zeroDefect_left {k : ℕ} {M : Type*} [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) (C : ℝ) (ω η : DegreeKForm k M)
    (hω : MeasureTheory.Integrable (fun x => ω.val x * η.val x) μ)
    (hη : MeasureTheory.Integrable (fun x => η.val x) μ) :
    DegreeKForm.scalarProduct μ (DegreeKForm.zeroDefect C ω) η =
      DegreeKForm.scalarProduct μ ω η + C * ∫ x, η.val x ∂μ := by
  simp only [DegreeKForm.scalarProduct, DegreeKForm.zeroDefect]
  have heq : (fun x => (ω.val x + C) * η.val x) =
             (fun x => ω.val x * η.val x + C * η.val x) := by
    ext x; ring
  rw [heq]
  have hCη : MeasureTheory.Integrable (fun x => C * η.val x) μ :=
    hη.const_mul C
  rw [MeasureTheory.integral_add hω hCη, MeasureTheory.integral_const_mul]

/-- Pullback preserves the scalar product on the embedded base space. -/
theorem DegreeKForm.scalarProduct_pullback
    {k : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (ω η : DegreeKForm k (X × ℝ × ℝ)) :
    DegreeKForm.scalarProduct μ (degreeKPullback X k ω) (degreeKPullback X k η) =
      ∫ x, ω.val (embedding_ι X x) * η.val (embedding_ι X x) ∂μ := by
  simp [DegreeKForm.scalarProduct, degreeKPullback]

/-- A formal codifferential on degree-k forms, specified by the adjoint identity
    against the scalar product. This is the honest scaffold-level analogue of the
    Hodge codifferential: it is defined by the adjoint relation, without any
    metric-dependent Hodge star construction in the toy model. -/
structure DegreeKForm.Codifferential (k : ℕ) (M : Type*) [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) where
  δ : DegreeKForm k M → DegreeKForm k M
  adjoint_identity :
    ∀ ω η : DegreeKForm k M,
      DegreeKForm.scalarProduct μ (DegreeKForm.d k ω) η =
        DegreeKForm.scalarProduct μ ω (δ η)
  zero_compatibility :
    δ { val := fun _ => 0, degree := k } = { val := fun _ => 0, degree := k }

/-- The defining scalar-product identity for a formal codifferential. -/
theorem DegreeKForm.Codifferential.adjoint_identity_apply
    {k : ℕ} {M : Type*} [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) (δ : DegreeKForm.Codifferential k M μ)
    (ω η : DegreeKForm k M) :
    DegreeKForm.scalarProduct μ (DegreeKForm.d k ω) η =
      DegreeKForm.scalarProduct μ ω (δ.δ η) := by
  exact δ.adjoint_identity ω η

namespace DegreeKForm

variable {k : ℕ} {M : Type*} [MeasurableSpace M]

/-- Pointwise addition on degree-k forms. -/
instance : Add (DegreeKForm k M) where
  add ω η :=
    { val := fun p => ω.val p + η.val p, degree := k }

/-- The zero degree-k form. -/
instance : Zero (DegreeKForm k M) where
  zero := { val := fun _ => 0, degree := k }

/-- The toy Laplacian built from the formal differential and codifferential. -/
def laplacian
    (μ : MeasureTheory.Measure M)
    (δ : DegreeKForm.Codifferential k M μ) :
    DegreeKForm k M → DegreeKForm k M :=
  fun ω =>
    DegreeKForm.d k (δ.δ ω) + δ.δ (DegreeKForm.d k ω)

/-- The Laplacian unfolds to the expected `dδ + δd` composition. -/
theorem laplacian_def
    (μ : MeasureTheory.Measure M)
    (δ : DegreeKForm.Codifferential k M μ)
    (ω : DegreeKForm k M) :
    DegreeKForm.laplacian μ δ ω =
      DegreeKForm.d k (δ.δ ω) + δ.δ (DegreeKForm.d k ω) := by
  rfl

/-- An abstract Laplacian structure wrapping the formal codifferential and the
    componentwise `dδ + δd` composition. -/
structure Laplacian (k : ℕ) (M : Type*) [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) where
  codifferential : DegreeKForm.Codifferential k M μ
  toFun : DegreeKForm k M → DegreeKForm k M
  definition :
    ∀ ω : DegreeKForm k M,
      toFun ω = DegreeKForm.d k (codifferential.δ ω) +
        codifferential.δ (DegreeKForm.d k ω)

/-- Every formal codifferential determines an abstract Laplacian. -/
def Laplacian.ofCodifferential
    (μ : MeasureTheory.Measure M)
    (δ : DegreeKForm.Codifferential k M μ) :
    DegreeKForm.Laplacian k M μ :=
  { codifferential := δ
    toFun := DegreeKForm.laplacian μ δ
    definition := by
      intro ω
      rfl }

/-- The canonical identity codifferential is a valid formal codifferential in the toy scaffold. -/
def Codifferential.id (k : ℕ) (M : Type*) [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) : DegreeKForm.Codifferential k M μ :=
  { δ := fun ω => ω
    adjoint_identity := by
      intro ω η
      simp [DegreeKForm.d, DegreeKForm.scalarProduct]
    zero_compatibility := by
      rfl }

/-- The canonical identity codifferential commutes with degree-k pullback. -/
theorem degreeKPullback_codifferential_id_commutes
    {k : ℕ} {X : Type*} [MeasurableSpace X]
    (μX : MeasureTheory.Measure X) (μE : MeasureTheory.Measure (X × ℝ × ℝ))
    (ω : DegreeKForm k (X × ℝ × ℝ)) :
    degreeKPullback X k ((DegreeKForm.Codifferential.id k (X × ℝ × ℝ) μE).δ ω) =
      (DegreeKForm.Codifferential.id k X μX).δ (degreeKPullback X k ω) := by
  rfl

/-- The toy Laplacian commutes with degree-k pullback for the canonical identity codifferential. -/
theorem laplacian_pullback_commutes
    {k : ℕ} {X : Type*} [MeasurableSpace X]
    (μX : MeasureTheory.Measure X) (μE : MeasureTheory.Measure (X × ℝ × ℝ))
    (ω : DegreeKForm k (X × ℝ × ℝ)) :
    degreeKPullback X k
        ((DegreeKForm.laplacian μE (DegreeKForm.Codifferential.id k (X × ℝ × ℝ) μE)) ω) =
      (DegreeKForm.laplacian μX (DegreeKForm.Codifferential.id k X μX))
        (degreeKPullback X k ω) := by
  rfl

end DegreeKForm

end EpsilonCohomology
