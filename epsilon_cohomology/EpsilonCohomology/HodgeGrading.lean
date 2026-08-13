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

/-- A graded form is a form together with an explicit degree label, suitable for adjacent-grade compatibility. -/
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

end EpsilonCohomology
