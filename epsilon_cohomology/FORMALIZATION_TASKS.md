# EPSILON COHOMOLOGY FORMALIZATION TASKS

## Overview

This issue tracks the three core geometric formalizations needed to promote the existing
epsilon cohomology scaffold into a full manifold-level comparison theorem.

**Status**: 🔄 **In Progress** – Three tasks ready for DeepSeek-Prover-V2 formalization

---

## Task 1: Smooth Manifold Embedding (ι : X → X_ε)

**Objective**: Prove that the canonical inclusion map ι(x) = (x, 0, 0) is a smooth embedding
into the toroidal double cover X_ε = X × T² × iT².

**Deliverables**:
- [ ] Prove `canonicalInclusion_smooth`
- [ ] Prove `canonicalInclusion_injective`
- [ ] Prove `canonicalInclusion_tangent_injective` (differential is injective)
- [ ] Combine into main theorem: `canonicalInclusion_is_smooth_embedding`

**Files**:
- Skeleton: `epsilon_cohomology/EpsilonCohomology/ManifoldEmbedding.lean`
- Prompt: `epsilon_cohomology/DeepSeek-Prompts/TASK_1_ManifoldEmbedding.txt`

**Key Mathlib Lemmas**:
- `Smooth.prod_mk` (smoothness of products)
- `Embedding.mk` (embedding from injectivity + openness)
- `Pi.smooth_iff` (product smoothness characterization)
- `tangentMap_prod` (differential of product map)

**Estimated Effort**: Medium (~100–200 lines of proof)

---

## Task 2: Almost Complex Structure (J_ε² = -id)

**Objective**: Formalize the almost complex structure J_ε on the tangent bundle T(X_ε) and prove
the fundamental property J_ε² = -id_TM.

**Deliverables**:
- [ ] Define `AlmostComplexStructure` structure with J, smoothness, J² = -id
- [ ] Define `epsilonAlmostComplexStructure` (product action on T² and iT²)
- [ ] Prove `epsilonAlmostComplex_squares_to_neg_id` (main theorem)
- [ ] Placeholder for integrability: `IsIntegrableAlmostComplexStructure` (dJ = 0)

**Files**:
- Skeleton: `epsilon_cohomology/EpsilonCohomology/AlmostComplexStructure.lean`
- Prompt: `epsilon_cohomology/DeepSeek-Prompts/TASK_2_AlmostComplexStructure.txt`

**Key Mathlib Lemmas**:
- `ContinuousLinearMap.comp` (composition of linear maps)
- `LinearMap.neg_apply` (negation on tangent spaces)
- `Prod.mk_neg` (negation on products)
- `simp` with `ring` for algebraic closure

**Estimated Effort**: Medium (component-wise proof, ~150 lines)

**Future Work**: Integrability (Nijenhuis tensor N_J = 0) requires exterior algebra integration.

---

## Task 3: Pullback Commutation (ι* ∘ d_ε = d ∘ ι*)

**Objective**: Prove that the pullback ι* commutes with the modified exterior derivative d_ε
when the defect tensor C = 0.

**Deliverables**:
- [ ] Prove `pullback_linear` (pullback preserves linearity)
- [ ] Prove `pullback_commutes_with_exterior_derivative` (main commutativity)
- [ ] Prove `pullback_preserves_closed_forms` (closed forms pull back to closed)
- [ ] Prove `pullback_preserves_exactness` (exact forms pull back to exact)

**Files**:
- Skeleton: `epsilon_cohomology/EpsilonCohomology/PullbackOperator.lean`
- Prompt: `epsilon_cohomology/DeepSeek-Prompts/TASK_3_PullbackOperator.txt`

**Key Mathlib Lemmas**:
- `funext` (function extensionality)
- `mul_zero`, `zero_mul`, `add_zero` (scalar arithmetic)
- `comp_apply` (function composition application)
- **Future**: `DifferentialForm.pullback`, `exterior_deriv_comp` (when integrating full forms)

**Estimated Effort**: Medium (relies on zero-defect reduction, ~120 lines)

**Current Limitation**: Working with scalar proxies; full differential form version requires
`Mathlib.Geometry.Manifold.Derivatives` and `Mathlib.LinearAlgebra.Exterior`.

---

## Build & Validation

### Prerequisites
- Lean 4.33.0 (see `lean-toolchain`)
- Mathlib v4.33.0 (see `lakefile.toml`)

### Build Steps
```bash
cd epsilon_cohomology
lake update
lake clean
lake build
```

**Expected Output**: No errors; all three modules compile successfully.

### Feedback Loop
1. If `lake build` fails, capture error output
2. Feed error + code snippet to DeepSeek-Prover-V2 in High-Precision CoT mode
3. Apply suggested fix, rebuild, repeat

See `VALIDATION_LOOP.md` for detailed error handling and iteration patterns.

---

## Integration with Existing Scaffold

These three formalizations extend the existing `EpsilonCohomology.lean` by:

1. **Manifold Embedding (Task 1)** ← Formalizes the geometric foundation
   - Currently: Abstract `doubleCoverEmbedding` and `pullbackForm` definitions
   - New: Smooth manifold structure with explicit tangent space compatibility

2. **Almost Complex Structure (Task 2)** ← Encodes topological richness
   - Currently: No J_ε formalized; placeholder in README
   - New: Concrete definition with J² = -id proof

3. **Pullback Commutation (Task 3)** ← Establishes commutativity at the heart of the theory
   - Currently: `pullback_preserves_closed_forms` (abstract, on vector spaces)
   - New: Concrete pullback ι* on differential forms, zero-defect commutativity

**Final Integration**: After all three tasks, import them in `EpsilonCohomology.lean`:
```lean
import EpsilonCohomology.ManifoldEmbedding
import EpsilonCohomology.AlmostComplexStructure
import EpsilonCohomology.PullbackOperator
```

---

## Success Criteria

✅ All three tasks formalize without errors  
✅ Proofs use Mathlib lemmas (≤ 3 `sorry` per task for unavoidable gaps)  
✅ Documentation comments explain gaps (e.g., "integrability requires full exterior algebra")  
✅ `lake build` passes on Lean 4.33.0 + Mathlib v4.33.0  
✅ Each proof compiles in < 5 seconds  

---

## Timeline & Milestones

- **Week 1**: Task 1 (Manifold Embedding) + initial validation
- **Week 2**: Task 2 (Almost Complex) refinement + error feedback loop
- **Week 3**: Task 3 (Pullback) formalization + integration testing
- **Week 4**: Documentation, cleanup, final integration into main scaffold

---

## References

- **Prompts**: See `DeepSeek-Prompts/` directory (CoT templates for high-precision reasoning)
- **Skeleton Code**: See `EpsilonCohomology/` directory (incomplete definitions with `sorry`)
- **Existing Scaffold**: `EpsilonCohomology.lean` (verified algebraic scaffold)
- **Mathlib Docs**: https://mathlib4.github.io/
- **Lean 4 Reference**: https://leanprover.github.io/lean4/doc/

---

## Assigned to
@probe6621 (owner)

## Labels
`formalization` `differential-geometry` `lean4` `manifold` `cohomology` `in-progress`
