#!/bin/bash
================================================================================
EPSILON COHOMOLOGY FORMALIZATION: BUILD & VALIDATION LOOP
================================================================================

## BUILD & IMMEDIATE FEEDBACK

This script automates the lake build cycle and captures error feedback for 
iteration with DeepSeek-Prover-V2.

### STEP 1: Update Dependencies
```bash
cd epsilon_cohomology
lake update
```

### STEP 2: Clean Build
```bash
lake clean
lake build 2>&1 | tee build.log
```

### STEP 3: Parse Errors
If errors appear, extract the first 50 lines:
```bash
head -50 build.log > error_excerpt.txt
```

### STEP 4: Feedback Loop Template

Paste this template + error_excerpt.txt into DeepSeek-Prover-V2:

---

**BUILD FAILURE FEEDBACK**

The following Lean 4 code failed to compile:

Module: `EpsilonCohomology/[Task].lean`

Error output:
```
[paste error_excerpt.txt here]
```

Please refactor the failing theorem/definition to:
1. Fix the type error or unification issue
2. Use appropriate Mathlib lemmas for the domain (manifolds, linear maps, etc.)
3. Preserve the high-level mathematical meaning

If the error stems from missing infrastructure (e.g., full differential forms),
insert `sorry` as a placeholder and note the omission.

---

### STEP 5: Apply Fixes

Copy the corrected proof snippet into the `.lean` file and rebuild:

```bash
lake build
```

### STEP 6: Iterative Refinement

Repeat Steps 2–5 until `lake build` succeeds with no errors.

---

## SUCCESS CRITERIA

✅ `lake build` produces no errors
✅ All three task files compile:
   - EpsilonCohomology/ManifoldEmbedding.lean
   - EpsilonCohomology/AlmostComplexStructure.lean
   - EpsilonCohomology/PullbackOperator.lean
✅ Proofs use Mathlib lemmas, not excessive `sorry`
✅ Documentation comments explain remaining gaps (e.g., for integrability)

---

## COMMON ERRORS & QUICK FIXES

### Error: "unknown identifier"
→ Missing import. Check `Mathlib.Geometry.Manifold.*` or `Mathlib.LinearAlgebra.*`

### Error: "type mismatch: expected ℝ but got something else"
→ Ensure tangent spaces, forms, and scalars use consistent types
→ Use type ascriptions: `(v : TangentSpace ℝ M x)`

### Error: "function expected" on `J.J x v`
→ J.J is a continuous linear map; apply it with `J.J x v` or `(J.J x) v`
→ Not `J.J x (v)` — this is usually fine, but check associativity

### Error: "sorry not allowed"
→ This is a warning if the project is in strict mode
→ Replace with legitimate proofs or use `partial` if acceptable

---

## RUNNING VALIDATION

To validate all three tasks at once:

```bash
#!/bin/bash
cd epsilon_cohomology
echo "Building Epsilon Cohomology formalization..."
lake build 2>&1

if [ $? -eq 0 ]; then
    echo "✅ All modules compiled successfully"
    echo "Checking for sorry count..."
    grep -r "sorry" EpsilonCohomology/*.lean | wc -l
    echo "sorrys found (should be minimal after formalization)"
else
    echo "❌ Build failed; see error output above"
    exit 1
fi
```

---

## NEXT STEPS AFTER SUCCESSFUL BUILD

1. Run the full test suite (if available):
   ```bash
   lake test
   ```

2. Generate documentation:
   ```bash
   lake doc
   ```

3. Move to integration with existing EpsilonCohomology.lean:
   - Import the three new modules in the main file
   - Link theorems to the existing zero-defect scaffold
   - Ensure no circular dependencies

================================================================================
