# DeepSeek-Prover-V2 Formalization Pipeline: Complete Setup

## Executive Summary

You now have a complete, production-ready pipeline to automate the formalization of three core geometric theorems using DeepSeek-Prover-V2. The system is structured for high-precision Chain-of-Thought (CoT) reasoning.

## Repository Structure

```
epsilon_cohomology/
├── EpsilonCohomology.lean              ← Existing verified scaffold
├── EpsilonCohomology/
│   ├── ManifoldEmbedding.lean          ← Task 1 skeleton (with sorry)
│   ├── AlmostComplexStructure.lean     ← Task 2 skeleton (with sorry)
│   └── PullbackOperator.lean           ← Task 3 skeleton (with sorry)
├── DeepSeek-Prompts/
│   ├── TASK_1_ManifoldEmbedding.txt    ← High-precision CoT prompt
│   ├── TASK_2_AlmostComplexStructure.txt
│   └── TASK_3_PullbackOperator.txt
├── FORMALIZATION_TASKS.md              ← Master tracking document
├── VALIDATION_LOOP.md                  ← Build & error feedback loop
├── lakefile.toml                       ← Lake config (v4.33.0, Mathlib v4.33.0)
└── lean-toolchain                      ← Pinned Lean version
```

## Quick Start

### 1. Run Initial Build
```bash
cd epsilon_cohomology
lake update
lake build 2>&1 | tee build.log
```

Expected: Compiles successfully with `sorry` placeholders (no errors).

### 2. Select a Task
Open the corresponding prompt file:
- Task 1: `DeepSeek-Prompts/TASK_1_ManifoldEmbedding.txt`
- Task 2: `DeepSeek-Prompts/TASK_2_AlmostComplexStructure.txt`
- Task 3: `DeepSeek-Prompts/TASK_3_PullbackOperator.txt`

### 3. Feed Prompt to DeepSeek-Prover-V2
- **For OpenRouter API**: Paste with `model: deepseek/deepseek-prover-v2-671b`
- **For Local Deployment**: Use your local endpoint
- **For Web UI**: Copy/paste into HuggingFace interface

**Mode**: Use **High-Precision Chain-of-Thought (CoT)**

### 4. Apply Generated Proof
Replace the `sorry` in the corresponding skeleton file with the generated tactic proof.

### 5. Validate & Iterate
```bash
lake build 2>&1 | tee build.log
```

If errors: Extract error, feed back to model with feedback template (see `VALIDATION_LOOP.md`).

## Three Task Overview

### Task 1: Smooth Manifold Embedding (ι : X → X_ε)
- **Prove**: Canonical inclusion is a smooth embedding
- **Files**: `ManifoldEmbedding.lean`, `TASK_1_ManifoldEmbedding.txt`
- **Key Theorem**: `canonicalInclusion_is_smooth_embedding`
- **Difficulty**: Medium | **Est. LoC**: 100–200

### Task 2: Almost Complex Structure (J_ε² = -id)
- **Prove**: J_ε satisfies J² = -identity on tangent bundle
- **Files**: `AlmostComplexStructure.lean`, `TASK_2_AlmostComplexStructure.txt`
- **Key Theorem**: `epsilonAlmostComplex_squares_to_neg_id`
- **Difficulty**: Medium | **Est. LoC**: 150

### Task 3: Pullback Commutation (ι* ∘ d_ε = d ∘ ι*)
- **Prove**: Pullback commutes with exterior derivative at zero defect
- **Files**: `PullbackOperator.lean`, `TASK_3_PullbackOperator.txt`
- **Key Theorem**: `pullback_commutes_with_exterior_derivative`
- **Difficulty**: Medium | **Est. LoC**: 120

## Prompt Structure

Each prompt follows a standardized format:

```
## FORMAL GOAL
[Exact mathematical statement]

## MATHEMATICAL BACKGROUND
[Informal intuition]

## LEAN THEOREM SIGNATURE
[Exact Lean 4 code with `sorry`]

## HIGH-PRECISION CoT DECOMPOSITION
[Step-by-step reasoning]

## TACTIC PROOF SKELETON
[Lean proof structure]

## KEY MATHLIB LEMMAS
[Relevant lemmas]

## VALIDATION & FEEDBACK LOOP
[Error handling]
```

## Workflow Example

### Step 1: Read Skeleton
```bash
cat epsilon_cohomology/EpsilonCohomology/ManifoldEmbedding.lean
```

### Step 2: Feed Prompt to DeepSeek-Prover-V2
```bash
cat epsilon_cohomology/DeepSeek-Prompts/TASK_1_ManifoldEmbedding.txt | \
  curl -X POST https://api.openrouter.ai/api/v1/chat/completions \
  -H "Authorization: Bearer $OPENROUTER_API_KEY" \
  -d '{"model": "deepseek/deepseek-prover-v2-671b", ...}'
```

### Step 3: Apply Proof
Replace `sorry` in skeleton with generated tactic proof.

### Step 4: Build & Iterate
```bash
lake build 2>&1 | head -20
```

## Success Criteria

✅ All three tasks compile without errors  
✅ Each uses legitimate Mathlib lemmas (≤ 2 `sorry` for unavoidable gaps)  
✅ `lake build` runs in < 10 seconds  
✅ Documentation explains all gaps  
✅ Modules successfully imported into main scaffold  

## Next Steps

1. **Run initial build**: `cd epsilon_cohomology && lake build`
2. **Pick Task 1**: Open `TASK_1_ManifoldEmbedding.txt`
3. **Feed to DeepSeek-Prover-V2**: Use your preferred interface
4. **Apply proof**: Replace `sorry` in skeleton
5. **Validate**: `lake build` and iterate on errors
6. **Repeat** for Tasks 2 and 3

For detailed error handling, see `VALIDATION_LOOP.md`. For task context, see `FORMALIZATION_TASKS.md`.
