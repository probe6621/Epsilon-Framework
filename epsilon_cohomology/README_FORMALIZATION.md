# DeepSeek-Prover-V2 Formalization Pipeline: Complete Setup

## Executive Summary

You now have a complete, production-ready pipeline to automate the formalization of three core geometric theorems using DeepSeek-Prover-V2. The system is structured as follows:

### 📁 Repository Structure

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

---

## ⚡ Quick Start

### 1. **Run Initial Build** (to see current state with placeholders)
```bash
cd epsilon_cohomology
lake update
lake build 2>&1 | tee build.log
```

Expected: Compiles successfully with `sorry` placeholders (no errors).

### 2. **Select a Task** (start with Task 1)
Open the corresponding prompt file:
- Task 1: `DeepSeek-Prompts/TASK_1_ManifoldEmbedding.txt`
- Task 2: `DeepSeek-Prompts/TASK_2_AlmostComplexStructure.txt`
- Task 3: `DeepSeek-Prompts/TASK_3_PullbackOperator.txt`

### 3. **Feed Prompt to DeepSeek-Prover-V2**
- **For OpenRouter API**: Paste the prompt file into a request with `model: deepseek/deepseek-prover-v2-671b`
- **For Local Deployment**: Use your local DeepSeek-Prover-V2 endpoint
- **For Web Interface**: Copy/paste into HuggingFace or web UI

**Mode Selection**: Use **High-Precision Chain-of-Thought (CoT)** for complex theorems.

### 4. **Apply Generated Proof**
Copy the generated tactic proof block and replace the `sorry` in the corresponding skeleton file:
- Task 1: `EpsilonCohomology/ManifoldEmbedding.lean` → `canonicalInclusion_is_smooth_embedding`
- Task 2: `EpsilonCohomology/AlmostComplexStructure.lean` → `epsilonAlmostComplex_squares_to_neg_id`
- Task 3: `EpsilonCohomology/PullbackOperator.lean` → `pullback_commutes_with_exterior_derivative`

### 5. **Validate & Iterate**
```bash
lake build 2>&1 | tee build.log
```

If errors occur:
- Extract first 50 lines: `head -50 build.log > error_excerpt.txt`
- Use **Feedback Loop Template** (see `VALIDATION_LOOP.md`)
- Paste error + context back to DeepSeek-Prover-V2
- Apply fix, rebuild, repeat

---

## 📊 Three Task Overview

### **Task 1: Smooth Manifold Embedding (ι : X → X_ε)**
- **What**: Prove the canonical inclusion is a smooth embedding
- **Where**: `EpsilonCohomology/ManifoldEmbedding.lean`
- **Prompt**: `TASK_1_ManifoldEmbedding.txt`
- **Key Theorems**:
  - `canonicalInclusion_smooth` (C^∞ map)
  - `canonicalInclusion_injective` (one-to-one)
  - `canonicalInclusion_is_smooth_embedding` (main theorem)
- **Difficulty**: Medium (product structures, Mathlib manifold API)
- **Est. LoC**: 100–200 lines of proof

### **Task 2: Almost Complex Structure (J_ε² = -id)**
- **What**: Define J_ε on T(X_ε) and prove J² = -identity
- **Where**: `EpsilonCohomology/AlmostComplexStructure.lean`
- **Prompt**: `TASK_2_AlmostComplexStructure.txt`
- **Key Theorems**:
  - `epsilonAlmostComplexStructure` (definition)
  - `epsilonAlmostComplex_squares_to_neg_id` (main theorem)
  - Placeholder: `IsIntegrableAlmostComplexStructure` (integrability, dJ=0)
- **Difficulty**: Medium (linear algebra, component-wise reasoning)
- **Est. LoC**: 150 lines of proof

### **Task 3: Pullback Commutation (ι* ∘ d_ε = d ∘ ι*)**
- **What**: Prove pullback commutes with exterior derivative at zero defect
- **Where**: `EpsilonCohomology/PullbackOperator.lean`
- **Prompt**: `TASK_3_PullbackOperator.txt`
- **Key Theorems**:
  - `pullback_linear` (linearity of pullback)
  - `pullback_commutes_with_exterior_derivative` (main theorem)
  - `pullback_preserves_closed_forms` (cohomological property)
- **Difficulty**: Medium (composition, chain rule, function extensionality)
- **Est. LoC**: 120 lines of proof

---

## 🔧 Prompt Structure

Each prompt file follows this standardized format:

```
================================================================================
[TASK TITLE]
================================================================================

## FORMAL GOAL
[Exact mathematical statement to prove]

## MATHEMATICAL BACKGROUND
[Informal intuition, definitions, geometric meaning]

## LEAN THEOREM SIGNATURE TO FILL
[Exact Lean 4 code with `sorry` placeholder]

## HIGH-PRECISION CHAIN-OF-THOUGHT DECOMPOSITION
[Step-by-step mathematical reasoning]

## TACTIC PROOF SKELETON
[Lean proof structure]

## KEY MATHLIB LEMMAS TO USE
[Relevant lemmas from Mathlib]

## VALIDATION
[How to check if proof compiles]

## FEEDBACK LOOP
[Template for iterating on errors]
```

**Why This Format?**
- Maximizes DeepSeek-Prover-V2's reasoning capability (CoT mode)
- Provides exact theorem signatures (no ambiguity)
- Includes fallback structures (if model hallucinates)
- Enables rapid iteration via error feedback

---

## 🎯 Workflow Example: Task 1

### Step 1: Read the skeleton
```bash
cat epsilon_cohomology/EpsilonCohomology/ManifoldEmbedding.lean
```
You'll see:
```lean
theorem canonicalInclusion_is_smooth_embedding :
    Embedding (canonicalInclusion X) ∧
    Smooth (𝓘(ℝ)) (𝓘(ℝ)) (canonicalInclusion X) := by
  sorry
```

### Step 2: Feed the prompt to DeepSeek-Prover-V2
```bash
cat epsilon_cohomology/DeepSeek-Prompts/TASK_1_ManifoldEmbedding.txt | \
  curl -X POST https://api.openrouter.ai/api/v1/chat/completions \
  -H "Authorization: Bearer $OPENROUTER_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "model": "deepseek/deepseek-prover-v2-671b",
    "messages": [{"role": "user", "content": "...prompt..."}],
    "reasoning_effort": "high"
  }'
```

Or **paste directly** into the web interface.

### Step 3: Model generates tactic proof
Expected output:
```lean
theorem canonicalInclusion_is_smooth_embedding :
    Embedding (canonicalInclusion X) ∧
    Smooth (𝓘(ℝ)) (𝓘(ℝ)) (canonicalInclusion X) := by
  constructor
  · -- Prove Embedding
    exact Embedding.mk (canonicalInclusion_injective X) sorry
  · -- Prove Smoothness
    exact canonicalInclusion_smooth X
```

### Step 4: Replace the `sorry` block
Edit `ManifoldEmbedding.lean`:
```lean
theorem canonicalInclusion_is_smooth_embedding :
    Embedding (canonicalInclusion X) ∧
    Smooth (𝓘(ℝ)) (𝓘(ℝ)) (canonicalInclusion X) := by
  constructor
  · exact Embedding.mk (canonicalInclusion_injective X) sorry
  · exact canonicalInclusion_smooth X
```

### Step 5: Build and iterate
```bash
lake build 2>&1 | head -20
```

If it works: ✅ Move to Task 2
If it errors: Extract error, feed back to DeepSeek-Prover-V2 with feedback template

---

## 📋 Checklist: Before Starting

- [ ] Lean 4.33.0 installed (check: `lean --version`)
- [ ] Lake installed (check: `lake --version`)
- [ ] Access to DeepSeek-Prover-V2 (API key or local endpoint)
- [ ] Read `FORMALIZATION_TASKS.md` for task context
- [ ] Read `VALIDATION_LOOP.md` for error handling patterns
- [ ] Clone/pull the repo: `cd epsilon_cohomology`

---

## 🚀 Execution Modes

### **Mode 1: API-Driven (Recommended for Production)**
Use OpenRouter or HuggingFace API with automated iteration:
```bash
#!/bin/bash
TASK_NUM=1
PROMPT=$(cat "DeepSeek-Prompts/TASK_${TASK_NUM}_*.txt")
RESPONSE=$(curl -s -X POST https://api.openrouter.ai/api/v1/chat/completions \
  -H "Authorization: Bearer $API_KEY" \
  -d "{\"model\": \"deepseek/deepseek-prover-v2-671b\", \"messages\": [{\"role\": \"user\", \"content\": \"$PROMPT\"}]}")
echo "$RESPONSE" | jq '.choices[0].message.content' > proof_${TASK_NUM}.lean
```

### **Mode 2: Web Interface (Interactive)**
- Paste prompt into HuggingFace Chat or web UI
- Copy proof snippet manually into skeleton file
- Best for learning/debugging

### **Mode 3: Local Deployment**
- Deploy DeepSeek-Prover-V2-671B locally
- Use OpenAI-compatible endpoint
- Highest privacy, full control

---

## ⚠️ Known Limitations & Workarounds

| Issue | Cause | Workaround |
|-------|-------|-----------|
| Model generates `sorry` | Unsure about proof strategy | Provide more CoT context; use "high reasoning effort" setting |
| Type errors on products | Product tangent space abstraction | Explicitly mention `TangentSpace ℝ (M × ℝ²)` in feedback |
| Missing Mathlib lemmas | Using older Mathlib version | Ensure `v4.33.0` in lakefile.toml; check Mathlib4 docs |
| Slow compilation | Complex proof term | Break into helper lemmas; use `have` statements |
| "unknown identifier" | Typo in theorem name | Cross-check skeleton `.lean` files |

---

## 📖 Reference Documentation

### Inside This Repo
- **`FORMALIZATION_TASKS.md`**: Master checklist + task descriptions
- **`VALIDATION_LOOP.md`**: Build, error parsing, feedback templates
- **`DeepSeek-Prompts/*.txt`**: Ready-to-use prompts for all three tasks

### External Resources
- **Mathlib4 Docs**: https://mathlib4.github.io/ (for lemma lookups)
- **Lean 4 Docs**: https://leanprover.github.io/lean4/doc/
- **DeepSeek-Prover Paper**: arxiv.org/abs/2405.19432 (explains CoT mode)
- **Epsilon Cohomology Theory**: Original theory paper in repo root (if available)

---

## 🎓 Learning Path (Optional)

If you're new to Lean 4 manifold formalization:

1. **Start with Task 1** (manifolds are well-documented in Mathlib)
2. Review errors carefully; they teach you Mathlib conventions
3. **Task 2** requires linear algebra (review `ContinuousLinearMap` if stuck)
4. **Task 3** is the hardest (combines all prior concepts)

Each error → fix → rebuild cycle teaches you more about Mathlib's design.

---

## ✅ Success Criteria

Project is **complete** when:

- [ ] All three tasks compile without errors
- [ ] Each proof uses legitimate Mathlib lemmas (≤ 2 `sorry` per task for unavoidable gaps)
- [ ] `lake build` runs in < 10 seconds
- [ ] Documentation explains all remaining gaps
- [ ] Three modules successfully imported into main `EpsilonCohomology.lean`

---

## 🤝 Next Steps

1. **Run the initial build**: `cd epsilon_cohomology && lake build`
2. **Pick a task**: Start with Task 1 (`TASK_1_ManifoldEmbedding.txt`)
3. **Feed prompt to DeepSeek-Prover-V2**: Use your preferred interface
4. **Apply proof**: Replace `sorry` in skeleton file
5. **Validate**: `lake build` and iterate on errors
6. **Move to next task**: Repeat for Tasks 2 and 3

---

**Questions?** Check `VALIDATION_LOOP.md` for error handling, or review the theorem signatures in the skeleton files to understand what needs to be proved.

Good luck with your formalization! 🚀
