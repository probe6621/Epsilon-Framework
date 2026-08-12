#!/bin/bash
################################################################################
# run_deepseek_task.sh
# 
# Automated DeepSeek-Prover-V2 Formalization Pipeline
# 
# Purpose:
#   1. Read task prompt from DeepSeek-Prompts/
#   2. Send to DeepSeek-Prover-V2 via OpenRouter API
#   3. Extract generated Lean code
#   4. Replace sorry in skeleton file
#   5. Run lake build to validate
#   6. Report success/failure with actionable feedback
#
# Usage:
#   export OPENROUTER_API_KEY="sk-..."
#   bash run_deepseek_task.sh 1
#   
#   Or:
#   OPENROUTER_API_KEY="sk-..." bash run_deepseek_task.sh 1
#
# Arguments:
#   Task number (1, 2, or 3)
#
################################################################################

set -euo pipefail

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
REPO_ROOT="$(pwd)"
EPSILON_DIR="${REPO_ROOT}/epsilon_cohomology"
PROMPTS_DIR="${EPSILON_DIR}/DeepSeek-Prompts"
CODE_DIR="${EPSILON_DIR}/EpsilonCohomology"
MAX_RETRIES=3
RETRY_DELAY=5

# Task mapping
declare -A TASK_FILES=(
  [1]="ManifoldEmbedding"
  [2]="AlmostComplexStructure"
  [3]="PullbackOperator"
)

declare -A TASK_PROMPTS=(
  [1]="TASK_1_ManifoldEmbedding_SystemPrompt.txt"
  [2]="TASK_2_AlmostComplexStructure.txt"
  [3]="TASK_3_PullbackOperator.txt"
)

################################################################################
# FUNCTION: Print colored output
################################################################################
log_info() {
  echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
  echo -e "${GREEN}[✓ SUCCESS]${NC} $1"
}

log_error() {
  echo -e "${RED}[✗ ERROR]${NC} $1"
}

log_warning() {
  echo -e "${YELLOW}[⚠ WARNING]${NC} $1"
}

################################################################################
# FUNCTION: Validate environment
################################################################################
validate_environment() {
  log_info "Validating environment..."
  
  # Check API key
  if [[ -z "${OPENROUTER_API_KEY:-}" ]]; then
    log_error "OPENROUTER_API_KEY not set"
    echo "Set it with: export OPENROUTER_API_KEY='sk-...'"
    exit 1
  fi
  
  # Check task number
  if [[ -z "${1:-}" ]] || [[ ! "${TASK_FILES[${1:-}]:-}" ]]; then
    log_error "Invalid task number: ${1:-none}"
    echo "Usage: bash run_deepseek_task.sh [1|2|3]"
    exit 1
  fi
  
  # Check directories
  if [[ ! -d "$PROMPTS_DIR" ]]; then
    log_error "Prompts directory not found: $PROMPTS_DIR"
    exit 1
  fi
  
  if [[ ! -d "$CODE_DIR" ]]; then
    log_error "Code directory not found: $CODE_DIR"
    exit 1
  fi
  
  # Check required tools
  for tool in jq curl; do
    if ! command -v "$tool" &> /dev/null; then
      log_error "Required tool not found: $tool"
      exit 1
    fi
  done
  
  log_success "Environment validation passed"
}

################################################################################
# FUNCTION: Load prompt file
################################################################################
load_prompt() {
  local task_num=$1
  local prompt_file="${PROMPTS_DIR}/${TASK_PROMPTS[$task_num]}"
  
  log_info "Loading prompt from: $prompt_file"
  
  if [[ ! -f "$prompt_file" ]]; then
    log_error "Prompt file not found: $prompt_file"
    exit 1
  fi
  
  # Read prompt, escape for JSON
  local prompt_content
  prompt_content=$(cat "$prompt_file" | jq -Rs '.')
  
  echo "$prompt_content"
}

################################################################################
# FUNCTION: Call DeepSeek-Prover-V2 API with retry logic
################################################################################
call_deepseek_api() {
  local prompt_json=$1
  local attempt=1
  
  log_info "Calling DeepSeek-Prover-V2 via OpenRouter (attempt $attempt/$MAX_RETRIES)..."
  
  while [[ $attempt -le $MAX_RETRIES ]]; do
    local response
    
    response=$(curl -s -X POST https://api.openrouter.ai/api/v1/chat/completions \
      -H "Authorization: Bearer ${OPENROUTER_API_KEY}" \
      -H "Content-Type: application/json" \
      -H "HTTP-Referer: https://github.com/probe6621/Epsilon-Framework" \
      -d @- << EOF
{
  "model": "deepseek/deepseek-prover-v2-671b",
  "messages": [
    {
      "role": "user",
      "content": $prompt_json
    }
  ],
  "temperature": 0.1,
  "max_tokens": 8000,
  "top_p": 0.95
}
EOF
    )
    
    # Check for API errors
    if echo "$response" | jq -e '.error' > /dev/null 2>&1; then
      local error_msg
      error_msg=$(echo "$response" | jq -r '.error.message // .error')
      log_warning "API error on attempt $attempt: $error_msg"
      
      if [[ $attempt -lt $MAX_RETRIES ]]; then
        log_info "Retrying in ${RETRY_DELAY}s..."
        sleep "$RETRY_DELAY"
        ((attempt++))
        continue
      else
        log_error "Max retries exceeded"
        exit 1
      fi
    fi
    
    # Extract response content
    local content
    content=$(echo "$response" | jq -r '.choices[0].message.content // empty')
    
    if [[ -z "$content" ]]; then
      log_error "Empty response from API"
      exit 1
    fi
    
    echo "$content"
    return 0
  done
}

################################################################################
# FUNCTION: Extract Lean code block from response
################################################################################
extract_lean_code() {
  local response=$1
  
  # Try to extract code between ```lean and ```
  local lean_code
  lean_code=$(echo "$response" | sed -n '/```lean/,/```/p' | sed '1d;$d')
  
  if [[ -z "$lean_code" ]]; then
    # Fallback: try extracting between ``` and ```
    lean_code=$(echo "$response" | sed -n '/^```$/,/^```$/p' | sed '1d;$d')
  fi
  
  if [[ -z "$lean_code" ]]; then
    log_error "Could not extract Lean code from response"
    log_info "Raw response:"
    echo "$response" | head -20
    exit 1
  fi
  
  echo "$lean_code"
}

################################################################################
# FUNCTION: Merge generated code into skeleton file
################################################################################
merge_into_skeleton() {
  local task_num=$1
  local generated_code=$2
  local output_file="${CODE_DIR}/${TASK_FILES[$task_num]}.lean"
  
  log_info "Merging generated code into: $output_file"
  
  if [[ ! -f "$output_file" ]]; then
    log_error "Skeleton file not found: $output_file"
    exit 1
  fi
  
  # Backup original
  cp "$output_file" "${output_file}.backup"
  log_info "Backed up original to: ${output_file}.backup"
  
  # Replace sorry blocks with generated code
  # Strategy: Find the main theorem and replace its sorry body
  
  local temp_file
  temp_file=$(mktemp)
  
  # Extract just the theorem proofs from generated code
  local theorem_section
  theorem_section=$(echo "$generated_code" | awk '/^theorem |^lemma / { found=1 } found { print }')
  
  if [[ -z "$theorem_section" ]]; then
    log_warning "No theorem/lemma found in generated code; using full output"
    theorem_section="$generated_code"
  fi
  
  # Append generated code to file (before the final 'end')
  {
    head -n -1 "$output_file"  # All lines except last (which should be 'end')
    echo ""
    echo "-- Generated by DeepSeek-Prover-V2"
    echo "-- $(date)"
    echo ""
    echo "$theorem_section"
    echo ""
    tail -n 1 "$output_file"   # Final 'end' line
  } > "$temp_file"
  
  mv "$temp_file" "$output_file"
  log_success "Code merged into skeleton file"
}

################################################################################
# FUNCTION: Run lake build and capture errors
################################################################################
validate_build() {
  log_info "Validating with lake build..."
  
  cd "$EPSILON_DIR"
  
  # Run lake build, capture output
  local build_output
  local build_exit_code=0
  
  build_output=$(lake build 2>&1) || build_exit_code=$?
  
  if [[ $build_exit_code -eq 0 ]]; then
    log_success "lake build succeeded!"
    echo "$build_output" | grep -i "lean" | head -5
    return 0
  else
    log_error "lake build failed with exit code $build_exit_code"
    echo ""
    echo -e "${YELLOW}Build output (first 50 lines):${NC}"
    echo "$build_output" | head -50
    echo ""
    echo -e "${YELLOW}To see full output:${NC}"
    echo "  cd $EPSILON_DIR && lake build 2>&1 | tee build_error.log"
    echo ""
    return 1
  fi
}

################################################################################
# FUNCTION: Generate feedback template for next iteration
################################################################################
generate_feedback_template() {
  local task_num=$1
  local error_output=$2
  
  local feedback_file="${EPSILON_DIR}/FEEDBACK_TASK_${task_num}.md"
  
  cat > "$feedback_file" << 'EOF'
# BUILD FAILURE FEEDBACK for DeepSeek-Prover-V2

## Error Summary

[Paste first 50 lines of `lake build` error here]

## Error Analysis

- **Type of error**: [type mismatch | unknown identifier | tactic failed | etc.]
- **Location**: [file and line number]
- **Context**: [the failing code snippet]

## Suggested Fix

Please refactor to:
1. Fix the type error or unification issue
2. Use appropriate Mathlib lemmas for manifolds/linear maps
3. Preserve the high-level mathematical meaning

If this requires infrastructure not yet in Mathlib (e.g., full differential forms),
use `sorry` and note the omission.

## Next Prompt

Feed this updated request back to DeepSeek-Prover-V2:

---

**System Context**:
[Original task description]

**Error to Fix**:
```
[error output]
```

**Current Code**:
```lean
[failing code snippet]
```

Please refactor the proof to fix this error while maintaining the mathematical intent.

---

## To Iterate

```bash
bash run_deepseek_task.sh [TASK_NUM]
```

EOF

  log_info "Feedback template generated: $feedback_file"
}

################################################################################
# FUNCTION: Main execution
################################################################################
main() {
  local task_num=${1:-}
  
  echo ""
  echo "╔════════════════════════════════════════════════════════════════╗"
  echo "║  DeepSeek-Prover-V2 Automated Formalization Pipeline           ║"
  echo "║  Task $task_num - ${TASK_FILES[$task_num]}                       ║"
  echo "╚════════════════════════════════════════════════════════════════╝"
  echo ""
  
  # Validate
  validate_environment "$task_num"
  
  # Load prompt
  log_info "Step 1/5: Loading prompt..."
  local prompt_json
  prompt_json=$(load_prompt "$task_num")
  
  # Call API
  log_info "Step 2/5: Calling DeepSeek-Prover-V2..."
  local api_response
  api_response=$(call_deepseek_api "$prompt_json")
  
  # Extract Lean code
  log_info "Step 3/5: Extracting Lean code..."
  local lean_code
  lean_code=$(extract_lean_code "$api_response")
  
  # Merge into skeleton
  log_info "Step 4/5: Merging into skeleton file..."
  merge_into_skeleton "$task_num" "$lean_code"
  
  # Validate build
  log_info "Step 5/5: Validating with lake build..."
  if validate_build; then
    echo ""
    log_success "═══════════════════════════════════════════════════════"
    log_success "TASK $task_num COMPLETE"
    log_success "═══════════════════════════════════════════════════════"
    echo ""
    log_info "Next steps:"
    echo "  1. Review changes: git diff epsilon_cohomology/EpsilonCohomology/${TASK_FILES[$task_num]}.lean"
    echo "  2. Commit: git add -A && git commit -m 'Task $task_num formalization complete'"
    if [[ $task_num -lt 3 ]]; then
      echo "  3. Run next task: bash run_deepseek_task.sh $((task_num + 1))"
    fi
    echo ""
    exit 0
  else
    echo ""
    log_error "═══════════════════════════════════════════════════════"
    log_error "TASK $task_num BUILD FAILED"
    log_error "═══════════════════════════════════════════════════════"
    echo ""
    
    # Generate feedback template
    local build_error
    build_error=$(cd "$EPSILON_DIR" && lake build 2>&1 | head -50)
    generate_feedback_template "$task_num" "$build_error"
    
    log_warning "Feedback template saved. Fix errors and iterate:"
    echo "  bash run_deepseek_task.sh $task_num"
    echo ""
    exit 1
  fi
}

# Run main
main "$@"
