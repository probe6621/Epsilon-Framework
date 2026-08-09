import subprocess
import sys
import time
import os
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent

simulations = [
    "bsd_conjecture.py",
    "collatz_toroidal_decay.py",
    "hodge_harmonic_phase_locking.py",
    "koide_toroidal_manifold.py",
    "navier_stokes_regularity.py",
    "odd_perfect_parity_defect.py",
    "p_vs_np_topological_equivalence.py",
    "poincare_epsilon_inversion.py",
    "riemann_phase_locking",
    "superfluid_dark_matter_rotation.py",
    "superfluid_plenum_ftl_phase.py",
    "yang_mills_mass_gap.py",
    "tesla_369_geometry.py"
]

def _dependencies_available():
    missing = []
    try:
        import numpy  # noqa: F401
    except ImportError:
        missing.append("numpy")
    try:
        import matplotlib  # noqa: F401
    except ImportError:
        missing.append("matplotlib")
    return missing


def _resolve_script_path(sim):
    script_path = SCRIPT_DIR / sim
    if script_path.exists():
        return script_path
    if not sim.endswith(".py"):
        py_variant = SCRIPT_DIR / f"{sim}.py"
        if py_variant.exists():
            return py_variant
    return None


def execute_suite():
    print("=" * 65)
    print("      EPSILON FRAMEWORK MASTER SIMULATION RUNNER      ")
    print("=" * 65)

    missing_dependencies = _dependencies_available()
    if missing_dependencies:
        print(f"\n❌ Missing dependencies: {', '.join(missing_dependencies)}")
        print("Install them with:")
        print("python3 -m pip install -r simulations/requirements.txt")
        return

    start_time = time.time()
    passed, failed = 0, 0

    for idx, sim in enumerate(simulations, 1):
        print(f"\n[{idx}/{len(simulations)}] Executing {sim}...")
        script_path = _resolve_script_path(sim)

        if script_path is None:
            print(f"⚠️ {sim} not found; skipping.")
            continue

        env = os.environ.copy()
        env["MPLBACKEND"] = "Agg"

        try:
            subprocess.run(
                [sys.executable, str(script_path)],
                check=True,
                cwd=str(SCRIPT_DIR),
                env=env,
            )
            print(f"✅ {sim} completed successfully.")
            passed += 1
        except subprocess.CalledProcessError as e:
            print(f"❌ {sim} failed with exit code {e.returncode}.")
            failed += 1

    total_time = time.time() - start_time
    print("\n" + "=" * 65)
    print(f"SUMMARY: Executed {len(simulations)} scripts in {total_time:.2f}s")
    print(f"Passed: {passed} | Failed: {failed}")
    print("=" * 65)

if __name__ == "__main__":
    execute_suite()
