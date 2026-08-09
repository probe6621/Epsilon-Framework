# run_all_simulations.py
import subprocess
import sys
import time

simulations = [
    "bsd_conjecture.py",
    "collatz_toroidal_decay.py",
    "hodge_harmonic_phase_locking.py",
    "koide_toroidal_manifold.py",
    "navier_stokes_regularity.py",
    "odd_perfect_parity_defect.py",
    "p_vs_np_topological_equivalence.py",
    "poincare_epsilon_inversion.py",
    "riemann_phase_locking.py",
    "superfluid_dark_matter_rotation.py",
    "superfluid_plenum_ftl_phase.py"
]

def execute_suite():
    print("=" * 65)
    print("      EPSILON FRAMEWORK MASTER SIMULATION RUNNER      ")
    print("=" * 65)
    
    start_time = time.time()
    passed, failed = 0, 0

    for idx, sim in enumerate(simulations, 1):
        print(f"\n[{idx}/{len(simulations)}] Executing {sim}...")
        try:
            subprocess.run([sys.executable, sim], check=True)
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
