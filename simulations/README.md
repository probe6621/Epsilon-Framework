# Epsilon Framework

Epsilon Framework is a collection of Python-based simulations exploring mathematical and topological ideas, including BSD-style rank verification, P vs NP collapse models, Yang–Mills mass-gap heuristics, and related geometric constructions.

## Quick start (for beginners)

1. Make sure Python 3 is installed:
   ```bash
   python3 --version
   ```

2. Install dependencies:
   ```bash
   python3 -m pip install -r simulations/requirements.txt
   ```

3. Run every simulation in one command:
   ```bash
   python3 simulations/run_all_simulations.py
   ```

The runner saves plots as `.png` files in the `simulations/` folder and runs in non-interactive mode so it does not stop waiting for plot windows.
