import numpy as np

class ESCTFEngine:
    def __init__(self, grid_size=16, epsilon=1e-4, dt=1e-3, kappa=0.1, eta_mass=0.09568e-9):
        self.N = grid_size
        self.eps = epsilon
        self.dt = dt
        self.kappa = kappa
        self.eta_mass = eta_mass

        # Grid initialization (T2 x iT2 coordinates: real spatial angle theta, mirror phase phi)
        self.theta = np.linspace(0, 2 * np.pi, self.N, endpoint=False)
        self.phi = np.linspace(0, 2 * np.pi, self.N, endpoint=False)
        self.TH, self.PH = np.meshgrid(self.theta, self.phi)

        # Phase 1: Initialize Bounded Metric Tensor (g_ij = g0 + eps * delta_ij)
        # Spatial variation simulating curvature near a potential singularity
        self.g = np.ones((self.N, self.N)) + 0.95 * np.cos(self.TH) * np.sin(self.PH)
        self.g = np.maximum(self.g, self.eps)  # Enforce non-zero floor

        # Initialize Mass Density (rho) and Defect Tensor C(m,n)
        self.rho = 1000.0 + 200.0 * np.sin(self.TH)  # Mass density
        self.C = np.sin(2 * self.TH) * np.cos(3 * self.PH)  # Initial off-diagonal defect

        # Phase Flag Matrix (0 = Outer T2, 1 = Inverted Mirror iT2)
        self.phase_map = np.zeros((self.N, self.N), dtype=int)

    def compute_energy_tension(self):
        # E_tension = rho * q = eta_mass * rho^2
        return self.eta_mass * (self.rho ** 2)

    def step(self):
        # Phase 2: Compute Energy Tension
        E_tension = self.compute_energy_tension()

        # Phase 3: Update Metric with Epsilon Lower Bound
        # Ricci-like relaxation with defect coupling term
        Ricci_approx = -0.5 * (np.roll(self.g, 1, axis=0) - 2 * self.g + np.roll(self.g, -1, axis=0))
        dg_dt = -2.0 * Ricci_approx + 0.1 * self.C * self.g
        self.g += self.dt * dg_dt

        # Strictly enforce plenum floor: det(g) >= eps
        self.g = np.maximum(self.g, self.eps)

        # Phase 4: Singularity Avoidance via Phase Inversion (theta -> theta + pi)
        # Condition: Near plenum floor threshold
        inversion_mask = (self.g <= 1.5 * self.eps) & (self.phase_map == 0)
        if np.any(inversion_mask):
            self.phase_map[inversion_mask] = 1  # Shift to mirror surface iT2
            self.TH[inversion_mask] = (self.TH[inversion_mask] + np.pi) % (2 * np.pi)
            print(f"[Phase Inversion Triggered] {np.sum(inversion_mask)} nodes routed to iT2 mirror surface.")

        # Phase 5: Defect Relaxation (dC/dt = -kappa * (Laplacian(C) + E_tension * C))
        laplacian_C = (
            np.roll(self.C, 1, axis=0)
            + np.roll(self.C, -1, axis=0)
            + np.roll(self.C, 1, axis=1)
            + np.roll(self.C, -1, axis=1)
            - 4 * self.C
        )

        dC_dt = -self.kappa * (laplacian_C + E_tension * self.C)
        self.C += self.dt * dC_dt

    def run(self, steps=1000, tol=1e-8):
        print(f"--- Initializing ESCTF Simulation (Grid: {self.N}x{self.N}, Plenum Floor ε: {self.eps}) ---")
        for step_idx in range(steps):
            self.step()
            max_defect = np.max(np.abs(self.C))
            if step_idx % 200 == 0:
                print(
                    f"Step {step_idx:4d} | Max Off-Diagonal Defect ||C(m,n)||: {max_defect:.10e} | Min g: {np.min(self.g):.6e}"
                )
            if max_defect < tol:
                print(f"--- Convergence Reached at Step {step_idx}! Defect C(m,n) -> 0 ---")
                break


if __name__ == "__main__":
    sim = ESCTFEngine(grid_size=32, epsilon=1e-4)
    sim.run(steps=1000)
