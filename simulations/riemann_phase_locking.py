import numpy as np
import matplotlib.pyplot as plt


def epsilon_boundary_force(sigma, t, epsilon_0=1e-5):
    """
    Computes the geometric phase-shear restoring torque on the dual torus (T^2 x iT^2).
    - sigma = Re(s), the real component of the zero candidate.
    - t = Im(s), the imaginary height along the critical line.
    - epsilon_0 = non-zero boundary floor condition.
    """
    delta_sigma = sigma - 0.5
    phase_shear = np.sin(2 * np.pi * delta_sigma) * np.exp(-epsilon_0 * np.abs(t))
    restoring_force = -phase_shear / (np.abs(delta_sigma) ** 2 + epsilon_0)
    return restoring_force


def simulate_zero_trajectories(num_zeros=10, steps=200, dt=0.01):
    """
    Simulates hypothetical zeros starting off Re(s)=0.5 and locking into equilibrium.
    """
    np.random.seed(42)
    initial_sigmas = np.random.uniform(0.1, 0.9, num_zeros)
    t_values = np.linspace(14.13, 50.0, num_zeros)

    trajectories = np.zeros((steps, num_zeros))
    trajectories[0, :] = initial_sigmas

    for step in range(1, steps):
        for i in range(num_zeros):
            current_sigma = trajectories[step - 1, i]
            force = epsilon_boundary_force(current_sigma, t_values[i])
            trajectories[step, i] = current_sigma + force * dt

    return trajectories, t_values


def run_simulation(save_path="riemann_phase_locking_plot.png", show_plot=True):
    steps = 200
    trajectories, t_values = simulate_zero_trajectories(num_zeros=8, steps=steps)

    plt.figure(figsize=(10, 6), dpi=120)
    time_axis = np.arange(steps)

    for i in range(trajectories.shape[1]):
        plt.plot(time_axis, trajectories[:, i], label=f"Zero {i+1} (t ≈ {t_values[i]:.1f})")

    plt.axhline(0.5, color="gold", linestyle="--", linewidth=2.5, label="Critical Line Re(s) = 0.5")
    plt.axhspan(0.0, 0.5, color="blue", alpha=0.03)
    plt.axhspan(0.5, 1.0, color="red", alpha=0.03)

    plt.title("Riemann Zeta Zero Phase-Locking under Toroidal Boundary Geometry", fontsize=12, fontweight="bold")
    plt.xlabel("Phase Convergence Steps", fontsize=10)
    plt.ylabel("Re(s) [Critical Strip Position]", fontsize=10)
    plt.ylim(0.0, 1.0)
    plt.grid(True, linestyle=":", alpha=0.6)
    plt.legend(loc="upper right", fontsize=8)
    plt.tight_layout()

    plt.savefig(save_path, dpi=300)
    print(f"[+] Saved plot: {save_path}")

    if show_plot:
        plt.show()
    else:
        plt.close()


if __name__ == "__main__":
    run_simulation()
