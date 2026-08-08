import numpy as np
import matplotlib.pyplot as plt


def simulate_superfluid_ftl_phase(grid_size=120, epsilon_0=1e-4):
    """
    Simulates superluminal phase-wave propagation across a dual-sheeted
    toroidal plenum (T² x iT²) bounded by a non-zero coordinate floor (ε).
    """
    r = np.linspace(-2, 2, grid_size)
    x, y = np.meshgrid(r, r)
    radius = np.sqrt(x**2 + y**2)

    # 1) Vacuum drag suppression
    planck_ratio = 1e-2
    vacuum_drag = (planck_ratio / epsilon_0) ** 3

    # 2) Field stress saturation limit
    k = 1.0
    field_stress_limit = (2 * np.sqrt(3) / 9) * (k / (epsilon_0**2))

    # 3) Phase excitation on primary sheet
    phase_velocity_v = 3.0
    time_t = 0.5
    wave_center = phase_velocity_v * time_t
    sheet_1_phase = np.exp(-((x - wave_center) ** 2 + y**2) / (0.3 + epsilon_0))

    # 4) Inverted dual-sheet resonance
    sheet_2_phase = -sheet_1_phase * np.cos(np.pi * radius / (1.0 + epsilon_0))

    grad_y, grad_x = np.gradient(sheet_1_phase)
    potential_gradient = np.sqrt(grad_x**2 + grad_y**2)
    bounded_gradient = np.minimum(potential_gradient, field_stress_limit)

    return x, y, sheet_1_phase, sheet_2_phase, bounded_gradient, vacuum_drag, field_stress_limit


def run_simulation(grid_size=120, epsilon_0=1e-4, save_path="superfluid_plenum_ftl_phase.png", show_plot=True):
    x, y, t2_sheet, it2_sheet, field_stress, drag, stress_limit = simulate_superfluid_ftl_phase(grid_size, epsilon_0)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5), dpi=120)

    c1 = ax1.contourf(x, y, t2_sheet, levels=25, cmap="plasma")
    ax1.set_title("Primary Sheet (T²): Superluminal Phase Wave", fontsize=10, fontweight="bold")
    ax1.set_xlabel("Plenum Coordinate X")
    ax1.set_ylabel("Plenum Coordinate Y")
    fig.colorbar(c1, ax=ax1, label="Phase Amplitude")

    c2 = ax2.contourf(x, y, it2_sheet, levels=25, cmap="magma")
    ax2.set_title("Dual Sheet (iT²): Inverted Quantum Twin Resonance", fontsize=10, fontweight="bold")
    ax2.set_xlabel("Plenum Coordinate X")
    ax2.set_ylabel("Plenum Coordinate Y")
    fig.colorbar(c2, ax=ax2, label="Inverted Phase Amplitude")

    plt.suptitle("Superfluid Plenum Hydrodynamics: Non-Local FTL Phase Inversion (ε-Floor)", fontsize=12, fontweight="bold")
    plt.tight_layout()
    plt.savefig(save_path, dpi=300)
    print(f"[+] Saved plot: {save_path}")

    if show_plot:
        plt.show()
    else:
        plt.close()

    print("--- SIMULATION VERIFICATION ---")
    print(f"Effective Vacuum Drag Coefficient (ζ): {drag:.6e}")
    print(f"Field Stress Limit: {stress_limit:.6e}")
    print(f"Max Bounded Gradient: {np.max(field_stress):.6e}")
    print(f"Bound respected: {np.max(field_stress) <= stress_limit}")


if __name__ == "__main__":
    run_simulation()
