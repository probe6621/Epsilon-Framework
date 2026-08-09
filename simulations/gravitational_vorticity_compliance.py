import os
import matplotlib.pyplot as plt
import numpy as np

# Set headless backend for runner compatibility
plt.switch_backend("Agg")


def simulate_gravitational_compliance():
    # Grid Setup: Radial distance r (m) and Vorticity Shear Omega (rad/s)
    r = np.linspace(0.1, 2.0, 300)  # Core distance (meters)
    omega_shear = np.linspace(0, 1e4, 300)  # Counter-rotating shear frequency
    R, OMEGA = np.meshgrid(r, omega_shear)

    # Fundamental Vacuum Constants under Epsilon Framework
    G_0 = 6.67430e-11  # Nominal gravitational constant (m^3 kg^-1 s^-2)
    kappa_epsilon = 1.0  # Baseline vacuum compliance factor
    alpha_coupling = 5.0e-9  # Electro-spin coupling coefficient

    # Hydro-Electrodynamic Modulation Model:
    # G_eff = G_0 * [1 - kappa_epsilon * (alpha_coupling * OMEGA**2) / (1 + R**2)]
    g_ratio = 1.0 - kappa_epsilon * (
        (alpha_coupling * (OMEGA**2)) / (1.0 + R**2)
    )
    G_eff = G_0 * g_ratio

    # Plotting Configuration
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    fig.patch.set_facecolor("#111111")

    for ax in (ax1, ax2):
        ax.set_facecolor("#1a1a1a")
        ax.tick_params(colors="#cccccc")
        ax.xaxis.label.set_color("#cccccc")
        ax.yaxis.label.set_color("#cccccc")
        ax.title.set_color("#ffffff")
        for spine in ax.spines.values():
            spine.set_color("#444444")

    # Panel 1: 2D Contour Map of G_eff Modulation Ratio
    contour = ax1.contourf(
        R, OMEGA, g_ratio, levels=50, cmap="magma"
    )
    cbar = fig.colorbar(contour, ax=ax1)
    cbar.ax.yaxis.set_tick_params(color="#cccccc")
    plt.setp(plt.getp(cbar.ax.axes, "yticklabels"), color="#cccccc")
    cbar.set_label("Effective G Ratio (G_eff / G_0)", color="#cccccc")

    ax1.set_title("Hydrodynamic Vacuum G_eff Compliance Map")
    ax1.set_xlabel("Core Radius r (m)")
    ax1.set_ylabel("Toroidal Shear Omega (rad/s)")

    # Panel 2: Radial Profile Cross-Sections at Varied Shear Velocities
    shears_to_plot = [0, 2500, 5000, 7500, 10000]
    colors = ["#00f2fe", "#4facfe", "#43e97b", "#fa709a", "#ff0844"]

    for shear_val, col in zip(shears_to_plot, colors):
        idx = np.argmin(np.abs(omega_shear - shear_val))
        ax2.plot(
            r,
            g_ratio[idx, :],
            label=f"Omega = {shear_val} rad/s",
            color=col,
            linewidth=2,
        )

    ax2.axhline(
        1.0,
        color="#ffff00",
        linestyle="--",
        alpha=0.7,
        label="Nominal Newtonian G_0",
    )
    ax2.set_title("Radial Decay of Gravitational Shift")
    ax2.set_xlabel("Core Radius r (m)")
    ax2.set_ylabel("G_eff / G_0")
    ax2.legend(
        facecolor="#222222", edgecolor="#444444", labelcolor="#ffffff", loc="lower right"
    )
    ax2.grid(True, linestyle=":", alpha=0.3, color="#666666")

    plt.tight_layout()

    # Save Output Artifact
    out_dir = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "visuals"
    )
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(
        out_dir, "simulations__gravitational_vorticity_compliance.png"
    )
    plt.savefig(out_path, dpi=300, facecolor=fig.get_facecolor(), edgecolor="none")
    plt.close()
    print(f"✅ Generated: {out_path}")


if __name__ == "__main__":
    simulate_gravitational_compliance()
