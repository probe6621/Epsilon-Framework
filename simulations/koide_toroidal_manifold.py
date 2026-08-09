import numpy as np
import matplotlib.pyplot as plt


def simulate_epsilon_koide_manifold(epsilon_0=1e-4):
    """
    Simulates Koide's Formula (Q = 2/3) and 4D toroidal geometry
    under the Epsilon Framework (T² x iT²).
    """
    # 1) Charged lepton pole masses (MeV/c²)
    m_e = 0.51099895
    m_mu = 105.658375
    m_tau = 1776.86
    m_leptons = np.array([m_e, m_mu, m_tau])

    # Empirical Koide quotient
    sqrt_m = np.sqrt(m_leptons)
    Q_empirical = np.sum(m_leptons) / (np.sum(sqrt_m) ** 2)

    # 2) 4D manifold dimensional unification: N(4) = 6*pi^5
    n_dim = 4
    rotation_planes = (n_dim * (n_dim - 1)) // 2   # 6
    nested_levels = n_dim + 1                       # 5
    N_4_theoretical = rotation_planes * (np.pi ** nested_levels)
    m_p_m_e_empirical = 1836.15267343

    # 3) Topological phase saturation: 2/3
    deg_total = 3.0
    deg_saturated = 2.0
    Q_topological = deg_saturated / deg_total

    # 4) Illustrative neutrino hierarchy scaling
    m_neutrinos_eV = epsilon_0 * (m_leptons / N_4_theoretical) ** 2 * 1e11

    return Q_empirical, Q_topological, N_4_theoretical, m_p_m_e_empirical, m_leptons, m_neutrinos_eV


def run_simulation(epsilon_0=1e-4, save_path="koide_toroidal_manifold.png", show_plot=True):
    Q_emp, Q_topo, N4_theo, m_p_m_e_emp, m_l, m_v = simulate_epsilon_koide_manifold(epsilon_0=epsilon_0)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5), dpi=120)

    # Plot 1: Phase saturation
    angles = np.linspace(0, 2 * np.pi, 300)
    phase_e = np.sin(angles)
    phase_mu = np.sin(angles + 2 * np.pi / 3)
    phase_tau = np.full_like(angles, 0.05)

    ax1.plot(angles, phase_e, color="#00f2fe", linewidth=2, label=r"Saturated Phase $e$ (Degree 1)")
    ax1.plot(angles, phase_mu, color="#ff007f", linewidth=2, label=r"Saturated Phase $\mu$ (Degree 2)")
    ax1.plot(angles, phase_tau, "--", color="gold", linewidth=2, label=r"Vacuum Floor Anchor $\epsilon$ (Degree 3)")
    ax1.set_title(f"Manifold Phase Saturation: Q = {Q_topo:.4f} (2/3 Saturated)", fontsize=10, fontweight="bold")
    ax1.set_xlabel("Phase Angle (Radians)")
    ax1.set_ylabel("Excitation Amplitude")
    ax1.grid(True, linestyle="--", alpha=0.3)
    ax1.legend(loc="upper right", fontsize=8)

    # Plot 2: Neutrino hierarchy
    lepton_names = ["Electron (e)", "Muon (μ)", "Tau (τ)"]
    ax2.bar(lepton_names, m_v, color=["#00f2fe", "#00c6ff", "#ff007f"], alpha=0.85, edgecolor="white")
    ax2.set_yscale("log")
    ax2.set_title(r"Predicted Neutrino Mass Hierarchy: $m_{\nu_i} \propto \epsilon \cdot (m_{l_i}/N(4))^2$", fontsize=10, fontweight="bold")
    ax2.set_ylabel("Relative Neutrino Mass Scale (eV)", fontsize=9)
    ax2.grid(True, which="both", linestyle="--", alpha=0.3)

    plt.suptitle("Epsilon Framework: Koide Q=2/3 Topological Derivation & Spectrum", fontsize=12, fontweight="bold")
    plt.tight_layout()
    plt.savefig(save_path, dpi=300)
    print(f"[+] Saved plot: {save_path}")

    if show_plot:
        plt.show()
    else:
        plt.close()

    print("=== EPSILON KOIDE DERIVATION VERIFICATION ===")
    print(f"Empirical Koide Ratio Q: {Q_emp:.6f}")
    print(f"Topological Saturated Ratio Q: {Q_topo:.6f} (Exact 2/3)")
    print(f"Derived Proton/Electron Ratio N(4) = 6*pi^5: {N4_theo:.4f}")
    print(f"Empirical Proton/Electron Ratio: {m_p_m_e_emp:.4f}")
    print(f"Precision: {100 * (1 - abs(N4_theo - m_p_m_e_emp) / m_p_m_e_emp):.2f}%")
    print("Neutrino Scaling Output (relative eV):", m_v)


if __name__ == "__main__":
    run_simulation()
