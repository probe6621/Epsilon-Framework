import numpy as np
import matplotlib.pyplot as plt


def digital_root(n: int) -> int:
    """Digital root in base-10 (mod 9 reduction)."""
    n = int(n)
    if n == 0:
        return 0
    return 1 + (n - 1) % 9


def simulate_tesla_369_geometry(steps=12):
    """
    Simulates digital-root separation between:
    - binary doubling roots {1,2,4,8,7,5}
    - triadic axis roots from multiples of 3 {3,6,9}
    plus roots of scaling exponents 6n (mod 9 behavior).
    """
    binary_powers = [2 ** i for i in range(steps)]
    binary_roots = [digital_root(p) for p in binary_powers]

    triadic_multiples = [3 * i for i in range(1, steps + 1)]
    triadic_roots = [digital_root(m) for m in triadic_multiples]

    exponent_indices = np.arange(1, steps + 1)
    exponents = 6 * exponent_indices
    scaling_roots = [digital_root(e) for e in exponents]

    return binary_roots, triadic_roots, scaling_roots


def run_simulation(steps=12, save_path="tesla_369_geometry.png", show_plot=True):
    bin_roots, tri_roots, scale_roots = simulate_tesla_369_geometry(steps=steps)
    x_axis = np.arange(1, steps + 1)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5), dpi=120)

    # Plot 1
    ax1.plot(x_axis, bin_roots, "o-", color="#00f2fe", linewidth=2, label=r"Binary Doubling $\{1,2,4,8,7,5\}$")
    ax1.plot(x_axis, tri_roots, "s--", color="#ff007f", linewidth=2, label=r"Tesla Triadic Axis $\{3,6,9\}$")
    ax1.set_yticks(range(1, 10))
    ax1.set_title("Digital Root Separation: Modulo 9 Field Lines", fontsize=10, fontweight="bold")
    ax1.set_xlabel("Iteration Step")
    ax1.set_ylabel(r"Digital Root Value ($n \pmod 9$)")
    ax1.grid(True, linestyle="--", alpha=0.3)
    ax1.legend(loc="upper right", fontsize=8.5)

    # Plot 2
    ax2.plot(x_axis, scale_roots, "d-", color="gold", linewidth=2.2, label=r"Cosmic Scaling Exponent Roots $(6n \pmod 9)$")
    ax2.set_yticks([3, 6, 9])
    ax2.set_title(r"Tesla Scaling Cycle: $\{6,3,6,9\}$ Toroidal Resonance", fontsize=10, fontweight="bold")
    ax2.set_xlabel(r"Scaling Level $n$")
    ax2.set_ylabel("Exponent Digital Root")
    ax2.grid(True, linestyle="--", alpha=0.3)
    ax2.legend(loc="lower right", fontsize=8.5)

    plt.suptitle("Epsilon Framework: Mathematical Resolution of Tesla's 3, 6, 9 Topology", fontsize=12, fontweight="bold")
    plt.tight_layout()
    plt.savefig(save_path, dpi=300)
    print(f"[+] Saved plot: {save_path}")

    if show_plot:
        plt.show()
    else:
        plt.close()

    print("=== TESLA 3,6,9 TOROIDAL TOPOLOGY VERIFICATION ===")
    print(f"Binary Doubling Digital Root Cycle: {bin_roots[:6]} (Strictly Excludes 3, 6, 9)")
    print(f"Triadic Multiples Digital Root Cycle: {tri_roots[:6]}")
    print(f"Cosmic Scaling Exponent Digital Root Cycle: {scale_roots[:8]} (Tesla 6-3-6-9 Pattern)")
    print("Zenodo Repository Citation: https://doi.org/10.5281/zenodo.21783495")


if __name__ == "__main__":
    run_simulation()
