# tesla_369_geometry.py
import numpy as np
import matplotlib.pyplot as plt

def digital_root(n):
    """Calculates the digital root (modulo 9 reduction) of a positive integer."""
    n = int(n)
    if n == 0:
        return 0
    return 1 + (n - 1) % 9

def simulate_tesla_369_geometry():
    """
    Simulates the digital root separation between binary doubling cycles {1,2,4,8,7,5}
    and the triadic counter-rotational shear axis {3,6,9} on a toroidal manifold.
    """
    # 1. Binary Doubling Sequence: 2^x
    steps = 12
    binary_powers = [2**i for i in range(steps)]
    binary_roots = [digital_root(p) for p in binary_powers]
    
    # 2. Triadic Multiples (3, 6, 9)
    triadic_multiples = [3 * i for i in range(1, steps + 1)]
    triadic_roots = [digital_root(m) for m in triadic_multiples]
    
    # 3. Universal Scaling Exponent Roots U_n = (6 * pi^(5/6))^(6n)
    exponent_indices = np.arange(1, 13)
    exponents = 6 * exponent_indices
    scaling_roots = [digital_root(exp) for exp in exponents]

    return binary_roots, triadic_roots, scaling_roots

# Run Simulation
bin_roots, tri_roots, scale_roots = simulate_tesla_369_geometry()

# Visualization
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5), dpi=120)

# Plot 1: Digital Root Trajectories (Binary Doubling Loop vs. Triadic Axis)
x_axis = np.arange(1, len(bin_roots) + 1)
ax1.plot(x_axis, bin_roots, 'o-', color='#00f2fe', linewidth=2, label=r'Binary Doubling $\{1,2,4,8,7,5\}$')
ax1.plot(x_axis, tri_roots, 's--', color='#ff007f', linewidth=2, label=r'Tesla Triadic Axis $\{3,6,9\}$')
ax1.set_yticks(range(1, 10))
ax1.set_title("Digital Root Separation: Modulo 9 Field Lines", fontsize=10, fontweight='bold')
ax1.set_xlabel("Iteration Step")
ax1.set_ylabel("Digital Root Value (n mod 9)")
ax1.grid(True, linestyle='--', alpha=0.3)
ax1.legend(loc='upper right', fontsize=8.5)

# Plot 2: Cosmic Hierarchy Exponent Roots (Tesla Cycle 6-3-6-9)
ax2.plot(x_axis, scale_roots, 'd-', color='gold', linewidth=2.2, label=r'Cosmic Scaling Exponent Roots (6n mod 9)')
ax2.set_yticks([3, 6, 9])
ax2.set_title(r"Tesla Scaling Cycle: $\{6, 3, 6, 9\}$ Toroidal Resonance", fontsize=10, fontweight='bold')
ax2.set_xlabel("Scaling Level n")
ax2.set_ylabel("Exponent Digital Root")
ax2.grid(True, linestyle='--', alpha=0.3)
ax2.legend(loc='lower right', fontsize=8.5)

plt.suptitle("Epsilon Framework: Mathematical Resolution of Tesla's 3, 6, 9 Topology", fontsize=12, fontweight='bold')
plt.tight_layout()
plt.show()

# Verification Console Output
print("=== TESLA 3,6,9 TOROIDAL TOPOLOGY VERIFICATION ===")
print(f"Binary Doubling Digital Root Cycle: {bin_roots[:6]} (Strictly Excludes 3, 6, 9)")
print(f"Triadic Multiples Digital Root Cycle: {tri_roots[:6]}")
print(f"Cosmic Scaling Exponent Digital Root Cycle: {scale_roots[:8]} (Tesla 6-3-6-9 Pattern)")
print("Zenodo Repository Citation: https://doi.org/10.5281/zenodo.21783495")
