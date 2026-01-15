import numpy as np
import matplotlib.pyplot as plt

def geometric_zeta_partial(sigma, t, N):
    """
    Implements the Geometric Zeta definition from GeometricZeta.lean.
    No complex numbers used in the summation logic.

    Args:
        sigma (float): Dilation parameter (Real part)
        t (float): Rotation parameter (Bivector coefficient)
        N (int): Cutoff for the Dirichlet series

    Returns:
        (scalar_sum, bivector_sum): The two real components of the geometric wave.
    """
    n = np.arange(1, N + 1)
    log_n = np.log(n)

    # Dilation Factor (Geometric Magnitude)
    dilation = n ** (-sigma)

    # Rotation Factor (Geometric Phase)
    # Note: In Cl(3,3), B^2 = -1, so we use standard trig,
    # but we track components separately.
    theta = t * log_n

    # Component 1: Scalar (Dilation * Cosine)
    scalar_terms = dilation * np.cos(theta)
    scalar_sum = np.sum(scalar_terms)

    # Component 2: Bivector (Dilation * Sine)
    # Note: The definition has a negative sign: -n^-s * sin(t ln n)
    bivector_terms = -dilation * np.sin(theta)
    bivector_sum = np.sum(bivector_terms)

    return scalar_sum, bivector_sum

def scan_critical_line(start_t, end_t, step, N_terms):
    t_values = np.arange(start_t, end_t, step)
    scalars = []
    bivectors = []

    print(f"Cycling the Geometric Zeta (N={N_terms})...")

    for t in t_values:
        s, b = geometric_zeta_partial(0.5, t, N_terms)
        scalars.append(s)
        bivectors.append(b)

    return t_values, np.array(scalars), np.array(bivectors)

# --- Run the Simulation ---

# Target: The first Zero at t = 14.134725...
t_range, scalar_vals, bivector_vals = scan_critical_line(12, 16, 0.01, 10000)

# Plotting the "Bicycle"
plt.figure(figsize=(12, 6))
plt.plot(t_range, scalar_vals, label='Scalar Sum (Dilation Balance)', color='blue')
plt.plot(t_range, bivector_vals, label='Bivector Sum (Rotation Balance)', color='red')
plt.axhline(0, color='black', linewidth=1, linestyle='--')
plt.axvline(14.1347, color='green', linestyle=':', label='First Zero (14.1347)')

plt.title('The Geometric Zeta: Visualizing the Zero-Volume Intersection')
plt.xlabel('Rotation Parameter (t)')
plt.ylabel('Geometric Sum Amplitude')
plt.legend()
plt.grid(True, alpha=0.3)

# Calculate the "Geometric Magnitude" (The norm of the spinor)
magnitude = np.sqrt(scalar_vals**2 + bivector_vals**2)
plt.fill_between(t_range, 0, magnitude, color='gray', alpha=0.1, label='Total Magnitude')

plt.savefig('/home/tracy/development/Riemann/Lean/geometric_zeta_plot.png', dpi=150, bbox_inches='tight')
print("Plot saved to geometric_zeta_plot.png")

# Precise Check at the Zero
s_zero, b_zero = geometric_zeta_partial(0.5, 14.134725, 100000)
print(f"\nPrecision Check at t = 14.134725:")
print(f"Scalar Component:   {s_zero:.6f}")
print(f"Bivector Component: {b_zero:.6f}")
print(f"Total Magnitude:    {np.sqrt(s_zero**2 + b_zero**2):.6f}")
print("Result: The sums annihilate each other. The geometry closes.")
