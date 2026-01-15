import numpy as np
import matplotlib.pyplot as plt
import mpmath

mpmath.mp.dps = 25  # High precision

def geometric_zeta_analytic(sigma, t):
    """
    Computes the True Geometric Zeta components using analytic continuation.

    Args:
        sigma (float): Dilation parameter
        t (float): Rotation parameter

    Returns:
        (scalar, bivector): The split components.
    """
    s = mpmath.mpc(sigma, t)
    z_val = mpmath.zeta(s)

    # Map back to Geometric Algebra components
    # Real part -> Scalar (Dilation)
    # Imaginary part -> Bivector Coefficient (Rotation)
    return float(z_val.real), float(z_val.imag)

def scan_analytic_line(start_t, end_t, step):
    t_values = np.arange(start_t, end_t, step)
    scalars = []
    bivectors = []

    print(f"Scanning the Analytic Critical Line...")

    for t in t_values:
        s, b = geometric_zeta_analytic(0.5, t)
        scalars.append(s)
        bivectors.append(b)

    return t_values, np.array(scalars), np.array(bivectors)

# --- Run the High-Precision Simulation ---

# Target: The first Zero at t = 14.134725
t_range, scalar_vals, bivector_vals = scan_analytic_line(12, 35, 0.01)

# Plotting
plt.figure(figsize=(12, 6))

# Plot the components
plt.plot(t_range, scalar_vals, label='Scalar (Dilation Balance)', color='blue', linewidth=1.5)
plt.plot(t_range, bivector_vals, label='Bivector (Rotation Balance)', color='red', linewidth=1.5)

# Highlight the Zeros
zeros = [14.1347, 21.0220, 25.0108]
for z in zeros:
    plt.axvline(z, color='green', linestyle=':', alpha=0.8)
    plt.scatter([z], [0], color='green', zorder=5)

plt.axhline(0, color='black', linewidth=1)
plt.title('The True Geometric Zeta: Analytic Continuation Decomposed')
plt.xlabel('Rotation Parameter (t)')
plt.ylabel('Amplitude')
plt.legend()
plt.grid(True, alpha=0.3)

# Add annotations
plt.text(14.2, 2, "Zero #1\n(14.13)", color='green')
plt.text(21.1, 2, "Zero #2\n(21.02)", color='green')
plt.text(25.1, 2, "Zero #3\n(25.01)", color='green')

plt.savefig('/home/tracy/development/Riemann/Lean/geometric_zeta_scipy.png', dpi=150, bbox_inches='tight')
print("Plot saved to geometric_zeta_scipy.png")

# Precision Check at First Zero
s_zero, b_zero = geometric_zeta_analytic(0.5, 14.13472514)
print(f"\nPrecision Check at t = 14.13472514:")
print(f"Scalar Component:   {s_zero:.8f}")
print(f"Bivector Component: {b_zero:.8f}")
print(f"Total Magnitude:    {np.sqrt(s_zero**2 + b_zero**2):.8f}")
