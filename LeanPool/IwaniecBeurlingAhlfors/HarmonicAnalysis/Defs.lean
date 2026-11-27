/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Order.LiminfLimsup
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Definitions: Fourier multipliers, the Beurling–Ahlfors transform, Dragičević's test functions

The definitions that the headline theorems of the library use: Fourier multipliers and their norms
on `L^p (V)`, `V` a Euclidean space, and on `L^p_0 (𝕋^ι)`; the Wirtinger derivatives; the
Beurling–Ahlfors transform and its powers; Dragičević's constants and test functions. Their theory
is in the other modules: `HarmonicAnalysis.FourierMultiplier.Basic`,
`HarmonicAnalysis.Torus.TrigPoly`, `HarmonicAnalysis.Complex.Wirtinger`,
`HarmonicAnalysis.BeurlingAhlfors.Basic`, `HarmonicAnalysis.BeurlingAhlfors.TestFunctions`,
`HarmonicAnalysis.BeurlingAhlfors.LowerBound`.

The block between the markers is copied word for word into
`palomar/FourierMultipliers/Challenge.lean` by `scripts/sync_challenge_defs.py`, and the imports
are the Challenge's.

The Fourier transform is Mathlib's, `𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv`, and `ℂ ≅ ℝ²` by
`x + iy ↦ (x, y)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace HarmonicAnalysis

-- BEGIN SHARED DEFINITIONS

/-! ### Fourier multipliers on a Euclidean space -/

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier multiplier with symbol `m`: `T_m f = 𝓕⁻¹ (m · 𝓕 f)`, by Mathlib's integral formulas
for `𝓕` and `𝓕⁻¹`. For a bounded measurable `m` and a Schwartz function `f`, `m · 𝓕 f` is
integrable and `T_m f (x) = ∫ m (ξ) 𝓕 f (ξ) e^{2πi ⟨ξ, x⟩} dξ`. -/
def fourierMultiplier (m : V → ℂ) (f : V → ℂ) : V → ℂ :=
  𝓕⁻ (fun ξ : V => m ξ • 𝓕 f ξ)

/-- `‖T_m‖_{L^p → L^p}`: the supremum, in `[0, ∞]`, of `‖T_m f‖_p / ‖f‖_p` over the Schwartz
functions `f` (dense in `L^p` for `1 ≤ p < ∞`; `0 / 0 = 0`). -/
def multiplierNorm (m : V → ℂ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ f : 𝓢(V, ℂ), eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume /
    eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume

end Euclidean

/-! ### Fourier multipliers on the torus -/

section Torus

open UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- The trigonometric polynomial `x ↦ Σ_n c_n e^{2πi ⟨n, x⟩}` on the torus `𝕋^ι = (ℝ / ℤ)^ι`, for
finitely supported coefficients `c`. -/
def trigPoly (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => a * mFourier n x

/-- The Fourier multiplier with symbol `m : ℤ^ι → ℂ` applied to the trigonometric polynomial with
coefficients `c`: `x ↦ Σ_n m (n) c_n e^{2πi ⟨n, x⟩}`. -/
def torusMultiplier (m : (ι → ℤ) → ℂ) (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => m n * a * mFourier n x

/-- `‖T_m‖_{L^p_0 (𝕋^ι) → L^p_0 (𝕋^ι)}`, `L^p_0` the subspace of mean-zero functions: the supremum,
in `[0, ∞]`, of `‖T_m f‖_p / ‖f‖_p` over the (dense) trigonometric polynomials `f` of mean zero
(`c₀ = 0`). The value `m (0)` does not matter. -/
def torusMultiplierNorm (m : (ι → ℤ) → ℂ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ (c : (ι → ℤ) →₀ ℂ) (_ : c 0 = 0),
    eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
      eLpNorm (trigPoly c) (ENNReal.ofReal p) volume

/-- The lattice point `n₀ + i n₁ ∈ ℂ` of `n ∈ ℤ²`. -/
def latticePoint (n : Fin 2 → ℤ) : ℂ := (n 0 : ℂ) + (n 1 : ℂ) * Complex.I

end Torus

/-! ### The Wirtinger derivatives -/

section Wirtinger

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Wirtinger derivative `∂g (z) = ½ (∂_x g (z) − i ∂_y g (z))` of a function `g : ℂ → F`
(`0` where `g` is not real-differentiable). -/
def dz (g : ℂ → F) (z : ℂ) : F :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 - Complex.I • fderiv ℝ g z Complex.I)

/-- The Wirtinger derivative `∂_zbar g (z) = ½ (∂_x g (z) + i ∂_y g (z))` of a function `g : ℂ → F`
(`0` where `g` is not real-differentiable). -/
def dzbar (g : ℂ → F) (z : ℂ) : F :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I)

end Wirtinger

/-! ### The Beurling–Ahlfors transform and its powers -/

/-- The symbol `m (ξ) = (conj ξ) / ξ` of the Beurling–Ahlfors transform (`m (0) = 0`). -/
def beurlingSymbol (ξ : ℂ) : ℂ := conj ξ / ξ

/-- `𝓑^k f = 𝓕⁻¹ (m^k · 𝓕 f)`, with `m (ξ) = (conj ξ) / ξ`. -/
def beurlingPow (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fourierMultiplier (fun ξ => beurlingSymbol ξ ^ k) f

/-- `‖𝓑^k‖_{L^p (ℝ²) → L^p (ℝ²)}`: the supremum, in `[0, ∞]`, of `‖𝓑^k f‖_p / ‖f‖_p` over the
(dense) Schwartz functions `f`. -/
def beurlingPowNorm (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  multiplierNorm (fun ξ => beurlingSymbol ξ ^ k) p

/-! ### Dragičević's constants and test functions -/

/-- Dragičević's constant `κ_n (p) = (1/q)_n / (1/p)_n`, `1/q = 1 − 1/p`, with the Pochhammer
symbol `(a)_n = a (a + 1) ⋯ (a + n − 1)`. -/
def beurlingKappa (n : ℕ) (p : ℝ) : ℝ :=
  (ascPochhammer ℝ n).eval (1 - p⁻¹) / (ascPochhammer ℝ n).eval p⁻¹

/-- `p* = max (p, p / (p − 1))`. -/
def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- The cutoff `g_n (x) = 1` for `x ≤ 1`, `exp (−(x − 1)^n)` for `x > 1`, which Dragičević (2011,
p. 465) gives as an example of a sufficiently smooth, rapidly decaying `g_n` equal to `1` on
`[0, 1]`. -/
def BeurlingAhlfors.testCutoff (n : ℕ) (x : ℝ) : ℝ := if x ≤ 1 then 1 else Real.exp (-(x - 1) ^ n)

/-- Dragičević's test function `f_{n,α} (z) = z^n |z|^{−2α} g_n (|z|)`, with this cutoff `g_n`. -/
def BeurlingAhlfors.testFun (n : ℕ) (α : ℝ) (z : ℂ) : ℂ :=
  z ^ n * ((‖z‖ ^ (-2 * α) * testCutoff n ‖z‖ : ℝ) : ℂ)

-- END SHARED DEFINITIONS

end HarmonicAnalysis
