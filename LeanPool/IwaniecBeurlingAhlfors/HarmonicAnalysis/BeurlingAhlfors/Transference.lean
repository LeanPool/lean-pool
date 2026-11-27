/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Transference.Homogeneous

/-!
# The powers of the Beurling–Ahlfors transform on `𝕋²`, and transference

* `HarmonicAnalysis.torusBeurlingPow k c`: `𝓑^k` on the torus `𝕋²`, the multiplier
  `m (n₀ + i n₁)^k`, `m (ξ) = (conj ξ) / ξ`, applied to the trigonometric polynomial with
  coefficients `c`;
* `HarmonicAnalysis.torusBeurlingPowNorm k p = ‖𝓑^k‖_{L^p_0 (𝕋²) → L^p_0 (𝕋²)}`, on mean-zero
  trigonometric polynomials.

`HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm`: `‖𝓑^k‖_{L^p (ℝ²)} ≤
‖𝓑^k‖_{L^p_0 (𝕋²)}` for `1 < p < ∞`, the inequality `I ≤ II` of Corollary 5.7.6 of
Hytönen–van Neerven–Veraar–Weis (HNVW; `HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm`)
for the symbol `m^k`, which is continuous off `0` and homogeneous of degree `0`.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*, Ergebnisse
  der Mathematik 63, Springer, 2016: Corollary 5.7.6 (pp. 462–463).
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace HarmonicAnalysis

/-- `𝓑^k` on `𝕋²`, the multiplier `m (n₀ + i n₁)^k`, applied to the trigonometric polynomial with
coefficients `c`. -/
def torusBeurlingPow (k : ℕ) (c : (Fin 2 → ℤ) →₀ ℂ) (x : UnitAddTorus (Fin 2)) : ℂ :=
  torusMultiplier (fun n => beurlingSymbol (latticePoint n) ^ k) c x

/-- `‖𝓑^k‖_{L^p_0 (𝕋²) → L^p_0 (𝕋²)}`, on mean-zero trigonometric polynomials. -/
def torusBeurlingPowNorm (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  torusMultiplierNorm (fun n => beurlingSymbol (latticePoint n) ^ k) p

/-- Transference (HNVW, Corollary 5.7.6): `‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}` for
`1 < p < ∞`. -/
theorem beurlingPowNorm_le_torusBeurlingPowNorm (k : ℕ) {p : ℝ} (hp : 1 < p) :
    beurlingPowNorm k p ≤ torusBeurlingPowNorm k p :=
  multiplierNorm_le_torusMultiplierNorm (m := fun ξ => beurlingSymbol ξ ^ k)
    (fun ξ hξ => (continuousAt_beurlingSymbol hξ).pow k)
    (fun t ht ξ => by rw [beurlingSymbol_ofReal_mul ht.ne']) hp

end HarmonicAnalysis
