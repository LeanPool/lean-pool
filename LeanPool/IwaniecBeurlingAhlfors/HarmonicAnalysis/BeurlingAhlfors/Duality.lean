/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Duality

/-!
# `‖𝓑^k‖_p = ‖𝓑^k‖_q`

`HarmonicAnalysis.beurlingPowNorm_conjExponent`: for `1 < p < ∞` and `q = p / (p − 1)`,
`‖𝓑^k‖_{L^p} = ‖𝓑^k‖_{L^q}`. The argument is Carbonaro–Dragičević–Kovač's (§1.3.1): `𝓑^{−k}`,
the multiplier with symbol `conj m^k`, is the `L²`-adjoint of `𝓑^k`, so `‖𝓑^k‖_p = ‖𝓑^{−k}‖_q`
(`HarmonicAnalysis.multiplierNorm_conj_conjExponent`); and `𝓑^{−k} f = conj (𝓑^k (conj f))`,
because `m (−ξ) = m (ξ)`, so `‖𝓑^{−k}‖_q = ‖𝓑^k‖_q`
(`HarmonicAnalysis.multiplierNorm_conj_comp_neg`).

## References

* A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), [arXiv:2109.08369](https://arxiv.org/abs/2109.08369),
  §1.3.1.
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), Exercise 1.16.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

namespace HarmonicAnalysis

/-- `‖𝓑^k‖_{L^p} = ‖𝓑^k‖_{L^q}` for `1 < p < ∞`, `q = p / (p − 1)`. -/
theorem beurlingPowNorm_conjExponent (k : ℕ) {p : ℝ} (hp : 1 < p) :
    beurlingPowNorm k p = beurlingPowNorm k (p / (p - 1)) := by
  unfold beurlingPowNorm
  rw [multiplierNorm_conj_conjExponent (measurable_beurlingSymbol.pow_const k)
    ⟨1, fun ξ => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_beurlingSymbol_le ξ)⟩ hp,
    ← multiplierNorm_conj_comp_neg (fun ξ => conj (beurlingSymbol ξ ^ k))]
  simp [beurlingSymbol_neg]

end HarmonicAnalysis
