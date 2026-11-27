/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.HaarMeasure
public import LeanPool.FunctionSpaces.ApproximationSpaces.Instances.NTermHilbertBasis

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# `n`-term trigonometric approximation

The trigonometric monomials `e_k(x) = exp(2πi ⟨k, x⟩)`, `k ∈ ℤ^d`, form Mathlib's Hilbert basis
of `L_2(𝕋^d)` (`UnitAddTorus.mFourierBasis`), with the Fourier coefficients `f̂(k)` as
coefficients (`UnitAddTorus.mFourierBasis_repr`). Best `n`-term approximation from this basis
approximates `f` by combinations `∑_{k ∈ Λ} c_k e_k` of at most `n` monomials, with frequencies
`Λ` chosen for each `f`. The theorem of Stechkin and DeVore for Hilbert bases
(`HilbertBasis.memApprox_nTerm_iff`) describes its approximation spaces by the Fourier
coefficients: for `0 < τ < 2` and `θ = 1/τ - 1/2`,

`f ∈ A^θ_τ(L_2(𝕋^d), n-term)  ↔  ∑_{k ∈ ℤ^d} |f̂(k)|^τ < ∞`   (`Torus.memApprox_nTerm_iff`).

For `τ = 1` the right side says that the Fourier series of `f` converges absolutely, Stechkin's
original setting. Linear approximation by the trigonometric polynomials of degree `< n` leads
instead to conditions on the sizes `(1 + max_i |k_i|)^s |f̂(k)|`, with the frequencies ordered by
degree, such as the Sobolev spaces `H^s(𝕋^d)` of `Torus.sobolevSpace`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus ApproximationScheme
open scoped ENNReal TorusHaar

namespace Torus

variable {d : Type*} [Fintype d]

/-- **`n`-term trigonometric approximation in `L_2(𝕋^d)`**: for `0 < τ < 2` and
`θ = 1/τ - 1/2`, `f ∈ L_2(𝕋^d)` lies in the approximation space `A^θ_τ` of `n`-term
approximation from the Fourier basis, the dictionary of the multiples `c e_k`, iff its Fourier
coefficients lie in `ℓ_τ`, `∑_{k ∈ ℤ^d} |f̂(k)|^τ < ∞`. This is the theorem of Stechkin and
DeVore (`HilbertBasis.memApprox_nTerm_iff`) for Mathlib's Fourier basis, whose coefficients are
the Fourier coefficients (`UnitAddTorus.mFourierBasis_repr`). For `τ < 1` the space is only
quasi-normed, and the condition is stronger than absolute convergence of the Fourier series;
for `τ = 1` it is absolute convergence, Stechkin's theorem. Linear approximation by
trigonometric polynomials of degree `< n` gives instead weighted `ℓ_2` conditions on the
coefficients, such as the Sobolev spaces of `Torus.sobolevSpace`. -/
theorem memApprox_nTerm_iff {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (nTerm (mFourierBasis (d := d)).coeffDictionary).MemApprox (1 / τ - 1 / 2)
        (ENNReal.ofReal τ) f ↔ ∑' k, ‖mFourierCoeff f k‖ₑ ^ τ < ∞ := by
  have h := mFourierBasis.memApprox_nTerm_iff hτ0 hτ2 f
  simp only [mFourierBasis_repr] at h
  exact h

end Torus
