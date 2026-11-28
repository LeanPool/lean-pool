/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.LocalWeyl
public import LeanPool.FunctionSpaces.Torus.Sobolev

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Fourier basis as a continuous spectral basis

The trigonometric monomials `e_k`, `k ∈ ℤ^d`, are the eigenfunctions of the Laplacian on the torus
`𝕋^d`, `Δ e_k = -4π² |k|² e_k`. With the level `deg k = max_i |k_i|` they form a continuous
spectral basis (`ContinuousSpectralBasis`, `Torus.fourierEigenbasis`): the Fourier basis of
`L_2(𝕋^d)`, represented by the bounded continuous functions `Torus.trigMonomial k`. Its spans are
the trigonometric polynomials (`Torus.basisSpan_fourierEigenbasis`), so its scheme is the
trigonometric scheme (`Torus.basisScheme_fourierEigenbasis`), and the general results for
continuous spectral bases hold on the torus. The hypotheses of those results are theorems here:

* **the local Weyl bound** of dimension `d` (`Torus.localWeylBound_fourierEigenbasis`):
  `∑_{deg k < n} |e_k(x)|² ≤ 2^d n^d`, since `|e_k| = 1` and there are at most `(2n)^d`
  frequencies of degree `< n`;
* **the Nikolskii property** of dimension `d` (`Torus.hasNikolskii_fourierEigenbasis`), from the
  power trick of `FunctionSpaces.Torus.Nikolskii`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus FunctionScheme
open scoped ENNReal BoundedContinuousFunction TorusHaar

namespace Torus

variable (d : Type*) [Fintype d]

/-- The **Fourier basis as a continuous spectral basis** of `L_2(𝕋^d)`, an eigenbasis of the
Laplacian: the trigonometric monomials `e_k` with the level `deg k = max_i |k_i|`. -/
noncomputable def fourierEigenbasis :
    ContinuousSpectralBasis (d → ℤ) (volume : Measure (UnitAddTorus d)) where
  toSpectralScheme := fourierScheme d
  basisFun := trigMonomial
  toLp_basisFun k := by
    rw [toLp_trigMonomial]
    exact (congrFun coe_mFourierBasis k).symm

variable {d}

/-- The level of `e_k` is `deg k`. -/
@[simp]
theorem fourierEigenbasis_level (k : d → ℤ) : (fourierEigenbasis d).level k = deg k := rfl

/-- The continuous basis functions are the trigonometric monomials. -/
@[simp]
theorem fourierEigenbasis_basisFun (k : d → ℤ) :
    (fourierEigenbasis d).basisFun k = trigMonomial k := rfl

/-- The span of the basis functions of level `< n` is the space of trigonometric polynomials of
degree `< n`. -/
theorem basisSpan_fourierEigenbasis (n : ℕ) :
    (fourierEigenbasis d).basisSpan n = trigPoly d n := by
  rw [ContinuousSpectralBasis.basisSpan, trigPoly]
  congr 2
  ext k
  simp [mem_boxLt]

/-- The scheme of the basis functions is the trigonometric scheme. -/
theorem basisScheme_fourierEigenbasis : (fourierEigenbasis d).basisScheme = trigScheme d := by
  ext n a
  change a ∈ (fourierEigenbasis d).basisSpan n ↔ a ∈ trigPoly d n
  rw [basisSpan_fourierEigenbasis]

/-- The levels `< n` are the frequencies of degree `< n`. -/
theorem levelSet_fourierEigenbasis (n : ℕ) : (fourierEigenbasis d).levelSet n = boxLt d n := by
  ext k
  rw [ContinuousSpectralBasis.mem_levelSet, mem_boxLt, fourierEigenbasis_level]

/-- **The local Weyl bound on the torus**: `∑_{deg k < n} |e_k(x)|² ≤ 2^d n^d`, since every
monomial has modulus `1` and there are at most `(2n)^d` frequencies of degree `< n`. -/
theorem localWeylBound_fourierEigenbasis :
    (fourierEigenbasis d).LocalWeylBound (Fintype.card d) (2 ^ Fintype.card d) := by
  refine ⟨by positivity, fun n _ x => ?_⟩
  rw [levelSet_fourierEigenbasis]
  have h1 : ∑ k ∈ boxLt d n, ‖(fourierEigenbasis d).basisFun k x‖ ^ 2 = (boxLt d n).card := by
    simp only [fourierEigenbasis_basisFun, norm_trigMonomial_apply, one_pow, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  rw [h1, Real.rpow_natCast]
  calc ((boxLt d n).card : ℝ) ≤ ((2 * n) ^ Fintype.card d : ℕ) := by
        exact_mod_cast card_boxLt_le n
    _ = 2 ^ Fintype.card d * (n : ℝ) ^ Fintype.card d := by push_cast; ring

/-- **The Nikolskii property of the Fourier eigenbasis**, of dimension `d`. -/
theorem hasNikolskii_fourierEigenbasis :
    (fourierEigenbasis d).basisScheme.HasNikolskii volume (Fintype.card d) := by
  rw [basisScheme_fourierEigenbasis]
  exact trigScheme_hasNikolskii

end Torus
