/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.Nikolskii
public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.Basic
public import LeanPool.FunctionSpaces.MeasureSpaces.Sobolev.Embeddings

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# `L_2` Sobolev spaces on the torus

Mathlib's Fourier basis `e_k`, `k ∈ ℤ^d`, of `L_2(𝕋^d)` (`UnitAddTorus.mFourierBasis`), with
the level `deg k = max_i |k_i|`, is a spectral scheme (`Torus.fourierScheme`).  Its
approximants of complexity `n` are the `L_2` classes of the trigonometric polynomials of
degree `< n`, so it is the scheme `Torus.trigScheme` transported to `L_2`
(`Torus.toLp_trigScheme_eq`).

The **Sobolev space** `H^s(𝕋^d)`, `s > 0`, consists of the `f ∈ L_2(𝕋^d)` with

`∑_{k ∈ ℤ^d} (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞`,

normed by the square root of this sum; it is the image of `ℓ²(ℤ^d)` under
`c ↦ ∑_k (1 + deg k)^(-s) c_k e_k` (`Torus.sobolevSpace`, `Torus.mem_range_sobolev_iff`). The weight
`(1 + max_i |k_i|)^(2s)` is equivalent to the more common `(1 + |k|²)^s`, up to constants depending
on `d` and `s`; it is used because the degree `max_i |k_i|` is the one that indexes the
trigonometric polynomials. By the spectral theory of `FunctionSpaces.MeasureSpaces.Spectral` it
satisfies Jackson's and Bernstein's inequalities with constant `1`, and so is a Sobolev space for
the scheme of trigonometric polynomials in the sense of `FunctionScheme.SobolevSpace`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal BoundedContinuousFunction TorusHaar lp

namespace Torus

variable (d : Type*) [Fintype d]

/-- The **Fourier basis** of `L_2(𝕋^d)` with the level `deg k = max_i |k_i|`, a spectral
scheme. -/
noncomputable def fourierScheme : SpectralScheme (d → ℤ) (Lp ℂ 2 (volume : Measure (UnitAddTorus
d))) where
  basis := mFourierBasis
  level := deg
  finite_level n := by
    convert (boxLt d n).finite_toSet using 1
    ext k; simp [mem_boxLt]

/-- The `L_2` classes of the trigonometric polynomials of degree `< n` are the span of the
Fourier basis elements of degree `< n`. -/
theorem toLp_trigScheme_eq :
    (trigScheme d).toLp volume 2 = (fourierScheme d).toScheme := by
  ext n f
  change f ∈ (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ) '' (trigPoly d n : Set _) ↔
    f ∈ ((fourierScheme d).span n : Set _)
  have hmap : (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ : _ → _) '' (trigPoly d n : Set _)
      = SetLike.coe ((trigPoly d n).map
          (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ).toLinearMap) := by
    rw [Submodule.map_coe]; rfl
  rw [hmap, trigPoly, Submodule.map_span, ← Set.image_comp]
  have hset : ((BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ).toLinearMap ∘ trigMonomial) ''
      (boxLt d n : Set (d → ℤ)) = mFourierBasis '' {k | deg k < n} := by
    ext g
    simp only [Set.mem_image, Function.comp_apply, Finset.mem_coe, mem_boxLt, Set.mem_ofPred_eq,
      ContinuousLinearMap.coe_coe, toLp_trigMonomial, coe_mFourierBasis]
  rw [hset]
  rfl

variable {d}

/-- The **Sobolev space `H^s(𝕋^d)`**, `s > 0`, as a Sobolev space for the scheme of
trigonometric polynomials in `L_2`: the image of `ℓ²(ℤ^d)` under
`c ↦ ∑_k (1 + deg k)^(-s) c_k e_k`, with Jackson's and Bernstein's inequalities of order `s`
and constant `1`. -/
noncomputable def sobolevSpace (s : ℝ) (hs : 0 < s) :
    (trigScheme d).SobolevSpace volume 2 ℓ²(d → ℤ, ℂ) :=
  ApproximationScheme.SmoothnessSpace.congr (toLp_trigScheme_eq d).symm
    ((fourierScheme d).toSmoothnessSpace s hs)

/-- `H^s(𝕋^d)` has order `s`. -/
@[simp]
theorem sobolevSpace_order (s : ℝ) (hs : 0 < s) : (sobolevSpace (d := d) s hs).order = s := rfl

/-- The embedding of `H^s(𝕋^d)` is `J_s`. -/
theorem sobolevSpace_incl (s : ℝ) (hs : 0 < s) (c : ℓ²(d → ℤ, ℂ)) :
    (sobolevSpace (d := d) s hs).incl c = (fourierScheme d).sobolevEmbed s hs.le c := rfl

/-- **Membership in `H^s(𝕋^d)`** through the Fourier coefficients: `f ∈ L_2(𝕋^d)` lies in the
range of the Sobolev embedding exactly when
`∑_k (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞`. -/
theorem mem_range_sobolev_iff (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus
d))) :
    f ∈ Set.range (sobolevSpace (d := d) s hs).incl ↔
      Memℓp (fun k => ((((1 + deg k : ℕ) : ℝ) ^ s : ℝ) : ℂ) * mFourierCoeff f k) 2 := by
  have := (fourierScheme d).mem_range_sobolevEmbed_iff s hs.le f
  simp only [fourierScheme, mFourierBasis_repr] at this
  exact this

end Torus
