/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.SpectralBound
public import LeanPool.HighContrastHomogenization.Setup.Contrast
public import LeanPool.HighContrastHomogenization.Setup.Geometry
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Setup.ResponsePositivity

/-!
# High-contrast homogenization: Setup

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Setup for the high-contrast polynomial-scale theorems

This is the object layer of the setup in `s.introduction`: the coefficient space and
its local sigma-fields, the integer translation action, the coarse block response
and its Schur data, the reference and annealed contrasts, and the triadic and
adapted geometry.  The two structural assumptions on the law and the coarse
ellipticity assumption are frozen declarations and live under `HCPoly.Frozen`.

**Scope of the coefficient class.**  The coefficient space used here is the set
of measurable fields that are locally uniformly elliptic: on every bounded subset
of `ℝ^d` a pair of ellipticity constants serves almost every value of the field
there, the pair being attached to the field and to the set rather than fixed in
advance.  No constant appearing in any statement below depends on such a pair.
The paper's standing condition `e.qualitative.ellipticity` requires local
essential bounds on `s`, `s⁻¹` and `kᵗ s⁻¹ k`; this is its formulation of local
uniform ellipticity. The class used here also implies the weaker local
integrability conditions needed by the analytic library. All quantitative
content — the reference aspect ratio
`Π`, the concentration gauge and its growth witness, the annealed contrast `Θ_m`,
and every dimensional constant — is unchanged.

## Module layout

* `HCPoly.Setup.CoefficientSpace` — the class `AEUniformlyEllipticField`, the
  carrier `CoeffSpace`, the translation action, and pointwise representatives.
* `HCPoly.Setup.LocalSigmaFields` — the generators of `F(U)`, the canonical
  measurable structure, unit separation, and measurability of the translation.
* `HCPoly.Setup.BlockAlgebra` — Schur data, the scalar Loewner bound, the
  intrinsic contrast, the reference aspect ratio, the matrix square root.
* `HCPoly.Setup.SpectralBound` — `specBound` is the least scalar Loewner bound;
  `matSqrt` is the unique positive semidefinite square root.
* `HCPoly.Setup.Contrast` — the conjugation identity and the printed form of the
  intrinsic contrast and of `Λ_0`.
* `HCPoly.Setup.Geometry` — triadic cubes, the rounding convention, adapted
  cells, ellipsoids.
* `HCPoly.Setup.Response` — the coarse response, the annealed block, `Θ_m`, and
  the identities that pin the annealed block to an expectation.
* `HCPoly.Setup.ResponsePositivity` — positive definiteness of the coarse
  response on the coefficient space.
-/
