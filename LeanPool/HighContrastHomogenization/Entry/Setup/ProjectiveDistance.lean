/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.Moments
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# High-contrast homogenization: Entry.Setup.ProjectiveDistance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Projective Distance

The block calculus of the doubled matrices, the canonical metric `m(F)` built from it, and the
projective distance `d_pr` the printed statements are stated with.  The module serves
`e.scale.selection.projective.distance`, with the canonical metric
`e.scale.selection.canonical.metric` and the reflection `𝐑` of
`e.renormalization.geometry.update` as the constructions its definition reads through.
-/

section
/-!
## The arithmetic the printed displays perform on doubled blocks

The paper writes ordinary matrix operations on `2d`-by-`2d` matrices — a
difference `P - I_{2d}`, a trace, a logarithm of a determinant, the operator norm `|M|`,
the normalization `F^{-1/2} H F^{-1/2}`, and the swap block `𝐑` — while the development
carries a `2d`-by-`2d` matrix as the four-field `BlockMat d`.  This file is the translation
layer those displays need, and nothing else: each definition is the named operation read
through `toFullBlockMat`.

Conventions, stated because a reader comparing this file to the manuscript must not have to
guess:

* `|M|` is Mathlib's L2 operator norm, as `HCPoly/Entry/Geometry/QuadraticForm.lean` already fixes
it
  for `Mat d`.
* `F^{-1/2}` is `matSqrt (F⁻¹)`, the canonical positive semidefinite square root of the
  inverse fixed in `HCPoly/Setup/BlockAlgebra.lean`; on a block that is not positive definite
  the inverse and the root take their junk values there, so `normalizedBlock` carries no
  positivity hypothesis and the printed hypothesis `F > 0` stays with the consumer.
* `blockLogDet` is `log (det H)`, which is Mathlib's junk `log` of a nonpositive determinant
  off the positive blocks, again by the same convention.

`blockSwap` is CoarseGraining's `Book.Ch02.blockR`, which is already the printed matrix; it is
named here only so that the printed symbol `𝐑` has a Lean name.
-/

namespace HCPolySupport.HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The operator norm `|H|` of a doubled block: Mathlib's L2 operator norm of the
`2d`-by-`2d` matrix. -/
@[expose]
def blockOpNorm (H : BlockMat d) : ℝ :=
  ‖toFullBlockMat H‖

/-- The swap block `𝐑 = ((0, I_d), (I_d, 0))` near `e.scale.selection.projective.distance`.  This
is CoarseGraining's reflection block `Book.Ch02.blockR`; the printed display is that matrix. -/
@[expose]
def blockSwap (d : ℕ) : BlockMat d :=
  Book.Ch02.blockR d

end

end HCPolySupport.HighContrast
end

section
/-!
## The canonical metric `m(F)`

Near `e.scale.selection.canonical.metric`:

> Set `𝐑 := ((0, I_d), (I_d, 0))`.  For a positive `2d`-by-`2d` block `F`, define
> `m(F) := (F^{1/2}(F^{-1/2}𝐑F^{-1}𝐑F^{-1/2})^{1/2}F^{1/2})_{22}^{-1} > 0`.

The definition matches the printed display symbol for symbol.  `F^{1/2}` and the inner `(·)^{1/2}`
are `matSqrt`, the
canonical positive semidefinite square root of `HCPoly/Setup/BlockAlgebra.lean`; `𝐑` is
`blockSwap`; `(·)_{22}` is the lower-right `d`-by-`d` block, the `.lowerRight` field of the
doubled block; and the outer `(·)^{-1}` is the inverse of that `d`-by-`d` matrix.

The printed hypothesis "positive `F`" and the printed assertion `m(F) > 0` are not part of
the definition: the first stays with the consumer, and the second is a statement about the
value, proved separately.  Off the positive blocks every root and inverse takes its junk
value.

An alternative characterization defines `m(E)` as the positive factor of the factorization
`M(E) = G_{−g(E)}^t diag(m(E), m(E)^{-1}) G_{−g(E)}` of the canonical block `M(E) = E # E^♯`
and reaches the printed formula through a geometric-mean layer.  The printed display is a
closed expression in `F` and is written here as such, which is why the definition below is
called `explicitCanonicalMetric`.
-/

open HCPolySupport.HighContrast (matSqrt)
namespace HCPolySupport.HighContrast

noncomputable section

variable {d : ℕ}

/-- The canonical metric
`m(F) = (F^{1/2}(F^{-1/2}𝐑F^{-1}𝐑F^{-1/2})^{1/2}F^{1/2})_{22}^{-1}`
(`e.scale.selection.canonical.metric`), the printed closed expression.

The `canonicalMetric` of the published `HCPoly` library
(`HCPoly/Setup/TransportObjects.lean`) is the same quantity, defined by a characterization rather
than by a formula: it
is `canonMetric (toFullBlockMat F)`, the positive factor of the canonical factorization
`M(F) = G_{−g}^t diag(m, m^{-1}) G_{−g}` (`HCPoly/Geometry/Canonical.lean`), selected by the
uniqueness of that factorization.  That the factor is given by the expression below is a
theorem about positive `F`, not a definitional identity, and nothing in this library proves
it, so the two definitions keep different names. -/
@[expose]
def explicitCanonicalMetric (F : BlockMat d) : Mat d :=
  (ofFullBlockMat
        (matSqrt (toFullBlockMat F) *
          matSqrt
            (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
              (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
              matSqrt ((toFullBlockMat F)⁻¹)) *
          matSqrt (toFullBlockMat F))).lowerRight⁻¹

end

end HCPolySupport.HighContrast
end

section
/-!
## The projective distance `d_pr([𝔪_0],[𝔪_1])`

Near `e.scale.selection.projective.distance`:

> For positive `d`-by-`d` matrices `𝔪_0, 𝔪_1`, define
> `d_pr([𝔪_0],[𝔪_1]) := ½ log (λ_max(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}) / λ_min(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}))`.

The extreme eigenvalues are written in their Loewner forms, which is how the setup layer
already writes `λ_max`: `specBound M` of `HCPoly/Setup/BlockAlgebra.lean` is
`inf {t ≥ 0 : M ≤ tI}`, the largest eigenvalue of a symmetric positive semidefinite `M`, and
`specMin` below is the dual `sup {t : tI ≤ M}`.  No matrix square root and no eigenvalue
family enters a scalar quantity; that convention is the setup layer's, not this file's.

Three things are recorded because a reader comparing this file to the manuscript would
otherwise have to reconstruct them:

* The printed argument is the projective **class** `[𝔪]`, and the function here takes
  representatives.  That `d_pr` depends only on the classes — it is invariant under
  `𝔪_i ↦ c 𝔪_i` with `c > 0` — is a statement about the value and is proved, not definitional.
  The class itself is rendered as the relation `ProjectiveEq`, which is what the case split
  of the geometry update `e.renormalization.geometry.update` tests.
* The printed hypothesis "positive `𝔪_0, 𝔪_1`" is not part of the definition.  Off the
  positive matrices, `𝔪_0⁻¹` and its square root take the junk values of
  `HCPoly/Setup/BlockAlgebra.lean`, `specMin` of a matrix with an empty lower-threshold set is
  totalized by `sSup`, and `log` of a nonpositive quotient is Mathlib's junk `log`.
* The quotient is written as printed, `λ_max / λ_min`, not as the product
  `λ_max(X) · λ_max(X⁻¹)`; the two agree on positive `X`, but only the first is the display.

An alternative definition writes the distance through the two relative sizes,
`½(log relSize(𝔪_1,𝔪_0) + log relSize(𝔪_0,𝔪_1))`, and proves the printed form as a
theorem (`projDist_eq_norm_form`).  That shape is **not** adopted: it is the printed display
only after that theorem, and a definition may not embed a proved identity.  The `d`-by-`d`
normalization `𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}` is the analogue of `normalizedBlock`, and that shape
is adopted.
-/

open HCPolySupport.HighContrast (matSqrt specBound)
namespace HCPolySupport.HighContrast

noncomputable section

variable {d : ℕ}

/-- The smallest eigenvalue of a symmetric matrix, in Loewner form: `sup {t : t I ≤ M}`.
This is the dual of `specBound`, which is `inf {t ≥ 0 : M ≤ t I}`. -/
@[expose]
def specMin (M : Mat d) : ℝ :=
  sSup {t : ℝ | MatLoewnerLE (t • (1 : Mat d)) M}

/-- The normalized matrix `𝔪_0^{-1/2} 𝔪_1 𝔪_0^{-1/2}`, the root being the canonical
positive semidefinite square root of `𝔪_0⁻¹`. -/
@[expose]
def normalizedMat (m₀ m₁ : Mat d) : Mat d :=
  matSqrt m₀⁻¹ * m₁ * matSqrt m₀⁻¹

/-- The projective class relation `[𝔪_0] = [𝔪_1]`: the two matrices differ by a positive
scalar.  This is the case distinction the geometry update `e.renormalization.geometry.update`
makes. -/
@[expose]
def ProjectiveEq (m₀ m₁ : Mat d) : Prop :=
  ∃ c : ℝ, 0 < c ∧ m₁ = c • m₀

/-- The projective distance
`d_pr([𝔪_0],[𝔪_1]) = ½ log (λ_max(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}) / λ_min(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}))`
(`e.scale.selection.projective.distance`). -/
@[expose]
def projectiveDistance (m₀ m₁ : Mat d) : ℝ :=
  1 / 2 * Real.log (specBound (normalizedMat m₀ m₁) / specMin (normalizedMat m₀ m₁))

end

end HCPolySupport.HighContrast
end
