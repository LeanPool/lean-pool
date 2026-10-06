/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Consistency.AdmissibleTests
public import LeanPool.HighContrastHomogenization.Consistency.AspectRatioSharpness
public import LeanPool.HighContrastHomogenization.Consistency.ClosureH1aNecessity
public import LeanPool.HighContrastHomogenization.Consistency.ClosureH1aPairing
public import LeanPool.HighContrastHomogenization.Consistency.ConvexDilation
public import LeanPool.HighContrastHomogenization.Consistency.Dissolution
public import LeanPool.HighContrastHomogenization.Consistency.DomainCompleteness
public import LeanPool.HighContrastHomogenization.Consistency.Necessity
public import LeanPool.HighContrastHomogenization.Consistency.PrintedForm
public import LeanPool.HighContrastHomogenization.Consistency.QualitativeClass
public import LeanPool.HighContrastHomogenization.Consistency.WitnessField
public import LeanPool.HighContrastHomogenization.Consistency.WitnessSigmaField

/-!
# High-contrast homogenization: Consistency

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Consistency checks of the definitions

The definitions the paper's statements are written with are encodings, and an encoding can
be satisfied for reasons that have nothing to do with the object it is meant to denote: a
supremum over an empty family of tests is `0`, a class with no member makes every hypothesis
about its members vacuous, a Bochner average with a junk branch is not an infimum, and an
infimum of Loewner scalings is not visibly the minimum of spectral norms the paper prints.

The modules collected here check exactly that, one definition at a time: that the admissible
tests exist, that the coefficient space has a point and its sigma-fields separate points,
that the membership classes are neither empty nor unreachable from the printed completions,
that local uniform ellipticity supplies the analytic integrability condition, that the junk
branch of the coarse response is never attained, that the encodings of the intrinsic
contrast and of `Λ_0` are the printed minima, and where a hypothesis of one of these
definitions cannot be dropped.

None of these modules is a result of the paper, and no exported theorem depends on one.
Each names in its own doc-string the definition it checks and what would go wrong were the
check to fail.
-/
