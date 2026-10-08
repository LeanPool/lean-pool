/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Maximizer
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Ellipticity

/-!
# Coarse-graining support: Support.CoarseGraining.ResponseIdentities.Foundations

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Foundational scalar deterministic identities for `ResponseJ` (aggregate)

Historically a single monolithic file; now split along namespace/section
boundaries into the three modules imported above. This shim re-exports
everything so downstream consumers keep working unchanged.
-/
