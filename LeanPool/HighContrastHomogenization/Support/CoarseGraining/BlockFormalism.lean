/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.Structures
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.MatrixIdentities
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.EllipticBounds
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.Properties

/-!
# Coarse-graining support: Support.CoarseGraining.BlockFormalism

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Block formalism (aggregate re-export)

Previously a 1298-line monolithic module; now split along thematic
boundaries into the four files imported above. Shim for backward
compatibility.
-/
