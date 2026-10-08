/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.OriginCubeSymmetry.Geometry
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.OriginCubeSymmetry.H1Actions
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.OriginCubeSymmetry.H10Actions

/-!
# Coordinate symmetry on centered cubes

Re-exports the original CoarseGraining coordinate geometry and Sobolev symmetry constructors
from commit `c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4` (Apache-2.0).
Geometry, H¹ transport, and H¹₀ approximation transport are separated while retaining all
original namespaces, mathematical definitions, theorem statements, and proof bodies.
-/
