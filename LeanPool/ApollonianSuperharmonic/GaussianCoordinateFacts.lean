/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt


/-!
# GaussianCoordinateFacts

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace GaussianCoordinateFacts

/-- Shared equal identity for GaussianCoordinateFacts. -/
theorem equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := by
  classical
  rcases u with ⟨u, w⟩
  rcases v with ⟨v, z⟩
  simp_all

/-- Shared pairSwap identity for GaussianCoordinateFacts. -/
theorem pairSwap (u v : GaussianInt) : ({u, v} : Finset GaussianInt) = {v, u} := by
  classical
  ext z
  simp [or_comm]

end GaussianCoordinateFacts
end ApollonianSuperharmonic

end
