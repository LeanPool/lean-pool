/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanPool.Triangular.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import LeanPool.Triangular.Auto.TriangularHT

/-!
# Boundedness of the triangular Hilbert transform
-/

public section

namespace Triangular

open MeasureTheory SchwartzMap

/-- The triangular Hilbert transform is bounded on `L³ × L³ × L³`.
*Implementation notes:*
We formulate the bound as an a priori estimate on Schwartz functions as is common practice.
-/
theorem triangular_ht_bound :
    ∃ C : ℝ, ∀ F₀ F₁ F₂ : 𝓢(ℝ × ℝ, ℂ),
      ‖T F₀ F₁ F₂‖ₑ ≤ ENNReal.ofReal C * eLpNorm F₀ 3 * eLpNorm F₁ 3 * eLpNorm F₂ 3 :=
  Auto.triangular_ht_bound

end Triangular

end
