/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanPool.TrilinearHilbertTransform.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import LeanPool.TrilinearHilbertTransform.Auto.Sec16_3SummingUpdateLevels

/-!
# Boundedness of the trilinear Hilbert transform
-/

public section

namespace TrilinearHT

open MeasureTheory SchwartzMap Topology Filter

/-- **Main theorem.** The trilinear Hilbert transform is bounded `L³ × L³ × L³ → L¹`.

**Implementation notes:**
- We formulate the bound as an a priori estimate on Schwartz functions as is common practice.
-/
theorem trilinear_ht_bound :
    ∃ C : ℝ, ∀ f : Fin 3 → 𝓢(ℝ, ℂ),
      eLpNorm (T (fun i ↦ f i)) 1 ≤ (ENNReal.ofReal C) * ∏ i, eLpNorm (f i) 3 :=
  Auto.trilinear_ht_bound

end TrilinearHT

end
