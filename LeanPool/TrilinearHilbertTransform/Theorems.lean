/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

public import LeanPool.TrilinearHilbertTransform.Auto.Sec163SummingUpdateLevels

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
  TrilinearHT.Auto.trilinear_ht_bound

end TrilinearHT

end
