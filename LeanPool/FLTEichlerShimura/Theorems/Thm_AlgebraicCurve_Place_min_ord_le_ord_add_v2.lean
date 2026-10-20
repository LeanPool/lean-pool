/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

Proof extracted from Definitions.FLT.Defs_IsogenyEndDatum_sharedLibrary.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_DivisorClassGroup

import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add

/-!
# Ultrametric inequality for the order at a place, allowing zero summands

The nonvanishing assumption on the sum suffices: either summand may be zero.
-/

public section publicSection

namespace AlgebraicCurve.Place

theorem min_ord_le_ord_add' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f g : F} (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  exact v.min_ord_le_ord_add hf hg hfg

end AlgebraicCurve.Place

end publicSection
