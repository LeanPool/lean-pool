/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransport
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NormScaling

/-!
# TranslationTransportNorms

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The A4 transport of the normalized norms

`TranslationTransport.lean` moves the *equation* from the frozen theorem's
frame (the window `z + □_{n+2}` at the sample `ω`) to the harmonic slot's frame
(the origin cube `□_{n+2}` at `translateCutoffSample z ω`).  This module moves
the *norms* that appear on the right-hand side of `e.good.scale.homog`, and
records the one geometric simplification the interior regime provides.

Everything here is an **exact identity**: Lebesgue measure is translation
invariant, so a normalized average over `z + A` of `f` is the normalized average
over `A` of `f(· + z)`, with no constant.

## The interior regime collapses the intersected windows

The frozen statement carries its right-hand-side norms on the *intersected*
window `(z + □_{n+2}) ∩ □_m`.  On the
frontier-empty gate — which is exactly the hypothesis of the anchor's sharpened
interior clause — the gate's own inclusion makes that intersection the bare
translate `z + □_{n+2}`.  So in the interior regime the intersection is pure
bookkeeping and disappears (`inter_eq_of_frontier_inter_empty`).

## Main results

* `inter_eq_of_frontier_inter_empty` — the intersected window is the translate.
* `normalizedL2SqOnSet_translateSet`, `normalizedSetAverage_translateSet`,
  `normalizedSetAverage_vecNormSq_translateSet` — the three norm transports.
* `normalizedL2SqOnSet_sub_volumeAverage_translateSet` — the mean-subtracted
  `L²` square of the anchor's solution on the parent window equals that of the
  transported solution on `□_{n+2}`; both the norm and the subtracted mean move
  together.

## References

* ABK26, `e.good.scale.homog`.
* CoarseGraining, `Homogenization/Book/Ch01/Theorems/NormScaling.lean`
  (`Ch01.volumeAverage_translateSet_eq_comp_addRight`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The interior regime collapses the intersected window -/

/-- **In the interior regime the anchor's intersected window is the bare
translate.**  The frontier-empty gate gives `z + □_k ⊆ □_m`, so the intersection
with `□_m` is inert. -/
theorem inter_eq_of_frontier_inter_empty {k m : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hfr : ((fun y => z + y) '' openCubeSet (originCube d k)) ∩
        frontier (openCubeSet (originCube d m)) = ∅) :
    ((fun y => z + y) '' openCubeSet (originCube d k)) ∩
        openCubeSet (originCube d m) =
      (fun y => z + y) '' openCubeSet (originCube d k) :=
  Set.inter_eq_left.mpr
    (image_add_openCubeSet_subset_of_frontier_inter_empty hz hfr)

/-! ## 2. The norm transports -/

/-- The normalized average transports exactly. -/
theorem normalizedSetAverage_translateSet (z : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) :
    normalizedSetAverage (translateSet z U) f =
      normalizedSetAverage U (fun x => f (x + z)) :=
  Ch01.volumeAverage_translateSet_eq_comp_addRight z U f

/-- The normalized `L²` square transports exactly. -/
theorem normalizedL2SqOnSet_translateSet (z : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) :
    normalizedL2SqOnSet (translateSet z U) f =
      normalizedL2SqOnSet U (fun x => f (x + z)) :=
  Ch01.volumeAverage_translateSet_eq_comp_addRight z U (fun x => f x ^ 2)

/-- The normalized gradient energy transports exactly. -/
theorem normalizedSetAverage_vecNormSq_translateSet (z : Vec d) (U : Set (Vec d))
    (G : Vec d → Vec d) :
    normalizedSetAverage (translateSet z U) (fun x => vecNormSq (G x)) =
      normalizedSetAverage U (fun x => vecNormSq (G (x + z))) :=
  Ch01.volumeAverage_translateSet_eq_comp_addRight z U (fun x => vecNormSq (G x))

/-! ## 3. The mean-subtracted `L²` square of the anchor's solution -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
