/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Numerics.Batch004
/-!
# Gerver sofa dependency batch

* `KernelOnly.LeanCertNumericsRows.FullPoint21`.
* `KernelOnly.LeanCertNumericsRows.FullImage21`.
-/

@[expose] public section

noncomputable section


section

/-!
# Direct 22D certificate, point residual 21

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_21_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (21 : Fin 22))
      (fullPointCache (21 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_21_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (21 : Fin 22) ∈
      fullPointCache (21 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (21 : Fin 22))
    full_point_21_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 21: strict self-map image

This theorem is isolated from the Jacobian-row theorem so each Lean process
checks one heavy proposition and then releases its memory before the next
module in the serial chain begins.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_image_21_inside :
    intervalStrictInside (fullImageCachedQ (21 : Fin 22))
      (unitBox (n := 22) (21 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end
