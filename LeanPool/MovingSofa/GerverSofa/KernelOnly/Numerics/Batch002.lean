/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Numerics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.LeanCertNumericsRows.FullPoint05`.
* `KernelOnly.LeanCertNumericsRows.FullImage05`.
* `KernelOnly.LeanCertNumericsRows.Full06`.
* `KernelOnly.LeanCertNumericsRows.FullPoint06`.
* `KernelOnly.LeanCertNumericsRows.FullImage06`.
* `KernelOnly.LeanCertNumericsRows.Full07`.
* `KernelOnly.LeanCertNumericsRows.FullPoint07`.
* `KernelOnly.LeanCertNumericsRows.FullImage07`.
* `KernelOnly.LeanCertNumericsRows.Full08`.
* `KernelOnly.LeanCertNumericsRows.FullPoint08`.
* `KernelOnly.LeanCertNumericsRows.FullImage08`.
* `KernelOnly.LeanCertNumericsRows.Full09`.
* `KernelOnly.LeanCertNumericsRows.FullPoint09`.
* `KernelOnly.LeanCertNumericsRows.FullImage09`.
* `KernelOnly.LeanCertNumericsRows.Full10`.
* `KernelOnly.LeanCertNumericsRows.FullPoint10`.
-/

@[expose] public section

noncomputable section


section

/-!
# Direct 22D certificate, point residual 5

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_5_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (5 : Fin 22))
      (fullPointCache (5 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_5_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (5 : Fin 22) ∈
      fullPointCache (5 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (5 : Fin 22))
    full_point_5_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 5: strict self-map image

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
theorem full_image_5_inside :
    intervalStrictInside (fullImageCachedQ (5 : Fin 22))
      (unitBox (n := 22) (5 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 6: Jacobian bound

The row modules form a deliberate dependency chain.  Lake therefore checks
only one expensive closed kernel proposition at a time instead of launching
all 22 rows concurrently and exhausting RAM.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_row_6_lt :
    intervalMatrixRowBound fullPJ (6 : Fin 22) < qTarget := by
  unfold fullPJ
  rw [jacobianCache_eq]
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, point residual 6

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_6_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (6 : Fin 22))
      (fullPointCache (6 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_6_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (6 : Fin 22) ∈
      fullPointCache (6 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (6 : Fin 22))
    full_point_6_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 6: strict self-map image

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
theorem full_image_6_inside :
    intervalStrictInside (fullImageCachedQ (6 : Fin 22))
      (unitBox (n := 22) (6 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 7: Jacobian bound

The row modules form a deliberate dependency chain.  Lake therefore checks
only one expensive closed kernel proposition at a time instead of launching
all 22 rows concurrently and exhausting RAM.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_row_7_lt :
    intervalMatrixRowBound fullPJ (7 : Fin 22) < qTarget := by
  unfold fullPJ
  rw [jacobianCache_eq]
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, point residual 7

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_7_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (7 : Fin 22))
      (fullPointCache (7 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_7_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (7 : Fin 22) ∈
      fullPointCache (7 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (7 : Fin 22))
    full_point_7_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 7: strict self-map image

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
theorem full_image_7_inside :
    intervalStrictInside (fullImageCachedQ (7 : Fin 22))
      (unitBox (n := 22) (7 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 8: Jacobian bound

The row modules form a deliberate dependency chain.  Lake therefore checks
only one expensive closed kernel proposition at a time instead of launching
all 22 rows concurrently and exhausting RAM.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_row_8_lt :
    intervalMatrixRowBound fullPJ (8 : Fin 22) < qTarget := by
  unfold fullPJ
  rw [jacobianCache_eq]
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, point residual 8

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_8_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (8 : Fin 22))
      (fullPointCache (8 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_8_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (8 : Fin 22) ∈
      fullPointCache (8 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (8 : Fin 22))
    full_point_8_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 8: strict self-map image

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
theorem full_image_8_inside :
    intervalStrictInside (fullImageCachedQ (8 : Fin 22))
      (unitBox (n := 22) (8 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 9: Jacobian bound

The row modules form a deliberate dependency chain.  Lake therefore checks
only one expensive closed kernel proposition at a time instead of launching
all 22 rows concurrently and exhausting RAM.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_row_9_lt :
    intervalMatrixRowBound fullPJ (9 : Fin 22) < qTarget := by
  unfold fullPJ
  rw [jacobianCache_eq]
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, point residual 9

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_9_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (9 : Fin 22))
      (fullPointCache (9 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_9_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (9 : Fin 22) ∈
      fullPointCache (9 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (9 : Fin 22))
    full_point_9_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 9: strict self-map image

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
theorem full_image_9_inside :
    intervalStrictInside (fullImageCachedQ (9 : Fin 22))
      (unitBox (n := 22) (9 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 10: Jacobian bound

The row modules form a deliberate dependency chain.  Lake therefore checks
only one expensive closed kernel proposition at a time instead of launching
all 22 rows concurrently and exhausting RAM.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_row_10_lt :
    intervalMatrixRowBound fullPJ (10 : Fin 22) < qTarget := by
  unfold fullPJ
  rw [jacobianCache_eq]
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, point residual 10

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_10_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (10 : Fin 22))
      (fullPointCache (10 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_10_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (10 : Fin 22) ∈
      fullPointCache (10 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (10 : Fin 22))
    full_point_10_contained

end PartALeanCert
end GerverSofa

end

end

end
