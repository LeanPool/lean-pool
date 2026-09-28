/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Numerics.Batch002
/-!
# Gerver sofa dependency batch

* `KernelOnly.LeanCertNumericsRows.FullImage10`.
* `KernelOnly.LeanCertNumericsRows.Full11`.
* `KernelOnly.LeanCertNumericsRows.FullPoint11`.
* `KernelOnly.LeanCertNumericsRows.FullImage11`.
* `KernelOnly.LeanCertNumericsRows.Full12`.
* `KernelOnly.LeanCertNumericsRows.FullPoint12`.
* `KernelOnly.LeanCertNumericsRows.FullImage12`.
* `KernelOnly.LeanCertNumericsRows.Full13`.
* `KernelOnly.LeanCertNumericsRows.FullPoint13`.
* `KernelOnly.LeanCertNumericsRows.FullImage13`.
* `KernelOnly.LeanCertNumericsRows.Full14`.
* `KernelOnly.LeanCertNumericsRows.FullPoint14`.
* `KernelOnly.LeanCertNumericsRows.FullImage14`.
* `KernelOnly.LeanCertNumericsRows.Full15`.
* `KernelOnly.LeanCertNumericsRows.FullPoint15`.
* `KernelOnly.LeanCertNumericsRows.FullImage15`.
-/

@[expose] public section

noncomputable section


section

/-!
# Direct 22D certificate, row 10: strict self-map image

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
theorem full_image_10_inside :
    intervalStrictInside (fullImageCachedQ (10 : Fin 22))
      (unitBox (n := 22) (10 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 11: Jacobian bound

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
theorem full_row_11_lt :
    intervalMatrixRowBound fullPJ (11 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 11

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_11_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (11 : Fin 22))
      (fullPointCache (11 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_11_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (11 : Fin 22) ∈
      fullPointCache (11 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (11 : Fin 22))
    full_point_11_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 11: strict self-map image

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
theorem full_image_11_inside :
    intervalStrictInside (fullImageCachedQ (11 : Fin 22))
      (unitBox (n := 22) (11 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 12: Jacobian bound

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
theorem full_row_12_lt :
    intervalMatrixRowBound fullPJ (12 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 12

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_12_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (12 : Fin 22))
      (fullPointCache (12 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_12_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (12 : Fin 22) ∈
      fullPointCache (12 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (12 : Fin 22))
    full_point_12_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 12: strict self-map image

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
theorem full_image_12_inside :
    intervalStrictInside (fullImageCachedQ (12 : Fin 22))
      (unitBox (n := 22) (12 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 13: Jacobian bound

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
theorem full_row_13_lt :
    intervalMatrixRowBound fullPJ (13 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 13

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_13_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (13 : Fin 22))
      (fullPointCache (13 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_13_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (13 : Fin 22) ∈
      fullPointCache (13 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (13 : Fin 22))
    full_point_13_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 13: strict self-map image

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
theorem full_image_13_inside :
    intervalStrictInside (fullImageCachedQ (13 : Fin 22))
      (unitBox (n := 22) (13 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 14: Jacobian bound

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
theorem full_row_14_lt :
    intervalMatrixRowBound fullPJ (14 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 14

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_14_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (14 : Fin 22))
      (fullPointCache (14 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_14_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (14 : Fin 22) ∈
      fullPointCache (14 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (14 : Fin 22))
    full_point_14_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 14: strict self-map image

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
theorem full_image_14_inside :
    intervalStrictInside (fullImageCachedQ (14 : Fin 22))
      (unitBox (n := 22) (14 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 15: Jacobian bound

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
theorem full_row_15_lt :
    intervalMatrixRowBound fullPJ (15 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 15

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_15_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (15 : Fin 22))
      (fullPointCache (15 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_15_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (15 : Fin 22) ∈
      fullPointCache (15 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (15 : Fin 22))
    full_point_15_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 15: strict self-map image

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
theorem full_image_15_inside :
    intervalStrictInside (fullImageCachedQ (15 : Fin 22))
      (unitBox (n := 22) (15 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end
