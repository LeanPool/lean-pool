/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Numerics.Batch003
/-!
# Gerver sofa dependency batch

* `KernelOnly.LeanCertNumericsRows.Full16`.
* `KernelOnly.LeanCertNumericsRows.FullPoint16`.
* `KernelOnly.LeanCertNumericsRows.FullImage16`.
* `KernelOnly.LeanCertNumericsRows.Full17`.
* `KernelOnly.LeanCertNumericsRows.FullPoint17`.
* `KernelOnly.LeanCertNumericsRows.FullImage17`.
* `KernelOnly.LeanCertNumericsRows.Full18`.
* `KernelOnly.LeanCertNumericsRows.FullPoint18`.
* `KernelOnly.LeanCertNumericsRows.FullImage18`.
* `KernelOnly.LeanCertNumericsRows.Full19`.
* `KernelOnly.LeanCertNumericsRows.FullPoint19`.
* `KernelOnly.LeanCertNumericsRows.FullImage19`.
* `KernelOnly.LeanCertNumericsRows.Full20`.
* `KernelOnly.LeanCertNumericsRows.FullPoint20`.
* `KernelOnly.LeanCertNumericsRows.FullImage20`.
* `KernelOnly.LeanCertNumericsRows.Full21`.
-/

@[expose] public section

noncomputable section


section

/-!
# Direct 22D certificate, row 16: Jacobian bound

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
theorem full_row_16_lt :
    intervalMatrixRowBound fullPJ (16 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 16

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_16_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (16 : Fin 22))
      (fullPointCache (16 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_16_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (16 : Fin 22) ∈
      fullPointCache (16 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (16 : Fin 22))
    full_point_16_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 16: strict self-map image

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
theorem full_image_16_inside :
    intervalStrictInside (fullImageCachedQ (16 : Fin 22))
      (unitBox (n := 22) (16 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 17: Jacobian bound

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
theorem full_row_17_lt :
    intervalMatrixRowBound fullPJ (17 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 17

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_17_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (17 : Fin 22))
      (fullPointCache (17 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_17_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (17 : Fin 22) ∈
      fullPointCache (17 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (17 : Fin 22))
    full_point_17_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 17: strict self-map image

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
theorem full_image_17_inside :
    intervalStrictInside (fullImageCachedQ (17 : Fin 22))
      (unitBox (n := 22) (17 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 18: Jacobian bound

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
theorem full_row_18_lt :
    intervalMatrixRowBound fullPJ (18 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 18

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_18_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (18 : Fin 22))
      (fullPointCache (18 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_18_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (18 : Fin 22) ∈
      fullPointCache (18 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (18 : Fin 22))
    full_point_18_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 18: strict self-map image

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
theorem full_image_18_inside :
    intervalStrictInside (fullImageCachedQ (18 : Fin 22))
      (unitBox (n := 22) (18 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 19: Jacobian bound

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
theorem full_row_19_lt :
    intervalMatrixRowBound fullPJ (19 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 19

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_19_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (19 : Fin 22))
      (fullPointCache (19 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_19_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (19 : Fin 22) ∈
      fullPointCache (19 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (19 : Fin 22))
    full_point_19_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 19: strict self-map image

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
theorem full_image_19_inside :
    intervalStrictInside (fullImageCachedQ (19 : Fin 22))
      (unitBox (n := 22) (19 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 20: Jacobian bound

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
theorem full_row_20_lt :
    intervalMatrixRowBound fullPJ (20 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 20

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_20_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (20 : Fin 22))
      (fullPointCache (20 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_20_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (20 : Fin 22) ∈
      fullPointCache (20 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (20 : Fin 22))
    full_point_20_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 20: strict self-map image

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
theorem full_image_20_inside :
    intervalStrictInside (fullImageCachedQ (20 : Fin 22))
      (unitBox (n := 22) (20 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 21: Jacobian bound

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
theorem full_row_21_lt :
    intervalMatrixRowBound fullPJ (21 : Fin 22) < qTarget := by
  unfold fullPJ
  rw [jacobianCache_eq]
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end
