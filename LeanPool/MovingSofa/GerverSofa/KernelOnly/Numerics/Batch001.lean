/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Foundation.Batch003

/-!
# Gerver sofa dependency batch

* `KernelOnly.LeanCertNumericsRows.Full00`.
* `KernelOnly.LeanCertNumericsRows.FullPoint00`.
* `KernelOnly.LeanCertNumericsRows.FullImage00`.
* `KernelOnly.LeanCertNumericsRows.Full01`.
* `KernelOnly.LeanCertNumericsRows.FullPoint01`.
* `KernelOnly.LeanCertNumericsRows.FullImage01`.
* `KernelOnly.LeanCertNumericsRows.Full02`.
* `KernelOnly.LeanCertNumericsRows.FullPoint02`.
* `KernelOnly.LeanCertNumericsRows.FullImage02`.
* `KernelOnly.LeanCertNumericsRows.Full03`.
* `KernelOnly.LeanCertNumericsRows.FullPoint03`.
* `KernelOnly.LeanCertNumericsRows.FullImage03`.
* `KernelOnly.LeanCertNumericsRows.Full04`.
* `KernelOnly.LeanCertNumericsRows.FullPoint04`.
* `KernelOnly.LeanCertNumericsRows.FullImage04`.
* `KernelOnly.LeanCertNumericsRows.Full05`.
-/

@[expose] public section

noncomputable section


section

/-!
# Direct 22D certificate, row 0: Jacobian bound

The row modules form a deliberate dependency chain beginning after the
already-certified reduced 4D module.  Lake therefore checks
only one expensive closed kernel proposition at a time instead of launching
all 22 rows concurrently and exhausting RAM.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_row_0_lt :
    intervalMatrixRowBound fullPJ (0 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 0

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_0_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (0 : Fin 22))
      (fullPointCache (0 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_0_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (0 : Fin 22) ∈
      fullPointCache (0 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (0 : Fin 22))
    full_point_0_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 0: strict self-map image

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
theorem full_image_0_inside :
    intervalStrictInside (fullImageCachedQ (0 : Fin 22))
      (unitBox (n := 22) (0 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 1: Jacobian bound

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
theorem full_row_1_lt :
    intervalMatrixRowBound fullPJ (1 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 1

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_1_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (1 : Fin 22))
      (fullPointCache (1 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_1_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (1 : Fin 22) ∈
      fullPointCache (1 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (1 : Fin 22))
    full_point_1_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 1: strict self-map image

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
theorem full_image_1_inside :
    intervalStrictInside (fullImageCachedQ (1 : Fin 22))
      (unitBox (n := 22) (1 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 2: Jacobian bound

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
theorem full_row_2_lt :
    intervalMatrixRowBound fullPJ (2 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 2

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_2_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (2 : Fin 22))
      (fullPointCache (2 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_2_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (2 : Fin 22) ∈
      fullPointCache (2 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (2 : Fin 22))
    full_point_2_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 2: strict self-map image

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
theorem full_image_2_inside :
    intervalStrictInside (fullImageCachedQ (2 : Fin 22))
      (unitBox (n := 22) (2 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 3: Jacobian bound

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
theorem full_row_3_lt :
    intervalMatrixRowBound fullPJ (3 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 3

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_3_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (3 : Fin 22))
      (fullPointCache (3 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_3_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (3 : Fin 22) ∈
      fullPointCache (3 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (3 : Fin 22))
    full_point_3_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 3: strict self-map image

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
theorem full_image_3_inside :
    intervalStrictInside (fullImageCachedQ (3 : Fin 22))
      (unitBox (n := 22) (3 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 4: Jacobian bound

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
theorem full_row_4_lt :
    intervalMatrixRowBound fullPJ (4 : Fin 22) < qTarget := by
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
# Direct 22D certificate, point residual 4

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
theorem full_point_4_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (4 : Fin 22))
      (fullPointCache (4 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_4_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (4 : Fin 22) ∈
      fullPointCache (4 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (4 : Fin 22))
    full_point_4_contained

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 4: strict self-map image

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
theorem full_image_4_inside :
    intervalStrictInside (fullImageCachedQ (4 : Fin 22))
      (unitBox (n := 22) (4 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Direct 22D certificate, row 5: Jacobian bound

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
theorem full_row_5_lt :
    intervalMatrixRowBound fullPJ (5 : Fin 22) < qTarget := by
  unfold fullPJ
  rw [jacobianCache_eq]
  decide +kernel

end PartALeanCert
end GerverSofa

end

end

end
