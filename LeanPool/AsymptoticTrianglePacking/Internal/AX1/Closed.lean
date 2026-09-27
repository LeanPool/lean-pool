/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxPlacementNibble
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoarseCellCoupled

/-! # Unconditional AX1 -/

@[expose] public section

namespace Nibble.AX1

/-- The coupled block-cover residual follows from the closed box-allocation theorem. -/
theorem blockCoverResidualCoupled_holds : BlockCoverResidualCoupled :=
  blockCoverResidualCoupled_of_boxAllocation boxAllocationResidual_holds

/-- The cover-side AX1 statement holds for every graph. -/
theorem ax1Statement_holds : AX1Statement :=
  ax1_of_boxAllocation boxAllocationResidual_holds

/-- The fractional–integral triangle-packing gap is uniformly `o(n²)`. -/
theorem nibbleGapHyp_holds : NibbleGapHyp :=
  nibbleGapHyp_of_ax1 ax1Statement_holds

end Nibble.AX1
