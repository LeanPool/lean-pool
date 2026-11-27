/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.PoweringPrograms

/-! # Symbolic certificate for the fifteenth power -/

namespace Catalytic

@[expose] public section

theorem prog9_x15_cert :
    exec3Poly prog9Power15 =
      ([((15, 0, 0), 876702103804656272895371895753963647960420947968000)],
       [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := by
  -- Replay the concrete symbolic execution in the kernel.
  apply beq_iff_eq.mp
  decide +kernel

end

end Catalytic
