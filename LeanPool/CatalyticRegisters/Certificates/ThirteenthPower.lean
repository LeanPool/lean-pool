/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.PoweringPrograms

/-! # Symbolic certificate for the thirteenth power -/

namespace Catalytic

@[expose] public section

theorem prog8_x13_cert :
    exec3Poly prog8Power13 =
      ([((13, 0, 0), 2656207148788801777680)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := by
  -- Replay the concrete symbolic execution in the kernel.
  apply beq_iff_eq.mp
  decide +kernel

end

end Catalytic
