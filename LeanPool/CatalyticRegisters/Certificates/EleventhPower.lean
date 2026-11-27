/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.PoweringPrograms

/-! # Symbolic certificate for the eleventh power -/

namespace Catalytic

@[expose] public section

theorem prog7_x11_cert :
    exec3Poly prog7Power11 =
      ([((11, 0, 0), 68724637549388656012800)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := rfl

end

end Catalytic
