/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.PoweringPrograms

/-! # Symbolic certificate for the seventh power -/

namespace Catalytic

@[expose] public section

theorem prog5_x7_cert :
    exec3Poly prog5Power7 = ([((7, 0, 0), 576)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := rfl

end

end Catalytic
