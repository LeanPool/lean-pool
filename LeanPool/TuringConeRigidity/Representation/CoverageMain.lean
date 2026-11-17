/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CoverageMain.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CategoryMain
public import LeanPool.TuringConeRigidity.Computability.DegreeCoverage

/-!
# Coverage Main
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

theorem main_of_representation (hrep : BorelRepresentation) : MainTheorem :=
  main_of_two_obligations hrep irrational_degree_coverage

end TuringRigidity

end OAI
