/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticSourceEquation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticProgramGraph
public import LeanPool.TuringConeRigidity.Computability.ArithmeticShuffleGraph
public import LeanPool.TuringConeRigidity.Computability.ArithmeticPrincipalIntersection

/-!
# Arithmetic Source Equation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticSourceEquation
open UniformArithmetic ArithmeticProgramGraph ArithmeticShuffleGraph GenericIdentity

theorem equation_arith (p : OracleCode) {P Y L R : OracleFamily}
    (hP : ArithmeticOracle P) (hY : ArithmeticOracle Y)
    (hL : ArithmeticOracle L) (hR : ArithmeticOracle R) :
    Arith (fun O v => SourceEquation p (P O v) (Y O v, L O v, R O v)) := by
  have hYL := code_arith hY hL
  have hYR := code_arith hY hR
  have hi := ArithmeticPrincipalIntersection.principal_arith (value_arith p hP hY)
    (join_arith (value_arith p hP hYL) (value_arith p hP hL))
    (join_arith (value_arith p hP hYR) (value_arith p hP hR))
  exact (total_arith p hP hY).and ((total_arith p hP hL).and
    ((total_arith p hP hR).and ((total_arith p hP hYL).and
      ((total_arith p hP hYR).and hi))))

theorem sourceEquation_arith (p : OracleCode) :
    Arith (fun O _ => SourceEquation p (O 0) (O 1, O 2, O 3)) :=
  equation_arith p (parameter_arith 0) (parameter_arith 1)
    (parameter_arith 2) (parameter_arith 3)

end TuringRigidity.ArithmeticSourceEquation

end OAI
