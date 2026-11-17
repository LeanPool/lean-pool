/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeProgramGlobalization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Representation.ArithmeticProgramGlobalization
public import LeanPool.TuringConeRigidity.SetModels.FixedArithmetic
public import LeanPool.TuringConeRigidity.TuringConeRepresentation

/-!
# From countable tests to a global generic inverse program

The only parameter candidates considered here represent the one fixed degree
e(0'). Hence the pairs (parameter representative, program) form a countable
set. If each prescribed countable sequence can be handled by one candidate,
a diagonal argument gives a candidate valid on every arithmetic-generic input.
This does not prove the countable-test premise; it isolates a sufficient
remaining model/coherence obligation and connects it to cone rigidity.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeProgramGlobalization

open OracleJump GenericIdentity TransitiveNameModel BoundedSetTheory CountableForcing
open ConeRigidity

noncomputable section

/-- The program is total at `X` and its output degree equals the cone isomorphism's pullback
value. -/
def RepresentsInverseAt {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : OracleCode) (P X : Oracle) : Prop :=
  Total p P X ∧ degree (value p P X) = pullback e (degree X)

/-- One candidate must handle every arithmetic-generic member of the
prescribed countable sequence; different sequences may choose different
candidates. This is an explicit premise, not asserted for arbitrary e. -/
def CountableTests {a : Degree} (e : Degree ≃o Set.Ici a) : Prop :=
  ∀ W : ℕ → Oracle, ∃ (R : Oracle) (p : OracleCode),
    degree R = (e (degree (jump FixedArithmetic.zero))).val ∧
    ∀ n, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) (W n) →
      RepresentsInverseAt e p (iterate R 5) (W n)

/-- Diagonalize over the countably many candidates. The conclusion is
uniform on all inputs, not merely on a single model's reals. -/
theorem program_of_countable_tests {a : Degree} (e : Degree ≃o Set.Ici a)
    (h : CountableTests e) :
    ∃ (R : Oracle) (p : OracleCode),
      degree R = (e (degree (jump FixedArithmetic.zero))).val ∧
      ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
        RepresentsInverseAt e p (iterate R 5) X := by
  exact ArithmeticProgramGlobalization.program_of_countable_tests
    ((e (degree (jump FixedArithmetic.zero))).val) (RepresentsInverseAt e) h

/-- Convert arithmetic genericity to the existing dense-open program-lift
interface, using a countable parameter-covering model. -/
theorem generic_lift_of_arithmetic_program {a : Degree} (e : Degree ≃o Set.Ici a)
    (R : Oracle) (p : OracleCode)
    (hrep : ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
      RepresentsInverseAt e p (iterate R 5) X) : InverseGenericProgramLift e := by
  exact ArithmeticProgramGlobalization.generic_lift_of_arithmetic_program
    (pullback e) R p hrep

theorem generic_lift_of_countable_tests {a : Degree} (e : Degree ≃o Set.Ici a)
    (h : CountableTests e) : InverseGenericProgramLift e := by
  obtain ⟨R, p, _, hp⟩ := program_of_countable_tests e h
  exact generic_lift_of_arithmetic_program e R p hp

/-- Conditional final endpoint. The model argument must still establish
CountableTests e; no full cone-rigidity theorem is claimed here. -/
theorem eq_bot_of_countable_tests {a : Degree} (e : Degree ≃o Set.Ici a)
    (h : CountableTests e) : a = ⊥ :=
  eq_bot_of_inverse_generic_program_lift e (generic_lift_of_countable_tests e h)

end
end OAI.TuringRigidity.ConeProgramGlobalization
