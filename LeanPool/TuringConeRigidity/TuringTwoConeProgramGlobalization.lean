/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeProgramGlobalization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Representation.ArithmeticProgramGlobalization
public import LeanPool.TuringConeRigidity.TuringTwoConeRepresentation
public import LeanPool.TuringConeRigidity.TuringTwoConeLocality

/-!
# Globalizing two-cone programs from countable tests

Candidate parameters represent only the fixed degree e(a'), so there are
countably many parameter/program pairs. The diagonal argument is independent
of bijectivity of the joined inverse. The countable-test premise remains
explicit in this module and will be discharged by the model argument.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeProgramGlobalization

open OracleJump GenericIdentity TransitiveNameModel BoundedSetTheory CountableForcing
open TwoConeRigidity
open TwoConeLocality (forwardAnchor)

noncomputable section

/-- The program is total at `X` and computes a representative of the cone isomorphism's
pullback degree. -/
def RepresentsInverseAt {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (p : OracleCode) (P X : Oracle) : Prop :=
  Total p P X ∧ degree (value p P X) = pullback e (degree X)

/-- For each countable test sequence, one anchored oracle and program represent the join-based
pullback on its arithmetic-generic members. -/
def CountableTests {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) : Prop :=
  ∀ W : ℕ → Oracle, ∃ (R : Oracle) (p : OracleCode),
    degree R = forwardAnchor e ∧
    ∀ n, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) (W n) →
      RepresentsInverseAt e p (iterate R 5) (W n)

theorem program_of_countable_tests {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (h : CountableTests e) :
    ∃ (R : Oracle) (p : OracleCode), degree R = forwardAnchor e ∧
      ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
        RepresentsInverseAt e p (iterate R 5) X := by
  exact ArithmeticProgramGlobalization.program_of_countable_tests
    (forwardAnchor e) (RepresentsInverseAt e) h

theorem generic_lift_of_arithmetic_program {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (R : Oracle) (p : OracleCode)
    (hrep : ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
      RepresentsInverseAt e p (iterate R 5) X) : InverseGenericProgramLift e := by
  exact ArithmeticProgramGlobalization.generic_lift_of_arithmetic_program
    (pullback e) R p hrep

theorem generic_lift_of_countable_tests {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (h : CountableTests e) : InverseGenericProgramLift e := by
  obtain ⟨R, p, _, hp⟩ := program_of_countable_tests e h
  exact generic_lift_of_arithmetic_program e R p hp

end
end OAI.TuringRigidity.TwoConeProgramGlobalization
