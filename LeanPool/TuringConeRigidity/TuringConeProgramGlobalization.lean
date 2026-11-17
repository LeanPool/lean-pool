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

public import LeanPool.TuringConeRigidity.TuringConeOracleProgram
public import LeanPool.TuringConeRigidity.Representation.GroundArithmeticGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenRequirements

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
  classical
  by_contra hnone
  push Not at hnone
  let d := (e (degree (jump FixedArithmetic.zero))).val
  let C := {R : Oracle // degree R = d} × OracleCode
  let : Countable {R : Oracle // degree R = d} := (countable_degree_fiber d).to_subtype
  obtain ⟨R₀, hR₀⟩ := degree_surjective d
  let : Nonempty C := ⟨(⟨R₀, hR₀⟩, OracleCode.zero)⟩
  have hw : ∀ c : C, ∃ X : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => iterate c.1.val 5) X ∧
      ¬ RepresentsInverseAt e c.2 (iterate c.1.val 5) X := by
    intro c
    exact hnone c.1.val c.2 c.1.property
  choose W hWg hWbad using hw
  obtain ⟨enumerate, he⟩ := exists_surjective_nat C
  obtain ⟨R, p, hR, hp⟩ := h (fun n => W (enumerate n))
  let c : C := (⟨R, hR⟩, p)
  obtain ⟨n, hn⟩ := he c
  have hgood : ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) (W (enumerate n)) := by
    simpa only [hn] using hWg c
  have hrep := hp n hgood
  rw [hn] at hrep
  exact hWbad c hrep

/-- Convert arithmetic genericity to the existing dense-open program-lift
interface, using a countable parameter-covering model. -/
theorem generic_lift_of_arithmetic_program {a : Degree} (e : Degree ≃o Set.Ici a)
    (R : Oracle) (p : OracleCode)
    (hrep : ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
      RepresentsInverseAt e p (iterate R 5) X) : InverseGenericProgramLift e := by
  obtain ⟨M, hM, hT, hcount, hRM⟩ :=
    ElementaryModel.parameter_covering_models.{0} (fun _ => R)
  let := hcount
  have hP := sourceT_real_iterate M hM hT (hRM 0) 5
  obtain ⟨D, hD, hground⟩ := InternalCohen.ground_family M ⟨realCode.{0} R, hRM 0⟩
  refine ⟨D, hD, iterate R 5, p, ?_⟩
  intro X hX
  have ha := GroundArithmeticGeneric.ground_arithmetic M hM hT (fun _ => iterate R 5)
    (fun _ => hP) X ((hground X).mp hX)
  obtain ⟨ht, hv⟩ := hrep X ha
  exact ⟨value p (iterate R 5) X, (total_iff p (iterate R 5) X).mp ht, hv⟩

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
