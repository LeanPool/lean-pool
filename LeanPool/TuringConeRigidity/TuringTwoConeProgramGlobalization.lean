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

public import LeanPool.TuringConeRigidity.TuringTwoConeRepresentation
public import LeanPool.TuringConeRigidity.TuringTwoConeLocality
public import LeanPool.TuringConeRigidity.TuringConeProgramGlobalization

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

def RepresentsInverseAt {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (p : OracleCode) (P X : Oracle) : Prop :=
  Total p P X ∧ degree (value p P X) = pullback e (degree X)

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
  classical
  by_contra hnone
  push Not at hnone
  let d := forwardAnchor e
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

theorem generic_lift_of_arithmetic_program {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
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

theorem generic_lift_of_countable_tests {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (h : CountableTests e) : InverseGenericProgramLift e := by
  obtain ⟨R, p, _, hp⟩ := program_of_countable_tests e h
  exact generic_lift_of_arithmetic_program e R p hp

end
end OAI.TuringRigidity.TwoConeProgramGlobalization
