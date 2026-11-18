/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Extracted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/
TuringConeProgramGlobalization.lean and TuringTwoConeProgramGlobalization.lean.
The shared arguments are generalized over the anchor and represented relation.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GroundArithmeticGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenRequirements
public import LeanPool.TuringConeRigidity.Representation.ParameterCoveringModels
public import LeanPool.TuringConeRigidity.SetModels.ModelRealOperations

/-!
# Arithmetic-program globalization

Countable anchored tests globalize by diagonalization. A program valid on all
arithmetic-generic inputs then yields a dense-open generic program lift. These
arguments apply independently of the degree map represented by the program.
-/

@[expose] public section

namespace OAI.TuringRigidity.ArithmeticProgramGlobalization

open OracleJump GenericIdentity TransitiveNameModel BoundedSetTheory

noncomputable section

/-- A countable family of anchored parameter/program candidates that handles every countable
sequence has one candidate valid on every arithmetic-generic input. -/
theorem program_of_countable_tests (d : Degree)
    (represents : OracleCode → Oracle → Oracle → Prop)
    (h : ∀ W : ℕ → Oracle, ∃ (R : Oracle) (p : OracleCode), degree R = d ∧
      ∀ n, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) (W n) →
        represents p (iterate R 5) (W n)) :
    ∃ (R : Oracle) (p : OracleCode), degree R = d ∧
      ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
        represents p (iterate R 5) X := by
  classical
  by_contra hnone
  push Not at hnone
  let C := {R : Oracle // degree R = d} × OracleCode
  let : Countable {R : Oracle // degree R = d} := (countable_degree_fiber d).to_subtype
  obtain ⟨R₀, hR₀⟩ := degree_surjective d
  let : Nonempty C := ⟨(⟨R₀, hR₀⟩, OracleCode.zero)⟩
  have hw : ∀ c : C, ∃ X : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => iterate c.1.val 5) X ∧
      ¬ represents c.2 (iterate c.1.val 5) X := by
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

/-- A fixed program representing a degree map on all arithmetic-generic inputs represents it
on a countable dense-open generic domain, using a parameter-covering model. -/
theorem generic_lift_of_arithmetic_program (f : Degree → Degree)
    (R : Oracle) (p : OracleCode)
    (hrep : ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
      Total p (iterate R 5) X ∧ degree (value p (iterate R 5) X) = f (degree X)) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
      ∃ P : Oracle, ∃ p : OracleCode, ∀ X, ShuffleRequirements.GenericFor D X →
        ∃ Y, OracleCode.eval (oracleFunction (join X P)) p = oracleFunction Y ∧
          degree Y = f (degree X) := by
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

end
end OAI.TuringRigidity.ArithmeticProgramGlobalization
