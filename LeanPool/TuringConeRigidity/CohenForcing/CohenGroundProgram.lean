/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenGroundProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundJump
public import LeanPool.TuringConeRigidity.Effective.UniformCohenIteration
public import LeanPool.TuringConeRigidity.Effective.UniformTableSimulation

/-!
# Cohen Ground Program
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CountableForcing OracleJump
open TableIndices IndexMatrix UniformPrograms
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem groundGeneric_iterate_program (M : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (R : Oracle) (hR : realCode R ∈ M) (k : ℕ) :
    ∃ p : OracleCode, ∀ A : Oracle,
      AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A)) →
      OracleCode.eval (oracleFunction (join A (iterate R k))) p =
        oracleFunction (iterate (join A R) k) := by
  obtain ⟨p,hp⟩ := UniformCohenJump.iterate_generic_join_program R k
  exact ⟨p,fun A hA => hp A (fun j _ => groundGeneric_iterate_oneGeneric M hM hT A R hR hA j)⟩

theorem groundGeneric_table_simulation (M : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (R : Oracle) (hR : realCode R ∈ M) (k d : ℕ) :
    ∃ e : ℕ, ∀ A : Oracle,
      AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A)) →
      ∀ X : Oracle, Represents (iterate (join A R) k) (machine d) X →
        Represents (join A (iterate R k)) (machine e) X := by
  let S := {A : Oracle //
    AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A))}
  obtain ⟨p,hp⟩ := groundGeneric_iterate_program M hM hT R hR k
  have h : Runs (fun A : S => oracleFunction (join A.val (iterate R k)))
      (fun A => oracleFunction (iterate (join A.val R) k)) := ⟨p,fun A => hp A.val A.property⟩
  obtain ⟨e,he⟩ := h.table_simulation d
  exact ⟨e,fun A hA => he ⟨A,hA⟩⟩

theorem selected_column_table_simulation (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (R : Oracle) (hR : realCode R ∈ M) (k d : ℕ) :
    ∃ e : ℕ, ∀ G : GenericFilter (Conditions (CohenColumnRealName.poset K)),
      AtomicForcing.GroundGeneric M G → ∀ A : Oracle,
      (CohenColumnRealName.realName K a).val G.carrier = realCode A →
      ∀ X : Oracle, Represents (iterate (join A R) k) (machine d) X →
        Represents (join A (iterate R k)) (machine e) X := by
  obtain ⟨e,he⟩ := groundGeneric_table_simulation M hM hT R hR k d
  exact ⟨e,fun G hG A hv => he A
    (CohenColumnRealName.selected_real_prefix_generic M K a hM hT hK ha G hG A hv)⟩

end TuringRigidity.InternalCohen

end OAI
