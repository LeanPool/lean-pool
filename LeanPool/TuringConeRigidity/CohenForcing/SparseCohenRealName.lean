/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/SparseCohenRealName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenRealNameCode
public import LeanPool.TuringConeRigidity.CohenForcing.CohenNiceNameConstruction

/-!
# Sparse Cohen Real Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
open InternalCohen (bitSet)

/-- The set-coded Cohen poset of finite Boolean partial functions on the natural numbers. -/
noncomputable abbrev poset : ZFSet.{0} := CohenGroundPoset.conditions ZFSet.omega

/-- The canonical real name for the sparse natural-number Cohen poset. -/
noncomputable def realName : Name (Conditions poset) :=
  CohenRealNameCode.realName poset

/-- Set-coded sparse generic-real name using the supplied numeral-name graph. -/
noncomputable def realNameCode (f : ZFSet.{0}) : ZFSet.{0} :=
  CohenRealNameCode.realNameCode poset f

theorem mem_realNameCode (f z : ZFSet.{0}) : z ∈ realNameCode f ↔
    ∃ q ∈ poset, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  exact CohenRealNameCode.mem_realNameCode poset f z

theorem realNameCode_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode f ∈ M := by
  exact CohenRealNameCode.realNameCode_mem M poset hM hT
    (CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)) hf

theorem encode_realName (d r f : ZFSet.{0}) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label poset ⊤)) :
    realName.encode (label poset) = realNameCode f := by
  exact CohenRealNameCode.encode_realName poset d r f hω hf

theorem realName_internal (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    realName.encode (label poset) ∈ M := by
  exact CohenRealNameCode.realName_internal M poset hM hT
    (CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT))

end TuringRigidity.SparseCohenRealName

end OAI
