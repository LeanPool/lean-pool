/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters
public import LeanPool.TuringConeRigidity.CohenForcing.CohenRealNameCode

/-!
# Internal Cohen Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
  RecursiveNames
attribute [local instance] InternalCollapse.order

/-- The canonical name for the generic real in the set-coded word poset. -/
noncomputable def realName : Name (Conditions conditions) :=
  CohenRealNameCode.realName conditions

/-- Bounded formula describing the set-coded canonical generic-real name. -/
def realNameFormula : BoundedSetTheory.Formula := CohenRealNameCode.realNameFormula

theorem eval_realNameFormula (z c f r one : ZFSet.{0}) (e : ℕ → ZFSet.{0}) :
    realNameFormula.Eval (cons z (cons c (cons ZFSet.omega (cons f (cons r (cons one e)))))) ↔
      ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v ∈ r,
        ZFSet.pair n v ∈ f ∧ ZFSet.pair n one ∈ q ∧ z = ZFSet.pair v q := by
  exact CohenRealNameCode.eval_realNameFormula z c f r one e

/-- Set-coded generic-real name using the supplied graph of numeral-name codes. -/
noncomputable def realNameCode (f : ZFSet.{0}) : ZFSet.{0} :=
  CohenRealNameCode.realNameCode conditions f

theorem mem_realNameCode (f z : ZFSet.{0}) : z ∈ realNameCode f ↔
    ∃ q ∈ conditions, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  exact CohenRealNameCode.mem_realNameCode conditions f z

theorem realNameCode_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode f ∈ M := by
  exact CohenRealNameCode.realNameCode_mem M conditions hM hT (conditions_mem M hM hT) hf

theorem encode_realName (d r f : ZFSet.{0}) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label conditions ⊤)) :
    realName.encode (label conditions) = realNameCode f := by
  exact CohenRealNameCode.encode_realName conditions d r f hω hf

theorem realName_internal (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    realName.encode (label conditions) ∈ M := by
  exact CohenRealNameCode.realName_internal M conditions hM hT (conditions_mem M hM hT)

end TuringRigidity.InternalCohen

end OAI
