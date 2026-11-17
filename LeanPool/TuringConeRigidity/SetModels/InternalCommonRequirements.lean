/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCommonRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticCommonRequirement
public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalCohenProductSets
public import LeanPool.TuringConeRigidity.CohenForcing.CohenProductSplitting

/-!
# Internal Common Requirements
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCommonRequirements
open TransitiveNameModel BoundedSetTheory InternalCohen Encodable UniformArithmetic
open EncodedForcing (word)
open TaggedProductConditions (code)
open CountableForcing CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def requirementCodes (A : Oracle) (p q : OracleCode) : Oracle :=
  arithmeticReal (fun O n => CommonIdeal.Requirement (O 0) p q
    (word (left n)) (word (right n))) (fun _ => A)

theorem requirementCodes_true (A : Oracle) (p q : OracleCode) (n : ℕ) :
    requirementCodes A p q n = true ↔
      CommonIdeal.Requirement A p q (word (left n)) (word (right n)) :=
  arithmeticReal_true _ _ _

theorem requirementCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ modelReals M) (p q : OracleCode) :
    realCode (requirementCodes A p q) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT
    (ArithmeticCommonRequirement.requirement_arith p q left_primrec right_primrec)
    (fun _ => A) (fun _ => hA)

noncomputable def denseSet (c : ZFSet.{0}) (A : Oracle) (p q : OracleCode) : ZFSet.{0} :=
  c.sep (fun z => ∃ s t : List Bool,
    z = code (wordCode s) (wordCode t) ∧ CommonIdeal.Requirement A p q s t)

theorem denseSet_eq_image (c : ZFSet.{0}) (A : Oracle) (p q : OracleCode) :
    denseSet c A p q = NumericalCohenProductSets.image c (requirementCodes A p q) := by
  apply ZFSet.ext
  intro z
  simp only [denseSet,NumericalCohenProductSets.image,ZFSet.mem_sep,requirementCodes_true]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨s,t,hz,h⟩
    refine ⟨Nat.pair (encode s) (encode t),?_,?_⟩
    · simpa [left,right,word] using h
    · simpa [left,right,word] using hz
  · rintro ⟨n,h,hz⟩
    exact ⟨word (left n),word (right n),hz,h⟩

theorem denseSet_mem (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (A : Oracle) (hA : A ∈ modelReals M) (p q : OracleCode) :
    denseSet c A p q ∈ M := by
  rw [denseSet_eq_image]
  exact NumericalCohenProductSets.image_mem M c hM hT hc _
    (requirementCodes_mem M hM hT A hA p q)

theorem denseSet_spec (c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions, ∃ s ∈ conditions, z = code p s)
    (A : Oracle) (p q : OracleCode) (s t : List Bool) :
    code (wordCode s) (wordCode t) ∈ denseSet c A p q ↔ CommonIdeal.Requirement A p q s t := by
  rw [denseSet_eq_image]
  exact NumericalCohenProductSets.image_spec c hcs _ _ (requirementCodes_true A p q) s t

theorem denseSet_dense (c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions, ∃ s ∈ conditions, z = code p s)
    (A : Oracle) (p q : OracleCode) :
    Dense {x : Conditions c | label c x ∈ denseSet c A p q} := by
  intro x
  let I := productIso conditions conditions c hcs
  let y := I.symm x
  let s := conditionEquiv.symm y.1
  let t := conditionEquiv.symm y.2
  obtain ⟨u,v,hu,hv,hreq⟩ := CommonIdeal.requirement_dense A p q s.word t.word
  let u' := conditionEquiv ⟨u⟩
  let v' := conditionEquiv ⟨v⟩
  have hu' : u' ≤ y.1 := by
    simpa only [s,OrderIso.apply_symm_apply] using conditionEquiv.monotone hu
  have hv' : v' ≤ y.2 := by
    simpa only [t,OrderIso.apply_symm_apply] using conditionEquiv.monotone hv
  refine ⟨I (u',v'),?_,?_⟩
  · simpa only [y,OrderIso.apply_symm_apply] using I.monotone (show (u',v') ≤ y from ⟨hu',hv'⟩)
  · change label c (productMap conditions conditions c hcs (u',v')) ∈ denseSet c A p q
    rw [label_productMap]
    change code (label conditions (encodeCondition ⟨u⟩))
      (label conditions (encodeCondition ⟨v⟩)) ∈ denseSet c A p q
    rw [label_encodeCondition,label_encodeCondition,denseSet_spec c hcs]
    exact hreq

end TuringRigidity.InternalCommonRequirements

end OAI
