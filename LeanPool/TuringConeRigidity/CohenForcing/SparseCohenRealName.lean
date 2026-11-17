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

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenName
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
open InternalCohen (bitSet realNameFormula eval_realNameFormula)

/-- The set-coded Cohen poset of finite Boolean partial functions on the natural numbers. -/
noncomputable abbrev poset : ZFSet.{0} := CohenGroundPoset.conditions ZFSet.omega

/-- The canonical real name for the sparse natural-number Cohen poset. -/
noncomputable def realName : Name (Conditions poset) :=
  .mk {t : Conditions poset × ℕ //
    ZFSet.pair (natSet t.2) (bitSet true) ∈ label poset t.1}
    (fun t => Name.check (natSet t.val.2)) (fun t => t.val.1)

/-- Set-coded sparse generic-real name using the supplied numeral-name graph. -/
noncomputable def realNameCode (f : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ q ∈ poset, ∃ n ∈ ZFSet.omega, ∃ v ∈ iterUnion 2 f,
    ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q)
    (ZFSet.prod (iterUnion 2 f) poset)

theorem mem_realNameCode (f z : ZFSet.{0}) : z ∈ realNameCode f ↔
    ∃ q ∈ poset, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  rw [realNameCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,n,hn,v,_,hv,hbit,hz⟩; exact ⟨q,hq,n,hn,v,hv,hbit,hz⟩
  · rintro ⟨q,hq,n,hn,v,hv,hbit,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,q,hq,rfl⟩,q,hq,n,hn,v,hr,hv,hbit,rfl⟩

theorem realNameCode_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode f ∈ M := by
  have hc := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  have hω := sourceT_omega_mem M hM hT
  have hr := iterUnion_mem M hM hT.union hf 2
  have h1 : bitSet true ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  let e := cons poset (cons ZFSet.omega (cons f (cons (iterUnion 2 f) (cons (bitSet true) (fun _
    => poset)))))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded realNameFormula e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hr hc)
  have heq : ZFSet.sep (fun z => realNameFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) poset) = realNameCode f := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,realNameCode]
    exact and_congr_right (fun _ => eval_realNameFormula _ _ _ _ _ _)
  exact heq ▸ hs

theorem encode_realName (d r f : ZFSet.{0}) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label poset ⊤)) :
    realName.encode (label poset) = realNameCode f := by
  have hfr : TransitiveNameModel.FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_realNameCode]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hz⟩
    have hn := (mem_omega (natSet n)).mpr ⟨n,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 _ (hω hn)
    have he := hf.correct _ (hω hn) v hv hfv
    refine ⟨label poset q,label_mem _ _,natSet n,hn,v,hfv,hbit,?_⟩
    simpa only [realName,encode_check,he] using hz.symm
  · rintro ⟨q,hq,n,hn,v,hfv,hbit,hz⟩
    obtain ⟨k,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨q,rfl⟩ := label_surjective poset hq
    have he := hf.correct _ (hω hn) v (hfr.value_mem hfv) hfv
    exact ⟨⟨(q,k),hbit⟩,by simpa only [realName,encode_check,he] using hz.symm⟩

theorem realName_internal (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    realName.encode (label poset) ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label poset ⊤) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM hqM (hM _ (CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM
      hT)) _ (label_mem poset ⊤)) hd hq ZFSet.omega hωd
  have hsub : ZFSet.omega ⊆ hull d q ZFSet.omega := fun x hx =>
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) x hx
  rw [encode_realName _ _ f hsub hfg]
  exact realNameCode_mem M hM hT hf

end TuringRigidity.SparseCohenRealName

end OAI
