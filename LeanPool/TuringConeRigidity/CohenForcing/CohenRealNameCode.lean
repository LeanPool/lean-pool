/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Extracted and generalized for Lean Pool from the Apache-2.0 proofs in
bjoernkjoshanssen/tt-auto/OAI/Computability/DegreeRigidity/CohenForcing/
InternalCohenName.lean, SparseCohenRealName.lean and CohenColumnRealName.lean.
The checked numeral-name encoding is independent of the chosen condition set.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenConditions

/-!
# Poset-parametric Cohen real-name codes
-/

@[expose] public section

namespace OAI.TuringRigidity.CohenRealNameCode
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order

/-- The checked-numeral name selected by an arbitrary relation on indices and conditions. -/
noncomputable def realNameFromPredicate (c : ZFSet.{0}) [Top (Conditions c)]
    (R : ZFSet.{0} → ZFSet.{0} → Prop) : Name (Conditions c) :=
  .mk {t : Conditions c × ℕ // R (natSet t.2) (label c t.1)}
    (fun t => Name.check (natSet t.val.2)) (fun t => t.val.1)

/-- The canonical generic-real name over an arbitrary set-coded condition set. -/
noncomputable def realName (c : ZFSet.{0}) [Top (Conditions c)] : Name (Conditions c) :=
  realNameFromPredicate c (fun n q => ZFSet.pair n (bitSet true) ∈ q)

/-- Bounded formula for the graph-coded generic-real name over a condition set. -/
def realNameFormula : BoundedSetTheory.Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 6
    (.conj (.pairMem 1 0 6) (.conj (.pairMem 1 8 2) (.orderedPair 3 0 2)))))

/-- Evaluate the bounded predicate for a selected numeral-name pair. -/
theorem eval_realNameFormula (z c f r one : ZFSet.{0}) (e : ℕ → ZFSet.{0}) :
    realNameFormula.Eval (cons z (cons c (cons ZFSet.omega (cons f (cons r (cons one e)))))) ↔
      ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v ∈ r,
        ZFSet.pair n v ∈ f ∧ ZFSet.pair n one ∈ q ∧ z = ZFSet.pair v q := by
  simp only
    [realNameFormula, BoundedSetTheory.Formula.Eval, BoundedSetTheory.Formula.eval_pairMem,
      BoundedSetTheory.Formula.eval_orderedPair, cons_zero, cons_succ]

/-- Graph-coded generic-real name over an arbitrary condition set. -/
noncomputable def realNameCode (c f : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v ∈ iterUnion 2 f,
    ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q)
    (ZFSet.prod (iterUnion 2 f) c)

/-- Membership does not require a separate bound on a graph value. -/
theorem mem_realNameCode (c f z : ZFSet.{0}) : z ∈ realNameCode c f ↔
    ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  rw [realNameCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,n,hn,v,_,hv,hbit,hz⟩; exact ⟨q,hq,n,hn,v,hv,hbit,hz⟩
  · rintro ⟨q,hq,n,hn,v,hv,hbit,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,q,hq,rfl⟩,q,hq,n,hn,v,hr,hv,hbit,rfl⟩

/-- Bounded separation internalizes the code from its condition set and numeral graph. -/
theorem realNameCode_mem (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode c f ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  have hr := iterUnion_mem M hM hT.union hf 2
  have h1 : bitSet true ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  let e := cons c (cons ZFSet.omega (cons f (cons (iterUnion 2 f) (cons (bitSet true)
    (fun _ => c)))))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded realNameFormula e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hr hc)
  have heq : ZFSet.sep (fun z => realNameFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) c) = realNameCode c f := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,realNameCode]
    exact and_congr_right (fun _ => eval_realNameFormula _ _ _ _ _ _)
  exact heq ▸ hs

/-- A checked numeral graph describes the encoding of any selected real name. -/
theorem mem_encode_realNameFromPredicate (c : ZFSet.{0}) [Top (Conditions c)]
    (R : ZFSet.{0} → ZFSet.{0} → Prop) (d r f : ZFSet.{0}) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label c ⊤)) :
    ∀ z, z ∈ (realNameFromPredicate c R).encode (label c) ↔
      ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v,
        ZFSet.pair n v ∈ f ∧ R n q ∧ z = ZFSet.pair v q := by
  have hfr : TransitiveNameModel.FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
  intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hz⟩
    have hn := (mem_omega (natSet n)).mpr ⟨n,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 _ (hω hn)
    have he := hf.correct _ (hω hn) v hv hfv
    refine ⟨label c q,label_mem _ _,natSet n,hn,v,hfv,hbit,?_⟩
    simpa only [realNameFromPredicate,encode_check,he] using hz.symm
  · rintro ⟨q,hq,n,hn,v,hfv,hbit,hz⟩
    obtain ⟨k,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨q,rfl⟩ := label_surjective c hq
    have he := hf.correct _ (hω hn) v (hfr.value_mem hfv) hfv
    exact ⟨⟨(q,k),hbit⟩,by simpa only [realNameFromPredicate,encode_check,he] using hz.symm⟩

/-- The poset-parametric real name has exactly the graph-coded encoding. -/
theorem encode_realName (c : ZFSet.{0}) [Top (Conditions c)] (d r f : ZFSet.{0})
    (hω : ZFSet.omega ⊆ d) (hf : CheckGraph d r f (label c ⊤)) :
    (realName c).encode (label c) = realNameCode c f := by
  apply ZFSet.ext
  intro z
  exact (mem_encode_realNameFromPredicate c (fun n q => ZFSet.pair n (bitSet true) ∈ q)
    d r f hω hf z).trans (mem_realNameCode c f z).symm

/-- A condition set internal to the source model gives an internal canonical real name. -/
theorem realName_internal (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) :
    (realName c).encode (label c) ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label c ⊤) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM hqM (hM _ (hc) _ (label_mem c ⊤)) hd hq ZFSet.omega hωd
  have hsub : ZFSet.omega ⊆ hull d q ZFSet.omega := fun x hx =>
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) x hx
  rw [encode_realName c _ _ f hsub hfg]
  exact realNameCode_mem M c hM hT hc hf

end OAI.TuringRigidity.CohenRealNameCode
