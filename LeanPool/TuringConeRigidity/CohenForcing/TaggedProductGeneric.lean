/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/TaggedProductGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenProductSplitting
public import LeanPool.TuringConeRigidity.SetModels.RegularTreeExtension

/-!
# Tagged Product Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TaggedProductGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Combine two filters and transport their product to the tagged condition poset. -/
noncomputable def joint (a b c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b)) :
    GenericFilter (Conditions c) :=
  AutomorphismName.mapFilter (productIso a b c hcs) (SourceEquationTail.productFilter G H)

theorem joint_mem (a b c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b))
    (p : Conditions a) (s : Conditions b) :
    productMap a b c hcs (p,s) ∈ (joint a b c hcs G H).carrier ↔
      p ∈ G.carrier ∧ s ∈ H.carrier := by
  change (productIso a b c hcs).symm ((productIso a b c hcs) (p,s)) ∈
    (SourceEquationTail.productFilter G H).carrier ↔ _
  rw [OrderIso.symm_apply_apply]
  rfl

/-- First-factor conditions admitting a member of `D` whose second factor extends `r`. -/
noncomputable def sectionSet (a b D r : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (fun p => ∃ s ∈ b, ∃ z ∈ D, z = code p s ∧ r ⊆ s)

/-- Second-factor conditions whose tagged pair with some member of `g` belongs to `D`. -/
noncomputable def fiberSet (b D g : ZFSet.{0}) : ZFSet.{0} :=
  b.sep (fun s => ∃ p ∈ g, ∃ z ∈ D, z = code p s)

theorem sectionSet_mem (M a b D r : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) (hr : r ∈ M) : sectionSet a b D r ∈ M := by
  let e := cons b (cons D (cons r (cons (natSet 0) (fun _ => natSet 1))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hb
    · exact hD
    · exact hr
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hsectionCode (left right value : ZFSet.{0}) :
      (codeFormula 2 1 0 6 7).Eval (cons value (cons right (cons left e))) ↔
        value = code left right :=
    codeFormula_spec 2 1 0 6 7 _ rfl rfl
  simpa only [sectionSet,Formula.Eval,hsectionCode,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (codeFormula 2 1 0 6 7) (.subset 5 1)))) e he ha

theorem fiberSet_mem (N b D g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hb : b ∈ N) (hD : D ∈ N) (hg : g ∈ N) : fiberSet b D g ∈ N := by
  let e := cons g (cons D (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i
    · exact hg
    · exact hD
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hfiberCode (left right value : ZFSet.{0}) :
      (codeFormula 1 2 0 5 6).Eval (cons value (cons left (cons right e))) ↔
        value = code left right :=
    codeFormula_spec 1 2 0 5 6 _ rfl rfl
  simpa only [fiberSet,Formula.Eval,hfiberCode,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (codeFormula 1 2 0 5 6))) e he hb

theorem sectionSet_dense (a b c D : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hD : Dense {x : Conditions c | label c x ∈ D}) (r : Conditions b) :
    Dense {p : Conditions a | label a p ∈ sectionSet a b D (label b r)} := by
  intro p
  obtain ⟨x,hx,hxD⟩ := hD (productMap a b c hcs (p,r))
  let y := (productIso a b c hcs).symm x
  have hy : y ≤ (p,r) := by
    have hh := (productIso a b c hcs).symm.monotone hx
    change (productIso a b c hcs).symm x ≤ (productIso a b c hcs).symm ((productIso a b c hcs)
      (p,r)) at hh
    simpa only [OrderIso.symm_apply_apply] using hh
  have hl : label c x = code (label a y.1) (label b y.2) := by
    rw [←label_productMap a b c hcs y]
    exact congrArg (label c) ((productIso a b c hcs).apply_symm_apply x).symm
  exact ⟨y.1,hy.1,ZFSet.mem_sep.mpr ⟨label_mem a y.1,label b y.2,label_mem b y.2,
    label c x,hxD,hl,hy.2⟩⟩

theorem fiberSet_dense (M a b c D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hd : Dense {x : Conditions c | label c x ∈ D})
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    Dense {r : Conditions b | label b r ∈ fiberSet b D (genericFilterSet a G.carrier)} := by
  intro r
  obtain ⟨p,hp,hpr⟩ := hG (sectionSet a b D (label b r))
    (sectionSet_mem M a b D _ hM hT ha hb hD (hM b hb _ (label_mem b r)))
    (sectionSet_dense a b c D hcs hd r)
  obtain ⟨_,s,hs,z,hz,hzs,hrs⟩ := ZFSet.mem_sep.mp hpr
  obtain ⟨s,rfl⟩ := label_surjective b hs
  exact ⟨s,hrs,ZFSet.mem_sep.mpr ⟨label_mem b s,label a p,
    (mem_genericFilterSet a G.carrier _).mpr ⟨p,hp,rfl⟩,z,hz,hzs⟩⟩

theorem joint_ground_generic (M a b c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions b))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M a G.carrier) H) :
    AtomicForcing.GroundGeneric M (joint a b c hcs G H) := by
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  intro D hD hd
  obtain ⟨s,hs,hsE⟩ := hH (fiberSet b D (genericFilterSet a G.carrier))
    (fiberSet_mem _ b D _ hN hTN (hMN hb) (hMN hD) hgN)
    (fiberSet_dense M a b c D hM hT ha hb hD hcs hd G hG)
  obtain ⟨_,p,hp,z,hz,he⟩ := ZFSet.mem_sep.mp hsE
  obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a G.carrier p).mp hp
  refine ⟨productMap a b c hcs (p,s),(joint_mem a b c hcs G H p s).mpr ⟨hpG,hs⟩,?_⟩
  rw [label_productMap,←he]
  exact hz

end TuringRigidity.TaggedProductGeneric

end OAI
