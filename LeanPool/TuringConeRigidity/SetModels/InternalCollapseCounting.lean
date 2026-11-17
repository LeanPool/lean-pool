/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCollapseCounting.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseDense
public import LeanPool.TuringConeRigidity.SetModels.CountableSetReal

/-!
# Internal Collapse Counting
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

noncomputable def unionGraph {c : ZFSet.{u}} (G : GenericFilter (Conditions c)) : ZFSet.{u} :=
  ZFSet.sUnion (genericFilterSet c G.carrier)

theorem mem_unionGraph {c : ZFSet.{u}} (G : GenericFilter (Conditions c)) (z : ZFSet.{u}) :
    z ∈ unionGraph G ↔ ∃ p ∈ G.carrier, z ∈ label c p := by
  rw [unionGraph,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨p,hp,hz⟩
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet c G.carrier p).mp hp
    exact ⟨q,hq,hz⟩
  · rintro ⟨p,hp,hz⟩
    exact ⟨label c p,(mem_genericFilterSet c G.carrier _).mpr ⟨p,hp,rfl⟩,hz⟩

theorem unionGraph_functional {A c : ZFSet.{u}}
    (hc : ∀ p ∈ c, Prefix A p) (G : GenericFilter (Conditions c))
    {i x y : ZFSet.{u}} (hx : ZFSet.pair i x ∈ unionGraph G)
    (hy : ZFSet.pair i y ∈ unionGraph G) : x = y := by
  obtain ⟨p,hp,hpx⟩ := (mem_unionGraph G _).mp hx
  obtain ⟨q,hq,hqy⟩ := (mem_unionGraph G _).mp hy
  obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
  obtain ⟨k,hr⟩ := hc _ (label_mem c r)
  have hid : i ∈ natSet k := by
    obtain ⟨j,hj,z,_,he⟩ := hr.1 _ (hrp hpx)
    obtain ⟨rfl,_⟩ := ZFSet.pair_inj.mp he
    exact hj
  exact hr.functional hid (hrp hpx) (hrq hqy)

theorem unionGraph_total (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (n : ℕ) :
    ∃ x ∈ A, ZFSet.pair (natSet n) x ∈ unionGraph G := by
  obtain ⟨p,hp,hpn⟩ := hG (definedAt c A n) (definedAt_mem M hM hT hcM hA n)
    (definedAt_dense M hM hT hA hc hne n)
  obtain ⟨_,x,hx,hnx⟩ := ZFSet.mem_sep.mp hpn
  exact ⟨x,hx,(mem_unionGraph G _).mpr ⟨p,hp,hnx⟩⟩

theorem unionGraph_onto (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    ∀ x ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ unionGraph G := by
  intro x hx
  obtain ⟨p,hp,hpx⟩ := hG (covers c x) (covers_mem M hM hT hcM (hM _ hA _ hx))
    (covers_dense M hM hT hA hc hx)
  obtain ⟨_,n,hn,hnx⟩ := ZFSet.mem_sep.mp hpx
  exact ⟨n,hn,(mem_unionGraph G _).mpr ⟨p,hp,hnx⟩⟩

theorem unionGraph_function (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    TransitiveNameModel.FunctionGraph ZFSet.omega A (unionGraph G) := by
  have hcP : ∀ p ∈ c, Prefix A p := fun p hp => ((hc p).mp hp).2
  constructor
  · intro z hz
    obtain ⟨p,_,hzp⟩ := (mem_unionGraph G z).mp hz
    exact ZFSet.mem_prod.mp (prefix_subset (hcP _ (label_mem c p)) hzp)
  · intro i hi
    obtain ⟨n,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨x,hx,hnx⟩ := unionGraph_total M hM hT hA hcM hc hne G hG n
    exact ⟨x,hx,hnx,fun y _ hny => unionGraph_functional hcP G hny hnx⟩

theorem unionGraph_mem_extension (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (hcM : c ∈ M) (h0 : (∅ : ZFSet.{u}) ∈ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M c G.carrier := by
  let _ := top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact G.upper le_top hp
  have hE := extension_sourceT M hM hT hcM (orderSet_mem M hM hT hcM) (orderSet_pair c) G hG htop
  apply union_mem _ (genericExtensionSet_transitive M c hM G.carrier) hE.union
  exact genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcM G.carrier htop

theorem internal_counting (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    InternallyCountable (genericExtensionSet M c G.carrier) A := by
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hc ∅).mpr ⟨hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero,prefix_empty A⟩
  exact ⟨unionGraph G,unionGraph_mem_extension M hM hT hcM h0 G hG,
    unionGraph_function M hM hT hA hcM hc hne G hG,unionGraph_onto M hM hT hA hcM hc G hG⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
