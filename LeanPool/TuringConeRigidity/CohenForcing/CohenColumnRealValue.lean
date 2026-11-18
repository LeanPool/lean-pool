/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenColumnRealValue.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnRealName
public import LeanPool.TuringConeRigidity.CohenForcing.SparseCohenFilter
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenProjectedGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGenericUnion

/-!
# Cohen Column Real Value
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet alphabet mem_alphabet bitSet_injective)
open CohenGroundPoset InternalCohenProjectedGeneric InternalCohenRestriction InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem union_real (K a : ZFSet.{0}) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K)))
    (hfun : FunctionGraph (ZFSet.prod K ZFSet.omega) alphabet (unionGraph G)) :
    ∃ A : Oracle, ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
  classical
  have hn (n : ℕ) : ZFSet.pair a (natSet n) ∈ ZFSet.prod K ZFSet.omega :=
    ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hex (n : ℕ) : ∃ b : Bool,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G := by
    obtain ⟨b,hb,hnb,_⟩ := hfun.2 _ (hn n)
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    exact ⟨b,hnb⟩
  let A : Oracle := fun n => (hex n).choose
  refine ⟨A,fun n b => ⟨fun hb => ?_,fun he => he ▸ (hex n).choose_spec⟩⟩
  obtain ⟨v,hv,hnv,huniq⟩ := hfun.2 _ (hn n)
  exact bitSet_injective ((huniq _ ((mem_alphabet _).mpr ⟨A n,rfl⟩)
    (hex n).choose_spec).trans (huniq _ ((mem_alphabet _).mpr ⟨b,rfl⟩) hb).symm)

theorem val_realName (K a : ZFSet.{0}) (G : GenericFilter (Conditions (poset K)))
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) :
    (realName K a).val G.carrier = realCode A := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions (poset K)) ∈ G.carrier := G.upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode A n).mpr ((hA n true).mp
      ((mem_unionGraph G _).mpr ⟨q,hq,hbit⟩))
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (mem_unionGraph G _).mp
      ((hA n true).mpr ((natSet_mem_realCode A n).mp hz))
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      realCode A ∈ genericExtensionSet M (poset K) G.carrier := by
  obtain ⟨A,hA⟩ := union_real K a ha G (CohenGenericUnion.manyColumn_union M K hM hT hK G hG).2
  have hv := val_realName K a G A hA
  exact ⟨A,hv,hA,(mem_extensionSet M (poset K) _ _).mpr
    ⟨realName K a,realName_internal M K a hM hT hK ha,hv⟩⟩

theorem singleton_filter_iff (a : ZFSet.{0})
    (G : GenericFilter (Conditions (poset {a}))) (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b)
    (p : Conditions (poset {a})) :
    p ∈ G.carrier ↔ ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b := by
  rw [SparseCohenFilter.mem_filter_iff_subset_union]
  constructor
  · intro hp n b hb
    exact (hA n b).mp (hp hb)
  · intro hp z hz
    have hsub := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions (ZFSet.prod {a} ZFSet.omega) _).mp (label_mem _ p)).1).1
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
    obtain ⟨a',ha',n,hn,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain rfl := ZFSet.mem_singleton.mp ha'
    obtain ⟨n,rfl⟩ := (mem_omega _).mp hn
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    exact (hA n b).mpr (hp n b hz)

theorem pair_mem_projected_union (C B : ZFSet.{0}) (hBC : B ⊆ C)
    (G : GenericFilter (Conditions (conditions C))) (x : ZFSet.{0}) (hx : x ∈ B) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ unionGraph (projected C B hBC G) ↔
      ZFSet.pair x (bitSet b) ∈ unionGraph G := by
  rw [InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨q,hq,hbit⟩
    obtain ⟨p,hp,rfl⟩ := (mem_projected C B hBC G q).mp hq
    rw [label_project,pair_restrict] at hbit
    exact ⟨p,hp,hbit.1⟩
  · rintro ⟨p,hp,hbit⟩
    refine ⟨project C B hBC p,projected_contains C B hBC G hp,?_⟩
    rw [label_project,pair_restrict]
    exact ⟨hbit,hx,(mem_alphabet _).mpr ⟨b,rfl⟩⟩

theorem singleton_coordinates_subset (K a : ZFSet.{0}) (ha : a ∈ K) :
    ZFSet.prod {a} ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega := by
  intro z hz
  obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
  obtain rfl := ZFSet.mem_singleton.mp hx
  exact ZFSet.pair_mem_prod.mpr ⟨ha,hn⟩

theorem projected_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ A : Oracle,
      (realName {a} a).val (projected C B hBC G).carrier = realCode A ∧
      (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      (∀ p : Conditions (poset {a}), p ∈ (projected C B hBC G).carrier ↔ ∀ n b,
        ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b) := by
  intro C B hBC
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  obtain ⟨A,hv,hA,_⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) (projected C B hBC G)
    (projected_groundGeneric M C B hM hT hC hB hBC G hG)
  have hfull (n : ℕ) (b : Bool) :
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
    rw [←pair_mem_projected_union C B hBC G _
      (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,(mem_omega _).mpr ⟨n,rfl⟩⟩) b]
    exact hA n b
  exact ⟨A,hv,val_realName K a G A hfull,hfull,
    singleton_filter_iff a (projected C B hBC G) A hA⟩

end TuringRigidity.CohenColumnRealName

end OAI
