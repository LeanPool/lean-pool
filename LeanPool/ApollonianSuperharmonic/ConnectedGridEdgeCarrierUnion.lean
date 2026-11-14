/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.IntermediateValue

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.GridEdgeCarrier

-- [TABLET NODE: ConnectedGridEdgeCarrierUnion]

/-!
# ConnectedGridEdgeCarrierUnion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ConnectedGridEdgeCarrierUnion
    (X : Set GaussianInt) (E : Set (Finset GaussianInt))
     (hEnonempty : E.Nonempty)
    (hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
      e = {a, b} ∧ FourNeighborAdjacent a b)
    (hsupport : X = {x | ∃ e ∈ E, x ∈ e})
    (hconnected : (SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E).Connected) :
    IsConnected (⋃ e ∈ E, GridEdgeCarrier e) := by
-- BODY
  classical
  have intervalConnected : ∀ p q : Real × Real, IsConnected (Set.uIcc p q) := by
    intro p q
    rw [Set.uIcc_prod_eq]
    exact (isConnected_Icc inf_le_sup).prod (isConnected_Icc inf_le_sup)
  have carrierConnected : ∀ e ∈ E, IsConnected (GridEdgeCarrier e) := by
    intro e he
    obtain ⟨a, b, hab, hadj⟩ := hgrid e he
    have hcarrier : GridEdgeCarrier e = Set.uIcc (GaussianRealPoint a) (GaussianRealPoint b) := by
      ext p
      simp only [GridEdgeCarrier, hab, Set.mem_iUnion]
      constructor
      · rintro ⟨x, hx, y, hy, hp⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rw [Set.uIcc_self] at hp
          rw [hp]
          exact Set.left_mem_uIcc
        · exact hp
        · simpa [Set.uIcc_comm] using hp
        · rw [Set.uIcc_self] at hp
          rw [hp]
          exact Set.right_mem_uIcc
      · intro hp
        exact ⟨a, by simp, b, by simp, hp⟩
    rw [hcarrier]
    exact intervalConnected _ _
  have carrierPoint : ∀ e ∈ E, ∀ x ∈ e, GaussianRealPoint x ∈ GridEdgeCarrier e := by
    intro e he x hx
    simp only [GridEdgeCarrier, Set.mem_iUnion]
    exact ⟨x, hx, x, hx, by simp⟩
  let R : (Finset GaussianInt) → (Finset GaussianInt) → Prop :=
    fun e f => (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty ∧ e ∈ E
  have liftPath : ∀ {x y : X}, Relation.ReflTransGen
      ((SimpleGraph.fromRel (fun a b : X => ({a.1, b.1} : Finset GaussianInt) ∈ E)).Adj) x y →
      ∀ e ∈ E, x.1 ∈ e → ∀ f ∈ E, y.1 ∈ f →
        Relation.ReflTransGen R e f := by
    intro x y hpath
    induction hpath with
    | refl =>
        intro e he hxe f hf hyf
        exact Relation.ReflTransGen.single ⟨⟨GaussianRealPoint x.1,
          carrierPoint e he x.1 hxe, carrierPoint f hf x.1 hyf⟩, he⟩
    | @tail z w hprev hadj ih =>
        intro e he hxe f hf hyf
        rcases (SimpleGraph.fromRel_adj _ _ _).mp hadj with ⟨hne, hrel | hrel⟩
        · let g : Finset GaussianInt := {z.1, w.1}
          have hg : g ∈ E := by simpa [g] using hrel
          have hgz : z.1 ∈ g := by simp [g]
          have hgw : w.1 ∈ g := by simp [g]
          have hmid := ih e he hxe g hg hgz
          exact hmid.tail ⟨⟨GaussianRealPoint w.1,
            carrierPoint g hg w.1 hgw, carrierPoint f hf w.1 hyf⟩, hg⟩
        · let g : Finset GaussianInt := {z.1, w.1}
          have hg : g ∈ E := by simpa [g, Finset.pair_comm] using hrel
          have hgz : z.1 ∈ g := by simp [g]
          have hgw : w.1 ∈ g := by simp [g]
          have hmid := ih e he hxe g hg hgz
          exact hmid.tail ⟨⟨GaussianRealPoint w.1,
            carrierPoint g hg w.1 hgw, carrierPoint f hf w.1 hyf⟩, hg⟩
  have hEsub : ∀ e ∈ E, IsConnected (GridEdgeCarrier e) := carrierConnected
  have hEne : E.Nonempty := hEnonempty
  have hR : ∀ e ∈ E, ∀ f ∈ E, Relation.ReflTransGen R e f := by
    intro e he f hf
    obtain ⟨a, b, hab, hadj⟩ := hgrid e he
    obtain ⟨c, d, hcd, hcdadj⟩ := hgrid f hf
    have haX : a ∈ X := by rw [hsupport]; exact ⟨e, he, by rw [hab]; simp⟩
    have hcX : c ∈ X := by rw [hsupport]; exact ⟨f, hf, by rw [hcd]; simp⟩
    have hreach : (SimpleGraph.fromRel (fun u v : X =>
        ({u.1, v.1} : Finset GaussianInt) ∈ E)).Reachable
        ⟨a, haX⟩ ⟨c, hcX⟩ := hconnected ⟨a, haX⟩ ⟨c, hcX⟩
    have hrt := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hreach
    exact liftPath hrt e he (by rw [hab]; simp) f hf (by rw [hcd]; simp)
  refine IsConnected.biUnion_of_reflTransGen hEne hEsub ?_
  intro e he f hf
  exact hR e he f hf

end ApollonianSuperharmonic

end
