/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners
import LeanPool.GraphMinor.GM11.EvenCircuit
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Distinct incident edges from distinct corner regions

In the base case of XII (7.4), pages 262--263, a non-loop
incident edge has just one half-edge at the vertex. If some
other edge had two half-edges there, distinct corner regions
force those half-edges to be each other's successors. The cyclic
order would then consist only of those two half-edges, contrary
to the non-loop edge. Thus every incident edge occurs once in
the corner order, as required by the finite gluing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The two endpoint parameters of a non-loop edge are distinct. -/
theorem endpoint_parameter_injective_of_distinct_ends
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ) {e : Set S} (he : e ∈ Γ.E)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ Γ.V = {u, v}) :
    Function.Injective (fun b => γ e (endOf b)) := by
  have huCap : u ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inl rfl : u ∈ ({u, v} : Set S))
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  rw [closure_inter_V_eq hγ he] at huCap hvCap
  have hne : γ e (endOf false) ≠ γ e (endOf true) := by
    intro heq
    rw [heq] at huCap hvCap
    have hu' : u = γ e (endOf true) := by
      simpa only [pair_eq_singleton, mem_singleton_iff] using huCap
    have hv' : v = γ e (endOf true) := by
      simpa only [pair_eq_singleton, mem_singleton_iff] using hvCap
    exact huv (hu'.trans hv'.symm)
  intro b c hbc
  cases b <;> cases c
  · rfl
  · exact (hne hbc).elim
  · exact (hne hbc.symm).elim
  · rfl

/-- A non-loop edge has just one half-edge at a specified end. -/
theorem halfedge_eq_of_same_nonloop_edge
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ) {v : S}
    (keep k : halfEdges Γ γ v) {u : S} (huv : u ≠ v)
    (hcap : closure keep.1.1 ∩ Γ.V = {u, v}) (hEdge : k.1.1 = keep.1.1) : k = keep := by
  have hk : γ keep.1.1 (endOf k.1.2) = v := by rw [← hEdge]; exact k.2.2
  have hb : k.1.2 = keep.1.2 :=
    endpoint_parameter_injective_of_distinct_ends hγ keep.2.1 huv hcap (hk.trans keep.2.2.symm)
  exact Subtype.ext (Prod.ext hEdge hb)

/-- If corner regions are distinct and one edge has a singleton
half-edge fibre, every edge does. A doubled edge would force a
cyclic order consisting of its two half-edges alone. -/
theorem corner_edges_injective_of_single_fibre
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → unitInterval → S} {v : S}
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ : halfEdges Γ γ v → Set S} (hcor : IsCorners Γ γ v next ρ)
    (hρ : Function.Injective ρ) (keep : halfEdges Γ γ v)
    (hkeep : ∀ k : halfEdges Γ γ v, k.1.1 = keep.1.1 → k = keep) :
    Function.Injective (fun k : halfEdges Γ γ v => k.1.1) := by
  intro a b hab
  by_contra hne
  have hsurj := next_surjective hcor
  have hcl : ∀ k : halfEdges Γ γ v, k.1.1 ⊆ closure (ρ k) := by
    intro k
    obtain ⟨p, hp⟩ := hsurj k
    exact hp ▸ hcor.right p
  have hnext : ∀ i j : halfEdges Γ γ v, i ≠ j → i.1.1 = j.1.1 → next j = i := by
    intro i j hij hEdge
    obtain ⟨p, hp⟩ := hsurj i
    have hecl : (next p).1.1 ⊆ closure (ρ j) := by rw [hp, hEdge]; exact hcl j
    rcases hcor.sides p (ρ j) (hcor.region j) hecl with h | h
    · have hjp : j = p := hρ h
      exact hjp.symm ▸ hp
    · have hji : j = i := hρ (h.trans (congrArg ρ hp))
      exact (hij hji.symm).elim
  have hba : next b = a := hnext a b hne hab
  have hab' : next a = b := hnext b a (Ne.symm hne) hab.symm
  have hall : ∀ k : halfEdges Γ γ v, k = a ∨ k = b := by
    intro k
    have hr := hcor.reach a k
    induction hr with
    | refl => exact Or.inl rfl
    | tail hr hs ih =>
      rcases ih with h | h
      · exact Or.inr (hs.trans ((congrArg next h).trans hab'))
      · exact Or.inl (hs.trans ((congrArg next h).trans hba))
  have haKeep : a.1.1 = keep.1.1 := by
    rcases hall keep with hk | hk
    · exact congrArg (fun j : halfEdges Γ γ v => j.1.1) hk.symm
    · exact hab.trans (congrArg (fun j : halfEdges Γ γ v => j.1.1) hk.symm)
  have hbKeep : b.1.1 = keep.1.1 := hab.symm.trans haKeep
  exact hne ((hkeep a haKeep).trans (hkeep b hbKeep).symm)

end GraphMinor.GM12
