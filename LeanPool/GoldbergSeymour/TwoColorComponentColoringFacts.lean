/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapPresentColors
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

/-!
# Missing-Color Endpoints and Component Swaps

Shared facts extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 and generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A vertex missing either swap color has at most one incidence-graph neighbor. -/
theorem TwoColorMissingVertexLeaf.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton := by
  classical
  intro V E _ G k rho a b hne hp v hm
  exact TwoColorMissingVertexNeighborsSubsingleton G rho hp a b v hm

/-- Three distinct missing-color endpoints cannot lie in the same two-color path component. -/
theorem TwoColorMissingVerticesDisjoint {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) (k : ℕ) (rho : PartialEdgeColoring E k) (a b : Fin k)
    (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
    (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
    (hsame : TwoColorComponent G rho a b (Sum.inl u) =
      TwoColorComponent G rho a b (Sum.inl v)) :
    Disjoint (TwoColorComponent G rho a b (Sum.inl w))
      (TwoColorComponent G rho a b (Sum.inl u)) := by
  classical
  let _ := Fintype.ofFinite V
  have self (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := rfl
  have leaf := TwoColorMissingVertexLeaf G k
  rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
  · exfalso
    obtain ⟨s, t, p, hpPath, hsupport⟩ :=
      TwoColorComponentSpanningPath G rho a b hp (Sum.inl w)
    have ends (x : V) (hx : Sum.inl x ∈ TwoColorComponent G rho a b (Sum.inl w))
        (hm : a ∈ MissingColors G rho x ∨ b ∈ MissingColors G rho x) :
        Sum.inl x = s ∨ Sum.inl x = t := by
      by_contra hnot
      push Not at hnot
      have hs : Sum.inl x ∈ p.support := by
        change Sum.inl x ∈ {z | z ∈ p.support}
        rw [hsupport]
        exact hx
      exact hpPath.isTrail.notMem_support_of_subsingleton_neighborSet
        hnot.1 hnot.2 (leaf rho a b hne hp x hm) hs
    have hue := ends u (he ▸ self rho a b u) (Or.inl hu)
    have hve := ends v (by rw [he, hsame]; exact self rho a b v) (Or.inr hv)
    have hwe := ends w (self rho a b w) hw
    rcases hue with hu | hu <;> rcases hve with hv | hv <;> rcases hwe with hw | hw
    all_goals first
      | exact huv (Sum.inl.inj (hu.trans hv.symm))
      | exact huw (Sum.inl.inj (hu.trans hw.symm))
      | exact hvw (Sum.inl.inj (hv.trans hw.symm))
  · exact hd

/-- A third missing-color endpoint is disjoint even when the two initial endpoints coincide. -/
theorem TwoColorMissingVerticesDisjointAny {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) (k : ℕ) (rho : PartialEdgeColoring E k) (a b : Fin k)
    (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w)
    (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
    (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
    (hsame : TwoColorComponent G rho a b (Sum.inl u) =
      TwoColorComponent G rho a b (Sum.inl v)) :
    Disjoint (TwoColorComponent G rho a b (Sum.inl w))
      (TwoColorComponent G rho a b (Sum.inl u)) := by
  classical
  let _ := Fintype.ofFinite V
  have self (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := rfl
  have separate := TwoColorMissingVerticesDisjoint G k
  by_cases huv : u = v
  · subst v
    rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
    · have noColor (c : Fin k) (hc : c ∈ MissingColors G rho u)
          (f : E) (hf : Incident G u f) : rho f ≠ some c := by
        intro hcol
        exact (Finset.mem_sdiff.mp hc).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hcol⟩)
      have hn : (TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl u) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        cases x with
        | inl x => exact hx
        | inr f =>
          rcases hx with ⟨hi, hc⟩
          exact hc.elim (noColor a hu f hi) (noColor b hv f hi)
      have hwIn : Sum.inl w ∈ TwoColorComponent G rho a b (Sum.inl u) :=
        he ▸ self rho a b w
      change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl w) =
        (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl u) at hwIn
      exact False.elim (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
        (fun h => huw (Sum.inl.inj h)) hn
        (SimpleGraph.ConnectedComponent.exact hwIn).symm)
    · exact hd
  · exact separate rho a b hne hp u v w huv huw hvw hu hv hw hsame

/-- Missing colors on an elementary set are unchanged when both witnesses avoid the swap
component. -/
theorem TwoColorComponentSwapMissingOnElementarySet {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} (vertices : Finset V) (rho : PartialEdgeColoring E k)
    (a b : Fin k) (hne : a ≠ b) (hp : IsProperEdgeColoring G rho)
    (elementary : ColoredVertexSetElementary G rho vertices) (z : Sum V E)
    (u v : V) (huSet : u ∈ vertices) (hvSet : v ∈ vertices)
    (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
    (huOutside : Sum.inl u ∉ TwoColorComponent G rho a b z)
    (hvOutside : Sum.inl v ∉ TwoColorComponent G rho a b z) :
    ∀ w ∈ vertices, MissingColors G (TwoColorComponentSwap G rho a b z) w =
      MissingColors G rho w := by
  classical
  have behavior := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
  intro w member
  by_cases component : Sum.inl w ∈ TwoColorComponent G rho a b z
  · have missingA : a ∉ MissingColors G rho w := by
      intro missing
      have different : w ≠ u := fun equal => huOutside (equal ▸ component)
      exact Finset.disjoint_left.mp (elementary member huSet different) missing hu
    have missingB : b ∉ MissingColors G rho w := by
      intro missing
      have different : w ≠ v := fun equal => hvOutside (equal ▸ component)
      exact Finset.disjoint_left.mp (elementary member hvSet different) missing hv
    have presentA : a ∈ PresentColors G rho w := by simpa [MissingColors] using missingA
    have presentB : b ∈ PresentColors G rho w := by simpa [MissingColors] using missingB
    have newA : a ∉ MissingColors G (TwoColorComponentSwap G rho a b z) w := by
      simpa [MissingColors] using TwoColorComponentSwapPreservesPresent presentA presentB a presentA
    have newB : b ∉ MissingColors G (TwoColorComponentSwap G rho a b z) w := by
      simpa [MissingColors] using TwoColorComponentSwapPreservesPresent presentA presentB b presentB
    apply Finset.ext
    intro color
    by_cases equalA : color = a
    · subst color
      simp only [newA, missingA]
    · by_cases equalB : color = b
      · subst color
        simp only [newB, missingB]
      · exact behavior.2.2.2 w color equalA equalB
  · exact behavior.1 w component

end GoldbergSeymour

end
