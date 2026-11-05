/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# P2905_T2_Elementary Terminal Component

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2905_T2_ElementaryTerminalComponent {V E : Type*}
    [Finite V] [Fintype E] {k : ℕ} (G : LooplessMultigraph V E)
    (psi : PartialEdgeColoring E k) (a b : Fin k)
    (hne : a ≠ b) (hproper : IsProperEdgeColoring G psi)
    (B : Finset V) (helem : ColoredVertexSetElementary G psi B)
    (u v w : V) (hu : u ∈ B) (hv : v ∈ B)
    (hwu : w ≠ u) (hwv : w ≠ v)
    (hau : a ∈ MissingColors G psi u) (hbv : b ∈ MissingColors G psi v)
    (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w)
    (hsame : TwoColorComponent G psi a b (Sum.inl u) =
      TwoColorComponent G psi a b (Sum.inl v)) :
    Disjoint (TwoColorComponent G psi a b (Sum.inl w))
        (TwoColorComponent G psi a b (Sum.inl u)) ∧
      TwoColorPathComponent G psi a b (Sum.inl w) ∧
      (∀ x ∈ B,
        MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
          MissingColors G psi x) := by
  classical
  let _ := Fintype.ofFinite V
  let J := TwoColorIncidenceGraph G psi a b
  have leaf (x : V) (hx : a ∈ MissingColors G psi x ∨ b ∈ MissingColors G psi x) :
      (J.neighborSet (Sum.inl x)).Subsingleton := by
    have hd : @SimpleGraph.degree _ J (Sum.inl x) (Fintype.ofFinite _) ≤ 1 := by
      rcases hx with hx | hx
      · exact MissingColorIncidenceEndpoint G psi a b hne hproper x hx
      · have hJ : TwoColorIncidenceGraph G psi b a = J := by
          ext z z'
          cases z <;> cases z' <;> simp [J, TwoColorIncidenceGraph, or_comm]
        rw [← hJ]
        exact MissingColorIncidenceEndpoint G psi b a hne.symm hproper x hx
    let : Fintype (J.neighborSet (Sum.inl x)) := Fintype.ofFinite _
    have hc : Fintype.card (J.neighborSet (Sum.inl x)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hd
    intro z hz z' hz'
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨z', hz'⟩)
  have hnot : Sum.inl w ∉ TwoColorComponent G psi a b (Sum.inl u) := by
    intro hwC
    by_cases huv : u = v
    · subst v
      have isolated : J.neighborSet (Sum.inl u) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        cases z with
        | inl x => exact hz
        | inr e =>
          rcases hz.2 with hc | hc
          · exact (Finset.mem_sdiff.mp hau).2
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hz.1, hc⟩)
          · exact (Finset.mem_sdiff.mp hbv).2
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hz.1, hc⟩)
      have reach : J.Reachable (Sum.inl w) (Sum.inl u) :=
        SimpleGraph.ConnectedComponent.exact hwC
      exact SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
        (by intro hh; exact hwu (Sum.inl.inj hh)) isolated reach
    · obtain ⟨s, t, p, hp, hsupport⟩ :=
        TwoColorComponentSpanningPath G psi a b hproper (Sum.inl u)
      have endpoint (x : V)
          (hxC : Sum.inl x ∈ TwoColorComponent G psi a b (Sum.inl u))
          (hx : a ∈ MissingColors G psi x ∨ b ∈ MissingColors G psi x) :
          Sum.inl x = s ∨ Sum.inl x = t := by
        by_contra hh
        push Not at hh
        have hxP : Sum.inl x ∈ p.support := by
          change Sum.inl x ∈ {z | z ∈ p.support}
          rw [hsupport]
          exact hxC
        exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
          hh.1 hh.2 (leaf x hx)) hxP
      have huE := endpoint u (by rfl) (Or.inl hau)
      have hvE := endpoint v (by rw [hsame]; rfl) (Or.inr hbv)
      have hwE := endpoint w hwC hw
      rcases huE with huE | huE <;> rcases hvE with hvE | hvE <;>
        rcases hwE with hwE | hwE
      all_goals first
        | exact huv (Sum.inl.inj (huE.trans hvE.symm))
        | exact hwu (Sum.inl.inj (hwE.trans huE.symm))
        | exact hwv (Sum.inl.inj (hwE.trans hvE.symm))
  have hdis : Disjoint (TwoColorComponent G psi a b (Sum.inl w))
      (TwoColorComponent G psi a b (Sum.inl u)) := by
    rcases TwoColorComponentsDisjoint G psi a b (Sum.inl w) (Sum.inl u) with hh | hh
    · exact (hnot (by rw [← hh]; rfl)).elim
    · exact hh
  refine ⟨hdis, ⟨hne, Sum.inl w, by rfl, leaf w hw⟩, ?_⟩
  let Q := TwoColorComponent G psi a b (Sum.inl w)
  let tau := TwoColorComponentSwap G psi a b (Sum.inl w)
  have huQ : Sum.inl u ∉ Q := by
    intro hh
    exact Set.disjoint_left.mp hdis hh (by rfl)
  have hvQ : Sum.inl v ∉ Q := by
    intro hh
    exact Set.disjoint_left.mp hdis hh (by rw [hsame]; rfl)
  obtain ⟨outside, -, -, unaffected⟩ :=
    TwoColorComponentSwapMissingBehavior G psi a b hne hproper (Sum.inl w)
  have edgeIn {x : V} {e : E} (hx : Sum.inl x ∈ Q)
      (hi : Incident G x e) (hc : psi e = some a ∨ psi e = some b) :
      Sum.inr e ∈ Q := by
    change J.connectedComponentMk (Sum.inl x) = J.connectedComponentMk (Sum.inl w) at hx
    change J.connectedComponentMk (Sum.inr e) = J.connectedComponentMk (Sum.inl w)
    have ha : J.Adj (Sum.inr e) (Sum.inl x) := ⟨hi, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans hx
  intro x hx
  by_cases hxQ : Sum.inl x ∈ Q
  · have haNot : a ∉ MissingColors G psi x := by
      intro ha
      by_cases hxu : x = u
      · exact huQ (hxu ▸ hxQ)
      · exact Finset.disjoint_left.mp (helem hx hu hxu) ha hau
    have hbNot : b ∉ MissingColors G psi x := by
      intro hb
      by_cases hxv : x = v
      · exact hvQ (hxv ▸ hxQ)
      · exact Finset.disjoint_left.mp (helem hx hv hxv) hb hbv
    have present (c : Fin k) (hc : c ∉ MissingColors G psi x) :
        ∃ e, Incident G x e ∧ psi e = some c := by
      simpa [MissingColors, PresentColors] using hc
    obtain ⟨ea, hia, hca⟩ := present a haNot
    obtain ⟨eb, hib, hcb⟩ := present b hbNot
    have haNew : a ∉ MissingColors G tau x := by
      have heQ := edgeIn hxQ hib (Or.inr hcb)
      have hcol : tau eb = some a := by
        simp [tau, TwoColorComponentSwap, show Sum.inr eb ∈
          TwoColorComponent G psi a b (Sum.inl w) from heQ, hcb, hne.symm]
      exact fun hm => (Finset.mem_sdiff.mp hm).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, eb, hib, hcol⟩)
    have hbNew : b ∉ MissingColors G tau x := by
      have heQ := edgeIn hxQ hia (Or.inl hca)
      have hcol : tau ea = some b := by
        simp [tau, TwoColorComponentSwap, show Sum.inr ea ∈
          TwoColorComponent G psi a b (Sum.inl w) from heQ, hca]
      exact fun hm => (Finset.mem_sdiff.mp hm).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ea, hia, hcol⟩)
    ext c
    by_cases hca : c = a
    · subst c
      exact iff_of_false haNew haNot
    · by_cases hcb : c = b
      · subst c
        exact iff_of_false hbNew hbNot
      · exact unaffected x c hca hcb
  · exact outside x hxQ

end GoldbergSeymour

end
