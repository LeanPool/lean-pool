/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Cited
public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM19.Cited
import LeanPool.GraphMinor.GM12.Section3Theorem
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM12.Section4
import LeanPool.GraphMinor.GM12.Section4Monotone
import LeanPool.GraphMinor.GM12.Section4Theorem45
import LeanPool.GraphMinor.GM12.Section4Theorem44
import LeanPool.GraphMinor.GM12.Section4Theorem43
import LeanPool.GraphMinor.GM12.Section4DrawnGraph
import LeanPool.GraphMinor.GM12.Section4MetricExistence
import LeanPool.GraphMinor.GM12.Section4SpanControl
import LeanPool.GraphMinor.Minor.Basic
import Mathlib.Data.Fintype.EquivFin

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XII results in later papers

This file matches XII's proved results to the statements used by later
papers. No other XII file imports it.
-/

public section

namespace GraphMinor.GM12

universe u v w

/-- Graph Minors XII, (3.2), pages 245--248, in the exact form used
by XIX. The boundary conventions agree for each prescribed closed disc. -/
theorem gm19_theorem32
    : GM19.GM12Theorem32Statement.{u} := by
  intro S _ _ hS hConn t z
  let : T2Space S := hS.2.1
  let : ConnectedSpace S := hConn
  obtain ⟨η, hηpos, hmain⟩ := theorem_3_2_proof hS t z
  refine ⟨η, hηpos, ?_⟩
  intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeasible horder hm hsep hfree
  have hb : ∀ i, Surface.subBd (Δ i) = Surface.discBd (Δ i) := fun i =>
    (GM11.subBd_eq_frontier (Δ i)).trans (GM11.IsClosedDisc.frontier_eq_discBd hS (hΔ i).1)
  have hZeq : (⋃ i, Γ.V ∩ Surface.subBd (Δ i)) = discBoundaryVertices Γ Δ := by
    simp_rw [hb]
    rfl
  have hΔ' : ∀ i, Surface.IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ Surface.discBd (Δ i) := by
    intro i
    exact ⟨(hΔ i).1, by simpa only [hb i] using (hΔ i).2⟩
  have hfree' : ∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ Surface.discBd (Δ i)) := by
    intro i
    simpa only [hb i] using hfree i
  have hresult := hmain Δ Γ θ T d p Zs hΔ' hdis (by simpa only [hZeq] using hcount)
    (hcover.trans hZeq) hdisZ hfeasible horder hm hsep hfree'
  rwa [← hZeq] at hresult

/-- Graph Minors XII, (4.1), page 248, in the exact form used by XV. -/
theorem gm15_theorem41 : GM15.GM12Theorem41Statement.{u} := by
  exact @theorem_4_1_proof

open Set Graph Hypergraph

private theorem clique_inc {p : ℕ} {x y z : Fin p} (hxy : x ≠ y) :
    (GM16.completeGraph p).Inc s(x, y) z ↔ z = x ∨ z = y := by
  constructor
  · rintro ⟨w, _, heq⟩
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact ⟨y, hxy, rfl⟩
    · exact ⟨x, hxy.symm, Sym2.eq_swap⟩

/-- Every finite multigraph is a minor of a finite complete graph. Use a
central vertex for each target vertex and two separate end vertices for
each target edge. The branches are stars at their central vertices. This
also represents loops and parallel edges. -/
private theorem exists_completeGraph_minor {γ δ : Type*} (L : Graph γ δ)
    (hV : L.vertexSet.Finite) (hE : L.edgeSet.Finite) :
    ∃ p : ℕ, 1 ≤ p ∧ IsIsoMinor L (GM16.completeGraph p) := by
  classical
  let : Fintype L.vertexSet := hV.fintype
  let : Fintype L.edgeSet := hE.fintype
  let I := L.vertexSet ⊕ (L.edgeSet × Bool)
  let p := Fintype.card I + 1
  let tag : I → Fin p := fun z => ⟨(Fintype.equivFin I z).val,
    Nat.lt_succ_of_lt (Fintype.equivFin I z).isLt⟩
  have htag : Function.Injective tag := by
    intro x y h
    have hval : (Fintype.equivFin I x).val = (Fintype.equivFin I y).val :=
      congrArg (fun z : Fin p => z.val) h
    exact (Fintype.equivFin I).injective (Fin.ext hval)
  have hend : ∀ e : L.edgeSet, ∃ x y, L.IsLink e.val x y := fun e =>
    L.exists_isLink_of_mem_edgeSet e.property
  choose left right hlink using hend
  let owner : I → γ := Sum.elim Subtype.val (fun t => if t.2 then right t.1 else left t.1)
  let core (v : L.vertexSet) : Fin p := tag (Sum.inl v)
  let port (e : L.edgeSet) (b : Bool) : Fin p := tag (Sum.inr (e, b))
  let a : γ → Set (Fin p) := fun v => tag '' {z | owner z = v}
  let b : δ → Sym2 (Fin p) := fun e => if he : e ∈ L.edgeSet then
    s(port ⟨e, he⟩ false, port ⟨e, he⟩ true) else s(⟨0, Nat.zero_lt_succ _⟩, ⟨0, Nat.zero_lt_succ
      _⟩)
  have hmem : ∀ z v, tag z ∈ a v ↔ owner z = v := by
    intro z v
    constructor
    · rintro ⟨w, hw, heq⟩
      exact htag heq ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hport : ∀ e : L.edgeSet, port e false ≠ port e true := by
    intro e heq
    have := htag heq
    let portSide : I → Bool
      | .inl _ => false
      | .inr t => t.2
    exact Bool.false_ne_true (congrArg portSide this)
  have hcore : ∀ v : L.vertexSet, ∀ e : L.edgeSet, ∀ k, core v ≠ port e k := by
    intro v e k heq
    exact Sum.inl_ne_inr (htag heq)
  have hdisj : ∀ u ∈ L.vertexSet, ∀ v ∈ L.vertexSet, u ≠ v → Disjoint (a u) (a v) := by
    intro u _ v _ huv
    apply Set.disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact huv (hz.symm.trans ((hmem z v).mp hx))
  have hb : ∀ e (he : e ∈ L.edgeSet), b e = s(port ⟨e, he⟩ false, port ⟨e, he⟩ true) :=
    fun e he => dite_eq_left he
  have hinc : ∀ e (he : e ∈ L.edgeSet) v,
      (∃ x ∈ a v, (GM16.completeGraph p).Inc (b e) x) ↔
        v = left ⟨e, he⟩ ∨ v = right ⟨e, he⟩ := by
    intro e he v
    rw [hb e he]
    simp only [clique_inc (hport ⟨e, he⟩)]
    constructor
    · rintro ⟨x, hx, rfl | rfl⟩
      · exact Or.inl ((hmem _ v).mp hx).symm
      · exact Or.inr ((hmem _ v).mp hx).symm
    · rintro (rfl | rfl)
      · exact ⟨port ⟨e, he⟩ false, (hmem _ _).mpr rfl, Or.inl rfl⟩
      · exact ⟨port ⟨e, he⟩ true, (hmem _ _).mpr rfl, Or.inr rfl⟩
  have hm : IsMinorModel L (GM16.completeGraph p) a b := by
    refine {
      vertex_nonempty := ?_
      vertex_subset := fun _ _ _ _ => mem_univ _
      edge_mem := ?_
      vertex_disjoint := hdisj
      edge_injOn := ?_
      inc_iff := ?_
      isLoopAt_iff := ?_
      connected := ?_ }
    · intro v hv
      exact ⟨core ⟨v, hv⟩, (hmem _ _).mpr rfl⟩
    · intro e he
      rw [hb e he]
      exact ⟨_, _, hport ⟨e, he⟩, rfl⟩
    · intro e he f hf hef
      rw [hb e he, hb f hf] at hef
      rcases Sym2.eq_iff.mp hef with ⟨h, _⟩ | ⟨h, _⟩
      · have h' := htag h
        exact congrArg (fun z : I => match z with | .inl _ => e | .inr t => t.1.val) h'
      · have h' := htag h
        exact congrArg (fun z : I => match z with | .inl _ => e | .inr t => t.1.val) h'
    · intro v _ e he
      rw [hinc e he]
      constructor
      · intro hv
        exact hv.eq_or_eq_of_isLink (hlink ⟨e, he⟩)
      · rintro (rfl | rfl)
        · exact (hlink ⟨e, he⟩).inc_left
        · exact (hlink ⟨e, he⟩).inc_right
    · intro v _ e he
      rw [hb e he]
      constructor
      · intro hl x hx
        have hl' := hlink ⟨e, he⟩
        have hlv := hl.eq_of_inc hl'.inc_left
        have hrv := hl.eq_of_inc hl'.inc_right
        rcases (clique_inc (hport ⟨e, he⟩)).mp hx with rfl | rfl
        · exact (hmem _ _).mpr hlv.symm
        · exact (hmem _ _).mpr hrv.symm
      · intro hall
        have hlv := (hmem _ v).mp (hall _ ((clique_inc (hport ⟨e, he⟩)).mpr (Or.inl rfl)))
        have hrv := (hmem _ v).mp (hall _ ((clique_inc (hport ⟨e, he⟩)).mpr (Or.inr rfl)))
        change left ⟨e, he⟩ = v at hlv
        change right ⟨e, he⟩ = v at hrv
        have hl := hlink ⟨e, he⟩
        rw [hlv, hrv] at hl
        exact hl
    · intro v hv
      let K := ((GM16.completeGraph p).induce (a v)).deleteEdges (b '' L.edgeSet)
      have hcm : core ⟨v, hv⟩ ∈ a v := (hmem _ _).mpr rfl
      have hreach : ∀ x ∈ a v, Relation.ReflTransGen K.Adj x (core ⟨v, hv⟩) ∧
          Relation.ReflTransGen K.Adj (core ⟨v, hv⟩) x := by
        intro x hx
        by_cases hxc : x = core ⟨v, hv⟩
        · subst x
          exact ⟨.refl, .refl⟩
        have hn : s(x, core ⟨v, hv⟩) ∉ b '' L.edgeSet := by
          rintro ⟨e, he, heq⟩
          rw [hb e he] at heq
          rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h, _⟩
          · exact hcore ⟨v, hv⟩ ⟨e, he⟩ true h.symm
          · exact hcore ⟨v, hv⟩ ⟨e, he⟩ false h.symm
        have hadj : K.Adj x (core ⟨v, hv⟩) := ⟨s(x, core ⟨v, hv⟩), ⟨⟨hxc, rfl⟩, hx, hcm⟩, hn⟩
        exact ⟨.single hadj, .single hadj.symm⟩
      refine ⟨K, ?_, rfl, ⟨core ⟨v, hv⟩, hcm⟩, ?_⟩
      · exact ⟨subset_univ _, fun _ _ _ h => ⟨h.1.1, h.2⟩⟩
      · intro x hx y hy
        exact (hreach x hx).1.trans (hreach y hy).2
  refine ⟨p, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  exact isIsoMinor_of_isMinorModel L (GM16.completeGraph p) hV hE
    (Set.toFinite _) (Set.toFinite _) a b hm

/-- The finite-graph consequence of XII (4.2) used by XVI, with exactly
the cited conclusion. A sufficiently large complete graph contains the
given finite multigraph as a minor. -/
theorem gm16_theorem42 : GM16.GM12Theorem42Statement.{u, v} := by
  intro γ δ L hV hE
  obtain ⟨p, hp, hminor⟩ := exists_completeGraph_minor L hV hE
  refine ⟨p, ?_⟩
  intro α β G θ T hT hc
  have : NeZero p := ⟨Nat.ne_zero_of_lt hp⟩
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have hc' := hc
  obtain ⟨_, b, _⟩ := hc'
  let : Nonempty β := ⟨b s((0 : Fin p), 0)⟩
  exact theorem_4_2_proof hT.finite_V hT.finite_E (Set.toFinite _) (Set.toFinite _) hminor hc

/-- XII (4.3), pages 249--251, with exactly the span conclusion
cited by XVI. The drawing embedding transfers every branch and
joining edge, and the controlling-tangle condition transfers the
small-side exclusion. The cited hypotheses are VII (7.5), (5.1),
and (5.5). -/
theorem gm16_theorem43
    : GM16.GM12Theorem43Statement.{u, v, w} := by
  intro S _ _ α' β' L hS hConn hVL hEL hdraw
  let : ConnectedSpace S := hConn
  obtain ⟨ν, edgeOf, hν, hline, hloop, hmeet, hon⟩ := hdraw
  obtain ⟨D, _, _⟩ := exists_graphDrawing_of_edge_curves L hVL hEL ν edgeOf hν hline hloop hmeet hon
  obtain ⟨N, hN, hmain⟩ := theorem_4_3_drawing hS D
  refine ⟨N, hN, ?_⟩
  intro α β G θstar Tstar H η θ T hTstar hNo hθ hSpan
  obtain ⟨d, hd⟩ := exists_metric_of_respectful_drawing_tangle hS hSpan.isRespectful
  have hc := hmain H θ T d hd hθ
  exact hNo (controlsMinor_of_controlling_drawing_tangle η hSpan.isControlling hc)

/-- XII (4.4), pages 251--252, with exactly the span conclusion
cited by XVI. All branch, path, feasibility, and control steps are
proved; the statement hypotheses are VII (7.5), (5.1), and (5.5). -/
theorem gm16_theorem44
    : GM16.GM12Theorem44Statement.{u, v, w} := by
  intro S _ _ hS hConn p
  let : ConnectedSpace S := hConn
  obtain ⟨N, hN, hmain⟩ := theorem_4_4_span hS p
  refine ⟨N, hN, ?_⟩
  dsimp only
  intro α β G θstar θ Tstar H η T d s t P hSpan hm hθ hends hs ht hdisj hfar hP hPP
  exact hmain G θstar θ Tstar H η T d s t P hSpan.isControlling hm hθ hends hs ht hdisj hfar hP hPP

/-- Graph Minors XII (4.5), pages 252--253, in the exact independent-eye
span form used by XV. The only statement hypotheses are the cited
VII (7.5), (5.1), and (5.5). -/
theorem gm15_theorem45
    : GM15.GM12Theorem45Statement.{u, v, w} := by
  intro S _ _ hS hConn p
  let : ConnectedSpace S := hConn
  obtain ⟨k, N, hN, hmain⟩ := theorem_4_5_span hS p
  refine ⟨k, N, ?_⟩
  intro α β G θstar Tstar H η θ T d hSpan hm hpθ hNθ heyes
  obtain ⟨r, P, Q, hri, heye, hdist, hdisj⟩ := heyes
  have hfar : ∀ i j, i ≠ j → N ≤ d (r i) (r j) := by
    intro i j hij
    rw [hdist i j hij]
    exact hNθ
  exact hmain G θstar θ Tstar H η T d hSpan.isControlling hm hNθ r P Q hri heye hfar hdisj

/-- Unconditional proof of `GM19.GM12Theorem32Statement`. -/
theorem gm19_theorem32_proved : GM19.GM12Theorem32Statement.{u} :=
  gm19_theorem32

/-- Unconditional proof of `GM16.GM12Theorem43Statement`. -/
theorem gm16_theorem43_proved : GM16.GM12Theorem43Statement.{u, v, w} :=
  gm16_theorem43

/-- Unconditional proof of `GM16.GM12Theorem44Statement`. -/
theorem gm16_theorem44_proved : GM16.GM12Theorem44Statement.{u, v, w} :=
  gm16_theorem44

/-- Unconditional proof of `GM15.GM12Theorem45Statement`. -/
theorem gm15_theorem45_proved : GM15.GM12Theorem45Statement.{u, v, w} :=
  gm15_theorem45

end GraphMinor.GM12
