/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeControlledInterchange
public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TashTreeProperPrefixElementary
public import LeanPool.GoldbergSeymour.TreeUsedColors

/-!
# Tash Tree Last Index Second Normal Form

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hgamma_unused_110.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (hq : (2 : ℕ) < TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length) (_
        : Fin (T.length + (1 : ℕ))), TashTreeBadPair G k e0 phi T →
    let r : Fin T.length := (⟨T.length - (1 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (1 : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length);
    let p : Fin (T.length + (1 : ℕ)) := (⟨T.length - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) =>
    by
            omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (hr : (↑r : ℕ) + (1 : ℕ) = T.length),
    ∀ gamma ∈ MissingColors G phi (T.vertex p),
    let P : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ); P.length = T.length - (1 : ℕ) → ColoredVertexSetElementary G phi (TreeSequenceVertexSet P)
        → TreeColorUnusedThrough phi T gamma p := by
  classical
  intro V E _ _ _ G k e0 phi T hq hlast j hbad r p hr gamma hgamma_missing P hPlength
      hPelementary s hs1 hsp hscolor
  rcases hbad.2.1 s hs1 with ⟨i, c, hc, hm⟩
  have hcg : c = gamma := by
    exact Option.some.inj (hc.symm.trans hscolor)
  subst c
  have hilt : i.val < T.length - 1 := by
    have hiq : i.val ≤ s.val := Nat.le_of_lt_succ i.isLt
    have hslt : s.val < T.length - 1 := by simpa [p] using hsp
    omega
  have himem : T.vertex (Fin.castLT i
      (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))) ∈
      TreeSequenceVertexSet P := by
    rw [TreeSequenceVertexSet]
    apply Finset.mem_image.mpr
    refine ⟨⟨i.val, by rw [hPlength]; omega⟩, Finset.mem_univ _, ?_⟩
    rfl
  have hpmem : T.vertex p ∈ TreeSequenceVertexSet P := by
    rw [TreeSequenceVertexSet]
    refine Finset.mem_image.mpr ⟨⟨T.length - 1, by rw [hPlength]; omega⟩,
      Finset.mem_univ _, ?_⟩
    rfl
  have hne : T.vertex (Fin.castLT i
      (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))) ≠ T.vertex p := by
    intro he
    have hv := T.vertex_injective he
    dsimp [p] at hv
    have hiq : i.val < T.length - 1 := hilt
    have hcast : (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))).val = i.val := rfl
    omega
  have hd := hPelementary himem hpmem hne
  exact (Finset.disjoint_left.mp hd) hm hgamma_missing

private theorem helper_branch_158.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length) (beta : Fin k) (j : Fin
        (T.length + (1 : ℕ))), (↑j : ℕ) + (2 : ℕ) ≤ T.length → beta ∈ MissingColors G phi
        (T.vertex (Fin.last T.length)) → IsProperEdgeColoring G phi →
    let r : Fin T.length := (⟨T.length - (1 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (1 : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length);
    let p : Fin (T.length + (1 : ℕ)) := (⟨T.length - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) =>
    by
            omega
    ⟩ : Fin (T.length + (1 : ℕ))); (↑r : ℕ) + (1 : ℕ) = T.length →
    ∀ (gamma : Fin k), phi (T.edge r) = some gamma → Incident G (T.vertex (Fin.last T.length))
        (T.edge r) → beta ≠ gamma → TwoColorPathComponent G phi beta gamma (Sum.inl (T.vertex p))
        → Sum.inl (T.vertex j) ∈ TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)) →
        ((TwoColorIncidenceGraph G phi beta gamma).neighborSet (Sum.inl (T.vertex
        j))).Subsingleton → ((TwoColorIncidenceGraph G phi beta gamma).neighborSet (Sum.inl
        (T.vertex p))).Subsingleton → TwoColorComponentSwap G phi beta gamma (Sum.inl (T.vertex
        p)) (T.edge r) = some gamma := by
  classical
  intro V E _ _ G k e0 phi T hq hlast beta j hj hblast hproper r p hr gamma hgamma hlastincident
      hbeta_gamma hpath hjC hiSub hpSub
  let _ := Fintype.ofFinite V
  have houtside : Sum.inr (T.edge r) ∉
      TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)) := by
    by_contra hin
    obtain ⟨a, b, path, hpath, hsupport⟩ :=
      TwoColorComponentSpanningPath G phi beta gamma hproper
        (Sum.inl (T.vertex p))
    have support_of_component {x : Sum V E} (hx : x ∈
        TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p))) :
        x ∈ path.support := by
      change x ∈ {y | y ∈ path.support}
      rw [hsupport]
      exact hx
    have endpoint_of_subsingleton {x : Sum V E} (hx : x ∈
        TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)))
        (hxSub : Set.Subsingleton
          ((TwoColorIncidenceGraph G phi beta gamma).neighborSet x)) :
        x = a ∨ x = b := by
      by_contra hend
      push Not at hend
      exact (hpath.isTrail.notMem_support_of_subsingleton_neighborSet
        hend.1 hend.2 hxSub) (support_of_component hx)
    have hpC : Sum.inl (T.vertex p) ∈
        TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)) := by
      change Sum.inl (T.vertex p) ∈
        ((TwoColorIncidenceGraph G phi beta gamma).connectedComponentMk
          (Sum.inl (T.vertex p))).supp
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hmEnd := endpoint_of_subsingleton hjC hiSub
    have hpEnd := endpoint_of_subsingleton
      hpC hpSub
    have hlastC : Sum.inl (T.vertex (Fin.last T.length)) ∈
        TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)) := by
      have hadj : (TwoColorIncidenceGraph G phi beta gamma).Adj
          (Sum.inl (T.vertex (Fin.last T.length))) (Sum.inr (T.edge r)) := by
        simp [TwoColorIncidenceGraph, hlastincident, hgamma]
      have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      change Sum.inl (T.vertex (Fin.last T.length)) ∈
        ((TwoColorIncidenceGraph G phi beta gamma).connectedComponentMk
          (Sum.inl (T.vertex p))).supp
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hin' := hin
      change Sum.inr (T.edge r) ∈
        ((TwoColorIncidenceGraph G phi beta gamma).connectedComponentMk
          (Sum.inl (T.vertex p))).supp at hin'
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hin'
      exact heq.trans hin'
    have hlSub : Set.Subsingleton
        ((TwoColorIncidenceGraph G phi beta gamma).neighborSet
          (Sum.inl (T.vertex (Fin.last T.length)))) := by
      let : Fintype
          ((TwoColorIncidenceGraph G phi beta gamma).neighborSet
            (Sum.inl (T.vertex (Fin.last T.length)))) := Fintype.ofFinite _
      have hd := MissingColorIncidenceEndpoint G phi beta gamma
        hbeta_gamma hproper (T.vertex (Fin.last T.length)) hblast
      intro x hx y hy
      have hx' : x ∈ (TwoColorIncidenceGraph G phi beta gamma).neighborFinset
          (Sum.inl (T.vertex (Fin.last T.length))) := by
        apply (SimpleGraph.mem_neighborFinset
          (TwoColorIncidenceGraph G phi beta gamma)
          (Sum.inl (T.vertex (Fin.last T.length))) x).2
        simpa [TwoColorIncidenceGraph, or_comm] using hx
      have hy' : y ∈ (TwoColorIncidenceGraph G phi beta gamma).neighborFinset
          (Sum.inl (T.vertex (Fin.last T.length))) := by
        apply (SimpleGraph.mem_neighborFinset
          (TwoColorIncidenceGraph G phi beta gamma)
          (Sum.inl (T.vertex (Fin.last T.length))) y).2
        simpa [TwoColorIncidenceGraph, or_comm] using hy
      have hc : ((TwoColorIncidenceGraph G phi beta gamma).neighborFinset
          (Sum.inl (T.vertex (Fin.last T.length)))).card ≤ 1 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact hd
      exact (Finset.card_le_one.mp hc) x hx' y hy'
    have hlEnd := endpoint_of_subsingleton hlastC hlSub
    have hm_ne_last : (Sum.inl (T.vertex p) : Sum V E) ≠
        Sum.inl (T.vertex (Fin.last T.length)) := by
      intro he
      have hv : T.vertex p = T.vertex (Fin.last T.length) := by simpa using he
      have hh := congrArg Fin.val (T.vertex_injective hv)
      dsimp [p] at hh
      omega
    have hp_ne_last : (Sum.inl (T.vertex p) : Sum V E) ≠
        Sum.inl (T.vertex (Fin.last T.length)) := hm_ne_last
    have hj_ne_last : (Sum.inl (T.vertex j) : Sum V E) ≠
        Sum.inl (T.vertex (Fin.last T.length)) := by
      intro he
      have hv : T.vertex j = T.vertex (Fin.last T.length) := by simpa using he
      have hh := congrArg Fin.val (T.vertex_injective hv)
      dsimp [p] at hh
      omega
    have hm_ne_p : (Sum.inl (T.vertex j) : Sum V E) ≠
        Sum.inl (T.vertex p) := by
      intro he
      have hv : T.vertex j = T.vertex p := by simpa using he
      have hh := congrArg Fin.val (T.vertex_injective hv)
      dsimp [p] at hh
      omega
    rcases hmEnd with hmA | hmB <;> rcases hpEnd with hpA | hpB
    · exact hm_ne_p (hmA.trans hpA.symm)
    · rcases hlEnd with hlA | hlB
      · exact hj_ne_last (hmA.trans hlA.symm)
      · exact hp_ne_last (hpB.trans hlB.symm)
    · rcases hlEnd with hlA | hlB
      · exact hp_ne_last (hpA.trans hlA.symm)
      · exact hj_ne_last (hmB.trans hlB.symm)
    · exact hm_ne_p (hmB.trans hpB.symm)
  simp [TwoColorComponentSwap, houtside, hgamma]

private theorem helper_branch_265.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hlast : TashTreePathIndex G T = T.length) (beta : Fin k) (j : Fin
        (T.length + (1 : ℕ))), (↑j : ℕ) + (2 : ℕ) ≤ T.length → IsProperEdgeColoring G phi →
    let r : Fin T.length := (⟨T.length - (1 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (1 : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length);
    let p : Fin (T.length + (1 : ℕ)) := (⟨T.length - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) =>
    by
            omega
    ⟩ : Fin (T.length + (1 : ℕ))); (↑r : ℕ) + (1 : ℕ) = T.length →
    ∀ (gamma : Fin k), beta ≠ gamma → gamma ∈ MissingColors G phi (T.vertex p) → Sum.inl (T.vertex
        j) ∈ TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)) → ((TwoColorIncidenceGraph
        G phi beta gamma).neighborSet (Sum.inl (T.vertex j))).Subsingleton →
        ((TwoColorIncidenceGraph G phi beta gamma).neighborSet (Sum.inl (T.vertex
        p))).Subsingleton → gamma ∈ PresentColors G (TwoColorComponentSwap G phi beta gamma
        (Sum.inl (T.vertex p))) (T.vertex p) := by
  classical
  intro V E _ _ G k e0 phi T hq hlast beta j hj hproper r p hr gamma hbeta_gamma hgamma_missing hjC
      hiSub hpSub
  let _ := Fintype.ofFinite V
  have hpC : Sum.inl (T.vertex p) ∈
      TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)) := by
    change Sum.inl (T.vertex p) ∈
      ((TwoColorIncidenceGraph G phi beta gamma).connectedComponentMk
        (Sum.inl (T.vertex p))).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  obtain ⟨a, b, path, pathIsPath, pathSupport⟩ :=
    TwoColorComponentSpanningPath G phi beta gamma hproper
      (Sum.inl (T.vertex p))
  have endpoint_of_subsingleton {x : Sum V E} (hx : x ∈
      TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)))
      (hxSub : Set.Subsingleton
        ((TwoColorIncidenceGraph G phi beta gamma).neighborSet x)) :
      x = a ∨ x = b := by
    by_contra hend
    push Not at hend
    have hsupp : x ∈ path.support := by
      change x ∈ {y | y ∈ path.support}
      rw [pathSupport]
      exact hx
    exact (pathIsPath.isTrail.notMem_support_of_subsingleton_neighborSet
      hend.1 hend.2 hxSub) hsupp
  have hpEnd := endpoint_of_subsingleton hpC hpSub
  have hjEnd := endpoint_of_subsingleton hjC hiSub
  have hj_ne_p : (Sum.inl (T.vertex j) : Sum V E) ≠
      Sum.inl (T.vertex p) := by
    intro he
    have hv : T.vertex j = T.vertex p := by simpa using he
    have hh := congrArg Fin.val (T.vertex_injective hv)
    dsimp [p] at hh
    omega
  have hab : a ≠ b := by
    intro hab
    rcases hpEnd with hpa | hpb
    · rcases hjEnd with hja | hjb
      · exact hj_ne_p (hja.trans hpa.symm)
      · exact hj_ne_p ((hjb.trans hab.symm).trans hpa.symm)
    · rcases hjEnd with hja | hjb
      · exact hj_ne_p ((hja.trans hab).trans hpb.symm)
      · exact hj_ne_p (hjb.trans hpb.symm)
  have hnon : ¬ path.Nil := SimpleGraph.Walk.not_nil_of_ne hab
  have hadj : ∃ x : Sum V E,
      (TwoColorIncidenceGraph G phi beta gamma).Adj
        (Sum.inl (T.vertex p)) x := by
    rcases hpEnd with hpa | hpb
    · refine ⟨path.snd, ?_⟩
      simpa [hpa] using path.adj_snd hnon
    · refine ⟨path.penultimate, ?_⟩
      simpa [hpb] using (path.adj_penultimate hnon).symm
  obtain ⟨x, hx⟩ := hadj
  cases x with
  | inl v => simp [TwoColorIncidenceGraph] at hx
  | inr e =>
    have he : Incident G (T.vertex p) e ∧
        (phi e = some beta ∨ phi e = some gamma) := by
      simpa [TwoColorIncidenceGraph] using hx
    have hnotgamma : gamma ∉ PresentColors G phi (T.vertex p) := by
      simpa [MissingColors] using hgamma_missing
    have hebeta : phi e = some beta := by
      rcases he.2 with heb | heg
      · exact heb
      · exfalso
        apply hnotgamma
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, he.1, heg⟩
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨e, he.1, ?_⟩
    have hCedge : Sum.inr e ∈
        TwoColorComponent G phi beta gamma (Sum.inl (T.vertex p)) := by
      change Sum.inr e ∈
        ((TwoColorIncidenceGraph G phi beta gamma).connectedComponentMk
          (Sum.inl (T.vertex p))).supp
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hx).symm
    simp [TwoColorComponentSwap, hCedge, hebeta]

theorem TashTreeLastIndexSecondNormalForm {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (beta : Fin k) (j : Fin (T.length + 1))
    (hj : j.val + 2 ≤ T.length)
    (hbj : beta ∈ MissingColors G phi (T.vertex j))
    (hblast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hbunused : beta ∉ TreeUsedColors phi T) :
    ∃ (phi₂ : PartialEdgeColoring E k) (gamma : Fin k) (r : Fin T.length) (p :
      Fin (T.length + 1)),
    r.val + 1 = T.length ∧
      p.val + 1 = T.length ∧
        TashTreeMinimumBadPair G k e0 phi₂ T ∧
          phi₂ (T.edge r) = some gamma ∧ gamma ∈ PresentColors G phi₂ (T.vertex p) := by
  classical
  have hlen : 3 ≤ T.length := by omega
  have hbad := hmin.1
  have htriple := hbad.1
  have hproper := htriple.2.2.2.1
  have hone := htriple.2.2.2.2
  let r : Fin T.length := ⟨T.length - 1, by omega⟩
  let p : Fin (T.length + 1) := ⟨T.length - 1, by omega⟩
  have hr : r.val + 1 = T.length := by dsimp [r]; omega
  have hp : p.val + 1 = T.length := by dsimp [p]; omega
  have hlastedge_ne : T.edge r ≠ e0 := by
    intro he
    have hz : T.edge r = T.edge ⟨0, T.positive⟩ := by
      rw [he, T.first_edge]
    have hrz := T.edge_injective hz
    dsimp [r] at hrz
    have hrzero : r.val = 0 := congrArg Fin.val hrz
    dsimp [r] at hrzero
    omega
  obtain ⟨gamma, hgamma⟩ := hone.2 (T.edge r) hlastedge_ne
  have hlastincident : Incident G (T.vertex (Fin.last T.length)) (T.edge r) := by
    obtain ⟨i, hi⟩ := T.attaches r
    have hrs : r.succ = Fin.last T.length := by
      apply Fin.ext
      simpa using hr
    rw [Incident, hi]
    simp [hrs]
  have hbeta_gamma : beta ≠ gamma := by
    intro heq
    have hnotpresent : beta ∉ PresentColors G phi
        (T.vertex (Fin.last T.length)) := by
      simpa [MissingColors] using hblast
    apply hnotpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨T.edge r, hlastincident, by simpa [heq] using hgamma⟩
  by_cases hpres : gamma ∈ PresentColors G phi (T.vertex p)
  · exact ⟨phi, gamma, r, p, hr, hp, hmin, hgamma, hpres⟩
  have hgamma_missing : gamma ∈ MissingColors G phi (T.vertex p) := by
    rw [MissingColors]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact hpres
  let P : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
  have hPlength : P.length = T.length - 1 := by rfl
  have hPprefix : TreeSequenceInitialSegment P T := by
    refine ⟨by rw [hPlength]; omega, ?_, ?_⟩
    · intro i; rfl
    · intro i; rfl
  have hPelementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet P) := by
    apply TashTreeProperPrefixElementary G k e0 phi T P hmin hPprefix
    change T.length - 1 < T.length
    omega
  have hgamma_unused := @helper_hgamma_unused_110 V E inferInstance inferInstance inferInstance G k
      e0 phi T hq hlast j hbad hr gamma hgamma_missing hPlength hPelementary
  have hcontrolled := TashTreeControlledInterchange G k e0 phi T hmin
    j p (by dsimp [p]; omega) (by dsimp [p]; omega)
    beta gamma hbeta_gamma hbj hgamma_missing
    (by
      intro s hs1 hsj heq
      apply hbunused
      rw [TreeUsedColors]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨s, hs1, heq⟩) hgamma_unused
  dsimp only at hcontrolled
  rcases hcontrolled with ⟨hpath, hjC, hiSub, hpSub, hbeta', hgamma', hunchanged,
    htransport, hmin'⟩
  refine ⟨TwoColorComponentSwap G phi beta gamma (Sum.inl (T.vertex p)), gamma,
    r, p, hr, hp, hmin', ?_, ?_⟩
  · exact @helper_branch_158 V E inferInstance inferInstance G k e0 phi T hq hlast
      beta j hj hblast hproper hr gamma hgamma hlastincident hbeta_gamma hpath hjC hiSub hpSub
  · exact @helper_branch_265 V E inferInstance inferInstance G k e0 phi T hq hlast
      beta j hj hproper hr gamma hbeta_gamma hgamma_missing hjC hiSub hpSub
end GoldbergSeymour

end
