/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeCaseRepeatedOnPath

/-!
# Tash Tree Controlled Repeated Suffix Contradiction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeControlledRepeatedSuffixContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (i j : Fin (T.length + 1)) (hij : i.val < j.val)
    (hj : j.val < T.length) (hpath : TashTreePathIndex G T ≤ j.val)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex i))
    (hb : beta ∈ MissingColors G phi (T.vertex j))
    (hau : TreeColorUnusedThrough phi T alpha j)
    (hbu : TreeColorUnusedThrough phi T beta j)
    (hlast : alpha ∈
      MissingColors G phi (T.vertex (Fin.last T.length))) : False := by
  classical
  have hproper : IsProperEdgeColoring G phi := hmin.1.1.2.2.2.1
  have hswap := TashTreeControlledInterchange G k e0 phi T hmin i j hij hj
    alpha beta hne ha hb hau hbu
  dsimp only at hswap
  let phi' := TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex j))
  rcases hswap with
    ⟨hcomponentPath, hiComponent, hiSub, hjSub, _hbetaI, halphaJ,
      _hearly, _hlater, hmin'⟩
  have hlastOutside : Sum.inl (T.vertex (Fin.last T.length)) ∉
      TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j)) := by
    intro hlastComponent
    obtain ⟨a, b, path, hpathSimple, hsupport⟩ :=
      TwoColorComponentSpanningPath G phi alpha beta hproper
        (Sum.inl (T.vertex j))
    have support_of_component {x : Sum V E} (hx : x ∈
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j))) :
        x ∈ path.support := by
      change x ∈ {y | y ∈ path.support}
      rw [hsupport]
      exact hx
    have endpoint_of_subsingleton {x : Sum V E} (hx : x ∈
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j)))
        (hxSub : Set.Subsingleton
          ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x)) :
        x = a ∨ x = b := by
      by_contra hend
      push Not at hend
      exact (hpathSimple.isTrail.notMem_support_of_subsingleton_neighborSet
        hend.1 hend.2 hxSub) (support_of_component hx)
    have hjComponent : Sum.inl (T.vertex j) ∈
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j)) := by
      change Sum.inl (T.vertex j) ∈
        ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
          (Sum.inl (T.vertex j))).supp
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hlastSub : Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
          (Sum.inl (T.vertex (Fin.last T.length)))) := by
      let : Fintype
          ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
            (Sum.inl (T.vertex (Fin.last T.length)))) := Fintype.ofFinite _
      have hdegree := MissingColorIncidenceEndpoint G phi alpha beta hne hproper
        (T.vertex (Fin.last T.length)) hlast
      have hcard :
          ((TwoColorIncidenceGraph G phi alpha beta).neighborFinset
            (Sum.inl (T.vertex (Fin.last T.length)))).card ≤ 1 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact hdegree
      intro x hx y hy
      exact (Finset.card_le_one.mp hcard) x
        (by simpa [SimpleGraph.mem_neighborFinset] using hx) y
        (by simpa [SimpleGraph.mem_neighborFinset] using hy)
    have hiEnd := endpoint_of_subsingleton hiComponent hiSub
    have hjEnd := endpoint_of_subsingleton hjComponent hjSub
    have hlastEnd := endpoint_of_subsingleton hlastComponent hlastSub
    have hi_ne_j : (Sum.inl (T.vertex i) : Sum V E) ≠
        Sum.inl (T.vertex j) := by
      intro heq
      have hv : T.vertex i = T.vertex j := by simpa using heq
      exact (Fin.ne_of_lt hij) (T.vertex_injective hv)
    have hi_ne_last : (Sum.inl (T.vertex i) : Sum V E) ≠
        Sum.inl (T.vertex (Fin.last T.length)) := by
      intro heq
      have hv : T.vertex i = T.vertex (Fin.last T.length) := by simpa using heq
      have hindices := congrArg Fin.val (T.vertex_injective hv)
      have hiLast : i.val = T.length := by simpa using hindices
      omega
    have hj_ne_last : (Sum.inl (T.vertex j) : Sum V E) ≠
        Sum.inl (T.vertex (Fin.last T.length)) := by
      intro heq
      have hv : T.vertex j = T.vertex (Fin.last T.length) := by simpa using heq
      have hindices := congrArg Fin.val (T.vertex_injective hv)
      have hjLast : j.val = T.length := by simpa using hindices
      omega
    have endpoint_is_i_or_j {x : Sum V E} (hx : x = a ∨ x = b) :
        x = Sum.inl (T.vertex i) ∨ x = Sum.inl (T.vertex j) := by
      rcases hiEnd with hiA | hiB <;> rcases hjEnd with hjA | hjB
      · exact False.elim (hi_ne_j (hiA.trans hjA.symm))
      · rcases hx with hxA | hxB
        · exact Or.inl (hxA.trans hiA.symm)
        · exact Or.inr (hxB.trans hjB.symm)
      · rcases hx with hxA | hxB
        · exact Or.inr (hxA.trans hjA.symm)
        · exact Or.inl (hxB.trans hiB.symm)
      · exact False.elim (hi_ne_j (hiB.trans hjB.symm))
    rcases endpoint_is_i_or_j hlastEnd with hlastI | hlastJ
    · exact hi_ne_last hlastI.symm
    · exact hj_ne_last hlastJ.symm
  have hlast' : alpha ∈ MissingColors G phi'
      (T.vertex (Fin.last T.length)) := by
    have hmissing := TwoColorComponentSwapMissingBehavior G phi alpha beta hne
      hproper (Sum.inl (T.vertex j))
    dsimp only at hmissing
    exact (hmissing.1 _ hlastOutside) ▸ hlast
  exact TashTreeCaseRepeatedOnPath G k e0 phi' T hmin' hq hbefore
    ⟨alpha, j, hpath, hj, halphaJ, hlast'⟩

end GoldbergSeymour

end
