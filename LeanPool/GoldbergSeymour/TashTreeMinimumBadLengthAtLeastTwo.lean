/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair

/-!
# Tash Tree Minimum Bad Length At Least Two

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeMinimumBadLengthAtLeastTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T) :
    2 ≤ T.length := by
  classical
  by_contra htwo
  have hpositive : 1 ≤ T.length := T.positive
  have hlength : T.length = 1 := by omega
  have hbad : TashTreeBadPair G k e0 phi T := hmin.1
  have htriple : KTriple G k e0 phi := hbad.1
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := htriple.2.2.2.2
  let i0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (T.length + 1) := ⟨1, by omega⟩
  let y0 : V := T.vertex i0
  let y1 : V := T.vertex i1
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hy01 : y0 ≠ y1 := by
    intro h
    exact hi01 (T.vertex_injective h)
  have hy0mem : y0 ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i0, rfl⟩
  have hy1mem : y1 ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i1, rfl⟩
  have hvertex_cases : ∀ {v : V}, v ∈ TreeSequenceVertexSet T → v = y0 ∨ v = y1 := by
    intro v hv
    rw [TreeSequenceVertexSet] at hv
    rcases Finset.mem_image.mp hv with ⟨i, -, rfl⟩
    by_cases hi : i.val = 0
    · left
      apply congrArg T.vertex
      apply Fin.ext
      simpa [i0] using hi
    · right
      apply congrArg T.vertex
      apply Fin.ext
      change i.val = 1
      omega
  have hnot : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := hbad.2.2
  unfold ColoredVertexSetElementary at hnot
  have hpairs : ∃ u, u ∈ TreeSequenceVertexSet T ∧ ∃ v, v ∈ TreeSequenceVertexSet T ∧
      u ≠ v ∧ ¬ Disjoint (MissingColors G phi u) (MissingColors G phi v) := by
    by_contra hnone
    apply hnot
    intro u hu v hv huv
    by_contra hdis
    exact hnone ⟨u, hu, v, hv, huv, hdis⟩
  rcases hpairs with ⟨u, hu, v, hv, huv, hdis⟩
  rw [Finset.disjoint_left] at hdis
  push Not at hdis
  rcases hdis with ⟨eta, hetau, hetav⟩
  have heta0 : eta ∈ MissingColors G phi y0 := by
    rcases hvertex_cases hu with rfl | rfl
    · exact hetau
    · rcases hvertex_cases hv with hv0 | hv1
      · simpa [hv0] using hetav
      · exact False.elim (huv (hv1.symm))
  have heta1 : eta ∈ MissingColors G phi y1 := by
    rcases hvertex_cases hu with hu0 | hu1
    · rcases hvertex_cases hv with hv0 | hv1
      · exact False.elim (huv (hu0.trans hv0.symm))
      · simpa [hv1] using hetav
    · simpa [hu1] using hetau
  have hends : G.ends e0 = s(y1, y0) := by
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    have hizero : i = 0 := Fin.eq_zero i
    rw [← T.first_edge, hi, hizero]
    congr 1
  have endpoint_of_incident : ∀ {v : V}, Incident G v e0 → v = y1 ∨ v = y0 := by
    intro v hv
    simpa only [Incident, hends, Sym2.mem_iff] using hv
  have no_eta_of_incident {v : V} (hv : v = y0 ∨ v = y1) {e : E}
      (hve : Incident G v e) : phi e ≠ some eta := by
    intro he
    have hpresent : eta ∈ PresentColors G phi v := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hve, he⟩
    rcases hv with rfl | rfl
    · have : eta ∉ PresentColors G phi y0 := by
        simpa [MissingColors] using heta0
      exact this hpresent
    · have : eta ∉ PresentColors G phi y1 := by
        simpa [MissingColors] using heta1
      exact this hpresent
  let psi : PartialEdgeColoring E k := fun e => if e = e0 then some eta else phi e
  have hfull : IsFullEdgeColoring psi := by
    intro e
    by_cases he : e = e0
    · exact ⟨eta, by simp [psi, he]⟩
    · obtain ⟨c, hc⟩ := hone.2 e he
      exact ⟨c, by simpa [psi, he] using hc⟩
  have hproperPsi : IsProperEdgeColoring G psi := by
    intro e f c hef hadj hec
    rcases hadj with ⟨v, hve, hvf⟩
    by_cases he0 : e = e0
    · subst e
      have hf0 : f ≠ e0 := by
        intro h
        exact hef h.symm
      have hetac : eta = c := by simpa [psi] using hec
      have hvends := endpoint_of_incident hve
      have hnocolor : phi f ≠ some eta :=
        no_eta_of_incident (hvends.elim Or.inr Or.inl) hvf
      rw [← hetac]
      simpa [psi, hf0] using hnocolor
    · have hphie : phi e = some c := by simpa [psi, he0] using hec
      by_cases hf0 : f = e0
      · subst f
        have hvends := endpoint_of_incident hvf
        have hnocolor : phi e ≠ some eta :=
          no_eta_of_incident (hvends.elim Or.inr Or.inl) hve
        have hcne : c ≠ eta := by
          intro h
          subst c
          exact hnocolor hphie
        simp only [psi, ite_eq_left]
        intro h
        exact hcne (Option.some.inj h.symm)
      · simpa [psi, hf0] using hproper hef ⟨v, hve, hvf⟩ hphie
  have hkcoloring : HasKEdgeColoring G k := ⟨psi, hproperPsi, hfull⟩
  have hchromatic : ChromaticIndex G ≤ k := by
    exact Nat.find_min' (ColoringExists G) hkcoloring
  rw [htriple.2.1] at hchromatic
  omega

end GoldbergSeymour

end
