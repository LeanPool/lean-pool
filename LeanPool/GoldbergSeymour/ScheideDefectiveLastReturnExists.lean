/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveReturnData
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase

/-!
# Scheide Defective Last Return Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hv1ExitProp_194.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let p : (TwoColorIncidenceGraph G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)).Walk (Sum.inl
        (D.v0 d)) (Sum.inl (D.replacementZ d)) := D.replacementPath d; ScheideDefectiveChainPath T
        phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (D.v0 d) (D.replacementZ d) (D.replacementPath
        d) →
    let indices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ (x : V), p.getVert (↑r : ℕ) = Sum.inl x ∧ x ∈ X};
    ∀ (hindices : indices.Nonempty),
    let i : Fin (p.length + (1 : ℕ)) := indices.max' hindices;
    ∀ (v1 : V), p.getVert (↑i : ℕ) = Sum.inl v1 → v1 ∈ X → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑i : ℕ) < (↑r : ℕ) →
    ∀ (x : V), p.getVert (↑r : ℕ) = Sum.inl x → x ∉ X) → ScheideExitVertex T phi v1 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X p hp indices hindices i v1 hiv1 hv1X hafter
  let gamma := C.gamma (D.gammaIndex d)
  let swapHom : TwoColorIncidenceGraph G phi gamma d.1 →g
      TwoColorIncidenceGraph G phi d.1 gamma :=
    ⟨id, by
      intro x y h
      simpa [TwoColorIncidenceGraph, or_comm] using h⟩
  let q := p.map swapHom
  have hcomponentSwap : TwoColorComponent G phi gamma d.1 (Sum.inl (D.v0 d)) =
      TwoColorComponent G phi d.1 gamma (Sum.inl (D.v0 d)) := by
    change ((TwoColorIncidenceGraph G phi gamma d.1).connectedComponentMk
        (Sum.inl (D.v0 d)) : Set (Sum V E)) =
      ((TwoColorIncidenceGraph G phi d.1 gamma).connectedComponentMk
        (Sum.inl (D.v0 d)) : Set (Sum V E))
    ext x
    change x ∈ ((TwoColorIncidenceGraph G phi gamma d.1).connectedComponentMk
        (Sum.inl (D.v0 d))).supp ↔
      x ∈ ((TwoColorIncidenceGraph G phi d.1 gamma).connectedComponentMk
        (Sum.inl (D.v0 d))).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq,
      SimpleGraph.ConnectedComponent.eq]
    constructor
    · intro h
      simpa [swapHom] using h.map swapHom
    · intro h
      let reverseHom : TwoColorIncidenceGraph G phi d.1 gamma →g
          TwoColorIncidenceGraph G phi gamma d.1 :=
        ⟨id, by
          intro x y h
          simpa [TwoColorIncidenceGraph, or_comm] using h⟩
      simpa [reverseHom] using h.map reverseHom
  have hq : ScheideDefectiveChainPath T phi d.1 gamma
      (D.v0 d) (D.replacementZ d) q := by
    change D.v0 d ∈ X ∧ q.IsPath ∧
      D.replacementZ d ∉ X ∧
      {x | x ∈ q.support} =
        TwoColorComponent G phi d.1 gamma (Sum.inl (D.v0 d))
    refine ⟨hp.1, (q.isPath_def).2 ?_, hp.2.2.1, ?_⟩
    · simpa [q, p, swapHom] using (p.isPath_def.mp hp.2.1)
    · have hsupp : q.support = p.support := by simp [q, p, swapHom]
      rw [hsupp, ← hcomponentSwap]
      exact hp.2.2.2
  let iq : Fin (q.length + 1) := ⟨i.val, by simpa [q, p] using i.isLt⟩
  refine ⟨D.v0 d, gamma, d.1, hp.1, D.gamma_missing_at_v0 d, d.2,
    D.replacementZ d, q, hq, iq, ?_, hv1X, ?_⟩
  · simpa [iq, q, p, swapHom] using hiv1
  · intro r hr x hrx
    let rp : Fin (p.length + 1) := ⟨r.val, by simpa [q, p] using r.isLt⟩
    apply hafter rp
    · simpa [iq, rp] using hr
    · simpa [rp, q, p, swapHom] using hrx

private theorem helper_hf1Ends_230.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let p : (TwoColorIncidenceGraph G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)).Walk (Sum.inl
        (D.v0 d)) (Sum.inl (D.replacementZ d)) := D.replacementPath d; ScheideDefectiveChainPath T
        phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (D.v0 d) (D.replacementZ d) (D.replacementPath
        d) →
    ∀ (_ : ℕ),
    let indices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ (x : V), p.getVert (↑r : ℕ) = Sum.inl x ∧ x ∈ X};
    ∀ (hindices : indices.Nonempty),
    let i : Fin (p.length + (1 : ℕ)) := indices.max' hindices;
    ∀ (v1 : V), p.getVert (↑i : ℕ) = Sum.inl v1 →
    ∀ (f1 : E), (↑i : ℕ) + (1 : ℕ) < p.length →
    ∀ (u1 : V), p.getVert ((↑i : ℕ) + (2 : ℕ)) = Sum.inl u1 → Incident G v1 f1 → Incident G u1 f1
        → G.ends f1 = s(v1, u1) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X p hp iw indices hindices i v1 hiv1 f1 hi2Length u1 hu1
      hv1Incident hu1Incident
  let a := (Quot.out (G.ends f1)).1
  let b := (Quot.out (G.ends f1)).2
  have hab : s(a, b) = G.ends f1 := Quot.out_eq _
  have hva : v1 = a ∨ v1 = b := by
    apply Sym2.mem_iff.mp
    rw [hab]
    exact hv1Incident
  have hua : u1 = a ∨ u1 = b := by
    apply Sym2.mem_iff.mp
    rw [hab]
    exact hu1Incident
  have hvu : v1 ≠ u1 := by
    intro hvu
    have hidx := hp.2.1.getVert_injOn
      (show i.val ≤ p.length by omega) (show i.val + 2 ≤ p.length by omega)
      (hiv1.trans (hvu ▸ hu1).symm)
    omega
  rw [← hab, Sym2.eq_iff]
  rcases hva with hva | hva
  · rcases hua with hua | hua
    · exact (hvu (hva.trans hua.symm)).elim
    · exact Or.inl ⟨hva.symm, hua.symm⟩
  · rcases hua with hua | hua
    · exact Or.inr ⟨hua.symm, hva.symm⟩
    · exact (hvu (hva.trans hua.symm)).elim

theorem ScheideDefectiveLastReturnExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (w : V) (hw : w ∈ TreeSequenceVertexSet T)
    (hcomponent : Sum.inl w ∈ TwoColorComponent G phi
      (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d)))
    (hne : w ≠ D.v0 d) :
    Nonempty (ScheideDefectiveReturnData G k e0 phi T C D d) := by
  classical
  let X := TreeSequenceVertexSet T
  let p := D.replacementPath d
  have hp := D.replacement_path_full d
  have hwSupport : Sum.inl w ∈ p.support := by
    change Sum.inl w ∈ {x | x ∈ p.support}
    rw [hp.2.2.2]
    exact hcomponent
  obtain ⟨iw, hiw, hiwLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwSupport
  let indices : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter (fun r => ∃ x : V, p.getVert r.val = Sum.inl x ∧ x ∈ X)
  have hindices : indices.Nonempty := by
    refine ⟨⟨iw, by omega⟩, ?_⟩
    simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hiw, hw⟩
  let i : Fin (p.length + 1) := indices.max' hindices
  have hi : i ∈ indices := Finset.max'_mem indices hindices
  obtain ⟨v1, hiv1, hv1X⟩ := (Finset.mem_filter.mp hi).2
  have hiwMem : (⟨iw, by omega⟩ : Fin (p.length + 1)) ∈ indices := by
    simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hiw, hw⟩
  have hiwPos : 0 < iw := by
    by_contra hn
    have hiwZero : iw = 0 := by omega
    have hwv0 : w = D.v0 d := by
      apply Sum.inl.inj
      calc
        Sum.inl w = p.getVert iw := hiw.symm
        _ = p.getVert 0 := by rw [hiwZero]
        _ = Sum.inl (D.v0 d) := p.getVert_zero
    exact hne hwv0
  have hiPos : 0 < i.val := by
    have hle := Finset.le_max' indices (⟨iw, by omega⟩ : Fin (p.length + 1)) hiwMem
    have hleVal : iw ≤ i.val := Fin.le_iff_val_le_val.mp hle
    omega
  have hiLength : i.val < p.length := by
    by_contra hn
    have heq : i.val = p.length := by omega
    have hend : p.getVert i.val = Sum.inl (D.replacementZ d) := by
      rw [heq, p.getVert_length]
    have hvz : v1 = D.replacementZ d := Sum.inl.inj (hiv1.symm.trans hend)
    exact hp.2.2.1 (hvz ▸ hv1X)
  have hi1 : i.val + 1 < p.length + 1 := by omega
  have hf1Exists : ∃ f1 : E, p.getVert (i.val + 1) = Sum.inr f1 := by
    cases hnode : p.getVert (i.val + 1) with
    | inl x =>
        have hadj := p.adj_getVert_succ hiLength
        rw [hiv1, hnode] at hadj
        simp [TwoColorIncidenceGraph] at hadj
    | inr f1 => exact ⟨f1, rfl⟩
  obtain ⟨f1, hf1⟩ := hf1Exists
  have hi1NotEnd : i.val + 1 ≠ p.length := by
    intro heq
    have hend := p.getVert_length
    rw [heq] at hf1
    exact Sum.inr_ne_inl (hf1.symm.trans hend)
  have hi2Length : i.val + 1 < p.length := by omega
  have hu1Exists : ∃ u1 : V, p.getVert (i.val + 2) = Sum.inl u1 := by
    cases hnode : p.getVert (i.val + 2) with
    | inr e =>
        have hadj := p.adj_getVert_succ hi2Length
        rw [hf1, hnode] at hadj
        simp [TwoColorIncidenceGraph] at hadj
    | inl u1 => exact ⟨u1, rfl⟩
  obtain ⟨u1, hu1⟩ := hu1Exists
  let edgeIndex : Fin (p.length + 1) := ⟨i.val + 1, hi1⟩
  let outsideIndex : Fin (p.length + 1) := ⟨i.val + 2, by omega⟩
  have hafter : ∀ r : Fin (p.length + 1), i.val < r.val →
      ∀ x : V, p.getVert r.val = Sum.inl x → x ∉ X := by
    intro r hir x hxr hx
    have hr : r ∈ indices := by
      simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxr, hx⟩
    have hle := Finset.le_max' indices r hr
    have hleVal : r.val ≤ i.val := Fin.le_iff_val_le_val.mp hle
    omega
  have hu1Outside : u1 ∉ X := by
    exact hafter outsideIndex (by simp [outsideIndex]) u1 (by simpa [outsideIndex] using hu1)
  have hv1Ne : v1 ≠ D.v0 d := by
    intro heq
    have hidx := hp.2.1.getVert_injOn
      (show i.val ≤ p.length by omega) (show 0 ≤ p.length by omega)
      (show p.getVert i.val = p.getVert 0 by simpa [heq] using hiv1)
    omega
  have hv1f1Adj := p.adj_getVert_succ hiLength
  have hf1u1Adj := p.adj_getVert_succ hi2Length
  have hv1Incident : Incident G v1 f1 := by
    rw [hiv1, hf1] at hv1f1Adj
    have htemp : Incident G v1 f1 ∧
        (phi f1 = some (C.gamma (D.gammaIndex d)) ∨ phi f1 = some d.1) := by
      simpa [TwoColorIncidenceGraph] using hv1f1Adj
    exact htemp.1
  have hu1Incident : Incident G u1 f1 := by
    rw [hf1, hu1] at hf1u1Adj
    have htemp : Incident G u1 f1 ∧
        (phi f1 = some (C.gamma (D.gammaIndex d)) ∨ phi f1 = some d.1) := by
      simpa [TwoColorIncidenceGraph] using hf1u1Adj
    exact htemp.1
  have hf1Ends := @helper_hf1Ends_230 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 phi T C D d hp iw hindices v1 hiv1 f1 hi2Length u1 hu1 hv1Incident hu1Incident
  have hstructure := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have helementary : ColoredVertexSetElementary G phi X := hstructure.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := hstructure.2.2.2.2
  have hf1Boundary : f1 ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v1, hv1X, u1, hu1Outside, hf1Ends⟩
  have hf1Color : phi f1 = some d.1 := by
    have hcolors : phi f1 = some (C.gamma (D.gammaIndex d)) ∨ phi f1 = some d.1 := by
      rw [hiv1, hf1] at hv1f1Adj
      have htemp : Incident G v1 f1 ∧
          (phi f1 = some (C.gamma (D.gammaIndex d)) ∨ phi f1 = some d.1) := by
        simpa [TwoColorIncidenceGraph] using hv1f1Adj
      exact htemp.2
    rcases hcolors with hgamma | hdelta
    · exact (hclosed hf1Boundary hp.1 hgamma (D.gamma_missing_at_v0 d)).elim
    · exact hdelta
  have hv1ExitProp := @helper_hv1ExitProp_194 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d hp hindices v1 hiv1 hv1X hafter
  have hv1Exit : v1 ∈ ScheideExitVertices T phi := by
    simp only [ScheideExitVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hv1ExitProp
  have hv1Base : v1 ∈ Finset.univ.image C.y :=
    ScheideStructuralExitsInBase G k e0 phi T C hv1Exit
  obtain ⟨j, hjMissing, hjUnique⟩ := C.exit_exactly_one v1 hv1Exit
  have hjNe : j ≠ D.gammaIndex d := by
    intro heq
    have hdisjoint := helementary hv1X hp.1 hv1Ne
    exact (Finset.disjoint_left.mp hdisjoint) hjMissing
        (by simpa [heq] using D.gamma_missing_at_v0 d)
  have hy0X : C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈ X := by
    let y0Index : Fin C.p := ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    have hwitness : C.y y0Index ∈ TreeSequenceVertexSet T :=
      (@Finset.mem_image (Fin (T.length + 1)) V (Classical.decEq V)).mpr
        ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, C.base_vertex_position y0Index⟩
    simpa only [X, y0Index] using hwitness
  have hdeltaBoundaryExists : (BoundaryColorEdges G phi X d.1).Nonempty := by
    have hdcard : 2 ≤ (BoundaryColorEdges G phi X d.1).card := by
      have hmem : d.1 ∈ DefectiveColors G phi X := by simpa only [X] using d.2
      have hddef : DefectiveColor G phi X d.1 := by
        simpa only [DefectiveColors, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
      exact hddef
    exact Finset.card_pos.mp (by omega)
  obtain ⟨fd, hfd⟩ := hdeltaBoundaryExists
  have hfdBoundary : fd ∈ BoundaryEdges G X :=
    (Finset.mem_filter.mp hfd).1
  have hfdColor : phi fd = some d.1 :=
    (Finset.mem_filter.mp hfd).2
  have hdeltaNotMissing : ∀ v ∈ X, d.1 ∉ MissingColors G phi v := by
    intro v hv
    exact hclosed hfdBoundary hv hfdColor
  have halphaDelta : D.alpha0 ≠ d.1 := by
    intro heq
    exact hdeltaNotMissing _ hy0X (heq ▸ D.alpha0_missing_at_y0)
  have hgammaDelta : C.gamma (D.gammaIndex d) ≠ d.1 := by
    intro heq
    exact hdeltaNotMissing _ hp.1 (heq ▸ D.gamma_missing_at_v0 d)
  have hgammaJDelta : C.gamma j ≠ d.1 := by
    intro heq
    exact hdeltaNotMissing _ hv1X (heq ▸ hjMissing)
  have hgammaDistinct : C.gamma (D.gammaIndex d) ≠ C.gamma j := by
    intro heq
    exact hjNe (C.gamma_injective heq).symm
  refine ⟨{
    pathIndex := i
    edgeIndex := edgeIndex
    outsideIndex := outsideIndex
    v1 := v1
    f1 := f1
    u1 := u1
    blockIndex := j
    v1_at_index := by simpa [p] using hiv1
    f1_at_index := by simpa [p, edgeIndex] using hf1
    u1_at_index := by simpa [p, outsideIndex] using hu1
    successive_indices := by simp [edgeIndex, outsideIndex]
    after_last_tree_vertex := by simpa [p, X] using hafter
    v1_mem := by simpa [X] using hv1X
    v1_ne_v0 := hv1Ne
    u1_outside := by simpa [X] using hu1Outside
    v1_is_exit := hv1Exit
    v1_in_base := hv1Base
    f1_color := hf1Color
    f1_ends := hf1Ends
    gammaJ_missing := hjMissing
    blockIndex_ne := hjNe
    alpha0_ne_gamma := D.alpha0_not_block (D.gammaIndex d)
    alpha0_ne_gammaJ := D.alpha0_not_block j
    alpha0_ne_delta := halphaDelta
    gamma_ne_gammaJ := hgammaDistinct
    gamma_ne_delta := hgammaDelta
    gammaJ_ne_delta := hgammaJDelta
  }⟩

end GoldbergSeymour

end
