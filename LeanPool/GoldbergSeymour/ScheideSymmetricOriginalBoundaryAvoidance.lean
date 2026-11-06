/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorReturnIndexBoundaryAvoidance

public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideSymmetricOriginalPathOrder

/-!
# Scheide Symmetric Original Boundary Avoidance

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hxOutside_165.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V :=
      {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let Z : Finset V := X \ U;
    (∀ (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) j ∈ U) →
    (∀ (f : E),
        phi f = some beta →
          ∀ (j : Fin (2 : ℕ)),
            Incident G (C.blockVertex (D.gammaIndex d) j) f → ∀ w ∈ Z, ¬Incident G w f) →
    ∀ (_ _ _ _ _ _ _ : Fin (p.length + (1 : ℕ))),
    let blockIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) |
        ∃ (a : Fin (2 : ℕ)),
          p.getVert (↑r : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) a)};
    ∀ (hblockIndices : blockIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := blockIndices.min' hblockIndices;
    ∀ (jt : Fin (2 : ℕ)),
    p.getVert (↑t : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) jt) →
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) |
        (↑r : ℕ) < (↑t : ℕ) ∧ ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)),
    ∀ w ∈ Z,
    (∀ r ∈ zIndices, (↑r : ℕ) ≤ (↑qz : ℕ)) →
    let qe : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qz : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    ∀ (hqet : (↑qe : ℕ) < (↑t : ℕ)) (f : E),
    Incident G w f →
    phi f = some (↑d : Fin k) ∨ phi f = some beta →
    let qx : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qe : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qe : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    ∀ (x : V),
    p.getVert (↑qx : ℕ) = Sum.inl x →
    Incident G x f →
    (↑qx : ℕ) ≤ (↑t : ℕ) →
    x ∉ X := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d beta v z p X U Z hblockU no_beta_cross i0 i1 i2 i3 i4 qv
      qf blockIndices hblockIndices t jt htNode zIndices hzIndices qz hqzt w hwZ hqzMax qe hqet f
      hwf hfColors qx x hqxNode hxf hqxle hxX
  by_cases hxU : x ∈ U
  · obtain (hfd | hfbeta) := hfColors
    · have hnocross := ScheideDefectiveNoCross G k e0 phi T C D d f hfd
      apply hnocross
      obtain (hx0 | hx1) : x = C.blockVertex (D.gammaIndex d) 0 ∨
          x = C.blockVertex (D.gammaIndex d) 1 := by
        simpa [U] using hxU
      · exact ⟨x, by simp [hx0], hxf, w, hwZ, hwf⟩
      · exact ⟨x, by simp [hx1], hxf, w, hwZ, hwf⟩
    · obtain (hx0 | hx1) : x = C.blockVertex (D.gammaIndex d) 0 ∨
          x = C.blockVertex (D.gammaIndex d) 1 := by
        simpa [U] using hxU
      · exact no_beta_cross f hfbeta 0 (by simpa [hx0] using hxf) w hwZ hwf
      · exact no_beta_cross f hfbeta 1 (by simpa [hx1] using hxf) w hwZ hwf
  · have hxZ : x ∈ Z := by exact Finset.mem_sdiff.mpr ⟨hxX, hxU⟩
    have hqxne : qx.val ≠ t.val := by
      intro heq
      have hxBlock : x = C.blockVertex (D.gammaIndex d) jt := by
        rw [heq, htNode] at hqxNode
        exact Sum.inl.inj hqxNode.symm
      exact hxU (hxBlock ▸ hblockU jt)
    have hqxt : qx.val < t.val := by omega
    have hqxMem : qx ∈ zIndices := by
      simp only [zIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqxt, x, hxZ, hqxNode⟩
    have := hqzMax qx hqxMem
    dsimp [qx, qe] at this
    omega

private theorem helper_hfdelta_489.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    beta ∈ MissingColors G phi v →
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V :=
      {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let Z : Finset V := X \ U;
    v ∈ X →
    ColoredVertexSetClosed G phi X →
    ∀ (_ _ _ _ _ _ _ : Fin (p.length + (1 : ℕ))),
    p.IsPath →
    (∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    let blockIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) |
        ∃ (a : Fin (2 : ℕ)),
          p.getVert (↑r : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) a)};
    ∀ (hblockIndices : blockIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := blockIndices.min' hblockIndices;
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) |
        (↑r : ℕ) < (↑t : ℕ) ∧ ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)),
    ∀ w ∈ Z,
    p.getVert (↑qz : ℕ) = Sum.inl w →
    let qe : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qz : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    ∀ (hqet : (↑qe : ℕ) < (↑t : ℕ)) (f : E),
    Incident G w f →
    phi f = some (↑d : Fin k) ∨ phi f = some beta →
    let qx : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qe : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qe : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    ∀ (x : V),
    p.getVert (↑qx : ℕ) = Sum.inl x →
    Incident G x f →
    x ∉ X →
    phi f = some (↑d : Fin k) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d beta v z p hbeta X U Z hvX hclosed i0 i1 i2 i3 i4 qv qf
      hpath fin_le blockIndices hblockIndices t zIndices hzIndices qz hqzt w hwZ hqw qe hqet f
      hwf hfColors qx x hqxNode hxf hxOutside
  rcases hfColors with hfd | hfbeta
  · exact hfd
  · have hfBoundary : f ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨w, (Finset.mem_sdiff.mp hwZ).1, x, hxOutside, ?_⟩
      obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp hwf
      have hxw : x ≠ w := by
        intro hxw
        have hnodes : p.getVert qx.val = p.getVert qz.val := by
          rw [hqxNode, hxw, hqw]
        have hinds := hpath.getVert_injOn
          (by simpa using fin_le qx) (by simpa using fin_le qz) hnodes
        dsimp [qx, qe] at hinds
        omega
      have hmem : x = w ∨ x = a := by
        simpa [Incident, ha] using hxf
      have hxa : x = a := hmem.resolve_left hxw
      simpa [hxa] using ha
    exact False.elim (hclosed hfBoundary hvX hfbeta hbeta)

private theorem helper_hfEnds_509.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V :=
      {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let Z : Finset V := X \ U;
    ∀ (_ _ _ _ _ _ _ : Fin (p.length + (1 : ℕ))),
    p.IsPath →
    (∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    let blockIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) |
        ∃ (a : Fin (2 : ℕ)),
          p.getVert (↑r : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) a)};
    ∀ (hblockIndices : blockIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := blockIndices.min' hblockIndices;
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) :=
      {r : Fin (p.length + (1 : ℕ)) |
        (↑r : ℕ) < (↑t : ℕ) ∧ ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)) (w : V),
    p.getVert (↑qz : ℕ) = Sum.inl w →
    let qe : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qz : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    ∀ (hqet : (↑qe : ℕ) < (↑t : ℕ)) (f : E),
    Incident G w f →
    let qx : Fin (p.length + (1 : ℕ)) :=
      (⟨(↑qe : ℕ) + (1 : ℕ),
          Decidable.byContradiction fun (a : ¬(↑qe : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
            by omega⟩ :
        Fin (p.length + (1 : ℕ)));
    ∀ (x : V),
    p.getVert (↑qx : ℕ) = Sum.inl x →
    Incident G x f →
    G.ends f = s(w, x) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d beta v z p X U Z i0 i1 i2 i3 i4 qv qf hpath fin_le
      blockIndices hblockIndices t zIndices hzIndices qz hqzt w hqw qe hqet f hwf qx x hqxNode hxf
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp hwf
  have hxw : x ≠ w := by
    intro hxw
    have hnodes : p.getVert qx.val = p.getVert qz.val := by
      rw [hqxNode, hxw, hqw]
    have hinds := hpath.getVert_injOn
      (by simpa using fin_le qx) (by simpa using fin_le qz) hnodes
    dsimp [qx, qe] at hinds
    omega
  have hmem : x = w ∨ x = a := by
    simpa [Incident, ha] using hxf
  have hxa : x = a := hmem.resolve_left hxw
  simpa [hxa] using ha

private theorem helper_havoid_126.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi (↑d : Fin k) beta).Walk (Sum.inl v) (Sum.inl z)),
    beta ∈ MissingColors G phi v →
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V :=
      {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let Z : Finset V := X \ U;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi (↑d : Fin k) beta;
    v ∈ Z →
    v ∈ X →
    ColoredVertexSetClosed G phi X →
    (∀ (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) j ∈ X) →
    (∀ (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) j ∈ U) →
    (∀ (f : E),
        phi f = some beta →
          ∀ (j : Fin (2 : ℕ)),
            Incident G (C.blockVertex (D.gammaIndex d) j) f → ∀ w ∈ Z, ¬Incident G w f) →
    ∀ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + (1 : ℕ))),
    (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) →
    (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) →
    (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) →
    (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) →
    p.getVert (↑i0 : ℕ) = Sum.inr R.f1 ∧
          p.getVert (↑i1 : ℕ) = Sum.inl R.u1 ∧
            p.getVert (↑i2 : ℕ) = Sum.inr h ∧
              p.getVert (↑i3 : ℕ) = Sum.inl R.u2 ∧ p.getVert (↑i4 : ℕ) = Sum.inr R.f2 ∨
        p.getVert (↑i0 : ℕ) = Sum.inr R.f2 ∧
          p.getVert (↑i1 : ℕ) = Sum.inl R.u2 ∧
            p.getVert (↑i2 : ℕ) = Sum.inr h ∧
              p.getVert (↑i3 : ℕ) = Sum.inl R.u1 ∧ p.getVert (↑i4 : ℕ) = Sum.inr R.f1 →
    (↑i4 : ℕ) < (↑qv : ℕ) →
    (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) →
    p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) →
    (∀ (r : Fin (p.length + (1 : ℕ))),
        (↑qv : ℕ) < (↑r : ℕ) →
          ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet T) →
    p.IsPath →
    (∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    ∀ (j : Fin (2 : ℕ)),
    Sum.inl (C.blockVertex (D.gammaIndex d) j) ∉ p.support := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hbeta X U Z H hvZ hvX hclosed hblockX hblockU
      no_beta_cross h i0 i1 i2 i3 i4 qv qf hi01 hi12 hi23 hi34 horient hi4qv hqfv hqfNode hafter
      hpath fin_le j hjSupport
  let blockIndices : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter fun r => ∃ a : Fin 2,
      p.getVert r.val = Sum.inl (C.blockVertex (D.gammaIndex d) a)
  have hblockIndices : blockIndices.Nonempty := by
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hjSupport
    refine ⟨⟨n, by omega⟩, ?_⟩
    simp only [blockIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hn⟩
  let t : Fin (p.length + 1) := blockIndices.min' hblockIndices
  have htMem : t ∈ blockIndices := Finset.min'_mem blockIndices hblockIndices
  obtain ⟨jt, htNode⟩ : ∃ a : Fin 2,
      p.getVert t.val = Sum.inl (C.blockVertex (D.gammaIndex d) a) := by
    simpa only [blockIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      using htMem
  have htMinimal : ∀ r : Fin (p.length + 1), r ∈ blockIndices → t.val ≤ r.val := by
    intro r hr
    exact_mod_cast Finset.min'_le blockIndices r hr
  have htPos : 0 < t.val := by
    by_contra hn
    have ht0 : t.val = 0 := by omega
    have hvBlock : v = C.blockVertex (D.gammaIndex d) jt := by
      rw [ht0, p.getVert_zero] at htNode
      exact Sum.inl.inj htNode
    have hvNotU := (Finset.mem_sdiff.mp hvZ).2
    apply hvNotU
    simpa [hvBlock] using hblockU jt
  let zIndices : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter fun r => r.val < t.val ∧
      ∃ w ∈ Z, p.getVert r.val = Sum.inl w
  have hzIndices : zIndices.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [zIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨htPos, v, hvZ, p.getVert_zero⟩
  let qz : Fin (p.length + 1) := zIndices.max' hzIndices
  have hqzMem : qz ∈ zIndices := Finset.max'_mem zIndices hzIndices
  obtain ⟨hqzt, w, hwZ, hqw⟩ : qz.val < t.val ∧
      ∃ w ∈ Z, p.getVert qz.val = Sum.inl w := by
    simpa only [zIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      using hqzMem
  have hqzMax : ∀ r : Fin (p.length + 1), r ∈ zIndices → r.val ≤ qz.val := by
    intro r hr
    exact_mod_cast Finset.le_max' zIndices r hr
  let qe : Fin (p.length + 1) := ⟨qz.val + 1, by omega⟩
  have hqzAdj := p.adj_getVert_succ (i := qz.val) (by omega : qz.val < p.length)
  have hqzAdj' : H.Adj (Sum.inl w) (p.getVert qe.val) := by
    simpa [H, qe, hqw] using hqzAdj
  have hqet : qe.val < t.val := by
    have hne : qe.val ≠ t.val := by
      intro heq
      have hadj : H.Adj (Sum.inl w)
          (Sum.inl (C.blockVertex (D.gammaIndex d) jt)) := by
        simpa [heq, htNode] using hqzAdj'
      simp [H, TwoColorIncidenceGraph] at hadj
    change qz.val + 1 ≠ t.val at hne
    change qz.val + 1 < t.val
    omega
  obtain ⟨f, hqeNode, hwf, hfColors⟩ : ∃ f : E,
      p.getVert qe.val = Sum.inr f ∧ Incident G w f ∧
        (phi f = some d.1 ∨ phi f = some beta) := by
    cases hn : p.getVert qe.val with
    | inl a =>
        exfalso
        have hadj : H.Adj (Sum.inl w) (Sum.inl a) := by
          simpa [hn] using hqzAdj'
        simp [H, TwoColorIncidenceGraph] at hadj
    | inr e =>
        refine ⟨e, rfl, ?_⟩
        rw [hn] at hqzAdj'
        simpa [H, TwoColorIncidenceGraph] using hqzAdj'
  let qx : Fin (p.length + 1) := ⟨qe.val + 1, by omega⟩
  have hqeAdj := p.adj_getVert_succ (i := qe.val) (by omega : qe.val < p.length)
  have hqeAdj' : H.Adj (Sum.inr f) (p.getVert qx.val) := by
    simpa [H, qx, hqeNode] using hqeAdj
  obtain ⟨x, hqxNode, hxf⟩ : ∃ x : V,
      p.getVert qx.val = Sum.inl x ∧ Incident G x f := by
    cases hn : p.getVert qx.val with
    | inl a =>
        refine ⟨a, rfl, ?_⟩
        have hadj : H.Adj (Sum.inr f) (Sum.inl a) := by
          simpa [hn] using hqeAdj'
        have hpair : Incident G a f ∧
            (phi f = some d.1 ∨ phi f = some beta) := by
          simpa [H, TwoColorIncidenceGraph] using hadj
        exact hpair.1
    | inr e =>
        exfalso
        have hadj : H.Adj (Sum.inr f) (Sum.inr e) := by
          simpa [hn] using hqeAdj'
        simp [H, TwoColorIncidenceGraph] at hadj
  have hqxle : qx.val ≤ t.val := by dsimp [qx]; omega
  have hxOutside := @helper_hxOutside_165 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d beta v z p hblockU no_beta_cross i0 i1 i2 i3 i4 qv qf
      hblockIndices jt htNode hzIndices hqzt w hwZ hqzMax hqet f hwf hfColors x hqxNode hxf hqxle
  have hfdelta := @helper_hfdelta_489 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 phi T C D d beta v z p hbeta hvX hclosed i0 i1 i2 i3 i4 qv qf hpath fin_le hblockIndices
      hzIndices hqzt w hwZ hqw hqet f hwf hfColors x hqxNode hxf hxOutside
  have hfEnds := @helper_hfEnds_509 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d beta v z p i0 i1 i2 i3 i4 qv qf hpath fin_le hblockIndices hzIndices hqzt w hqw
      hqet f hwf x hqxNode hxf
  have hfBoundaryZ : f ∈ BoundaryColorEdges G phi Z d.1 := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    refine ⟨?_, hfdelta⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwZ, x, fun hxZ => hxOutside (Finset.mem_sdiff.mp hxZ).1, hfEnds⟩
  have hfThree : f = D.f0 d ∨ f = R.f1 ∨ f = R.f2 := by
    apply (R.exact_three f).mp
    exact ⟨by simpa [X, U, Z] using hfBoundaryZ,
      ⟨x, by simpa [X] using hxOutside, hxf⟩⟩
  have hblockOutsideNe : ∀ (u : V), u ∉ X → ∀ a : Fin 2,
      u ≠ C.blockVertex (D.gammaIndex d) a := by
    intro u hu a hua
    exact hu (hua ▸ hblockX a)
  have blockNotZ : C.blockVertex (D.gammaIndex d) jt ∉ Z := by
    intro member
    exact (Finset.mem_sdiff.mp member).2 (hblockU jt)
  have maximalReturn (index : Fin (p.length + 1)) (before : index.val < t.val)
      (member : ∃ vertex ∈ Z, p.getVert index.val = Sum.inl vertex) : index.val ≤ qz.val :=
    hqzMax index (Finset.mem_filter.mpr ⟨Finset.mem_univ _, before, member⟩)
  have wNeOutside (outside : V) (missing : outside ∉ X) : w ≠ outside := by
    intro same
    apply missing
    simpa only [same] using (Finset.mem_sdiff.mp hwZ).1
  rcases hfThree with hf0 | hf1 | hf2
  · have hqeqf : qe.val = qf.val := by
      have hvEq : p.getVert qe.val = p.getVert qf.val := by
        rw [hqeNode, hf0, hqfNode]
      exact hpath.getVert_injOn
        (by simpa using fin_le qe) (by simpa using fin_le qf) hvEq
    have hqvt : qv.val < t.val := by
      dsimp [qe] at hqeqf
      omega
    exact (hafter t hqvt (C.blockVertex (D.gammaIndex d) jt) htNode)
      (hblockX jt)
  · rcases horient with first | second
    · apply TwoColorReturnIndexBoundaryAvoidance p hpath hi01 hi12 hi23 hi34 rfl hqet htNode
        first.1 first.2.1 first.2.2.1 first.2.2.2.1 first.2.2.2.2
        (hblockOutsideNe _ R.u1_outside jt) (hblockOutsideNe _ R.u2_outside jt)
        R.f2_ends (by simpa only [X, U, Z] using R.v2_in_remainder) blockNotZ maximalReturn
      simpa only [hf1] using hqeNode
    · apply ReturnIndexAvoidsOutsideEdge (query := qe) p hpath rfl hi34
        second.2.2.2.2 second.2.2.2.1 hqw (wNeOutside _ R.u1_outside)
      simpa only [hf1] using hqeNode
  · rcases horient with first | second
    · apply ReturnIndexAvoidsOutsideEdge (query := qe) p hpath rfl hi34
        first.2.2.2.2 first.2.2.2.1 hqw (wNeOutside _ R.u2_outside)
      simpa only [hf2] using hqeNode
    · apply TwoColorReturnIndexBoundaryAvoidance p hpath hi01 hi12 hi23 hi34 rfl hqet htNode
        second.1 second.2.1 second.2.2.1 second.2.2.2.1 second.2.2.2.2
        (hblockOutsideNe _ R.u2_outside jt) (hblockOutsideNe _ R.u1_outside jt)
        R.f1_ends (by simpa only [X, U, Z] using R.v1_in_remainder) blockNotZ maximalReturn
      simpa only [hf2] using hqeNode
theorem ScheideSymmetricOriginalBoundaryAvoidance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi d.1 beta).Walk (Sum.inl v) (Sum.inl z)),
    v ∈
        TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} →
    beta ∈ MissingColors G phi v →
    beta ∈ TreeFreeColors phi T →
    beta ≠ C.gamma (D.gammaIndex d) →
    ScheideDefectiveChainPath T phi d.1 beta v z p →
    (∀ j : Fin 2, Sum.inl (C.blockVertex (D.gammaIndex d) j) ∉ p.support) ∧
      ∀ f : E,
        f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) d.1 →
          ∀ j : Fin 2, ¬Incident G (C.blockVertex (D.gammaIndex d) j) f := by
  classical
  intro beta v z p hv hbeta hfree hbetaGamma hp
  let X := TreeSequenceVertexSet T
  let U := ({C.blockVertex (D.gammaIndex d) 0,
    C.blockVertex (D.gammaIndex d) 1} : Finset V)
  let Z := X \ U
  let H := TwoColorIncidenceGraph G phi d.1 beta
  have hvZ : v ∈ Z := by simpa [X, U, Z] using hv
  have hvX : v ∈ X := (Finset.mem_sdiff.mp hvZ).1
  have hglobal : GlobalMaximumTriple G k e0 phi T := C.globally_maximum
  have htriple : KTriple G k e0 phi := hglobal.1
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := by
    change ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)
    exact (ScheideGlobalMaximumOrder G k e0 phi T hglobal).2.2.2.2
  have hblockX : ∀ j : Fin 2,
      C.blockVertex (D.gammaIndex d) j ∈ X := by
    intro j
    change C.blockVertex (D.gammaIndex d) j ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) j]
    simp [TreeSequenceVertexSet]
  have hblockU : ∀ j : Fin 2,
      C.blockVertex (D.gammaIndex d) j ∈ U := by
    intro j
    have hjval : j.val = 0 ∨ j.val = 1 := by omega
    rcases hjval with hjval | hjval
    · have hj : j = (0 : Fin 2) := Fin.ext hjval
      subst j
      simp [U]
    · have hj : j = (1 : Fin 2) := Fin.ext hjval
      subst j
      simp [U]
  obtain ⟨b, hbColor, hbEnds⟩ :=
    ScheideStructuralInternalPair G k e0 phi T C (D.gammaIndex d) beta
      hbetaGamma ⟨v, hv, hbeta⟩
  have hbIncident : ∀ j : Fin 2,
      Incident G (C.blockVertex (D.gammaIndex d) j) b := by
    intro j
    have hjval : j.val = 0 ∨ j.val = 1 := by omega
    rcases hjval with hjval | hjval
    · have hj : j = (0 : Fin 2) := Fin.ext hjval
      subst j
      simp [Incident, hbEnds]
    · have hj : j = (1 : Fin 2) := Fin.ext hjval
      subst j
      simp [Incident, hbEnds]
  have beta_incident_unique : ∀ (j : Fin 2) (f : E),
      Incident G (C.blockVertex (D.gammaIndex d) j) f →
      phi f = some beta → f = b := by
    intro j f hjf hfColor
    by_contra hfb
    exact (hproper hfb
      ⟨C.blockVertex (D.gammaIndex d) j, hjf, hbIncident j⟩
      hfColor) hbColor
  have no_beta_cross : ∀ (f : E), phi f = some beta →
      ∀ j : Fin 2, Incident G (C.blockVertex (D.gammaIndex d) j) f →
      ∀ w ∈ Z, ¬ Incident G w f := by
    intro f hfColor j hjf w hwZ hwf
    have hfb : f = b := beta_incident_unique j f hjf hfColor
    subst f
    have hwU : w ∈ U := by
      change w ∈ ({C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1} : Finset V)
      simpa [Incident, hbEnds] using hwf
    exact (Finset.mem_sdiff.mp hwZ).2 hwU
  obtain ⟨h, i0, i1, i2, i3, i4, qv, qf,
      hhColor, hhEnds, hi01, hi12, hi23, hi34, horient,
      hi4qv, hqfv, hqvNode, hqfNode, hafter⟩ :=
    ScheideSymmetricOriginalPathOrder G k e0 phi T C D d R
      beta v z p hv hbeta hfree hbetaGamma hp
  have hpath : p.IsPath := hp.2.1
  have fin_le (r : Fin (p.length + 1)) : r.val ≤ p.length := by
    have := r.isLt
    omega
  have havoid := @helper_havoid_126 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R beta v z p hbeta hvZ hvX hclosed hblockX hblockU no_beta_cross h i0 i1 i2 i3
      i4 qv qf hi01 hi12 hi23 hi34 horient hi4qv hqfv hqfNode hafter hpath fin_le
  refine ⟨havoid, ?_⟩
  intro f hfBoundary j hjf
  have hfSupport : Sum.inr f ∈ p.support :=
    ((ScheideDefectiveChainBoundaryEdges G k e0 phi T hglobal
      d.1 beta d.2 hfree v hvX hbeta z p hp) f).mp hfBoundary |>.2
  have hfColor : phi f = some d.1 := (Finset.mem_filter.mp hfBoundary).2
  have hadj : H.Adj
      (Sum.inl (C.blockVertex (D.gammaIndex d) j)) (Sum.inr f) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (C.blockVertex (D.gammaIndex d) j) f ∧
          (phi f = some d.1 ∨ phi f = some beta) from
        ⟨hjf, Or.inl hfColor⟩)
  have hfComponent : H.connectedComponentMk (Sum.inr f) =
      H.connectedComponentMk (Sum.inl v) := by
    change Sum.inr f ∈ TwoColorComponent G phi d.1 beta (Sum.inl v)
    rw [← hp.2.2.2]
    exact hfSupport
  have hjComponent : H.connectedComponentMk
      (Sum.inl (C.blockVertex (D.gammaIndex d) j)) =
      H.connectedComponentMk (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
      hfComponent
  apply havoid j
  have hjComp : Sum.inl (C.blockVertex (D.gammaIndex d) j) ∈
      TwoColorComponent G phi d.1 beta (Sum.inl v) := hjComponent
  rw [← hp.2.2.2] at hjComp
  exact hjComp

end GoldbergSeymour

end
