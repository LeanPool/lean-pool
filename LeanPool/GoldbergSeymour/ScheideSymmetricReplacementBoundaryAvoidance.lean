/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveChainBoundaryEdges
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReplacementInternalMissing
public import LeanPool.GoldbergSeymour.ScheideReplacementPairFixed
public import LeanPool.GoldbergSeymour.ScheideSymmetricReplacementBoundaryConfiguration
public import LeanPool.GoldbergSeymour.ScheideSymmetricReplacementPathOrder

/-!
# Scheide Symmetric Replacement Boundary Avoidance

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperHavoidU249Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (beta : Fin k) (v z : V) (p : (TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)), beta ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v
        →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet R.replacementTree;
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; v ∈ Z → X = Z ∪ U → Z
        ⊆ X → v ∈ X → ColoredVertexSetClosed G phiD X → (
    ∀ {w : V}, w ∈ U → w = R.u1 ∨ w = R.u2) → (
    ∀ (f : E), phiD f = some gamma → Incident G R.u1 f ∨ Incident G R.u2 f →
    ∀ w ∈ Z, ¬Incident G w f) → (
    ∀ (f : E), phiD f = some beta →
    ∀ u ∈ U, Incident G u f →
    ∀ w ∈ Z, ¬Incident G w f) →
    ∀ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + (1 : ℕ))), (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) →
        (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) → (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) → (↑i4 : ℕ) = (↑i3 : ℕ)
        + (1 : ℕ) → p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ∧ p.getVert (↑i1 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧
        p.getVert (↑i2 : ℕ) = Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨ p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ) = Sum.inl (C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) = Sum.inr h ∧ p.getVert (↑i3 :
        ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i4 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → (↑i4 : ℕ) < (↑qv : ℕ) → (↑qf :
        ℕ) = (↑qv : ℕ) + (1 : ℕ) → p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) →
        p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) → (
    ∀ (f : E), (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) f = some (C.gamma (D.gammaIndex d)) ∧
    ∃ v ∈ TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))},
    ∃ w ∉ TreeSequenceVertexSet R.replacementTree, G.ends f = s(v, w)) ↔ f = D.f0 d ∨ f =
        C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨ f = C.blockEdge (D.gammaIndex d) (1 : Fin
        (2 : ℕ))) → (
    ∀ (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) j ∉ U) → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → (
    ∀ {w : V}, w ∈ Z → w ∉ U) →
    ∀ u ∈ U, Sum.inl u ∉ p.support

private theorem helper_no_gamma_cross_96.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    ∀ (f : E), phiD f = some gamma → Incident G R.u1 f ∨ Incident G R.u2 f →
    ∀ w ∈ Z, ¬Incident G w f := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD Z f hfcolor hfu w hwZ hfw
  have hfix := ScheideReplacementPairFixed G k e0 phi T C D d R f hfu
  have holdColor : phi f = some gamma := by
    simpa [phiD, gamma] using hfix.symm.trans hfcolor
  have hwT : w ∈ TreeSequenceVertexSet T := (Finset.mem_sdiff.mp hwZ).1
  have hout : (if Incident G R.u1 f then R.u1 else R.u2) ∉
      TreeSequenceVertexSet T := by
    split
    · exact R.u1_outside
    · exact R.u2_outside
  have hfo : Incident G (if Incident G R.u1 f then R.u1 else R.u2) f := by
    split
    · assumption
    · exact hfu.resolve_left (by assumption)
  have hne : w ≠ (if Incident G R.u1 f then R.u1 else R.u2) := by
    intro heq
    exact hout (heq ▸ hwT)
  have ends_eq_of_mem : ∀ {q : Sym2 V} {a b : V},
      a ∈ q → b ∈ q → a ≠ b → q = s(a, b) := by
    intro q a b ha hb hab
    induction q using Sym2.inductionOn with
    | _ x y =>
        simp only [Sym2.mem_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        <;> simp_all []
  have hfBoundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwT, _, hout,
      ends_eq_of_mem (by simpa [Incident] using hfw)
        (by simpa [Incident] using hfo) hne⟩
  have holdClosed : ColoredVertexSetClosed G phi
      (TreeSequenceVertexSet T) :=
    (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
  exact (holdClosed hfBoundary
    ((D.v0_is_exit d |> fun hexit =>
      (ScheideDefectiveSetup.replacement_path_full D d).1))
    holdColor) (D.gamma_missing_at_v0 d)

private theorem helper_hxOutside_244.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet R.replacementTree;
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))}; X = Z ∪ U → (
    ∀ {w : V}, w ∈ U → w = R.u1 ∨ w = R.u2) → (
    ∀ (f : E), phiD f = some gamma → Incident G R.u1 f ∨ Incident G R.u2 f →
    ∀ w ∈ Z, ¬Incident G w f) → (
    ∀ (f : E), phiD f = some beta →
    ∀ u ∈ U, Incident G u f →
    ∀ w ∈ Z, ¬Incident G w f) →
    ∀ (_ _ _ _ _ _ _ : Fin (p.length + (1 : ℕ))), (
    ∀ {w : V}, w ∈ Z → w ∉ U) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    ∀ ut ∈ U, p.getVert (↑t : ℕ) = Sum.inl ut →
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)),
    ∀ w ∈ Z, (
    ∀ r ∈ zIndices, (↑r : ℕ) ≤ (↑qz : ℕ)) →
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ)));
    ∀ (hqet : (↑qe : ℕ) < (↑t : ℕ)) (f : E), Incident G w f → phiD f = some gamma ∨ phiD f = some
        beta →
    let qx : Fin (p.length + (1 : ℕ)) := (⟨(↑qe : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qe : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ)));
    ∀ (x : V), p.getVert (↑qx : ℕ) = Sum.inl x → Incident G x f → (↑qx : ℕ) ≤ (↑t : ℕ) → x ∉ X := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p gamma phiD X U Z hXeq u_mem_cases
      no_gamma_cross no_beta_cross i0 i1 i2 i3 i4 qv qf hZU pairIndices hpairIndices t ut hutU
      htNode zIndices hzIndices qz hqzt w hwZ hqzMax qe hqet f hwf hfColors qx x hqxNode hxf
      hqxle hxX
  rw [hXeq] at hxX
  rcases Finset.mem_union.mp hxX with hxZ | hxU
  · have hqxne : qx.val ≠ t.val := by
      intro heq
      have hxut : x = ut := by
        rw [heq, htNode] at hqxNode
        exact Sum.inl.inj hqxNode.symm
      exact hZU hxZ (hxut ▸ hutU)
    have hqxt : qx.val < t.val := by omega
    have hqxMem : qx ∈ zIndices := by
      simp only [zIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqxt, x, hxZ, hqxNode⟩
    have := hqzMax qx hqxMem
    dsimp [qx, qe] at this
    omega
  · rcases hfColors with hfgamma | hfbeta
    · rcases u_mem_cases hxU with hx1 | hx2
      · exact no_gamma_cross f hfgamma (Or.inl (hx1.symm ▸ hxf))
          w hwZ hwf
      · exact no_gamma_cross f hfgamma (Or.inr (hx2.symm ▸ hxf))
          w hwZ hwf
    · exact no_beta_cross f hfbeta x hxU hxf w hwZ hwf

private theorem helper_hfGamma_268.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
        beta ∈ MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin
        k) (Sum.inl (D.v0 d))) v →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet R.replacementTree;
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))}; Z ⊆ X → v ∈ X →
        ColoredVertexSetClosed G phiD X →
    ∀ (_ _ _ _ _ _ _ : Fin (p.length + (1 : ℕ))), p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)),
    ∀ w ∈ Z, p.getVert (↑qz : ℕ) = Sum.inl w →
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ)));
    ∀ (hqet : (↑qe : ℕ) < (↑t : ℕ)) (f : E), Incident G w f → phiD f = some gamma ∨ phiD f = some
        beta →
    let qx : Fin (p.length + (1 : ℕ)) := (⟨(↑qe : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qe : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ)));
    ∀ (x : V), p.getVert (↑qx : ℕ) = Sum.inl x → Incident G x f → x ∉ X → phiD f = some gamma := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hbetaD gamma phiD X U Z hZsubX hvX hclosed i0
      i1 i2 i3 i4 qv qf hpath fin_le pairIndices hpairIndices t zIndices hzIndices qz hqzt w hwZ
      hqw qe hqet f hwf hfColors qx x hqxNode hxf hxOutside
  rcases hfColors with hfgamma | hfbeta
  · exact hfgamma
  · have hfBoundary : f ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine ⟨w, hZsubX hwZ, x, hxOutside, ?_⟩
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
    exact False.elim (hclosed hfBoundary hvX hfbeta hbetaD)

private theorem helper_hreturn_forward_310.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta;
    ∀ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + (1 : ℕ))), (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) →
        (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) → (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) → (↑i4 : ℕ) = (↑i3 : ℕ)
        + (1 : ℕ) → (↑i4 : ℕ) < (↑qv : ℕ) → (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) → p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) → (
    ∀ (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) j ∉ U) → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → (
    ∀ {w : V}, w ∈ Z → w ∉ U) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    ∀ ut ∈ U, p.getVert (↑t : ℕ) = Sum.inl ut →
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)), (
    ∀ r ∈ zIndices, (↑r : ℕ) ≤ (↑qz : ℕ)) →
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qe : ℕ) < (↑t : ℕ) →
    ∀ (f : E), p.getVert (↑qe : ℕ) = Sum.inr f →
    ∀ (a1 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = s(C.y a1,
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.getVert (↑i0 : ℕ) = Sum.inr
        (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) → p.getVert (↑i2 : ℕ) = Sum.inr h →
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) →
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → f =
        C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p gamma phiD U Z H h i0 i1 i2 i3 i4 qv qf hi01
      hi12 hi23 hi34 hi4qv hqfv hpath fin_le hblockNotU hbaseZ hZU pairIndices hpairIndices t ut
      hutU htNode zIndices hzIndices qz hqzt hqzMax qe hqet f hqeNode a1 ha1ends ha0 ha1 ha2 ha3
      ha4 hf
  have hqe0 : qe.val = i0.val := by
    have hvEq : p.getVert qe.val = p.getVert i0.val := by
      rw [hqeNode, hf, ha0]
    exact hpath.getVert_injOn
      (by simpa using fin_le qe) (by simpa using fin_le i0) hvEq
  have hi1ne : t.val ≠ i1.val := by
    intro heq
    have he : ut = C.blockVertex (D.gammaIndex d) 0 := by
      apply Sum.inl.inj
      rw [← htNode, heq, ha1]
    exact hblockNotU 0 (he.symm ▸ hutU)
  have hi2ne : t.val ≠ i2.val := by
    intro heq
    have : (Sum.inl ut : Sum V E) = Sum.inr h := by
      rw [← htNode, heq, ha2]
    simp at this
  have hi3ne : t.val ≠ i3.val := by
    intro heq
    have he : ut = C.blockVertex (D.gammaIndex d) 1 := by
      apply Sum.inl.inj
      rw [← htNode, heq, ha3]
    exact hblockNotU 1 (he.symm ▸ hutU)
  have hi4ne : t.val ≠ i4.val := by
    intro heq
    have : (Sum.inl ut : Sum V E) =
        Sum.inr (C.blockEdge (D.gammaIndex d) 1) := by
      rw [← htNode, heq, ha4]
    simp at this
  have hi4t : i4.val < t.val := by
    dsimp [qe] at hqe0 hqet
    omega
  let ir : Fin (p.length + 1) := ⟨i4.val + 1, by omega⟩
  have hretAdj := p.adj_getVert_succ (i := i4.val) (by omega)
  have hret : p.getVert ir.val = Sum.inl (C.y a1) := by
    cases hn : p.getVert ir.val with
    | inr e =>
        have hadj : H.Adj
            (Sum.inr (C.blockEdge (D.gammaIndex d) 1))
            (Sum.inr e) := by
          simpa [H, ir, ha4, hn] using hretAdj
        simp [H, TwoColorIncidenceGraph] at hadj
    | inl y =>
        have hyInc : Incident G y
            (C.blockEdge (D.gammaIndex d) 1) := by
          have hadj : H.Adj
              (Sum.inr (C.blockEdge (D.gammaIndex d) 1))
              (Sum.inl y) := by
            simpa [H, ir, ha4, hn] using hretAdj
          have hpair : Incident G y
                (C.blockEdge (D.gammaIndex d) 1) ∧
              (phiD (C.blockEdge (D.gammaIndex d) 1) = some gamma ∨
                phiD (C.blockEdge (D.gammaIndex d) 1) = some beta) := by
            simpa [H, TwoColorIncidenceGraph] using hadj
          exact hpair.1
        have hyEnds : y = C.y a1 ∨
            y = C.blockVertex (D.gammaIndex d) 1 := by
          simpa [Incident, ha1ends] using hyInc
        rcases hyEnds with hy | hy
        · simp [hy]
        · have hrepeat : p.getVert ir.val = p.getVert i3.val := by
            rw [hn, hy, ha3]
          have hind := hpath.getVert_injOn
            (by simpa using fin_le ir) (by simpa using fin_le i3) hrepeat
          dsimp [ir] at hind
          omega
  have hirle : ir.val ≤ t.val := by dsimp [ir]; omega
  have hirne : ir.val ≠ t.val := by
    intro heq
    have he : C.y a1 = ut := by
      apply Sum.inl.inj
      rw [← hret, heq, htNode]
    exact hZU (hbaseZ a1) (he ▸ hutU)
  have hirt : ir.val < t.val := by omega
  have hirMem : ir ∈ zIndices := by
    simp only [zIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hirt, C.y a1, hbaseZ a1, hret⟩
  have hmax := hqzMax ir hirMem
  dsimp [ir, qe] at hmax hqe0
  omega

private theorem helper_hreturn_reverse_400.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta;
    ∀ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + (1 : ℕ))), (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) →
        (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) → (↑i3 : ℕ) = (↑i2 : ℕ) + (1 : ℕ) → (↑i4 : ℕ) = (↑i3 : ℕ)
        + (1 : ℕ) → (↑i4 : ℕ) < (↑qv : ℕ) → (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) → p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) → (
    ∀ (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) j ∉ U) → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → (
    ∀ {w : V}, w ∈ Z → w ∉ U) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    ∀ ut ∈ U, p.getVert (↑t : ℕ) = Sum.inl ut →
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)), (
    ∀ r ∈ zIndices, (↑r : ℕ) ≤ (↑qz : ℕ)) →
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qe : ℕ) < (↑t : ℕ) →
    ∀ (f : E), p.getVert (↑qe : ℕ) = Sum.inr f →
    ∀ (a0 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = s(C.y a0,
        C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) → p.getVert (↑i0 : ℕ) = Sum.inr
        (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.getVert (↑i2 : ℕ) = Sum.inr h →
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → f =
        C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ)) → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p gamma phiD U Z H h i0 i1 i2 i3 i4 qv qf hi01
      hi12 hi23 hi34 hi4qv hqfv hpath fin_le hblockNotU hbaseZ hZU pairIndices hpairIndices t ut
      hutU htNode zIndices hzIndices qz hqzt hqzMax qe hqet f hqeNode a0 ha0ends ha0 ha1 ha2 ha3
      ha4 hf
  have hqe0 : qe.val = i0.val := by
    have hvEq : p.getVert qe.val = p.getVert i0.val := by
      rw [hqeNode, hf, ha0]
    exact hpath.getVert_injOn
      (by simpa using fin_le qe) (by simpa using fin_le i0) hvEq
  have hi1ne : t.val ≠ i1.val := by
    intro heq
    have he : ut = C.blockVertex (D.gammaIndex d) 1 := by
      apply Sum.inl.inj
      rw [← htNode, heq, ha1]
    exact hblockNotU 1 (he.symm ▸ hutU)
  have hi2ne : t.val ≠ i2.val := by
    intro heq
    have : (Sum.inl ut : Sum V E) = Sum.inr h := by
      rw [← htNode, heq, ha2]
    simp at this
  have hi3ne : t.val ≠ i3.val := by
    intro heq
    have he : ut = C.blockVertex (D.gammaIndex d) 0 := by
      apply Sum.inl.inj
      rw [← htNode, heq, ha3]
    exact hblockNotU 0 (he.symm ▸ hutU)
  have hi4ne : t.val ≠ i4.val := by
    intro heq
    have : (Sum.inl ut : Sum V E) =
        Sum.inr (C.blockEdge (D.gammaIndex d) 0) := by
      rw [← htNode, heq, ha4]
    simp at this
  have hi4t : i4.val < t.val := by
    dsimp [qe] at hqe0 hqet
    omega
  let ir : Fin (p.length + 1) := ⟨i4.val + 1, by omega⟩
  have hretAdj := p.adj_getVert_succ (i := i4.val) (by omega)
  have hret : p.getVert ir.val = Sum.inl (C.y a0) := by
    cases hn : p.getVert ir.val with
    | inr e =>
        have hadj : H.Adj
            (Sum.inr (C.blockEdge (D.gammaIndex d) 0))
            (Sum.inr e) := by
          simpa [H, ir, ha4, hn] using hretAdj
        simp [H, TwoColorIncidenceGraph] at hadj
    | inl y =>
        have hyInc : Incident G y
            (C.blockEdge (D.gammaIndex d) 0) := by
          have hadj : H.Adj
              (Sum.inr (C.blockEdge (D.gammaIndex d) 0))
              (Sum.inl y) := by
            simpa [H, ir, ha4, hn] using hretAdj
          have hpair : Incident G y
                (C.blockEdge (D.gammaIndex d) 0) ∧
              (phiD (C.blockEdge (D.gammaIndex d) 0) = some gamma ∨
                phiD (C.blockEdge (D.gammaIndex d) 0) = some beta) := by
            simpa [H, TwoColorIncidenceGraph] using hadj
          exact hpair.1
        have hyEnds : y = C.y a0 ∨
            y = C.blockVertex (D.gammaIndex d) 0 := by
          simpa [Incident, ha0ends] using hyInc
        rcases hyEnds with hy | hy
        · simp [hy]
        · have hrepeat : p.getVert ir.val = p.getVert i3.val := by
            rw [hn, hy, ha3]
          have hind := hpath.getVert_injOn
            (by simpa using fin_le ir) (by simpa using fin_le i3) hrepeat
          dsimp [ir] at hind
          omega
  have hirle : ir.val ≤ t.val := by dsimp [ir]; omega
  have hirne : ir.val ≠ t.val := by
    intro heq
    have he : C.y a0 = ut := by
      apply Sum.inl.inj
      rw [← hret, heq, htNode]
    exact hZU (hbaseZ a0) (he ▸ hutU)
  have hirt : ir.val < t.val := by omega
  have hirMem : ir ∈ zIndices := by
    simp only [zIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hirt, C.y a0, hbaseZ a0, hret⟩
  have hmax := hqzMax ir hirMem
  dsimp [ir, qe] at hmax hqe0
  omega

private theorem helper_hfEnds_693.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    ∀ (_ _ _ _ _ _ _ : Fin (p.length + (1 : ℕ))), p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)) (w : V), p.getVert (↑qz : ℕ) = Sum.inl w →
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ)));
    ∀ (hqet : (↑qe : ℕ) < (↑t : ℕ)) (f : E), Incident G w f →
    let qx : Fin (p.length + (1 : ℕ)) := (⟨(↑qe : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qe : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ)));
    ∀ (x : V), p.getVert (↑qx : ℕ) = Sum.inl x → Incident G x f → G.ends f = s(w, x) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p U Z i0 i1 i2 i3 i4 qv qf hpath fin_le
      pairIndices hpairIndices t zIndices hzIndices qz hqzt w hqw qe hqet f hwf qx x hqxNode hxf
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

private theorem helper_branch_739.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let X : Finset V := TreeSequenceVertexSet R.replacementTree;
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))}; X = Z ∪ U →
    ∀ (_ _ _ _ _ qv qf : Fin (p.length + (1 : ℕ))), (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) → p.getVert
        (↑qf : ℕ) = Sum.inr (D.f0 d) → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) →
        p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    ∀ ut ∈ U, p.getVert (↑t : ℕ) = Sum.inl ut →
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)),
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qe : ℕ) < (↑t : ℕ) →
    ∀ (f : E), p.getVert (↑qe : ℕ) = Sum.inr f → f = D.f0 d → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p X U Z hXeq i0 i1 i2 i3 i4 qv qf hqfv hqfNode
      hafter hpath fin_le pairIndices hpairIndices t ut hutU htNode zIndices hzIndices qz hqzt qe
      hqet f hqeNode hf0
  have hqeqf : qe.val = qf.val := by
    have hvEq : p.getVert qe.val = p.getVert qf.val := by
      rw [hqeNode, hf0, hqfNode]
    exact hpath.getVert_injOn
      (by simpa using fin_le qe) (by simpa using fin_le qf) hvEq
  have hqvt : qv.val < t.val := by
    dsimp [qe] at hqeqf
    omega
  have hutX : ut ∈ X := by
    rw [hXeq]
    exact Finset.mem_union_right _ hutU
  exact (hafter t hqvt ut htNode) (by simpa [X] using hutX)

private theorem helper_branch_751.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    ∀ (h : E) (i0 i1 i2 i3 i4 _ _ : Fin (p.length + (1 : ℕ))), (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) →
        p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert
        (↑i1 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 :
        ℕ) = Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2
        : ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨
        p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert
        (↑i1 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 :
        ℕ) = Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2
        : ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
        p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)),
    ∀ w ∈ Z, p.getVert (↑qz : ℕ) = Sum.inl w →
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qe : ℕ) < (↑t : ℕ) →
    ∀ (f : E), p.getVert (↑qe : ℕ) = Sum.inr f → (p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge
        (D.gammaIndex d) (0 : Fin (2 : ℕ))) → p.getVert (↑i1 : ℕ) = Sum.inl (C.blockVertex
        (D.gammaIndex d) (0 : Fin (2 : ℕ))) → p.getVert (↑i2 : ℕ) = Sum.inr h → p.getVert (↑i3 :
        ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.getVert (↑i4 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → f = C.blockEdge (D.gammaIndex
        d) (0 : Fin (2 : ℕ)) → False) → f = C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) → False
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p U Z h i0 i1 i2 i3 i4 qv qf hi34 horient hpath
      fin_le pairIndices hpairIndices t zIndices hzIndices qz hqzt w hwZ hqw qe hqet f hqeNode
      hreturn_forward hfBlock0
  rcases horient with hforward | hreverse
  · exact hreturn_forward hforward.1 hforward.2.1 hforward.2.2.1
      hforward.2.2.2.1 hforward.2.2.2.2 hfBlock0
  · have hqei4 : qe.val = i4.val := by
      have hvEq : p.getVert qe.val = p.getVert i4.val := by
        rw [hqeNode, hfBlock0, hreverse.2.2.2.2]
      exact hpath.getVert_injOn
        (by simpa using fin_le qe) (by simpa using fin_le i4) hvEq
    have hqzi3 : qz.val = i3.val := by
      dsimp [qe] at hqei4
      omega
    have hwEq : w = C.blockVertex (D.gammaIndex d) 0 := by
      apply Sum.inl.inj
      rw [← hqw, hqzi3, hreverse.2.2.2.1]
    exact (Finset.mem_sdiff.mp hwZ).2 (by simp [hwEq])

private theorem helper_branch_766.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let U : Finset V := { R.u1, R.u2 };
    let Z : Finset V := TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    ∀ (h : E) (i0 i1 i2 i3 i4 _ _ : Fin (p.length + (1 : ℕ))), (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) →
        p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert
        (↑i1 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 :
        ℕ) = Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2
        : ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨
        p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert
        (↑i1 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 :
        ℕ) = Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2
        : ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
        p.IsPath → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑r : ℕ) ≤ p.length) →
    let pairIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) |
    ∃ a ∈ U, p.getVert (↑r : ℕ) = Sum.inl a};
    ∀ (hpairIndices : pairIndices.Nonempty),
    let t : Fin (p.length + (1 : ℕ)) := pairIndices.min' hpairIndices;
    let zIndices : Finset (Fin (p.length + (1 : ℕ))) := {r : Fin (p.length + (1 : ℕ)) | (↑r : ℕ) <
        (↑t : ℕ) ∧
    ∃ w ∈ Z, p.getVert (↑r : ℕ) = Sum.inl w};
    ∀ (hzIndices : zIndices.Nonempty),
    let qz : Fin (p.length + (1 : ℕ)) := zIndices.max' hzIndices;
    ∀ (hqzt : (↑qz : ℕ) < (↑t : ℕ)),
    ∀ w ∈ Z, p.getVert (↑qz : ℕ) = Sum.inl w →
    let qe : Fin (p.length + (1 : ℕ)) := (⟨(↑qz : ℕ) + (1 : ℕ), Decidable.byContradiction fun (a :
        ¬(↑qz : ℕ) + (1 : ℕ) < p.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qe : ℕ) < (↑t : ℕ) →
    ∀ (f : E), p.getVert (↑qe : ℕ) = Sum.inr f → (p.getVert (↑i0 : ℕ) = Sum.inr (C.blockEdge
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.getVert (↑i1 : ℕ) = Sum.inl (C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.getVert (↑i2 : ℕ) = Sum.inr h → p.getVert (↑i3 :
        ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) → p.getVert (↑i4 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → f = C.blockEdge (D.gammaIndex
        d) (1 : Fin (2 : ℕ)) → False) → f = C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ)) → False
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p U Z h i0 i1 i2 i3 i4 qv qf hi34 horient hpath
      fin_le pairIndices hpairIndices t zIndices hzIndices qz hqzt w hwZ hqw qe hqet f hqeNode
      hreturn_reverse hfBlock1
  rcases horient with hforward | hreverse
  · have hqei4 : qe.val = i4.val := by
      have hvEq : p.getVert qe.val = p.getVert i4.val := by
        rw [hqeNode, hfBlock1, hforward.2.2.2.2]
      exact hpath.getVert_injOn
        (by simpa using fin_le qe) (by simpa using fin_le i4) hvEq
    have hqzi3 : qz.val = i3.val := by
      dsimp [qe] at hqei4
      omega
    have hwEq : w = C.blockVertex (D.gammaIndex d) 1 := by
      apply Sum.inl.inj
      rw [← hqw, hqzi3, hforward.2.2.2.1]
    exact (Finset.mem_sdiff.mp hwZ).2 (by simp [hwEq])
  · exact hreturn_reverse hreverse.1 hreverse.2.1 hreverse.2.2.1
      hreverse.2.2.2.1 hreverse.2.2.2.2 hfBlock1

private theorem helper_havoidU_249.{u_1, u_2} :
    helperHavoidU249Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hbetaD gamma phiD X U Z H hvZ hXeq hZsubX hvX
      hclosed u_mem_cases no_gamma_cross no_beta_cross h i0 i1 i2 i3 i4 qv qf hi01 hi12 hi23 hi34
      horient hi4qv hqfv hqfNode hafter hpath fin_le hexact hblockNotU hbaseZ hZU u huU huSupport
  let pairIndices : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter fun r => ∃ a ∈ U, p.getVert r.val = Sum.inl a
  have hpairIndices : pairIndices.Nonempty := by
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp huSupport
    refine ⟨⟨n, by omega⟩, ?_⟩
    simp only [pairIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, huU, hn⟩
  let t : Fin (p.length + 1) := pairIndices.min' hpairIndices
  have htMem : t ∈ pairIndices := Finset.min'_mem pairIndices hpairIndices
  obtain ⟨ut, hutU, htNode⟩ : ∃ a ∈ U,
      p.getVert t.val = Sum.inl a := by
    simpa only [pairIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      using htMem
  have htPos : 0 < t.val := by
    by_contra hn
    have ht0 : t.val = 0 := by omega
    have hvut : v = ut := by
      rw [ht0, p.getVert_zero] at htNode
      exact Sum.inl.inj htNode
    exact hZU hvZ (hvut ▸ hutU)
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
  have hqzMax : ∀ r : Fin (p.length + 1), r ∈ zIndices →
      r.val ≤ qz.val := by
    intro r hr
    exact_mod_cast Finset.le_max' zIndices r hr
  let qe : Fin (p.length + 1) := ⟨qz.val + 1, by omega⟩
  have hqzAdj := p.adj_getVert_succ (i := qz.val)
    (by omega : qz.val < p.length)
  have hqzAdj' : H.Adj (Sum.inl w) (p.getVert qe.val) := by
    simpa [H, qe, hqw] using hqzAdj
  have hqet : qe.val < t.val := by
    have hne : qe.val ≠ t.val := by
      intro heq
      have hadj : H.Adj (Sum.inl w) (Sum.inl ut) := by
        simpa [heq, htNode] using hqzAdj'
      simp [H, TwoColorIncidenceGraph] at hadj
    change qz.val + 1 ≠ t.val at hne
    change qz.val + 1 < t.val
    omega
  obtain ⟨f, hqeNode, hwf, hfColors⟩ : ∃ f : E,
      p.getVert qe.val = Sum.inr f ∧ Incident G w f ∧
        (phiD f = some gamma ∨ phiD f = some beta) := by
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
  have hqeAdj := p.adj_getVert_succ (i := qe.val)
    (by omega : qe.val < p.length)
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
            (phiD f = some gamma ∨ phiD f = some beta) := by
          simpa [H, TwoColorIncidenceGraph] using hadj
        exact hpair.1
    | inr e =>
        exfalso
        have hadj : H.Adj (Sum.inr f) (Sum.inr e) := by
          simpa [hn] using hqeAdj'
        simp [H, TwoColorIncidenceGraph] at hadj
  have hqxle : qx.val ≤ t.val := by dsimp [qx]; omega
  have hxOutside := @helper_hxOutside_244 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R beta v z p hXeq u_mem_cases no_gamma_cross no_beta_cross i0
      i1 i2 i3 i4 qv qf hZU hpairIndices ut hutU htNode hzIndices hqzt w hwZ hqzMax hqet f hwf
      hfColors x hqxNode hxf hqxle
  have hfGamma := @helper_hfGamma_268 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 phi T C D d R beta v z p hbetaD hZsubX hvX hclosed i0 i1 i2 i3 i4 qv qf hpath fin_le
      hpairIndices hzIndices hqzt w hwZ hqw hqet f hwf hfColors x hqxNode hxf hxOutside
  have hfEnds := @helper_hfEnds_693 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R beta v z p i0 i1 i2 i3 i4 qv qf hpath fin_le hpairIndices hzIndices hqzt w
      hqw hqet f hwf x hqxNode hxf
  have hfThree : f = D.f0 d ∨
      f = C.blockEdge (D.gammaIndex d) 0 ∨
      f = C.blockEdge (D.gammaIndex d) 1 := by
    apply (hexact f).mp
    exact ⟨hfGamma, w, hwZ, x, hxOutside, hfEnds⟩
  obtain ⟨a0, ha0ends⟩ := C.block_attaches_to_base (D.gammaIndex d) 0
  obtain ⟨a1, ha1ends⟩ := C.block_attaches_to_base (D.gammaIndex d) 1
  have hreturn_forward := @helper_hreturn_forward_310 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R beta v z p h i0 i1 i2 i3 i4 qv qf hi01 hi12 hi23 hi34 hi4qv
      hqfv hpath fin_le hblockNotU hbaseZ hZU hpairIndices ut hutU htNode hzIndices hqzt hqzMax hqet
      f hqeNode a1 ha1ends
  have hreturn_reverse := @helper_hreturn_reverse_400 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R beta v z p h i0 i1 i2 i3 i4 qv qf hi01 hi12 hi23 hi34 hi4qv
      hqfv hpath fin_le hblockNotU hbaseZ hZU hpairIndices ut hutU htNode hzIndices hqzt hqzMax hqet
      f hqeNode a0 ha0ends
  rcases hfThree with hf0 | hfBlock0 | hfBlock1
  · exact @helper_branch_739 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R beta v z p hXeq i0 i1 i2 i3 i4 qv qf hqfv hqfNode hafter hpath fin_le
      hpairIndices ut hutU htNode hzIndices hqzt hqet f hqeNode hf0
  · exact @helper_branch_751 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R beta v z p h i0 i1 i2 i3 i4 qv qf hi34 horient hpath fin_le hpairIndices
      hzIndices hqzt w hwZ hqw hqet f hqeNode hreturn_forward hfBlock0
  · exact @helper_branch_766 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R beta v z p h i0 i1 i2 i3 i4 qv qf hi34 horient hpath fin_le hpairIndices
      hzIndices hqzt w hwZ hqw hqet f hqeNode hreturn_reverse hfBlock1
private theorem helper_branch_630.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (beta : Fin k) (v z : V) (p : (TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)), beta ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v
        → beta ∈ TreeFreeColors (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin
        k) (Sum.inl (D.v0 d))) R.replacementTree → ScheideDefectiveChainPath R.replacementTree
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (C.gamma (D.gammaIndex d)) beta v z p →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet R.replacementTree;
    let U : Finset V := { R.u1, R.u2 };
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; v ∈ X →
        GlobalMaximumTriple G k e0 phiD R.replacementTree → R.u1 ∈ U → R.u2 ∈ U → C.gamma
        (D.gammaIndex d) ∈ DefectiveColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (TreeSequenceVertexSet R.replacementTree) → Sum.inl
        R.u1 ∉ p.support → Sum.inl R.u2 ∉ p.support →
    ∀ f ∈ BoundaryColorEdges G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin
        k) (Sum.inl (D.v0 d))) (TreeSequenceVertexSet R.replacementTree) (C.gamma (D.gammaIndex
        d)), ¬Incident G R.u1 f ∧ ¬Incident G R.u2 f := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hbetaD hbetaFree hp gamma phiD X U H hvX
      hglobal hu1U hu2U hgammaDef hu1Avoid hu2Avoid f hfBoundary
  have hfSupport : Sum.inr f ∈ p.support :=
    ((ScheideDefectiveChainBoundaryEdges G k e0 phiD
      R.replacementTree hglobal gamma beta
      (by simpa [gamma, phiD, X] using hgammaDef) hbetaFree v
      (by simpa [X] using hvX) (by simpa [phiD] using hbetaD)
      z p (by simpa [gamma, phiD] using hp)) f).mp
        (by simpa [gamma, phiD, X] using hfBoundary) |>.2
  have hfColor : phiD f = some gamma := by
    have := (Finset.mem_filter.mp
      (show f ∈ BoundaryColorEdges G phiD X gamma by
        simpa [gamma, phiD, X] using hfBoundary)).2
    exact this
  have avoid_incident (u : V) (huU : u ∈ U)
      (huAvoid : Sum.inl u ∉ p.support) : ¬ Incident G u f := by
    intro huf
    have hadj : H.Adj (Sum.inl u) (Sum.inr f) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G u f ∧
            (phiD f = some gamma ∨ phiD f = some beta) from
          ⟨huf, Or.inl hfColor⟩)
    have hfComponent : H.connectedComponentMk (Sum.inr f) =
        H.connectedComponentMk (Sum.inl v) := by
      change Sum.inr f ∈ TwoColorComponent G phiD gamma beta (Sum.inl v)
      rw [← hp.2.2.2]
      exact hfSupport
    have huComponent : H.connectedComponentMk (Sum.inl u) =
        H.connectedComponentMk (Sum.inl v) :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj).trans hfComponent
    apply huAvoid
    have huComp : Sum.inl u ∈
        TwoColorComponent G phiD gamma beta (Sum.inl v) := huComponent
    rw [← hp.2.2.2] at huComp
    exact huComp
  exact ⟨avoid_incident R.u1 hu1U hu1Avoid,
    avoid_incident R.u2 hu2U hu2Avoid⟩

theorem ScheideSymmetricReplacementBoundaryAvoidance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    let Z :=
      TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}
    ∀ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phiD gamma beta).Walk (Sum.inl v) (Sum.inl z)),
    v ∈ Z →
    beta ∈ MissingColors G phiD v →
    beta ∈ MissingColors G phi v →
    beta ∈ TreeFreeColors phiD R.replacementTree →
    beta ≠ d.1 →
    beta ≠ gamma →
    ScheideDefectiveChainPath R.replacementTree phiD gamma beta v z p →
    (Sum.inl R.u1 ∉ p.support ∧ Sum.inl R.u2 ∉ p.support) ∧
      (∀ f : E,
          f ∈ BoundaryColorEdges G phiD (TreeSequenceVertexSet R.replacementTree) gamma →
            ¬Incident G R.u1 f ∧ ¬Incident G R.u2 f) ∧
        ∀ f : E,
          phiD f = some gamma →
            (Incident G R.u1 f ∨ Incident G R.u2 f) → ∀ w ∈ Z, ¬Incident G w f := by
  classical
  dsimp only
  intro beta v z p hv hbetaD hbetaOld hbetaFree hbetaDelta hbetaGamma hp
  let gamma := C.gamma (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let X := TreeSequenceVertexSet R.replacementTree
  let U := ({R.u1, R.u2} : Finset V)
  let Z := TreeSequenceVertexSet T \
    {C.blockVertex (D.gammaIndex d) 0,
      C.blockVertex (D.gammaIndex d) 1}
  let H := TwoColorIncidenceGraph G phiD gamma beta
  have hvZ : v ∈ Z := by simpa [Z] using hv
  have hXeq : X = Z ∪ U := by
    simpa [X, Z, U] using R.replacement_vertices
  have hZsubX : Z ⊆ X := by
    intro w hw
    rw [hXeq]
    exact Finset.mem_union_left _ hw
  have hvX : v ∈ X := hZsubX hvZ
  have hu1X : R.u1 ∈ X := by
    rw [hXeq]
    simp [U]
  have hu2X : R.u2 ∈ X := by
    rw [hXeq]
    simp [U]
  have hmaximum := ScheideReplacementMaximum G k e0 phi T C D d R
  dsimp [gamma, phiD] at hmaximum
  have hproper : IsProperEdgeColoring G phiD := hmaximum.1
  have hglobal : GlobalMaximumTriple G k e0 phiD R.replacementTree :=
    hmaximum.2.2
  have hclosed : ColoredVertexSetClosed G phiD X := by
    change ColoredVertexSetClosed G phiD
      (TreeSequenceVertexSet R.replacementTree)
    exact (ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree hglobal).2.2.2.2
  have hu1U : R.u1 ∈ U := by simp [U]
  have hu2U : R.u2 ∈ U := by simp [U]
  have u_mem_cases : ∀ {w : V}, w ∈ U → w = R.u1 ∨ w = R.u2 := by
    intro w hw
    simpa [U] using hw
  have no_gamma_cross := @helper_no_gamma_cross_96 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R
  obtain ⟨b, hbOldColor, hbEnds⟩ :=
    ScheideReplacementInternalMissing G k e0 phi T C D d R beta
      (by simpa [gamma] using hbetaGamma) ⟨v, hv, hbetaOld⟩
  have hbIncident1 : Incident G R.u1 b := by
    change R.u1 ∈ G.ends b
    rw [hbEnds]
    simp
  have hbIncident2 : Incident G R.u2 b := by
    change R.u2 ∈ G.ends b
    rw [hbEnds]
    simp
  have hbColor : phiD b = some beta := by
    have hfix := ScheideReplacementPairFixed G k e0 phi T C D d R b
      (Or.inl hbIncident1)
    simpa [phiD] using hfix.trans hbOldColor
  have beta_incident_unique : ∀ (u : V), u ∈ U → ∀ f : E,
      Incident G u f → phiD f = some beta → f = b := by
    intro u hu f huf hfColor
    rcases u_mem_cases hu with rfl | rfl
    · by_contra hfb
      exact (hproper hfb ⟨R.u1, huf, hbIncident1⟩ hfColor) hbColor
    · by_contra hfb
      exact (hproper hfb ⟨R.u2, huf, hbIncident2⟩ hfColor) hbColor
  have no_beta_cross : ∀ f : E, phiD f = some beta →
      ∀ u ∈ U, Incident G u f → ∀ w ∈ Z, ¬ Incident G w f := by
    intro f hfColor u huU huf w hwZ hwf
    have hfb : f = b := beta_incident_unique u huU f huf hfColor
    subst f
    have hwU : w ∈ U := by
      change w ∈ ({R.u1, R.u2} : Finset V)
      simpa [Incident, hbEnds] using hwf
    have hwT : w ∈ TreeSequenceVertexSet T :=
      (Finset.mem_sdiff.mp hwZ).1
    rcases u_mem_cases hwU with hw1 | hw2
    · exact R.u1_outside (hw1 ▸ hwT)
    · exact R.u2_outside (hw2 ▸ hwT)
  obtain ⟨h, i0, i1, i2, i3, i4, qv, qf,
      hhColor, hhEnds, hi01, hi12, hi23, hi34, horient,
      hi4qv, hqfv, hqvNode, hqfNode, hafter, hu1NotExit, hu2NotExit⟩ :=
    ScheideSymmetricReplacementPathOrder G k e0 phi T C D d R
      beta v z p hv hbetaD hbetaOld hbetaFree hbetaDelta hbetaGamma hp
  have hpath : p.IsPath := hp.2.1
  have fin_le (r : Fin (p.length + 1)) : r.val ≤ p.length := by
    have := r.isLt
    omega
  have hconfig :=
    ScheideSymmetricReplacementBoundaryConfiguration G k e0 phi T C D d R
  dsimp [gamma, phiD, X, Z] at hconfig
  rcases hconfig with
    ⟨hgammaDef, hf0Color, hb0Color, hb1Color, hf0ne0, hf0ne1,
      hb01ne, hexact⟩
  have hblockOld : ∀ j : Fin 2,
      C.blockVertex (D.gammaIndex d) j ∈ TreeSequenceVertexSet T := by
    intro j
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨⟨C.p + 2 * (D.gammaIndex d).val + j.val, by
      rw [C.length_eq]
      omega⟩, C.block_vertex_position _ _⟩
  have hblockNotU : ∀ j : Fin 2,
      C.blockVertex (D.gammaIndex d) j ∉ U := by
    intro j hj
    rcases u_mem_cases hj with hj1 | hj2
    · exact R.u1_outside (hj1.symm ▸ hblockOld j)
    · exact R.u2_outside (hj2.symm ▸ hblockOld j)
  have hblockNotX : ∀ j : Fin 2,
      C.blockVertex (D.gammaIndex d) j ∉ X := by
    intro j hj
    rw [hXeq] at hj
    rcases Finset.mem_union.mp hj with hjZ | hjU
    · exact (Finset.mem_sdiff.mp hjZ).2 (by
        have hjval : j.val = 0 ∨ j.val = 1 := by omega
        rcases hjval with hjval | hjval
        · have heq : j = (0 : Fin 2) := Fin.ext hjval
          subst j
          simp
        · have heq : j = (1 : Fin 2) := Fin.ext hjval
          subst j
          simp)
    · exact hblockNotU j hjU
  have hbaseZ : ∀ q : Fin C.p, C.y q ∈ Z := by
    intro q
    simp only [Z, Finset.mem_sdiff]
    constructor
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩,
        C.base_vertex_position q⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      intro he
      rcases he with he | he
      · have hi := T.vertex_injective
          ((C.base_vertex_position q).trans
            (he.trans (C.block_vertex_position (D.gammaIndex d) 0).symm))
        have hv := congrArg Fin.val hi
        have hq := q.isLt
        have hpC := C.p_ge_two
        change q.val = C.p + 2 * (D.gammaIndex d).val at hv
        omega
      · have hi := T.vertex_injective
          ((C.base_vertex_position q).trans
            (he.trans (C.block_vertex_position (D.gammaIndex d) 1).symm))
        have hv := congrArg Fin.val hi
        have hq := q.isLt
        have hpC := C.p_ge_two
        change q.val = C.p + 2 * (D.gammaIndex d).val + 1 at hv
        omega
  have hZU : ∀ {w : V}, w ∈ Z → w ∉ U := by
    intro w hwZ hwU
    have hwT := (Finset.mem_sdiff.mp hwZ).1
    rcases u_mem_cases hwU with hw1 | hw2
    · exact R.u1_outside (hw1 ▸ hwT)
    · exact R.u2_outside (hw2 ▸ hwT)
  have havoidU := @helper_havoidU_249 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 phi T C D d R beta v z p hbetaD hvZ hXeq hZsubX hvX hclosed u_mem_cases no_gamma_cross
      no_beta_cross h i0 i1 i2 i3 i4 qv qf hi01 hi12 hi23 hi34 horient hi4qv hqfv hqfNode hafter
      hpath fin_le hexact hblockNotU hbaseZ hZU
  have hu1Avoid : Sum.inl R.u1 ∉ p.support := havoidU R.u1 hu1U
  have hu2Avoid : Sum.inl R.u2 ∉ p.support := havoidU R.u2 hu2U
  refine ⟨⟨hu1Avoid, hu2Avoid⟩, ?_, ?_⟩
  · exact @helper_branch_630 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R beta v z p hbetaD hbetaFree hp hvX hglobal hu1U hu2U hgammaDef hu1Avoid hu2Avoid
  · intro f hfColor hfu w hwZ
    exact no_gamma_cross f (by simpa [phiD, gamma] using hfColor) hfu w
      (by simpa [Z] using hwZ)

end GoldbergSeymour

end
