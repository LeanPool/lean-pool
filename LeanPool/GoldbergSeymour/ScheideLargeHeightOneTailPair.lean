/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.FixedPairMaximalTashkinovTree
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ScheideExitNoFree
public import LeanPool.GoldbergSeymour.ScheideExitVertex
public import LeanPool.GoldbergSeymour.ScheideExitVertices
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.ScheideGraphHeightOdd
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumFixedPairMaximal
public import LeanPool.GoldbergSeymour.ScheideKempePathHeightBound
public import LeanPool.GoldbergSeymour.ScheideMaximalKempePath
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralLemma
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeUsedColors
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Scheide Large Height One Tail Pair

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation929Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T), BalancedGlobalMaximumTriple N → (
    ∀ (v : V),
    ∃ (e : E), Incident G v e) → ScheideGraphHeight G + (2 : ℕ) = TashkinovOrder G →
    let this : DecidableEq V := Classical.decEq V;
    ∀ (hcard : (TreeSequenceVertexSet T).card = T.length + (1 : ℕ)) (horder : TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ)
        = N.height + (2 : ℕ)),
    let firstTail : Fin T.length := (⟨N.height - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    let firstNew : Fin (T.length + (1 : ℕ)) := (⟨N.height,
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let secondNew : Fin (T.length + (1 : ℕ)) := (⟨N.height + (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (a0 : Fin ((↑firstTail : ℕ) + (1 : ℕ))) (gamma : Fin k), phi (T.edge firstTail) = some gamma
        →
    let gammaBase : Fin N.height := (⟨(↑a0 : ℕ),
    have ha : (↑a0 : ℕ) < (↑firstTail : ℕ) + (1 : ℕ) := a0.isLt;
    have hh : (2 : ℕ) ≤ N.height := N.height_lower; Eq.mpr (id rfl) (Eq.mp (congrArg (LT.lt (↑a0 :
        ℕ)) (Nat.sub_add_cancel (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ N.height) => (
    by omega
    )))) ha)⟩ : Fin N.height); gamma ∈ MissingColors G phi (T.vertex (Fin.castLE N.height_upper
        gammaBase)) →
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)), phi (T.edge secondTail) = some gamma →
    ∀ (base0raw : Fin ((↑firstTail : ℕ) + (1 : ℕ))),
    let base0 : Fin N.height := (⟨(↑base0raw : ℕ),
    have hb : (↑base0raw : ℕ) < (↑firstTail : ℕ) + (1 : ℕ) := base0raw.isLt;
    have hh : (2 : ℕ) ≤ N.height := N.height_lower; Eq.mpr (id rfl) (Eq.mp (congrArg (LT.lt
        (↑base0raw : ℕ)) (Nat.sub_add_cancel (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        N.height) =>
    by omega
    ))) hb)⟩ : Fin N.height); G.ends (T.edge firstTail) = s(T.vertex (Fin.castLE N.height_upper
        base0), T.vertex firstNew) →
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (w : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))), w.IsPath → {z : V ⊕ E | z ∈ w.support} = TwoColorComponent G phi N.alpha
        N.beta (Sum.inl (T.vertex i0)) → (4 : ℕ) ∣ w.length → (
    ∀ (v : V), Sum.inl v ∈ w.support → v ∈ TreeSequenceVertexSet T) → (TreeColorUnusedThrough phi
        T N.alpha i1 → IsProperEdgeColoring G (TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl
        (T.vertex i0))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl
        (T.vertex i0))) e0 ∧ TashkinovTree G e0 (TwoColorComponentSwap G phi N.alpha N.beta
        (Sum.inl (T.vertex i0))) T) →
    ∀ (P : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), P.IsPath → (4 : ℕ) ∣ P.length
        → (
    ∀ (v : V), Sum.inl v ∈ P.support → v ∈ TreeSequenceVertexSet T) → P.length / (2 : ℕ) + (1 : ℕ)
        ≤ ScheideGraphHeight G → (
    ∀ {z : V ⊕ E}, z ∈ N.closingPath.support → z ∈ P.support) → (phi (T.edge firstTail) = some
        N.alpha ∨ phi (T.edge firstTail) = some N.beta → Sum.inl (T.vertex firstNew) ∈ P.support)
        → Sum.inl (T.vertex firstNew) ∉ N.closingPath.support → Elementary G

private theorem helper_free_of_ne_gamma_377.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hcard : (TreeSequenceVertexSet T).card = T.length + (1 : ℕ)) (horder : TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ)
        = N.height + (2 : ℕ)),
    let firstTail : Fin T.length := (⟨N.height - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    ∀ (a0 : Fin ((↑firstTail : ℕ) + (1 : ℕ))) (gamma : Fin k),
    let gammaBase : Fin N.height := (⟨(↑a0 : ℕ),
    have ha : (↑a0 : ℕ) < (↑firstTail : ℕ) + (1 : ℕ) := a0.isLt;
    have hh : (2 : ℕ) ≤ N.height := N.height_lower; Eq.mpr (id rfl) (Eq.mp (congrArg (LT.lt (↑a0 :
        ℕ)) (Nat.sub_add_cancel (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ N.height) =>
    by omega
    ))) ha)⟩ : Fin N.height); gamma ∈ MissingColors G phi (T.vertex (Fin.castLE N.height_upper
        gammaBase)) →
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (_ : Fin
        ((↑secondTail : ℕ) + (1 : ℕ))),
    let X : Finset V := TreeSequenceVertexSet T;
    let yzero : V := T.vertex (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yone : V := T.vertex (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let ygamma : V := T.vertex (Fin.castLE N.height_upper gammaBase); yzero ∈ X → yone ∈ X →
        ygamma ∈ X → yzero ≠ yone → Incident G yzero e0 → Incident G yone e0 →
        ColoredVertexSetElementary G phi X → (
    ∀ {v : V}, v ∈ X →
    ∀ {c : Fin k}, c ∈ MissingColors G phi v → c ≠ N.alpha → c ≠ N.beta → c ≠ gamma → c ∈
        TreeFreeColors phi T) →
    ∀ v ∈ X, v ≠ ygamma →
    ∃ c ∈ MissingColors G phi v, c ∈ TreeFreeColors phi T := by
  classical
  intro V E _ _ _ G k e0 phi T N this hcard horder hlength firstTail secondTail a0 gamma
      gammaBase hgammaMissing m hm i0 i1 _ P base1raw X yzero yone ygamma hyzero hyone hygamma
      hyzero_ne_yone hinczero hincone helem color_is_free v hv hvGamma
  by_cases hv0 : v = yzero
  · subst v
    have hm := (ScheideGlobalMaximumMissingCounts G k e0 phi T N.global
      yzero (by simpa [X] using hyzero)).1 hinczero
    obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne hm.2 N.alpha
    have hcb : c ≠ N.beta := by
      intro h
      have hd := helem hyzero hyone hyzero_ne_yone
      exact (Finset.disjoint_left.mp hd) hc
        (by simpa [h, yone] using N.beta_missing)
    have hcg : c ≠ gamma := by
      intro h
      have hd := helem hyzero hygamma hvGamma
      exact (Finset.disjoint_left.mp hd) hc
        (by simpa [h, ygamma] using hgammaMissing)
    exact ⟨c, hc, color_is_free hyzero hc hca hcb hcg⟩
  · by_cases hv1 : v = yone
    · subst v
      have hm := (ScheideGlobalMaximumMissingCounts G k e0 phi T N.global
        yone (by simpa [X] using hyone)).1 hincone
      obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne hm.2 N.beta
      have hca : c ≠ N.alpha := by
        intro h
        have hd := helem hyone hyzero hyzero_ne_yone.symm
        exact (Finset.disjoint_left.mp hd) hc
          (by simpa [h, yzero] using N.alpha_missing)
      have hcg : c ≠ gamma := by
        intro h
        have hd := helem hyone hygamma hvGamma
        exact (Finset.disjoint_left.mp hd) hc
          (by simpa [h, ygamma] using hgammaMissing)
      exact ⟨c, hc, color_is_free hyone hc hca hcb hcg⟩
    · have hmissing : 1 ≤ (MissingColors G phi v).card := by
        have hm := ScheideGlobalMaximumMissingCounts G k e0 phi T N.global
          v (by simpa [X] using hv)
        by_cases hi : Incident G v e0
        · have htwo := (hm.1 hi).2
          omega
        · exact (hm.2 hi).2
      obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega :
        0 < (MissingColors G phi v).card)
      have hca : c ≠ N.alpha := by
        intro h
        have hd := helem hv hyzero hv0
        exact (Finset.disjoint_left.mp hd) hc
          (by simpa [h, yzero] using N.alpha_missing)
      have hcb : c ≠ N.beta := by
        intro h
        have hd := helem hv hyone hv1
        exact (Finset.disjoint_left.mp hd) hc
          (by simpa [h, yone] using N.beta_missing)
      have hcg : c ≠ gamma := by
        intro h
        have hd := helem hv hygamma hvGamma
        exact (Finset.disjoint_left.mp hd) hc
          (by simpa [h, ygamma] using hgammaMissing)
      exact ⟨c, hc, color_is_free hv hc hca hcb hcg⟩

private theorem helper_path_length_contradiction_328.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T), BalancedGlobalMaximumTriple N →
        ScheideGraphHeight G + (2 : ℕ) = TashkinovOrder G →
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hcard : (TreeSequenceVertexSet T).card = T.length + (1 : ℕ)) (horder : TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ)
        = N.height + (2 : ℕ)),
    let firstNew : Fin (T.length + (1 : ℕ)) := (⟨N.height,
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (P : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), P.IsPath → (4 : ℕ)
        ∣ P.length → P.length / (2 : ℕ) + (1 : ℕ) ≤ ScheideGraphHeight G → (
    ∀ {z : V ⊕ E}, z ∈ N.closingPath.support → z ∈ P.support) → Sum.inl (T.vertex firstNew) ∉
        N.closingPath.support → Sum.inl (T.vertex firstNew) ∈ P.support → False := by
  classical
  intro V E _ _ _ G k e0 phi T N hbalanced hheight this hcard horder hlength firstNew m hm i0 i1
      _ P hPpath hPdiv hPbound closing_mem_P hfirstNewNotClosing hnew
  let S : Finset (Sum V E) :=
    insert (Sum.inl (T.vertex firstNew)) N.closingPath.support.toFinset
  have hSsub : S ⊆ P.support.toFinset := by
    intro z hz
    simp only [S, Finset.mem_insert, List.mem_toFinset] at hz ⊢
    rcases hz with rfl | hz
    · exact hnew
    · exact closing_mem_P hz
  have hScard : S.card = N.closingPath.length + 2 := by
    rw [show S = insert (Sum.inl (T.vertex firstNew))
        N.closingPath.support.toFinset by rfl,
      Finset.card_insert_of_notMem (by
        simpa only [List.mem_toFinset] using hfirstNewNotClosing),
      List.toFinset_card_of_nodup N.closingPath_isPath.support_nodup,
      SimpleGraph.Walk.length_support]
  have hc := Finset.card_le_card hSsub
  rw [hScard, List.toFinset_card_of_nodup hPpath.support_nodup,
    SimpleGraph.Walk.length_support] at hc
  rcases hPdiv with ⟨d, hd⟩
  have hbound : P.length / 2 + 1 ≤ N.height := by
    rw [hbalanced.1]
    exact hPbound
  have hcloseLength := N.closingPath_length
  omega

private theorem helper_hbase1lt_366.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)),
    let firstTail : Fin T.length := (⟨N.height - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    let firstNew : Fin (T.length + (1 : ℕ)) := (⟨N.height,
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (gamma : Fin k), phi (T.edge firstTail) = some gamma →
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)), phi (T.edge secondTail) = some gamma →
    ∀ (base0raw : Fin ((↑firstTail : ℕ) + (1 : ℕ))),
    let base0 : Fin N.height := (⟨(↑base0raw : ℕ),
    have hb : (↑base0raw : ℕ) < (↑firstTail : ℕ) + (1 : ℕ) := base0raw.isLt;
    have hh : (2 : ℕ) ≤ N.height := N.height_lower; Eq.mpr (id rfl) (Eq.mp (congrArg (LT.lt
        (↑base0raw : ℕ)) (Nat.sub_add_cancel (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        N.height) =>
    by omega
    ))) hb)⟩ : Fin N.height); G.ends (T.edge firstTail) = s(T.vertex (Fin.castLE N.height_upper
        base0), T.vertex firstNew) →
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (base1raw : Fin
        ((↑secondTail : ℕ) + (1 : ℕ))), G.ends (T.edge secondTail) = s(T.vertex secondTail.succ,
        T.vertex (base1raw.castLT (Nat.lt_trans base1raw.isLt (Nat.succ_lt_succ
        secondTail.isLt)))) → (↑base1raw : ℕ) < N.height := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength firstTail secondTail firstNew gamma
      hfirstColor m hm hsecondColor base0raw base0 hfirstEnds i0 i1 _ P base1raw hbase1raw
  by_contra hn
  have heq : base1raw.val = N.height := by
    have hb := base1raw.isLt
    simp [secondTail] at hb
    omega
  have hinc0 : Incident G (T.vertex firstNew) (T.edge firstTail) := by
    simp [Incident, hfirstEnds]
  have hcast : T.vertex (Fin.castLT base1raw
      (Nat.lt_trans base1raw.isLt
        (Nat.succ_lt_succ secondTail.isLt))) = T.vertex firstNew := by
    apply congrArg T.vertex
    apply Fin.ext
    exact heq
  have hinc1 : Incident G (T.vertex firstNew) (T.edge secondTail) := by
    unfold Incident
    rw [hbase1raw]
    simp [hcast]
  have hne : T.edge firstTail ≠ T.edge secondTail := by
    intro he
    have hi := T.edge_injective he
    have hiv := congrArg Fin.val hi
    simp [firstTail, secondTail] at hiv
    omega
  exact (N.global.1.2.2.2.1 hne ⟨T.vertex firstNew, hinc0, hinc1⟩
    hfirstColor) hsecondColor

private theorem helper_hfirstEnds_388.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)),
    let firstTail : Fin T.length := (⟨N.height - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let firstNew : Fin (T.length + (1 : ℕ)) := (⟨N.height,
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)) (base0raw : Fin ((↑firstTail : ℕ) + (1 :
        ℕ))), G.ends (T.edge firstTail) = s(T.vertex firstTail.succ, T.vertex (base0raw.castLT
        (Nat.lt_trans base0raw.isLt (Nat.succ_lt_succ firstTail.isLt)))) →
    let base0 : Fin N.height := (⟨(↑base0raw : ℕ),
    have hb : (↑base0raw : ℕ) < (↑firstTail : ℕ) + (1 : ℕ) := base0raw.isLt;
    have hh : (2 : ℕ) ≤ N.height := N.height_lower; Eq.mpr (id rfl) (Eq.mp (congrArg (LT.lt
        (↑base0raw : ℕ)) (Nat.sub_add_cancel (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        N.height) =>
    by omega
    ))) hb)⟩ : Fin N.height); G.ends (T.edge firstTail) = s(T.vertex (Fin.castLE N.height_upper
        base0), T.vertex firstNew) := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength firstTail firstNew m hm base0raw hbase0raw
      base0
  calc
    G.ends (T.edge firstTail) =
        s(T.vertex firstTail.succ,
          T.vertex (Fin.castLT base0raw
            (Nat.lt_trans base0raw.isLt
              (Nat.succ_lt_succ firstTail.isLt)))) := hbase0raw
    _ = s(T.vertex firstNew,
          T.vertex (Fin.castLE N.height_upper base0)) := by
        congr 2; apply Fin.ext; simp [firstTail, firstNew]; omega
    _ = s(T.vertex (Fin.castLE N.height_upper base0),
          T.vertex firstNew) := Sym2.eq_swap

private theorem helper_closing_mem_P_419.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)) (m : ℕ) (hm
        : N.height = (2 : ℕ) * m + (1 : ℕ)),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (P : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi N.alpha N.beta;
    let C : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl (T.vertex i0));
        {z : V ⊕ E | z ∈ P.support} = C →
    ∀ {z : V ⊕ E}, z ∈ N.closingPath.support → z ∈ P.support := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength m hm i0 i1 _ P H C hPspan' z hz
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hr : H.Reachable z (Sum.inl (T.vertex i0)) := by
    have hd := (N.closingPath.drop n).reachable
    rw [← hn]
    simpa [H, i0] using hd
  have hzC : z ∈ C := by
    change H.connectedComponentMk z =
      H.connectedComponentMk (Sum.inl (T.vertex i0))
    exact SimpleGraph.ConnectedComponent.sound hr
  change z ∈ {w | w ∈ P.support}
  rw [hPspan']
  exact hzC

private theorem helper_first_new_mem_P_449.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)),
    let firstTail : Fin T.length := (⟨N.height - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let firstNew : Fin (T.length + (1 : ℕ)) := (⟨N.height,
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)) (base0raw : Fin ((↑firstTail : ℕ) + (1 :
        ℕ))),
    let base0 : Fin N.height := (⟨(↑base0raw : ℕ),
    have hb : (↑base0raw : ℕ) < (↑firstTail : ℕ) + (1 : ℕ) := base0raw.isLt;
    have hh : (2 : ℕ) ≤ N.height := N.height_lower; Eq.mpr (id rfl) (Eq.mp (congrArg (LT.lt
        (↑base0raw : ℕ)) (Nat.sub_add_cancel (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        N.height) =>
    by omega
    ))) hb)⟩ : Fin N.height); G.ends (T.edge firstTail) = s(T.vertex (Fin.castLE N.height_upper
        base0), T.vertex firstNew) →
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (P : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi N.alpha N.beta;
    let C : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl (T.vertex i0));
        {z : V ⊕ E | z ∈ P.support} = C → Sum.inl (T.vertex (Fin.castLE N.height_upper base0)) ∈ C
        → (
    ∀ {x z : V ⊕ E}, x ∈ C → H.Adj x z → z ∈ C) → phi (T.edge firstTail) = some N.alpha ∨ phi
        (T.edge firstTail) = some N.beta → Sum.inl (T.vertex firstNew) ∈ P.support := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength firstTail firstNew m hm base0raw base0
      hfirstEnds i0 i1 _ P H C hPspan' hrootC C_of_adj hc
  have hbaseEdge : H.Adj
      (Sum.inl (T.vertex (Fin.castLE N.height_upper base0)))
      (Sum.inr (T.edge firstTail)) := by
    simp [H, TwoColorIncidenceGraph, Incident, hfirstEnds, hc]
  have hedgeC : Sum.inr (T.edge firstTail) ∈ C :=
    C_of_adj hrootC hbaseEdge
  have hedgeNew : H.Adj (Sum.inr (T.edge firstTail))
      (Sum.inl (T.vertex firstNew)) := by
    simp [H, TwoColorIncidenceGraph, Incident, hfirstEnds, hc]
  have hnewC := C_of_adj hedgeC hedgeNew
  change Sum.inl (T.vertex firstNew) ∈ {w | w ∈ P.support}
  rw [hPspan']
  exact hnewC

private theorem helper_hsecondEnds_493.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hlength : T.length + (1 : ℕ) =
        N.height + (2 : ℕ)),
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    let secondNew : Fin (T.length + (1 : ℕ)) := (⟨N.height + (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (base1raw : Fin ((↑secondTail : ℕ) + (1 : ℕ))), G.ends (T.edge secondTail) = s(T.vertex
        secondTail.succ, T.vertex (base1raw.castLT (Nat.lt_trans base1raw.isLt (Nat.succ_lt_succ
        secondTail.isLt)))) →
    ∀ (hbase1lt : (↑base1raw : ℕ) < N.height),
    let base1 : Fin N.height := (⟨(↑base1raw : ℕ), hbase1lt⟩ : Fin N.height); G.ends (T.edge
        secondTail) = s(T.vertex (Fin.castLE N.height_upper base1), T.vertex secondNew) := by
  classical
  intro V E _ _ _ G k e0 phi T N hlength secondTail secondNew base1raw hbase1raw hbase1lt base1
  calc
    G.ends (T.edge secondTail) =
        s(T.vertex secondTail.succ,
          T.vertex (Fin.castLT base1raw
            (Nat.lt_trans base1raw.isLt
              (Nat.succ_lt_succ secondTail.isLt)))) := hbase1raw
    _ = s(T.vertex secondNew,
          T.vertex (Fin.castLE N.height_upper base1)) := by
        congr 2
    _ = s(T.vertex (Fin.castLE N.height_upper base1),
          T.vertex secondNew) := Sym2.eq_swap

private theorem helper_edge_color_of_closing_support_507.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)),
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (_ : Fin
        ((↑secondTail : ℕ) + (1 : ℕ))) (f : E), Sum.inr f ∈ N.closingPath.support → phi f = some
        N.alpha ∨ phi f = some N.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength secondTail m hm i0 i1 _ P base1raw f hf
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
  have hnlt : n < N.closingPath.length := by
    by_contra hnl
    have hend := N.closingPath.getVert_of_length_le (i := n) (by omega)
    rw [hn] at hend
    simp at hend
  have hadj := N.closingPath.adj_getVert_succ hnlt
  rw [hn] at hadj
  cases hz : N.closingPath.getVert (n + 1) with
  | inl v =>
      rw [hz] at hadj
      simpa [TwoColorIncidenceGraph] using hadj.2
  | inr e =>
      rw [hz] at hadj
      simp [TwoColorIncidenceGraph] at hadj

private theorem helper_used_color_cases_532.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)),
    let firstTail : Fin T.length := (⟨N.height - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    ∀ (gamma : Fin k), phi (T.edge firstTail) = some gamma →
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)), phi (T.edge secondTail) = some gamma →
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (_ : Fin
        ((↑secondTail : ℕ) + (1 : ℕ))), (
    ∀ (j : Fin T.length), (1 : ℕ) ≤ (↑j : ℕ) → (↑j : ℕ) + (2 : ℕ) ≤ N.height → phi (T.edge j) =
        some N.alpha ∨ phi (T.edge j) = some N.beta) →
    ∀ {c : Fin k} (j : Fin T.length), (1 : ℕ) ≤ (↑j : ℕ) → phi (T.edge j) = some c → c = N.alpha ∨
        c = N.beta ∨ c = gamma := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength firstTail secondTail gamma hfirstColor m hm
      hsecondColor i0 i1 _ P base1raw base_nonfirst_color c j hj hc
  by_cases htrunk : j.val + 2 ≤ N.height
  · rcases base_nonfirst_color j hj htrunk with h | h
    · exact Or.inl (Option.some.inj (hc.symm.trans h))
    · exact Or.inr (Or.inl (Option.some.inj (hc.symm.trans h)))
  · have hjbound := j.isLt
    have hcases : j.val = N.height - 1 ∨ j.val = N.height := by
      simp [] at hjbound
      omega
    rcases hcases with h | h
    · have he : j = firstTail := by apply Fin.ext; simpa [firstTail]
      subst j
      exact Or.inr (Or.inr (Option.some.inj (hc.symm.trans hfirstColor)))
    · have he : j = secondTail := by apply Fin.ext; simpa [secondTail]
      subst j
      exact Or.inr (Or.inr (Option.some.inj (hc.symm.trans hsecondColor)))

private theorem helper_hfirstEdgeEnds_562.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)),
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (_ : Fin
        ((↑secondTail : ℕ) + (1 : ℕ))),
    let yzero : V := T.vertex (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yone : V := T.vertex (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); G.ends e0 = s(yone, yzero) := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength secondTail m hm i0 i1 _ P base1raw yzero yone
  obtain ⟨q, hq⟩ := T.attaches ⟨0, T.positive⟩
  have hq0 : q = 0 := Fin.eq_zero q
  subst q
  rw [T.first_edge] at hq
  have hsucc : (⟨0, T.positive⟩ : Fin T.length).succ =
      (⟨1, by omega⟩ : Fin (T.length + 1)) := by
    apply Fin.ext
    rfl
  have hcast : Fin.castLT (0 : Fin 1)
      (Nat.lt_trans (0 : Fin 1).isLt
        (Nat.succ_lt_succ (⟨0, T.positive⟩ : Fin T.length).isLt)) =
      (⟨0, by omega⟩ : Fin (T.length + 1)) := by
    apply Fin.ext
    rfl
  simpa [yzero, yone, hsucc, hcast] using hq

private theorem helper_color_is_free_590.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (gamma : Fin k), (
    ∀ {c : Fin k} (j : Fin T.length), (1 : ℕ) ≤ (↑j : ℕ) → phi (T.edge j) = some c → c = N.alpha ∨
        c = N.beta ∨ c = gamma) →
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ {v : V}, v ∈ X →
    ∀ {c : Fin k}, c ∈ MissingColors G phi v → c ≠ N.alpha → c ≠ N.beta → c ≠ gamma → c ∈
        TreeFreeColors phi T := by
  classical
  intro V E _ _ _ G k e0 phi T N gamma used_color_cases X v hv c hc hca hcb hcg
  apply Finset.mem_sdiff.mpr
  constructor
  · simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v, by simpa [X] using hv, hc⟩
  · intro hu
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hu
    obtain ⟨j, hj, hcol⟩ := hu
    rcases used_color_cases j hj hcol with h | h | h
    · exact hca h
    · exact hcb h
    · exact hcg h

private theorem helper_hexit_609.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hcard : (TreeSequenceVertexSet T).card = T.length + (1 : ℕ)) (horder : TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ)
        = N.height + (2 : ℕ)),
    let firstTail : Fin T.length := (⟨N.height - (1 : ℕ),
    by omega
    ⟩ : Fin T.length);
    ∀ (a0 : Fin ((↑firstTail : ℕ) + (1 : ℕ))) (gamma : Fin k),
    let gammaBase : Fin N.height := (⟨(↑a0 : ℕ),
    have ha : (↑a0 : ℕ) < (↑firstTail : ℕ) + (1 : ℕ) := a0.isLt;
    have hh : (2 : ℕ) ≤ N.height := N.height_lower; Eq.mpr (id rfl) (Eq.mp (congrArg (LT.lt (↑a0 :
        ℕ)) (Nat.sub_add_cancel (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ N.height) => (
    by omega
    )))) ha)⟩ : Fin N.height); gamma ∈ MissingColors G phi (T.vertex (Fin.castLE N.height_upper
        gammaBase)) →
    let X : Finset V := TreeSequenceVertexSet T;
    let ygamma : V := T.vertex (Fin.castLE N.height_upper gammaBase); (
    ∀ v ∈ X, v ≠ ygamma →
    ∃ c ∈ MissingColors G phi v, c ∈ TreeFreeColors phi T) →
    ∀ v ∈ ScheideExitVertices T phi, gamma ∈ MissingColors G phi v := by
  classical
  intro V E _ _ _ G k e0 phi T N this hcard horder hlength firstTail a0 gamma gammaBase
      hgammaMissing X ygamma free_of_ne_gamma v hvExit
  have hExit : ScheideExitVertex T phi v := by
    simpa [ScheideExitVertices] using hvExit
  obtain ⟨u, c, d, hu, hc, hd, z, p, hp, i, hi, hv, hafter⟩ := hExit
  have hvX : v ∈ X := by simpa [X] using hv
  by_contra hn
  have hvne : v ≠ ygamma := by
    intro h
    subst v
    exact hn (by simpa [ygamma] using hgammaMissing)
  obtain ⟨c', hc', hfree⟩ := free_of_ne_gamma v hvX hvne
  have hdis := ScheideExitNoFree G k e0 phi T N.global v hvExit
  exact (Finset.disjoint_left.mp hdis) hc' hfree

private theorem helper_branch_677.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hcard : (TreeSequenceVertexSet T).card
        = T.length + (1 : ℕ)) (horder : TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 :
        ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T)) (hlength : T.length + (1 : ℕ) = N.height + (2 : ℕ)),
    let secondTail : Fin T.length := (⟨N.height,
    by omega
    ⟩ : Fin T.length);
    let secondNew : Fin (T.length + (1 : ℕ)) := (⟨N.height + (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (m : ℕ) (hm : N.height = (2 : ℕ) * m + (1 : ℕ)),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (base1raw : Fin
        ((↑secondTail : ℕ) + (1 : ℕ))) (hbase1lt : (↑base1raw : ℕ) < N.height),
    let base1 : Fin N.height := (⟨(↑base1raw : ℕ), hbase1lt⟩ : Fin N.height); G.ends (T.edge
        secondTail) = s(T.vertex (Fin.castLE N.height_upper base1), T.vertex secondNew) →
    ∃ (q : Fin N.height), G.ends (T.edge (⟨N.height - (1 : ℕ) + (↑(1 : Fin (2 : ℕ)) : ℕ),
    by
              have _ : (↑(1 : Fin (2 : ℕ)) : ℕ) < (2 : ℕ) := Fin.isLt (1 : Fin (2 : ℕ));
              omega
    ⟩ : Fin T.length)) = s(T.vertex (Fin.castLE N.height_upper q), T.vertex (⟨N.height + (↑(1 :
        Fin (2 : ℕ)) : ℕ),
    by
              have _ : (↑(1 : Fin (2 : ℕ)) : ℕ) < (2 : ℕ) := Fin.isLt (1 : Fin (2 : ℕ));
              omega
    ⟩ : Fin (T.length + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 phi T N hcard horder hlength secondTail secondNew m hm i0 i1 _ P
      base1raw hbase1lt base1 hsecondEnds
  refine ⟨base1, ?_⟩
  have hedge : (⟨N.height - 1 + 1, by omega⟩ : Fin T.length) =
      secondTail := by
    apply Fin.ext
    simp [secondTail]
    omega
  have hvertex : (⟨N.height + 1, by omega⟩ : Fin (T.length + 1)) =
      secondNew := by
    apply Fin.ext
    rfl
  norm_num at ⊢
  rw [hedge, hvertex]
  exact hsecondEnds

private theorem helper_continuation_929.{u_1, u_2} :
    helperContinuation929Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hbalanced hnoisolated hheight this hcard horder hlength
      firstTail secondTail firstNew secondNew a0 gamma hfirstColor gammaBase hgammaMissing m hm
      hsecondColor base0raw base0 hfirstEnds i0 i1 _ _ _ _ _ _ P hPpath hPdiv _ hPbound
      closing_mem_P first_new_mem_P hfirstNewNotClosing
  have path_length_contradiction
      (hnew : Sum.inl (T.vertex firstNew) ∈ P.support) : False := by
    exact @helper_path_length_contradiction_328 V E inferInstance inferInstance inferInstance G k
        e0 phi T N hbalanced hheight hcard horder hlength m hm (by assumption) P hPpath hPdiv
        hPbound closing_mem_P hfirstNewNotClosing hnew
  have hgammaAlpha : gamma ≠ N.alpha := by
    intro h
    apply path_length_contradiction
    apply first_new_mem_P
    exact Or.inl (by simpa [h] using hfirstColor)
  have hgammaBeta : gamma ≠ N.beta := by
    intro h
    apply path_length_contradiction
    apply first_new_mem_P
    exact Or.inr (by simpa [h] using hfirstColor)
  obtain ⟨base1raw, hbase1raw⟩ := T.attaches secondTail
  have hbase1lt : base1raw.val < N.height := by
    exact @helper_hbase1lt_366 V E inferInstance inferInstance inferInstance G k e0 phi T N hcard
        horder hlength gamma hfirstColor m hm hsecondColor base0raw hfirstEnds (by assumption) P
        base1raw hbase1raw
  let base1 : Fin N.height := ⟨base1raw.val, hbase1lt⟩
  have hsecondEnds := @helper_hsecondEnds_493 V E inferInstance inferInstance inferInstance G k e0
      phi T N hlength base1raw hbase1raw hbase1lt
  have edge_color_of_closing_support (f : E)
      (hf : Sum.inr f ∈ N.closingPath.support) :
      phi f = some N.alpha ∨ phi f = some N.beta := by
    exact @helper_edge_color_of_closing_support_507 V E inferInstance inferInstance inferInstance
        G k e0 phi T N hcard horder hlength m hm (by assumption) P base1raw f hf
  have base_nonfirst_color (j : Fin T.length)
      (hj : 1 ≤ j.val) (hjh : j.val + 2 ≤ N.height) :
      phi (T.edge j) = some N.alpha ∨ phi (T.edge j) = some N.beta := by
    apply edge_color_of_closing_support
    apply (N.closingPath_edges (T.edge j)).2
    exact Or.inr ⟨j, hj, hjh, rfl⟩
  have used_color_cases {c : Fin k} (j : Fin T.length) (hj : 1 ≤ j.val)
      (hc : phi (T.edge j) = some c) :
      c = N.alpha ∨ c = N.beta ∨ c = gamma := by
    exact @helper_used_color_cases_532 V E inferInstance inferInstance inferInstance G k e0 phi T
        N hcard horder hlength gamma hfirstColor m hm hsecondColor (by assumption) P base1raw
        base_nonfirst_color c j hj hc
  let X := TreeSequenceVertexSet T
  let yzero : V := T.vertex ⟨0, by omega⟩
  let yone : V := T.vertex ⟨1, by omega⟩
  let ygamma : V := T.vertex (Fin.castLE N.height_upper gammaBase)
  have hyzero : yzero ∈ X := by simp [yzero, X, TreeSequenceVertexSet]
  have hyone : yone ∈ X := by simp [yone, X, TreeSequenceVertexSet]
  have hygamma : ygamma ∈ X := by simp [ygamma, X, TreeSequenceVertexSet]
  have hyzero_ne_yone : yzero ≠ yone := by
    intro h
    have hi := T.vertex_injective h
    simp [] at hi
  have hfirstEdgeEnds : G.ends e0 = s(yone, yzero) := by
    exact @helper_hfirstEdgeEnds_562 V E inferInstance inferInstance inferInstance G k e0 phi T N
        hcard horder hlength m hm (by assumption) P base1raw
  have hinczero : Incident G yzero e0 := by
    unfold Incident
    rw [hfirstEdgeEnds]
    simp
  have hincone : Incident G yone e0 := by
    unfold Incident
    rw [hfirstEdgeEnds]
    simp
  have helem : ColoredVertexSetElementary G phi X := by
    intro u hu v hv huv
    exact horder.2.2.2.1 (by simpa [X] using hu)
      (by simpa [X] using hv) huv
  have color_is_free := @helper_color_is_free_590 V E inferInstance inferInstance inferInstance G k
      e0 phi T N gamma used_color_cases
  have free_of_ne_gamma : ∀ v ∈ X, v ≠ ygamma →
      ∃ c, c ∈ MissingColors G phi v ∧ c ∈ TreeFreeColors phi T := by
    exact @helper_free_of_ne_gamma_377 V E inferInstance inferInstance inferInstance G k e0 phi T
        N hcard horder hlength a0 gamma hgammaMissing m hm (by assumption) P base1raw hyzero
        hyone hygamma hyzero_ne_yone hinczero hincone helem color_is_free
  have hexit := @helper_hexit_609 V E inferInstance inferInstance inferInstance G k e0 phi T N hcard
      horder hlength a0 gamma hgammaMissing free_of_ne_gamma
  let Config : ScheideStructuralConfiguration G k e0 phi T := {
    p := N.height
    s := 1
    p_ge_two := N.height_lower
    gamma := fun _ => gamma
    gamma_injective := fun a b _ => Subsingleton.elim a b
    y := fun i => T.vertex (Fin.castLE N.height_upper i)
    baseEdge := fun i => T.edge ⟨i.val, by
      have hi := i.isLt
      omega⟩
    blockVertex := fun _ j => T.vertex ⟨N.height + j.val, by
      have hj := j.isLt
      omega⟩
    blockEdge := fun _ j => T.edge ⟨N.height - 1 + j.val, by
      have hj := j.isLt
      omega⟩
    length_eq := by simpa using hlength
    base_vertex_position := by
      intro i
      rfl
    block_vertex_position := by
      intro i j
      apply congrArg T.vertex
      apply Fin.ext
      have hi := i.isLt
      have hiz : i.val = 0 := by omega
      simp []
    base_edge_position := by
      intro i
      rfl
    block_edge_position := by
      intro i j
      apply congrArg T.edge
      apply Fin.ext
      have hi := i.isLt
      have hiz : i.val = 0 := by omega
      simp []
    block_attaches_to_base := by
      intro i j
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      have hj : j = 0 ∨ j = 1 := by
        by_cases hz : j.val = 0
        · left
          apply Fin.ext
          exact hz
        · right
          apply Fin.ext
          have hjlt := j.isLt
          omega
      rcases hj with rfl | rfl
      · exact ⟨base0, by simpa [firstTail, firstNew] using hfirstEnds⟩
      · exact @helper_branch_677 V E inferInstance inferInstance inferInstance G k e0 phi T N
          hcard horder hlength m hm (by assumption) P base1raw hbase1lt hsecondEnds
    block_color := by
      intro i j
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      have hj : j = 0 ∨ j = 1 := by
        by_cases hz : j.val = 0
        · left
          apply Fin.ext
          exact hz
        · right
          apply Fin.ext
          have hjlt := j.isLt
          omega
      rcases hj with rfl | rfl
      · simpa [firstTail] using hfirstColor
      · convert hsecondColor using 1
        apply congrArg phi
        apply congrArg T.edge
        apply Fin.ext
        simp [secondTail]
        omega
    block_color_missing_on_base := by
      intro i
      exact ⟨gammaBase, hgammaMissing⟩
    initial_nonfirst_avoids_blocks := by
      intro i hi c hc r
      let j : Fin T.length := ⟨i.val, by
        have hil := i.isLt
        omega⟩
      have hjh : j.val + 2 ≤ N.height := by
        have hil := i.isLt
        simp [j]
        omega
      have hcol : phi (T.edge j) = some N.alpha ∨
          phi (T.edge j) = some N.beta := base_nonfirst_color j hi hjh
      have heq : T.edge j = T.edge ⟨i.val, by
          have hil := i.isLt
          omega⟩ := by
        apply congrArg T.edge
        apply Fin.ext
        rfl
      rw [heq, hc] at hcol
      rcases hcol with h | h
      · have : c = N.alpha := Option.some.inj h
        simpa [this] using hgammaAlpha.symm
      · have : c = N.beta := Option.some.inj h
        simpa [this] using hgammaBeta.symm
    exit_covered := by
      intro v hv
      exact ⟨0, hexit v hv⟩
    no_isolated := hnoisolated
    globally_maximum := N.global
  }
  exact ScheideStructuralLemma G k e0 phi T Config

theorem ScheideLargeHeightOneTailPair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hheight : ScheideGraphHeight G + 2 = TashkinovOrder G) :
    Elementary G := by
  classical
  let : DecidableEq V := Classical.decEq V
  have hcard : (TreeSequenceVertexSet T).card = T.length + 1 := by
    unfold TreeSequenceVertexSet
    rw [Finset.card_image_iff.mpr (by
      intro a ha b hb hab
      exact T.vertex_injective hab)]
    simp
  have horder := ScheideGlobalMaximumOrder G k e0 phi T N.global
  have hlength : T.length + 1 = N.height + 2 := by
    calc
      T.length + 1 = (TreeSequenceVertexSet T).card := hcard.symm
      _ = TashkinovOrder G := N.global.2.2
      _ = ScheideGraphHeight G + 2 := hheight.symm
      _ = N.height + 2 := by rw [hbalanced.1]
  have hodd : Odd N.height := by
    rw [hbalanced.1]
    exact (ScheideGraphHeightOdd G k e0 phi T N.global).2
  let firstTail : Fin T.length := ⟨N.height - 1, by omega⟩
  let secondTail : Fin T.length := ⟨N.height, by omega⟩
  let firstNew : Fin (T.length + 1) := ⟨N.height, by omega⟩
  let secondNew : Fin (T.length + 1) := ⟨N.height + 1, by omega⟩
  obtain ⟨a0, gamma, hfirstColor, hgammaMissing0⟩ :=
    N.global.2.1 firstTail (by
      have hh := N.height_lower
      simp [firstTail]
      omega)
  let gammaBase : Fin N.height := ⟨a0.val, by
    have ha := a0.isLt
    have hh := N.height_lower
    simpa [firstTail, Nat.sub_add_cancel (by omega : 1 ≤ N.height)] using ha⟩
  have hgammaMissing : gamma ∈ MissingColors G phi
      (T.vertex (Fin.castLE N.height_upper gammaBase)) := by
    have hi : Fin.castLE N.height_upper gammaBase =
        Fin.castLT a0
          (Nat.lt_trans a0.isLt (Nat.succ_lt_succ firstTail.isLt)) := by
      apply Fin.ext
      rfl
    rw [hi]
    exact hgammaMissing0
  rcases hodd with ⟨m, hm⟩
  have hpair := hbalanced.2 (m + 1) (by omega) (by omega)
  have hsecondColor : phi (T.edge secondTail) = some gamma := by
    have hpair' : phi (T.edge firstTail) = phi (T.edge secondTail) := by
      convert hpair using 1 <;> apply congrArg phi <;> apply congrArg T.edge <;>
        apply Fin.ext <;> simp [firstTail, secondTail] <;> omega
    rw [hpair'] at hfirstColor
    exact hfirstColor
  obtain ⟨base0raw, hbase0raw⟩ := T.attaches firstTail
  let base0 : Fin N.height := ⟨base0raw.val, by
    have hb := base0raw.isLt
    have hh := N.height_lower
    simpa [firstTail, Nat.sub_add_cancel (by omega : 1 ≤ N.height)] using hb⟩
  have hfirstEnds := @helper_hfirstEnds_388 V E inferInstance inferInstance inferInstance G k e0 phi
      T N hcard horder hlength m hm base0raw hbase0raw
  have hfixed : FixedPairMaximalTashkinovTree G e0 phi T :=
    ScheideGlobalMaximumFixedPairMaximal G k e0 phi T N.global
  let i0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (T.length + 1) := ⟨1, by omega⟩
  obtain ⟨hab, _, _, _, _, _, _⟩ :=
    ScheideMaximalKempePath G k e0 phi T T N.global.1 hfixed N.global.2.1
      i0 i1 (by simp [i0, i1]) N.alpha N.beta
      (by simpa [i0] using N.alpha_missing)
      (by simpa [i1] using N.beta_missing)
  obtain ⟨P, hPpath, hPspan, hPdiv, _, hPbound⟩ :=
    ScheideKempePathHeightBound G k e0 phi T N.global N.alpha N.beta
      N.alpha_missing N.beta_missing
  let H := TwoColorIncidenceGraph G phi N.alpha N.beta
  let C := TwoColorComponent G phi N.alpha N.beta
    (Sum.inl (T.vertex i0))
  have hPspan' : {z | z ∈ P.support} = C := by
    simpa [C, i0] using hPspan
  have closing_mem_P {z : Sum V E} (hz : z ∈ N.closingPath.support) :
      z ∈ P.support := by
    exact @helper_closing_mem_P_419 V E inferInstance inferInstance inferInstance G k e0 phi T N
        hcard horder hlength m hm (by assumption) P hPspan' z hz
  have hbase0Closing :
      Sum.inl (T.vertex (Fin.castLE N.height_upper base0)) ∈
        N.closingPath.support := by
    apply (N.closingPath_vertices _).2
    exact ⟨base0, rfl⟩
  have hrootC : Sum.inl (T.vertex (Fin.castLE N.height_upper base0)) ∈ C := by
    rw [← hPspan']
    exact closing_mem_P hbase0Closing
  have C_of_adj {x z : Sum V E} (hx : x ∈ C) (hxz : H.Adj x z) : z ∈ C := by
    change H.connectedComponentMk x =
        H.connectedComponentMk (Sum.inl (T.vertex i0)) at hx
    change H.connectedComponentMk z =
      H.connectedComponentMk (Sum.inl (T.vertex i0))
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hxz).symm.trans hx
  have first_new_mem_P
      (hc : phi (T.edge firstTail) = some N.alpha ∨
        phi (T.edge firstTail) = some N.beta) :
      Sum.inl (T.vertex firstNew) ∈ P.support := by
    exact @helper_first_new_mem_P_449 V E inferInstance inferInstance inferInstance G k e0 phi T
        N hcard horder hlength m hm base0raw hfirstEnds (by assumption) P hPspan' hrootC C_of_adj hc
  have hfirstNewNotClosing :
      Sum.inl (T.vertex firstNew) ∉ N.closingPath.support := by
    intro hmem
    obtain ⟨q, hq⟩ := (N.closingPath_vertices (T.vertex firstNew)).1 hmem
    have hi := T.vertex_injective hq
    have hqv := q.isLt
    have hiv := congrArg Fin.val hi
    simp [firstNew] at hiv
    omega
  exact @helper_continuation_929 V E inferInstance inferInstance inferInstance G k e0 phi T N
      hbalanced hnoisolated hheight hcard horder hlength a0 gamma hfirstColor hgammaMissing m hm
      hsecondColor base0raw hfirstEnds (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) P hPpath hPdiv (by assumption) hPbound
      closing_mem_P first_new_mem_P hfirstNewNotClosing
end GoldbergSeymour

end
