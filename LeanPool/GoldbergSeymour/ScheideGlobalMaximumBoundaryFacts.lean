/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetStronglyClosed
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Scheide Global Maximum Boundary Facts

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ScheideGlobalMaximumBoundaryFacts_branch_90.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0), ColoredVertexSetClosed G
        phi (TreeSequenceVertexSet T) → Odd (TreeSequenceVertexSet T).card → IsProperEdgeColoring
        G phi →
    let _ := TreeSequenceVertexSet T;
    ∀ alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T), Odd (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card ∧ 3 ≤ (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card := by
  classical
  intro V E _ _ G k e0 phi T hclosed hodd hproper X alpha halpha
  have hcard : 2 ≤ (BoundaryColorEdges G phi X alpha).card := by
    exact (Finset.mem_filter.mp halpha).2
  let B := BoundaryColorEdges G phi X alpha
  let edges := (Finset.univ : Finset E).filter (fun e => phi e = some alpha)
  let good := edges.filter (fun e => ∀ v, Incident G v e → v ∈ X)
  have hpresent : ∀ v, v ∈ X → alpha ∈ PresentColors G phi v := by
    intro v hv
    have hBpos : 0 < B.card := by dsimp [B]; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hBpos
    have hbb : b ∈ BoundaryEdges G X := (Finset.mem_filter.mp hb).1
    have hbc : phi b = some alpha := (Finset.mem_filter.mp hb).2
    have hn : alpha ∉ MissingColors G phi v := by
      intro hm
      exact (hclosed hbb hv hbc) hm
    simpa [MissingColors] using hn
  have hedge_mem : ∀ e, e ∈ edges ↔ phi e = some alpha := by
    intro e
    simp [edges]
  have hgood : ∀ e, e ∈ good ↔ e ∈ edges ∧ ∀ v, Incident G v e → v ∈ X := by
    intro e
    simp [good]
  have hendcard : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd) (Sym2.diag_diagElem hd).symm
  have hgood_disjoint : ∀ ⦃e⦄, e ∈ good → ∀ ⦃f⦄, f ∈ good →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      (hedge_mem e |>.mp (hgood e |>.mp he).1))
      (hedge_mem f |>.mp (hgood f |>.mp hf).1)
  have hgood_union : (good.biUnion fun edge => (G.ends edge).toFinset).card =
      2 * good.card := by
    rw [Finset.card_biUnion @hgood_disjoint]
    exact (Finset.sum_const_nat (fun edge _ => hendcard edge)).trans (Nat.mul_comm _ _)
  have hgood_cover : ∀ v, v ∈ X →
      v ∈ good.biUnion (fun e => (G.ends e).toFinset) ∨
        v ∈ B.biUnion (fun e => X.filter (fun v => Incident G v e)) := by
    intro v hv
    obtain ⟨e, he, hve⟩ := by simpa [PresentColors] using hpresent v hv
    by_cases hall : ∀ w, Incident G w e → w ∈ X
    · left
      exact Finset.mem_biUnion.mpr ⟨e, (hgood e).mpr ⟨(hedge_mem e).mpr hve, hall⟩,
        Sym2.mem_toFinset.mpr he⟩
    · right
      push Not at hall
      obtain ⟨w, hw, hwo⟩ := hall
      obtain ⟨z, hze⟩ := Sym2.mem_iff_exists.mp hw
      have heq : G.ends e = s(w, z) := hze
      have hne : w ≠ z := by
        intro h
        exact G.loopless e w (by simpa [h] using heq)
      have hzX : z ∈ X := by
        have : v = w ∨ v = z := by
          have : v ∈ s(w, z) := by rw [← heq]; exact he
          simpa using this
        rcases this with rfl | rfl
        · exact False.elim (hwo hv)
        · exact hv
      have hbound : e ∈ BoundaryEdges G X := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, z, hzX, w, hwo, heq.trans Sym2.eq_swap⟩
      exact Finset.mem_biUnion.mpr ⟨e,
        (Finset.mem_filter.mpr ⟨hbound, hve⟩),
        Finset.mem_filter.mpr ⟨hv, he⟩⟩
  have hb_fiber : ∀ e, e ∈ B →
      (X.filter (fun v => Incident G v e)).card = 1 := by
    intro e he
    obtain ⟨u, hu, v, hv, huv⟩ := by
      simpa [B, BoundaryColorEdges, BoundaryEdges] using
        (Finset.mem_filter.mp he).1
    have hs : X.filter (fun x => Incident G x e) = {u} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, Incident,
        huv, Sym2.mem_iff]
      constructor
      · rintro ⟨hx, rfl | hxe⟩
        · exact rfl
        · exact False.elim (hv (hxe ▸ hx))
      · intro hxu
        subst hxu
        exact ⟨hu, Or.inl rfl⟩
    rw [hs]
    simp
  have hb_disjoint : ∀ ⦃e⦄, e ∈ B → ∀ ⦃f⦄, f ∈ B →
      e ≠ f → Disjoint (X.filter (fun v => Incident G v e))
        (X.filter (fun v => Incident G v f)) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef ⟨v, (Finset.mem_filter.mp hev).2,
      (Finset.mem_filter.mp hvf).2⟩
      (Finset.mem_filter.mp he).2)
      (Finset.mem_filter.mp hf).2
  have hb_union : (B.biUnion fun edge => X.filter (fun vertex => Incident G vertex edge)).card =
      B.card := by
    rw [Finset.card_biUnion @hb_disjoint]
    simpa only [Nat.mul_one] using Finset.sum_const_nat hb_fiber
  let U := good.biUnion (fun e => (G.ends e).toFinset)
  let W := B.biUnion (fun e => X.filter (fun v => Incident G v e))
  have hU : U ⊆ X := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact (hgood e).mp he |>.2 v (Sym2.mem_toFinset.mp hve)
  have hW : W ⊆ X := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hve).1
  have hUW : Disjoint U W := by
    rw [Finset.disjoint_left]
    intro v hvU hvW
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvU
    obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvW
    have hef : e ≠ f := by
      intro hef
      subst hef
      obtain ⟨u, hu, w, hw, huw⟩ := by
        simpa [B, BoundaryColorEdges, BoundaryEdges] using
          (Finset.mem_filter.mp hf).1
      have : w ∈ X := (hgood e).mp he |>.2 w
        (by change w ∈ G.ends e; rw [huw]; exact Sym2.mem_mk_right u w)
      exact hw this
    exact (hproper hef ⟨v, Sym2.mem_toFinset.mp hve,
      (Finset.mem_filter.mp hvf).2⟩
      (hedge_mem e |>.mp (hgood e |>.mp he).1))
      (Finset.mem_filter.mp hf).2
  have hUX : U ∪ W = X := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hU hW
    · intro v hv
      rcases hgood_cover v hv with hvU | hvB
      · exact Finset.mem_union.mpr (Or.inl hvU)
      · obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvB
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨e, he, hve⟩))
  have hcardeq : X.card = 2 * good.card + B.card := by
    rw [← hUX, Finset.card_union_of_disjoint hUW, hgood_union, hb_union]
  rcases hodd with ⟨q, hq⟩
  have hBodd : Odd B.card := by
    have hq' : X.card = 2 * q + 1 := by simpa [X] using hq
    have hqgood : good.card ≤ q := by omega
    refine ⟨q - good.card, ?_⟩
    omega
  have hBthree : 3 ≤ B.card := by
    rcases hBodd with ⟨q, hq⟩
    have hcardB : 2 ≤ B.card := by simpa [B] using hcard
    omega
  exact ⟨by simpa [B] using hBodd, by simpa [B] using hBthree⟩

theorem ScheideGlobalMaximumBoundaryFacts {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    (DefectiveColors G phi (TreeSequenceVertexSet T) = ∅ →
      ColoredVertexSetStronglyClosed G phi (TreeSequenceVertexSet T)) ∧
    (∀ alpha ∈ TreeMissingColors phi T,
      BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha = ∅) ∧
    (∀ alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T),
      Odd (BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha).card ∧
        3 ≤ (BoundaryColorEdges G phi
          (TreeSequenceVertexSet T) alpha).card) := by
  classical
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hodd : Odd (TreeSequenceVertexSet T).card := horder.2.2.1
  have hproper : IsProperEdgeColoring G phi := hglobal.1.2.2.2.1
  let X := TreeSequenceVertexSet T
  constructor
  · intro hempty
    refine ⟨hclosed, ?_⟩
    intro f g c hf hg hfg hfc hgc
    exfalso
    have htwo : 2 ≤ (BoundaryColorEdges G phi X c).card := by
      have hinsert : 2 ≤ ({f, g} : Finset E).card := by simp [hfg]
      apply le_trans hinsert
      exact Finset.card_le_card (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact (Finset.mem_filter.mpr ⟨hf, hfc⟩)
        · exact (Finset.mem_filter.mpr ⟨hg, hgc⟩))
    have hmem : c ∈ DefectiveColors G phi X := by
      simp only [DefectiveColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact htwo
    rw [hempty] at hmem
    simp at hmem
  constructor
  · intro alpha halpha
    ext f
    constructor
    · intro hf
      have hfb : f ∈ BoundaryEdges G X := (Finset.mem_filter.mp hf).1
      have hfc : phi f = some alpha := (Finset.mem_filter.mp hf).2
      change alpha ∈ X.biUnion (fun v => MissingColors G phi v) at halpha
      simp only [Finset.mem_biUnion] at halpha
      obtain ⟨v, hvX, hva⟩ := halpha
      exact False.elim ((hclosed hfb hvX hfc) hva)
    · intro hf
      simp at hf
  · exact @ScheideGlobalMaximumBoundaryFacts_branch_90 V E inferInstance inferInstance
       G k e0 phi T hclosed hodd hproper
end GoldbergSeymour

end
