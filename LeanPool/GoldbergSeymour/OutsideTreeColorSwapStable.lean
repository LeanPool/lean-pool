/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed

public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring

public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap

public import LeanPool.GoldbergSeymour.StableColoring

/-!
# Outside Tree Color Swap Stable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem OutsideTreeColorSwapStable {V E : Type*}
    [Fintype V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (halpha : alpha ∈ TreeMissingColors phi T)
    (hbeta : beta ∈ TreeMissingColors phi T)
    (hdistinct : alpha ≠ beta) :
    let psi := OutsideTreeColorSwap T phi alpha beta
    IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0 ∧
      StableColoring T C phi psi ∧
      ∀ f : E, TreeIncidentEdge T f → psi f = phi f := by
  classical
  let psi := OutsideTreeColorSwap T phi alpha beta
  change IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0 ∧
    StableColoring T C phi psi ∧
      ∀ f : E, TreeIncidentEdge T f → psi f = phi f
  have ends_eq_of_mem : ∀ {z : Sym2 V} {x y : V}, x ∈ z → y ∈ z → x ≠ y →
      z = s(x, y) := by
    intro z x y hx hy hxy
    induction z using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        simp_all []
  have halpha_closed : ∀ {f}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      phi f ≠ some alpha := by
    intro f hf hfa
    obtain ⟨v, hv, hvm⟩ := by
      unfold TreeMissingColors at halpha
      simpa only [Finset.mem_biUnion] using halpha
    exact (hclosed hf hv hfa) hvm
  have hbeta_closed : ∀ {f}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      phi f ≠ some beta := by
    intro f hf hfb
    obtain ⟨v, hv, hvm⟩ := by
      unfold TreeMissingColors at hbeta
      simpa only [Finset.mem_biUnion] using hbeta
    exact (hclosed hf hv hfb) hvm
  have tree_fixed : ∀ {f}, TreeIncidentEdge T f → psi f = phi f := by
    intro f hf
    simp [psi, OutsideTreeColorSwap, hf]
  have tree_boundary : ∀ {f g : E}, TreeIncidentEdge T f →
      ¬ TreeIncidentEdge T g → AdjacentEdges G f g →
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    intro f g hf hg hadj
    obtain ⟨x, hx, hxf⟩ := hf
    obtain ⟨w, hwf, hwg⟩ := hadj
    have hw : w ∉ TreeSequenceVertexSet T := by
      intro hw
      exact hg ⟨w, hw, hwg⟩
    have hxw : x ≠ w := by
      intro h
      exact hw (h ▸ hx)
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, w, hw, ends_eq_of_mem hxf hwf hxw⟩
  have swap_injective : Function.Injective (fun q : Option (Fin k) =>
      if q = some alpha then some beta else
      if q = some beta then some alpha else q) := by
    intro q r h
    cases q <;> cases r
    · rfl
    · rename_i a
      by_cases ha : a = alpha
      · simp [ha] at h
      · by_cases hb : a = beta
        · have hab : beta ≠ alpha := by
            intro hab
            exact ha (hb.trans hab)
          simp [hb, hab] at h
        · simp [ha, hb] at h
    · rename_i a
      by_cases ha : a = alpha
      · simp [ha] at h
      · by_cases hb : a = beta
        · have hab : beta ≠ alpha := by
            intro hab
            exact ha (hb.trans hab)
          simp [hb, hab] at h
        · simp [ha, hb] at h
    · simp only [Option.some.injEq] at h ⊢
      rename_i a b
      by_cases aa : a = alpha <;> by_cases ab : a = beta <;>
        by_cases ba : b = alpha <;> by_cases bb : b = beta <;> simp_all
  refine ⟨?_, ?_, ?_, fun f hf => tree_fixed hf⟩
  · intro f g c hne hadj hfc
    by_cases hf : TreeIncidentEdge T f
    · by_cases hg : TreeIncidentEdge T g
      · intro hgc
        apply hproper hne hadj
        · simpa [tree_fixed hf] using hfc
        · simpa [tree_fixed hg] using hgc
      · have hb := tree_boundary hf hg hadj
        have hfa : phi f ≠ some alpha := halpha_closed hb
        have hfb : phi f ≠ some beta := hbeta_closed hb
        have hca : c ≠ alpha := by
          intro hc
          exact hfa (hc ▸ (by simpa [tree_fixed hf] using hfc))
        have hcb : c ≠ beta := by
          intro hc
          exact hfb (hc ▸ (by simpa [tree_fixed hf] using hfc))
        intro hgc
        have hpg : phi g = some c := by
          by_cases ga : phi g = some alpha
          · have hs : some beta = some c := by
              simpa [psi, OutsideTreeColorSwap, hg, ga] using hgc
            exact False.elim (hcb (Option.some.inj hs).symm)
          · by_cases gb : phi g = some beta
            · have hab : alpha ≠ beta := by
                intro hab
                exact ga (hab ▸ gb)
              have hs : some alpha = some c := by
                simpa [psi, OutsideTreeColorSwap, hg, ga, gb, hab, hab.symm]
                  using hgc
              exact False.elim (hca (Option.some.inj hs).symm)
            · simpa [psi, OutsideTreeColorSwap, hg, ga, gb] using hgc
        exact hproper hne hadj (by simpa [tree_fixed hf] using hfc) hpg
    · by_cases hg : TreeIncidentEdge T g
      · obtain ⟨w, hwf, hwg⟩ := hadj
        have hb := tree_boundary hg hf ⟨w, hwg, hwf⟩
        have hga : phi g ≠ some alpha := halpha_closed hb
        have hgb : phi g ≠ some beta := hbeta_closed hb
        intro hgc
        have hpg : phi g = some c := by simpa [tree_fixed hg] using hgc
        have hca : c ≠ alpha := by
          intro hc
          exact hga (hc ▸ hpg)
        have hcb : c ≠ beta := by
          intro hc
          exact hgb (hc ▸ hpg)
        have hfc' : phi f = some c := by
          by_cases fa : phi f = some alpha
          · have hs : some beta = some c := by
              simpa [psi, OutsideTreeColorSwap, hf, fa] using hfc
            exact False.elim (hcb (Option.some.inj hs).symm)
          · by_cases fb : phi f = some beta
            · have hab : alpha ≠ beta := by
                intro hab
                exact fa (hab ▸ fb)
              have hs : some alpha = some c := by
                simpa [psi, OutsideTreeColorSwap, hf, fa, fb, hab, hab.symm]
                  using hfc
              exact False.elim (hca (Option.some.inj hs).symm)
            · simpa [psi, OutsideTreeColorSwap, hf, fa, fb] using hfc
        exact (hproper hne.symm (⟨w, hwg, hwf⟩) hpg hfc')
      · intro hgc
        have heq : phi f = phi g := by
          apply swap_injective
          simpa [psi, OutsideTreeColorSwap, hf, hg] using hfc.trans hgc.symm
        have hfn : phi f ≠ none := by
          intro hnone
          simp [psi, OutsideTreeColorSwap, hf, hnone] at hfc
        obtain ⟨d, hfd⟩ := Option.ne_none_iff_exists.mp hfn
        exact (hproper hne hadj hfd.symm) (heq ▸ hfd.symm)
  · unfold IsOneEdgeUncolored
    constructor
    · by_cases ht : TreeIncidentEdge T e0
      · simpa [psi, OutsideTreeColorSwap, ht] using hone.1
      · simp [psi, OutsideTreeColorSwap, ht, hone.1]
    · intro f hfe
      obtain ⟨c, hcf⟩ := hone.2 f hfe
      by_cases hf : TreeIncidentEdge T f
      · exact ⟨c, by simpa [tree_fixed hf] using hcf⟩
      · by_cases ha : phi f = some alpha
        · exact ⟨beta, by simp [psi, OutsideTreeColorSwap, hf, ha]⟩
        · by_cases hb : phi f = some beta
          · exact ⟨alpha, by simp [psi, OutsideTreeColorSwap, hf, hb]⟩
          · exact ⟨c, by simpa [psi, OutsideTreeColorSwap, hf, ha, hb] using hcf⟩
  · unfold StableColoring
    constructor
    · intro f hf h
      exact (tree_fixed hf).trans (Eq.refl _)
    · intro v hv
      unfold MissingColors PresentColors
      congr 1
      ext c
      constructor <;> intro hc
      · obtain ⟨_, ⟨f, hfv, hfc⟩⟩ := Finset.mem_filter.mp hc
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, ⟨f, hfv, by simpa [tree_fixed ⟨v, hv, hfv⟩] using hfc⟩⟩
      · obtain ⟨_, ⟨f, hfv, hfc⟩⟩ := Finset.mem_filter.mp hc
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, ⟨f, hfv, by simpa [tree_fixed ⟨v, hv, hfv⟩] using hfc⟩⟩

end GoldbergSeymour

end
