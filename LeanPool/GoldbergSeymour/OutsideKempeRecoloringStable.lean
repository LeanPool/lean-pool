/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloring
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TreeColoringInvariant

/-!
# Outside Kempe Recoloring Stable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem OutsideKempeRecoloringStable {V E : Type*}
    [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} (e0 : E)
    (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi sigma : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta) :
    IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
    StableColoring T C phi sigma ∧
    TreeColoringInvariant T phi sigma ∧
    ∀ f : E, TreeIncidentEdge T f → sigma f = phi f := by
  classical
  let _ := Fintype.ofFinite V
  rcases hrecolor with ⟨hab, roots, hout, hsigma⟩
  let changeColor : Option (Fin k) → Option (Fin k) := fun q =>
    if q = some alpha then some beta else
    if q = some beta then some alpha else q
  have hroot : ∀ {f : E}, (∃ z ∈ roots,
      Sum.inr f ∈ TwoColorComponent G phi alpha beta z) →
      (phi f = some alpha ∨ phi f = some beta) → ¬ TreeIncidentEdge T f := by
    intro f hf hcol htf
    obtain ⟨z, hz, hzf⟩ := hf
    obtain ⟨v, hv, hvf⟩ := htf
    have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj
        (Sum.inl v) (Sum.inr f) := by
      exact ⟨hvf, hcol⟩
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    have hzf' : (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
        (Sum.inr f) = (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z := by
      change Sum.inr f ∈ ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z).supp
          at hzf
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hzf
    have hvcomp : Sum.inl v ∈ TwoColorComponent G phi alpha beta z := by
      change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk (Sum.inl v) =
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z
      exact heq.trans hzf'
    exact (hout z hz v hvcomp) hv
  have hswap : ∀ f, sigma f = if ∃ z ∈ roots,
      Sum.inr f ∈ TwoColorComponent G phi alpha beta z then changeColor (phi f)
      else phi f := by
    intro f
    simpa [changeColor] using hsigma f
  have hfixed : ∀ {f}, TreeIncidentEdge T f → sigma f = phi f := by
    intro f hf
    rw [hswap f]
    by_cases ha : phi f = some alpha
    · by_cases h : ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha beta z
      · exact False.elim (hroot h (Or.inl ha) hf)
      · simp [changeColor, h, ha]
    · by_cases hb' : phi f = some beta
      · by_cases h : ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha beta z
        · exact False.elim (hroot h (Or.inr hb') hf)
        · simp [changeColor, h, hb']
      · simp [changeColor, ha, hb']
  have swap_injective : Function.Injective changeColor := by
    intro x y equal
    apply (Equiv.swap (some alpha) (some beta)).injective
    simpa only [Equiv.swap_apply_def, changeColor] using equal
  have component_step :
    ∀ {e f : E}, (
    ∃ z ∈ roots, Sum.inr e ∈ TwoColorComponent G phi alpha beta z) → AdjacentEdges G e f → (phi e
        = some alpha ∨ phi e = some beta) → (phi f = some alpha ∨ phi f = some beta) →
    ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha beta z := by
    intro e f he hadj hce hcf
    obtain ⟨z, hz, hze⟩ := he
    obtain ⟨v, hve, hvf⟩ := hadj
    have hae : (TwoColorIncidenceGraph G phi alpha beta).Adj
        (Sum.inr e) (Sum.inl v) := ⟨hve, hce⟩
    have haf : (TwoColorIncidenceGraph G phi alpha beta).Adj
        (Sum.inl v) (Sum.inr f) := ⟨hvf, hcf⟩
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hae
    have hfq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj haf
    have hze' : (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
        (Sum.inr e) = (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z := by
      change Sum.inr e ∈ ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z).supp
          at hze
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hze
    exact ⟨z, hz, hfq.symm.trans (heq.symm.trans hze')⟩
  have hproper' : IsProperEdgeColoring G sigma := by
    intro e f c hef hadj hec hfc
    by_cases se : ∃ z ∈ roots, Sum.inr e ∈ TwoColorComponent G phi alpha beta z
    · by_cases sf : ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha beta z
      · have heq : phi e = phi f := by
          apply swap_injective
          rw [hswap e] at hec
          rw [hswap f] at hfc
          simp only [se, sf, ↓reduceIte] at hec hfc
          exact hec.trans hfc.symm
        have hne : phi e ≠ none := by
          intro hn
          rw [hswap e, hn] at hec
          simp [changeColor] at hec
        obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hne
        exact (hproper hef hadj hd.symm) (heq ▸ hd.symm)
      · rw [hswap e] at hec
        rw [ite_eq_left se] at hec
        rw [hswap f] at hfc
        rw [ite_eq_right sf] at hfc
        by_cases ha' : phi e = some alpha
        · have hc : c = beta := by simpa [changeColor, ha'] using hec.symm
          have hf : phi f = some beta := hc ▸ hfc
          exact sf (component_step se hadj (Or.inl ha') (Or.inr hf))
        · by_cases hb' : phi e = some beta
          · have hc : c = alpha := by simpa [changeColor, hb', hab, hab.symm] using hec.symm
            have hf : phi f = some alpha := hc ▸ hfc
            exact sf (component_step se hadj (Or.inr hb') (Or.inl hf))
          · have he : phi e = some c := by simpa [changeColor, ha', hb'] using hec
            exact (hproper hef hadj he) hfc
    · by_cases sf : ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha beta z
      · rw [hswap e] at hec
        rw [ite_eq_right se] at hec
        rw [hswap f] at hfc
        rw [ite_eq_left sf] at hfc
        by_cases ha' : phi f = some alpha
        · have hc : c = beta := by simpa [changeColor, ha'] using hfc.symm
          have he : phi e = some beta := hc ▸ hec
          obtain ⟨v, hve, hvf⟩ := hadj
          exact se (component_step sf ⟨v, hvf, hve⟩ (Or.inl ha') (Or.inr he))
        · by_cases hb' : phi f = some beta
          · have hc : c = alpha := by simpa [changeColor, hb', hab, hab.symm] using hfc.symm
            have he : phi e = some alpha := hc ▸ hec
            obtain ⟨v, hve, hvf⟩ := hadj
            exact se (component_step sf ⟨v, hvf, hve⟩ (Or.inr hb') (Or.inl he))
          · have hf : phi f = some c := by simpa [changeColor, ha', hb'] using hfc
            obtain ⟨v, hve, hvf⟩ := hadj
            exact (hproper hef.symm ⟨v, hvf, hve⟩ hf) hec
      · rw [hswap e] at hec
        rw [ite_eq_right se] at hec
        rw [hswap f] at hfc
        rw [ite_eq_right sf] at hfc
        exact hproper hef hadj hec hfc
  refine ⟨hproper', ?_, ?_, ?_, fun f hf => hfixed hf⟩
  · unfold IsOneEdgeUncolored
    constructor
    · rw [hswap e0]
      by_cases h : ∃ z ∈ roots, Sum.inr e0 ∈ TwoColorComponent G phi alpha beta z
      · simp [changeColor, hone.1]
      · simp [h, hone.1]
    · intro f hfe
      obtain ⟨d, hd⟩ := hone.2 f hfe
      rw [hswap f]
      by_cases h : ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha beta z
      · rw [ite_eq_left h]
        by_cases ha' : phi f = some alpha
        · exact ⟨beta, by simp [changeColor, ha']⟩
        · by_cases hb' : phi f = some beta
          · exact ⟨alpha, by simp [changeColor, hb']⟩
          · exact ⟨d, by simp only [ha', ↓reduceIte, hb', changeColor]; exact hd⟩
      · rw [ite_eq_right h]
        exact ⟨d, hd⟩
  · unfold StableColoring
    constructor
    · intro f hf h
      exact hfixed hf
    · intro v hv
      unfold MissingColors PresentColors
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro hd
      · obtain ⟨f, hfv, hfc⟩ := hd
        exact ⟨f, hfv, by simpa [hfixed ⟨v, hv, hfv⟩] using hfc⟩
      · obtain ⟨f, hfv, hfc⟩ := hd
        exact ⟨f, hfv, by simpa [hfixed ⟨v, hv, hfv⟩] using hfc⟩
  · unfold TreeColoringInvariant
    constructor
    · intro j hj
      apply hfixed
      obtain ⟨i, hi⟩ := T.attaches j
      exact ⟨T.vertex j.succ, by
        unfold TreeSequenceVertexSet
        simp, by
          unfold Incident
          rw [hi]
          simp⟩
    · intro v hv
      unfold MissingColors PresentColors
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro hd
      · obtain ⟨f, hfv, hfc⟩ := hd
        exact ⟨f, hfv, by simpa [hfixed ⟨v, hv, hfv⟩] using hfc⟩
      · obtain ⟨f, hfv, hfc⟩ := hd
        exact ⟨f, hfv, by simpa [hfixed ⟨v, hv, hfv⟩] using hfc⟩

end GoldbergSeymour

end
