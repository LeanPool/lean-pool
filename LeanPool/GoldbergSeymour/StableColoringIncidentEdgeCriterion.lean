/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.StableColoring
public import Mathlib.Data.Fintype.EquivFin

/-!
# sc1

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem sc1 {V E : Type*} [Finite V] [Fintype E]
      (G : LooplessMultigraph V E) {k : ℕ}
    (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi pi : PartialEdgeColoring E k)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperPi : IsProperEdgeColoring G pi)
    (honePi : IsOneEdgeUncolored pi e0) :
    StableColoring T C phi pi ↔
      ∀ f, TreeIncidentEdge T f →
        ((∃ c ∈ TreeMissingColors phi T ∪ C, phi f = some c) ∨
          (∃ c ∈ TreeMissingColors phi T ∪ C, pi f = some c)) →
        pi f = phi f := by
  classical
  let _ := Fintype.ofFinite V
  unfold StableColoring
  have colored_iff : ∀ (ψ : PartialEdgeColoring E k),
      IsOneEdgeUncolored ψ e0 → ∀ v e,
        (Incident G v e ∧ ∃ c, ψ e = some c) ↔ Incident G v e ∧ e ≠ e0 := by
    intro ψ hone v e
    constructor
    · rintro ⟨hv, c, hc⟩
      refine ⟨hv, ?_⟩
      intro he
      subst e
      rw [hone.1] at hc
      cases hc
    · rintro ⟨hv, he⟩
      obtain ⟨c, hc⟩ := hone.2 e he
      exact ⟨hv, c, hc⟩
  have present_card : ∀ (ψ : PartialEdgeColoring E k),
      IsProperEdgeColoring G ψ → ∀ v,
        (PresentColors G ψ v).card =
          (Finset.univ.filter fun e => Incident G v e ∧ ∃ c, ψ e = some c).card := by
    intro ψ hproper v
    let colored := Finset.univ.filter fun e => Incident G v e ∧ ∃ c, ψ e = some c
    let chooseColor : (e : E) → e ∈ colored → Fin k :=
      fun e he => Classical.choose (Finset.mem_filter.mp he).2.2
    have choose_spec : ∀ (e : E) (he : e ∈ colored),
        ψ e = some (chooseColor e he) := by
      intro e he
      exact Classical.choose_spec (Finset.mem_filter.mp he).2.2
    symm
    apply (Finset.card_bij chooseColor)
    · intro e he
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, (Finset.mem_filter.mp he).2.1, choose_spec e he⟩
    · intro e₁ h₁ e₂ h₂ heq
      by_contra hne
      have hi₁ := (Finset.mem_filter.mp h₁).2.1
      have hi₂ := (Finset.mem_filter.mp h₂).2.1
      have ha : AdjacentEdges G e₁ e₂ := ⟨v, hi₁, hi₂⟩
      have hp := hproper hne ha (choose_spec e₁ h₁)
      exact hp (by simpa [heq] using choose_spec e₂ h₂)
    · intro c hc
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      obtain ⟨e, he, hce⟩ := hc
      have hecol : e ∈ colored := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, colored]
        exact ⟨he, c, hce⟩
      refine ⟨e, hecol, ?_⟩
      exact Option.some.inj ((choose_spec e hecol).symm.trans hce)
  have same_colored : ∀ v,
      (Finset.univ.filter fun e => Incident G v e ∧ ∃ c, phi e = some c) =
      (Finset.univ.filter fun e => Incident G v e ∧ ∃ c, pi e = some c) := by
    intro v
    ext e
    simp only [Finset.mem_filter]
    rw [colored_iff phi honePhi v e, colored_iff pi honePi v e]
  have same_present_card : ∀ v, (PresentColors G phi v).card =
      (PresentColors G pi v).card := by
    intro v
    rw [present_card phi hproperPhi v, present_card pi hproperPi v,
      same_colored v]
  have same_missing_card : ∀ v, (MissingColors G phi v).card =
      (MissingColors G pi v).card := by
    intro v
    simp [MissingColors, Finset.card_sdiff, same_present_card v]
  constructor
  · intro hstable f hf hor
    rcases hor with hphi | hpi
    · exact hstable.1 f hf hphi
    · obtain ⟨c, hcmem, hfc⟩ := hpi
      rcases hf with ⟨v, hv, hfv⟩
      have hpresentPi : c ∈ PresentColors G pi v := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨f, hfv, hfc⟩
      have hpresentPhi : c ∈ PresentColors G phi v := by
        have hmissPi : c ∉ MissingColors G pi v := by
          simpa [MissingColors] using hpresentPi
        have hmissPhi : c ∉ MissingColors G phi v := by
          rw [← hstable.2 v hv]
          exact hmissPi
        simpa [MissingColors] using hmissPhi
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresentPhi
      obtain ⟨g, hgv, hgc⟩ := hpresentPhi
      by_cases heq : phi f = some c
      · exact hstable.1 f ⟨v, hv, hfv⟩ ⟨c, hcmem, heq⟩
      · have hneq : g ≠ f := by
          intro hgf
          subst g
          exact heq hgc
        have hadj : AdjacentEdges G g f := ⟨v, hgv, hfv⟩
        have hgcPi : pi g = some c :=
          (hstable.1 g ⟨v, hv, hgv⟩ ⟨c, hcmem, hgc⟩).trans hgc
        have hp := hproperPi hneq hadj hgcPi
        exact False.elim (hp hfc)
  · intro hcond
    constructor
    · intro f hf hphi
      exact hcond f hf (Or.inl hphi)
    · intro v hv
      have hmissing : MissingColors G phi v = MissingColors G pi v := by
        apply Finset.eq_of_subset_of_card_le
        · intro c hc
          by_contra hnot
          have hcp : c ∈ PresentColors G pi v := by
            simpa [MissingColors] using hnot
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hcp
          obtain ⟨f, hf, hfc⟩ := hcp
          have htf : TreeIncidentEdge T f := ⟨v, hv, hf⟩
          have hmem : c ∈ TreeMissingColors phi T ∪ C := by
            have : c ∈ TreeMissingColors phi T := by
              simp only [TreeMissingColors, Finset.mem_biUnion]
              exact ⟨v, hv, by simpa [MissingColors] using hc⟩
            exact Finset.mem_union_left _ this
          have heq := hcond f htf (Or.inr ⟨c, hmem, hfc⟩)
          have hpnot : c ∉ PresentColors G phi v := by
            simpa [MissingColors] using hc
          apply hpnot
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨f, hf, heq.symm.trans hfc⟩
        · simp [same_missing_card v]
      exact hmissing.symm

end GoldbergSeymour

end
