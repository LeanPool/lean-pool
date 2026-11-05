/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges

public import LeanPool.GoldbergSeymour.TashkinovClosure

public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# Extension Base Case Two Observation20

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseCaseTwoObservation20 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn seed TjPrime : TreeSequence G e0)
    (phiN sigmaN rho1 : PartialEdgeColoring E k)
    (controlled restorationColors : Finset (Fin k))
    (gammaN deltaN : Fin k) (fN : E) (terminalSupport : V)
    (hphiProper : IsProperEdgeColoring G phiN)
    (hphiOne : IsOneEdgeUncolored phiN e0)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (_ : IsProperEdgeColoring G rho1)
    (_ : IsOneEdgeUncolored rho1 e0)
    (hsigmaStable : StableColoring Tn controlled phiN sigmaN)
    (hgammaControlled : gammaN ∈ controlled)
    (hdeltaControlled : deltaN ∈ controlled)
    (hb3 : ∀ f : E, rho1 f ≠ sigmaN f →
      ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
        c ∈ restorationColors ∧ d ∈ restorationColors)
    (hgammaRestored : gammaN ∉ restorationColors)
    (hdeltaRestored : deltaN ∉ restorationColors)
    (hgammaBoundary :
      BoundaryColorEdges G phiN (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaLocation : ∀ f ∈ BoundaryColorEdges G phiN
        (TreeSequenceVertexSet Tn) deltaN,
      ∃ w ∈ TreeSequenceVertexSet seed, Incident G w f)
    (_ : TreeSequenceInitialSegment seed Tn)
    (_ : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport) :
    BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) gammaN = { fN } ∧
      BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
          deltaN =
        ∅ := by
  classical
  exact (by
    classical
    have hsigmaPhi : StableColoring Tn controlled sigmaN phiN := by
      exact (sc2 G e0 Tn controlled).symm
          (x := ⟨phiN, hphiProper, hphiOne⟩)
          (y := ⟨sigmaN, hsigmaProper, hsigmaOne⟩) (by simpa using hsigmaStable)
    have boundary_transport : ∀ (a : Fin k), a ∈ controlled →
        BoundaryColorEdges G phiN (TreeSequenceVertexSet Tn) a =
          BoundaryColorEdges G sigmaN (TreeSequenceVertexSet Tn) a := by
      intro a ha
      apply Finset.ext
      intro f
      constructor
      · intro hf
        have hb : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) :=
          (Finset.mem_filter.mp hf).1
        have hc : phiN f = some a := (Finset.mem_filter.mp hf).2
        have ht : TreeIncidentEdge Tn f := by
          unfold TreeIncidentEdge
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          rcases hb with ⟨u, hu, v, hv, he⟩
          have huend : u ∈ G.ends f := he ▸ Sym2.mem_iff.mpr (Or.inl rfl)
          exact ⟨u, hu, huend⟩
        have heq := hsigmaStable.1 f ht
        have hcontrol : ∃ c ∈ TreeMissingColors phiN Tn ∪ controlled,
            phiN f = some c := ⟨a, Finset.mem_union.mpr (Or.inr ha), hc⟩
        have hfix := heq hcontrol
        exact Finset.mem_filter.mpr ⟨hb, hfix.symm ▸ hc⟩
      · intro hf
        have hb : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) :=
          (Finset.mem_filter.mp hf).1
        have hc : sigmaN f = some a := (Finset.mem_filter.mp hf).2
        have ht : TreeIncidentEdge Tn f := by
          unfold TreeIncidentEdge
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          rcases hb with ⟨u, hu, v, hv, he⟩
          have huend : u ∈ G.ends f := he ▸ Sym2.mem_iff.mpr (Or.inl rfl)
          exact ⟨u, hu, huend⟩
        have heq := hsigmaPhi.1 f ht
        have hcontrol : ∃ c ∈ TreeMissingColors sigmaN Tn ∪ controlled,
            sigmaN f = some c := ⟨a, Finset.mem_union.mpr (Or.inr ha), hc⟩
        have hfix := heq hcontrol
        exact Finset.mem_filter.mpr ⟨hb, hfix ▸ hc⟩
    have rho_transport : ∀ (a : Fin k), a ∉ restorationColors →
        BoundaryColorEdges G sigmaN (TreeSequenceVertexSet Tn) a =
          BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) a := by
      intro a ha
      apply Finset.ext
      intro f
      constructor <;> intro hf
      · have hc : sigmaN f = some a := (Finset.mem_filter.mp hf).2
        by_cases heq : rho1 f = sigmaN f
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, heq ▸ hc⟩
        · rcases hb3 f heq with ⟨c, d, hsc, hrd, hcr, hdr⟩
          have : a ∈ restorationColors := by
            have hca : c = a := Option.some.inj (hsc.symm.trans hc)
            simpa [hca] using hcr
          exact (ha this).elim
      · have hc : rho1 f = some a := (Finset.mem_filter.mp hf).2
        by_cases heq : rho1 f = sigmaN f
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, heq.symm ▸ hc⟩
        · rcases hb3 f heq with ⟨c, d, hsc, hrd, hcr, hdr⟩
          have : a ∈ restorationColors := by
            have hda : d = a := Option.some.inj (hrd.symm.trans hc)
            simpa [hda] using hdr
          exact (ha this).elim
    have first : BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) gammaN = {fN} := by
      rw [← rho_transport gammaN hgammaRestored, ← boundary_transport gammaN hgammaControlled]
      exact hgammaBoundary
    refine ⟨first, ?_⟩
    have initial_subset {A B : TreeSequence G e0}
        (h : TreeSequenceInitialSegment A B) :
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
      intro v hv
      simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
      obtain ⟨i, hi, hvi⟩ := hv
      obtain ⟨hlen, hvertices, hedges⟩ := h
      exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
        (hvertices i).trans hvi⟩
    have seed_prime : TreeSequenceVertexSet seed ⊆
        TreeSequenceVertexSet TjPrime := by
      rcases hclosure with ⟨hseq, hclosed⟩
      unfold TashkinovAugmentationSequence at hseq
      clear * - hseq initial_subset
      induction hseq using Relation.ReflTransGen.head_induction_on with
      | refl => exact Finset.Subset.rfl
      | head hstep htail ih =>
          exact (initial_subset hstep.2.1).trans ih
    rcases hclosure with ⟨hseq, hclosed⟩
    rw [← Finset.not_nonempty_iff_eq_empty]
    intro hnonempty
    rcases hnonempty with ⟨f, hf⟩
    have hbU : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) :=
      (Finset.mem_filter.mp hf).1
    have hcf : rho1 f = some deltaN := (Finset.mem_filter.mp hf).2
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hbU
    rcases hbU with ⟨u, hu, v, hv, huv⟩
    have boundary_prime : f ∈ BoundaryEdges G (TreeSequenceVertexSet TjPrime) := by
      by_cases huprime : u ∈ TreeSequenceVertexSet TjPrime
      · simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, huprime, v, by
          intro hvprime
          exact hv (Finset.mem_union.mpr (Or.inr hvprime)), huv⟩
      · have hutn : u ∈ TreeSequenceVertexSet Tn :=
          (Finset.mem_union.mp hu).resolve_right huprime
        have hbt : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) := by
            simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨u, hutn, v, by
            intro hvtn
            exact hv (Finset.mem_union.mpr (Or.inl hvtn)), huv⟩
        have hbf : f ∈ BoundaryColorEdges G phiN
            (TreeSequenceVertexSet Tn) deltaN := by
          have hsig : sigmaN f = some deltaN := by
            by_cases hsame : rho1 f = sigmaN f
            · exact hsame ▸ hcf
            · rcases hb3 f hsame with ⟨c, d, hsc, hrd, hcr, hdr⟩
              have hda : d = deltaN := Option.some.inj (hrd.symm.trans hcf)
              exact (hdeltaRestored (by simpa [hda] using hdr)).elim
          have hsame : phiN f = sigmaN f :=
            (hsigmaPhi.1 f (by
              unfold TreeIncidentEdge
              have huend : u ∈ G.ends f := huv ▸ Sym2.mem_iff.mpr (Or.inl rfl)
              exact ⟨u, hutn, huend⟩))
              ⟨deltaN, Finset.mem_union.mpr (Or.inr hdeltaControlled), hsig⟩
          exact Finset.mem_filter.mpr ⟨hbt, hsame ▸ hsig⟩
        obtain ⟨w, hw, hwf⟩ := hdeltaLocation f hbf
        have hwprime : w ∈ TreeSequenceVertexSet TjPrime := seed_prime hw
        have hwu : w = u := by
          change w ∈ G.ends f at hwf
          have hmem : w = u ∨ w = v := by
            rw [huv] at hwf
            exact Sym2.mem_iff.mp hwf
          rcases hmem with hmem | hmem
          · exact hmem
          · have hwunion : w ∈ TreeSequenceVertexSet Tn ∪
                TreeSequenceVertexSet TjPrime := Finset.mem_union.mpr (Or.inr hwprime)
            exact False.elim (hv (hmem ▸ hwunion))
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w, hwu ▸ hwprime, v, by
          intro hvprime
          exact hv (Finset.mem_union.mpr (Or.inr hvprime)), hwu ▸ huv⟩
    have htermPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
      seed_prime hterminalSeed
    exact (hclosed boundary_prime htermPrime hcf) hdeltaMissing
  )

end GoldbergSeymour

end
