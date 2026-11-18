/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GlobalMaximumTriple

/-!
# Scheide Global Maximum Missing Counts

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideGlobalMaximumMissingCounts {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (v : V) (_ : v ∈ TreeSequenceVertexSet T) :
    (Incident G v e0 →
      (MissingColors G phi v).card = k - Degree G v + 1 ∧
        2 ≤ (MissingColors G phi v).card) ∧
    (¬ Incident G v e0 →
      (MissingColors G phi v).card = k - Degree G v ∧
        1 ≤ (MissingColors G phi v).card) := by
  classical
  have htriple : KTriple G k e0 phi := hglobal.1
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := htriple.2.2.2.2
  have colored_iff : ∀ v e,
      (Incident G v e ∧ ∃ c, phi e = some c) ↔ Incident G v e ∧ e ≠ e0 := by
    intro w e
    constructor
    · rintro ⟨hw, c, hc⟩
      refine ⟨hw, ?_⟩
      intro he
      subst e
      rw [hone.1] at hc
      cases hc
    · rintro ⟨hw, he⟩
      obtain ⟨c, hc⟩ := hone.2 e he
      exact ⟨hw, c, hc⟩
  have present_card : ∀ w,
      (PresentColors G phi w).card =
        (Finset.univ.filter fun e => Incident G w e ∧ ∃ c, phi e = some c).card := by
    intro w
    let colored := Finset.univ.filter fun e => Incident G w e ∧ ∃ c, phi e = some c
    let chooseColor : (e : E) → e ∈ colored → Fin k :=
      fun e he => Classical.choose (Finset.mem_filter.mp he).2.2
    have choose_spec : ∀ (e : E) (he : e ∈ colored),
        phi e = some (chooseColor e he) := by
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
      have ha : AdjacentEdges G e₁ e₂ := ⟨w, hi₁, hi₂⟩
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
  have colored_card : ∀ w,
      (Finset.univ.filter fun e => Incident G w e ∧ ∃ c, phi e = some c).card =
        if Incident G w e0 then Degree G w - 1 else Degree G w := by
    intro w
    have hset : (Finset.univ.filter fun e => Incident G w e ∧ ∃ c, phi e = some c) =
        (Finset.univ.filter fun e => Incident G w e).filter (fun e => e ≠ e0) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [colored_iff w e]
    rw [hset]
    by_cases hw : Incident G w e0
    · have hmem : e0 ∈ Finset.univ.filter (fun e => Incident G w e) := by
        simp [hw]
      rw [Finset.filter_ne', Finset.card_erase_of_mem hmem]
      simp [Degree, hw]
    · have hnot : e0 ∉ Finset.univ.filter (fun e => Incident G w e) := by
        simp [hw]
      rw [Finset.filter_ne']
      rw [Finset.erase_eq_self.mpr hnot]
      simp [hw, Degree]
  have missing_card : ∀ w,
      (MissingColors G phi w).card = k -
        (if Incident G w e0 then Degree G w - 1 else Degree G w) := by
    intro w
    rw [show (MissingColors G phi w).card = k - (PresentColors G phi w).card by
      simp [MissingColors, Finset.card_sdiff]]
    rw [present_card w, colored_card w]
  have hdeg : ∀ w, Degree G w ≤ MaximumDegree G := by
    intro w
    unfold MaximumDegree
    apply Finset.le_max'
    simp [Degree]
  have hkdeg : ∀ w, Degree G w + 1 ≤ k := by
    intro w
    exact (Nat.le_trans (Nat.succ_le_succ (hdeg w)) htriple.2.2.1)
  constructor
  · intro hw
    have hm := missing_card v
    rw [ite_eq_left hw] at hm
    have hkv := hkdeg v
    have hd : Degree G v ≤ k := by omega
    have hpos : 1 ≤ Degree G v := by
      unfold Degree
      apply Finset.card_pos.mpr
      exact ⟨e0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
    have hrem : k - Degree G v + Degree G v = k := Nat.sub_add_cancel hd
    have hremd : Degree G v - 1 + 1 = Degree G v := Nat.sub_add_cancel hpos
    constructor
    · omega
    · rw [hm]
      apply Nat.le_sub_of_add_le
      omega
  · intro hw
    have hm := missing_card v
    rw [ite_eq_right hw] at hm
    have hkv := hkdeg v
    constructor
    · exact hm
    · have hd : Degree G v ≤ k := by omega
      omega

end GoldbergSeymour

end
