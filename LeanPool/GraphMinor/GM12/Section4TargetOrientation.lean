/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement

/-!
# Orienting the finite labelled target

In XII (4.3), page 250, direct the target edges arbitrarily.
The two selected ends are assigned to the head and tail. A vertex
incident with two distinct edges then has assigned ends on two
distinct selected edges, which supplies the witnesses in the
final control argument.
-/

public section

namespace GraphMinor.GM12

open Set

/-- The orientation and two-edge end assignments used in XII
(4.3), pages 250--251. -/
theorem exists_target_end_assignment
    {p t : ℕ} (L : Graph (Fin p) (Fin t)) (hE : L.edgeSet = univ)
    (hloopless : ∀ e v, ¬ L.IsLink e v v)
    (htwo : ∀ v ∈ L.vertexSet, ∃ e f, e ≠ f ∧ L.Inc e v ∧ L.Inc f v) :
    ∃ κ : Fin t × Bool → Fin p,
      (∀ e u v, L.IsLink e u v →
        (κ (e, true) = u ∧ κ (e, false) = v) ∨
          (κ (e, true) = v ∧ κ (e, false) = u)) ∧
      ∀ v ∈ L.vertexSet, ∃ i j, i ≠ j ∧ ∃ c d : Bool, κ (i, c) = v ∧ κ (j, d) = v := by
  classical
  have hex : ∀ e : Fin t, ∃ u v, L.IsLink e u v := by
    intro e
    apply L.exists_isLink_of_mem_edgeSet
    rw [hE]
    exact mem_univ e
  choose head tail horient using hex
  let κ : Fin t × Bool → Fin p := fun q => if q.2 then head q.1 else tail q.1
  refine ⟨κ, ?_, ?_⟩
  · intro e u v hl
    have huv : u ≠ v := by
      intro heq
      exact hloopless e v (heq ▸ hl)
    have hu := hl.inc_left.eq_or_eq_of_isLink (horient e)
    have hv := hl.inc_right.eq_or_eq_of_isLink (horient e)
    change (head e = u ∧ tail e = v) ∨ (head e = v ∧ tail e = u)
    rcases hu with hu | hu
    · rcases hv with hv | hv
      · exact False.elim (huv (hu.trans hv.symm))
      · exact Or.inl ⟨hu.symm, hv.symm⟩
    · rcases hv with hv | hv
      · exact Or.inr ⟨hv.symm, hu.symm⟩
      · exact False.elim (huv (hu.trans hv.symm))
  · have hslot : ∀ e v, L.Inc e v → ∃ c : Bool, κ (e, c) = v := by
      intro e v hev
      rcases hev.eq_or_eq_of_isLink (horient e) with hv | hv
      · exact ⟨true, hv.symm⟩
      · exact ⟨false, hv.symm⟩
    intro v hv
    obtain ⟨e, f, hef, he, hf⟩ := htwo v hv
    obtain ⟨c, hc⟩ := hslot e v he
    obtain ⟨d, hd⟩ := hslot f v hf
    exact ⟨e, f, hef, c, d, hc, hd⟩

end GraphMinor.GM12
