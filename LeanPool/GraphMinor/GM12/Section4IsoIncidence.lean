/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement

/-!
# Incidences under the target's finite relabelling

In XII (4.3), page 249, the loopless minimum-degree-two target
is enumerated by finite vertex and edge labels. An isomorphism
preserves incidences, loops, and the existence of two distinct
incident edges. These facts transfer the replacement's properties
to its finite labelled graph.
-/

public section

namespace GraphMinor.GM12

/-- A graph isomorphism preserves incidence, as used when labelling
the target of XII (4.3), page 249. -/
theorem iso_inc_iff {α β γ δ : Type*} {L : Graph α β} {G : Graph γ δ}
    (φ : Iso L G) (e : L.edgeSet) (v : L.vertexSet) :
    L.Inc e.val v.val ↔ G.Inc (φ.edgeEquiv e).val (φ.vertexEquiv v).val := by
  constructor
  · rintro ⟨w, hl⟩
    exact ⟨(φ.vertexEquiv ⟨w, hl.right_mem⟩).val,
      (φ.isLink_iff e v ⟨w, hl.right_mem⟩).mp hl⟩
  · rintro ⟨w, hl⟩
    let w' := φ.vertexEquiv.symm ⟨w, hl.right_mem⟩
    refine ⟨w'.val, (φ.isLink_iff e v w').mpr ?_⟩
    simpa only [w', φ.vertexEquiv.apply_symm_apply] using hl

/-- Looplessness is preserved by graph isomorphism. -/
theorem loopless_of_iso {α β γ δ : Type*} {L : Graph α β} {G : Graph γ δ}
    (φ : Iso L G) (hG : ∀ e v, ¬ G.IsLink e v v) :
    ∀ e v, ¬ L.IsLink e v v := by
  intro e v hl
  exact hG (φ.edgeEquiv ⟨e, hl.edge_mem⟩).val (φ.vertexEquiv ⟨v, hl.left_mem⟩).val
    ((φ.isLink_iff ⟨e, hl.edge_mem⟩ ⟨v, hl.left_mem⟩ ⟨v, hl.left_mem⟩).mp hl)

/-- The two-distinct-incident-edges condition is preserved by
isomorphism, as used for the replacement in XII (4.3), page 249. -/
theorem two_incident_edges_of_iso {α β γ δ : Type*} {L : Graph α β} {G : Graph γ δ}
    (φ : Iso L G)
    (hG : ∀ v ∈ G.vertexSet, ∃ e f, e ≠ f ∧ G.Inc e v ∧ G.Inc f v) :
    ∀ v ∈ L.vertexSet, ∃ e f, e ≠ f ∧ L.Inc e v ∧ L.Inc f v := by
  intro v hv
  obtain ⟨e, f, hef, he, hf⟩ := hG (φ.vertexEquiv ⟨v, hv⟩).val
    (φ.vertexEquiv ⟨v, hv⟩).property
  let e' := φ.edgeEquiv.symm ⟨e, he.edge_mem⟩
  let f' := φ.edgeEquiv.symm ⟨f, hf.edge_mem⟩
  refine ⟨e'.val, f'.val, ?_, ?_, ?_⟩
  · intro hval
    have heq : e' = f' := Subtype.ext hval
    have heq' := congrArg (fun q : L.edgeSet => (φ.edgeEquiv q).val) heq
    exact hef (by simpa only [e', f', φ.edgeEquiv.apply_symm_apply] using heq')
  · apply (iso_inc_iff φ e' ⟨v, hv⟩).mpr
    simpa only [e', φ.edgeEquiv.apply_symm_apply] using he
  · apply (iso_inc_iff φ f' ⟨v, hv⟩).mpr
    simpa only [f', φ.edgeEquiv.apply_symm_apply] using hf

end GraphMinor.GM12
