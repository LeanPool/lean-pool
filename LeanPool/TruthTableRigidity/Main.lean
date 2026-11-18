/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import LeanPool.TruthTableRigidity.Prop31

/-!
# Continuous functions induce only the trivial automorphism of the tt-degrees

The rigidity conclusion of Theorem 1.3 in the paper says that an automorphism `π` of the
truth-table degrees induced by a continuous function `F : 2^ω → 2^ω` is the identity.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-- **Proposition 3.3.** If a continuous function induces `π`, then `π⁻¹` is induced by a
tt-functional. -/
theorem prop_3_3 {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle} (hF : Continuous F)
    (hπ : InducedBy π F) : ∃ F' : Oracle → Oracle, IsTTFunctional F' ∧ InducedBy π.symm F' := by
  have hP := hπ.inducesProperties
  have hle : ∀ X, TTReducible X (F X) := le_tt_of_prop_3_1 hF hP
  -- every `Z` is tt-equivalent to `F (Φ Z)` for suitable tt-functionals
  let C (w : InverseWitness) : Set Oracle := {Z | w.valid F Z}
  have hclosed : ∀ t, IsClosed (C t) := by
    intro t
    have c1 : Continuous fun Z => F (t.1.1 Z) := hF.comp t.1.2.continuous
    exact (isClosed_eq (t.2.1.2.continuous.comp c1) continuous_id).inter
      (isClosed_eq t.2.2.2.continuous c1)
  have hcover : ⋃ t, C t = Set.univ := by
    apply Set.eq_univ_of_forall
    intro Z
    obtain ⟨w, hw⟩ := hπ.exists_inverse_witness hle Z
    exact Set.mem_iUnion.mpr ⟨w, hw⟩
  obtain ⟨t, Z₀, hZ₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨k, hk⟩ := exists_cyl_subset isOpen_interior hZ₀
  set σ := pre Z₀ k
  have hσ : ∀ W, prep σ W ∈ C t := fun W =>
    interior_subset (hk (by rw [← Ncyl_pre]; exact prep_mem σ W))
  refine ⟨fun Z => t.1.1 (prep σ Z), t.1.2.comp (isTTFunctional_prep σ), fun Z => ?_⟩
  have e1 : ttDegree (F (t.1.1 (prep σ Z))) = ttDegree Z :=
    (InverseWitness.degree_eq (hσ Z)).trans (ttDegree_eq_iff.mpr (prep_ttEquiv σ Z))
  rw [hπ] at e1
  rw [← e1, OrderIso.symm_apply_apply]

/-- **Rigidity conclusion of Theorem 1.3.** An automorphism of the truth-table degrees
induced by a continuous function `F : 2^ω → 2^ω` is the identity. -/
theorem eq_refl_of_inducedByContinuous {π : TTDegree ≃o TTDegree}
    (h : InducedByContinuous π) : π = OrderIso.refl TTDegree := by
  obtain ⟨F, hF, hπ⟩ := h
  obtain ⟨F', hF', hπ'⟩ := prop_3_3 hF hπ
  have hle : ∀ Z, TTReducible Z (F' Z) :=
    le_tt_of_prop_3_1 hF'.continuous hπ'.inducesProperties
  have hsymm : ∀ a, π.symm a = a := by
    intro a
    obtain ⟨Z, rfl⟩ := ttDegree_surjective a
    rw [← hπ' Z, ttDegree_eq_iff]
    exact ⟨ttReducible_of_isTTFunctional hF' Z, hle Z⟩
  ext a
  have := hsymm (π a)
  rw [OrderIso.symm_apply_apply] at this
  exact this.symm

/-- Restatement: every degree is fixed. -/
theorem inducedByContinuous_apply {π : TTDegree ≃o TTDegree} (h : InducedByContinuous π)
    (a : TTDegree) : π a = a := by
  rw [eq_refl_of_inducedByContinuous h]; rfl

/-- Moreover, a continuous `F` inducing an automorphism satisfies `F X ≡tt X` for all `X`. -/
theorem ttEquiv_of_inducedBy_continuous {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : Continuous F) (hπ : InducedBy π F) (X : Oracle) :
    TTReducible (F X) X ∧ TTReducible X (F X) := by
  have := hπ X
  rw [inducedByContinuous_apply ⟨F, hF, hπ⟩] at this
  exact ttDegree_eq_iff.mp this

end TT
