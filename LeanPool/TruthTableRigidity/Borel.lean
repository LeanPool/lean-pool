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

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import LeanPool.TruthTableRigidity.BaireMain

/-!
# Borel functions induce only the trivial automorphism (Theorem 1.1)

If a Borel function `F` induces `π`, then `X ≤tt F(X)` for all `X` (from the Baire measurable
case).  Then we choose, Borel-ly, a preimage under `F` up to tt-equivalence: for each `Z`,
take the first triple `(Φ, Λ, Λ')` of tt-functionals (in a fixed enumeration) with
`Λ(F(Φ Z)) = Z` and `Λ'(Z) = F(Φ Z)`, and put `F'(Z) = Φ(Z)`.  This `F'` is Borel and induces
`π⁻¹`, so Remark 4.5 applies.

This replaces the appeal to the Lusin–Novikov uniformization theorem in Section 4.5 of the
note: the reduction `X ≤tt F(X)` makes the uniformization explicit.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-- An automorphism `π` of the tt-degrees is *induced by a Borel function* if some Borel
measurable `F : 2^ω → 2^ω` induces it. -/
def InducedByBorel (π : TTDegree ≃o TTDegree) : Prop :=
  ∃ F : Oracle → Oracle, Measurable F ∧ InducedBy π F

/-- If a Borel function induces `π`, then a Borel function induces `π⁻¹`. -/
theorem InducedByBorel.symm {π : TTDegree ≃o TTDegree} (h : InducedByBorel π) :
    InducedByBorel π.symm := by
  classical
  obtain ⟨F, hF, hπ⟩ := h
  have hle := ttReducible_self_of_baireMeasurable (.of_measurable hF) hπ
  let ι := {Φ : Oracle → Oracle // IsTTFunctional Φ}
  have : Nonempty ι := ⟨⟨id, isTTFunctional_id⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ι × ι × ι)
  let p : ℕ → Oracle → Prop := fun n Z =>
    (e n).2.1.1 (F ((e n).1.1 Z)) = Z ∧ (e n).2.2.1 Z = F ((e n).1.1 Z)
  have hcover : ∀ Z, ∃ n, p n Z := by
    intro Z
    obtain ⟨X, hX⟩ := ttDegree_surjective (π.symm (ttDegree Z))
    have hFX : ttDegree (F X) = ttDegree Z := by rw [hπ, hX, OrderIso.apply_symm_apply]
    obtain ⟨h1, h2⟩ := ttDegree_eq_iff.mp hFX
    obtain ⟨Φ, hΦ, hΦZ⟩ := (hle X).trans h1
    obtain ⟨Λ, hΛ, hΛZ⟩ := h2
    obtain ⟨Λ', hΛ', hΛ'Z⟩ := h1
    obtain ⟨n, hn⟩ := he (⟨Φ, hΦ⟩, ⟨Λ, hΛ⟩, ⟨Λ', hΛ'⟩)
    refine ⟨n, ?_, ?_⟩
    · rw [hn]; change Λ (F (Φ Z)) = Z; rw [hΦZ, hΛZ]
    · rw [hn]; change Λ' Z = F (Φ Z); rw [hΦZ, hΛ'Z]
  have hmeas : ∀ n, MeasurableSet {Z | p n Z} := by
    intro n
    have c1 : Measurable fun Z => F ((e n).1.1 Z) := hF.comp (e n).1.2.continuous.measurable
    exact (measurableSet_eq_fun ((e n).2.1.2.continuous.measurable.comp c1) measurable_id).inter
      (measurableSet_eq_fun (e n).2.2.2.continuous.measurable c1)
  refine ⟨fun Z => (e (Nat.find (hcover Z))).1.1 Z,
    Measurable.find (fun n => (e n).1.2.continuous.measurable) hmeas hcover, fun Z => ?_⟩
  have h := Nat.find_spec (hcover Z)
  set n := Nat.find (hcover Z)
  have e1 : ttDegree (F ((e n).1.1 Z)) = ttDegree Z :=
    ttDegree_eq_iff.mpr ⟨⟨(e n).2.2.1, (e n).2.2.2, h.2⟩, ⟨(e n).2.1.1, (e n).2.1.2, h.1⟩⟩
  rw [hπ] at e1
  change ttDegree ((e n).1.1 Z) = π.symm (ttDegree Z)
  rw [← e1, OrderIso.symm_apply_apply]

/-- An automorphism of the truth-table degrees which is induced by a Borel
function `F : 2^ω → 2^ω` is the identity. -/
theorem eq_refl_of_inducedByBorel {π : TTDegree ≃o TTDegree} (h : InducedByBorel π) :
    π = OrderIso.refl TTDegree := by
  obtain ⟨F', hF', hπ'⟩ := h.symm
  obtain ⟨F, hF, hπ⟩ := h
  exact eq_refl_of_inducedByBorel_of_symm hF hπ hF' hπ'

/-- Moreover, a Borel `F` inducing an automorphism satisfies `F(X) ≡tt X` for all `X`. -/
theorem ttEquiv_of_inducedBy_borel {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : Measurable F) (hπ : InducedBy π F) (X : Oracle) :
    TTReducible (F X) X ∧ TTReducible X (F X) := by
  have := hπ X
  rw [eq_refl_of_inducedByBorel ⟨F, hF, hπ⟩] at this
  exact ttDegree_eq_iff.mp this

end TT
