/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ValidClosed

/-!
# Shared and indexed replay of closed affine certificates

Slope and endpoint checks depend on the core, divisor, anchor and witness, independently of the
cone. A checked witness pool shares those calculations across cells. Each cell proves that its
witness selection belongs to the pool and checks its remaining affine rows using explicit hints.

The generated closed covers list their coordinate segment forms first. Other required forms are
zero or occur in the cone. Zero forms finish without reading a hint. When a cone row is used,
the checker tests its bound and affine equality. The soundness theorem recovers the original
checker result, including every cached geometry condition.
-/

@[expose] public section

open Utilities.Certificate ExplicitPotential

namespace Utilities.Certificate.AffineCover.AffineForm

/-- Accept zero forms immediately, or check cone row `index` with hint `index + 1`. -/
def checkMembershipAt {dimension : ℕ} (form : AffineForm dimension)
    (cone : List (AffineForm dimension)) (index : ℕ) : Bool :=
  equal form 0 ||
    match index with
    | 0 => false
    | index + 1 => decide (index < cone.length) && equal form (cone.getD index 0)

/-- An accepted hint proves the original zero-or-membership condition. -/
theorem checkMembershipAt_sound {dimension : ℕ} (form : AffineForm dimension)
    (cone : List (AffineForm dimension)) (index : ℕ)
    (checked : checkMembershipAt form cone index = true) : form = 0 ∨ form ∈ cone := by
  obtain zero | indexed := Bool.or_eq_true_iff.mp checked
  · exact Or.inl ((equal_eq_true_iff _ _).mp zero)
  · cases index with
    | zero => cases indexed
    | succ index =>
      obtain ⟨inBounds, equalForm⟩ := Bool.and_eq_true_iff.mp indexed
      have bound : index < cone.length := of_decide_eq_true inBounds
      have equation := (equal_eq_true_iff _ _).mp equalForm
      rw [List.getD_eq_getElem cone 0 bound] at equation
      exact Or.inr (equation ▸ List.getElem_mem bound)

end Utilities.Certificate.AffineCover.AffineForm

namespace Utilities.Certificate.ExplicitPotential.CertificateData

/-- Cone-independent slope and endpoint checks for one anchored witness. -/
def checkAnchorWitness {dimension vertices edges : ℕ}
    (core : Core vertices edges) (divisor : Fin vertices → ℤ)
    (witness : AnchorWitness dimension vertices edges) (anchor : Fin vertices) : Bool :=
  (allFin fun edge : Fin edges => decide (witness.alpha edge + witness.beta edge ≤ 0)) &&
  (allFin fun vertex : Fin vertices =>
    decide (0 ≤ (divisor vertex - (if vertex = anchor then 1 else 0)) +
      ∑ edge : Fin edges,
        ((if core.tail edge = vertex then witness.alpha edge else 0) +
          (if core.head edge = vertex then witness.beta edge else 0))))

/-- Check each used anchor/witness pair once, independently of its cell's cone. -/
def checkWitnessPool {dimension vertices edges : ℕ}
    (core : Core vertices edges) (divisor : Fin vertices → ℤ)
    (witnesses : List (AnchorWitness dimension vertices edges))
    (fallback : AnchorWitness dimension vertices edges) (allowed : List (List ℕ)) : Bool :=
  allFin fun anchor : Fin vertices => (allowed.getD anchor.val []).all fun index =>
    checkAnchorWitness core divisor (witnesses.getD index fallback) anchor

/-- A selection from a checked pool reuses its verified anchor geometry. -/
theorem checkWitnessSelection {dimension vertices edges : ℕ}
    (core : Core vertices edges) (divisor : Fin vertices → ℤ)
    (witnesses : List (AnchorWitness dimension vertices edges))
    (fallback : AnchorWitness dimension vertices edges) (allowed : List (List ℕ))
    (selection : List ℕ)
    (poolChecked : checkWitnessPool core divisor witnesses fallback allowed = true)
    (selectionChecked : (allFin fun anchor : Fin vertices =>
      decide (selection.getD anchor.val 0 ∈ allowed.getD anchor.val [])) = true) :
    ∀ anchor : Fin vertices,
      checkAnchorWitness core divisor
        (witnesses.getD (selection.getD anchor.val 0) fallback) anchor = true := by
  intro anchor
  have pool := (allFin_eq_true_iff _).mp poolChecked anchor
  have member := of_decide_eq_true ((allFin_eq_true_iff _).mp selectionChecked anchor)
  exact (List.all_eq_true.mp pool) _ member

/-- Check the loop, degree, segment and affine rows after sharing anchor geometry. -/
def checkClosedRows {dimension vertices edges : ℕ}
    (certificate : CertificateData dimension vertices edges) (degree : ℤ)
    (indices : List (List ℕ)) : Bool :=
  (allFin fun edge : Fin edges =>
    decide (certificate.core.tail edge ≠ certificate.core.head edge)) &&
  decide ((∑ vertex : Fin vertices, certificate.divisor vertex) = degree) &&
  (allFin fun edge : Fin edges =>
    AffineCover.AffineForm.checkMembershipAt (certificate.segment edge) certificate.cone
      (edge.val + 1)) &&
  (allFin fun anchor : Fin vertices =>
    allFin fun edge : Fin edges =>
      AffineCover.AffineForm.checkMembershipAt (certificate.lowerForm anchor edge) certificate.cone
        ((indices.getD anchor.val []).getD (2 * edge.val) 0) &&
      AffineCover.AffineForm.checkMembershipAt (certificate.upperForm anchor edge) certificate.cone
        ((indices.getD anchor.val []).getD (2 * edge.val + 1) 0))

/-- Cached anchor geometry and indexed rows recover the original closed-certificate check. -/
theorem checkClosedRows_sound {dimension vertices edges : ℕ}
    (certificate : CertificateData dimension vertices edges) (degree : ℤ)
    (indices : List (List ℕ))
    (anchorChecks : ∀ anchor : Fin vertices,
      checkAnchorWitness certificate.core certificate.divisor
        (certificate.witness anchor) anchor = true)
    (checked : certificate.checkClosedRows degree indices = true) :
    certificate.checkClosed degree = true := by
  apply (checkClosed_eq_true_iff _ _).mpr
  simp only [checkClosedRows, Bool.and_eq_true, allFin_eq_true_iff,
    decide_eq_true_eq] at checked
  obtain ⟨⟨⟨loopless, degreeSum⟩, segments⟩, forms⟩ := checked
  have anchors anchor := Bool.and_eq_true_iff.mp (anchorChecks anchor)
  refine ⟨loopless, degreeSum, ?_, ?_, ?_, ?_⟩
  · intro anchor edge
    exact of_decide_eq_true ((allFin_eq_true_iff _).mp (anchors anchor).1 edge)
  · intro anchor vertex
    exact of_decide_eq_true ((allFin_eq_true_iff _).mp (anchors anchor).2 vertex)
  · intro edge
    exact Or.inr (Or.inr (AffineCover.AffineForm.checkMembershipAt_sound _ _ _ (segments edge)))
  · intro anchor edge
    exact ⟨AffineCover.AffineForm.checkMembershipAt_sound _ _ _ (forms anchor edge).1,
      AffineCover.AffineForm.checkMembershipAt_sound _ _ _ (forms anchor edge).2⟩

end Utilities.Certificate.ExplicitPotential.CertificateData
