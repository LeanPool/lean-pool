/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-!
# Indexed replay of closed-cover cell rows

The generated hints specify either a zero affine form or a row in the cell's cone.
For a witness with zero slopes and zero potentials, all its row forms are zero.
The transfer lemma recovers the original Boolean check in both cases.
-/

@[expose] public section

namespace Utilities.Certificate.AffineCover.AffineForm

/-- Check zero for a zero hint and look up the specified row for a positive hint. -/
def checkMembershipAtHint {dimension : ℕ} (form : AffineForm dimension)
    (cone : List (AffineForm dimension)) (hint : ℕ) : Bool :=
  match hint with
  | 0 => equal form 0
  | index + 1 =>
    (match cone[index]? with
     | none => false
     | some row => equal form row) || equal form 0

/-- A successful direct lookup also satisfies the original membership checker. -/
theorem checkMembershipAt_of_checkMembershipAtHint {dimension : ℕ} (form : AffineForm dimension)
    (cone : List (AffineForm dimension)) (hint : ℕ)
    (checked : checkMembershipAtHint form cone hint = true) :
    checkMembershipAt form cone hint = true := by
  apply Bool.or_eq_true_iff.mpr
  cases hint with
  | zero => exact Or.inl checked
  | succ index =>
    simp only [checkMembershipAtHint, Bool.or_eq_true] at checked
    obtain indexed | zero := checked
    · right
      cases atRow : cone[index]? with
      | none => simp [atRow] at indexed
      | some row =>
        have bound : index < cone.length := (List.getElem?_eq_some_iff.mp atRow).choose
        have equalRow : equal form row = true := by simpa only [atRow] using indexed
        change (decide (index < cone.length) && equal form (cone.getD index 0)) = true
        rw [List.getD_eq_getElem?_getD, atRow]
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true bound, equalRow⟩
    · exact Or.inl zero

end Utilities.Certificate.AffineCover.AffineForm

namespace Utilities.Certificate.ExplicitPotential.CertificateData

open AffineCover.AffineForm

/-- Recognize the shared witness with zero slopes and zero vertex potentials. -/
def isZeroWitness {dimension vertices edges : ℕ}
    (witness : AnchorWitness dimension vertices edges) : Bool :=
  (allFin fun edge => decide (witness.alpha edge = 0) && decide (witness.beta edge = 0)) &&
    (allFin fun vertex => AffineCover.AffineForm.equal (witness.potential vertex) 0)

private theorem checks_of_isZeroWitness {dimension vertices edges : ℕ}
    (certificate : CertificateData dimension vertices edges)
    (indices : List (List ℕ)) (anchor : Fin vertices) (edge : Fin edges)
    (zero : isZeroWitness (certificate.witness anchor) = true) :
    AffineCover.AffineForm.checkMembershipAt (certificate.lowerForm anchor edge) certificate.cone
      ((indices.getD anchor.val []).getD (2 * edge.val) 0) = true ∧
    AffineCover.AffineForm.checkMembershipAt (certificate.upperForm anchor edge) certificate.cone
      ((indices.getD anchor.val []).getD (2 * edge.val + 1) 0) = true := by
  simp only [isZeroWitness, Bool.and_eq_true, allFin_eq_true_iff, decide_eq_true_eq,
    AffineCover.AffineForm.equal_eq_true_iff] at zero
  obtain ⟨slopes, potential⟩ := zero
  have zeroLower : certificate.lowerForm anchor edge = 0 := by
    simp only [lowerForm, rise, potential, (slopes edge).1]
    cases certificate.segment edge with
    | mk fixed coefficient =>
      simp [AffineForm.sub, AffineForm.scale]
      rfl
  have zeroUpper : certificate.upperForm anchor edge = 0 := by
    simp only [upperForm, rise, potential, (slopes edge).2, neg_zero]
    cases certificate.segment edge with
    | mk fixed coefficient =>
      simp [AffineForm.sub, AffineForm.scale]
      rfl
  have acceptsZero (hint : ℕ) :
      AffineCover.AffineForm.checkMembershipAt (0 : ExplicitPotential.AffineForm dimension)
        certificate.cone hint = true :=
    Bool.or_eq_true_iff.mpr (Or.inl ((AffineCover.AffineForm.equal_eq_true_iff _ _).mpr rfl))
  exact ⟨zeroLower.symm ▸ acceptsZero _, zeroUpper.symm ▸ acceptsZero _⟩

/-- Check the cell rows by direct lookup, guided by the generated hints. -/
def checkClosedRowsAtHints {dimension vertices edges : ℕ}
    (certificate : CertificateData dimension vertices edges) (degree : ℤ)
    (indices : List (List ℕ)) : Bool :=
  (allFin fun edge : Fin edges =>
    decide (certificate.core.tail edge ≠ certificate.core.head edge)) &&
  decide ((∑ vertex : Fin vertices, certificate.divisor vertex) = degree) &&
  (allFin fun edge : Fin edges =>
    checkMembershipAtHint (certificate.segment edge) certificate.cone (edge.val + 1)) &&
  (allFin fun anchor : Fin vertices =>
    isZeroWitness (certificate.witness anchor) ||
      (allFin fun edge : Fin edges =>
        checkMembershipAtHint (certificate.lowerForm anchor edge) certificate.cone
          ((indices.getD anchor.val []).getD (2 * edge.val) 0) &&
        checkMembershipAtHint (certificate.upperForm anchor edge) certificate.cone
          ((indices.getD anchor.val []).getD (2 * edge.val + 1) 0)))

/-- Directly checked hints establish the original cell row checks. -/
theorem checkClosedRows_of_checkClosedRowsAtHints {dimension vertices edges : ℕ}
    {certificate : CertificateData dimension vertices edges} {degree : ℤ}
    {indices : List (List ℕ)} (checked : certificate.checkClosedRowsAtHints degree indices = true) :
    certificate.checkClosedRows degree indices = true := by
  simp only [checkClosedRowsAtHints, Bool.and_eq_true, allFin_eq_true_iff] at checked
  obtain ⟨⟨⟨loopless, degreeSum⟩, segments⟩, forms⟩ := checked
  simp only [checkClosedRows, Bool.and_eq_true, allFin_eq_true_iff]
  refine ⟨⟨⟨loopless, degreeSum⟩,
    fun edge => checkMembershipAt_of_checkMembershipAtHint _ _ _ (segments edge)⟩, ?_⟩
  intro anchor edge
  obtain zero | hintChecks := Bool.or_eq_true_iff.mp (forms anchor)
  · exact checks_of_isZeroWitness certificate indices anchor edge zero
  · obtain ⟨lower, upper⟩ := Bool.and_eq_true_iff.mp ((allFin_eq_true_iff _).mp hintChecks edge)
    exact ⟨checkMembershipAt_of_checkMembershipAtHint _ _ _ lower,
      checkMembershipAt_of_checkMembershipAtHint _ _ _ upper⟩

end Utilities.Certificate.ExplicitPotential.CertificateData
