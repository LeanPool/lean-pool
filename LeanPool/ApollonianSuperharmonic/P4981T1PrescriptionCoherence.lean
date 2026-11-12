/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4981T1PrescriptionValue
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.P4828T1ParentsDistinct

-- [TABLET NODE: P4981T1PrescriptionCoherence]

/-!
# P4981T1PrescriptionCoherence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4981T1PrescriptionCoherence {e : CircleCoordinates × CircleCoordinates}
    (p p' : P4981T1EdgePrescription e)
    (F : CircleCoordinates × CircleCoordinates → GaussianInt × GaussianInt) :
    P4981T1PrescriptionValue p F = P4981T1PrescriptionValue p' F := by
-- BODY
  have large (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) :
      1 < (q 0).1 := by
    have facts := ProperBandCurvatureStructure q hq
    have h0 := hq.2 0
    have h1 := hq.2 1
    have n0 := facts.2.1 0
    have n1 := facts.2.1 1
    by_contra hn
    have z0 : (q (0 : Fin 3).succ).1 = 0 := by omega
    have z1 : (q (1 : Fin 3).succ).1 = 0 := by omega
    have bad := facts.2.2 0 1 z0 z1
    exact (by decide : (0 : Fin 3) ≠ 1) bad
  have proper_equal (q q' : Fin 4 → CircleCoordinates)
      (hq : ProperBandQuadruple q) (hq' : ProperBandQuadruple q')
      (j j' : Fin 3) (hc : q 0 = q' 0) (hp : q j.succ = q' j'.succ) :
      P4981T1PrescriptionValue (.proper q hq j) F =
        P4981T1PrescriptionValue (.proper q' hq' j') F := by
    obtain ⟨r, hr, _⟩ := BandPredecessorNoCollision q q' hq hq' hc
    have idx : j = j' + r := P4828T1ParentsDistinct q hq (hp.trans (hr j'))
    have idx1 : j' + 1 + r = j + 1 := by omega
    have idx2 : j' + 2 + r = j + 2 := by omega
    simp only [P4981T1PrescriptionValue, hr, idx1, idx2, ← idx]
  have parameter (z w : GaussianInt)
      (h : 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt) =
        1 + 2 * w + 2 * (⟨0, 1⟩ : GaussianInt)) : z = w := by
    apply Zsqrtd.ext
    · have := congrArg Zsqrtd.re h
      simp at this
      omega
    · have := congrArg Zsqrtd.im h
      simp at this
      omega
  have general {e e' : CircleCoordinates × CircleCoordinates}
      (p : P4981T1EdgePrescription e) (p' : P4981T1EdgePrescription e')
      (he : e = e') :
      P4981T1PrescriptionValue p F = P4981T1PrescriptionValue p' F := by
    cases p <;> cases p'
    all_goals try rfl
    all_goals try { have hc := congrArg (fun e => e.2.1) he; norm_num at hc }
    all_goals try { have hp := congrArg (fun e => e.1.1) he; norm_num at hp }
    all_goals try { have hp := congrArg (fun e => e.1.2) he; norm_num at hp }
    all_goals try {
      have hc := congrArg (fun e => e.2.1) he
      have big := large _ (by assumption)
      dsimp at hc
      omega }
    all_goals try {
      have hz := parameter _ _ (congrArg (fun e => e.2.2) he)
      cases hz
      rfl }
    all_goals try {
      have hz := parameter _ _ (congrArg (fun e => e.1.2) he)
      cases hz
      rfl }
    exact proper_equal _ _ (by assumption) (by assumption) _ _
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  exact general p p' rfl

end ApollonianSuperharmonic

end
