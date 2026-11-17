/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: BandPackingSymmetryProperCovariance]

/-!
# BandPackingSymmetryProperCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPackingSymmetryProperCovariance (g : BandPackingSymmetry)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) :
    ProperBandQuadruple (BandPackingSymmetryQuadrupleAction g q) := by
-- BODY
  let R := fun r : Fin 4 → CircleCoordinates => ![r 0, r 2, r 3, r 1]
  let S := fun r : Fin 4 → CircleCoordinates =>
    ![(2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1,
       2 * (r 0).2 + 2 * (r 2).2 + 2 * (r 3).2 - (r 1).2),
      r 0, r 2, r 3]
  let Q := BandPackingSymmetryQuadrupleAction
  let root := fun z : GaussianInt =>
    (![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
       (0, 1), (0, -1)] : Fin 4 → CircleCoordinates)
  -- The first proper successors of the two rotated roots.
  let A := fun z => S (R (root z))
  let B := fun z => S (R (R (root z)))
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  have curvature (a : BandPackingSymmetry) (C : CircleCoordinates) :
      (BandPackingSymmetryCircleAction a C).1 = C.1 := by
    induction a generalizing C with
    | identity => rfl
    | negate => rfl
    | conjugate => rfl
    | shift w => rfl
    | comp a b iha ihb => simp [BandPackingSymmetryCircleAction, iha, ihb]
  have inequalities (a : BandPackingSymmetry) (r : Fin 4 → CircleCoordinates)
      (hp : ProperBandQuadruple r) :
      ∀ j : Fin 3, ((Q a r) j.succ).1 < ((Q a r) 0).1 := by
    intro j
    cases he : BandPackingSymmetryReversesOrientation a <;> fin_cases j
    all_goals
      first
      | simpa [Q, BandPackingSymmetryQuadrupleAction, he, curvature, neg1, neg2] using hp.2 0
      | simpa [Q, BandPackingSymmetryQuadrupleAction, he, curvature, neg1, neg2] using hp.2 1
      | simpa [Q, BandPackingSymmetryQuadrupleAction, he, curvature, neg1, neg2] using hp.2 2
  have rotate_action (a : BandPackingSymmetry) (r : Fin 4 → CircleCoordinates) :
      Q a (R r) = if BandPackingSymmetryReversesOrientation a then
        R (R (Q a r)) else R (Q a r) := by
    cases he : BandPackingSymmetryReversesOrientation a <;>
      funext k <;> fin_cases k <;>
      simp [Q, R, BandPackingSymmetryQuadrupleAction, he, neg1, neg2]
  have successor_action (a : BandPackingSymmetry)
      (ha : a = .negate ∨ a = .conjugate ∨ ∃ w, a = .shift w)
      (r : Fin 4 → CircleCoordinates) : Q a (S r) = S (Q a r) := by
    rcases ha with rfl | rfl | ⟨w, rfl⟩
    all_goals
      funext k
      fin_cases k
      all_goals
        apply Prod.ext
        · simp [Q, S, BandPackingSymmetryQuadrupleAction,
            BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation, neg1, neg2]
          all_goals ring
        · apply Zsqrtd.ext <;>
            simp [Q, S, BandPackingSymmetryQuadrupleAction,
              BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation,
              GaussianReflection, neg1, neg2] <;> ring
  have semiA (z : GaussianInt) : SemiProperQuadruple (A z) :=
    SemiProperQuadruple.successor (SemiProperQuadruple.rotate (SemiProperQuadruple.base z))
  have semiB (z : GaussianInt) : SemiProperQuadruple (B z) :=
    SemiProperQuadruple.successor
      (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate (SemiProperQuadruple.base z)))
  have negateA (z : GaussianInt) : Q .negate (A z) = R (B (-1 - z - ⟨0, 1⟩)) := by
    funext k
    fin_cases k <;> apply Prod.ext
    all_goals
      simp [Q, A, B, R, S, root, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation]
    all_goals ring
  have negateB (z : GaussianInt) : Q .negate (B z) = R (R (A (-1 - z - ⟨0, 1⟩))) := by
    funext k
    fin_cases k <;> apply Prod.ext
    all_goals
      simp [Q, A, B, R, S, root, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation]
    all_goals ring
  have conjugateA (z : GaussianInt) :
      Q .conjugate (A z) = R (R (A (GaussianReflection z - ⟨0, 1⟩))) := by
    funext k
    fin_cases k <;> apply Prod.ext <;> try apply Zsqrtd.ext
    all_goals
      simp [Q, A, R, S, root, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation,
        GaussianReflection, neg1, neg2]
    all_goals ring
  have conjugateB (z : GaussianInt) :
      Q .conjugate (B z) = R (B (GaussianReflection z - ⟨0, 1⟩)) := by
    funext k
    fin_cases k <;> apply Prod.ext <;> try apply Zsqrtd.ext
    all_goals
      simp [Q, B, R, S, root, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation,
        GaussianReflection, neg1, neg2]
    all_goals ring
  have shiftA (w z : GaussianInt) : Q (.shift w) (A z) = A (z + w) := by
    funext k
    fin_cases k <;> apply Prod.ext
    all_goals
      simp [Q, A, R, S, root, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation]
    all_goals ring
  have shiftB (w z : GaussianInt) : Q (.shift w) (B z) = B (z + w) := by
    funext k
    fin_cases k <;> apply Prod.ext
    all_goals
      simp [Q, B, R, S, root, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryReversesOrientation]
    all_goals ring
  have firstA (a : BandPackingSymmetry)
      (ha : a = .negate ∨ a = .conjugate ∨ ∃ w, a = .shift w)
      (z : GaussianInt) : SemiProperQuadruple (Q a (A z)) := by
    rcases ha with rfl | rfl | ⟨w, rfl⟩
    · rw [negateA]
      exact SemiProperQuadruple.rotate (semiB _)
    · rw [conjugateA]
      exact SemiProperQuadruple.rotate (SemiProperQuadruple.rotate (semiA _))
    · rw [shiftA]
      exact semiA _
  have firstB (a : BandPackingSymmetry)
      (ha : a = .negate ∨ a = .conjugate ∨ ∃ w, a = .shift w)
      (z : GaussianInt) : SemiProperQuadruple (Q a (B z)) := by
    rcases ha with rfl | rfl | ⟨w, rfl⟩
    · rw [negateB]
      exact SemiProperQuadruple.rotate (SemiProperQuadruple.rotate (semiA _))
    · rw [conjugateB]
      exact SemiProperQuadruple.rotate (semiB _)
    · rw [shiftB]
      exact semiB _
  -- Only proper inputs are transported through the semi-proper forest.
  have generator (a : BandPackingSymmetry)
      (ha : a = .negate ∨ a = .conjugate ∨ ∃ w, a = .shift w)
      (r : Fin 4 → CircleCoordinates) (hs : SemiProperQuadruple r) :
      ProperBandQuadruple r → ProperBandQuadruple (Q a r) := by
    induction hs with
    | base z =>
        intro hp
        have bad := hp.2 (0 : Fin 3)
        norm_num at bad
    | @rotate r hs ih =>
        intro hp
        have old : ProperBandQuadruple r := by
          refine ⟨hs, ?_⟩
          intro j
          fin_cases j
          · simpa using hp.2 2
          · simpa using hp.2 0
          · simpa using hp.2 1
        refine ⟨?_, inequalities a _ hp⟩
        change SemiProperQuadruple (Q a (R r))
        rw [rotate_action]
        cases BandPackingSymmetryReversesOrientation a
        · exact SemiProperQuadruple.rotate (ih old).1
        · exact SemiProperQuadruple.rotate (SemiProperQuadruple.rotate (ih old).1)
    | @successor r hs ih =>
        intro hp
        refine ⟨?_, inequalities a _ hp⟩
        change SemiProperQuadruple (Q a (S r))
        rcases (SemiProperForestClassification r hs).2 with root0 | root1 | root2 | proper
        · rcases root0 with ⟨z, hz⟩
          have bad := hp.2 (0 : Fin 3)
          rw [hz] at bad
          simp at bad
        · rcases root1 with ⟨z, hz⟩
          have eq : r = R (root z) := by
            rw [hz]
            funext k
            fin_cases k <;> rfl
          rw [eq]
          exact firstA a ha z
        · rcases root2 with ⟨z, hz⟩
          have eq : r = R (R (root z)) := by
            rw [hz]
            funext k
            fin_cases k <;> rfl
          rw [eq]
          exact firstB a ha z
        · rw [successor_action a ha]
          exact SemiProperQuadruple.successor (ih proper).1
  have composition (a b : BandPackingSymmetry) (r : Fin 4 → CircleCoordinates) :
      Q (.comp a b) r = Q a (Q b r) := by
    cases ha : BandPackingSymmetryReversesOrientation a <;>
      cases hb : BandPackingSymmetryReversesOrientation b <;>
      funext k <;> fin_cases k <;>
      simp [Q, BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
        BandPackingSymmetryReversesOrientation, ha, hb, neg1, neg2]
  induction g generalizing q with
  | identity =>
      have eq : Q .identity q = q := by
        funext k
        fin_cases k <;> rfl
      change ProperBandQuadruple (Q .identity q)
      rw [eq]
      exact hq
  | negate => exact generator .negate (Or.inl rfl) q hq.1 hq
  | conjugate => exact generator .conjugate (Or.inr (Or.inl rfl)) q hq.1 hq
  | shift w => exact generator (.shift w) (Or.inr (Or.inr ⟨w, rfl⟩)) q hq.1 hq
  | comp a b iha ihb =>
      change ProperBandQuadruple (Q (.comp a b) q)
      rw [composition]
      exact iha _ (ihb q hq)

end ApollonianSuperharmonic

end
