/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1HistoryNormalForm
public import LeanPool.ApollonianSuperharmonic.P4828T1HistoryRealization
public import LeanPool.ApollonianSuperharmonic.P4828T1RootSeparation
public import LeanPool.ApollonianSuperharmonic.P4828T1FiniteWordSeparation
public import LeanPool.ApollonianSuperharmonic.P4828T1ParentsDistinct

-- [TABLET NODE: BandPredecessorNoCollision]

/-!
# BandPredecessorNoCollision

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPredecessorNoCollision (q q' : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (hq' : ProperBandQuadruple q')
    (hchild : q 0 = q' 0) :
    ∃! r : Fin 3, ∀ j : Fin 3, q' j.succ = q ((j + r).succ) := by
-- BODY
  let G (a : GaussianInt × Bool) (w : List (Fin 3)) :=
    P4828T1Gap (2 * (a.1.re : Real)) (P4828T1Evaluate a.1 a.2 w)
  let D (a : GaussianInt × Bool) (w : List (Fin 3)) :=
    P4828T1Disk (P4828T1Evaluate a.1 a.2 w 0)
  have separated := P4828T1FiniteWordSeparation G D
    (fun a b h => P4828T1RootSeparation a.1 b.1 a.2 b.2
      (by simpa only [Prod.mk.eta] using h))
    (fun a w b => (P4828T1HistoryRealization a.1 a.2 w).2.1 b |>.1)
    (fun a w b c h => (P4828T1HistoryRealization a.1 a.2 w).2.2 b c h)
    (fun a w b => (P4828T1HistoryRealization a.1 a.2 w).2.1 b |>.2)
    (fun a w => (P4828T1HistoryRealization a.1 a.2 w).1.2.2)
    (by
      intro a w
      have pos := (ProperBandCurvatureStructure _
        (P4828T1HistoryRealization a.1 a.2 w).1.1).1
      refine ⟨(P4828T1Evaluate a.1 a.2 w 0).2 /
        ((P4828T1Evaluate a.1 a.2 w 0).1 : Real), ?_⟩
      change dist _ _ < 1 / ((P4828T1Evaluate a.1 a.2 w 0).1 : Real)
      rw [dist_self]
      exact one_div_pos.mpr (by exact_mod_cast pos))
  obtain ⟨a, e, w, r, hqrep⟩ := P4828T1HistoryNormalForm q hq
  obtain ⟨a', e', w', r', hq'rep⟩ := P4828T1HistoryNormalForm q' hq'
  have hcoord : P4828T1Evaluate a e w 0 = P4828T1Evaluate a' e' w' 0 := by
    simpa only [hqrep, hq'rep, P4828T1Rotate, Fin.cases_zero] using hchild
  have hindex : ((a, e), w) = ((a', e'), w') := by
    by_contra hne
    have hdis := separated.2.2.2 (a, e) (a', e') w w' hne
    have pos := (ProperBandCurvatureStructure _
      (P4828T1HistoryRealization a e w).1.1).1
    have hp : ((P4828T1Evaluate a e w 0).2 : Complex) /
        ((P4828T1Evaluate a e w 0).1 : Real) ∈ D (a, e) w := by
      change dist _ _ < 1 / ((P4828T1Evaluate a e w 0).1 : Real)
      rw [dist_self]
      exact one_div_pos.mpr (by exact_mod_cast pos)
    have heq : D (a, e) w = D (a', e') w' := congrArg P4828T1Disk hcoord
    exact Set.disjoint_left.mp hdis hp (by rwa [← heq])
  have ha : a = a' := congrArg (fun x => x.1.1) hindex
  have he : e = e' := congrArg (fun x => x.1.2) hindex
  have hw : w = w' := congrArg Prod.snd hindex
  subst a'
  subst e'
  subst w'
  refine ⟨r' - r, ?_, ?_⟩
  · intro j
    rw [hqrep, hq'rep]
    simp only [P4828T1Rotate, Fin.cases_succ]
    congr 2
    omega
  · intro s hs
    have eqs := hs (0 : Fin 3)
    have eqr : q' (0 : Fin 3).succ = q ((0 + (r' - r)).succ) := by
      rw [hqrep, hq'rep]
      simp only [P4828T1Rotate, Fin.cases_succ]
      congr 2
      omega
    have idx := P4828T1ParentsDistinct q hq (eqs.symm.trans eqr)
    simpa using idx

end ApollonianSuperharmonic

end
