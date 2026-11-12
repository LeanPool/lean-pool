/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1RightRows
public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint

-- [TABLET NODE: P5332T1VectorPlacements]

/-!
# P5332T1VectorPlacements

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1VectorPlacements (P : FordFareyParameter) (hq : 1 < P.q) :
    let q := FordRecursiveQuadruple P
    (∀ j : Fin 3,
      BandVectors.1 (q 0) (q j.succ) = (P5332T1RightRows P j 0).displacement ∧
      BandVectors.2 (q 0) (q j.succ) = (P5332T1RightRows P j 0).linear) ∧
    ∀ (j : Fin 2) (k : Fin 4),
      let i : Fin 3 := ⟨j.val, by omega⟩
      let R := P5332T1ParentRows P j k 0
      (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ k.val *
            (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) =
        (((((![P.q₁, P.q₂] j : Nat) : ℝ) - P.q) / 2 + R.displacement.re),
         ((((![P.q₁, P.q₂] j : Nat) : ℝ) - P.q) / 2 + R.displacement.im)) ∧
      (1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ k.val *
            (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))) =
        (((((![P.p₁, P.p₂] j : Int) : ℝ) - P.p) / 2 + R.linear.re),
         ((((![P.p₁, P.p₂] j : Int) : ℝ) - P.p) / 2 + R.linear.im)) ∧
      (⟨0, 1⟩ : GaussianInt) ^ k.val *
        (if Even k.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0)) = R.companion := by
-- BODY
  classical
  dsimp only
  obtain ⟨hproper, hv1, hv2, hv3, ha1, ha2, ha3, _⟩ :=
    (FordCoordinateConfiguration P).2 hq
  have flip := (VectorRecursionLaws _ hproper.1).2.2.2.2 hproper
  have o0 := flip 0
  have o1 := flip 1
  have o2 := flip 2
  simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
    show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at o0 o1 o2
  rw [hv1, ha1] at o0
  rw [hv2, ha2] at o1
  rw [hv3, ha3] at o2
  constructor
  · intro j
    fin_cases j <;> simp [P5332T1RightRows, o0.1, o0.2, o1.1, o1.2, o2.1, o2.2,
      Zsqrtd.ext_iff]
  · intro j k
    have hqsum : (P.q : ℝ) = (P.q₁ : ℝ) + (P.q₂ : ℝ) := by
      exact_mod_cast P.sum_q
    have hpsum : (P.p : ℝ) = (P.p₁ : ℝ) + (P.p₂ : ℝ) := by
      exact_mod_cast P.sum_p
    fin_cases j <;> fin_cases k <;>
      norm_num [P5332T1ParentRows, hv1, hv2, ha1, ha2,
        o0.1, o0.2, o1.1, o1.2, GaussianRealPoint, Zsqrtd.ext_iff,
        pow_succ, GaussianInt.toComplex_def, Prod.ext_iff,
        show Even 0 from ⟨0, rfl⟩, show ¬ Even 1 by decide,
        show Even 2 from ⟨1, rfl⟩, show ¬ Even 3 by decide] <;>
        (repeat' constructor) <;> linarith

end ApollonianSuperharmonic

end
