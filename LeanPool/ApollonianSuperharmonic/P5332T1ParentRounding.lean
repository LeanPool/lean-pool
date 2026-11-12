/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic
public import LeanPool.ApollonianSuperharmonic.P5332T1SignedParentIntervals

-- [TABLET NODE: P5332T1ParentRounding]

/-!
# P5332T1ParentRounding

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1ParentRounding (P : FordFareyParameter) (hq : 1 < P.q)
    (j : Fin 2) (k : Fin 4) (t : Int) (ht : 0 ≤ t)
    (ht' : t < ((![P.q₁, P.q₂] j : Nat) : Int)) :
    let V := (P5332T1ParentRows P j k t).values
    V 1 + V 2 + V 3 + V 4 - 4 * V 0 =
      if t = 0 ∧ Even (k.val + j.val) then 0 else 1 := by
-- BODY
  obtain ⟨hr, hrl, hs, hsl, _⟩ := P5130T5ParentArithmetic P hq
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have hr' : 0 < (P.q₁ : Int) := by exact_mod_cast hr
  have hs' : 0 < (P.q₂ : Int) := by exact_mod_cast hs
  have hrl' : (P.q₁ : Int) < P.q := by exact_mod_cast hrl
  have hsl' : (P.q₂ : Int) < P.q := by exact_mod_cast hsl
  have det1 : P.p₁ * (P.q : Int) - P.p * (P.q₁ : Int) = 1 := by
    nlinarith [P.det₁]
  have det2 : P.p₂ * (P.q : Int) - P.p * (P.q₂ : Int) = -1 := by
    nlinarith [P.det₂]
  have fm (K : Int) : (K*(P.q : Int)-1)/(P.q : Int) = K-1 := by
    apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
    constructor <;> nlinarith
  have fp (K : Int) : (K*(P.q : Int)+1)/(P.q : Int) = K := by
    apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
    constructor <;> nlinarith
  have cm (K : Int) : -((-(K*(P.q : Int)-1))/(P.q : Int)) = K := by
    have hh : (-(K*(P.q : Int)-1))/(P.q : Int) = -K := by
      apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
      constructor <;> nlinarith
    rw [hh]
    ring
  have cp (K : Int) : -((-(K*(P.q : Int)+1))/(P.q : Int)) = K+1 := by
    have hh : (-(K*(P.q : Int)+1))/(P.q : Int) = -(K+1) := by
      apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
      constructor <;> nlinarith
    rw [hh]
    ring
  by_cases ht0 : t = 0
  · subst t
    have hpr : P.p * (P.q₁ : Int) = P.p₁ * (P.q : Int) - 1 := by omega
    have hps : P.p * (P.q₂ : Int) = P.p₂ * (P.q : Int) + 1 := by omega
    have cq1 : -((-1)/(P.q : Int)) = 1 := by simpa using cp 0
    have cqneg1 : -(1/(P.q : Int)) = 0 := by simpa using cm 0
    have fq1 : 1/(P.q : Int) = 0 := by simpa using fp 0
    have fqneg1 : (-1)/(P.q : Int) = -1 := by simpa using fm 0
    have fnm (K : Int) : (1-K*(P.q : Int))/(P.q : Int) = -K := by
      apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
      constructor <;> nlinarith
    have fnp (K : Int) : (-1-K*(P.q : Int))/(P.q : Int) = -(K+1) := by
      apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
      constructor <;> nlinarith
    have dr (K : Int) : K*(P.q₁ : Int)/(P.q₁ : Int) = K :=
      Int.mul_ediv_cancel K hr'.ne'
    have ds (K : Int) : K*(P.q₂ : Int)/(P.q₂ : Int) = K :=
      Int.mul_ediv_cancel K hs'.ne'
    have cr (K : Int) : -((-(K*(P.q₁ : Int)))/(P.q₁ : Int)) = K := by
      rw [← neg_mul, dr]
      ring
    have cs (K : Int) : -((-(K*(P.q₂ : Int)))/(P.q₂ : Int)) = K := by
      rw [← neg_mul, ds]
      ring
    have fnp' (K : Int) : (-1 + -(K*(P.q : Int)))/(P.q : Int) = -(K+1) := by
      simpa only [sub_eq_add_neg] using fnp K
    fin_cases j <;> fin_cases k <;> dsimp [P5332T1ParentRows] <;>
      norm_num only [add_zero, sub_zero, mul_zero, zero_mul, neg_zero, Int.zero_ediv,
        true_and, and_false, ite_true, ite_false,
        hpr, hps, cm, cp, fm, fp,
        cq1, cqneg1, fq1, fqneg1, fnm, fnp, fnp', dr, ds, cr, cs,
        hr'.ne', hs'.ne', show Even 0 from ⟨0,rfl⟩, show ¬Even 1 by decide,
        show Even 2 from ⟨1,rfl⟩, show ¬Even 3 by decide,
        show Even 4 from ⟨2,rfl⟩] <;> nlinarith only [hpr, hps]
  · have htpos : 0 < t := by omega
    fin_cases j
    · change t < (P.q₁ : Int) at ht'
      have h := P5332T1SignedParentIntervals P.p₁ P.p P.q₁ P.q t 1
        hr' hrl' htpos ht' (Or.inl rfl) det1
      have h' := P5332T1SignedParentIntervals P.p₁ P.p P.q₁ P.q (P.q₁-t) 1
        hr' hrl' (by omega) (by omega) (Or.inl rfl) det1
      dsimp only at h h'
      try
      fin_cases k <;> dsimp [P5332T1ParentRows] <;>
        norm_num only [ht0, false_and, ite_false, h.1, h.2.1, h.2.2.1,
          h.2.2.2.1, h.2.2.2.2, h'.1, h'.2.1, h'.2.2.1,
          h'.2.2.2.1, h'.2.2.2.2] <;> ring
    · change t < (P.q₂ : Int) at ht'
      have h := P5332T1SignedParentIntervals P.p₂ P.p P.q₂ P.q t (-1)
        hs' hsl' htpos ht' (Or.inr rfl) det2
      have h' := P5332T1SignedParentIntervals P.p₂ P.p P.q₂ P.q (P.q₂-t) (-1)
        hs' hsl' (by omega) (by omega) (Or.inr rfl) det2
      dsimp only at h h'
      try simp only [← sub_eq_add_neg] at h h'
      fin_cases k <;> dsimp [P5332T1ParentRows] <;>
        norm_num only [ht0, false_and, ite_false, h.1, h.2.1, h.2.2.1,
          h.2.2.2.1, h.2.2.2.2, h'.1, h'.2.1, h'.2.2.1,
          h'.2.2.2.1, h'.2.2.2.2] <;> ring

end ApollonianSuperharmonic

end
