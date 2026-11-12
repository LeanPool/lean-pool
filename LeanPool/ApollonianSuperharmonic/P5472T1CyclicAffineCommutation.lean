/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorAction

-- [TABLET NODE: P5472T1CyclicAffineCommutation]

/-!
# P5472T1CyclicAffineCommutation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5472T1CyclicAffineCommutation
    (s : BandPackingSymmetry)
    (hword : ∃ z : GaussianInt, s = .shift z ∨ s = (BandPackingSymmetry.shift z).comp .negate)
    (W A : GaussianInt) :
    let I : GaussianInt := ⟨0, 1⟩
    let B := BandPackingSymmetryAffineVectorAction s (W, A)
    BandPackingSymmetryAffineVectorAction s (W - I * W, A + I * A) =
      (B.1 - I * B.1, B.2 + I * B.2) := by
-- BODY
  let Icyc : GaussianInt := ⟨0, 1⟩
  have hI_mul (z : GaussianInt) : Icyc * z = GaussianQuarterTurn z := by
    ext <;> simp [Icyc, GaussianQuarterTurn]
  let Pcyc (z : GaussianInt × GaussianInt) : GaussianInt × GaussianInt :=
    (z.1 - Icyc * z.1, z.2 + Icyc * z.2)
  have shiftPcyc (z W A : GaussianInt) :
      BandPackingSymmetryAffineVectorAction (.shift z) (Pcyc (W, A)) =
        Pcyc (BandPackingSymmetryAffineVectorAction (.shift z) (W, A)) := by
    have hconj (X : GaussianInt) : GaussianReflection (X - Icyc * X) =
        GaussianReflection X + Icyc * GaussianReflection X := by
      rw [hI_mul]
      rcases X with ⟨u, v⟩
      rw [hI_mul]
      ext <;>
        simp only [GaussianReflection, GaussianQuarterTurn,
          Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
          ] <;> ring
    simp only [BandPackingSymmetryAffineVectorAction, Pcyc]
    rw [Prod.mk.injEq]
    constructor
    · rfl
    · rw [hconj]
      rw [mul_add, mul_add]
      have hmul (R : GaussianInt) : z * (Icyc * R) = Icyc * (z * R) := by
        rw [← mul_assoc, mul_comm z Icyc, mul_assoc]
      rw [hmul]
      ac_rfl
  have negatePcyc (W A : GaussianInt) :
      BandPackingSymmetryAffineVectorAction .negate (Pcyc (W, A)) =
        Pcyc (BandPackingSymmetryAffineVectorAction .negate (W, A)) := by
    change (GaussianQuarterTurn (W - Icyc * W),
        GaussianQuarterTurn (A + Icyc * A)) =
      (GaussianQuarterTurn W - Icyc * GaussianQuarterTurn W,
        GaussianQuarterTurn A + Icyc * GaussianQuarterTurn A)
    rw [Prod.mk.injEq]
    constructor
    · rw [hI_mul]
      rcases W with ⟨wr, wi⟩
      rw [hI_mul]
      ext <;>
        simp only [GaussianQuarterTurn,
          Zsqrtd.re_sub, Zsqrtd.im_sub]; ring
    · rw [hI_mul]
      rcases A with ⟨ar, ai⟩
      rw [hI_mul]
      ext <;>
        simp only [GaussianQuarterTurn, Zsqrtd.re_add, Zsqrtd.im_add,
          ]; ring
  change BandPackingSymmetryAffineVectorAction s (Pcyc (W, A)) =
    Pcyc (BandPackingSymmetryAffineVectorAction s (W, A))
  rcases hword with ⟨z, hs | hs⟩
  · rw [hs]
    exact shiftPcyc z W A
  · rw [hs]
    change BandPackingSymmetryAffineVectorAction (.shift z)
        (BandPackingSymmetryAffineVectorAction .negate (Pcyc (W, A))) =
      Pcyc (BandPackingSymmetryAffineVectorAction (.shift z)
        (BandPackingSymmetryAffineVectorAction .negate (W, A)))
    rw [negatePcyc]
    exact shiftPcyc z _ _

end ApollonianSuperharmonic

end
