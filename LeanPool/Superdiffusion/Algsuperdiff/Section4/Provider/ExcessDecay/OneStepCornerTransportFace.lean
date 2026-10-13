/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerTransport

/-!
# OneStepCornerTransportFace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The one-met-face regime at the lower face

`OneStepCornerTransport` removed the orientation restriction from the corner
pricing `(★★)`.  This module does the same for the one-met-face pricing `(★)`
and its producer, which the proved
`OneStepEvenBoundFinal` and the one-met-face producer state at a met **upper**
face only.

## What travels, and what the datum becomes

The negation `σ_i` carries a window meeting the lower `i`-face to one meeting the
upper `i`-face, so `(★)` transports verbatim except for the affine datum, which
is read at the *reflected* parameters: the normal slope
`oddAffineSlope i (σ_i A) = σ_i (oddAffineSlope i A)` and the normal intercept

```text
  oddAffineIntercept (σ_i x) m i (σ_i A) = A_i (x_i + ½·3^m) ,
```

the **lower** normal intercept `oddAffineInterceptLower`, whose ramp vanishes
on the lower face exactly as `oddAffineIntercept`'s vanishes on the upper one.
With that datum the odd-class membership `isOddAffineData_oddAffineDatumLower`
and the pricing `exists_oddClassDefect_le_affineExcessRaw_lower` are the mirror
images of the proved upper-face statements, and the producer
`exists_gradientHolder_boundary_faceOdd_lower` is the upper-face producer's
proof run at those data.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The lower normal datum -/

/-- The intercept of the normal part of `(c, A)` at a met **lower** `i`-face:
the ramp `A_i (y_i + ½·3^m)`, which vanishes on that face. -/
def oddAffineInterceptLower (x : Vec d) (m : ℤ) (i : Fin d) (A : Vec d) : ℝ :=
  A i * (x i + (1 / 2 : ℝ) * (3 : ℝ) ^ m)

theorem oddAffineIntercept_comp_coordFaceReflection_zero (x : Vec d) (m : ℤ)
    (i : Fin d) (A : Vec d) :
    oddAffineIntercept (coordFaceReflection (0 : ℝ) i x) m i
        (coordFaceReflection (0 : ℝ) i A)
      = oddAffineInterceptLower x m i A := by
  rw [oddAffineIntercept, oddAffineInterceptLower,
    HCPolySupport.coordFaceReflection_apply_self,
    HCPolySupport.coordFaceReflection_apply_self]
  ring

private theorem oddAffineSlope_apply_of_ne {i j : Fin d} (A : Vec d) (hji : j ≠ i) :
    oddAffineSlope i A j = 0 := by
  show (if j = i then A i else 0) = 0
  rw [ite_eq_right hji]

theorem oddAffineSlope_comp_coordFaceReflection_zero (i : Fin d) (A : Vec d) :
    oddAffineSlope i (coordFaceReflection (0 : ℝ) i A)
      = coordFaceReflection (0 : ℝ) i (oddAffineSlope i A) := by
  funext j
  by_cases hji : j = i
  · subst hji
    rw [oddAffineSlope_apply_self, HCPolySupport.coordFaceReflection_apply_self,
      HCPolySupport.coordFaceReflection_apply_self, oddAffineSlope_apply_self]
  · rw [oddAffineSlope_apply_of_ne _ hji,
      HCPolySupport.coordFaceReflection_apply_ne 0 i j _ hji,
      oddAffineSlope_apply_of_ne _ hji]

/-- **The lower normal datum lies in the odd affine class.**  The lower-face
twin of `OneStepDatumPriceOdd.isOddAffineData_oddAffineDatum`. -/
theorem isOddAffineData_oddAffineDatumLower {x : Vec d} {m k : ℤ} {i : Fin d}
    (hkm : k < m) (hlow : MeetsLowerFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (A : Vec d) :
    IsOddAffineData x m k (oddAffineInterceptLower x m i A) (oddAffineSlope i A) := by
  refine isOddAffineData_of_comp_coordFaceReflection_zero i ?_
  rw [← oddAffineIntercept_comp_coordFaceReflection_zero x m i A,
    ← oddAffineSlope_comp_coordFaceReflection_zero i A]
  refine isOddAffineData_oddAffineDatum hkm
    ((meetsUpperFace_coordFaceReflection_zero_self i).mpr hlow) (fun j hji => ?_) _
  exact ⟨fun h => (hother j hji).1
      ((meetsUpperFace_coordFaceReflection_zero_ne hji).mp h),
    fun h => (hother j hji).2
      ((meetsLowerFace_coordFaceReflection_zero_ne hji).mp h)⟩

/-! ## 2. The one-met-face pricing at the lower face -/

/-- **`(★)` at a met lower face.**  The odd-class defect at the lower normal
datum is priced by the excess. -/
theorem exists_oddClassDefect_le_affineExcessRaw_lower (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i : Fin d) (V : Vec d → ℝ) (c : ℝ)
      (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m →
      MeetsLowerFace x m (n - 2) i →
      (∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j) →
      (∀ z, V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      oddClassDefect x m n V (oddAffineInterceptLower x m i A) (oddAffineSlope i A)
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  obtain ⟨C, hC0, hC⟩ := exists_oddClassDefect_le_affineExcessRaw d
  refine ⟨C, hC0, ?_⟩
  intro m n x i V c A hx hmn hlow hother hVodd hharm hVR hmin
  have hnup : ¬ MeetsUpperFace x m (n - 2) i := fun h =>
    not_meetsLowerFace_of_meetsUpperFace hmn h hlow
  have hupV : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
      V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z := by
    intro l hl _
    by_cases hli : l = i
    · subst hli
      exact absurd hl hnup
    · exact absurd hl (hother l hli).1
  have hlowV : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
      V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z := by
    intro l hl z
    by_cases hli : l = i
    · subst hli
      exact hVodd z
    · exact absurd hl (hother l hli).2
  have hxmem : coordFaceReflection (0 : ℝ) i x ∈ openCubeSet (originCube d m) :=
    (mem_openCubeSet_coordFaceReflection_zero_iff i x).mpr hx
  have hupi : MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m (n - 2) i :=
    (meetsUpperFace_coordFaceReflection_zero_self i).mpr hlow
  have hother' : ∀ j, j ≠ i →
      ¬ MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m (n - 2) j ∧
      ¬ MeetsLowerFace (coordFaceReflection (0 : ℝ) i x) m (n - 2) j := by
    intro j hji
    exact ⟨fun h => (hother j hji).1
        ((meetsUpperFace_coordFaceReflection_zero_ne hji).mp h),
      fun h => (hother j hji).2
        ((meetsLowerFace_coordFaceReflection_zero_ne hji).mp h)⟩
  have hharm' : HarmonicOnNhd
      ((fun y => V (coordFaceReflection (0 : ℝ) i y)) ∘
        (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
        reflectedWindow (coordFaceReflection (0 : ℝ) i x) m (n - 2)) := by
    rw [reflectedWindow_coordFaceReflection_zero]
    exact harmonicOnNhd_comp_coordFaceReflection_zero i hharm
  have hVR' : MemLp (fun y => V (coordFaceReflection (0 : ℝ) i y)) 2
      (volume.restrict
        (reflectedWindow (coordFaceReflection (0 : ℝ) i x) m (n - 2))) := by
    rw [reflectedWindow_coordFaceReflection_zero]
    exact memLp_comp_coordFaceReflection i
      (isOpen_reflectedWindow x m (n - 2)).measurableSet hVR
  have hmin' : IsAffineMinimizer
      (truncatedWindow (coordFaceReflection (0 : ℝ) i x) m (n - 2))
      (fun y => V (coordFaceReflection (0 : ℝ) i y))
      (c - vecDot (coordFaceReflection (0 : ℝ) i A) (coordFaceReflection (0 : ℝ) i x))
      (coordFaceReflection (0 : ℝ) i A) :=
    (isAffineMinimizer_truncatedWindow_comp_coordFaceReflection_zero i V c A).mpr hmin
  have hmain := hC m n (coordFaceReflection (0 : ℝ) i x) i
    (fun y => V (coordFaceReflection (0 : ℝ) i y)) c (coordFaceReflection (0 : ℝ) i A)
    hxmem hmn hupi hother'
    (fun z => faceOddUpper_comp_coordFaceReflection_zero i hupV hlowV i hupi z)
    hharm' hVR' hmin'
  rw [oddAffineIntercept_comp_coordFaceReflection_zero,
    oddAffineSlope_comp_coordFaceReflection_zero,
    oddClassDefect_comp_coordFaceReflection_zero,
    affineExcessRaw_truncatedWindow_comp_coordFaceReflection_zero] at hmain
  exact hmain

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
