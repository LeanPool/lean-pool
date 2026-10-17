/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerTransportGeom
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerTransportNorms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerTransportHarmonic
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerProducer

/-!
# OneStepCornerTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The odd-class pricing at every met orientation

The proved odd-class apparatus is stated at **upper** met faces: `(★)`
(`OneStepEvenBoundFinal.exists_oddClassDefect_le_affineExcessRaw`) at one met
upper face, `(★★)`
(`OneStepOddClassCornerFinal.exists_oddClassDefect_le_affineExcessRaw_corner`)
at a pair of met upper faces.  The covering the excess-decay consumption runs
over meets lower and mixed configurations too.  This module removes the
orientation restriction, by transport rather than by duplication.

## The transport

The domain cube `□_m` is origin-symmetric, so the coordinate negation
`σ_l = coordFaceReflection (0 : ℝ) l` is a linear isometric involution of the
ambient space carrying

```text
  (x + □_k) ∩ □_m  ↦  (σ_l x + □_k) ∩ □_m ,
```

exchanging the upper and lower `l`-faces and fixing every other face
(`OneStepCornerTransportGeom`).  Every quantity the odd-class apparatus reads is
invariant: `normalizedL2On`, `affineDistOn`, `affineExcessRaw`, `affineExcess`,
`IsAffineMinimizer`, `MemLp` (`OneStepCornerTransportNorms`), classical
harmonicity (`OneStepCornerTransportHarmonic`), the met-face oddness binders and
`IsOddAffineData` (§1--§2 here) and hence `oddClassDefect` (§3 here).

So a window meeting a lower `l`-face is carried by one negation to a window
meeting the upper `l`-face, and a corner in an arbitrary orientation is carried
by at most two negations to an upper-upper corner.  §4 and §5 run those
negations.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The met-face oddness binders under a coordinate negation -/

/-- A coordinate negation turns the reflection in the upper `l`-face into the
reflection in the lower `l`-face. -/
theorem coordFaceReflection_zero_comm_self (a : ℝ) (l : Fin d) (y : Vec d) :
    coordFaceReflection (0 : ℝ) l (coordFaceReflection a l y)
      = coordFaceReflection (-a) l (coordFaceReflection (0 : ℝ) l y) := by
  funext j
  by_cases hjl : j = l
  · simp only [HCPolySupport.coordFaceReflection_apply, ite_eq_left hjl]
    ring
  · simp only [HCPolySupport.coordFaceReflection_apply, ite_eq_right hjl]

/-- The negation fixes the origin. -/
theorem coordFaceReflection_zero_zero (l : Fin d) :
    coordFaceReflection (0 : ℝ) l (0 : Vec d) = 0 := by
  funext j
  simp only [HCPolySupport.coordFaceReflection_apply, Pi.zero_apply]
  by_cases hjl : j = l
  · rw [ite_eq_left hjl]
    ring
  · rw [ite_eq_right hjl]

/-- The negation of a difference. -/
theorem coordFaceReflection_zero_sub (l : Fin d) (u v : Vec d) :
    coordFaceReflection (0 : ℝ) l (u - v)
      = coordFaceReflection (0 : ℝ) l u - coordFaceReflection (0 : ℝ) l v := by
  funext j
  by_cases hjl : j = l
  · simp only [HCPolySupport.coordFaceReflection_apply, ite_eq_left hjl, Pi.sub_apply]
    ring
  · simp only [HCPolySupport.coordFaceReflection_apply, ite_eq_right hjl, Pi.sub_apply]

private theorem neg_half_zpow (m : ℤ) :
    -((1 / 2 : ℝ) * (3 : ℝ) ^ m) = -(1 / 2 : ℝ) * (3 : ℝ) ^ m := by ring

private theorem neg_neg_half_zpow (m : ℤ) :
    -(-(1 / 2 : ℝ) * (3 : ℝ) ^ m) = (1 / 2 : ℝ) * (3 : ℝ) ^ m := by ring

/-- **Upper-face oddness travels.**  If `V` is odd about every met face of the
window at `x`, then `V ∘ σ_l` is odd about every met **upper** face of the
window at `σ_l x`. -/
theorem faceOddUpper_comp_coordFaceReflection_zero {x : Vec d} {m k : ℤ} (l : Fin d)
    {V : Vec d → ℝ}
    (hupV : ∀ i : Fin d, MeetsUpperFace x m k i → ∀ z : Vec d,
      V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (hlowV : ∀ i : Fin d, MeetsLowerFace x m k i → ∀ z : Vec d,
      V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (i : Fin d) (hi : MeetsUpperFace (coordFaceReflection (0 : ℝ) l x) m k i)
    (z : Vec d) :
    V (coordFaceReflection (0 : ℝ) l
        (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z))
      = -V (coordFaceReflection (0 : ℝ) l z) := by
  by_cases hil : i = l
  · subst hil
    have hlow : MeetsLowerFace x m k i :=
      (meetsUpperFace_coordFaceReflection_zero_self i).mp hi
    rw [coordFaceReflection_zero_comm_self, neg_half_zpow]
    exact hlowV i hlow _
  · have hup : MeetsUpperFace x m k i :=
      (meetsUpperFace_coordFaceReflection_zero_ne hil).mp hi
    rw [coordFaceReflection_comm (Ne.symm hil)]
    exact hupV i hup _

/-- **Lower-face oddness travels**, the twin of
`faceOddUpper_comp_coordFaceReflection_zero`. -/
theorem faceOddLower_comp_coordFaceReflection_zero {x : Vec d} {m k : ℤ} (l : Fin d)
    {V : Vec d → ℝ}
    (hupV : ∀ i : Fin d, MeetsUpperFace x m k i → ∀ z : Vec d,
      V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (hlowV : ∀ i : Fin d, MeetsLowerFace x m k i → ∀ z : Vec d,
      V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (i : Fin d) (hi : MeetsLowerFace (coordFaceReflection (0 : ℝ) l x) m k i)
    (z : Vec d) :
    V (coordFaceReflection (0 : ℝ) l
        (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z))
      = -V (coordFaceReflection (0 : ℝ) l z) := by
  by_cases hil : i = l
  · subst hil
    have hup : MeetsUpperFace x m k i :=
      (meetsLowerFace_coordFaceReflection_zero_self i).mp hi
    rw [coordFaceReflection_zero_comm_self, neg_neg_half_zpow]
    exact hupV i hup _
  · have hlow : MeetsLowerFace x m k i :=
      (meetsLowerFace_coordFaceReflection_zero_ne hil).mp hi
    rw [coordFaceReflection_comm (Ne.symm hil)]
    exact hlowV i hlow _

/-! ## 2. The odd affine class under a coordinate negation -/

/-- The affine lift travels with the negation. -/
theorem affineLift_comp_coordFaceReflection_zero (x : Vec d) (c : ℝ) (A : Vec d)
    (l : Fin d) (y : Vec d) :
    affineLift (coordFaceReflection (0 : ℝ) l x) c (coordFaceReflection (0 : ℝ) l A) y
      = affineLift x c A (coordFaceReflection (0 : ℝ) l y) := by
  have hdot : vecDot A (coordFaceReflection (0 : ℝ) l
      (y - coordFaceReflection (0 : ℝ) l x))
      = vecDot (coordFaceReflection (0 : ℝ) l A)
        (y - coordFaceReflection (0 : ℝ) l x) :=
    vecDot_coordFaceReflection_zero l A _
  rw [affineLift, affineLift, ← hdot, coordFaceReflection_zero_sub,
    HCPolySupport.coordFaceReflection_involutive]

/-- **The odd affine class travels.**  A datum odd for the negated window is odd
for the original one. -/
theorem isOddAffineData_of_comp_coordFaceReflection_zero {x : Vec d} {m k : ℤ}
    (l : Fin d) {c : ℝ} {A : Vec d}
    (h : IsOddAffineData (coordFaceReflection (0 : ℝ) l x) m k c
      (coordFaceReflection (0 : ℝ) l A)) :
    IsOddAffineData x m k c A := by
  refine ⟨fun i hi y hy => ?_, fun i hi y hy => ?_⟩
  · have hkey := affineLift_comp_coordFaceReflection_zero x c A l
      (coordFaceReflection (0 : ℝ) l y)
    rw [HCPolySupport.coordFaceReflection_involutive] at hkey
    rw [← hkey]
    by_cases hil : i = l
    · subst hil
      refine h.2 i ((meetsLowerFace_coordFaceReflection_zero_self i).mpr hi) _ ?_
      rw [HCPolySupport.coordFaceReflection_apply, ite_eq_left rfl, hy]
      ring
    · refine h.1 i ((meetsUpperFace_coordFaceReflection_zero_ne hil).mpr hi) _ ?_
      rw [HCPolySupport.coordFaceReflection_apply, ite_eq_right hil]
      exact hy
  · have hkey := affineLift_comp_coordFaceReflection_zero x c A l
      (coordFaceReflection (0 : ℝ) l y)
    rw [HCPolySupport.coordFaceReflection_involutive] at hkey
    rw [← hkey]
    by_cases hil : i = l
    · subst hil
      refine h.1 i ((meetsUpperFace_coordFaceReflection_zero_self i).mpr hi) _ ?_
      rw [HCPolySupport.coordFaceReflection_apply, ite_eq_left rfl, hy]
      ring
    · refine h.2 i ((meetsLowerFace_coordFaceReflection_zero_ne hil).mpr hi) _ ?_
      rw [HCPolySupport.coordFaceReflection_apply, ite_eq_right hil]
      exact hy

/-! ## 3. The window quantities under a coordinate negation -/

theorem affineExcessRaw_truncatedWindow_comp_coordFaceReflection_zero (x : Vec d)
    (m k : ℤ) (l : Fin d) (V : Vec d → ℝ) :
    affineExcessRaw (truncatedWindow (coordFaceReflection (0 : ℝ) l x) m k)
        (fun y => V (coordFaceReflection (0 : ℝ) l y))
      = affineExcessRaw (truncatedWindow x m k) V := by
  rw [truncatedWindow_coordFaceReflection_zero]
  exact affineExcessRaw_comp_coordFaceReflection_zero l
    (measurableSet_truncatedWindow x m k) V

theorem vecDot_coordFaceReflection_zero_pair (l : Fin d) (A x : Vec d) :
    vecDot (coordFaceReflection (0 : ℝ) l A) (coordFaceReflection (0 : ℝ) l x)
      = vecDot A x := by
  have h := vecDot_coordFaceReflection_zero l A (coordFaceReflection (0 : ℝ) l x)
  rw [HCPolySupport.coordFaceReflection_involutive] at h
  exact h.symm

theorem isAffineMinimizer_truncatedWindow_comp_coordFaceReflection_zero {x : Vec d}
    {m k : ℤ} (l : Fin d) (V : Vec d → ℝ) (c : ℝ) (A : Vec d) :
    IsAffineMinimizer (truncatedWindow (coordFaceReflection (0 : ℝ) l x) m k)
        (fun y => V (coordFaceReflection (0 : ℝ) l y))
        (c - vecDot (coordFaceReflection (0 : ℝ) l A)
          (coordFaceReflection (0 : ℝ) l x))
        (coordFaceReflection (0 : ℝ) l A)
      ↔ IsAffineMinimizer (truncatedWindow x m k) V (c - vecDot A x) A := by
  rw [truncatedWindow_coordFaceReflection_zero, vecDot_coordFaceReflection_zero_pair]
  exact isAffineMinimizer_comp_coordFaceReflection_zero l
    (measurableSet_truncatedWindow x m k) V (c - vecDot A x) A

theorem oddClassDefect_comp_coordFaceReflection_zero (x : Vec d) (m n : ℤ)
    (l : Fin d) (V : Vec d → ℝ) (c : ℝ) (A : Vec d) :
    oddClassDefect (coordFaceReflection (0 : ℝ) l x) m n
        (fun y => V (coordFaceReflection (0 : ℝ) l y)) c
        (coordFaceReflection (0 : ℝ) l A)
      = oddClassDefect x m n V c A := by
  rw [oddClassDefect, oddClassDefect, vecDot_coordFaceReflection_zero_pair,
    truncatedWindow_coordFaceReflection_zero,
    affineDistOn_comp_coordFaceReflection_zero l
      (measurableSet_truncatedWindow x m (n - 2)) V (c - vecDot A x) A,
    affineExcessRaw_comp_coordFaceReflection_zero l
      (measurableSet_truncatedWindow x m (n - 2)) V]

/-! ## 4. The corner pricing at every orientation -/

/-- **One negation at the first distinguished coordinate.**  A corner pricing
valid whenever the coordinate `i` meets an **upper** face is upgraded to one
valid whenever `i` meets a face in either orientation.  The condition `P` on the
second distinguished coordinate is carried unchanged; the hypothesis `hP` is its
(automatic) invariance under a negation in a *different* coordinate. -/
private theorem corner_pricing_flip {C : ℝ} {P : Vec d → ℤ → ℤ → Fin d → Prop}
    (hP : ∀ (x : Vec d) (m k : ℤ) (l j : Fin d), j ≠ l →
      (P (coordFaceReflection (0 : ℝ) l x) m k j ↔ P x m k j))
    (hC : ∀ (m n : ℤ) (x : Vec d) (i j : Fin d) (V : Vec d → ℝ) (c : ℝ) (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m → i ≠ j →
      MeetsUpperFace x m (n - 2) i → P x m (n - 2) j →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      oddClassDefect x m n V 0 0
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V) :
    ∀ (m n : ℤ) (x : Vec d) (i j : Fin d) (V : Vec d → ℝ) (c : ℝ) (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m → i ≠ j →
      (MeetsUpperFace x m (n - 2) i ∨ MeetsLowerFace x m (n - 2) i) →
      P x m (n - 2) j →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      oddClassDefect x m n V 0 0
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  intro m n x i j V c A hx hmn hij hi hj hupV hlowV hharm hVR hmin
  rcases hi with hi | hi
  · exact hC m n x i j V c A hx hmn hij hi hj hupV hlowV hharm hVR hmin
  · have hxmem : coordFaceReflection (0 : ℝ) i x ∈ openCubeSet (originCube d m) :=
      (mem_openCubeSet_coordFaceReflection_zero_iff i x).mpr hx
    have hupi : MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m (n - 2) i :=
      (meetsUpperFace_coordFaceReflection_zero_self i).mpr hi
    have hjP : P (coordFaceReflection (0 : ℝ) i x) m (n - 2) j :=
      (hP x m (n - 2) i j (Ne.symm hij)).mpr hj
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
        (c - vecDot (coordFaceReflection (0 : ℝ) i A)
          (coordFaceReflection (0 : ℝ) i x))
        (coordFaceReflection (0 : ℝ) i A) :=
      (isAffineMinimizer_truncatedWindow_comp_coordFaceReflection_zero i V c A).mpr hmin
    have hmain := hC m n (coordFaceReflection (0 : ℝ) i x) i j
      (fun y => V (coordFaceReflection (0 : ℝ) i y)) c
      (coordFaceReflection (0 : ℝ) i A) hxmem hmn hij hupi hjP
      (fun l hl z => faceOddUpper_comp_coordFaceReflection_zero i hupV hlowV l hl z)
      (fun l hl z => faceOddLower_comp_coordFaceReflection_zero i hupV hlowV l hl z)
      hharm' hVR' hmin'
    have hdef := oddClassDefect_comp_coordFaceReflection_zero x m n i V 0 (0 : Vec d)
    rw [coordFaceReflection_zero_zero] at hdef
    rw [hdef, affineExcessRaw_truncatedWindow_comp_coordFaceReflection_zero] at hmain
    exact hmain

/-- **`(★★)` at every met orientation.**  The corner pricing with the upper-upper
restriction removed: the two distinguished met faces may be upper or lower in
any combination (the remaining met faces are arbitrary, as in the proved
statement). -/
theorem exists_oddClassDefect_le_affineExcessRaw_corner_any (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i j : Fin d) (V : Vec d → ℝ)
      (c : ℝ) (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m → i ≠ j →
      (MeetsUpperFace x m (n - 2) i ∨ MeetsLowerFace x m (n - 2) i) →
      (MeetsUpperFace x m (n - 2) j ∨ MeetsLowerFace x m (n - 2) j) →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      oddClassDefect x m n V 0 0
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  obtain ⟨C, hC0, hC⟩ := exists_oddClassDefect_le_affineExcessRaw_corner d
  refine ⟨C, hC0, ?_⟩
  have step1 := corner_pricing_flip (C := C)
    (P := fun x m k j => MeetsUpperFace x m k j)
    (fun _ _ _ l j hjl => meetsUpperFace_coordFaceReflection_zero_ne (i := l) (l := j) hjl)
    hC
  exact corner_pricing_flip (C := C)
    (P := fun x m k j => MeetsUpperFace x m k j ∨ MeetsLowerFace x m k j)
    (fun _ _ _ l j hjl =>
      or_congr (meetsUpperFace_coordFaceReflection_zero_ne (i := l) (l := j) hjl)
        (meetsLowerFace_coordFaceReflection_zero_ne (i := l) (l := j) hjl))
    (fun m n x i j V c A hx hmn hij hupi hj hupV hlowV hharm hVR hmin =>
      step1 m n x j i V c A hx hmn (Ne.symm hij) hj hupi hupV hlowV hharm hVR hmin)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
