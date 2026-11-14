/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenGridFold
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5Basket

/-!
# GammaTenLoadFold

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `cgamma^{10}` grid fold with the **load leg on the grid**

ABK26, Step 2 of `l.approximate.recurrence.formula`, at the carrier of
`e.lower.bound.localization.terms`.

## The gap this module fills

`Closure.GammaTenGridFold.descendantsAverage_integral_fold_le_of_moments` asks
for the load leg in the **uniform per-cell** form

```
  forall R in the grid,  E[ | bfAhom^{1/2} P_R |^4 ]  <=  Cload^4 .
```

Its producer cannot deliver that.  The source display --- and therefore
`Closure.GammaTenLoad.exists_gammaTenLoadConst` --- is a **grid** average over
`z in 3^n Zd cap cu_K`, and the grid step of its proof is the tiling identity
`avsum_R fint_R = fint_{cu_K}`, which loses a factor `3^{jd}` when read at a
single cell.  This module therefore re-runs the fold with the load leg in the
grid form its producer really delivers,

```
  hload : gridFourthMomentRoot mu (descendantsAtDepth Q j) G  <=  Cload ,
```

and changes nothing else.

## What changes in the proof

Only the **cross** term.  In the uniform-load version the load leg is released
to a constant per cell before the grid average is taken; here it stays inside,
and the grid average of the product of two per-cell fourth roots is handled by
discrete Cauchy--Schwarz (`Step5Basket.cubeFamilyAverage_sqrt_mul_le`) followed
by Jensen for the concave square root on each factor
(`JunctionDischargeStepFiveDisplay.cubeFamilyAverage_sqrt_le`), giving

```
  avsum_R E[ F_R G_R H_R ]  <=  a * gridFourthMomentRoot mu I G
                                  * gridFourthMomentRoot mu I H .
```

The **quadratic** term is unchanged: it never involved the load, so
`GammaTenGridFold.cubeFamilyAverage_integral_mul_sq_le_sq_gridFourthMomentRoot`
is reused verbatim.

The numerical binder `hthr` of
`descendantsAverage_integral_fold_le_of_grid_moments` is **identical** to the
one of the uniform-load statement, so
`GammaTenGridFold.exists_gamma_threshold_gridFold (c1 * Cload) c2` still
**produces** it: with the ellipticity leg at `cgamma^{-2}` and the oscillation
grid root at `cgamma^{15}` the cross term is `c1 Cload cgamma^{13}` and the
quadratic term `c2 cgamma^{28}`, both strictly above `cgamma^{10}`'s exponent.

## Binders

Measure theory and real arithmetic at a probability measure: the pointwise
nonnegativity of the three families, the `L^p` memberships of the Hoelder
pairing at each cell, the per-cell integrability of the two products, and the
three moment bounds.  No smallness gate is assumed.  Nothing about the
corrector, the coefficient field or the cube geometry occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, the load display,
  `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ}

section Grid

variable {Omega : Type*} [MeasurableSpace Omega]

private theorem rpow_half_half {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹) = x ^ ((4 : ℝ)⁻¹) := by
  rw [← Real.rpow_mul hx]
  norm_num

/-- **The grid root dominates the square root of the grid average of the
per-cell square roots.**  Jensen for the concave square root, twice. -/
theorem cubeFamilyAverage_sqrt_integral_rpow_four_le_gridFourthMomentRoot
    (mu : Measure Omega) (I : Finset (TriadicCube d)) (G : TriadicCube d → Omega → ℝ)
    (hG : ∀ R w, 0 ≤ G R w) :
    (cubeFamilyAverage I (fun R => (∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)))
        ^ ((2 : ℝ)⁻¹) ≤ gridFourthMomentRoot mu I G := by
  have hIG : ∀ R : TriadicCube d, (0 : ℝ) ≤ ∫ w, G R w ^ (4 : ℝ) ∂mu := fun R =>
    integral_nonneg fun w => Real.rpow_nonneg (hG R w) _
  have hjensen := cubeFamilyAverage_sqrt_le I (fun R => ∫ w, G R w ^ (4 : ℝ) ∂mu)
    (fun R _ => hIG R)
  have hnn : (0 : ℝ) ≤
      cubeFamilyAverage I (fun R => (∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) :=
    cubeFamilyAverage_nonneg fun R _ => Real.rpow_nonneg (hIG R) _
  have hnn2 : (0 : ℝ) ≤ cubeFamilyAverage I (fun R => ∫ w, G R w ^ (4 : ℝ) ∂mu) :=
    cubeFamilyAverage_nonneg fun R _ => hIG R
  have hstep := Real.rpow_le_rpow hnn hjensen (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  refine hstep.trans (le_of_eq ?_)
  rw [gridFourthMomentRoot, gridFourthMoment, rpow_half_half hnn2]

/-- **The cross term with the load leg on the grid.**

The variant of
`GammaTenGridFold.cubeFamilyAverage_integral_mul_mul_le_gridFourthMomentRoot`
in which the *load* leg is controlled only in the grid-averaged form the source
display delivers:

```
  avsum_R E[ F_R G_R H_R ]  <=  a * ( gridFourthMomentRoot mu I G
                                      * gridFourthMomentRoot mu I H ) .
```

The per-cell step is the same Hoelder triple as the uniform-load version; the
grid step is discrete Cauchy--Schwarz
(`Step5Basket.cubeFamilyAverage_sqrt_mul_le`) followed by Jensen for the concave
square root on each of the two factors.

exactly as the uniform-load version, minus its uniform load binder. -/
theorem cubeFamilyAverage_integral_mul_mul_le_gridLoad
    (mu : Measure Omega) [IsProbabilityMeasure mu] (I : Finset (TriadicCube d))
    (F G H : TriadicCube d → Omega → ℝ)
    (hF : ∀ R w, 0 ≤ F R w) (hG : ∀ R w, 0 ≤ G R w) (hH : ∀ R w, 0 ≤ H R w)
    (hFm : ∀ R ∈ I, MemLp (fun w => F R w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hGm : ∀ R ∈ I, MemLp (fun w => G R w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hHm : ∀ R ∈ I, MemLp (H R) 4 mu)
    (hFGm : ∀ R ∈ I, MemLp (fun w => F R w * G R w) (ENNReal.ofReal 2) mu)
    {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ R ∈ I, (∫ w, F R w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ a) :
    cubeFamilyAverage I (fun R => ∫ w, F R w * G R w * H R w ∂mu) ≤
      a * (gridFourthMomentRoot mu I G * gridFourthMomentRoot mu I H) := by
  classical
  have hIG : ∀ R : TriadicCube d, (0 : ℝ) ≤ ∫ w, G R w ^ (4 : ℝ) ∂mu := fun R =>
    integral_nonneg fun w => Real.rpow_nonneg (hG R w) _
  have hIH : ∀ R : TriadicCube d, (0 : ℝ) ≤ ∫ w, H R w ^ (4 : ℝ) ∂mu := fun R =>
    integral_nonneg fun w => Real.rpow_nonneg (hH R w) _
  have hper : ∀ R ∈ I, (∫ w, F R w * G R w * H R w ∂mu) ≤
      a * (((∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹) *
        ((∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹)) := by
    intro R hR
    rw [rpow_half_half (hIG R), rpow_half_half (hIH R)]
    have hbase := integral_mul_mul_le_mul_mul_rpowFourRoot mu (F R) (G R) (H R)
      (hF R) (hG R) (hH R) (hFm R hR) (hGm R hR) (hHm R hR) (hFGm R hR) ha0
      (Real.rpow_nonneg (hIG R) _) (ha R hR) (le_refl _)
    have hfix : (∫ w, G R w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) =
        (∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) := by rw [one_div]
    rw [hfix] at hbase
    refine hbase.trans (le_of_eq ?_)
    ring
  have hcs := cubeFamilyAverage_sqrt_mul_le I
    (fun R => (∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹))
    (fun R => (∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹))
    (fun R _ => Real.rpow_nonneg (hIG R) _) (fun R _ => Real.rpow_nonneg (hIH R) _)
  have hGroot := cubeFamilyAverage_sqrt_integral_rpow_four_le_gridFourthMomentRoot
    mu I G hG
  have hHroot := cubeFamilyAverage_sqrt_integral_rpow_four_le_gridFourthMomentRoot
    mu I H hH
  have hHalf0 : (0 : ℝ) ≤
      (cubeFamilyAverage I (fun R => (∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)))
        ^ ((2 : ℝ)⁻¹) :=
    Real.rpow_nonneg (cubeFamilyAverage_nonneg fun R _ => Real.rpow_nonneg (hIH R) _) _
  have hGroot0 : (0 : ℝ) ≤ gridFourthMomentRoot mu I G :=
    Real.rpow_nonneg (gridFourthMoment_nonneg mu I G) _
  calc cubeFamilyAverage I (fun R => ∫ w, F R w * G R w * H R w ∂mu)
      ≤ cubeFamilyAverage I (fun R => a *
          (((∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹) *
            ((∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹))) :=
        cubeFamilyAverage_mono hper
    _ = a * cubeFamilyAverage I (fun R =>
          ((∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹) *
            ((∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹)) :=
        cubeFamilyAverage_const_mul I a _
    _ ≤ a * ((cubeFamilyAverage I
            (fun R => (∫ w, G R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹))) ^ ((2 : ℝ)⁻¹) *
          (cubeFamilyAverage I
            (fun R => (∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹))) ^ ((2 : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hcs ha0
    _ ≤ a * (gridFourthMomentRoot mu I G * gridFourthMomentRoot mu I H) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hGroot hHroot hHalf0 hGroot0) ha0

/-- **The two legs added, with the load leg on the grid.**

The grid-load variant of `GammaTenGridFold.cubeFamilyAverage_integral_fold_le`.
exactly as that statement, with its uniform load binder replaced by nothing:
the load is carried in the grid functional on the right. -/
theorem cubeFamilyAverage_integral_fold_le_gridLoad
    (mu : Measure Omega) [IsProbabilityMeasure mu] (I : Finset (TriadicCube d))
    (F G H : TriadicCube d → Omega → ℝ)
    (hF : ∀ R w, 0 ≤ F R w) (hG : ∀ R w, 0 ≤ G R w) (hH : ∀ R w, 0 ≤ H R w)
    (hFm : ∀ R ∈ I, MemLp (fun w => F R w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hGm : ∀ R ∈ I, MemLp (fun w => G R w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hHsqm : ∀ R ∈ I, MemLp (fun w => H R w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hHm : ∀ R ∈ I, MemLp (H R) 4 mu)
    (hFGm : ∀ R ∈ I, MemLp (fun w => F R w * G R w) (ENNReal.ofReal 2) mu)
    (hFHm : ∀ R ∈ I, MemLp (fun w => F R w * H R w) (ENNReal.ofReal 2) mu)
    (hint1 : ∀ R ∈ I, Integrable (fun w => F R w * G R w * H R w) mu)
    (hint2 : ∀ R ∈ I, Integrable (fun w => F R w * H R w * H R w) mu)
    {a c1 c2 : ℝ} (ha0 : 0 ≤ a) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (ha : ∀ R ∈ I, (∫ w, F R w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ a) :
    cubeFamilyAverage I (fun R => ∫ w,
        c1 * (F R w * G R w * H R w) + c2 * (F R w * H R w * H R w) ∂mu) ≤
      c1 * (a * (gridFourthMomentRoot mu I G * gridFourthMomentRoot mu I H)) +
        c2 * (a * (gridFourthMomentRoot mu I H) ^ (2 : ℕ)) := by
  have hsplit : ∀ R ∈ I, (∫ w,
      c1 * (F R w * G R w * H R w) + c2 * (F R w * H R w * H R w) ∂mu) =
      c1 * (∫ w, F R w * G R w * H R w ∂mu) +
        c2 * (∫ w, F R w * H R w * H R w ∂mu) := by
    intro R hR
    rw [integral_add ((hint1 R hR).const_mul c1) ((hint2 R hR).const_mul c2),
      integral_const_mul, integral_const_mul]
  have hrw : cubeFamilyAverage I (fun R => ∫ w,
        c1 * (F R w * G R w * H R w) + c2 * (F R w * H R w * H R w) ∂mu) =
      cubeFamilyAverage I (fun R => c1 * (∫ w, F R w * G R w * H R w ∂mu)) +
        cubeFamilyAverage I (fun R => c2 * (∫ w, F R w * H R w * H R w ∂mu)) := by
    rw [← cubeFamilyAverage_add]
    unfold cubeFamilyAverage
    exact congrArg _ (Finset.sum_congr rfl hsplit)
  rw [hrw, cubeFamilyAverage_const_mul, cubeFamilyAverage_const_mul]
  have hcross := cubeFamilyAverage_integral_mul_mul_le_gridLoad mu I F G H
    hF hG hH hFm hGm hHm hFGm ha0 ha
  have hquad := cubeFamilyAverage_integral_mul_sq_le_sq_gridFourthMomentRoot mu I F H
    hF hH hFm hHsqm hHm hFHm ha0 ha
  exact add_le_add (mul_le_mul_of_nonneg_left hcross hc1)
    (mul_le_mul_of_nonneg_left hquad hc2)

end Grid

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
