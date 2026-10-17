/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Support.Sobolev.Fractional.EuclideanWspSmoothDualBesovBound
public import LeanPool.Superdiffusion.Support.Book.Ch03.ABK26.FluxComparisonCZ
public import LeanPool.Superdiffusion.Support.Book.Ch03.ABK26.LocalCoarseGraining

/-!
# HomCGDischargeBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The middle link: descendant smooth duals from descendant negative Besov data

## What this file is for

The printed finite-`p` coarse-graining display is a composition of three
`CoarseGraining` statements:

```text
  (1)  exists_centeredCubeFluxComparison_cz          -- the printed LHS pair
  (2)  the smooth-dual / negative-Besov comparison   -- the middle link
  (3)  exists_localCoarseGrainingLp                  -- the printed RHS
```

Link (1) speaks about the **smooth-dual** `ℓ^p` descendant average of the local
flux defect; link (3) bounds the **negative-Besov** `ℓ^p` descendant average of
the same defect fields.  The two averages are different objects, and (2) is the
only thing that joins them.  This file performs that join once, at the exact
carriers of (1) and (3):

* `localFluxDefect_smoothDualAverage_le` --
  `centeredCubeLocalFluxDefectSmoothDualLpAverage ≤ C(d) · 3^{s n} ·
  localFluxDefectNegativeBesovLpAverage`.

The `3^{s n}` is not a loss: it is exactly the normalization `3^{-s n}` that
`CoarseGraining`'s `localFluxDefectNegativeBesovLpAverage` carries in front and the
smooth-dual average does not.  Composed with the `3^{s(m-n)}` of link (1) it
produces the printed `3^{s m}`, i.e. the printed `3^{-ms}` on the left.

## The per-descendant identification

The two links name the same field by two different constructors:
`centeredCubeLocalFluxDefectL2Field` (link 1) and `localFluxDefectL2Field`
(link 3).  Both carry `x ↦ (𝐚(x) - σ₀ I)∇u(x)` and differ only in the `Prop`
certificate, so they are **definitionally equal** — recorded here as
`centeredCubeLocalFluxDefectL2Field_eq`.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26
open MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The two constructors of the local flux defect agree -/

/-- **The flux-defect fields of the two `CoarseGraining` links are the same field.**

`centeredCubeLocalFluxDefectL2Field` (the flux-comparison side) and
`localFluxDefectL2Field` (the coarse-graining side) have the same `toField`,
`x ↦ (𝐚(x) - σ₀ I)∇u(x)`, and differ only in their `MemLp` certificate. -/
theorem centeredCubeLocalFluxDefectL2Field_eq {m n : ℤ} (hnm : n < m)
    (hn : n ≤ (originCube d m).scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u : H1Function (openCubeSet (originCube d m))) (R : TriadicCube d)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    centeredCubeLocalFluxDefectL2Field m n hnm a sigma0 u R hR =
      localFluxDefectL2Field a
        (openCubeSet_subset_of_mem_descendantsAtScale hn hR) sigma0 u := rfl

/-! ## 2. The exponent of a finite `L^p` index is a positive real -/

/-- The real exponent attached to a `FiniteLpExponent` is positive. -/
theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne

/-! ## 3. The middle link -/

/-- **The descendant smooth-dual average is controlled by the descendant
negative-Besov average.**

This is the comparison
`cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm`
applied on every descendant, aggregated through the `ℓ^p` average, and
renormalized by the `3^{-s n}` that `CoarseGraining`'s negative-Besov average
carries. -/
theorem localFluxDefect_smoothDualAverage_le {m n : ℤ} (hnm : n < m)
    (hn : n ≤ (originCube d m).scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u : H1Function (openCubeSet (originCube d m)))
    (s : FractionalOrder) (p : FiniteLpExponent) :
    centeredCubeLocalFluxDefectSmoothDualLpAverage m n hnm a sigma0 u s p ≤
      cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
        localFluxDefectNegativeBesovLpAverage (originCube d m) n hn a sigma0 u s p := by
  classical
  set t : ℝ := p.exponent.toReal with ht_def
  have ht : 0 < t := finiteLpExponent_toReal_pos p
  set Cd : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualBesovConstant d with hCd_def
  set D := descendantsAtScale (originCube d m) n with hD_def
  set g : {x // x ∈ D} → ℝ≥0∞ := fun R =>
    cubeEuclideanNegativeBesovESeminorm R.1 s p
      (localFluxDefectL2Field a
        (openCubeSet_subset_of_mem_descendantsAtScale hn R.2) sigma0 u) with hg_def
  set f : {x // x ∈ D} → ℝ≥0∞ := fun R =>
    cubeEuclideanNegativeWspSmoothDualENorm R.1 s p
      (centeredCubeLocalFluxDefectL2Field m n hnm a sigma0 u R.1 R.2) with hf_def
  /- the pointwise comparison, at the identified fie -/
  have hpt : ∀ R : {x // x ∈ D}, f R ≤ Cd * g R := by
    intro R
    have h := cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm
      d R.1 s p (localFluxDefectL2Field a
        (openCubeSet_subset_of_mem_descendantsAtScale hn R.2) sigma0 u)
    rw [hf_def, hg_def, hCd_def]
    simpa only [centeredCubeLocalFluxDefectL2Field_eq hnm hn a sigma0 u R.1 R.2] using h
  /- the aggregated comparis -/
  have hsum : (∑ R ∈ D.attach, f R ^ t) ≤ Cd ^ t * ∑ R ∈ D.attach, g R ^ t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun R _ => ?_
    calc f R ^ t ≤ (Cd * g R) ^ t := ENNReal.rpow_le_rpow (hpt R) ht.le
      _ = Cd ^ t * g R ^ t := ENNReal.mul_rpow_of_nonneg _ _ ht.le
  /- the averaged comparis -/
  have havg : ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ≤
      Cd ^ t * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) := by
    calc ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t)
        ≤ (D.card : ℝ≥0∞)⁻¹ * (Cd ^ t * ∑ R ∈ D.attach, g R ^ t) := by
          gcongr
      _ = Cd ^ t * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) := by
          rw [← mul_assoc, ← mul_assoc, mul_comm ((D.card : ℝ≥0∞)⁻¹) (Cd ^ t)]
  /- take the outer ro -/
  have hroot : ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ^ t⁻¹ ≤
      Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ := by
    calc ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ^ t⁻¹
        ≤ (Cd ^ t * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t)) ^ t⁻¹ :=
          ENNReal.rpow_le_rpow havg (inv_nonneg.mpr ht.le)
      _ = (Cd ^ t) ^ t⁻¹ * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ :=
          ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr ht.le)
      _ = Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (ne_of_gt ht), ENNReal.rpow_one]
  /- restore the printed normalizati -/
  have hnorm : ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
      ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ))) = 1 := by
    have h3 : (0 : ℝ) ≤ Real.rpow 3 (s.1 * (n : ℝ)) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    have hadd : s.1 * (n : ℝ) + -s.1 * (n : ℝ) = 0 := by ring
    have hprod : Real.rpow 3 (s.1 * (n : ℝ)) * Real.rpow 3 (-s.1 * (n : ℝ)) = 1 := by
      change (3 : ℝ) ^ (s.1 * (n : ℝ)) * (3 : ℝ) ^ (-s.1 * (n : ℝ)) = 1
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hadd, Real.rpow_zero]
    rw [← ENNReal.ofReal_mul h3, hprod, ENNReal.ofReal_one]
  have hfinal : Cd * ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
        (ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ))) *
          ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹) =
      Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ := by
    calc Cd * ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
          (ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ))) *
            ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹)
        = (ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
              ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ)))) *
            (Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹) := by ring
      _ = 1 * (Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹) := by
          rw [hnorm]
      _ = Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ := one_mul _
  rw [centeredCubeLocalFluxDefectSmoothDualLpAverage,
    localFluxDefectNegativeBesovLpAverage, one_div]
  exact hroot.trans (le_of_eq hfinal.symm)

end

end Algsuperdiff.Section4.Provider.Homogenization
