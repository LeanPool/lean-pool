/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.AffineExcess
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMetric
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.AxisCube
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# CubeMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exact cube second moment

ABK26, §4.3 rests four separate assertions on one unstated computation: the
**second moment of an axis-parallel cube**.  For the open box
`axisCube z L = ∏ᵢ (zᵢ, zᵢ + L)` with centre `x = axisCubeCenter z L = z + (L/2)·𝟙`,

```
⨍_□ 1 = 1,        ⨍_□ (xᵢ − xᵢ) = 0,        ⨍_□ (xᵢ − xᵢ)(x_j − x_j) = δ_{ij} · L²/12 ,
```

and hence, for the affine function `ℓ(x) = c + g·x`,

```
⨍_□ ℓ   = c + g·x ,
⨍_□ ℓ²  = (c + g·x)² + (L²/12)|g|²         (`volumeAverage_axisCube_affineEval_sq`).
```

On an exact cube both the *inverse* (Bernstein) inequality and the *direct*
(diameter) inequality for affine functions become sharp:

```
(L/(2√3))·|g| ≤ ‖c + g·x‖_{L²(□)} ,        ‖ℓ − (ℓ)_□‖_{L²(□)} = (L/(2√3))·|g| .
```

The route is Fubini on a product measure: `MeasureTheory.Measure.restrict_pi_pi` identifies
`volume.restrict (axisCube z L)` with `Measure.pi (fun i ↦ volume.restrict (zᵢ, zᵢ+L))`, and
`MeasureTheory.integral_fintype_prod_eq_prod` factorizes the integral of a coordinate-wise
product (`setIntegral_axisCube_prod`).  Every moment is then a one-dimensional
`intervalIntegral.integral_pow` computation: odd moments vanish because the interval is centred,
the diagonal second moment is `L³/12`, and off-diagonal moments vanish because one factor is an
odd moment.

## Why this is not "the triangle inequality"

This module supplies the true input; `SandwichNondegeneracy.lean` transports it
to the lemma's sandwiched windows.  This is a change of proof attribution, not a
statement change: the sandwich is already a hypothesis of `l.iteration.lemma`.

## References

* ABK26, `e.grad.stability`; `l.iteration.lemma`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeCenter cubeScaleFactor)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### Measure-theoretic basics for `axisCube` -/

/-- The centre of `axisCube z L` (lower corner `z`, side `L`). -/
def axisCubeCenter (z : Vec d) (L : ℝ) : Vec d := fun i => z i + L / 2

@[simp] theorem axisCubeCenter_apply (z : Vec d) (L : ℝ) (i : Fin d) :
    axisCubeCenter z L i = z i + L / 2 := rfl

theorem measurableSet_axisCube (z : Vec d) (L : ℝ) : MeasurableSet (axisCube z L) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem volume_axisCube_ne_top (z : Vec d) (L : ℝ) : volume (axisCube z L) ≠ ⊤ := by
  have h : volume (axisCube z L) = ∏ i, ENNReal.ofReal ((z i + L) - z i) := by
    rw [axisCube, Real.volume_pi_Ioo]
  rw [h]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- `|□(z,L)| = L^d`. -/
theorem volume_axisCube_toReal (z : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (volume (axisCube z L)).toReal = L ^ d := by
  have hle : z ≤ fun i => z i + L := fun i => by
    simp only [le_add_iff_nonneg_right]
    exact hL
  have h : (volume (axisCube z L)).toReal = ∏ _i : Fin d, L := by
    rw [axisCube, Real.volume_pi_Ioo_toReal hle]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem volume_axisCube_toReal_pos (z : Vec d) {L : ℝ} (hL : 0 < L) :
    0 < (volume (axisCube z L)).toReal := by
  rw [volume_axisCube_toReal z hL.le]
  exact pow_pos hL d

/-- A cube sits inside the corresponding closed box, which is compact; hence continuous functions
are integrable on it. -/
theorem integrableOn_axisCube_of_continuous {f : Vec d → ℝ} (hf : Continuous f)
    (z : Vec d) (L : ℝ) : IntegrableOn f (axisCube z L) := by
  have hcpt : IsCompact (Set.pi Set.univ fun i : Fin d => Set.Icc (z i) (z i + L)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : axisCube z L ⊆ Set.pi Set.univ fun i : Fin d => Set.Icc (z i) (z i + L) := by
    intro x hx i _
    exact Set.Ioo_subset_Icc_self (hx i (Set.mem_univ i))
  exact (ContinuousOn.integrableOn_compact hcpt hf.continuousOn).mono_set hsub

/-- The affine map `x ↦ c + g·x` is continuous. -/
theorem continuous_affineEval (c : ℝ) (g : Vec d) : Continuous (affineEval c g) := by
  have hfun : affineEval c g = fun x : Vec d => c + ∑ i, g i * x i := by
    funext x
    rw [affineEval, vecDot]
  rw [hfun]
  exact continuous_const.add
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))

/-- **The normalizer, applied once.**  If `|U| = V ≠ 0` and `∫_U f = V · A`, then `⨍_U f = A`.
Every average in this module is computed through this lemma, so that no step depends on a
`field_simp` reading positivity facts out of the local context. -/
theorem volumeAverage_eq_of_setIntegral {U : Set (Vec d)} {V A : ℝ} (hV : V ≠ 0)
    (hvol : (volume U).toReal = V) {f : Vec d → ℝ} (hint : (∫ x in U, f x) = V * A) :
    volumeAverage U f = A := by
  unfold volumeAverage
  rw [hvol, hint, ← mul_assoc, inv_mul_cancel₀ hV, one_mul]

/-! ### Fubini: the integral of a coordinate-wise product over a cube -/

/-- **The product formula on a cube.**  `∫_□ ∏ᵢ hᵢ(xᵢ) = ∏ᵢ ∫_{(zᵢ,zᵢ+L)} hᵢ`.

This is `MeasureTheory.integral_fintype_prod_eq_prod` transported along
`MeasureTheory.Measure.restrict_pi_pi`, which identifies `volume.restrict (axisCube z L)` with the
product of the one-dimensional restricted measures.  No integrability hypotheses are needed (they
are absent from the mathlib statement as well). -/
theorem setIntegral_axisCube_prod (z : Vec d) (L : ℝ) (h : Fin d → ℝ → ℝ) :
    (∫ x in axisCube z L, ∏ i, h i (x i))
      = ∏ i, ∫ t in Set.Ioo (z i) (z i + L), h i t := by
  rw [axisCube, MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun i => h i)

/-! ### The one-dimensional moments -/

/-- `∫_{(a,a+L)} (t − (a + L/2))^n dt` in closed form. -/
theorem integral_Ioo_sub_center_pow (a : ℝ) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    (∫ t in Set.Ioo a (a + L), (t - (a + L / 2)) ^ n)
      = ((L / 2) ^ (n + 1) - (-(L / 2)) ^ (n + 1)) / (n + 1) := by
  have hle : a ≤ a + L := by linarith only [hL]
  have h1 : (∫ t in Set.Ioo a (a + L), (t - (a + L / 2)) ^ n)
      = ∫ t in a..(a + L), (t - (a + L / 2)) ^ n := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have e1 : a - (a + L / 2) = -(L / 2) := by ring
  have e2 : a + L - (a + L / 2) = L / 2 := by ring
  rw [h1, intervalIntegral.integral_comp_sub_right (fun t => t ^ n) (a + L / 2), e1, e2,
    _root_.integral_pow]

/-- The centred first moment of an interval vanishes. -/
theorem integral_Ioo_sub_center (a : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ t in Set.Ioo a (a + L), (t - (a + L / 2))) = 0 := by
  have h := integral_Ioo_sub_center_pow a hL 1
  simp only [pow_one] at h
  rw [h]
  norm_num

/-- The centred second moment of an interval is `L³/12`. -/
theorem integral_Ioo_sub_center_sq (a : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ t in Set.Ioo a (a + L), (t - (a + L / 2)) ^ 2) = L ^ 3 / 12 := by
  rw [integral_Ioo_sub_center_pow a hL 2]
  push_cast
  ring

/-- The length of an interval. -/
theorem integral_Ioo_one (a : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ _t in Set.Ioo a (a + L), (1 : ℝ)) = L := by
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith only [hL] : (0 : ℝ) ≤ a + L - a)]
  rw [smul_eq_mul, mul_one]
  ring

/-- `∏ k, (if k = i then A·B else B) = A·B^d` --- the shape every cube moment takes after Fubini:
one distinguished coordinate, all the others contributing the side length. -/
private theorem prod_ite_single (i : Fin d) (A B : ℝ) :
    (∏ k : Fin d, if k = i then A * B else B) = A * B ^ d := by
  have h : ∀ k : Fin d, (if k = i then A * B else B) = (if k = i then A else 1) * B := by
    intro k
    split_ifs with hk
    · rfl
    · rw [one_mul]
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i (fun _ => A), ite_eq_left (Finset.mem_univ i),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The cube moments -/

/-- **First moment: the centre is the barycentre.**  `∫_□ (xᵢ − xᵢ) dx = 0`. -/
theorem setIntegral_axisCube_centered (z : Vec d) {L : ℝ} (hL : 0 < L) (i : Fin d) :
    (∫ x in axisCube z L, (x i - axisCubeCenter z L i)) = 0 := by
  have hpt : (fun x : Vec d => x i - axisCubeCenter z L i)
      = fun x : Vec d => ∏ k, (if k = i then x k - (z k + L / 2) else 1) := by
    funext x
    rw [Finset.prod_ite_eq' Finset.univ i (fun k => x k - (z k + L / 2)),
      ite_eq_left (Finset.mem_univ i), axisCubeCenter_apply]
  have hbody : (fun t : ℝ => if i = i then t - (z i + L / 2) else (1 : ℝ))
      = fun t : ℝ => t - (z i + L / 2) := by
    funext t
    rw [ite_eq_left rfl]
  rw [hpt, setIntegral_axisCube_prod z L (fun k t => if k = i then t - (z k + L / 2) else 1)]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  show (∫ t in Set.Ioo (z i) (z i + L), if i = i then t - (z i + L / 2) else (1 : ℝ)) = 0
  rw [hbody]
  exact integral_Ioo_sub_center (z i) hL.le

theorem setIntegral_axisCube_centered_mul (z : Vec d) {L : ℝ} (hL : 0 < L) (i j : Fin d) :
    (∫ x in axisCube z L, (x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j))
      = if i = j then L ^ d * (L ^ 2 / 12) else 0 := by
  have hpt : (fun x : Vec d => (x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j))
      = fun x : Vec d =>
        ∏ k, ((if k = i then x k - (z k + L / 2) else 1)
          * (if k = j then x k - (z k + L / 2) else 1)) := by
    funext x
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ i (fun k => x k - (z k + L / 2)),
      Finset.prod_ite_eq' Finset.univ j (fun k => x k - (z k + L / 2)),
      ite_eq_left (Finset.mem_univ i), ite_eq_left (Finset.mem_univ j), axisCubeCenter_apply,
      axisCubeCenter_apply]
  rw [hpt, setIntegral_axisCube_prod z L
    (fun k t => (if k = i then t - (z k + L / 2) else 1)
      * (if k = j then t - (z k + L / 2) else 1))]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    have hfac : ∀ k : Fin d,
        (∫ t in Set.Ioo (z k) (z k + L),
            (if k = i then t - (z k + L / 2) else 1) * (if k = i then t - (z k + L / 2) else 1))
          = if k = i then L ^ 2 / 12 * L else L := by
      intro k
      by_cases hk : k = i
      · have hbody : ∀ t : ℝ,
            (if k = i then t - (z k + L / 2) else 1) * (if k = i then t - (z k + L / 2) else 1)
              = (t - (z k + L / 2)) ^ 2 := by
          intro t
          rw [ite_eq_left hk]
          ring
        simp only [hbody]
        rw [ite_eq_left hk, integral_Ioo_sub_center_sq (z k) hL.le]
        ring
      · have hbody : ∀ t : ℝ,
            (if k = i then t - (z k + L / 2) else 1) * (if k = i then t - (z k + L / 2) else 1)
              = (1 : ℝ) := by
          intro t
          rw [ite_eq_right hk]
          ring
        simp only [hbody]
        rw [ite_eq_right hk, integral_Ioo_one (z k) hL.le]
    rw [Finset.prod_congr rfl (fun k _ => hfac k), prod_ite_single i (L ^ 2 / 12) L]
    ring
  · rw [ite_eq_right hij]
    have hbody : (fun t : ℝ =>
        (if i = i then t - (z i + L / 2) else 1) * (if i = j then t - (z i + L / 2) else (1 : ℝ)))
          = fun t : ℝ => t - (z i + L / 2) := by
      funext t
      rw [ite_eq_left rfl, ite_eq_right hij, mul_one]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    show (∫ t in Set.Ioo (z i) (z i + L),
        (if i = i then t - (z i + L / 2) else 1)
          * (if i = j then t - (z i + L / 2) else (1 : ℝ))) = 0
    rw [hbody]
    exact integral_Ioo_sub_center (z i) hL.le

/-! ### Affine functions on an exact cube: the two sharp identities -/

/-- Recentring an affine function at an arbitrary point. -/
theorem affineEval_eq_center_add (c : ℝ) (g y x : Vec d) :
    affineEval c g x = affineEval c g y + ∑ i, g i * (x i - y i) := by
  have h : ∀ i : Fin d, g i * y i + g i * (x i - y i) = g i * x i := fun i => by ring
  rw [affineEval, affineEval, vecDot, vecDot]
  calc c + ∑ i, g i * x i
      = c + ∑ i, (g i * y i + g i * (x i - y i)) := by
        rw [Finset.sum_congr rfl fun i _ => h i]
    _ = c + ∑ i, g i * y i + ∑ i, g i * (x i - y i) := by
        rw [Finset.sum_add_distrib]
        ring

private theorem integrableOn_axisCube_coordSum (z : Vec d) (L : ℝ) (a : Fin d → ℝ) :
    IntegrableOn (fun x : Vec d => ∑ i, a i * (x i - axisCubeCenter z L i)) (axisCube z L) :=
  integrableOn_axisCube_of_continuous
    (continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).sub continuous_const)) z L

private theorem integrableOn_axisCube_coordQuad (z : Vec d) (L : ℝ) (g : Vec d) :
    IntegrableOn (fun x : Vec d => ∑ i, ∑ j, (g i * g j)
        * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j))) (axisCube z L) :=
  integrableOn_axisCube_of_continuous
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (((continuous_apply i).sub continuous_const).mul
        ((continuous_apply j).sub continuous_const))) z L

/-- The linear part of an affine function integrates to zero over a cube. -/
theorem setIntegral_axisCube_coordSum (z : Vec d) {L : ℝ} (hL : 0 < L) (a : Fin d → ℝ) :
    (∫ x in axisCube z L, ∑ i, a i * (x i - axisCubeCenter z L i)) = 0 := by
  have hint : ∀ i : Fin d, IntegrableOn (fun x : Vec d => a i * (x i - axisCubeCenter z L i))
      (axisCube z L) := fun i =>
    integrableOn_axisCube_of_continuous
      (continuous_const.mul ((continuous_apply i).sub continuous_const)) z L
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hint i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MeasureTheory.integral_const_mul, setIntegral_axisCube_centered z hL i, mul_zero]

/-- The quadratic part: the cube second moment, summed against `g ⊗ g`. -/
theorem setIntegral_axisCube_coordQuad (z : Vec d) {L : ℝ} (hL : 0 < L) (g : Vec d) :
    (∫ x in axisCube z L, ∑ i, ∑ j, (g i * g j)
        * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j)))
      = L ^ d * (L ^ 2 / 12) * vecNormSq g := by
  have hint : ∀ i j : Fin d, IntegrableOn (fun x : Vec d => (g i * g j)
      * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j))) (axisCube z L) :=
    fun i j => integrableOn_axisCube_of_continuous
      (continuous_const.mul (((continuous_apply i).sub continuous_const).mul
        ((continuous_apply j).sub continuous_const))) z L
  have hinner : ∀ i : Fin d, IntegrableOn (fun x : Vec d => ∑ j, (g i * g j)
      * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j))) (axisCube z L) :=
    fun i => integrableOn_axisCube_of_continuous
      (continuous_finsetSum _ fun j _ => continuous_const.mul
        (((continuous_apply i).sub continuous_const).mul
          ((continuous_apply j).sub continuous_const))) z L
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hinner i)]
  have hstep : ∀ i : Fin d, (∫ x in axisCube z L, ∑ j, (g i * g j)
      * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j)))
      = g i * g i * (L ^ d * (L ^ 2 / 12)) := by
    intro i
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)]
    have hj : ∀ j : Fin d, (∫ x in axisCube z L, (g i * g j)
        * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j)))
        = if j = i then g i * g i * (L ^ d * (L ^ 2 / 12)) else 0 := by
      intro j
      rw [MeasureTheory.integral_const_mul, setIntegral_axisCube_centered_mul z hL i j]
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hji, ite_eq_right (fun h : i = j => hji h.symm), mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hj j),
      Finset.sum_ite_eq' Finset.univ i (fun _ => g i * g i * (L ^ d * (L ^ 2 / 12))),
      ite_eq_left (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.sum_mul, vecNormSq, vecDot]
  ring

/-- **The mean of an affine function over a cube is its value at the centre.** -/
theorem volumeAverage_axisCube_affineEval (z : Vec d) {L : ℝ} (hL : 0 < L) (c : ℝ) (g : Vec d) :
    volumeAverage (axisCube z L) (affineEval c g) = affineEval c g (axisCubeCenter z L) := by
  refine volumeAverage_eq_of_setIntegral (V := L ^ d) (ne_of_gt (pow_pos hL d))
    (volume_axisCube_toReal z hL.le) ?_
  have hcongr : (∫ x in axisCube z L, affineEval c g x)
      = ∫ x in axisCube z L, (affineEval c g (axisCubeCenter z L)
          + ∑ i, g i * (x i - axisCubeCenter z L i)) :=
    MeasureTheory.setIntegral_congr_fun (measurableSet_axisCube z L)
      (fun x _ => affineEval_eq_center_add c g (axisCubeCenter z L) x)
  rw [hcongr, MeasureTheory.integral_add
      (integrableOn_axisCube_of_continuous continuous_const z L)
      (integrableOn_axisCube_coordSum z L g),
    setIntegral_axisCube_coordSum z hL g, MeasureTheory.setIntegral_const,
    MeasureTheory.measureReal_def, volume_axisCube_toReal z hL.le, smul_eq_mul, add_zero]

/-- This is the single missing ingredient the whole §4.3 window geometry rests on: the inverse
(Bernstein) inequality, the direct (diameter) inequality, attainment of the affine minimum on the
consumption class, and both endpoint comparisons are corollaries. -/
theorem volumeAverage_axisCube_affineEval_sq (z : Vec d) {L : ℝ} (hL : 0 < L) (c : ℝ) (g : Vec d) :
    volumeAverage (axisCube z L) (fun x => affineEval c g x ^ 2)
      = affineEval c g (axisCubeCenter z L) ^ 2 + L ^ 2 / 12 * vecNormSq g := by
  refine volumeAverage_eq_of_setIntegral (V := L ^ d) (ne_of_gt (pow_pos hL d))
    (volume_axisCube_toReal z hL.le) ?_
  have hpt : ∀ x : Vec d, affineEval c g x ^ 2
      = affineEval c g (axisCubeCenter z L) ^ 2
          + (∑ i, (2 * affineEval c g (axisCubeCenter z L) * g i)
              * (x i - axisCubeCenter z L i))
        + ∑ i, ∑ j, (g i * g j)
            * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j)) := by
    intro x
    have hs := affineEval_eq_center_add c g (axisCubeCenter z L) x
    have hsq : (∑ i, g i * (x i - axisCubeCenter z L i)) ^ 2
        = ∑ i, ∑ j, (g i * g j)
            * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j)) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hlin : (∑ i, (2 * affineEval c g (axisCubeCenter z L) * g i)
          * (x i - axisCubeCenter z L i))
        = 2 * affineEval c g (axisCubeCenter z L)
            * ∑ i, g i * (x i - axisCubeCenter z L i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs, hlin, ← hsq]
    ring
  have hcongr : (∫ x in axisCube z L, affineEval c g x ^ 2)
      = ∫ x in axisCube z L, (affineEval c g (axisCubeCenter z L) ^ 2
          + (∑ i, (2 * affineEval c g (axisCubeCenter z L) * g i)
              * (x i - axisCubeCenter z L i))
        + ∑ i, ∑ j, (g i * g j)
            * ((x i - axisCubeCenter z L i) * (x j - axisCubeCenter z L j))) :=
    MeasureTheory.setIntegral_congr_fun (measurableSet_axisCube z L) (fun x _ => hpt x)
  have hint12 : IntegrableOn (fun x : Vec d => affineEval c g (axisCubeCenter z L) ^ 2
      + ∑ i, (2 * affineEval c g (axisCubeCenter z L) * g i) * (x i - axisCubeCenter z L i))
      (axisCube z L) :=
    integrableOn_axisCube_of_continuous
      (continuous_const.add (continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).sub continuous_const))) z L
  rw [hcongr, MeasureTheory.integral_add hint12 (integrableOn_axisCube_coordQuad z L g),
    MeasureTheory.integral_add (integrableOn_axisCube_of_continuous continuous_const z L)
      (integrableOn_axisCube_coordSum z L _),
    setIntegral_axisCube_coordSum z hL _, setIntegral_axisCube_coordQuad z hL g,
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    volume_axisCube_toReal z hL.le, smul_eq_mul, add_zero]
  ring

/-! ### The two sharp `L²` statements on an exact cube -/

private theorem sqrt_sq_div_twelve {L : ℝ} (hL : 0 ≤ L) :
    Real.sqrt (L ^ 2 / 12) = L / (2 * Real.sqrt 3) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hkey : (L / (2 * Real.sqrt 3)) ^ 2 = L ^ 2 / 12 := by
    rw [div_pow, mul_pow, h3]
    norm_num
  rw [← hkey, Real.sqrt_sq (by positivity)]

/-- `‖c + g·x‖_{L²(□)} = ((c + g·x)² + (L²/12)|g|²)^{1/2}`. -/
theorem normalizedL2On_axisCube_affineEval (z : Vec d) {L : ℝ} (hL : 0 < L) (c : ℝ) (g : Vec d) :
    normalizedL2On (axisCube z L) (affineEval c g)
      = Real.sqrt (affineEval c g (axisCubeCenter z L) ^ 2 + L ^ 2 / 12 * vecNormSq g) := by
  rw [normalizedL2On, volumeAverage_axisCube_affineEval_sq z hL c g]

/-- **The inverse (Bernstein) inequality on an exact cube, with the sharp
constant.** `(L/(2√3))·|g| ≤ ‖c + g·x‖_{L²(□)}`. -/
theorem normalizedL2On_axisCube_affineEval_ge (z : Vec d) {L : ℝ} (hL : 0 < L) (c : ℝ)
    (g : Vec d) :
    L / (2 * Real.sqrt 3) * slopeMagnitude g
      ≤ normalizedL2On (axisCube z L) (affineEval c g) := by
  have hg : 0 ≤ vecNormSq g := HCPolySupport.vecNormSq_nonneg g
  rw [normalizedL2On_axisCube_affineEval z hL c g]
  have hstep : Real.sqrt (L ^ 2 / 12 * vecNormSq g)
      ≤ Real.sqrt (affineEval c g (axisCubeCenter z L) ^ 2 + L ^ 2 / 12 * vecNormSq g) := by
    refine Real.sqrt_le_sqrt ?_
    linarith only [sq_nonneg (affineEval c g (axisCubeCenter z L))]
  refine le_trans (le_of_eq ?_) hstep
  rw [Real.sqrt_mul (by positivity), sqrt_sq_div_twelve hL.le, slopeMagnitude]

/-- `|c + g·x| ≤ ‖c + g·x‖_{L²(□)}` --- the intercept half of the two-sided cube bound. -/
theorem abs_le_normalizedL2On_axisCube_affineEval (z : Vec d) {L : ℝ} (hL : 0 < L) (c : ℝ)
    (g : Vec d) :
    |affineEval c g (axisCubeCenter z L)| ≤ normalizedL2On (axisCube z L) (affineEval c g) := by
  have hg : 0 ≤ L ^ 2 / 12 * vecNormSq g :=
    mul_nonneg (by positivity) (HCPolySupport.vecNormSq_nonneg g)
  rw [normalizedL2On_axisCube_affineEval z hL c g, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  linarith only [hg]

/-- **The direct (diameter) identity on an exact cube.** `‖ℓ − (ℓ)_□‖_{L²(□)} =
(L/(2√3))·|∇ℓ|` --- an *equality*, so the diameter constant's lower comparison
is sharp on cubes. -/
theorem normalizedL2On_axisCube_affineEval_sub_average (z : Vec d) {L : ℝ} (hL : 0 < L)
    (c : ℝ) (g : Vec d) :
    normalizedL2On (axisCube z L)
        (fun x => affineEval c g x - volumeAverage (axisCube z L) (affineEval c g))
      = L / (2 * Real.sqrt 3) * slopeMagnitude g := by
  rw [volumeAverage_axisCube_affineEval z hL c g]
  have hfun : (fun x : Vec d => affineEval c g x - affineEval c g (axisCubeCenter z L))
      = affineEval (c - affineEval c g (axisCubeCenter z L)) g := by
    funext x
    rw [affineEval, affineEval, affineEval]
    ring
  have hzero :
      affineEval (c - affineEval c g (axisCubeCenter z L)) g (axisCubeCenter z L) = 0 := by
    rw [affineEval, affineEval]
    ring
  rw [hfun, normalizedL2On_axisCube_affineEval z hL, hzero,
    show (0 : ℝ) ^ 2 + L ^ 2 / 12 * vecNormSq g = L ^ 2 / 12 * vecNormSq g by ring,
    Real.sqrt_mul (by positivity), sqrt_sq_div_twelve hL.le, slopeMagnitude]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
