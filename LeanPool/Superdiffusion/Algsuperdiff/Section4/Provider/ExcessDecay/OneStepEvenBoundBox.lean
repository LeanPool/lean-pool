/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CubeMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionVolume

/-!
# OneStepEvenBoundBox

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Affine moments on an open coordinate box (the unequal-sided cube moment)

`CubeMoments.lean` computes the moments of an affine function on the *equal-sided* open cube
`axisCube z L = ∏ᵢ (zᵢ, zᵢ + L)`.  The boundary branch of the one-step even-part bound `(★)`
never sees an exact cube: it sees the **open coordinate box**
`coordBox lo hi = ∏ᵢ (loᵢ, hiᵢ)` with unequal sides, because a truncated window, a reflected
window, and a transverse halving all change the sides coordinate by coordinate.  This module is
the side-by-side box analogue of `CubeMoments`.

The sharp identity is, with `x = boxCenter lo hi` the centre `xᵢ = (loᵢ + hiᵢ)/2`,

```
⨍_B 1 = 1,   ⨍_B (xᵢ − xᵢ) = 0,   ⨍_B (xᵢ − xᵢ)(x_j − x_j) = δ_{ij} · (hiᵢ − loᵢ)²/12 ,
```

and hence, for the affine function `ℓ(x) = c + g·x`,

```
⨍_B ℓ² = ℓ(x)² + ∑ᵢ gᵢ² (hiᵢ − loᵢ)²/12          (`volumeAverage_coordBox_affineEval_sq`).
```

Unlike the cube case the second term is **not** proportional to `|g|²`: each coordinate carries
its own side length, and that anisotropy is exactly what the boundary branch exploits.  The two
comparison corollaries `(★)` consumes are read straight off the identity:

* `normalizedL2On_coordBox_affineEval_congr_of_slope_zero` --- sliding (or stretching) the box
  in a direction `i` where the slope vanishes, `gᵢ = 0`, changes nothing: neither the centre
  value (the `i`-th term of `g·x` is `0`) nor the `i`-th summand (`gᵢ² = 0`).
* `normalizedL2On_coordBox_affineEval_half_le` --- **reverse Chebyshev**: halving the transverse
  sides of a concentric box costs at most the factor two, because each transverse summand loses
  at most the factor `4` inside the square root while the centre value is unchanged.

The route is the same as in `CubeMoments`: Fubini via `MeasureTheory.Measure.restrict_pi_pi` and
`MeasureTheory.integral_fintype_prod_eq_prod` (`setIntegral_coordBox_prod`), then three
one-dimensional moments on `Set.Ioo a b`, obtained from `CubeMoments`' moments on
`Set.Ioo a (a + L)` at `L = b - a`.  Normalization goes once through
`CubeMoments.volumeAverage_eq_of_setIntegral`, so that no step reads positivity out of the local
context via `field_simp`.

Three ambient facts about the seminorm are proved alongside, because the
boundary branch moves the box before it measures: translation invariance
(`normalizedL2On_comp_sub_right`, through `measurePreserving_sub_right`),
pointwise domination (`normalizedL2On_mono_of_abs_le`), and the seminorm of a
constant (`normalizedL2On_const_of_toReal_pos`).

## References

* `Algsuperdiff/Section4/Provider/ExcessDecay/OddReflectionWindow.lean` (`coordBox`).
* `Algsuperdiff/Section4/Provider/ExcessDecay/OddReflectionVolume.lean` (`volume_coordBox`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec vecDot volumeAverage)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### The centre of a box, and measure-theoretic basics -/

/-- The centre of the open coordinate box `∏ᵢ (loᵢ, hiᵢ)`. -/
def boxCenter (lo hi : Fin d → ℝ) : Vec d := fun i => (lo i + hi i) / 2

@[simp] theorem boxCenter_apply (lo hi : Fin d → ℝ) (i : Fin d) :
    boxCenter lo hi i = (lo i + hi i) / 2 := rfl

theorem volume_coordBox_ne_top (lo hi : Fin d → ℝ) : volume (coordBox lo hi) ≠ ⊤ := by
  rw [volume_coordBox]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- `|B| = ∏ᵢ (hiᵢ − loᵢ)`. -/
theorem volume_coordBox_toReal {lo hi : Fin d → ℝ} (hle : ∀ i, lo i ≤ hi i) :
    (volume (coordBox lo hi)).toReal = ∏ i, (hi i - lo i) := by
  rw [coordBox, Real.volume_pi_Ioo_toReal hle]

/-- A box sits inside the corresponding closed box, which is compact; hence continuous functions
are integrable on it. -/
theorem integrableOn_coordBox_of_continuous {f : Vec d → ℝ} (hf : Continuous f)
    (lo hi : Fin d → ℝ) : IntegrableOn f (coordBox lo hi) volume := by
  have hcpt : IsCompact (Set.pi Set.univ fun i : Fin d => Set.Icc (lo i) (hi i)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : coordBox lo hi ⊆ Set.pi Set.univ fun i : Fin d => Set.Icc (lo i) (hi i) := by
    intro x hx i _
    exact Set.Ioo_subset_Icc_self (hx i (Set.mem_univ i))
  exact (ContinuousOn.integrableOn_compact hcpt hf.continuousOn).mono_set hsub

/-! ### Fubini: the integral of a coordinate-wise product over a box -/

/-- **The product formula on a box.**  `∫_B ∏ᵢ hᵢ(xᵢ) = ∏ᵢ ∫_{(loᵢ,hiᵢ)} hᵢ`. -/
theorem setIntegral_coordBox_prod (lo hi : Fin d → ℝ) (h : Fin d → ℝ → ℝ) :
    (∫ x in coordBox lo hi, ∏ i, h i (x i))
      = ∏ i, ∫ t in Set.Ioo (lo i) (hi i), h i t := by
  rw [coordBox, MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun i => h i)

/-! ### The one-dimensional moments on `Set.Ioo a b` -/

/-- The centred first moment of an interval vanishes. -/
private theorem integral_Ioo_mid {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Ioo a b, (t - (a + b) / 2)) = 0 := by
  have hL : (0 : ℝ) ≤ b - a := by linarith only [hab]
  have h := integral_Ioo_sub_center a hL
  rw [show a + (b - a) = b from by ring, show a + (b - a) / 2 = (a + b) / 2 from by ring] at h
  exact h

/-- The centred second moment of an interval is `(b − a)³/12`. -/
private theorem integral_Ioo_mid_sq {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Ioo a b, (t - (a + b) / 2) ^ 2) = (b - a) ^ 3 / 12 := by
  have hL : (0 : ℝ) ≤ b - a := by linarith only [hab]
  have h := integral_Ioo_sub_center_sq a hL
  rw [show a + (b - a) = b from by ring, show a + (b - a) / 2 = (a + b) / 2 from by ring] at h
  exact h

/-- The length of an interval. -/
private theorem integral_Ioo_length {a b : ℝ} (hab : a ≤ b) :
    (∫ _t in Set.Ioo a b, (1 : ℝ)) = b - a := by
  have hL : (0 : ℝ) ≤ b - a := by linarith only [hab]
  have h := integral_Ioo_one a hL
  rw [show a + (b - a) = b from by ring] at h
  exact h

/-- `∏ k, (if k = i then A · B k else B k) = A · ∏ k, B k` --- the shape every box moment takes
after Fubini: one distinguished coordinate, all the others contributing their side length. -/
private theorem prod_ite_single_box (i : Fin d) (A : ℝ) (B : Fin d → ℝ) :
    (∏ k : Fin d, if k = i then A * B k else B k) = A * ∏ k, B k := by
  have h : ∀ k : Fin d, (if k = i then A * B k else B k) = (if k = i then A else 1) * B k := by
    intro k
    split_ifs with hk
    · rfl
    · rw [one_mul]
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i (fun _ => A), ite_eq_left (Finset.mem_univ i)]

/-! ### The box moments -/

/-- **First moment: the centre is the barycentre.**  `∫_B (xᵢ − xᵢ) dx = 0`. -/
theorem setIntegral_coordBox_centered {lo hi : Fin d → ℝ} (hlt : ∀ i, lo i < hi i) (i : Fin d) :
    (∫ x in coordBox lo hi, (x i - boxCenter lo hi i)) = 0 := by
  have hpt : (fun x : Vec d => x i - boxCenter lo hi i)
      = fun x : Vec d => ∏ k, (if k = i then x k - (lo k + hi k) / 2 else 1) := by
    funext x
    rw [Finset.prod_ite_eq' Finset.univ i (fun k => x k - (lo k + hi k) / 2),
      ite_eq_left (Finset.mem_univ i), boxCenter_apply]
  have hbody : (fun t : ℝ => if i = i then t - (lo i + hi i) / 2 else (1 : ℝ))
      = fun t : ℝ => t - (lo i + hi i) / 2 := by
    funext t
    rw [ite_eq_left rfl]
  rw [hpt, setIntegral_coordBox_prod lo hi
    (fun k t => if k = i then t - (lo k + hi k) / 2 else 1)]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  show (∫ t in Set.Ioo (lo i) (hi i), if i = i then t - (lo i + hi i) / 2 else (1 : ℝ)) = 0
  rw [hbody]
  exact integral_Ioo_mid (hlt i).le

/-- **The box second moment, unnormalized.**
`∫_B (xᵢ − xᵢ)(x_j − x_j) dx = δ_{ij} · |B| · (hiᵢ − loᵢ)²/12`. -/
theorem setIntegral_coordBox_centered_mul {lo hi : Fin d → ℝ} (hlt : ∀ i, lo i < hi i)
    (i j : Fin d) :
    (∫ x in coordBox lo hi, (x i - boxCenter lo hi i) * (x j - boxCenter lo hi j))
      = if i = j then (∏ k, (hi k - lo k)) * ((hi i - lo i) ^ 2 / 12) else 0 := by
  have hpt : (fun x : Vec d => (x i - boxCenter lo hi i) * (x j - boxCenter lo hi j))
      = fun x : Vec d =>
        ∏ k, ((if k = i then x k - (lo k + hi k) / 2 else 1)
          * (if k = j then x k - (lo k + hi k) / 2 else 1)) := by
    funext x
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ i (fun k => x k - (lo k + hi k) / 2),
      Finset.prod_ite_eq' Finset.univ j (fun k => x k - (lo k + hi k) / 2),
      ite_eq_left (Finset.mem_univ i), ite_eq_left (Finset.mem_univ j), boxCenter_apply, boxCenter_apply]
  rw [hpt, setIntegral_coordBox_prod lo hi
    (fun k t => (if k = i then t - (lo k + hi k) / 2 else 1)
      * (if k = j then t - (lo k + hi k) / 2 else 1))]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    have hfac : ∀ k : Fin d,
        (∫ t in Set.Ioo (lo k) (hi k),
            (if k = i then t - (lo k + hi k) / 2 else 1)
              * (if k = i then t - (lo k + hi k) / 2 else 1))
          = if k = i then (hi i - lo i) ^ 2 / 12 * (hi k - lo k) else hi k - lo k := by
      intro k
      by_cases hk : k = i
      · have hbody : ∀ t : ℝ,
            (if k = i then t - (lo k + hi k) / 2 else 1)
                * (if k = i then t - (lo k + hi k) / 2 else 1)
              = (t - (lo k + hi k) / 2) ^ 2 := by
          intro t
          rw [ite_eq_left hk]
          ring
        simp only [hbody]
        rw [ite_eq_left hk, integral_Ioo_mid_sq (hlt k).le, hk]
        ring
      · have hbody : ∀ t : ℝ,
            (if k = i then t - (lo k + hi k) / 2 else 1)
                * (if k = i then t - (lo k + hi k) / 2 else 1)
              = (1 : ℝ) := by
          intro t
          rw [ite_eq_right hk]
          ring
        simp only [hbody]
        rw [ite_eq_right hk, integral_Ioo_length (hlt k).le]
    rw [Finset.prod_congr rfl (fun k _ => hfac k),
      prod_ite_single_box i ((hi i - lo i) ^ 2 / 12) (fun k => hi k - lo k)]
    ring
  · rw [ite_eq_right hij]
    have hbody : (fun t : ℝ =>
        (if i = i then t - (lo i + hi i) / 2 else 1)
          * (if i = j then t - (lo i + hi i) / 2 else (1 : ℝ)))
          = fun t : ℝ => t - (lo i + hi i) / 2 := by
      funext t
      rw [ite_eq_left rfl, ite_eq_right hij, mul_one]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    show (∫ t in Set.Ioo (lo i) (hi i),
        (if i = i then t - (lo i + hi i) / 2 else 1)
          * (if i = j then t - (lo i + hi i) / 2 else (1 : ℝ))) = 0
    rw [hbody]
    exact integral_Ioo_mid (hlt i).le

/-! ### Affine functions on a box: the sharp `L²` identity -/

private theorem integrableOn_coordBox_coordSum (lo hi : Fin d → ℝ) (a : Fin d → ℝ) :
    IntegrableOn (fun x : Vec d => ∑ i, a i * (x i - boxCenter lo hi i)) (coordBox lo hi) :=
  integrableOn_coordBox_of_continuous
    (continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).sub continuous_const)) lo hi

private theorem integrableOn_coordBox_coordQuad (lo hi : Fin d → ℝ) (g : Vec d) :
    IntegrableOn (fun x : Vec d => ∑ i, ∑ j, (g i * g j)
        * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j))) (coordBox lo hi) :=
  integrableOn_coordBox_of_continuous
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (((continuous_apply i).sub continuous_const).mul
        ((continuous_apply j).sub continuous_const))) lo hi

/-- The linear part of an affine function integrates to zero over a box. -/
theorem setIntegral_coordBox_coordSum {lo hi : Fin d → ℝ} (hlt : ∀ i, lo i < hi i)
    (a : Fin d → ℝ) :
    (∫ x in coordBox lo hi, ∑ i, a i * (x i - boxCenter lo hi i)) = 0 := by
  have hsum : (∫ x in coordBox lo hi, ∑ i, a i * (x i - boxCenter lo hi i))
      = ∑ i, ∫ x in coordBox lo hi, a i * (x i - boxCenter lo hi i) :=
    MeasureTheory.integral_finsetSum _ (fun i _ =>
      integrableOn_coordBox_of_continuous
        (continuous_const.mul ((continuous_apply i).sub continuous_const)) lo hi)
  rw [hsum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MeasureTheory.integral_const_mul, setIntegral_coordBox_centered hlt i, mul_zero]

/-- The quadratic part: the box second moment, summed against `g ⊗ g`. -/
theorem setIntegral_coordBox_coordQuad {lo hi : Fin d → ℝ} (hlt : ∀ i, lo i < hi i) (g : Vec d) :
    (∫ x in coordBox lo hi, ∑ i, ∑ j, (g i * g j)
        * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j)))
      = (∏ k, (hi k - lo k)) * ∑ i, g i ^ 2 * ((hi i - lo i) ^ 2 / 12) := by
  have hint : ∀ i j : Fin d, IntegrableOn (fun x : Vec d => (g i * g j)
      * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j))) (coordBox lo hi) :=
    fun i j => integrableOn_coordBox_of_continuous
      (continuous_const.mul (((continuous_apply i).sub continuous_const).mul
        ((continuous_apply j).sub continuous_const))) lo hi
  have hinner : ∀ i : Fin d, IntegrableOn (fun x : Vec d => ∑ j, (g i * g j)
      * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j))) (coordBox lo hi) :=
    fun i => integrableOn_coordBox_of_continuous
      (continuous_finsetSum _ fun j _ => continuous_const.mul
        (((continuous_apply i).sub continuous_const).mul
          ((continuous_apply j).sub continuous_const))) lo hi
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hinner i)]
  have hstep : ∀ i : Fin d, (∫ x in coordBox lo hi, ∑ j, (g i * g j)
      * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j)))
      = g i ^ 2 * ((hi i - lo i) ^ 2 / 12) * ∏ k, (hi k - lo k) := by
    intro i
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)]
    have hj : ∀ j : Fin d, (∫ x in coordBox lo hi, (g i * g j)
        * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j)))
        = if j = i then g i ^ 2 * ((hi i - lo i) ^ 2 / 12) * ∏ k, (hi k - lo k) else 0 := by
      intro j
      rw [MeasureTheory.integral_const_mul, setIntegral_coordBox_centered_mul hlt i j]
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl, ite_eq_left rfl]
        ring
      · rw [ite_eq_right hji, ite_eq_right (fun h : i = j => hji h.symm), mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hj j),
      Finset.sum_ite_eq' Finset.univ i
        (fun _ => g i ^ 2 * ((hi i - lo i) ^ 2 / 12) * ∏ k, (hi k - lo k)),
      ite_eq_left (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.sum_mul]
  ring

/-- **The sharp `L²` identity for an affine function on a box.**
`⨍_B (c + g·x)² = (c + g·x)² + ∑ᵢ gᵢ² (hiᵢ − loᵢ)²/12`, with `x = boxCenter lo hi`. -/
theorem volumeAverage_coordBox_affineEval_sq {lo hi : Fin d → ℝ} (hlt : ∀ i, lo i < hi i)
    (c : ℝ) (g : Vec d) :
    volumeAverage (coordBox lo hi) (fun y => affineEval c g y ^ 2)
      = affineEval c g (boxCenter lo hi) ^ 2
        + ∑ i, g i ^ 2 * ((hi i - lo i) ^ 2 / 12) := by
  have hVpos : 0 < ∏ k, (hi k - lo k) :=
    Finset.prod_pos fun k _ => by linarith only [hlt k]
  refine volumeAverage_eq_of_setIntegral (V := ∏ k, (hi k - lo k)) (ne_of_gt hVpos)
    (volume_coordBox_toReal fun i => (hlt i).le) ?_
  have hpt : ∀ x : Vec d, affineEval c g x ^ 2
      = affineEval c g (boxCenter lo hi) ^ 2
          + (∑ i, (2 * affineEval c g (boxCenter lo hi) * g i) * (x i - boxCenter lo hi i))
        + ∑ i, ∑ j, (g i * g j)
            * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j)) := by
    intro x
    have hs := affineEval_eq_center_add c g (boxCenter lo hi) x
    have hsq : (∑ i, g i * (x i - boxCenter lo hi i)) ^ 2
        = ∑ i, ∑ j, (g i * g j)
            * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j)) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hlin : (∑ i, (2 * affineEval c g (boxCenter lo hi) * g i) * (x i - boxCenter lo hi i))
        = 2 * affineEval c g (boxCenter lo hi) * ∑ i, g i * (x i - boxCenter lo hi i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs, hlin, ← hsq]
    ring
  have hcongr : (∫ x in coordBox lo hi, affineEval c g x ^ 2)
      = ∫ x in coordBox lo hi, (affineEval c g (boxCenter lo hi) ^ 2
          + (∑ i, (2 * affineEval c g (boxCenter lo hi) * g i) * (x i - boxCenter lo hi i))
        + ∑ i, ∑ j, (g i * g j)
            * ((x i - boxCenter lo hi i) * (x j - boxCenter lo hi j))) :=
    MeasureTheory.setIntegral_congr_fun (measurableSet_coordBox lo hi) (fun x _ => hpt x)
  have hint12 : IntegrableOn (fun x : Vec d => affineEval c g (boxCenter lo hi) ^ 2
      + ∑ i, (2 * affineEval c g (boxCenter lo hi) * g i) * (x i - boxCenter lo hi i))
      (coordBox lo hi) :=
    integrableOn_coordBox_of_continuous
      (continuous_const.add (continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).sub continuous_const))) lo hi
  rw [hcongr, MeasureTheory.integral_add hint12 (integrableOn_coordBox_coordQuad lo hi g),
    MeasureTheory.integral_add (integrableOn_coordBox_of_continuous continuous_const lo hi)
      (integrableOn_coordBox_coordSum lo hi _),
    setIntegral_coordBox_coordSum hlt _, setIntegral_coordBox_coordQuad hlt g,
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    volume_coordBox_toReal (fun i => (hlt i).le), smul_eq_mul, add_zero]
  ring

/-- The seminorm form of the identity, before taking the square root. -/
theorem normalizedL2On_coordBox_affineEval_sq {lo hi : Fin d → ℝ} (hlt : ∀ i, lo i < hi i)
    (c : ℝ) (g : Vec d) :
    normalizedL2On (coordBox lo hi) (affineEval c g) ^ 2
      = affineEval c g (boxCenter lo hi) ^ 2
        + ∑ i, g i ^ 2 * ((hi i - lo i) ^ 2 / 12) := by
  rw [normalizedL2On_sq, volumeAverage_coordBox_affineEval_sq hlt c g]

/-- The seminorm form of the identity, as a square root. -/
theorem normalizedL2On_coordBox_affineEval {lo hi : Fin d → ℝ} (hlt : ∀ i, lo i < hi i)
    (c : ℝ) (g : Vec d) :
    normalizedL2On (coordBox lo hi) (affineEval c g)
      = Real.sqrt (affineEval c g (boxCenter lo hi) ^ 2
          + ∑ i, g i ^ 2 * ((hi i - lo i) ^ 2 / 12)) := by
  rw [normalizedL2On, volumeAverage_coordBox_affineEval_sq hlt c g]

/-! ### The two comparison corollaries -/

/-- If the `i`-slope vanishes then the value of `ℓ` at the centre only sees the coordinate sums
`loⱼ + hiⱼ` for `j ≠ i`. -/
private theorem affineEval_boxCenter_congr {lo hi lo' hi' : Fin d → ℝ} {i : Fin d}
    {c : ℝ} {g : Vec d} (hg : g i = 0)
    (hcen : ∀ j, j ≠ i → lo' j + hi' j = lo j + hi j) :
    affineEval c g (boxCenter lo' hi') = affineEval c g (boxCenter lo hi) := by
  have hs : ∑ j, g j * boxCenter lo' hi' j = ∑ j, g j * boxCenter lo hi j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · rw [hj, hg]
      ring
    · rw [boxCenter_apply, boxCenter_apply, hcen j hj]
  rw [affineEval, affineEval, vecDot, vecDot, hs]

/-- **Sliding the box along a direction of vanishing slope changes nothing.** -/
theorem normalizedL2On_coordBox_affineEval_congr_of_slope_zero
    {lo hi lo' hi' : Fin d → ℝ} (hlt : ∀ j, lo j < hi j) (hlt' : ∀ j, lo' j < hi' j)
    {i : Fin d} {c : ℝ} {g : Vec d} (hg : g i = 0)
    (hsame : ∀ j, j ≠ i → lo' j = lo j ∧ hi' j = hi j) :
    normalizedL2On (coordBox lo' hi') (affineEval c g)
      = normalizedL2On (coordBox lo hi) (affineEval c g) := by
  have hctr : affineEval c g (boxCenter lo' hi') = affineEval c g (boxCenter lo hi) :=
    affineEval_boxCenter_congr hg fun j hj => by
      obtain ⟨h1, h2⟩ := hsame j hj
      rw [h1, h2]
  have hsum : ∑ j, g j ^ 2 * ((hi' j - lo' j) ^ 2 / 12)
      = ∑ j, g j ^ 2 * ((hi j - lo j) ^ 2 / 12) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · rw [hj, hg]
      ring
    · obtain ⟨h1, h2⟩ := hsame j hj
      rw [h1, h2]
  rw [normalizedL2On_coordBox_affineEval hlt' c g, normalizedL2On_coordBox_affineEval hlt c g,
    hctr, hsum]

/-- **Reverse Chebyshev for affine functions: halving the transverse sides of a
concentric box costs at most the factor two.** -/
theorem normalizedL2On_coordBox_affineEval_half_le
    {lo hi lo' hi' : Fin d → ℝ} (hlt : ∀ j, lo j < hi j) (hlt' : ∀ j, lo' j < hi' j)
    {i : Fin d} {c : ℝ} {g : Vec d} (hg : g i = 0)
    (hcen : ∀ j, j ≠ i → lo' j + hi' j = lo j + hi j)
    (hside : ∀ j, j ≠ i → hi j - lo j ≤ 2 * (hi' j - lo' j)) :
    (1 / 2 : ℝ) * normalizedL2On (coordBox lo hi) (affineEval c g)
      ≤ normalizedL2On (coordBox lo' hi') (affineEval c g) := by
  have hctr : affineEval c g (boxCenter lo' hi') = affineEval c g (boxCenter lo hi) :=
    affineEval_boxCenter_congr hg hcen
  have hterm : ∀ j : Fin d, g j ^ 2 * ((hi j - lo j) ^ 2 / 12)
      ≤ 4 * (g j ^ 2 * ((hi' j - lo' j) ^ 2 / 12)) := by
    intro j
    by_cases hj : j = i
    · rw [hj, hg]
      norm_num
    · have h1 : (0 : ℝ) ≤ hi j - lo j := by linarith only [hlt j]
      have h3 := hside j hj
      have hsq := mul_self_le_mul_self h1 h3
      have hXY : (hi j - lo j) ^ 2 / 12 ≤ 4 * ((hi' j - lo' j) ^ 2 / 12) := by
        linarith only [hsq]
      calc g j ^ 2 * ((hi j - lo j) ^ 2 / 12)
          ≤ g j ^ 2 * (4 * ((hi' j - lo' j) ^ 2 / 12)) :=
            mul_le_mul_of_nonneg_left hXY (sq_nonneg (g j))
        _ = 4 * (g j ^ 2 * ((hi' j - lo' j) ^ 2 / 12)) := by ring
  rw [normalizedL2On_coordBox_affineEval hlt c g, normalizedL2On_coordBox_affineEval hlt' c g,
    hctr]
  have hsum : ∑ j, g j ^ 2 * ((hi j - lo j) ^ 2 / 12)
      ≤ 4 * ∑ j, g j ^ 2 * ((hi' j - lo' j) ^ 2 / 12) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    rwa [← Finset.mul_sum] at h
  have hkey : 1 / 4 * (affineEval c g (boxCenter lo hi) ^ 2
      + ∑ j, g j ^ 2 * ((hi j - lo j) ^ 2 / 12))
      ≤ affineEval c g (boxCenter lo hi) ^ 2
        + ∑ j, g j ^ 2 * ((hi' j - lo' j) ^ 2 / 12) := by
    linarith only [hsum, sq_nonneg (affineEval c g (boxCenter lo hi))]
  have hhalf : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc (1 / 2 : ℝ) * Real.sqrt (affineEval c g (boxCenter lo hi) ^ 2
        + ∑ j, g j ^ 2 * ((hi j - lo j) ^ 2 / 12))
      = Real.sqrt (1 / 4 * (affineEval c g (boxCenter lo hi) ^ 2
          + ∑ j, g j ^ 2 * ((hi j - lo j) ^ 2 / 12))) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4), hhalf]
    _ ≤ Real.sqrt (affineEval c g (boxCenter lo hi) ^ 2
          + ∑ j, g j ^ 2 * ((hi' j - lo' j) ^ 2 / 12)) := Real.sqrt_le_sqrt hkey

/-! ### Translation, domination, constants -/

/-- The image of a box under a translation is a box. -/
theorem image_sub_coordBox (lo hi : Fin d → ℝ) (v : Vec d) :
    (fun z => z - v) '' coordBox lo hi
      = coordBox (fun j => lo j - v j) (fun j => hi j - v j) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_coordBox_iff] at hx ⊢
    intro j
    obtain ⟨h1, h2⟩ := hx j
    refine ⟨?_, ?_⟩
    · show lo j - v j < x j - v j
      linarith only [h1]
    · show x j - v j < hi j - v j
      linarith only [h2]
  · intro hy
    rw [mem_coordBox_iff] at hy
    refine ⟨y + v, ?_, ?_⟩
    · rw [mem_coordBox_iff]
      intro j
      obtain ⟨h1, h2⟩ := hy j
      refine ⟨?_, ?_⟩
      · show lo j < y j + v j
        linarith only [h1]
      · show y j + v j < hi j
        linarith only [h2]
    · funext j
      show y j + v j - v j = y j
      ring

private theorem image_sub_eq_preimage_add (W : Set (Vec d)) (v : Vec d) :
    (fun z => z - v) '' W = (fun z => z + v) ⁻¹' W := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show x - v + v ∈ W
    rwa [sub_add_cancel]
  · intro hy
    refine ⟨y + v, hy, ?_⟩
    show y + v - v = y
    abel

/-- **Translation invariance of the normalized seminorm.** -/
theorem normalizedL2On_comp_sub_right (W : Set (Vec d)) (v : Vec d) (f : Vec d → ℝ) :
    normalizedL2On W (fun y => f (y - v)) = normalizedL2On ((fun z => z - v) '' W) f := by
  have hvol : (volume ((fun z : Vec d => z - v) '' W)).toReal = (volume W).toReal := by
    rw [image_sub_eq_preimage_add W v, measure_preimage_add_right]
  have hint : (∫ y in (fun z : Vec d => z - v) '' W, f y ^ 2)
      = ∫ x in W, f (x - v) ^ 2 :=
    (measurePreserving_sub_right (volume : Measure (Vec d)) v).setIntegral_image_emb
      (measurableEmbedding_subRight v) (fun y => f y ^ 2) W
  show Real.sqrt (volumeAverage W fun y => f (y - v) ^ 2)
      = Real.sqrt (volumeAverage ((fun z : Vec d => z - v) '' W) fun y => f y ^ 2)
  unfold volumeAverage
  rw [hvol, hint]

/-- **Pointwise domination.** -/
theorem normalizedL2On_mono_of_abs_le {W : Set (Vec d)} (hW : MeasurableSet W)
    {f g : Vec d → ℝ} (hf : IntegrableOn (fun y => f y ^ 2) W volume)
    (hg : IntegrableOn (fun y => g y ^ 2) W volume)
    (h : ∀ y ∈ W, |f y| ≤ g y) :
    normalizedL2On W f ≤ normalizedL2On W g := by
  have hmono : volumeAverage W (fun y => f y ^ 2) ≤ volumeAverage W (fun y => g y ^ 2) := by
    unfold volumeAverage
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine MeasureTheory.setIntegral_mono_on hf hg hW ?_
    intro y hy
    obtain ⟨hl, hr⟩ := abs_le.1 (h y hy)
    exact sq_le_sq' hl hr
  exact Real.sqrt_le_sqrt hmono

/-- The seminorm of a constant. -/
theorem normalizedL2On_const_of_toReal_pos {W : Set (Vec d)}
    (hpos : 0 < (volume W).toReal)
    (c : ℝ) : normalizedL2On W (fun _ => c) = |c| := by
  have hne : (volume W).toReal ≠ 0 := ne_of_gt hpos
  have hAvg : volumeAverage W (fun _ : Vec d => c ^ 2) = c ^ 2 := by
    unfold volumeAverage
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  show Real.sqrt (volumeAverage W fun _ : Vec d => c ^ 2) = |c|
  rw [hAvg, Real.sqrt_sq_eq_abs]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
