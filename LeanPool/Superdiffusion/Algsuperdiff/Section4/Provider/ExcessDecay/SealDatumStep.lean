/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringVolume
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryClauseSkeleton
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanControlReduction

/-!
# SealDatumStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The datum step of the `S4.3` boundary lane, closed on the anchor's own core cube

## What is proved

Let `x, z ∈ □_m`, `n + 2 ≤ m`, and let the anchor's geometry binder
`x + □_n ⊆ (z + □_{n+1}) ∩ □_m` hold.  Write

```text
  V₁ := wellPlacedCentre x m (n+2) + □_{n+2}      (the anchor's covering cube)
  K  := wellPlacedCentre z m (n+2) + □_{n+2}      (the boundary-flush cube)
  W' := (z + □_{n+3}) ∩ □_m                       (the anchor's own window)
```

and let `K' := c' + □_n` be **any** scale-`n` cube inside `K` (the intended
instance is the sub-cube flush against the face `K` shares with `∂□_m`).  For the
anchor's Dirichlet datum `h : H1Function □_m` this module proves, with **no
hypothesis beyond those binders**,

```text
  |⨍_{V₁} h − ⨍_{K'} h|
      ≤ datumStepConst d · 3^n · Σᵢ ‖∂ᵢh‖_{L²(W')} ,
```

`datumStepConst d = 27 · 3^d · 3^d · unitMeanZeroPoincareConst d`, i.e. exactly
the frozen fifth-leg shape: a constant depending on `d` alone, a single factor
`3^n`, the gradient read on `W'`, no `s`-power, no `σ`, no `ν`.

## The mechanism: the anchor's own core cube, not a translation estimate

The route originally scoped for this step was the `H¹` **translation** estimate
between the two scale-`(n+2)` cubes `V₁` and `K` (they *are* translates of one
another).  That route needs the fundamental theorem of calculus along lines for a
*weak* gradient, which exists nowhere in the upstream library.  It is not needed.

The anchor's binders already supply a set contained in **both** cubes, namely the
anchor's own core window

```text
  J := x + □_n .
```

Indeed `J ⊆ □_m` and `J ⊆ z + □_{n+1}` are two halves of the geometry binder,
so `J ⊆ truncatedWindow x m n ⊆ V₁` and `J ⊆ truncatedWindow z m (n+1) ⊆ K` by
the proved covering lemma `truncatedWindow_subset_image_add_wellPlacedCentre`
at the scales `n ≤ n+2` and `n+1 ≤ n+2`.  Since `|V₁| / |J| = |K| / |J| = |K| /
|K'| = 9^d`, the three mean transfers of `MeanControlReduction` each cost the
*exact* factor `3^d`, and the chain

```text
  |⨍_{V₁}h − ⨍_{K'}h| ≤ |⨍_{V₁}h − ⨍_J h| + |⨍_J h − ⨍_K h| + |⨍_K h − ⨍_{K'}h|
```

is closed by the **equal-sides** mean-zero cube Poincaré on `V₁` and on `K`
separately.  Both are genuine cubes of side `3^{n+2}` sitting inside `□_m`, so
`BoundaryClauseSkeleton.eLpNorm_sub_average_coveringCube_le_meanZeroPoincare`
applies verbatim (read at `x`, and at `z`).  The window `W'` enters only
through the two proved `L²` transports at the `3^d` volume ratio.

## A recorded side fact: the window's eccentricity

Section 7 records, independently of the chain above, that `W'` is an
axis-aligned box **all of whose edges have length in `(½·3^{n+3}, 3^{n+3}]`** —
i.e. its eccentricity is at most `2`, uniformly over every configuration the
anchor's binders allow.  Nothing in sections 1--6 consumes it.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 0. Volume and integrability slots of a translated origin cube -/

/-- The real volume of a translated origin cube. -/
theorem volume_toReal_image_add_openCubeSet_originCube (c : Vec d) (k : ℤ) :
    (volume ((fun y => c + y) '' openCubeSet (originCube d k))).toReal =
      ((3 : ℝ) ^ k) ^ d := by
  rw [volume_image_add c (openCubeSet (originCube d k)),
    volume_toReal_openCubeSet_originCube]

/-- A translated origin cube has finite volume. -/
theorem volume_image_add_openCubeSet_ne_top (c : Vec d) (k : ℤ) :
    volume ((fun y => c + y) '' openCubeSet (originCube d k)) ≠ ⊤ := by
  rw [volume_image_add c (openCubeSet (originCube d k))]
  exact volume_openCubeSet_originCube_ne_top d k

/-- A translated origin cube has positive real volume. -/
theorem volume_toReal_image_add_openCubeSet_pos (c : Vec d) (k : ℤ) :
    0 < (volume ((fun y => c + y) '' openCubeSet (originCube d k))).toReal := by
  rw [volume_toReal_image_add_openCubeSet_originCube]
  exact pow_pos (zpow_pos (by norm_num) _) d

/-- A translated origin cube is measurable. -/
theorem measurableSet_image_add_openCubeSet_originCube (c : Vec d) (k : ℤ) :
    MeasurableSet ((fun y => c + y) '' openCubeSet (originCube d k)) :=
  (isOpen_image_add_openCubeSet_originCube c k).measurableSet

/-- The datum is `L²` on every subset of its own domain. -/
theorem memLp_toFun_of_subset {m : ℤ} (h : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) :
    MemLp h.toFun 2 (volume.restrict A) :=
  h.memL2.mono_measure (Measure.restrict_mono hA le_rfl)

/-- Each coordinate of the datum's weak gradient is `L²` on every subset of the
datum's own domain. -/
theorem memLp_grad_of_subset {m : ℤ} (h : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) (i : Fin d) :
    MemLp (fun y => h.grad y i) 2 (volume.restrict A) :=
  (h.gradMemL2 i).mono_measure (Measure.restrict_mono hA le_rfl)

/-- An `L²` function on a finite-measure set is integrable there. -/
theorem integrableOn_of_memLp_two {A : Set (Vec d)} (hAtop : volume A ≠ ⊤)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict A)) :
    IntegrableOn f A volume := by
  have : IsFiniteMeasure (volume.restrict A) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hAtop
  exact hf.integrable (by norm_num)

/-- The square of a mean-shifted `L²` function is integrable. -/
theorem integrableOn_sub_const_sq {A : Set (Vec d)} (hAtop : volume A ≠ ⊤)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict A)) (b : ℝ) :
    IntegrableOn (fun y => (f y - b) ^ 2) A volume := by
  have : IsFiniteMeasure (volume.restrict A) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hAtop
  have hb : MemLp (fun _ : Vec d => b) 2 (volume.restrict A) := memLp_const b
  have hsub : MemLp (fun y => f y - b) 2 (volume.restrict A) := hf.sub hb
  have hsq := hsub.integrable_sq
  simpa only [IntegrableOn] using hsq

/-! ## 1. The anchor's own core cube sits inside both scale-`(n+2)` cubes -/

/-- **The core cube lies in the anchor's covering cube.**

`x + □_n ⊆ wellPlacedCentre x m (n+2) + □_{n+2}`: the anchor's geometry binder
puts `x + □_n` inside `□_m`, so it is the truncated window `truncatedWindow x m
n` and the proved covering lemma applies at `n ≤ n + 2`. -/
theorem image_add_x_subset_coveringCube {n m : ℤ} {x z : Vec d} (hnm : n + 2 ≤ m)
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      (fun y => wellPlacedCentre x m (n + 2) + y) '' openCubeSet (originCube d (n + 2)) := by
  intro p hp
  refine truncatedWindow_subset_image_add_wellPlacedCentre x hnm
    (by omega : n ≤ n + 2) ?_
  exact ⟨hp, (hgeom hp).2⟩

/-- **The core cube lies in the boundary-flush cube.**

`x + □_n ⊆ wellPlacedCentre z m (n+2) + □_{n+2}`: the anchor's geometry binder
puts `x + □_n` inside `truncatedWindow z m (n+1)`, and the proved covering
lemma applies at `n + 1 ≤ n + 2`. -/
theorem image_add_x_subset_flushCube {n m : ℤ} {x z : Vec d} (hnm : n + 2 ≤ m)
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      (fun y => wellPlacedCentre z m (n + 2) + y) '' openCubeSet (originCube d (n + 2)) := by
  intro p hp
  exact truncatedWindow_subset_image_add_wellPlacedCentre z hnm
    (by omega : n + 1 ≤ n + 2) (hgeom hp)

/-! ## 2. The two-scale volume ratio -/

/-- The square root of the volume ratio between a scale-`(k+2)` cube and a
scale-`k` cube is exactly `3^d`. -/
theorem sqrt_volume_ratio_two_scales (c c' : Vec d) (k : ℤ) :
    Real.sqrt ((volume ((fun y => c + y) '' openCubeSet (originCube d (k + 2)))).toReal /
        (volume ((fun y => c' + y) '' openCubeSet (originCube d k))).toReal) =
      (3 : ℝ) ^ d := by
  rw [volume_toReal_image_add_openCubeSet_originCube,
    volume_toReal_image_add_openCubeSet_originCube]
  have h3 : (3 : ℝ) ^ (k + 2) = 9 * (3 : ℝ) ^ k := by
    have h2 : (3 : ℝ) ^ (2 : ℤ) = 9 := by norm_num
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), h2, mul_comm]
  have hpos : (0 : ℝ) < ((3 : ℝ) ^ k) ^ d := pow_pos (zpow_pos (by norm_num) _) d
  have hid : (((3 : ℝ) ^ (k + 2)) ^ d) / (((3 : ℝ) ^ k) ^ d) = (9 : ℝ) ^ d := by
    rw [h3, mul_pow, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]
  rw [hid]
  have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ 2 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h9, Real.sqrt_sq (by positivity)]

/-! ## 3. The two-scale mean transfer on the datum -/

/-- **The two-scale mean transfer.**

For a scale-`k` cube inside a scale-`(k+2)` cube, the gap between the two datum
means is at most `3^d` times the oscillation of the datum on the big cube. -/
theorem abs_volumeAverage_sub_cubeAverage_le {m k : ℤ} {c c' : Vec d}
    (hsub : (fun y => c' + y) '' openCubeSet (originCube d k) ⊆
      (fun y => c + y) '' openCubeSet (originCube d (k + 2)))
    (hcm : (fun y => c + y) '' openCubeSet (originCube d (k + 2)) ⊆
      openCubeSet (originCube d m))
    (h : H1Function (openCubeSet (originCube d m))) :
    |volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d k)) h.toFun -
        volumeAverage ((fun y => c + y) '' openCubeSet (originCube d (k + 2)))
          h.toFun| ≤
      (3 : ℝ) ^ d *
        normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d (k + 2)))
          (fun y => h.toFun y -
            volumeAverage ((fun y => c + y) '' openCubeSet (originCube d (k + 2)))
              h.toFun) := by
  classical
  set Big : Set (Vec d) := (fun y => c + y) '' openCubeSet (originCube d (k + 2)) with hBig
  set Small : Set (Vec d) := (fun y => c' + y) '' openCubeSet (originCube d k) with hSmall
  have hsmallm : Small ⊆ openCubeSet (originCube d m) := hsub.trans hcm
  have hfBig : MemLp h.toFun 2 (volume.restrict Big) := memLp_toFun_of_subset h hcm
  have hfSmall : MemLp h.toFun 2 (volume.restrict Small) := memLp_toFun_of_subset h hsmallm
  have hBigtop : volume Big ≠ ⊤ := volume_image_add_openCubeSet_ne_top c (k + 2)
  have hSmalltop : volume Small ≠ ⊤ := volume_image_add_openCubeSet_ne_top c' k
  have hbase := abs_volumeAverage_sub_windowAverage_le
    (W := Big) (V := Small)
    (measurableSet_image_add_openCubeSet_originCube c' k) hsub
    (volume_toReal_image_add_openCubeSet_pos c (k + 2))
    (volume_toReal_image_add_openCubeSet_pos c' k) hSmalltop
    (integrableOn_of_memLp_two hSmalltop hfSmall)
    (integrableOn_sub_const_sq hSmalltop hfSmall (volumeAverage Big h.toFun))
    (integrableOn_sub_const_sq hBigtop hfBig (volumeAverage Big h.toFun))
  rwa [sqrt_volume_ratio_two_scales c c' k] at hbase

/-! ## 4. The equal-sides cube Poincaré, in the `normalizedL2On` spelling -/

/-- **The mean-zero Poincaré on a well-placed cube, in the real seminorm.**

`BoundaryClauseSkeleton.eLpNorm_sub_average_coveringCube_le_meanZeroPoincare`
read through the `normalizedL2On` dictionary.  The cube is a genuine equal-sides
cube of side `3^{n+2}` inside `□_m`, so the constant is scale-uniform: it is
`unitMeanZeroPoincareConst d` times the side length. -/
theorem normalizedL2On_sub_average_wellPlacedCube_le {n m : ℤ} (hnm : n + 2 ≤ m)
    (x : Vec d) (h : H1Function (openCubeSet (originCube d m))) :
    normalizedL2On
        ((fun y => wellPlacedCentre x m (n + 2) + y) '' openCubeSet (originCube d (n + 2)))
        (fun y => h.toFun y -
          volumeAverage ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
            openCubeSet (originCube d (n + 2))) h.toFun) ≤
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
                openCubeSet (originCube d (n + 2))))).toReal := by
  classical
  set cc : Set (Vec d) :=
    (fun y' => wellPlacedCentre x m (n + 2) + y') '' openCubeSet (originCube d (n + 2))
    with hcc
  have hccsub : cc ⊆ openCubeSet (originCube d m) := by
    rw [hcc]
    exact image_add_wellPlacedCentre_subset_openCubeSet x hnm
  have hcctop : volume cc ≠ ⊤ := volume_image_add_openCubeSet_ne_top _ (n + 2)
  have hccpos : 0 < volume cc := by
    have := volume_toReal_image_add_openCubeSet_pos (wellPlacedCentre x m (n + 2)) (n + 2)
    rw [← hcc] at this
    exact ENNReal.toReal_pos_iff.mp this |>.1
  have hf : MemLp h.toFun 2 (volume.restrict cc) := memLp_toFun_of_subset h hccsub
  have hconst : MemLp (fun _ : Vec d => volumeAverage cc h.toFun) 2 (volume.restrict cc) := by
    have : IsFiniteMeasure (volume.restrict cc) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2 hcctop
    exact memLp_const _
  have hbridge := Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
    (W := cc) (f := fun y => h.toFun y - volumeAverage cc h.toFun) hccpos hcctop (hf.sub hconst)
  rw [hbridge]
  exact eLpNorm_sub_average_coveringCube_le_meanZeroPoincare (x := x) hnm h

/-! ## 5. The `L²` transport of a scale-`(n+2)` cube onto the frozen window -/

/-- **The window transport at a general centre.**

Any scale-`(n+2)` cube inside the frozen window `W' = (z+□_{n+3}) ∩ □_m` prices
its normalized `L²` norms at the volume ratio `3^d`.  The volume comparison
`volume_anchorWindow_le_coveringCube` carries no hypothesis on the centre, so
this serves the `x`-cube and the `z`-cube alike. -/
theorem toReal_eLpNorm_cube_le_anchorWindow {n m : ℤ} {z c : Vec d}
    (hsub : (fun y => c + y) '' openCubeSet (originCube d (n + 2)) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    {f : Vec d → ℝ}
    (hfin : eLpNorm f 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤) :
    (eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => c + y) '' openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d *
        (eLpNorm f 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  have hbase := eLpNorm_le_of_volume_le (K := ENNReal.ofReal ((9 : ℝ) ^ d))
    hsub (by simp) (by simp) (volume_anchorWindow_le_coveringCube n m z c) f
  have hhalf : (ENNReal.ofReal ((9 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((3 : ℝ) ^ d) := by
    have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ (2 : ℕ) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (9 : ℝ) ^ d), h9,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rw [hhalf] at hbase
  have hRne : ENNReal.ofReal ((3 : ℝ) ^ d) *
      eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hstep := ENNReal.toReal_mono hRne hbase
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep

/-- **The coordinate-sum form of the window transport, on the datum's gradient.** -/
theorem sum_toReal_eLpNorm_grad_cube_le_anchorWindow {n m : ℤ} {z c : Vec d}
    (hsub : (fun y => c + y) '' openCubeSet (originCube d (n + 2)) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (h : H1Function (openCubeSet (originCube d m))) :
    ∑ i : Fin d,
        (eLpNorm (fun y => h.grad y i) 2
          (Support.normalizedVolumeMeasureOn
            ((fun y => c + y) '' openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by
  classical
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  have hWm : W ⊆ openCubeSet (originCube d m) := by
    rw [hW]; exact Set.inter_subset_right
  have hW0 : volume W ≠ 0 := by
    intro h0
    have hcub : volume ((fun y => c + y) '' openCubeSet (originCube d (n + 2))) = 0 :=
      le_antisymm (h0 ▸ measure_mono hsub) zero_le
    have hpos := volume_toReal_image_add_openCubeSet_pos c (n + 2)
    rw [hcub] at hpos
    simp only [ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  have hfin : eLpNorm (fun y => h.grad y i) 2 (Support.normalizedVolumeMeasureOn W) ≠ ⊤ :=
    (memLp_normalizedVolumeMeasureOn_of_restrict hW0
      (memLp_grad_of_subset h hWm i)).eLpNorm_ne_top
  exact toReal_eLpNorm_cube_le_anchorWindow hsub hfin

/-! ## 6. The datum step -/

/-- The datum step's coefficient-free constant: `27 · 3^d · 3^d` times the
absolute mean-zero Poincaré constant of the unit cube. -/
def datumStepConst (d : ℕ) : ℝ :=
  27 * (3 : ℝ) ^ d * (3 : ℝ) ^ d * unitMeanZeroPoincareConst d

theorem datumStepConst_nonneg (d : ℕ) : 0 ≤ datumStepConst d := by
  have h1 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  unfold datumStepConst
  have h3 : (0 : ℝ) ≤ 27 * (3 : ℝ) ^ d * (3 : ℝ) ^ d := by positivity
  exact mul_nonneg h3 h1

/-- **The datum step of the boundary lane.**

The two datum means the boundary chain compares — the one on the anchor's own
covering cube `V₁ = wellPlacedCentre x m (n+2) + □_{n+2}` and the one on **any**
scale-`n` sub-cube `K'` of the boundary-flush cube `K = wellPlacedCentre z m
(n+2) + □_{n+2}` — differ by at most the frozen fifth-leg shape

```text
  datumStepConst d · 3^n · Σᵢ ‖∂ᵢh‖_{L²(W')} ,   W' = (z+□_{n+3}) ∩ □_m .
```

The proof chains three two-scale mean transfers through the anchor's own core
cube `x + □_n`, which the geometry binder places inside **both** scale-`(n+2)`
cubes, and closes each oscillation by the equal-sides mean-zero cube Poincaré on
`V₁` and on `K` separately.  No Poincaré inequality is taken on `W'`, no
translation estimate is used, and no analytic input is assumed. -/
theorem abs_volumeAverage_datum_sub_le_datumStep {n m : ℤ} {x z c' : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hz : z ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hK' : (fun y => c' + y) '' openCubeSet (originCube d n) ⊆
      (fun y => wellPlacedCentre z m (n + 2) + y) '' openCubeSet (originCube d (n + 2)))
    (h : H1Function (openCubeSet (originCube d m))) :
    |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))) h.toFun -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) h.toFun| ≤
      datumStepConst d * (3 : ℝ) ^ n *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by
  classical
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  set cx : Vec d := wellPlacedCentre x m (n + 2) with hcx
  set cz : Vec d := wellPlacedCentre z m (n + 2) with hcz
  set V₁ : Set (Vec d) := (fun y => cx + y) '' openCubeSet (originCube d (n + 2)) with hV
  set K : Set (Vec d) := (fun y => cz + y) '' openCubeSet (originCube d (n + 2)) with hK
  set J : Set (Vec d) := (fun y => x + y) '' openCubeSet (originCube d n) with hJ
  set Kp : Set (Vec d) := (fun y => c' + y) '' openCubeSet (originCube d n) with hKp
  set S : ℝ := ∑ i : Fin d,
    (eLpNorm (fun y => h.grad y i) 2 (Support.normalizedVolumeMeasureOn W)).toReal with hS
  -- the two scale-`(n+2)` cubes are inside the datum's domain and inside the window
  have hV₁m : V₁ ⊆ openCubeSet (originCube d m) := by
    rw [hV, hcx]; exact image_add_wellPlacedCentre_subset_openCubeSet x hnm
  have hKm : K ⊆ openCubeSet (originCube d m) := by
    rw [hK, hcz]; exact image_add_wellPlacedCentre_subset_openCubeSet z hnm
  have hKW : K ⊆ W := by
    rw [hK, hcz, hW]
    exact image_add_wellPlacedCentre_z_subset_anchorWindow hnm hz
  have hV₁W : V₁ ⊆ W := by
    rw [hV, hcx, hW]
    exact image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom
  -- the anchor's core cube sits inside both
  have hJV : J ⊆ V₁ := by
    rw [hJ, hV, hcx]; exact image_add_x_subset_coveringCube hnm hgeom
  have hJK : J ⊆ K := by
    rw [hJ, hK, hcz]; exact image_add_x_subset_flushCube hnm hgeom
  -- the three two-scale mean transfers
  have hT1 := abs_volumeAverage_sub_cubeAverage_le (k := n) (c := cx) (c' := x)
    (by rw [← hJ, ← hV]; exact hJV) (by rw [← hV]; exact hV₁m) h
  have hT2 := abs_volumeAverage_sub_cubeAverage_le (k := n) (c := cz) (c' := x)
    (by rw [← hJ, ← hK]; exact hJK) (by rw [← hK]; exact hKm) h
  have hT3 := abs_volumeAverage_sub_cubeAverage_le (k := n) (c := cz) (c' := c')
    (by rw [← hKp, ← hK]; exact hK') (by rw [← hK]; exact hKm) h
  rw [← hJ, ← hV] at hT1
  rw [← hJ, ← hK] at hT2
  rw [← hKp, ← hK] at hT3
  -- the equal-sides cube Poincaré on each of the two cubes
  have hP1 := normalizedL2On_sub_average_wellPlacedCube_le hnm x h
  have hP2 := normalizedL2On_sub_average_wellPlacedCube_le hnm z h
  rw [← hcx, ← hV] at hP1
  rw [← hcz, ← hK] at hP2
  -- the two window transports
  have hQ1 := sum_toReal_eLpNorm_grad_cube_le_anchorWindow (c := cx)
    (by rw [← hV, ← hW]; exact hV₁W) h
  have hQ2 := sum_toReal_eLpNorm_grad_cube_le_anchorWindow (c := cz)
    (by rw [← hK, ← hW]; exact hKW) h
  rw [← hV, ← hW, ← hS] at hQ1
  rw [← hK, ← hW, ← hS] at hQ2
  -- the arithmetic
  set P₁ : ℝ := normalizedL2On V₁ (fun y => h.toFun y - volumeAverage V₁ h.toFun) with hP₁
  set P₂ : ℝ := normalizedL2On K (fun y => h.toFun y - volumeAverage K h.toFun) with hP₂
  have hc3 : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  have hcP : (0 : ℝ) ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) := by
    have h1 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
    have h2 : (0 : ℝ) < (3 : ℝ) ^ (n + 2) := zpow_pos (by norm_num) _
    exact mul_nonneg h1 h2.le
  have hB : ∀ Q : ℝ, Q ≤ (3 : ℝ) ^ d * S →
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * Q ≤
        unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * ((3 : ℝ) ^ d * S) :=
    fun Q hQ => mul_le_mul_of_nonneg_left hQ hcP
  have hP1' : P₁ ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * ((3 : ℝ) ^ d * S) :=
    le_trans hP1 (hB _ hQ1)
  have hP2' : P₂ ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * ((3 : ℝ) ^ d * S) :=
    le_trans hP2 (hB _ hQ2)
  have htri1 := abs_sub_le (volumeAverage V₁ h.toFun) (volumeAverage J h.toFun)
    (volumeAverage Kp h.toFun)
  have htri2 := abs_sub_le (volumeAverage J h.toFun) (volumeAverage K h.toFun)
    (volumeAverage Kp h.toFun)
  have hs1 : |volumeAverage V₁ h.toFun - volumeAverage J h.toFun| ≤ (3 : ℝ) ^ d * P₁ := by
    rw [abs_sub_comm]; exact hT1
  have hs2 : |volumeAverage J h.toFun - volumeAverage K h.toFun| ≤ (3 : ℝ) ^ d * P₂ := hT2
  have hs3 : |volumeAverage K h.toFun - volumeAverage Kp h.toFun| ≤ (3 : ℝ) ^ d * P₂ := by
    rw [abs_sub_comm]; exact hT3
  have hfinal : |volumeAverage V₁ h.toFun - volumeAverage Kp h.toFun| ≤
      (3 : ℝ) ^ d * P₁ + ((3 : ℝ) ^ d * P₂ + (3 : ℝ) ^ d * P₂) := by
    linarith only [htri1, htri2, hs1, hs2, hs3]
  have hbig : (3 : ℝ) ^ d * P₁ + ((3 : ℝ) ^ d * P₂ + (3 : ℝ) ^ d * P₂) ≤
      datumStepConst d * (3 : ℝ) ^ n * S := by
    have hA1 : (3 : ℝ) ^ d * P₁ ≤
        (3 : ℝ) ^ d * (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * ((3 : ℝ) ^ d * S)) :=
      mul_le_mul_of_nonneg_left hP1' hc3
    have hA2 : (3 : ℝ) ^ d * P₂ ≤
        (3 : ℝ) ^ d * (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * ((3 : ℝ) ^ d * S)) :=
      mul_le_mul_of_nonneg_left hP2' hc3
    have hexp : (3 : ℝ) ^ (n + 2) = 9 * (3 : ℝ) ^ n := by
      have h2 : (3 : ℝ) ^ (2 : ℤ) = 9 := by norm_num
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), h2, mul_comm]
    have hid : 3 * ((3 : ℝ) ^ d *
        (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) * ((3 : ℝ) ^ d * S))) =
        datumStepConst d * (3 : ℝ) ^ n * S := by
      unfold datumStepConst
      rw [hexp]
      ring
    linarith only [hA1, hA2, hid]
  exact le_trans hfinal hbig

/-! ## 7. The frozen window is a box of eccentricity at most two -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
