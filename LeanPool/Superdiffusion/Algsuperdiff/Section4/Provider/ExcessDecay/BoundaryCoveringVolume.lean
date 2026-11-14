/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringGeometry

/-!
# BoundaryCoveringVolume

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The covering inequality of the boundary lane

`BoundaryCoveringGeometry` places a cube of side `3^k` so that it stays inside
`□_m` and covers the truncated window `(x+□_j) ∩ □_m`.  This module supplies
the quantitative half of the printed "simple covering argument": a
**normalized** quantity on the anchor's window is controlled by the same
normalized quantity on CoarseGraining's Caccioppoli core, at the dimension-only
cost

```text
  |core| / |(x+□_{k-2}) ∩ □_m|  ≤  3^d .
```

## Where the `3^d` comes from (disclosed)

The lower bound on the window volume is obtained by *inscribing a cube*: the
well-placed cube of side `3^{k-3}` centred at `wellPlacedCentre x m (k-3)` fits
inside `(x+□_{k-2}) ∩ □_m` (a clamped centre moves by less than half a side, so
the inscribed cube stays within `3^{k-3}` of `x`, and `3^{k-3} < 3^{k-2}/2`).
The core is contained in a cube of side `3^{k-2} = 3·3^{k-3}`, whence `3^d`.

The sharp constant for this geometry is `2^d` (each coordinate interval of the
truncated window has length at least `3^{k-2}/2`), obtained by computing the
volume of the window as a product of intervals.  The inscribed-cube route is
taken here because it reuses the cube volume A verbatim; the loss is a
`(3/2)^d` factor inside a `C(d)` and is recorded, not hidden.

## Main results

* `image_add_wellPlacedCentre_subset_truncatedWindow` — the inscribed cube.
* `volume_toReal_image_add_openCubeSet_originCube` — a translated origin cube has
  volume `(3^n)^d`.
* `volume_toReal_wellPlacedCore_le_three_pow_mul_truncatedWindow` — the ratio.
* `normalizedSetAverage_le_mul_of_subset` — the general covering inequality for a
  nonnegative integrand.
* `normalizedSetAverage_truncatedWindow_le_three_pow_mul_wellPlacedCore` — the
  covering step, in the anchor's own frame.

## What is not done here

The covering is proved for *normalized set averages* of a nonnegative
integrand, which is the shape of every quantity on the right of the printed
display (`localizedCoeffEnergyValue` is such an average of the coefficient
energy density, `normalizedL2SqOnSet` of a square).

## References

* ABK26, ("after a simple covering argument").
* CoarseGraining, `Geometry/CubeMeasure.lean`, `Geometry/Translation.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The inscribed cube -/

/-- A clamped centre moves by less than half a side. -/
private theorem wellPlacedCentre_sub_bound {m k : ℤ} (hkm : k ≤ m) {x : Vec d}
    (i : Fin d) (hx1 : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < x i)
    (hx2 : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    -((1 / 2 : ℝ) * (3 : ℝ) ^ k) < wellPlacedCentre x m k i - x i ∧
      wellPlacedCentre x m k i - x i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hA : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hAdef : wellPlacedHalfGap m k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  rcases le_total (x i) (-wellPlacedHalfGap m k) with h1 | h1
  · have hc : wellPlacedCentre x m k i = -wellPlacedHalfGap m k := by
      rw [wellPlacedCentre, min_eq_right (h1.trans (by linarith only [hA]))]
      exact max_eq_left h1
    have h1u : x i ≤ -((1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k) := by
      rw [← hAdef]
      exact h1
    rw [hc, hAdef]
    exact ⟨by linarith only [h1u, hkpos], by linarith only [hx1]⟩
  · rcases le_total (x i) (wellPlacedHalfGap m k) with h2 | h2
    · have hc : wellPlacedCentre x m k i = x i := by
        rw [wellPlacedCentre, min_eq_right h2]
        exact max_eq_right h1
      rw [hc]
      exact ⟨by linarith only [hkpos], by linarith only [hkpos]⟩
    · have hc : wellPlacedCentre x m k i = wellPlacedHalfGap m k := by
        rw [wellPlacedCentre, min_eq_left h2]
        exact max_eq_right (by linarith only [h2, hA])
      have h2u : (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ x i := by
        rw [← hAdef]
        exact h2
      rw [hc, hAdef]
      exact ⟨by linarith only [hx2], by linarith only [h2u, hkpos]⟩

/-- **The inscribed cube.**  The well-placed cube of side `3^{j-1}` sits inside
the truncated window `(x+□_j) ∩ □_m`: it stays in `□_m` by construction, and its
centre is within `3^{j-1}/2` of `x`, so the whole cube is within `3^{j-1}` of
`x`, which is less than the half-side `3^j/2`. -/
theorem image_add_wellPlacedCentre_subset_truncatedWindow {m j : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hjm : j - 1 ≤ m) :
    (fun y => wellPlacedCentre x m (j - 1) + y) ''
        openCubeSet (originCube d (j - 1)) ⊆ truncatedWindow x m j := by
  intro p hp
  have hdomain : p ∈ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet x hjm hp
  refine ⟨?_, hdomain⟩
  rw [mem_image_add_iff] at hp ⊢
  rw [mem_openCubeSet_originCube_iff] at hp hx ⊢
  intro i
  have hstep : (3 : ℝ) ^ (j - 1) * 3 = (3 : ℝ) ^ j := by
    rw [show j = j - 1 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
  have hcx := wellPlacedCentre_sub_bound (k := j - 1) hjm i (hx i).1 (hx i).2
  have hi := hp i
  simp only [Pi.sub_apply] at hi ⊢
  constructor
  · linarith only [hi.1, hcx.1, hstep, hpos]
  · linarith only [hi.2, hcx.2, hstep, hpos]

/-! ## 2. Volumes of translated origin cubes -/

theorem image_add_eq_preimage (c : Vec d) (S : Set (Vec d)) :
    (fun y => c + y) '' S = (fun y => -c + y) ⁻¹' S := by
  ext p
  rw [mem_image_add_iff, Set.mem_preimage]
  have hp : -c + p = p - c := by abel
  rw [hp]

theorem volume_image_add (c : Vec d) (S : Set (Vec d)) :
    volume ((fun y => c + y) '' S) = volume S := by
  rw [image_add_eq_translateSet, volume_translateSet_eq]

theorem volume_openCubeSet_originCube_ne_top (d : ℕ) (n : ℤ) :
    volume (openCubeSet (originCube d n)) ≠ ⊤ :=
  ne_of_lt (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).volume_lt_top

theorem volume_toReal_openCubeSet_originCube (d : ℕ) (n : ℤ) :
    (volume (openCubeSet (originCube d n))).toReal = ((3 : ℝ) ^ n) ^ d := by
  rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal,
    cubeVolume_eq_pow_scale, scale_originCube]

/-! ## 3. The volume ratio -/

/-- **The covering ratio.**  The translated Caccioppoli core is at most `3^d`
times the anchor's window in volume. -/
theorem volume_toReal_wellPlacedCore_le_three_pow_mul_truncatedWindow {m k : ℤ}
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    (volume ((fun y => wellPlacedCentre x m k + y) ''
        caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k))).toReal ≤
      (3 : ℝ) ^ d * (volume (truncatedWindow x m (k - 2))).toReal := by
  have hkm3 : k - 3 ≤ m := by linarith only [hkm]
  have hcore_le : volume ((fun y => wellPlacedCentre x m k + y) ''
      caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k)) ≤
      volume (openCubeSet (originCube d (k - 2))) := by
    rw [volume_image_add]
    have hsub : caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k) ⊆
        openCubeAtScale (x - wellPlacedCentre x m k) ((originCube d k).scale - 2) :=
      fun y hy => hy.2
    have heq : volume (openCubeAtScale (x - wellPlacedCentre x m k)
        ((originCube d k).scale - 2)) =
        volume (openCubeSet (originCube d (k - 2))) := by
      rw [scale_originCube, openCubeAtScale_eq_image_add, volume_image_add]
    exact le_trans (measure_mono hsub) (le_of_eq heq)
  have hwin_ge : volume ((fun y => wellPlacedCentre x m (k - 3) + y) ''
      openCubeSet (originCube d (k - 3))) ≤ volume (truncatedWindow x m (k - 2)) := by
    refine measure_mono ?_
    have h := image_add_wellPlacedCentre_subset_truncatedWindow (j := k - 2) x hx
      (by linarith only [hkm] : k - 2 - 1 ≤ m)
    have hje : k - 2 - 1 = k - 3 := by ring
    rwa [hje] at h
  have hwin_top : volume (truncatedWindow x m (k - 2)) ≠ ⊤ :=
    ne_of_lt (volume_truncatedWindow_lt_top x m (k - 2))
  have hcore_real : (volume ((fun y => wellPlacedCentre x m k + y) ''
      caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k))).toReal ≤
      ((3 : ℝ) ^ (k - 2)) ^ d := by
    rw [← volume_toReal_openCubeSet_originCube d (k - 2)]
    exact ENNReal.toReal_mono (volume_openCubeSet_originCube_ne_top d (k - 2)) hcore_le
  have hwin_real : ((3 : ℝ) ^ (k - 3)) ^ d ≤ (volume (truncatedWindow x m (k - 2))).toReal := by
    rw [← volume_toReal_openCubeSet_originCube d (k - 3),
      ← volume_image_add (wellPlacedCentre x m (k - 3)) (openCubeSet (originCube d (k - 3)))]
    exact ENNReal.toReal_mono hwin_top hwin_ge
  have hsplit : ((3 : ℝ) ^ (k - 2)) ^ d = (3 : ℝ) ^ d * ((3 : ℝ) ^ (k - 3)) ^ d := by
    have h3 : (3 : ℝ) ^ (k - 2) = 3 * (3 : ℝ) ^ (k - 3) := by
      rw [show k - 2 = k - 3 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    rw [h3, mul_pow]
  have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  calc
    (volume ((fun y => wellPlacedCentre x m k + y) ''
        caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k))).toReal
        ≤ ((3 : ℝ) ^ (k - 2)) ^ d := hcore_real
    _ = (3 : ℝ) ^ d * ((3 : ℝ) ^ (k - 3)) ^ d := hsplit
    _ ≤ (3 : ℝ) ^ d * (volume (truncatedWindow x m (k - 2))).toReal :=
        mul_le_mul_of_nonneg_left hwin_real h3d

/-! ## 4. The covering inequality -/

/-- **The covering inequality.**  A normalized average over a subset is bounded by
the volume ratio times the normalized average over the ambient set, for a
nonnegative integrable integrand.  This is CoarseGraining's `18^d` argument
abstracted from its geometry. -/
theorem normalizedSetAverage_le_mul_of_subset {S T : Set (Vec d)} {f : Vec d → ℝ}
    {K : ℝ} (hST : S ⊆ T) (hSpos : 0 < volume S) (hTtop : volume T < ⊤)
    (hTmeas : MeasurableSet T) (hf : ∀ y ∈ T, 0 ≤ f y)
    (hint : IntegrableOn f T volume)
    (hK : (volume T).toReal ≤ K * (volume S).toReal) :
    normalizedSetAverage S f ≤ K * normalizedSetAverage T f := by
  have hSle : volume S ≤ volume T := measure_mono hST
  have hSreal : 0 < (volume S).toReal :=
    ENNReal.toReal_pos (ne_of_gt hSpos) (ne_of_lt (lt_of_le_of_lt hSle hTtop))
  have hTreal : 0 < (volume T).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hSpos hSle)) (ne_of_lt hTtop)
  have hTne : (volume T).toReal ≠ 0 := ne_of_gt hTreal
  have hnonneg_pt : ∀ᵐ y ∂(volume.restrict T), 0 ≤ f y := by
    rw [MeasureTheory.ae_restrict_iff' hTmeas]
    exact Filter.Eventually.of_forall hf
  have hnonneg_ae : 0 ≤ᵐ[volume.restrict T] f := hnonneg_pt
  have hraw : ∫ y in S, f y ∂volume ≤ ∫ y in T, f y ∂volume :=
    MeasureTheory.setIntegral_mono_set hint hnonneg_ae
      (Filter.Eventually.of_forall hST)
  have hIT : 0 ≤ ∫ y in T, f y ∂volume :=
    MeasureTheory.integral_nonneg_of_ae hnonneg_ae
  have hratio : (volume S).toReal⁻¹ * (volume T).toReal ≤ K := by
    have h := mul_le_mul_of_nonneg_left hK (le_of_lt (inv_pos.2 hSreal))
    have he : (volume S).toReal⁻¹ * (K * (volume S).toReal) = K := by
      field_simp
    rwa [he] at h
  have hTavg : 0 ≤ (volume T).toReal⁻¹ * ∫ y in T, f y ∂volume :=
    mul_nonneg (le_of_lt (inv_pos.2 hTreal)) hIT
  unfold normalizedSetAverage volumeAverage
  calc
    (volume S).toReal⁻¹ * ∫ y in S, f y ∂volume
        ≤ (volume S).toReal⁻¹ * ∫ y in T, f y ∂volume :=
          mul_le_mul_of_nonneg_left hraw (le_of_lt (inv_pos.2 hSreal))
    _ = ((volume S).toReal⁻¹ * (volume T).toReal) *
          ((volume T).toReal⁻¹ * ∫ y in T, f y ∂volume) := by
          field_simp
    _ ≤ K * ((volume T).toReal⁻¹ * ∫ y in T, f y ∂volume) :=
          mul_le_mul_of_nonneg_right hratio hTavg

/-! ## 5. The covering step of the boundary lane -/

theorem isOpen_image_add_caccioppoliCoreSet (c : Vec d) (Q : TriadicCube d)
    (w : Vec d) : IsOpen ((fun y => c + y) '' caccioppoliCoreSet Q w) := by
  rw [image_add_eq_preimage]
  refine IsOpen.preimage (continuous_const.add continuous_id) ?_
  exact (isOpen_openCubeSet Q).inter (isOpen_openCubeAtScale w (Q.scale - 2))

/-- **The covering step.**

The normalized average of a nonnegative integrand over the anchor's window
`(x+□_{k-2}) ∩ □_m` is at most `3^d` times its normalized average over the
translated Caccioppoli core of the well-placed cube — the set on which
CoarseGraining's boundary Caccioppoli inequality delivers an estimate.  With
the integrand the coefficient energy density this is exactly the printed
covering conversion. -/
theorem normalizedSetAverage_truncatedWindow_le_three_pow_mul_wellPlacedCore
    {m k : ℤ} {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m)
    {f : Vec d → ℝ}
    (hf : ∀ y ∈ (fun y => wellPlacedCentre x m k + y) ''
      caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k), 0 ≤ f y)
    (hint : IntegrableOn f ((fun y => wellPlacedCentre x m k + y) ''
      caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k)) volume) :
    normalizedSetAverage (truncatedWindow x m (k - 2)) f ≤
      (3 : ℝ) ^ d * normalizedSetAverage ((fun y => wellPlacedCentre x m k + y) ''
        caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k)) f := by
  refine normalizedSetAverage_le_mul_of_subset
    (truncatedWindow_subset_image_add_caccioppoliCoreSet x hkm le_rfl)
    (volume_truncatedWindow_pos (k - 2) hx) ?_
    (isOpen_image_add_caccioppoliCoreSet _ _ _).measurableSet hf hint
    (volume_toReal_wellPlacedCore_le_three_pow_mul_truncatedWindow hx hkm)
  rw [volume_image_add]
  refine lt_of_le_of_lt (measure_mono (fun y hy => hy.1)) ?_
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).volume_lt_top

end

end Algsuperdiff.Section4.Provider.ExcessDecay
