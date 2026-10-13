/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWindows

/-!
# OneStepTriangle

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The excess algebra of the one-step contraction

The two purely definitional children of `l.excess.decay.good.scales`:

* **The triangle assembly** needs `E(u,W) ≤ E(v,W) + |W|^{-1/d} ‖u-v‖_{L²(W)}`
  and the passage of `‖u-v‖` between two windows of the family at the
  volume-ratio cost.  Landed here as `affineExcess_sub_le_truncatedWindow` and
  `normalizedL2On_truncatedWindow_le`.
* **The oscillation-to-excess comparison** needs `3^{-n}‖u -
  (u)_{U_0}‖_{L²(U_0)} ≤ E(u,U_0) + C|∇ℓ_0|`.  Landed here as
  `oscillationScaled_truncatedWindow_le`, by composing the two proved sandwich
  comparisons of `SlopeStabilityEndpoints` / `IterationLemmaProviderGeometry`.

## Two disclosed deviations from the printed displays

1. **The subadditivity carrier.**  The tree's proved subadditivity
   (`BoundaryLaneExcess.affineExcessRaw_add_le`) is unusable from this module:
   `BoundaryLaneExcess` and `SandwichNondegeneracyAttainment` both declare
   `normalizedL2On_le_of_abs_le` in the same namespace, so they cannot be
   imported together, and the excess-geometry lane needs the latter.  The
   subadditivity is therefore re-proved here from Minkowski
   (`normalizedL2On_add_le`) under the disclosing name
   `affineExcessRaw_add_le_of_memLp`, with the affine `MemLp` slot explicit.
2. **The constant of the oscillation fold.**  ABK26 prints `3^{-n}‖u-(u)_{U_0}‖
   ≤ E(u,U_0) + C|∇ℓ_0|`, i.e. the constant on the slope only.  The proved
   endpoint comparison charges one constant to *both* summands: `osc ≤
   endpointConst d (1/9) · (E + |∇ℓ|)`.  That is weaker than print on the excess
   leg, and it is what is stated here.  (The printed constant already hides a
   window-geometry fact, not "the triangle inequality" alone.)
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. Affine competitors are square-integrable on a truncated window -/

theorem memLp_affineEval_truncatedWindow {m k : ℤ} (x : Vec d) (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict (truncatedWindow x m k)) := by
  refine memLp_affineEval_of_sandwich (zout := x + fun _ => -(1 / 2) * (3 : ℝ) ^ k)
    (Lout := (3 : ℝ) ^ k) (zpow_pos (by norm_num) k)
    (measurableSet_truncatedWindow x m k) ?_ c g
  refine subset_trans (truncatedWindow_subset_translate x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube, image_add_axisCube]

/-! ## 2. Subadditivity of the raw excess -/

/-- **Subadditivity of the raw excess**, re-proved from Minkowski with the affine
`MemLp` slot explicit (see deviation 1 in the module docstring). -/
theorem affineExcessRaw_add_le_of_memLp {W : Set (Vec d)} {u w : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict W)) (hw : MemLp w 2 (volume.restrict W))
    (haff : ∀ (c : ℝ) (g : Vec d), MemLp (affineEval c g) 2 (volume.restrict W)) :
    affineExcessRaw W (fun y => u y + w y) ≤ affineExcessRaw W u + normalizedL2On W w := by
  have hle : ∀ b ∈ affineDistSet W u,
      affineExcessRaw W (fun y => u y + w y) - normalizedL2On W w ≤ b := by
    rintro b ⟨⟨c, g⟩, rfl⟩
    have hmink := normalizedL2On_add_le (W := W)
      (f := fun y => u y - affineEval c g y) (g := w) (hu.sub (haff c g)) hw
    have hcongr : (fun y => (u y - affineEval c g y) + w y)
        = fun y => (u y + w y) - affineEval c g y := by
      funext y; ring
    rw [hcongr] at hmink
    have hproj := affineExcessRaw_le_affineDistOn W (fun y => u y + w y) c g
    have hdist : affineDistOn W (fun y => u y + w y) c g
        = normalizedL2On W fun y => (u y + w y) - affineEval c g y := rfl
    have hdistu : affineDistOn W u c g = normalizedL2On W fun y => u y - affineEval c g y := rfl
    rw [hdist] at hproj
    show affineExcessRaw W (fun y => u y + w y) - normalizedL2On W w ≤ affineDistOn W u c g
    rw [hdistu]
    linarith only [hproj, hmink]
  have hcinf := le_csInf (affineDistSet_nonempty W u) hle
  rw [← affineExcessRaw] at hcinf
  linarith only [hcinf]

/-! ## 3. The triangle step at the `|W|^{-1/d}` normalizer -/

/-- **The triangle assembly, the comparison step.**

`E(u,W) ≤ E(v,W) + 9·3^{-k}·‖u-v‖_{L²(W)}` on the truncated window
`W = (x+□_k) ∩ □_m`; the factor `9` is the aspect-`1/9` slack of the truncated
normalizer against the cube normalizer `3^{-k}`. -/
theorem affineExcess_sub_le_truncatedWindow (hd : d ≠ 0) {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m k)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m k))) :
    affineExcess (truncatedWindow x m k) u
      ≤ affineExcess (truncatedWindow x m k) v
        + 9 * (3 : ℝ) ^ (-k) * normalizedL2On (truncatedWindow x m k) (fun y => u y - v y) := by
  set W := truncatedWindow x m k with hWdef
  have hraw : affineExcessRaw W u
      ≤ affineExcessRaw W v + normalizedL2On W (fun y => u y - v y) := by
    have h := affineExcessRaw_add_le_of_memLp (W := W) (u := v) (w := fun y => u y - v y)
      hv (hu.sub hv) (fun c g => memLp_affineEval_truncatedWindow x c g)
    have hcongr : (fun y => v y + (u y - v y)) = u := by funext y; ring
    rwa [hcongr] at h
  obtain ⟨_, hnorm⟩ := rpow_volume_truncatedWindow_bounds hd x hx hkm
  have hnn : (0 : ℝ) ≤ ((volume W).toReal) ^ (-(d : ℝ)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hL2 : (0 : ℝ) ≤ normalizedL2On W (fun y => u y - v y) := normalizedL2On_nonneg _ _
  have hstep : ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W u
      ≤ ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W v
        + ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * normalizedL2On W (fun y => u y - v y) := by
    have := mul_le_mul_of_nonneg_left hraw hnn
    linarith only [this]
  have hlast : ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * normalizedL2On W (fun y => u y - v y)
      ≤ 9 * (3 : ℝ) ^ (-k) * normalizedL2On W (fun y => u y - v y) :=
    mul_le_mul_of_nonneg_right hnorm hL2
  show ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W u ≤ _
  have hEv : affineExcess W v = ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W v := rfl
  rw [hEv]
  linarith only [hstep, hlast]

/-! ## 4. The window transfer of the `L²` remainder -/

/-- **The volume-ratio transfer.**  Passing `‖f‖_{L²}` from the outer window `U_l`
down to the inner window `U_k` (`k ≤ l`) costs `(3^{l-k+2})^{d/2}`.  This is
the `3^{(d/2+1)k}` bookkeeping, with the `+2` coming from the truncated
window's own aspect ratio. -/
theorem normalizedL2On_truncatedWindow_le {m k l : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) (hlm : l - 1 ≤ m)
    (hkl : k ≤ l) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (truncatedWindow x m l))) :
    normalizedL2On (truncatedWindow x m k) f
      ≤ Real.sqrt (((3 : ℝ) ^ (l - k + 2)) ^ d) * normalizedL2On (truncatedWindow x m l) f := by
  have hsub : truncatedWindow x m k ⊆ truncatedWindow x m l := truncatedWindow_mono x m hkl
  have hW : 0 < (volume (truncatedWindow x m l)).toReal :=
    volume_toReal_truncatedWindow_pos x hx hlm
  have hW' : 0 < (volume (truncatedWindow x m k)).toReal :=
    volume_toReal_truncatedWindow_pos x hx hkm
  have hint : IntegrableOn (fun p => f p ^ 2) (truncatedWindow x m l) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  refine (normalizedL2On_le_of_subset hsub hW hW' hint).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (normalizedL2On_nonneg _ _)
  exact Real.sqrt_le_sqrt (volume_ratio_truncatedWindow_le x hx hkm hlm)

/-! ## 5. The oscillation-to-excess fold -/

/-- Existence of an affine minimizer on a truncated window (the source's `ℓ(u,W)`),
from the proved sandwich attainment. -/
theorem exists_isAffineMinimizer_truncatedWindow {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m k))) :
    ∃ (c : ℝ) (g : Vec d), IsAffineMinimizer (truncatedWindow x m k) u c g := by
  obtain ⟨zin, zout, hin, hout⟩ := exists_axisCube_sandwich_truncatedWindow x hx hkm
  exact exists_isAffineMinimizer_of_axisCubeSandwich (zpow_pos (by norm_num) (k - 2))
    (zpow_pos (by norm_num) k) (measurableSet_truncatedWindow x m k) hin hout u hu

end

end Algsuperdiff.Section4.Provider.ExcessDecay
