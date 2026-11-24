/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Plurisubharmonic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Complex affine pullback of plurisubharmonic functions

A complex continuous linear affine map sends each parametrized closed disc
to the corresponding parametrized closed disc, with the same angular
parameter. Thus its pullback preserves the actual nonnegative circle-deficit
integrals. No general holomorphic pullback theorem is assumed here.
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The actual image of a closed affine complex disc under an affine map. -/
theorem image_affineClosedDisc (L : E →L[ℂ] F) (b : F) (x v : E) (r : ℝ) :
    (fun y => b + L y) '' affineClosedDisc x v r =
      affineClosedDisc (b + L x) (L v) r := by
  unfold affineClosedDisc
  rw [image_image]
  congr 1
  funext z
  simp only [map_add, map_smul, add_assoc]

/-- The angular deficit integral is exactly preserved by affine pullback,
including infinite deficit values at poles. -/
theorem circleDeficit_comp_affine (u : F → EReal) (L : E →L[ℂ] F) (b : F)
    (x v : E) (r C : ℝ) :
    circleDeficit (fun y => u (b + L y)) x v r C =
      circleDeficit u (b + L x) (L v) r C := by
  simp only [circleDeficit, map_add, map_smul, add_assoc]

theorem HasDiscSubmeanOn.comp_affine {u : F → EReal} {U : Set F}
    (hu : HasDiscSubmeanOn u U) (L : E →L[ℂ] F) (b : F) :
    HasDiscSubmeanOn (fun y => u (b + L y)) ((fun y => b + L y) ⁻¹' U) := by
  intro x v r hr hD C hC
  have hDU : affineClosedDisc (b + L x) (L v) r ⊆ U := by
    rw [← image_affineClosedDisc L b]
    rintro _ ⟨y, hy, rfl⟩
    exact hD hy
  have hbound : ∀ z ∈ affineClosedDisc (b + L x) (L v) r, u z ≤ (C : EReal) := by
    rw [← image_affineClosedDisc L b]
    rintro _ ⟨y, hy, rfl⟩
    exact hC y hy
  rw [circleDeficit_comp_affine]
  exact hu (b + L x) (L v) r hr hDU C hbound

/-- The full disc criterion is stable under arbitrary complex continuous
linear affine pullback. Injectivity and surjectivity are not required. -/
theorem DiscPshOn.comp_affine {u : F → EReal} {U : Set F}
    (hu : DiscPshOn u U) (L : E →L[ℂ] F) (b : F) :
    DiscPshOn (fun y => u (b + L y)) ((fun y => b + L y) ⁻¹' U) := by
  refine ⟨fun y hy => hu.ne_top (b + L y) hy, ?_, hu.submean.comp_affine L b⟩
  exact hu.upperSemicontinuousOn.comp
    (continuous_const.add L.continuous).continuousOn (fun _ hy => hy)

theorem PlurisubharmonicAt.comp_affine (L : E →L[ℂ] F) (b : F)
    {u : F → EReal} {x : E} (hu : PlurisubharmonicAt u (b + L x)) :
    PlurisubharmonicAt (fun y => u (b + L y)) x := by
  obtain ⟨U, hU, hx, hu⟩ := hu
  exact ⟨(fun y => b + L y) ⁻¹' U,
    hU.preimage (continuous_const.add L.continuous), hx, hu.comp_affine L b⟩

theorem PlurisubharmonicOn.comp_affine {u : F → EReal} {U : Set F}
    (hu : PlurisubharmonicOn u U) (L : E →L[ℂ] F) (b : F) :
    PlurisubharmonicOn (fun y => u (b + L y)) ((fun y => b + L y) ⁻¹' U) := by
  intro x hx
  exact PlurisubharmonicAt.comp_affine L b (hu (b + L x) hx)

theorem DiscPshOn.comp_continuousLinearMap {u : F → EReal} {U : Set F}
    (hu : DiscPshOn u U) (L : E →L[ℂ] F) :
    DiscPshOn (fun y => u (L y)) (L ⁻¹' U) := by
  simpa only [zero_add] using hu.comp_affine L 0

theorem PlurisubharmonicAt.comp_continuousLinearMap (L : E →L[ℂ] F)
    {u : F → EReal} {x : E} (hu : PlurisubharmonicAt u (L x)) :
    PlurisubharmonicAt (fun y => u (L y)) x := by
  have h : PlurisubharmonicAt u (0 + L x) := by simpa only [zero_add] using hu
  simpa only [zero_add] using PlurisubharmonicAt.comp_affine L 0 h

theorem PlurisubharmonicOn.comp_continuousLinearMap {u : F → EReal} {U : Set F}
    (hu : PlurisubharmonicOn u U) (L : E →L[ℂ] F) :
    PlurisubharmonicOn (fun y => u (L y)) (L ⁻¹' U) := by
  simpa only [zero_add] using hu.comp_affine L 0

/-- Restriction to a complex linear subspace preserves the disc criterion;
the subspace need not be closed. -/
theorem DiscPshOn.submodule {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (S : Submodule ℂ E) :
    DiscPshOn (fun y : S => u y) ((fun y : S => (y : E)) ⁻¹' U) := by
  simpa only [Submodule.coe_subtypeL, Submodule.coe_subtype] using!
    hu.comp_continuousLinearMap S.subtypeL

theorem PlurisubharmonicAt.submodule {u : E → EReal} (S : Submodule ℂ E)
    {x : S} (hu : PlurisubharmonicAt u (x : E)) :
    PlurisubharmonicAt (fun y : S => u y) x := by
  exact PlurisubharmonicAt.comp_continuousLinearMap S.subtypeL hu

theorem PlurisubharmonicOn.submodule {u : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) (S : Submodule ℂ E) :
    PlurisubharmonicOn (fun y : S => u y) ((fun y : S => (y : E)) ⁻¹' U) := by
  simpa only [Submodule.coe_subtypeL, Submodule.coe_subtype] using!
    hu.comp_continuousLinearMap S.subtypeL

end SGPT.Foundations.Analysis
