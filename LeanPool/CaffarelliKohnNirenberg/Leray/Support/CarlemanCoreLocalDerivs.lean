/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreConjugation
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Local smoothness of space-time coordinate derivatives

The phase in `prop:carleman-halfspace` of the Escauriaza–Seregin–Šverák
manuscript is smooth only on its open cylinder.
These facts keep its coordinate derivatives smooth on that same cylinder.
-/

public section

open MeasureTheory CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace CKN

/-- The product normed additive group structure used for local derivative estimates. -/
local instance carlemanCoreLocalDerivsNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

/-- The real product normed-space structure used for local derivative estimates. -/
local instance carlemanCoreLocalDerivsNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- Spatial differentiation preserves smoothness on an open set. -/
theorem contDiffOn_spatialPartial
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => spatialPartial φ i z) U := by
  apply hU.contDiffOn_iff.mpr
  intro z hz
  let F : ParabolicPoint → Vec3 → ℝ := fun q x => φ (x, q.2)
  have hmap : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ParabolicPoint × Vec3 => ((q.2, q.1.2) : ParabolicPoint))
      (z, z.1) := by fun_prop
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry F) (z, z.1) :=
    (hφ.contDiffAt (hU.mem_nhds hz)).comp (z, z.1) hmap
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ParabolicPoint => q.1) z :=
    by fun_prop
  have hderiv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (F q) q.1) z :=
    hF.fderiv hg (by simp)
  have hval : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (F q) q.1 (basisVec i)) z :=
    hderiv.clm_apply (contDiffAt_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
  exact hval

/-- Time differentiation preserves smoothness on an open set. -/
theorem contDiffOn_timePartial
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => timePartial φ z) U := by
  apply hU.contDiffOn_iff.mpr
  intro z hz
  let F : ParabolicPoint → ℝ → ℝ := fun q t => φ (q.1, t)
  have hmap : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ParabolicPoint × ℝ => ((q.1.1, q.2) : ParabolicPoint))
      (z, z.2) := by fun_prop
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry F) (z, z.2) :=
    (hφ.contDiffAt (hU.mem_nhds hz)).comp (z, z.2) hmap
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ParabolicPoint => q.2) z :=
    by fun_prop
  have hderiv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (F q) q.2) z :=
    hF.fderiv hg (by simp)
  have hval : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (F q) q.2 1) z :=
    hderiv.clm_apply (contDiffAt_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
  exact hval

/-- A local smooth coefficient times a smooth field supported in its domain
extends smoothly by zero to the whole ordinary space-time product. -/
theorem contDiff_mul_of_tsupport
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f w : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwU : tsupport w ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => f z * w z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact (hf.contDiffAt (hU.mem_nhds hz)).mul hw.contDiffAt
  · have hzs : z ∉ tsupport w := fun h => hz (hwU h)
    have hnhds : (tsupport w)ᶜ ∈ 𝓝 z :=
      (isClosed_tsupport w).isOpen_compl.mem_nhds hzs
    have heq : (fun y => f y * w y) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hnhds] with y hy
      have hwy : w y = 0 := by
        by_contra hne
        exact hy (subset_tsupport w hne)
      simp only [hwy, mul_zero]
    exact (contDiffAt_const (𝕜 := ℝ) (c := (0 : ℝ))).congr_of_eventuallyEq heq

/-- A compactly supported product of a local smooth coefficient and a smooth
field is integrable on space-time. -/
theorem integrable_mul_of_tsupport
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f w : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    MeasureTheory.Integrable (fun z : Vec3 × ℝ => f z * w z) MeasureTheory.volume := by
  have hcont : Continuous (fun z : Vec3 × ℝ => f z * w z) :=
    (contDiff_mul_of_tsupport hU hf hw hwU).continuous
  have hcompact : HasCompactSupport (fun z : Vec3 × ℝ => f z * w z) :=
    hwc.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The scalar squared gradient of a smooth phase is smooth on its domain. -/
theorem contDiffOn_scalarGradSq
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (scalarGradSq f) U := by
  unfold scalarGradSq
  exact ContDiffOn.sum (fun i _ => (contDiffOn_spatialPartial hU hf i).pow 2)

/-- The scalar spatial Laplacian of a smooth phase is smooth on its domain. -/
theorem contDiffOn_scalarLaplacian
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (scalarLaplacian f) U := by
  unfold scalarLaplacian
  exact ContDiffOn.sum (fun i _ =>
    contDiffOn_spatialPartial hU (contDiffOn_spatialPartial hU hf i) i)

/-- The expanded conjugated heat operator is smooth where the phase is smooth. -/
theorem contDiffOn_carlemanConj
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiffOn ℝ (⊤ : ℕ∞) (carlemanConj φ v) U := by
  have htv := contDiffOn_timePartial hU hv.contDiffOn
  have hLv := contDiffOn_scalarLaplacian hU hv.contDiffOn
  have hgv := contDiffOn_scalarGradSq hU hφ
  have htφ := contDiffOn_timePartial hU hφ
  have hLφ := contDiffOn_scalarLaplacian hU hφ
  have hdrift : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∑ i, spatialPartial φ i z * spatialPartial v i z) U := by
    exact ContDiffOn.sum (fun i _ =>
      (contDiffOn_spatialPartial hU hφ i).mul
        (contDiffOn_spatialPartial hU hv.contDiffOn i))
  unfold carlemanConj
  exact ((htv.add hLv).sub ((contDiffOn_const.mul hdrift))).add
    (((hgv.sub htφ).sub hLφ).mul hv.contDiffOn)

end CKN
