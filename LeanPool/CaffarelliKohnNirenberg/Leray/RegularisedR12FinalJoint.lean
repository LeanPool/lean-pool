/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Joint continuous differentiability from continuous partial derivatives

A space-time field whose spatial slices are differentiable, whose coordinate
spatial partial derivatives are continuous, and whose time derivative exists
and is continuous on `ℝ³ × (0,∞)` is continuously differentiable there as a
function of the space-time point. This gives the joint `C¹` clause of
`thm:regularised` (R2).
-/

public section

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- A linear functional on Vec3 is the sum of its values on the coordinate
basis times the coordinate projections. -/
private theorem regR12Joint_clm_eq_sum (L : Vec3 →L[ℝ] ℝ) :
    L = ∑ j : Fin 3, L (basisVec j) • ContinuousLinearMap.proj j := by
  ext x
  rw [sum_apply]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hx : x = ∑ j : Fin 3, x j • basisVec j := by
    funext i
    simp [basisVec, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- `thm:regularised` (R2), joint `C¹`: continuous spatial partial
derivatives and a continuous time derivative give joint continuous
differentiability on `ℝ³ × (0,∞)`. -/
theorem regR12_contDiffOn_one_of_partials
    (f : ParabolicPoint → ℝ) (g : ParabolicPoint → ℝ)
    (hdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => f (x, z.2)) z.1)
    (hD : ∀ j : Fin 3, ContinuousOn (fun z => spatialPartial f j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (ht : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      HasDerivAt (fun s : ℝ => f (z.1, s)) (g z) z.2)
    (hg : ContinuousOn g (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) :
    letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
    letI : NormedAddCommGroup ParabolicPoint :=
      inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
    letI : NormedSpace ℝ ParabolicPoint :=
      inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
    ContDiffOn ℝ 1 f (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ Ioi 0
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioi
  let F : Vec3 × ℝ → ℝ := fun z => f z
  have hDprod : ∀ j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial f j ((z.1, z.2) : ParabolicPoint)) S :=
    fun j => regUniform_continuousOn_pullback (hD j) (fun z hz => hz)
  have hgprod : ContinuousOn (fun z : Vec3 × ℝ => g ((z.1, z.2) : ParabolicPoint)) S :=
    regUniform_continuousOn_pullback hg (fun z hz => hz)
  -- the partial derivatives as continuous linear maps
  let f₁ : Vec3 → ℝ → Vec3 →L[ℝ] ℝ := fun x t =>
    ∑ j : Fin 3, spatialPartial f j ((x, t) : ParabolicPoint) • ContinuousLinearMap.proj j
  let f₂ : Vec3 → ℝ → ℝ →L[ℝ] ℝ := fun x t =>
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g ((x, t) : ParabolicPoint))
  have hf₁ : ∀ v ∈ S, HasFDerivAt (fun x : Vec3 => F (x, v.2)) (f₁ v.1 v.2) v.1 := by
    intro v hv
    have hd := (hdiff ((v.1, v.2) : ParabolicPoint) hv).hasFDerivAt
    have heq : fderiv ℝ (fun x : Vec3 => f (x, v.2)) v.1 = f₁ v.1 v.2 := by
      rw [regR12Joint_clm_eq_sum (fderiv ℝ (fun x : Vec3 => f (x, v.2)) v.1)]
      rfl
    rw [heq] at hd
    exact hd
  have hf₂ : ∀ v ∈ S, HasFDerivAt (fun s : ℝ => F (v.1, s)) (f₂ v.1 v.2) v.2 := by
    intro v hv
    exact (ht ((v.1, v.2) : ParabolicPoint) hv).hasFDerivAt
  have hcf₁ : ContinuousOn (fun v : Vec3 × ℝ => f₁ v.1 v.2) S := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact (hDprod j).smul continuousOn_const
  have hcf₂ : ContinuousOn (fun v : Vec3 × ℝ => f₂ v.1 v.2) S :=
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp_continuousOn
      hgprod)
  have hstrict : ∀ u ∈ S,
      HasFDerivAt F ((f₁ u.1 u.2).coprod (f₂ u.1 u.2)) u := by
    intro u hu
    have hnhds : S ∈ 𝓝 u := hSopen.mem_nhds hu
    have h := hasStrictFDerivAt_uncurry_coprod (u := u) (f := fun x t => F (x, t))
      (f₁ := f₁) (f₂ := f₂)
      (Filter.eventually_of_mem hnhds fun v hv => hf₁ v hv)
      (Filter.eventually_of_mem hnhds fun v hv => hf₂ v hv)
      ((hcf₁.continuousAt hnhds))
      ((hcf₂.continuousAt hnhds))
    exact h.hasFDerivAt
  have hC1 : ContDiffOn ℝ 1 F S := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hSopen]
    refine ⟨fun u hu => (hstrict u hu).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_zero]
    have hcoprod : Continuous (fun p : (Vec3 →L[ℝ] ℝ) × (ℝ →L[ℝ] ℝ) => p.1.coprod p.2) :=
      (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (S := ℝ) (E := Vec3) (F := ℝ)
        (G := ℝ)).continuous
    have hpair : ContinuousOn (fun u : Vec3 × ℝ => (f₁ u.1 u.2, f₂ u.1 u.2)) S :=
      hcf₁.prodMk hcf₂
    have hcont := hcoprod.comp_continuousOn hpair
    refine hcont.congr fun u hu => ?_
    rw [(hstrict u hu).fderiv]
    rfl
  exact hC1

end CKN.Leray
