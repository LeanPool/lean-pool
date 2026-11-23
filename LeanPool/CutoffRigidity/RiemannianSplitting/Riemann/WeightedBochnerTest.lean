/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedGradientRegularity
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame

/-! # G2: test functions with prescribed gradient and vanishing Hessian at a point

`exists_test_function`: for `v ∈ T_xM` there is a globally smooth `g` with `∇g(x) = v` and
`Hess g(x) = 0`: in the chart at `x`, `g̃(z) = ξ(z-z₀) + ½ ξ(Γ(z-z₀,z-z₀))` (`Γ` the Christoffel map
at the centre, `ξ = ⟪v,·⟫`), cut off by a smooth bump function.
-/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology

namespace CutCur.WBoch
open CutoffRigidity
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- chart derivative at the centre equals the intrinsic differential. -/
private theorem fderiv_comp_symm_center {f : M → ℝ} (x : M)
    (v : F) :
    fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, F) x).symm) (extChartAt 𝓘(ℝ, F) x x) v =
      mvfderiv 𝓘(ℝ, F) f x v := by
  rw [← TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm]
  rfl

/-- The Christoffel map in the canonical frame at the chart centre. -/
private noncomputable def gamCLM (x : M) : F →L[ℝ] F →L[ℝ] F :=
  TauCeti.Manifold.christoffelMap (Module.finBasis ℝ F)
    ((CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn
      (s := (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet)) x

private theorem gamCLM_symm (x : M) (a b : F) : gamCLM x a b = gamCLM x b a := by
  let : IsManifold 𝓘(ℝ, F) (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold 𝓘(ℝ, F) 2 M)
  have torsionFree : (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).IsTorsionFree :=
    (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero _).2
      (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, F))
  exact TauCeti.Manifold.christoffelMap_comm (I := 𝓘(ℝ, F))
    torsionFree (Module.finBasis ℝ F) x (mem_extChartAt_source x) a b

/-- the quadratic test polynomial in chart coordinates -/
private noncomputable def gt (x : M) (ξ : F →L[ℝ] ℝ) (z : F) : ℝ :=
  ξ (z - extChartAt 𝓘(ℝ, F) x x) +
    (1 / 2) * ξ (gamCLM x (z - extChartAt 𝓘(ℝ, F) x x) (z - extChartAt 𝓘(ℝ, F) x x))

private theorem contDiff_gt (x : M) (ξ : F →L[ℝ] ℝ) : ContDiff ℝ ∞ (gt x ξ) := by
  unfold gt
  fun_prop

private theorem hasFDerivAt_gt (x : M) (ξ : F →L[ℝ] ℝ) (z : F) :
    HasFDerivAt (gt x ξ) (ξ + (1 / 2 : ℝ) • (ξ.comp (gamCLM x (z - extChartAt 𝓘(ℝ, F) x x) +
      (gamCLM x).flip (z - extChartAt 𝓘(ℝ, F) x x)))) z := by
  have h1 : HasFDerivAt (fun z : F => z - extChartAt 𝓘(ℝ, F) x x) (ContinuousLinearMap.id ℝ F) z :=
    (hasFDerivAt_id z).sub_const _
  have h2 := ((gamCLM x).hasFDerivAt.comp z h1).clm_apply h1
  have h3 := (ξ.hasFDerivAt.comp z h1).add (((ξ.hasFDerivAt.comp z h2).const_mul (1 / 2 : ℝ)))
  refine HasFDerivAt.congr_fderiv (f' := _) (by exact h3) ?_
  ext w
  simp


private theorem fderiv_gt_center (x : M) (ξ : F →L[ℝ] ℝ) :
    fderiv ℝ (gt x ξ) (extChartAt 𝓘(ℝ, F) x x) = ξ := by
  rw [(hasFDerivAt_gt x ξ _).fderiv]
  simp

private theorem mvfderiv_eq_xi {G : M → ℝ} (x : M) (ξ : F →L[ℝ] ℝ)
    (hG : (G ∘ (extChartAt 𝓘(ℝ, F) x).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, F) x x)] gt x ξ) (w : F) :
    mvfderiv 𝓘(ℝ, F) G x w = ξ w := by
  rw [← fderiv_comp_symm_center x w, hG.fderiv_eq, fderiv_gt_center]


/-- first derivative of `gt` in the direction `w`, as an explicit affine function -/
private noncomputable def Kfun (x : M) (ξ : F →L[ℝ] ℝ) (w : F) (z : F) : ℝ :=
  ξ w + (1 / 2) * ξ ((gamCLM x).flip w (z - extChartAt 𝓘(ℝ, F) x x) +
    gamCLM x w (z - extChartAt 𝓘(ℝ, F) x x))

private theorem fderiv_gt_apply (x : M) (ξ : F →L[ℝ] ℝ) (w z : F) :
    fderiv ℝ (gt x ξ) z w = Kfun x ξ w z := by
  rw [(hasFDerivAt_gt x ξ z).fderiv]
  simp only [Kfun, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]

private theorem hasFDerivAt_Kfun (x : M) (ξ : F →L[ℝ] ℝ) (w z : F) :
    HasFDerivAt (Kfun x ξ w)
      ((1 / 2 : ℝ) • ξ.comp ((gamCLM x).flip w + gamCLM x w)) z := by
  have h1 : HasFDerivAt (fun z : F => z - extChartAt 𝓘(ℝ, F) x x) (ContinuousLinearMap.id ℝ F) z :=
    (hasFDerivAt_id z).sub_const _
  have h2 := (((gamCLM x).flip w + gamCLM x w).hasFDerivAt.comp z h1)
  have h3 := ((ξ.hasFDerivAt.comp z h2).const_mul (1 / 2 : ℝ)).const_add (ξ w)
  refine HasFDerivAt.congr_fderiv (f' := _) (by exact h3) ?_
  ext u
  simp

private theorem fderiv_Kfun_center (x : M) (ξ : F →L[ℝ] ℝ) (w a : F) :
    fderiv ℝ (Kfun x ξ w) (extChartAt 𝓘(ℝ, F) x x) a = ξ (gamCLM x a w) := by
  rw [(hasFDerivAt_Kfun x ξ w _).fderiv]
  simp [gamCLM_symm x w a]
  ring


private theorem hessian_zero_of_chart {G : M → ℝ} (x : M) (ξ : F →L[ℝ] ℝ)
    (hGs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ G)
    (hG : (G ∘ (extChartAt 𝓘(ℝ, F) x).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, F) x x)] gt x ξ)
    (a w : F) : CutoffRigidity.manifoldHessian 𝓘(ℝ, F) G x a w = 0 := by
  set e := extChartAt 𝓘(ℝ, F) x with he
  let : IsManifold 𝓘(ℝ, F) (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold 𝓘(ℝ, F) 2 M)
  let aT : TangentSpace 𝓘(ℝ, F) x := a
  let wT : TangentSpace 𝓘(ℝ, F) x := w
  let W (v : TangentSpace 𝓘(ℝ, F) x) := FiberBundle.extend F v
  have hEq : (fun y => mvfderiv 𝓘(ℝ, F) G y (W wT y)) =ᶠ[𝓝 x]
      (Kfun x ξ w ∘ e) := by
    refine (TauCeti.Manifold.mvfderiv_extend_eventuallyEq ((hGs x).of_le (by simp)) w).trans ?_
    filter_upwards [(continuousAt_extChartAt (I := 𝓘(ℝ, F)) x).eventually hG.eventuallyEq_nhds]
      with y hy
    change fderiv ℝ (G ∘ e.symm) (e y) w = Kfun x ξ w (e y)
    have derivative : fderiv ℝ (G ∘ e.symm) (e y) = fderiv ℝ (gt x ξ) (e y) := hy.fderiv_eq
    rw [derivative, fderiv_gt_apply]
  have hKe2 : (Kfun x ξ w ∘ e) ∘ e.symm =ᶠ[𝓝 (e x)] Kfun x ξ w := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, F)) x] with z hz
    simp [e.right_inv hz]
  have hB : mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) G y (W wT y)) x a =
      ξ (gamCLM x a w) := by
    rw [hEq.mvfderiv_eq, ← fderiv_comp_symm_center x a, hKe2.fderiv_eq]
    exact fderiv_Kfun_center x ξ w a
  have hW : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% (W wT)) x :=
    FiberBundle.mdifferentiableAt_extend 𝓘(ℝ, F) F wT
  have h := TauCeti.Manifold.hessian_apply_eq_mvfderiv_sub (I := 𝓘(ℝ, F))
    x ((hGs.of_le (by simp)) x) (W aT) (W wT) hW
  have hWa : W aT x = aT := FiberBundle.extend_apply_self F aT
  have hWw : W wT x = wT := FiberBundle.extend_apply_self F wT
  have hΓ : (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M) (W wT) x (W aT x) =
      gamCLM x a w := by
    rw [hWa]
    exact (TauCeti.Manifold.covariantDerivative_extend_eq_christoffelMap (I := 𝓘(ℝ, F))
      (cov := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M)
      (Module.finBasis ℝ F) aT wT).trans (gamCLM_symm x w a)
  rw [TauCeti.Manifold.hessian_def, hΓ] at h
  rw [hWa, hWw, hB] at h
  rw [mvfderiv_eq_xi x ξ hG, sub_self] at h
  exact h


variable (F) in
theorem exists_test_function (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    ∃ g : M → ℝ, MSmooth F g ∧ mgrad F g x = v ∧ mHessNormSq F g x = 0 := by
  obtain ⟨f⟩ : Nonempty (SmoothBumpFunction 𝓘(ℝ, F) x) := inferInstance
  let ξ : F →L[ℝ] ℝ := innerSL ℝ (E := TangentSpace 𝓘(ℝ, F) x) v
  let e := extChartAt 𝓘(ℝ, F) x
  let g : M → ℝ := fun y => f y * gt x ξ (e y)
  have hg : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y => gt x ξ (e y)) (chartAt F x).source :=
    (contDiff_gt x ξ).contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt (I := 𝓘(ℝ, F)))
  have hgs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g := by
    have := f.contMDiff_smul hg
    simpa [g, smul_eq_mul] using this
  have h1 : ∀ᶠ y in 𝓝 x, f y = 1 := f.eventuallyEq_one
  have h2 : ∀ᶠ z in 𝓝 (e x), f (e.symm z) = 1 := by
    have hc := (continuousAt_extChartAt_symm (I := 𝓘(ℝ, F)) x)
    have h1' : ∀ᶠ y in 𝓝 (e.symm (e x)), f y = 1 := by
      rw [extChartAt_to_inv]; exact h1
    exact hc.eventually h1'
  have hG : (g ∘ e.symm) =ᶠ[𝓝 (e x)] gt x ξ := by
    filter_upwards [h2, extChartAt_target_mem_nhds (I := 𝓘(ℝ, F)) x] with z hz1 hz2
    change f (e.symm z) * gt x ξ (e (e.symm z)) = gt x ξ z
    rw [e.right_inv hz2, hz1, one_mul]
  refine ⟨g, hgs, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro w
    rw [mgrad_inner F]
    exact mvfderiv_eq_xi x ξ hG w
  · have h0 : ∀ a w : TangentSpace 𝓘(ℝ, F) x, CutoffRigidity.manifoldHessian 𝓘(ℝ, F) g x a w = 0 :=
      fun a w => hessian_zero_of_chart x ξ hgs hG a w
    exact (CutoffRigidity.manifoldHessianNormSq_eq_zero_iff 𝓘(ℝ, F) g x).mpr
      ((CutoffRigidity.manifoldHessian_eq_zero_iff 𝓘(ℝ, F) g x).mp h0)

end CutCur.WBoch
