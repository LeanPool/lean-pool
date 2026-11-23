/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.BumpFunction
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedBochnerDefs
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldScalarChartDerivative
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartBrackets
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedGradientRegularity
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

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
theorem fderiv_comp_symm_center {f : M → ℝ} (x : M)
    (v : F) :
    fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, F) x).symm) (extChartAt 𝓘(ℝ, F) x x) v =
      mvfderiv 𝓘(ℝ, F) f x v := by
  rw [← TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm]
  rfl

/-- Christoffel map at the centre. -/
noncomputable def gam (x : M) (a b : F) : F :=
  CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (chartFrame (I := 𝓘(ℝ, F)) x b) x a


omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mdiffAt_chartFrame (x : M) (b : F) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% (chartFrame (I := 𝓘(ℝ, F)) x b)) x :=
  (contMDiffAt_chartFrame (I := 𝓘(ℝ, F)) x b).mdifferentiableAt one_ne_zero

theorem gam_add_right (x : M) (a b b' : F) : gam x a (b + b') = gam x a b + gam x a b' := by
  have h : chartFrame (I := 𝓘(ℝ, F)) x (b + b') =
      chartFrame (I := 𝓘(ℝ, F)) x b + chartFrame (I := 𝓘(ℝ, F)) x b' := by
    funext y
    simp [chartFrame]
  unfold gam
  rw [h, (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn.add (s :=
      Set.univ)
    (mdiffAt_chartFrame x b) (mdiffAt_chartFrame x b')]
  rfl

theorem gam_smul_right (x : M) (a b : F) (c : ℝ) : gam x a (c • b) = c • gam x a b := by
  have h : chartFrame (I := 𝓘(ℝ, F)) x (c • b) = c • chartFrame (I := 𝓘(ℝ, F)) x b := by
    funext y
    simp [chartFrame]
  unfold gam
  rw [h, (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn.smul_const
      (s := Set.univ) c
    (mdiffAt_chartFrame x b)]
  rfl

theorem gam_symm (x : M) (a b : F) : gam x a b = gam x b a := by
  have h := (CovariantDerivative.torsion_eq_zero_iff (CovariantDerivative.leviCivitaConnection
      𝓘(ℝ, F) M)).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, F)) (X := chartFrame (I := 𝓘(ℝ,
        F)) x a)
    (Y := chartFrame (I := 𝓘(ℝ, F)) x b) (x := x) (mdiffAt_chartFrame x a) (mdiffAt_chartFrame x b)
  rw [mlieBracket_chartFrames, chartFrame_self, chartFrame_self] at h
  exact sub_eq_zero.mp h


/-- the Christoffel map as a continuous bilinear map -/
noncomputable def gamCLM (x : M) : F →L[ℝ] F →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (E := F) (F' := F)).toLinearMap ∘ₗ
      (LinearMap.mk₂ ℝ (gam x)
        (fun a a' b => by
          unfold gam
          exact map_add _ a a')
        (fun c a b => by
          unfold gam
          exact map_smul _ c a)
        (gam_add_right x) (fun c m n => gam_smul_right x m n c)))

theorem gamCLM_apply (x : M) (a b : F) : gamCLM x a b = gam x a b := rfl

/-- the quadratic test polynomial in chart coordinates -/
noncomputable def gt (x : M) (ξ : F →L[ℝ] ℝ) (z : F) : ℝ :=
  ξ (z - extChartAt 𝓘(ℝ, F) x x) +
    (1 / 2) * ξ (gamCLM x (z - extChartAt 𝓘(ℝ, F) x x) (z - extChartAt 𝓘(ℝ, F) x x))

theorem contDiff_gt (x : M) (ξ : F →L[ℝ] ℝ) : ContDiff ℝ ∞ (gt x ξ) := by
  unfold gt
  fun_prop

theorem hasFDerivAt_gt (x : M) (ξ : F →L[ℝ] ℝ) (z : F) :
    HasFDerivAt (gt x ξ) (ξ + (1 / 2 : ℝ) • (ξ.comp (gamCLM x (z - extChartAt 𝓘(ℝ, F) x x) +
      (gamCLM x).flip (z - extChartAt 𝓘(ℝ, F) x x)))) z := by
  have h1 : HasFDerivAt (fun z : F => z - extChartAt 𝓘(ℝ, F) x x) (ContinuousLinearMap.id ℝ F) z :=
    (hasFDerivAt_id z).sub_const _
  have h2 := ((gamCLM x).hasFDerivAt.comp z h1).clm_apply h1
  have h3 := (ξ.hasFDerivAt.comp z h1).add (((ξ.hasFDerivAt.comp z h2).const_mul (1 / 2 : ℝ)))
  refine HasFDerivAt.congr_fderiv (f' := _) (by exact h3) ?_
  ext w
  simp


theorem fderiv_gt_center (x : M) (ξ : F →L[ℝ] ℝ) :
    fderiv ℝ (gt x ξ) (extChartAt 𝓘(ℝ, F) x x) = ξ := by
  rw [(hasFDerivAt_gt x ξ _).fderiv]
  simp

theorem mvfderiv_eq_xi {G : M → ℝ} (x : M) (ξ : F →L[ℝ] ℝ)
    (hG : (G ∘ (extChartAt 𝓘(ℝ, F) x).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, F) x x)] gt x ξ) (w : F) :
    mvfderiv 𝓘(ℝ, F) G x w = ξ w := by
  rw [← fderiv_comp_symm_center x w, hG.fderiv_eq, fderiv_gt_center]


/-- first derivative of `gt` in the direction `w`, as an explicit affine function -/
noncomputable def Kfun (x : M) (ξ : F →L[ℝ] ℝ) (w : F) (z : F) : ℝ :=
  ξ w + (1 / 2) * ξ ((gamCLM x).flip w (z - extChartAt 𝓘(ℝ, F) x x) +
    gamCLM x w (z - extChartAt 𝓘(ℝ, F) x x))

theorem fderiv_gt_apply (x : M) (ξ : F →L[ℝ] ℝ) (w z : F) :
    fderiv ℝ (gt x ξ) z w = Kfun x ξ w z := by
  rw [(hasFDerivAt_gt x ξ z).fderiv]
  simp [Kfun, add_comm]
  ring

theorem hasFDerivAt_Kfun (x : M) (ξ : F →L[ℝ] ℝ) (w z : F) :
    HasFDerivAt (Kfun x ξ w)
      ((1 / 2 : ℝ) • ξ.comp ((gamCLM x).flip w + gamCLM x w)) z := by
  have h1 : HasFDerivAt (fun z : F => z - extChartAt 𝓘(ℝ, F) x x) (ContinuousLinearMap.id ℝ F) z :=
    (hasFDerivAt_id z).sub_const _
  have h2 := (((gamCLM x).flip w + gamCLM x w).hasFDerivAt.comp z h1)
  have h3 := ((ξ.hasFDerivAt.comp z h2).const_mul (1 / 2 : ℝ)).const_add (ξ w)
  refine HasFDerivAt.congr_fderiv (f' := _) (by exact h3) ?_
  ext u
  simp

theorem fderiv_Kfun_center (x : M) (ξ : F →L[ℝ] ℝ) (w a : F) :
    fderiv ℝ (Kfun x ξ w) (extChartAt 𝓘(ℝ, F) x x) a = ξ (gam x a w) := by
  rw [(hasFDerivAt_Kfun x ξ w _).fderiv]
  simp [gamCLM_apply, gam_symm x w a]
  ring


theorem hessian_zero_of_chart {G : M → ℝ} (x : M) (ξ : F →L[ℝ] ℝ)
    (hGs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ G)
    (hG : (G ∘ (extChartAt 𝓘(ℝ, F) x).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, F) x x)] gt x ξ)
    (a w : F) : CutoffRigidity.manifoldHessian 𝓘(ℝ, F) G x a w = 0 := by
  have hGd : ∀ y, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) G y :=
    fun y => (hGs y).mdifferentiableAt (by simp)
  have hgrad : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (T% (manifoldGradient 𝓘(ℝ, F) G)) x :=
    ((WReg.contMDiff_manifoldGradient_top hGs) x).mdifferentiableAt (by simp)
  have hm := (CovariantDerivative.isMetricCompatible_leviCivitaConnection 𝓘(ℝ, F) (M :=
      M)).mvfderiv_inner_eq
    (chartFrame (I := 𝓘(ℝ, F)) x a) hgrad (mdiffAt_chartFrame x w)
  set e := extChartAt 𝓘(ℝ, F) x with he
  have hev1 : ∀ᶠ z in 𝓝 (e x), G ∘ e.symm =ᶠ[𝓝 z] gt x ξ := hG.eventuallyEq_nhds
  have hev2 : ∀ᶠ y in 𝓝 x, (G ∘ e.symm =ᶠ[𝓝 (e y)] gt x ξ) ∧ y ∈ (chartAt F x).source :=
    ((continuousAt_extChartAt (I := 𝓘(ℝ, F)) x).eventually hev1).and (chart_source_mem_nhds F x)
  have hEq : (fun y => mvfderiv 𝓘(ℝ, F) G y (chartFrame (I := 𝓘(ℝ, F)) x w y)) =ᶠ[𝓝 x]
      (Kfun x ξ w ∘ e) := by
    filter_upwards [hev2] with y ⟨hy1, hy2⟩
    have hys : y ∈ e.source := by simpa only [e, extChartAt_source] using hy2
    have hz : e y ∈ e.target := e.map_source hys
    have h0 := fderiv_chartScalar_frame (I := 𝓘(ℝ, F)) x hz (hGd (e.symm (e y))) w
    have key : ∀ y' : M, y' = y →
        mvfderiv 𝓘(ℝ, F) G y' (chartFrame (I := 𝓘(ℝ, F)) x w y') =
        mvfderiv 𝓘(ℝ, F) G y (chartFrame (I := 𝓘(ℝ, F)) x w y) := by
      intro y' h; subst h; rfl
    rw [key _ (e.left_inv hys)] at h0
    rw [← h0, hy1.fderiv_eq]
    exact fderiv_gt_apply x ξ w (e y)
  have hcongr : mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) G y
      (chartFrame (I := 𝓘(ℝ, F)) x w y)) x = mvfderiv 𝓘(ℝ, F) (Kfun x ξ w ∘ e) x := by
    exact hEq.mvfderiv_eq
  have hKe2 : (Kfun x ξ w ∘ e) ∘ e.symm =ᶠ[𝓝 (e x)] Kfun x ξ w := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, F)) x] with z hz
    simp [e.right_inv hz]
  have hB : mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) G y
      (chartFrame (I := 𝓘(ℝ, F)) x w y)) x a = ξ (gam x a w) := by
    rw [hcongr, ← fderiv_comp_symm_center x a, hKe2.fderiv_eq]
    exact fderiv_Kfun_center x ξ w a
  have hA : (fun y => inner ℝ (manifoldGradient 𝓘(ℝ, F) G y) (chartFrame (I := 𝓘(ℝ, F)) x w y)) =
      fun y => mvfderiv 𝓘(ℝ, F) G y (chartFrame (I := 𝓘(ℝ, F)) x w y) := by
    funext y
    exact inner_manifoldGradient 𝓘(ℝ, F) G y _
  have hC : inner ℝ (manifoldGradient 𝓘(ℝ, F) G x)
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (chartFrame (I := 𝓘(ℝ, F)) x w) x a)
      = ξ (gam x a w) := by
    rw [inner_manifoldGradient]
    exact mvfderiv_eq_xi x ξ hG _
  have hXa : chartFrame (I := 𝓘(ℝ, F)) x a x = a := chartFrame_self x a
  have hWw : chartFrame (I := 𝓘(ℝ, F)) x w x = w := chartFrame_self x w
  beta_reduce at hm
  rw [hA, hXa, hWw, hB] at hm
  have hm2 := hm
  rw [hC] at hm2
  unfold CutoffRigidity.manifoldHessian
  linarith


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
