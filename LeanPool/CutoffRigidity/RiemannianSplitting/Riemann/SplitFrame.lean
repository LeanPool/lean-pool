/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitFlowGlobal
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFields
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedGradientRegularity
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.Riemannian.Killing.Flow

/-! # Orthonormal parallel frames and their flows

A *frame* of size `k` is a family of smooth functions `sᵢ` with parallel gradients and
`Γ(sᵢ, sⱼ) = δᵢⱼ`.  Their unit gradients `Xᵢ` are complete parallel fields; the flow `φᵢ` of `Xᵢ`
consists of isometries (project), is `C^∞` jointly (`SplitFlowGlobal`), shifts `sⱼ` by `δᵢⱼ t`, and
(derived here) commutes with the other fields: `dφᵢᵗ(Xⱼ) = Xⱼ ∘ φᵢᵗ`.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

section Frame

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (M : Type) [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M]

/-- A frame of size `k`: smooth functions with parallel gradients and `Γ(sᵢ,sⱼ) = δᵢⱼ`. -/
structure Frame (k : ℕ) where
  /-- Smooth potentials for the parallel vector fields. -/
  s : Fin k → M → ℝ
  smooth : ∀ i, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (s i)
  parallel : ∀ i x, CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F (s i)) x = 0
  gram : ∀ i j x, carre F (s i) (s j) x = if i = j then 1 else 0

variable {F M} {k : ℕ}

namespace Frame

variable (fr : Frame F M k)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsRiemannianManifold 𝓘(ℝ, F) M]
  [CompleteSpace M] in
/-- The Riesz gradient pairs with the differential. -/
theorem inner_mgrad (f : M → ℝ) (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ (mgrad F f x) v = mvfderiv 𝓘(ℝ, F) f x v := by
  simp [mgrad]
  rfl

/-- The unit parallel gradient field. -/
noncomputable def X (i : Fin k) : (x : M) → TangentSpace 𝓘(ℝ, F) x := mgrad F (fr.s i)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem inner_X (i j : Fin k) (x : M) :
    inner ℝ (fr.X i x) (fr.X j x) = if i = j then 1 else 0 := fr.gram i j x

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem norm_X (i : Fin k) (x : M) : ‖fr.X i x‖ = 1 := by
  have h := fr.inner_X i i x
  simp only [ite_true, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (fr.X i x)]

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem contMDiff_X (i : Fin k) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% (fr.X i)) :=
  WReg.contMDiff_mgrad (fr.smooth i)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem contMDiff_X_one (i : Fin k) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% (fr.X i)) :=
  (fr.contMDiff_X i).of_le (by simp)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem enorm_X_le (i : Fin k) (x : M) : ‖fr.X i x‖ₑ ≤ (1 : ℝ≥0) := by
  apply eNorm_le_coe.mpr
  have := fr.norm_X i x
  exact_mod_cast this.le

/-- The flow of the `i`-th parallel field. -/
noncomputable def flow (i : Fin k) (x : M) (t : ℝ) : M :=
  CutoffRigidity.completeBoundedFlow (fr.contMDiff_X_one i) (fr.enorm_X_le i) x t

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem mvfderiv_s_X (j i : Fin k) (x : M) :
    mvfderiv 𝓘(ℝ, F) (fr.s j) x (fr.X i x) = if j = i then 1 else 0 := by
  rw [← inner_mgrad]
  exact fr.gram j i x

/-- `sⱼ` is shifted by `δᵢⱼ t` along the flow of `Xᵢ`. -/
theorem s_flow (j i : Fin k) (x : M) (t : ℝ) :
    fr.s j (fr.flow i x t) = fr.s j x + (if j = i then t else 0) := by
  have h := CutoffRigidity.scalar_integralCurve_eq_add
    (CutoffRigidity.completeBoundedFlow_isMIntegralCurve (fr.contMDiff_X_one i) (fr.enorm_X_le i) x)
    ((fr.smooth j).mdifferentiable (by simp)) (c := if j = i then 1 else 0)
    (fun y => fr.mvfderiv_s_X j i y) t
  simp only [CutoffRigidity.completeBoundedFlow_zero] at h
  rw [flow, h]
  split_ifs <;> simp

theorem contMDiff_flow_joint (i : Fin k) :
    ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun p : M × ℝ => fr.flow i p.1 p.2) :=
  CutoffRigidity.Riemann.contMDiff_completeBoundedFlow_joint_infty (fr.contMDiff_X_one i)
    (fr.contMDiff_X i) (fr.enorm_X_le i)

theorem contMDiff_flow_slice (i : Fin k) (t : ℝ) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun x : M => fr.flow i x t) :=
  (fr.contMDiff_flow_joint i).comp (contMDiff_id.prodMk contMDiff_const)

private theorem flow_slice_eq_flowOf (i : Fin k) (t : ℝ) :
    (fun y ↦ fr.flow i y t) = TauCeti.flowOf (fr.X i) t := by
  funext y
  have hcurve := CutoffRigidity.completeBoundedFlow_isMIntegralCurve
    (fr.contMDiff_X_one i) (fr.enorm_X_le i) y
  have h := TauCeti.flowOf_eq_of_isMIntegralCurve (fr.contMDiff_X_one i) hcurve t
  simpa only [flow, CutoffRigidity.completeBoundedFlow_zero] using h.symm

/-- The differential of the frame flow preserves the Riemannian pairing. -/
theorem inner_mfderiv_flow (i : Fin k) (x : M) (u v : TangentSpace 𝓘(ℝ, F) x) (t : ℝ) :
    inner ℝ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x u)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x v) = inner ℝ u v := by
  let I := 𝓘(ℝ, F)
  have hK : TauCeti.Manifold.IsKillingField I (fr.X i) := by
    have hcompatible := CovariantDerivative.isMetricCompatible_leviCivitaConnection (M := M) I
    apply (hcompatible.isKillingField_iff
      (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)).2
    refine ⟨fr.contMDiff_X i, fun y w z ↦ ?_⟩
    change inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgrad F (fr.s i)) y w) z =
      -inner ℝ w (CovariantDerivative.leviCivitaConnection I M (mgrad F (fr.s i)) y z)
    have hparallel : CovariantDerivative.leviCivitaConnection I M (mgrad F (fr.s i)) y = 0 :=
      fr.parallel i y
    rw [hparallel]
    simp
  have hcomplete := TauCeti.isCompleteVectorField_of_forall_exists_isMIntegralCurve
    (CutoffRigidity.exists_global_integralCurve_of_bounded (fr.contMDiff_X_one i) (fr.enorm_X_le i))
  let preserves (slice : M → M) : Prop :=
    inner ℝ (mfderiv I I slice x u) (mfderiv I I slice x v) = inner ℝ u v
  change preserves (fun y ↦ fr.flow i y t)
  rw [fr.flow_slice_eq_flowOf i t]
  exact hK.inner_mfderiv_flowOf (hcomplete.mem_flowDomain t x) u v

theorem norm_mfderiv_flow (i : Fin k) (x : M) (u : TangentSpace 𝓘(ℝ, F) x) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x u‖ = ‖u‖ := by
  have h := fr.inner_mfderiv_flow i x u u t
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    congrArg Real.sqrt h

/-- Differentials of `sⱼ` are invariant under the flows of the frame. -/
theorem mvfderiv_s_flow (j i : Fin k) (x : M) (t : ℝ) (u : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (fr.s j) (fr.flow i x t)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x u) = mvfderiv 𝓘(ℝ, F) (fr.s j) x u := by
  have hs : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fr.s j) (fr.flow i x t) :=
    ((fr.smooth j).mdifferentiable (by simp)) _
  have hf : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x :=
    ((fr.contMDiff_flow_slice i t).mdifferentiable (by simp)) x
  have hcomp : (fun y => fr.s j (fr.flow i y t)) = fun y => fr.s j y + (if j = i then t else 0) :=
    funext fun y => fr.s_flow j i y t
  have h1 := mfderiv_comp x hs hf
  have h3 : mvfderiv 𝓘(ℝ, F) (fun y => fr.s j (fr.flow i y t)) x =
      (mvfderiv 𝓘(ℝ, F) (fr.s j) (fr.flow i x t)).comp
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x) := by
    ext u
    simp only [mvfderiv, ContinuousLinearMap.comp_apply]
    rw [show (fun y => fr.s j (fr.flow i y t)) = (fr.s j) ∘ (fun y => fr.flow i y t) from rfl, h1]
    rfl
  have h4 : mvfderiv 𝓘(ℝ, F) (fun y => fr.s j (fr.flow i y t)) x = mvfderiv 𝓘(ℝ, F) (fr.s j) x := by
    rw [hcomp]
    have hs' : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fr.s j) x :=
      ((fr.smooth j).mdifferentiable (by simp)) x
    have := mvfderiv_add (I := 𝓘(ℝ, F)) (x := x) hs'
      (mdifferentiableAt_const (c := (if j = i then t else 0)))
    simp only [Pi.add_def] at this
    rw [this, mvfderiv_const, add_zero]
  have := congrArg (fun L => L u) (h3.symm.trans h4)
  exact this

/-- Parallel gradient fields are invariant under the flows of the frame:
`dφᵢᵗ (Xⱼ) = Xⱼ ∘ φᵢᵗ`. -/
theorem mfderiv_flow_X (i j : Fin k) (x : M) (t : ℝ) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x (fr.X j x) = fr.X j (fr.flow i x t) := by
  set W := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.flow i y t) x (fr.X j x) with hWdef
  set V := fr.X j (fr.flow i x t) with hVdef
  have hW : ‖W‖ = 1 := by rw [hWdef, fr.norm_mfderiv_flow, fr.norm_X]
  have hV : ‖V‖ = 1 := fr.norm_X j _
  have hWV : inner ℝ V W = 1 := by
    have h1 : inner ℝ V W = mvfderiv 𝓘(ℝ, F) (fr.s j) (fr.flow i x t) W :=
      inner_mgrad (fr.s j) _ W
    rw [h1, hWdef, fr.mvfderiv_s_flow, ← inner_mgrad]
    have := fr.inner_X j j x
    simpa [Frame.X] using this
  have hsq : ‖W - V‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hW, hV, real_inner_comm, hWV]
    norm_num
  have : W - V = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    exact norm_eq_zero.mp this
  exact sub_eq_zero.mp this

end Frame

end Frame

end CutCur
