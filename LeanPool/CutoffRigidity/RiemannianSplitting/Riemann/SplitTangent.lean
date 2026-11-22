/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitProduct

/-! # Tangent maps of the `ℝ^k`-action of a frame -/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)

theorem contMDiff_comp_slice (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun y : M => fr.comp L t y) :=
  (fr.contMDiff_comp L).comp (contMDiff_const.prodMk contMDiff_id)

theorem contMDiff_comp_orbit (L : List (Fin k)) (x : M) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F) ∞ (fun t : EuclideanSpace ℝ (Fin k) =>
        fr.comp L t x) :=
  (fr.contMDiff_comp L).comp (contMDiff_id.prodMk contMDiff_const)

/-- The tangent map of the composed flow (at fixed times) preserves inner products. -/
theorem inner_mfderiv_comp (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) :
    ∀ (x : M) (u v : TangentSpace 𝓘(ℝ, F) x),
    inner ℝ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x u)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x v) = inner ℝ u v := by
  induction L with
  | nil =>
    intro x u v
    have : (fun y : M => fr.comp [] t y) = id := rfl
    rw [this, mfderiv_id]
    rfl
  | cons a L ih =>
    intro x u v
    have hs : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.flow a z (t a)) (fr.comp L t x) :=
      ((fr.contMDiff_flow_slice a (t a)).mdifferentiable (by simp)) _
    have hc : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x :=
      ((fr.contMDiff_comp_slice L t).mdifferentiable (by simp)) x
    have hfun : (fun y : M => fr.comp (a :: L) t y) =
        (fun z => fr.flow a z (t a)) ∘ (fun y => fr.comp L t y) := rfl
    change inner ℝ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F)
        ((fun z => fr.flow a z (t a)) ∘ (fun y => fr.comp L t y)) x u)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F)
        ((fun z => fr.flow a z (t a)) ∘ (fun y => fr.comp L t y)) x v) = _
    rw [mfderiv_comp x hs hc]
    change inner ℝ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.flow a z (t a)) (fr.comp L t x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x u))
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.flow a z (t a)) (fr.comp L t x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x v)) = _
    rw [fr.inner_mfderiv_flow a _ _ _ (t a), ih]

/-- Parallel gradient fields are invariant under the composed flow. -/
theorem mfderiv_comp_X (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    ∀ x : M, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x (fr.X i x) =
      fr.X i (fr.comp L t x) := by
  induction L with
  | nil =>
    intro x
    have : (fun y : M => fr.comp [] t y) = id := rfl
    rw [this, mfderiv_id]
    rfl
  | cons a L ih =>
    intro x
    have hs : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.flow a z (t a)) (fr.comp L t x) :=
      ((fr.contMDiff_flow_slice a (t a)).mdifferentiable (by simp)) _
    have hc : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x :=
      ((fr.contMDiff_comp_slice L t).mdifferentiable (by simp)) x
    have hfun : (fun y : M => fr.comp (a :: L) t y) =
        (fun z => fr.flow a z (t a)) ∘ (fun y => fr.comp L t y) := rfl
    change mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F)
        ((fun z => fr.flow a z (t a)) ∘ (fun y => fr.comp L t y)) x (fr.X i x) = _
    rw [mfderiv_comp x hs hc]
    change mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.flow a z (t a)) (fr.comp L t x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => fr.comp L t y) x (fr.X i x)) = _
    rw [ih x]
    exact fr.mfderiv_flow_X a i _ (t a)

/-- Derivative of the orbit of a flow. -/
theorem mfderiv_flow_orbit (a : Fin k) (y : M) (r σ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun z : ℝ => fr.flow a y z) r σ = σ • fr.X a (fr.flow a y r) := by
  have hγ := CutoffRigidity.completeBoundedFlow_isMIntegralCurve (fr.contMDiff_X_one a)
    (fr.enorm_X_le a) y r
  have h := hγ.mfderiv
  let velocity : TangentSpace 𝓘(ℝ, ℝ) r := σ
  have h2 := congrArg (fun L => L velocity) h
  exact h2

/-- Derivative in the times of the composed flow. -/
theorem mfderiv_comp_t (L : List (Fin k)) (x : M) :
    ∀ (t w : EuclideanSpace ℝ (Fin k)),
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F) (fun τ => fr.comp L τ x) t w =
      (L.map (fun i => w i • fr.X i (fr.comp L t x))).sum := by
  induction L with
  | nil =>
    intro t w
    have : (fun τ : EuclideanSpace ℝ (Fin k) => fr.comp [] τ x) = fun _ => x := rfl
    rw [this, mfderiv_const]
    rfl
  | cons a L ih =>
    intro t w
    have hflow : MDifferentiableAt (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F)
        (fun p : M × ℝ => fr.flow a p.1 p.2) (fr.comp L t x, t a) :=
      ((fr.contMDiff_flow_joint a).mdifferentiable (by simp)) _
    have hL : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F)
        (fun τ => fr.comp L τ x) t :=
      ((fr.contMDiff_comp_orbit L x).mdifferentiable (by simp)) t
    have hc : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, ℝ)
        (fun τ : EuclideanSpace ℝ (Fin k) => τ a) t :=
      ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero _
    have hpair := hL.prodMk hc
    change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F)
      ((fun p : M × ℝ => fr.flow a p.1 p.2) ∘ (fun τ => (fr.comp L τ x, τ a))) t w = _
    rw [mfderiv_comp t hflow hpair, mfderiv_prodMk hL hc]
    have hproj : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, ℝ)
        (fun τ : EuclideanSpace ℝ (Fin k) => τ a) t = EuclideanSpace.proj (𝕜 := ℝ) a := by
      rw [mfderiv_eq_fderiv]
      exact (EuclideanSpace.proj (𝕜 := ℝ) a).fderiv
    change mfderiv (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) (fun p : M × ℝ => fr.flow a p.1 p.2)
      (fr.comp L t x, t a) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F)
        (fun τ => fr.comp L τ x) t w,
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, ℝ) (fun τ : EuclideanSpace ℝ (Fin k) => τ a) t
            w) = _
    have hsplit := mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, ℝ))
      (I'' := 𝓘(ℝ, F)) (p := (fr.comp L t x, t a)) (v :=
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F) (fun τ => fr.comp L τ x) t w,
       mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, ℝ) (fun τ => τ a) t w)) hflow
    rw [hsplit, hproj]
    change mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.flow a z (t a)) (fr.comp L t x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F) (fun τ => fr.comp L τ x) t w) +
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun z : ℝ => fr.flow a (fr.comp L t x) z) (t a)
        ((EuclideanSpace.proj (𝕜 := ℝ) a) w) = _
    have h1 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.flow a z (t a)) (fr.comp L t x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, F) (fun τ => fr.comp L τ x) t w) =
        (L.map (fun i => w i • fr.X i (fr.flow a (fr.comp L t x) (t a)))).sum := by
      rw [ih t w, map_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, map_smul]
      rw [fr.mfderiv_flow_X a i _ (t a)]
    rw [h1, fr.mfderiv_flow_orbit]
    change _ = (List.map (fun i => w.ofLp i • fr.X i (fr.flow a (fr.comp L t x) (t a))) (a ::
        L)).sum
    rw [List.map_cons, List.sum_cons, add_comm]
    rfl

/-- Joint derivative of the composed flow in (times, point). -/
theorem mfderiv_comp_joint (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) (m : M)
    (w : EuclideanSpace ℝ (Fin k)) (v : TangentSpace 𝓘(ℝ, F) m) :
    mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
      (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp L p.1 p.2) (t, m) (w, v) =
    (L.map (fun i => w i • fr.X i (fr.comp L t m))).sum +
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.comp L t z) m v := by
  have hd : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
      (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp L p.1 p.2) (t, m) :=
    ((fr.contMDiff_comp L).mdifferentiable (by simp)) _
  have hsplit := mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin k)))
    (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, F)) (p := (t, m)) (v := (w, v)) hd
  exact hsplit.trans (congrArg (fun u => u + _) (fr.mfderiv_comp_t L m t w))

theorem contMDiff_retr_mdiff (x : M) : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x :=
  (fr.contMDiff_retr.mdifferentiable (by simp)) x

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem mdiff_sv (x : M) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv x :=
  (fr.contMDiff_sv.mdifferentiable (by simp)) x

/-- Forget the base point of a tangent vector. -/
def tf (v : F) : F := v

/-- The frame coordinates `(⟨Xᵢ, v⟩)ᵢ` of a tangent vector, as the differential of `s`. -/
noncomputable def dsv (x : M) (v : TangentSpace 𝓘(ℝ, F) x) : EuclideanSpace ℝ (Fin k) :=
  mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv x v

/-- Decomposition of a tangent vector along the frame and the level. -/
theorem decomp (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    tf v = tf ((∑ i, (fr.dsv x v) i • fr.X i (fr.comp (List.finRange k) (fr.sv x) (fr.retr x))) +
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.comp (List.finRange k) (fr.sv x) z) (fr.retr x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v)) := by
  have hΓ : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
      (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp (List.finRange k) p.1 p.2)
      (fr.sv x, fr.retr x) :=
    ((fr.contMDiff_comp (List.finRange k)).mdifferentiable (by simp)) _
  have hpair : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F))
      (fun z => (fr.sv z, fr.retr z)) x := (fr.mdiff_sv x).prodMk (fr.contMDiff_retr_mdiff x)
  have hcomp := hΓ.hasMFDerivAt.comp x hpair.hasMFDerivAt
  have hid : ((fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp (List.finRange k) p.1 p.2) ∘
      (fun z => (fr.sv z, fr.retr z))) =ᶠ[nhds x] (id : M → M) :=
    Filter.Eventually.of_forall (fun z => fr.comp_retr z)
  have h2 := hcomp.congr_of_eventuallyEq_abuse hid.symm
  have h3 := h2.mfderiv
  rw [mfderiv_id] at h3
  have h4 := congrArg (fun L => L v) h3
  simp only at h4
  have hpd : mfderiv 𝓘(ℝ, F) (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F))
      (fun z => (fr.sv z, fr.retr z)) x =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv x).prod
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x) :=
    mfderiv_prodMk (fr.mdiff_sv x) (fr.contMDiff_retr_mdiff x)
  rw [hpd] at h4
  have h6 := fr.mfderiv_comp_joint (List.finRange k) (fr.sv x) (fr.retr x)
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv x v)
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v)
  have h7 : tf v = tf (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
      (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp (List.finRange k) p.1 p.2)
      (fr.sv x, fr.retr x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv x v,
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v)) := congrArg tf h4
  rw [h6] at h7
  rw [Fin.sum_univ_def]
  exact h7

end Frame

end CutCur
