/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitFrame

/-! # The `ℝ^k`-action of a frame: composition of flows, its inverse, smoothness -/

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

/-- `φ_{L₀}^{t_{L₀}} ∘ φ_{L₁}^{t_{L₁}} ∘ ⋯`. -/
noncomputable def comp (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) (x : M) : M :=
  L.foldr (fun i acc => fr.flow i acc (t i)) x

/-- The inverse composition: first `φ_{L₀}^{-t_{L₀}}`, then `φ_{L₁}^{-t_{L₁}}`, ... -/
noncomputable def compRev (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) (x : M) : M :=
  L.foldl (fun acc i => fr.flow i acc (-(t i))) x

@[simp] theorem comp_nil (t : EuclideanSpace ℝ (Fin k)) (x : M) : fr.comp [] t x = x := rfl

theorem comp_cons (a : Fin k) (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) (x : M) :
    fr.comp (a :: L) t x = fr.flow a (fr.comp L t x) (t a) := rfl

@[simp] theorem compRev_nil (t : EuclideanSpace ℝ (Fin k)) (x : M) : fr.compRev [] t x = x := rfl

theorem compRev_cons (a : Fin k) (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) (x : M) :
    fr.compRev (a :: L) t x = fr.compRev L t (fr.flow a x (-(t a))) := rfl

theorem flow_neg_cancel' (a : Fin k) (x : M) (r : ℝ) : fr.flow a (fr.flow a x (-r)) r = x := by
  have := CutoffRigidity.completeBoundedFlow_neg_cancel (fr.contMDiff_X_one a) (fr.enorm_X_le a) x
      (-r)
  simpa [Frame.flow] using this

theorem flow_neg_cancel (a : Fin k) (x : M) (r : ℝ) : fr.flow a (fr.flow a x r) (-r) = x := by
  have := CutoffRigidity.completeBoundedFlow_neg_cancel (fr.contMDiff_X_one a) (fr.enorm_X_le a) x r
  simpa [Frame.flow] using this

theorem comp_compRev (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) :
    ∀ x : M, fr.comp L t (fr.compRev L t x) = x := by
  induction L with
  | nil => intro x; rfl
  | cons a L ih =>
    intro x
    rw [compRev_cons, comp_cons, ih, flow_neg_cancel']

theorem compRev_comp (L : List (Fin k)) (t : EuclideanSpace ℝ (Fin k)) :
    ∀ x : M, fr.compRev L t (fr.comp L t x) = x := by
  induction L with
  | nil => intro x; rfl
  | cons a L ih =>
    intro x
    rw [comp_cons, compRev_cons, flow_neg_cancel, ih]

theorem s_comp (j : Fin k) (L : List (Fin k)) (hL : L.Nodup) (t : EuclideanSpace ℝ (Fin k)) :
    ∀ x : M, fr.s j (fr.comp L t x) = fr.s j x + (if j ∈ L then t j else 0) := by
  induction L with
  | nil => intro x; simp
  | cons a L ih =>
    intro x
    have hnd := List.nodup_cons.mp hL
    rw [comp_cons, fr.s_flow, ih hnd.2]
    by_cases hja : j = a
    · subst hja
      simp [hnd.1]
    · simp [hja, List.mem_cons]

theorem s_compRev (j : Fin k) (L : List (Fin k)) (hL : L.Nodup) (t : EuclideanSpace ℝ (Fin k)) :
    ∀ x : M, fr.s j (fr.compRev L t x) = fr.s j x - (if j ∈ L then t j else 0) := by
  induction L generalizing t with
  | nil => intro x; simp
  | cons a L ih =>
    intro x
    have hnd := List.nodup_cons.mp hL
    rw [compRev_cons, ih hnd.2, fr.s_flow]
    by_cases hja : j = a
    · subst hja
      simp [hnd.1, sub_eq_add_neg]
    · simp [hja, List.mem_cons]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsRiemannianManifold 𝓘(ℝ, F) M]
  [CompleteSpace M] in
theorem contMDiff_coord (a : Fin k) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
      (fun p : EuclideanSpace ℝ (Fin k) × M => p.1 a) :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.contMDiff.comp contMDiff_fst

theorem contMDiff_comp (L : List (Fin k)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
      (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp L p.1 p.2) := by
  induction L with
  | nil => exact contMDiff_snd
  | cons a L ih =>
    exact (fr.contMDiff_flow_joint a).comp (ih.prodMk (contMDiff_coord (F := F) (M := M) a))

theorem contMDiff_compRev (L : List (Fin k)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
      (fun p : EuclideanSpace ℝ (Fin k) × M => fr.compRev L p.1 p.2) := by
  induction L with
  | nil => exact contMDiff_snd
  | cons a L ih =>
    have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) ∞
        (fun p : EuclideanSpace ℝ (Fin k) × M => (p.1, fr.flow a p.2 (-(p.1 a)))) := by
      refine contMDiff_fst.prodMk ?_
      exact (fr.contMDiff_flow_joint a).comp (contMDiff_snd.prodMk (contMDiff_coord (F := F) (M :=
          M) a).neg)
    exact ih.comp h1

/-- The vector of frame functions, in Euclidean coordinates. -/
noncomputable def sv (x : M) : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun i => fr.s i x)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem contMDiff_sv : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ fr.sv := by
  have h : fr.sv = (EuclideanSpace.equiv (Fin k) ℝ).symm ∘ (fun x i => fr.s i x) := rfl
  rw [h]
  exact ((EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.contMDiff).comp
    (contMDiff_pi_module_iff.mpr fr.smooth)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem mfderiv_sv_apply (y : M) (v : TangentSpace 𝓘(ℝ, F) y) (j : Fin k) :
    (show EuclideanSpace ℝ (Fin k) from mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv y v)
        j =
      inner ℝ (fr.X j y) v := by
  have hsv : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv y :=
    (fr.contMDiff_sv.mdifferentiable (by simp)) y
  have hp : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, ℝ)
      (fun z : EuclideanSpace ℝ (Fin k) => z j) (fr.sv y) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero _
  have h := mfderiv_comp y hp hsv
  have hfun : ((fun z : EuclideanSpace ℝ (Fin k) => z j) ∘ fr.sv) = fr.s j := rfl
  rw [hfun] at h
  have hproj : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, ℝ)
      (fun z : EuclideanSpace ℝ (Fin k) => z j) (fr.sv y) = EuclideanSpace.proj (𝕜 := ℝ) j := by
    rw [mfderiv_eq_fderiv]
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).fderiv
  rw [hproj] at h
  have h2 := congrArg (fun L => L v) h
  have h3 : inner ℝ (fr.X j y) v = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fr.s j) y v := by
    rw [Frame.X, inner_mgrad]
    rfl
  rw [h3, h2]
  rfl

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem surjective_mfderiv_sv (y : M) :
    Function.Surjective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv y) := by
  intro c
  let c' : EuclideanSpace ℝ (Fin k) := c
  refine ⟨∑ i, c' i • fr.X i y, ?_⟩
  change _ = c'
  ext j
  rw [mfderiv_sv_apply]
  rw [inner_sum]
  simp only [inner_smul_right, fr.inner_X]
  simp

/-- Level set `{s = 0}`. -/
abbrev Level := {x : M // fr.sv x = 0}

/-- The retraction onto the zero level `{s = 0}`: flow back to level zero. -/
noncomputable def retr (x : M) : M := fr.compRev (List.finRange k) (fr.sv x) x

theorem s_retr (x : M) (j : Fin k) : fr.s j (fr.retr x) = 0 := by
  rw [retr, fr.s_compRev j _ (List.nodup_finRange k)]
  simp [sv]

theorem sv_retr (x : M) : fr.sv (fr.retr x) = 0 := by
  ext j
  simp [sv, fr.s_retr]

theorem comp_retr (x : M) : fr.comp (List.finRange k) (fr.sv x) (fr.retr x) = x :=
  fr.comp_compRev _ _ x

theorem contMDiff_retr : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ fr.retr :=
  (fr.contMDiff_compRev (List.finRange k)).comp (fr.contMDiff_sv.prodMk contMDiff_id)

theorem compRev_zero (L : List (Fin k)) (x : M) : fr.compRev L 0 x = x := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih =>
    rw [compRev_cons]
    have : fr.flow a x (-((0 : EuclideanSpace ℝ (Fin k)) a)) = x := by
      simpa [Frame.flow] using CutoffRigidity.completeBoundedFlow_zero (fr.contMDiff_X_one a)
          (fr.enorm_X_le a) x
    rw [this, ih]

theorem retr_of_level {y : M} (hy : fr.sv y = 0) : fr.retr y = y := by
  rw [retr, hy, compRev_zero]

theorem sv_comp (t : EuclideanSpace ℝ (Fin k)) (y : M) (hy : fr.sv y = 0) :
    fr.sv (fr.comp (List.finRange k) t y) = t := by
  ext j
  have := fr.s_comp j (List.finRange k) (List.nodup_finRange k) t y
  have hj : fr.s j y = 0 := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v j) hy
    simpa [sv] using this
  simp [sv, this, hj]

theorem retr_comp (t : EuclideanSpace ℝ (Fin k)) (y : M) (hy : fr.sv y = 0) :
    fr.retr (fr.comp (List.finRange k) t y) = y := by
  rw [retr, fr.sv_comp t y hy, compRev_comp]

end Frame

end CutCur
