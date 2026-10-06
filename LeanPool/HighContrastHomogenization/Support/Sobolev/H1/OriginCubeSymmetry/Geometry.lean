/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.OriginCubeSymmetry
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Coarse-graining support: Support.Sobolev.H1.OriginCubeSymmetry

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

open scoped Topology

noncomputable section

/-- File-level typeclass cache for `Module ℝ (Vec d)`. -/
private instance instModuleVecOCS (d : ℕ) : Module ℝ (Vec d) := inferInstance

/--
Coordinate sign-flip on `Vec d` as a continuous linear equivalence.
-/
@[expose]
noncomputable def signFlipVecContinuousLinearEquiv {d : ℕ} (i : Fin d) :
    Vec d ≃L[ℝ] Vec d :=
  ContinuousLinearEquiv.piCongrRight fun j : Fin d =>
    if h : j = i then
      by
        subst h
        exact ContinuousLinearEquiv.neg ℝ
    else
      ContinuousLinearEquiv.refl ℝ ℝ

/--
Coordinate swap on `Vec d` as a continuous linear equivalence.
-/
@[expose]
noncomputable def swapVecContinuousLinearEquiv {d : ℕ} (i j : Fin d) :
    Vec d ≃L[ℝ] Vec d :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin d => ℝ) (Equiv.swap i j)

@[simp] theorem signFlipVecContinuousLinearEquiv_apply {d : ℕ} (i : Fin d) (x : Vec d) :
    signFlipVecContinuousLinearEquiv i x = matVecMul (signFlipMatrix i) x := by
  ext j
  by_cases h : j = i
  · subst h
    simp [signFlipVecContinuousLinearEquiv, matVecMul_signFlipMatrix_apply]
  · simp [signFlipVecContinuousLinearEquiv, matVecMul_signFlipMatrix_apply, h]

@[simp] theorem signFlipVecContinuousLinearEquiv_symm_apply {d : ℕ} (i : Fin d) (x : Vec d) :
    (signFlipVecContinuousLinearEquiv i).symm x = matVecMul (signFlipMatrix i) x := by
  have hs : (signFlipVecContinuousLinearEquiv i).symm = signFlipVecContinuousLinearEquiv i := by
    ext y j
    by_cases h : j = i
    · subst h
      simp [signFlipVecContinuousLinearEquiv]
    · simp [signFlipVecContinuousLinearEquiv, h]
  rw [hs]
  exact signFlipVecContinuousLinearEquiv_apply i x

@[simp] theorem swapVecContinuousLinearEquiv_apply {d : ℕ} (i j : Fin d) (x : Vec d) :
    swapVecContinuousLinearEquiv i j x = matVecMul (Matrix.swap ℝ i j) x := by
  ext k
  have h :=
    Homeomorph.piCongrLeft_apply_apply (Y := fun _ : Fin d => ℝ) (Equiv.swap i j) x
      (Equiv.swap i j k)
  simpa [swapVecContinuousLinearEquiv, matVecMul_swap_eq_comp] using! h

@[simp] theorem swapVecContinuousLinearEquiv_symm_apply {d : ℕ} (i j : Fin d) (x : Vec d) :
    (swapVecContinuousLinearEquiv i j).symm x = matVecMul (Matrix.swap ℝ i j) x := by
  ext k
  have hfun :
      ⇑(Homeomorph.piCongrLeft (Y := fun _ : Fin d => ℝ) (Equiv.swap i j)).symm =
        fun y z => y ((Equiv.swap i j) z) :=
    Homeomorph.piCongrLeft_symm_apply (Y := fun _ : Fin d => ℝ) (Equiv.swap i j)
  have h :
      (swapVecContinuousLinearEquiv i j).symm x k = x ((Equiv.swap i j) k) := by
    change (Homeomorph.piCongrLeft (Y := fun _ : Fin d => ℝ) (Equiv.swap i j)).symm x k = _
    exact congrFun (congrFun hfun x) k
  simp [h, matVecMul_swap_eq_comp]

@[simp] theorem signFlipVecContinuousLinearEquiv_self_apply {d : ℕ} (i : Fin d) (x : Vec d) :
    signFlipVecContinuousLinearEquiv i (signFlipVecContinuousLinearEquiv i x) = x := by
  have hs : (signFlipVecContinuousLinearEquiv i).symm = signFlipVecContinuousLinearEquiv i := by
    ext y j
    by_cases h : j = i
    · subst h
      simp [signFlipVecContinuousLinearEquiv]
    · simp [signFlipVecContinuousLinearEquiv, h]
  simpa [hs] using (signFlipVecContinuousLinearEquiv i).apply_symm_apply x

@[simp] theorem swapVecContinuousLinearEquiv_self_apply {d : ℕ} (i j : Fin d) (x : Vec d) :
    swapVecContinuousLinearEquiv i j (swapVecContinuousLinearEquiv i j x) = x := by
  simpa [swapVecContinuousLinearEquiv_symm_apply] using
    (swapVecContinuousLinearEquiv i j).apply_symm_apply x

@[simp] theorem signFlipVecContinuousLinearEquiv_basisVec {d : ℕ} (i k : Fin d) :
    signFlipVecContinuousLinearEquiv i (basisVec k) =
      (if k = i then (-1 : ℝ) else 1) • basisVec k := by
  by_cases hki : k = i
  · subst hki
    ext j
    by_cases hjk : j = k
    · subst hjk
      simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply]
    · simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply,
        hjk]
  · ext j
    by_cases hjk : j = k
    · subst hjk
      simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply,
        hki]
    · simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply,
        hki, hjk]

@[simp] theorem swapVecContinuousLinearEquiv_basisVec {d : ℕ} (i j k : Fin d) :
    swapVecContinuousLinearEquiv i j (basisVec k) = basisVec (Equiv.swap i j k) := by
  ext l
  by_cases h : (Equiv.swap i j l) = k
  · have h' : l = Equiv.swap i j k := by
      simpa using congrArg (Equiv.swap i j) h
    simp [basisVec_apply, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp, h']
  · have h' : l ≠ Equiv.swap i j k := by
      intro hl
      apply h
      simp [hl]
    simp [basisVec_apply, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp, h, h']

private theorem measurePreserving_signFlipVecContinuousLinearEquiv {d : ℕ} (i : Fin d) :
    MeasureTheory.MeasurePreserving (signFlipVecContinuousLinearEquiv i) MeasureTheory.volume
      MeasureTheory.volume := by
  classical
  simpa [signFlipVecContinuousLinearEquiv_apply] using!
    (MeasureTheory.volume_preserving_pi fun j : Fin d =>
      by
        by_cases h : j = i
        · subst h
          simpa using!
            (MeasureTheory.Measure.measurePreserving_neg
              (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        · simpa [h] using
            (MeasureTheory.MeasurePreserving.id
              (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))))

private theorem measurePreserving_swapVecContinuousLinearEquiv {d : ℕ} (i j : Fin d) :
    MeasureTheory.MeasurePreserving (swapVecContinuousLinearEquiv i j) MeasureTheory.volume
      MeasureTheory.volume := by
  simpa [swapVecContinuousLinearEquiv] using!
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin d => ℝ) (Equiv.swap i j))

theorem measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube
    {d : ℕ} (i : Fin d) (n : ℤ) :
    MeasureTheory.MeasurePreserving (signFlipVecContinuousLinearEquiv i)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n)))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n))) := by
  let U := openCubeSet (originCube d n)
  have hpre : (signFlipVecContinuousLinearEquiv i) ⁻¹' U = U := by
    ext x
    simpa [U] using (mem_openCubeSet_originCube_signFlipMatrix_iff (m := n) (i := i) (x := x))
  simpa [U, hpre] using
    (measurePreserving_signFlipVecContinuousLinearEquiv i).restrict_preimage_emb
      (signFlipVecContinuousLinearEquiv i).toHomeomorph.measurableEmbedding U

theorem measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube
    {d : ℕ} (i j : Fin d) (n : ℤ) :
    MeasureTheory.MeasurePreserving (swapVecContinuousLinearEquiv i j)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n)))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n))) := by
  let U := openCubeSet (originCube d n)
  have hpre : (swapVecContinuousLinearEquiv i j) ⁻¹' U = U := by
    ext x
    simpa [U] using (mem_openCubeSet_originCube_swap_iff (m := n) (i := i) (j := j) (x := x))
  simpa [U, hpre] using
    (measurePreserving_swapVecContinuousLinearEquiv i j).restrict_preimage_emb
      (swapVecContinuousLinearEquiv i j).toHomeomorph.measurableEmbedding U

theorem setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube
    {d : ℕ} (i : Fin d) (n : ℤ) (f : Vec d → ℝ) :
    ∫ x in openCubeSet (originCube d n), f (signFlipVecContinuousLinearEquiv i x)
      ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d n), f x ∂MeasureTheory.volume := by
  let U := openCubeSet (originCube d n)
  let hμ := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i n
  simpa [U] using
    (hμ.integral_comp (signFlipVecContinuousLinearEquiv i).toHomeomorph.measurableEmbedding f)

theorem setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube
    {d : ℕ} (i j : Fin d) (n : ℤ) (f : Vec d → ℝ) :
    ∫ x in openCubeSet (originCube d n), f (swapVecContinuousLinearEquiv i j x)
      ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d n), f x ∂MeasureTheory.volume := by
  let U := openCubeSet (originCube d n)
  let hμ := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n
  simpa [U] using
    (hμ.integral_comp (swapVecContinuousLinearEquiv i j).toHomeomorph.measurableEmbedding f)

theorem fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec {d : ℕ}
    (i k : Fin d) {φ : Vec d → ℝ} {x : Vec d}
    (hφ : DifferentiableAt ℝ φ (signFlipVecContinuousLinearEquiv i x)) :
    (fderiv ℝ (fun y => φ (signFlipVecContinuousLinearEquiv i y)) x) (basisVec k) =
      (if k = i then (-1 : ℝ) else 1) *
        (fderiv ℝ φ (signFlipVecContinuousLinearEquiv i x)) (basisVec k) := by
  let T : Vec d → Vec d := signFlipVecContinuousLinearEquiv i
  have hcomp :
      fderiv ℝ (fun y => φ (T y)) x =
        (fderiv ℝ φ (T x)).comp (fderiv ℝ T x) := by
    simpa [T] using
      (fderiv_fun_comp (f := T) (g := φ) x hφ (signFlipVecContinuousLinearEquiv i).differentiableAt)
  have hlin : fderiv ℝ T x = (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap := by
    simpa [T] using ((signFlipVecContinuousLinearEquiv i).toContinuousLinearMap.fderiv (x := x))
  have hb :
      (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap (basisVec k) =
        (if k = i then (-1 : ℝ) else 1) • basisVec k := by
    simpa using (signFlipVecContinuousLinearEquiv_basisVec (i := i) (k := k))
  calc
    (fderiv ℝ (fun y => φ (signFlipVecContinuousLinearEquiv i y)) x) (basisVec k)
      = ((fderiv ℝ φ (T x)).comp (fderiv ℝ T x)) (basisVec k) := by
          simpa [T] using congrArg (fun L => L (basisVec k)) hcomp
    _ = ((fderiv ℝ φ (T x)).comp (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap)
          (basisVec k) := by rw [hlin]
    _ = (fderiv ℝ φ (T x))
          ((signFlipVecContinuousLinearEquiv i).toContinuousLinearMap (basisVec k)) := by
            rw [ContinuousLinearMap.comp_apply]
    _ = (fderiv ℝ φ (T x)) (((if k = i then (-1 : ℝ) else 1) • basisVec k)) := by rw [hb]
    _ = (if k = i then (-1 : ℝ) else 1) * (fderiv ℝ φ (T x)) (basisVec k) := by
          by_cases hki : k = i <;> simp [hki]
    _ = (if k = i then (-1 : ℝ) else 1) *
        (fderiv ℝ φ (signFlipVecContinuousLinearEquiv i x)) (basisVec k) := by
          simp [T]

theorem fderiv_comp_swapVecContinuousLinearEquiv_apply_basisVec {d : ℕ}
    (i j k : Fin d) {φ : Vec d → ℝ} {x : Vec d}
    (hφ : DifferentiableAt ℝ φ (swapVecContinuousLinearEquiv i j x)) :
    (fderiv ℝ (fun y => φ (swapVecContinuousLinearEquiv i j y)) x) (basisVec (Equiv.swap i j k)) =
      (fderiv ℝ φ (swapVecContinuousLinearEquiv i j x)) (basisVec k) := by
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  have hcomp :
      fderiv ℝ (fun y => φ (T y)) x =
        (fderiv ℝ φ (T x)).comp (fderiv ℝ T x) := by
    simpa [T] using
      (fderiv_fun_comp (f := T) (g := φ) x hφ (swapVecContinuousLinearEquiv i j).differentiableAt)
  have hlin : fderiv ℝ T x = (swapVecContinuousLinearEquiv i j).toContinuousLinearMap := by
    simpa [T] using ((swapVecContinuousLinearEquiv i j).toContinuousLinearMap.fderiv (x := x))
  have hb :
      (swapVecContinuousLinearEquiv i j).toContinuousLinearMap (basisVec (Equiv.swap i j k)) =
        basisVec k := by
    simpa using
      (swapVecContinuousLinearEquiv_basisVec (i := i) (j := j) (k := Equiv.swap i j k))
  calc
    (fderiv ℝ (fun y => φ (swapVecContinuousLinearEquiv i j y)) x) (basisVec (Equiv.swap i j k))
      = ((fderiv ℝ φ (T x)).comp (fderiv ℝ T x)) (basisVec (Equiv.swap i j k)) := by
          simpa [T] using congrArg (fun L => L (basisVec (Equiv.swap i j k))) hcomp
    _ = ((fderiv ℝ φ (T x)).comp (swapVecContinuousLinearEquiv i j).toContinuousLinearMap)
          (basisVec (Equiv.swap i j k)) := by rw [hlin]
    _ = (fderiv ℝ φ (T x))
          ((swapVecContinuousLinearEquiv i j).toContinuousLinearMap
            (basisVec (Equiv.swap i j k))) := by
            rw [ContinuousLinearMap.comp_apply]
    _ = (fderiv ℝ φ (T x)) (basisVec k) := by rw [hb]
    _ = (fderiv ℝ φ (swapVecContinuousLinearEquiv i j x)) (basisVec k) := by
          simp [T]

private theorem tsupport_comp_homeomorph_eq_preimage {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : β → ℝ} (e : α ≃ₜ β) :
    tsupport (fun x => f (e x)) = e ⁻¹' tsupport f := by
  rw [tsupport, tsupport, e.preimage_closure]
  ext x
  simp [Function.support]

theorem tsupport_comp_signFlip_subset_openCubeSet_originCube {d : ℕ}
    {f : Vec d → ℝ} (i : Fin d) (n : ℤ)
    (hsub : tsupport f ⊆ openCubeSet (originCube d n)) :
    tsupport (fun x => f (signFlipVecContinuousLinearEquiv i x)) ⊆
      openCubeSet (originCube d n) := by
  let U := openCubeSet (originCube d n)
  intro x hx
  have htsupp :
      tsupport (fun y => f (signFlipVecContinuousLinearEquiv i y)) =
        (signFlipVecContinuousLinearEquiv i) ⁻¹' tsupport f :=
    tsupport_comp_homeomorph_eq_preimage (signFlipVecContinuousLinearEquiv i).toHomeomorph
  have hx' : signFlipVecContinuousLinearEquiv i x ∈ tsupport f := by
    rw [htsupp] at hx
    exact hx
  have hTx : signFlipVecContinuousLinearEquiv i x ∈ U := hsub hx'
  have hTx' : matVecMul (signFlipMatrix i) x ∈ U := by
    simpa [signFlipVecContinuousLinearEquiv_apply] using hTx
  simpa [U] using
    (mem_openCubeSet_originCube_signFlipMatrix_iff (m := n) (i := i) (x := x)).1 hTx'

theorem tsupport_comp_swap_subset_openCubeSet_originCube {d : ℕ}
    {f : Vec d → ℝ} (i j : Fin d) (n : ℤ)
    (hsub : tsupport f ⊆ openCubeSet (originCube d n)) :
    tsupport (fun x => f (swapVecContinuousLinearEquiv i j x)) ⊆
      openCubeSet (originCube d n) := by
  let U := openCubeSet (originCube d n)
  intro x hx
  have htsupp :
      tsupport (fun y => f (swapVecContinuousLinearEquiv i j y)) =
        (swapVecContinuousLinearEquiv i j) ⁻¹' tsupport f :=
    tsupport_comp_homeomorph_eq_preimage (swapVecContinuousLinearEquiv i j).toHomeomorph
  have hx' : swapVecContinuousLinearEquiv i j x ∈ tsupport f := by
    rw [htsupp] at hx
    exact hx
  have hTx : swapVecContinuousLinearEquiv i j x ∈ U := hsub hx'
  have hTx' : matVecMul (Matrix.swap ℝ i j) x ∈ U := by
    simpa [swapVecContinuousLinearEquiv_apply] using hTx
  simpa [U] using
    (mem_openCubeSet_originCube_swap_iff (m := n) (i := i) (j := j) (x := x)).1 hTx'

end

end HCPolySupport
