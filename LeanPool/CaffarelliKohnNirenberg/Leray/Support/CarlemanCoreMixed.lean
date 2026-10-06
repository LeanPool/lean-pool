/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreGradient
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Commutation of space-time coordinate derivatives

The commutator calculation in `eq:carleman-commutator` of the Escauriaza–Seregin–Šverák manuscript
uses symmetry of the
second derivative of a smooth scalar field.
-/

public section

open CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace CKN

open Finset

/-- A spatial coordinate derivative is the ordinary space-time derivative
in the corresponding coordinate direction. -/
theorem spatialPartial_eq_product_fderiv
    {f : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hf : DifferentiableAt ℝ f z) (i : Fin 3) :
    spatialPartial f i z = fderiv ℝ f z (basisVec i, 0) := by
  have hF : HasFDerivAt f (fderiv ℝ f z) z := hf.hasFDerivAt
  let G : Vec3 → Vec3 × ℝ := fun x => (x, z.2)
  have hG : HasFDerivAt G
      ((ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ)) z.1 := by
    exact (hasFDerivAt_id z.1).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) z.2 z.1)
  have hc := hF.comp z.1 hG
  have hfun : (fun x : Vec3 => f (x, z.2)) = f ∘ G := rfl
  change (fderiv ℝ (fun x : Vec3 => f (x, z.2)) z.1) (basisVec i) = _
  rw [hfun, hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

/-- The time coordinate derivative is the ordinary space-time derivative
in the time direction. -/
theorem timePartial_eq_product_fderiv
    {f : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hf : DifferentiableAt ℝ f z) :
    timePartial f z = fderiv ℝ f z (0, 1) := by
  have hF : HasFDerivAt f (fderiv ℝ f z) z := hf.hasFDerivAt
  let G : ℝ → Vec3 × ℝ := fun t => (z.1, t)
  have hG : HasFDerivAt G
      ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 := by
    exact (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk
      (hasFDerivAt_id z.2)
  have hc := hF.comp z.2 hG
  have hfun : (fun t : ℝ => f (z.1, t)) = f ∘ G := rfl
  change (fderiv ℝ (fun t : ℝ => f (z.1, t)) z.2) 1 = _
  rw [hfun, hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

private theorem fderiv_coordinate_apply_const
    {f : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z)
    (e d : Vec3 × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ f y e) z d =
      fderiv ℝ (fderiv ℝ f) z d e := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hfd (differentiableAt_const (c := e))]
  simp

/-- Smooth scalar fields have symmetric iterated spatial coordinate
derivatives. -/
theorem spatialSecondPartial_comm
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z : Vec3 × ℝ) (i j : Fin 3) :
    spatialSecondPartial f i j z = spatialSecondPartial f j i z := by
  have hfirst (k : Fin 3) :
      (fun y : ParabolicPoint => spatialPartial f k y) =
        (fun y : ParabolicPoint => fderiv ℝ f y (basisVec k, 0)) := by
    funext y
    exact spatialPartial_eq_product_fderiv
      (hf.differentiable (by simp) y) k
  have hfd (k : Fin 3) : DifferentiableAt ℝ
      (fun y : Vec3 × ℝ => fderiv ℝ f y (basisVec k, 0)) z :=
    ((hf.contDiffAt.fderiv_right (m := (1 : ℕ∞)) (by simp)).clm_apply
      (contDiffAt_const (𝕜 := ℝ) (n := (1 : ℕ∞)))).differentiableAt
      (by simp)
  have hcoord (k l : Fin 3) :
      spatialSecondPartial f k l z =
        fderiv ℝ (fderiv ℝ f) z (basisVec l, 0) (basisVec k, 0) := by
    unfold spatialSecondPartial
    rw [hfirst k]
    calc
      _ = fderiv ℝ (fun y : Vec3 × ℝ =>
          fderiv ℝ f y (basisVec k, 0)) z (basisVec l, 0) :=
        spatialPartial_eq_product_fderiv (hfd k) l
      _ = _ := fderiv_coordinate_apply_const hf.contDiffAt _ _
  rw [hcoord i j, hcoord j i]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- Time and spatial coordinate differentiation commute for smooth scalar
fields. -/
theorem timePartial_spatialPartial_comm
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z : Vec3 × ℝ) (i : Fin 3) :
    timePartial (fun y => spatialPartial f i y) z =
      spatialPartial (fun y => timePartial f y) i z := by
  let es : Vec3 × ℝ := (basisVec i, 0)
  let et : Vec3 × ℝ := (0, 1)
  have hs : (fun y : ParabolicPoint => spatialPartial f i y) =
      (fun y : ParabolicPoint => fderiv ℝ f y es) := by
    funext y
    exact spatialPartial_eq_product_fderiv
      (hf.differentiable (by simp) y) i
  have ht : (fun y : ParabolicPoint => timePartial f y) =
      (fun y : ParabolicPoint => fderiv ℝ f y et) := by
    funext y
    exact timePartial_eq_product_fderiv
      (hf.differentiable (by simp) y)
  have hd (e : Vec3 × ℝ) : DifferentiableAt ℝ
      (fun y : Vec3 × ℝ => fderiv ℝ f y e) z :=
    ((hf.contDiffAt.fderiv_right (m := (1 : ℕ∞)) (by simp)).clm_apply
      (contDiffAt_const (𝕜 := ℝ) (n := (1 : ℕ∞)))).differentiableAt
      (by simp)
  have hleft : timePartial (fun y => spatialPartial f i y) z =
      fderiv ℝ (fderiv ℝ f) z et es := by
    rw [hs]
    calc
      _ = fderiv ℝ (fun y : Vec3 × ℝ => fderiv ℝ f y es) z et :=
        timePartial_eq_product_fderiv (hd es)
      _ = _ := fderiv_coordinate_apply_const hf.contDiffAt _ _
  have hright : spatialPartial (fun y => timePartial f y) i z =
      fderiv ℝ (fderiv ℝ f) z es et := by
    rw [ht]
    calc
      _ = fderiv ℝ (fun y : Vec3 × ℝ => fderiv ℝ f y et) z es :=
        spatialPartial_eq_product_fderiv (hd et) i
      _ = _ := fderiv_coordinate_apply_const hf.contDiffAt _ _
  rw [hleft, hright]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) et es

/-- Spatial differentiation commutes with a finite sum of differentiable
scalar fields. -/
theorem spatialPartial_finsetSum_at
    {ι : Type*} (s : Finset ι) (f : ι → Vec3 × ℝ → ℝ)
    {z : Vec3 × ℝ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (j : Fin 3) :
    spatialPartial (fun y => ∑ i ∈ s, f i y) j z =
      ∑ i ∈ s, spatialPartial (f i) j z := by
  have hsum : DifferentiableAt ℝ (fun y : Vec3 × ℝ => ∑ i ∈ s, f i y) z := by
    fun_prop (disch := assumption)
  calc
    _ = fderiv ℝ (fun y : Vec3 × ℝ => ∑ i ∈ s, f i y) z
          (basisVec j, 0) := spatialPartial_eq_product_fderiv hsum j
    _ = ∑ i ∈ s, fderiv ℝ (f i) z (basisVec j, 0) := by
      rw [fderiv_fun_sum hf]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (spatialPartial_eq_product_fderiv (hf i hi) j).symm

/-- Time differentiation commutes with a finite sum of differentiable
scalar fields. -/
theorem timePartial_finsetSum_at
    {ι : Type*} (s : Finset ι) (f : ι → Vec3 × ℝ → ℝ)
    {z : Vec3 × ℝ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    timePartial (fun y => ∑ i ∈ s, f i y) z =
      ∑ i ∈ s, timePartial (f i) z := by
  have hsum : DifferentiableAt ℝ (fun y : Vec3 × ℝ => ∑ i ∈ s, f i y) z := by
    fun_prop (disch := assumption)
  calc
    _ = fderiv ℝ (fun y : Vec3 × ℝ => ∑ i ∈ s, f i y) z (0, 1) :=
      timePartial_eq_product_fderiv hsum
    _ = ∑ i ∈ s, fderiv ℝ (f i) z (0, 1) := by
      rw [fderiv_fun_sum hf]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (timePartial_eq_product_fderiv (hf i hi)).symm

/-- A spatial coordinate derivative distributes over subtraction. -/
theorem spatialPartial_sub_at
    {f g : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (i : Fin 3) :
    spatialPartial (fun y => f y - g y) i z =
      spatialPartial f i z - spatialPartial g i z := by
  calc
    _ = fderiv ℝ (fun y => f y - g y) z (basisVec i, 0) :=
      spatialPartial_eq_product_fderiv (hf.sub hg) i
    _ = fderiv ℝ f z (basisVec i, 0) -
          fderiv ℝ g z (basisVec i, 0) := by rw [fderiv_fun_sub hf hg]; simp
    _ = _ := by rw [← spatialPartial_eq_product_fderiv hf i,
      ← spatialPartial_eq_product_fderiv hg i]

/-- A time coordinate derivative distributes over subtraction. -/
theorem timePartial_sub_at
    {f g : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    timePartial (fun y => f y - g y) z =
      timePartial f z - timePartial g z := by
  calc
    _ = fderiv ℝ (fun y => f y - g y) z (0, 1) :=
      timePartial_eq_product_fderiv (hf.sub hg)
    _ = fderiv ℝ f z (0, 1) - fderiv ℝ g z (0, 1) := by
      rw [fderiv_fun_sub hf hg]
      simp
    _ = _ := by rw [← timePartial_eq_product_fderiv hf,
      ← timePartial_eq_product_fderiv hg]

/-- A spatial coordinate derivative distributes over addition. -/
theorem spatialPartial_add_at
    {f g : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (i : Fin 3) :
    spatialPartial (fun y => f y + g y) i z =
      spatialPartial f i z + spatialPartial g i z := by
  calc
    _ = fderiv ℝ (fun y => f y + g y) z (basisVec i, 0) :=
      spatialPartial_eq_product_fderiv (hf.add hg) i
    _ = fderiv ℝ f z (basisVec i, 0) +
          fderiv ℝ g z (basisVec i, 0) := by rw [fderiv_fun_add hf hg]; simp
    _ = _ := by rw [← spatialPartial_eq_product_fderiv hf i,
      ← spatialPartial_eq_product_fderiv hg i]

/-- A time coordinate derivative distributes over addition. -/
theorem timePartial_add_at
    {f g : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    timePartial (fun y => f y + g y) z =
      timePartial f z + timePartial g z := by
  calc
    _ = fderiv ℝ (fun y => f y + g y) z (0, 1) :=
      timePartial_eq_product_fderiv (hf.add hg)
    _ = fderiv ℝ f z (0, 1) + fderiv ℝ g z (0, 1) := by
      rw [fderiv_fun_add hf hg]
      simp
    _ = _ := by rw [← timePartial_eq_product_fderiv hf,
      ← timePartial_eq_product_fderiv hg]

section Local

local instance carlemanCoreMixedNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreMixedNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- Coordinate second derivatives commute at every point where the phase is
smooth on an open set. -/
theorem spatialSecondPartial_comm_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) (i j : Fin 3) :
    spatialSecondPartial f i j z = spatialSecondPartial f j i z := by
  have hfat : ContDiffAt ℝ (⊤ : ℕ∞)
      (show Vec3 × ℝ → ℝ from f) z := by
    exact hf.contDiffAt (hU.mem_nhds hz)
  have hfirst (k : Fin 3) :
      (fun y : Vec3 × ℝ => spatialPartial f k y) =ᶠ[𝓝 z]
        (fun y => fderiv ℝ (show Vec3 × ℝ → ℝ from f) y (basisVec k, 0)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact spatialPartial_eq_product_fderiv
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) k
  have hfd (k : Fin 3) : DifferentiableAt ℝ
      (fun y : Vec3 × ℝ => fderiv ℝ (show Vec3 × ℝ → ℝ from f) y
        (basisVec k, 0)) z :=
    ((hfat.fderiv_right (m := (1 : ℕ∞)) (by simp)).clm_apply
      (contDiffAt_const (𝕜 := ℝ) (n := (1 : ℕ∞)))).differentiableAt
      (by simp)
  have hcoord (k l : Fin 3) :
      spatialSecondPartial f k l z =
        fderiv ℝ (fderiv ℝ (show Vec3 × ℝ → ℝ from f)) z
          (basisVec l, 0) (basisVec k, 0) := by
    unfold spatialSecondPartial
    calc
      _ = fderiv ℝ (fun y : Vec3 × ℝ => spatialPartial f k y) z
            (basisVec l, 0) :=
          spatialPartial_eq_product_fderiv
            ((hfirst k).differentiableAt_iff.mpr (hfd k)) l
      _ = fderiv ℝ (fun y : Vec3 × ℝ =>
            fderiv ℝ (show Vec3 × ℝ → ℝ from f) y (basisVec k, 0)) z
            (basisVec l, 0) := by
          exact congrArg (fun L : Vec3 × ℝ →L[ℝ] ℝ =>
            L (basisVec l, 0)) (hfirst k).fderiv_eq
      _ = _ := fderiv_coordinate_apply_const hfat _ _
  rw [hcoord i j, hcoord j i]
  exact (hfat.isSymmSndFDerivAt (by simp)) _ _

/-- Time and spatial coordinate derivatives commute wherever the phase is
smooth on an open set. -/
theorem timePartial_spatialPartial_comm_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    timePartial (fun y => spatialPartial f i y) z =
      spatialPartial (fun y => timePartial f y) i z := by
  let es : Vec3 × ℝ := (basisVec i, 0)
  let et : Vec3 × ℝ := (0, 1)
  have hfat : ContDiffAt ℝ (⊤ : ℕ∞)
      (show Vec3 × ℝ → ℝ from f) z :=
    hf.contDiffAt (hU.mem_nhds hz)
  have hs : (fun y : Vec3 × ℝ => spatialPartial f i y) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ (show Vec3 × ℝ → ℝ from f) y es) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact spatialPartial_eq_product_fderiv
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) i
  have ht : (fun y : Vec3 × ℝ => timePartial f y) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ (show Vec3 × ℝ → ℝ from f) y et) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact timePartial_eq_product_fderiv
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  have hd (e : Vec3 × ℝ) : DifferentiableAt ℝ
      (fun y : Vec3 × ℝ => fderiv ℝ (show Vec3 × ℝ → ℝ from f) y e) z :=
    ((hfat.fderiv_right (m := (1 : ℕ∞)) (by simp)).clm_apply
      (contDiffAt_const (𝕜 := ℝ) (n := (1 : ℕ∞)))).differentiableAt
      (by simp)
  have hleft : timePartial (fun y => spatialPartial f i y) z =
      fderiv ℝ (fderiv ℝ (show Vec3 × ℝ → ℝ from f)) z et es := by
    calc
      _ = fderiv ℝ (fun y : Vec3 × ℝ => spatialPartial f i y) z et :=
        timePartial_eq_product_fderiv (hs.differentiableAt_iff.mpr (hd es))
      _ = fderiv ℝ (fun y : Vec3 × ℝ =>
            fderiv ℝ (show Vec3 × ℝ → ℝ from f) y es) z et := by
          exact congrArg (fun L : Vec3 × ℝ →L[ℝ] ℝ => L et) hs.fderiv_eq
      _ = _ := fderiv_coordinate_apply_const hfat _ _
  have hright : spatialPartial (fun y => timePartial f y) i z =
      fderiv ℝ (fderiv ℝ (show Vec3 × ℝ → ℝ from f)) z es et := by
    calc
      _ = fderiv ℝ (fun y : Vec3 × ℝ => timePartial f y) z es :=
        spatialPartial_eq_product_fderiv (ht.differentiableAt_iff.mpr (hd et)) i
      _ = fderiv ℝ (fun y : Vec3 × ℝ =>
            fderiv ℝ (show Vec3 × ℝ → ℝ from f) y et) z es := by
          exact congrArg (fun L : Vec3 × ℝ →L[ℝ] ℝ => L es) ht.fderiv_eq
      _ = _ := fderiv_coordinate_apply_const hfat _ _
  rw [hleft, hright]
  exact (hfat.isSymmSndFDerivAt (by simp)) et es

end Local

end CKN
