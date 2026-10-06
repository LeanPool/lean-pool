/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreCalculus

/-!
# Second spatial derivatives on an open domain

The local second derivative product rule used in
`prop:carleman-gauss` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace CKN

local instance carlemanCoreSecondNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreSecondNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- A spatial derivative of a smooth function is differentiable along each
spatial slice. -/
theorem differentiableAt_spatialPartial_slice
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    DifferentiableAt ℝ (fun x : Vec3 => spatialPartial f i (x, z.2)) z.1 := by
  have hslice : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => f (x, z.2)) z.1 :=
    (hf.contDiffAt (hU.mem_nhds hz)).comp z.1 (by fun_prop)
  change DifferentiableAt ℝ
    (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => f (y, z.2)) x (basisVec i)) z.1
  have hfd : ContDiffAt ℝ (⊤ : ℕ∞)
      (fderiv ℝ (fun y : Vec3 => f (y, z.2))) z.1 :=
    hslice.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have heval : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => f (y, z.2)) x (basisVec i)) z.1 :=
    hfd.clm_apply (contDiffAt_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
  exact heval.differentiableAt (by simp)

/-- Local product rule for an iterated spatial derivative. -/
theorem spatialSecondPartial_mul_at
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {a b : ParabolicPoint → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a U)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U)
    {z : ParabolicPoint} (hz : z ∈ U) (i j : Fin 3) :
    spatialSecondPartial (fun y => a y * b y) i j z =
      spatialSecondPartial a i j z * b z +
        spatialPartial a i z * spatialPartial b j z +
        spatialPartial a j z * spatialPartial b i z +
        a z * spatialSecondPartial b i j z := by
  let A : Vec3 → ℝ := fun x => spatialPartial a i (x, z.2)
  let B : Vec3 → ℝ := fun x => b (x, z.2)
  let C : Vec3 → ℝ := fun x => a (x, z.2)
  let D : Vec3 → ℝ := fun x => spatialPartial b i (x, z.2)
  have hA : DifferentiableAt ℝ A z.1 :=
    differentiableAt_spatialPartial_slice hU ha hz i
  have hB : DifferentiableAt ℝ B z.1 :=
    ((hb.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).comp z.1
      (by fun_prop)
  have hC : DifferentiableAt ℝ C z.1 :=
    ((ha.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).comp z.1
      (by fun_prop)
  have hD : DifferentiableAt ℝ D z.1 :=
    differentiableAt_spatialPartial_slice hU hb hz i
  have hnhds : {x : Vec3 | (x, z.2) ∈ U} ∈ 𝓝 z.1 := by
    have hopen : IsOpen {x : Vec3 | (x, z.2) ∈ U} :=
      hU.preimage (by fun_prop : Continuous (fun x : Vec3 => (x, z.2)))
    exact hopen.mem_nhds hz
  have heq :
      (fun x : Vec3 => spatialPartial (fun y => a y * b y) i (x, z.2))
        =ᶠ[𝓝 z.1] (fun x => A x * B x + C x * D x) := by
    filter_upwards [hnhds] with x hx
    dsimp [A, B, C, D]
    exact spatialPartial_mul_at
      ((ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      ((hb.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) i
  have hderiv := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
    (heq.fderiv_eq (𝕜 := ℝ))
  change (fderiv ℝ
    (fun x : Vec3 => spatialPartial (fun y => a y * b y) i (x, z.2)) z.1)
      (basisVec j) = _
  rw [hderiv]
  change (fderiv ℝ (A * B + C * D) z.1) (basisVec j) = _
  rw [fderiv_add (hA.mul hB) (hC.mul hD),
    fderiv_mul hA hB, fderiv_mul hC hD]
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp only [A, B, C, D, spatialSecondPartial, spatialPartial]
  have hae : a (z.1, z.2) = a z := by cases z; rfl
  have hbe : b (z.1, z.2) = b z := by cases z; rfl
  rw [hae, hbe]
  ring

/-- The second spatial derivative of an exponential phase. -/
theorem spatialSecondPartial_exp_at
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    {z : ParabolicPoint} (hz : z ∈ U) (i j : Fin 3) :
    spatialSecondPartial (fun y => Real.exp (φ y)) i j z =
      Real.exp (φ z) *
        (spatialSecondPartial φ i j z +
          spatialPartial φ i z * spatialPartial φ j z) := by
  let A : Vec3 → ℝ := fun x => Real.exp (φ (x, z.2))
  let B : Vec3 → ℝ := fun x => spatialPartial φ i (x, z.2)
  have hφz : DifferentiableAt ℝ φ z :=
    (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hφslice : DifferentiableAt ℝ (fun x : Vec3 => φ (x, z.2)) z.1 :=
    hφz.comp z.1 (by fun_prop)
  have hA : DifferentiableAt ℝ A z.1 := hφslice.exp
  have hB : DifferentiableAt ℝ B z.1 :=
    differentiableAt_spatialPartial_slice hU hφ hz i
  have hnhds : {x : Vec3 | (x, z.2) ∈ U} ∈ 𝓝 z.1 := by
    have hopen : IsOpen {x : Vec3 | (x, z.2) ∈ U} :=
      hU.preimage (by fun_prop : Continuous (fun x : Vec3 => (x, z.2)))
    exact hopen.mem_nhds hz
  have heq :
      (fun x : Vec3 => spatialPartial (fun y => Real.exp (φ y)) i (x, z.2))
        =ᶠ[𝓝 z.1] (fun x => A x * B x) := by
    filter_upwards [hnhds] with x hx
    dsimp [A, B]
    exact spatialPartial_exp_at
      ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) i
  have hderiv := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
    (heq.fderiv_eq (𝕜 := ℝ))
  change (fderiv ℝ
    (fun x : Vec3 => spatialPartial (fun y => Real.exp (φ y)) i (x, z.2)) z.1)
      (basisVec j) = _
  rw [hderiv]
  change (fderiv ℝ (A * B) z.1) (basisVec j) = _
  rw [fderiv_mul hA hB]
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp only [A, B, spatialSecondPartial, spatialPartial]
  have hφe : φ (z.1, z.2) = φ z := by cases z; rfl
  rw [hφe]
  rw [fderiv_exp hφslice]
  simp only [smul_apply, smul_eq_mul]
  rw [hφe]
  ring

/-- The second spatial derivative under exponential conjugation. -/
theorem spatialSecondPartial_exp_mul_at
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {z : ParabolicPoint} (hz : z ∈ U) (i j : Fin 3) :
    spatialSecondPartial (fun y => Real.exp (φ y) * w y) i j z =
      Real.exp (φ z) *
        (spatialSecondPartial w i j z +
          spatialPartial φ i z * spatialPartial w j z +
          spatialPartial φ j z * spatialPartial w i z +
          w z * (spatialSecondPartial φ i j z +
            spatialPartial φ i z * spatialPartial φ j z)) := by
  have h := spatialSecondPartial_mul_at hU hφ.exp hw.contDiffOn hz i j
  rw [h, spatialSecondPartial_exp_at hU hφ hz i j,
    spatialPartial_exp_at
      ((hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) i,
    spatialPartial_exp_at
      ((hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) j]
  ring

end CKN
