/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed

/-!
# Derivatives of the Carleman phase quantities

The coordinate rules here expand the squared gradient and spatial Laplacian
in the commutator identity `eq:carleman-commutator`.
-/

public section


open MeasureTheory CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

local instance carlemanCoreCommDerivativesNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreCommDerivativesNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- Spatial differentiation ignores a factor depending only on time. -/
theorem spatialPartial_time_pow_mul_at
    (m : ℕ) {f : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hf : DifferentiableAt ℝ f z) (i : Fin 3) :
    spatialPartial (fun y => y.2 ^ m * f y) i z =
      z.2 ^ m * spatialPartial f i z := by
  have ht : DifferentiableAt ℝ
      (fun y : ParabolicPoint => y.2 ^ m) z := by fun_prop
  calc
    _ = spatialPartial (fun y : ParabolicPoint => y.2 ^ m) i z * f z +
        z.2 ^ m * spatialPartial f i z :=
      spatialPartial_mul_at ht hf i
    _ = _ := by rw [spatialPartial_time_pow]; ring

/-- A real constant factors out of a spatial coordinate derivative. -/
theorem spatialPartial_const_mul_at
    (c : ℝ) {f : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hf : DifferentiableAt ℝ f z) (i : Fin 3) :
    spatialPartial (fun y => c * f y) i z =
      c * spatialPartial f i z := by
  have hc : DifferentiableAt ℝ
      (fun _ : ParabolicPoint => c) z := differentiableAt_const _
  calc
    _ = spatialPartial (fun _ : ParabolicPoint => c) i z * f z +
        c * spatialPartial f i z :=
      spatialPartial_mul_at hc hf i
    _ = _ := by simp [spatialPartial]

/-- A constant times an integral time power factors out of a spatial
coordinate derivative. -/
theorem spatialPartial_const_time_pow_mul_at
    (c : ℝ) (m : ℕ) {f : ParabolicPoint → ℝ}
    {z : ParabolicPoint} (hf : DifferentiableAt ℝ f z) (i : Fin 3) :
    spatialPartial (fun y => c * (y.2 ^ m * f y)) i z =
      c * z.2 ^ m * spatialPartial f i z := by
  have ht : DifferentiableAt ℝ
      (fun y : ParabolicPoint => y.2 ^ m) z := by fun_prop
  calc
    _ = c * spatialPartial (fun y => y.2 ^ m * f y) i z :=
      spatialPartial_const_mul_at c (ht.mul hf) i
    _ = _ := by rw [spatialPartial_time_pow_mul_at m hf i]; ring

/-- The time derivative of a squared spatial gradient. -/
theorem timePartial_scalarGradSq_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) :
    timePartial (scalarGradSq f) z =
      2 * ∑ i, spatialPartial f i z *
        timePartial (fun y => spatialPartial f i y) z := by
  have hd (i : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial f i y) z :=
    ((contDiffOn_spatialPartial hU hf i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hds (i : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial f i y ^ 2) z :=
    (hd i).pow 2
  unfold scalarGradSq
  rw [timePartial_finsetSum_at Finset.univ
    (fun i y => spatialPartial f i y ^ 2) (fun i _ => hds i)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = 2 * spatialPartial f i z *
          timePartial (fun y => spatialPartial f i y) z :=
      timePartial_sq_at (hd i)
    _ = _ := by ring

/-- A spatial derivative of a squared spatial gradient. -/
theorem spatialPartial_scalarGradSq_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) (j : Fin 3) :
    spatialPartial (scalarGradSq f) j z =
      2 * ∑ i, spatialPartial f i z * spatialSecondPartial f i j z := by
  have hd (i : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial f i y) z :=
    ((contDiffOn_spatialPartial hU hf i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hds (i : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial f i y ^ 2) z :=
    (hd i).pow 2
  unfold scalarGradSq
  rw [spatialPartial_finsetSum_at Finset.univ
    (fun i y => spatialPartial f i y ^ 2) (fun i _ => hds i)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = 2 * spatialPartial f i z *
          spatialPartial (fun y => spatialPartial f i y) j z :=
      spatialPartial_sq_at (hd i) j
    _ = _ := by unfold spatialSecondPartial; ring

/-- The time derivative of the zeroth-order conjugation potential. -/
theorem timePartial_carlemanPotential_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) :
    timePartial (fun y => scalarGradSq f y - timePartial f y) z =
      2 * ∑ i, spatialPartial f i z *
        timePartial (fun y => spatialPartial f i y) z -
      timePartial (fun y => timePartial f y) z := by
  have hg : DifferentiableAt ℝ (scalarGradSq f) z :=
    ((contDiffOn_scalarGradSq hU hf).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ (fun y => timePartial f y) z :=
    ((contDiffOn_timePartial hU hf).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  calc
    _ = timePartial (scalarGradSq f) z -
        timePartial (fun y => timePartial f y) z :=
      timePartial_sub_at hg ht
    _ = _ := by rw [timePartial_scalarGradSq_on hU hf hz]

/-- A spatial derivative of the zeroth-order conjugation potential. -/
theorem spatialPartial_carlemanPotential_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => scalarGradSq f y - timePartial f y) i z =
      2 * ∑ j, spatialPartial f j z * spatialSecondPartial f j i z -
      timePartial (fun y => spatialPartial f i y) z := by
  have hg : DifferentiableAt ℝ (scalarGradSq f) z :=
    ((contDiffOn_scalarGradSq hU hf).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ (fun y => timePartial f y) z :=
    ((contDiffOn_timePartial hU hf).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  calc
    _ = spatialPartial (scalarGradSq f) i z -
        spatialPartial (fun y => timePartial f y) i z :=
      spatialPartial_sub_at hg ht i
    _ = _ := by
      rw [spatialPartial_scalarGradSq_on hU hf hz i,
        ← timePartial_spatialPartial_comm_on hU hf hz i]

/-- Product rule for the spatial dot product of two gradients. -/
theorem spatialPartial_gradientDot_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f g : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial
        (fun y => ∑ j, spatialPartial f j y * spatialPartial g j y) i z =
      ∑ j, (spatialSecondPartial f j i z * spatialPartial g j z +
        spatialPartial f j z * spatialSecondPartial g j i z) := by
  have hdf (j : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial f j y) z :=
    ((contDiffOn_spatialPartial hU hf j).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hdg (j : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial g j y) z :=
    ((contDiffOn_spatialPartial hU hg j).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hprod (j : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial f j y *
        spatialPartial g j y) z := (hdf j).mul (hdg j)
  calc
    _ = ∑ j, spatialPartial
          (fun y => spatialPartial f j y * spatialPartial g j y) i z :=
      spatialPartial_finsetSum_at Finset.univ _ (fun j _ => hprod j) i
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [spatialPartial_mul_at (hdf j) (hdg j) i]
      unfold spatialSecondPartial
      ring

/-- A spatial derivative distributes over the scalar Laplacian. -/
theorem spatialPartial_scalarLaplacian_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (scalarLaplacian f) i z =
      ∑ j, spatialPartial
        (fun y => spatialSecondPartial f j j y) i z := by
  have hd (j : Fin 3) : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialSecondPartial f j j y) z :=
    ((contDiffOn_spatialPartial hU
      (contDiffOn_spatialPartial hU hf j) j).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  unfold scalarLaplacian
  exact spatialPartial_finsetSum_at Finset.univ _ (fun j _ => hd j) i

/-- The spatial bi-Laplacian is the double sum of fourth coordinate
derivatives. -/
theorem scalarLaplacian_second_diagonal_on
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {z : ParabolicPoint} (hz : z ∈ U) :
    (∑ i, spatialSecondPartial (scalarLaplacian f) i i z) =
      ∑ j, ∑ i, spatialSecondPartial
        (fun y => spatialSecondPartial f j j y) i i z := by
  have hper (i : Fin 3) :
      spatialSecondPartial (scalarLaplacian f) i i z =
        ∑ j, spatialSecondPartial
          (fun y => spatialSecondPartial f j j y) i i z := by
    let F : ParabolicPoint → ℝ := fun y =>
      spatialPartial (scalarLaplacian f) i y
    let G : ParabolicPoint → ℝ := fun y =>
      ∑ j, spatialPartial (fun x => spatialSecondPartial f j j x) i y
    have hEq : (show Vec3 × ℝ → ℝ from F) =ᶠ[𝓝 z]
        (show Vec3 × ℝ → ℝ from G) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact spatialPartial_scalarLaplacian_on hU hf hy i
    have hFdiff : DifferentiableAt ℝ
        (show Vec3 × ℝ → ℝ from F) z :=
      ((contDiffOn_spatialPartial hU
        (contDiffOn_scalarLaplacian hU hf) i).contDiffAt
        (hU.mem_nhds hz)).differentiableAt (by simp)
    have hGdiff : DifferentiableAt ℝ
        (show Vec3 × ℝ → ℝ from G) z :=
      hEq.differentiableAt_iff.mp hFdiff
    have hd (j : Fin 3) : DifferentiableAt ℝ
        (fun y : ParabolicPoint =>
          spatialPartial (fun x => spatialSecondPartial f j j x) i y) z :=
      ((contDiffOn_spatialPartial hU
        (contDiffOn_spatialPartial hU
          (contDiffOn_spatialPartial hU hf j) j) i).contDiffAt
        (hU.mem_nhds hz)).differentiableAt (by simp)
    calc
      _ = spatialPartial F i z := rfl
      _ = fderiv ℝ (show Vec3 × ℝ → ℝ from F) z (basisVec i, 0) :=
        spatialPartial_eq_product_fderiv hFdiff i
      _ = fderiv ℝ (show Vec3 × ℝ → ℝ from G) z (basisVec i, 0) :=
        congrArg (fun L : Vec3 × ℝ →L[ℝ] ℝ => L (basisVec i, 0)) hEq.fderiv_eq
      _ = spatialPartial G i z :=
        (spatialPartial_eq_product_fderiv hGdiff i).symm
      _ = ∑ j, spatialPartial
            (fun y => spatialPartial
              (fun x => spatialSecondPartial f j j x) i y) i z :=
        spatialPartial_finsetSum_at Finset.univ _ (fun j _ => hd j) i
      _ = _ := rfl
  calc
    _ = ∑ i, ∑ j, spatialSecondPartial
          (fun y => spatialSecondPartial f j j y) i i z := by
      apply Finset.sum_congr rfl
      intro i _
      exact hper i
    _ = _ := Finset.sum_comm

end ESS
