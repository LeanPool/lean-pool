/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreProduct
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussWeights
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Carleman Half Weights Derivatives

Weight bounds used in the half-space Carleman estimate.
-/

public section


open CKN CKN.Foundation.Parabolic Set Filter
open scoped Topology

noncomputable section

namespace ESS

/-- The product topology used to differentiate the half-space Carleman weights. -/
local instance halfWeightsTopologicalSpace : TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd
/-- The product norm on parabolic space-time used for classical differentiation. -/
local instance halfWeightsNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup
/-- The real scalar action compatible with the product norm on parabolic space-time. -/
local instance halfWeightsNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- The open half-space and time slab used by `prop:carleman-halfspace`. -/
@[expose] def halfSpaceDomain : Set ParabolicPoint :=
  {x : Vec3 | 1 < x 2} ×ˢ Ioo 0 1

/-- The anisotropic phase in `prop:carleman-halfspace`. -/
@[expose] def halfSpacePhase (a α : ℝ) (z : ParabolicPoint) : ℝ :=
  -(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
    a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α

/-- The normal component of the spatial gradient of the half-space phase. -/
@[expose] def halfSpaceGradientTwo (a α : ℝ) (z : ParabolicPoint) : ℝ :=
  2 * α * a * (1 - z.2) * z.1 2 ^ (2 * α - 1) / z.2 ^ α

/-- The half-space in space times the time interval `(0,1)` is open. -/
theorem isOpen_halfSpaceDomain : IsOpen halfSpaceDomain := by
  dsimp [halfSpaceDomain]
  exact (isOpen_lt continuous_const (continuous_apply 2)).prod isOpen_Ioo

/-- The half-space phase is smooth on its domain. -/
theorem halfSpacePhase_contDiffOn (a α : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (halfSpacePhase a α) halfSpaceDomain := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  have hx2 : z.1 2 ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have ht0 : z.2 ≠ 0 := ne_of_gt ht.1
  have hden : 8 * z.2 ≠ 0 := mul_ne_zero (by norm_num) ht0
  have hpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht.1 α)
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun w : ParabolicPoint =>
      -(w.1 0 ^ 2 + w.1 1 ^ 2) / (8 * w.2) +
        a * (1 - w.2) * w.1 2 ^ (2 * α) / w.2 ^ α)
    halfSpaceDomain z
  have h : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : ParabolicPoint =>
        -(w.1 0 ^ 2 + w.1 1 ^ 2) / (8 * w.2) +
          a * (1 - w.2) * w.1 2 ^ (2 * α) / w.2 ^ α) z := by
    fun_prop
  exact h.contDiffWithinAt

private theorem coordRpowDeriv (x : Vec3) (j i : Fin 3) (p : ℝ)
    (hx : x j ≠ 0) :
    (fderiv ℝ (fun y : Vec3 => (y j) ^ p) x) (basisVec i) =
      if j = i then p * (x j) ^ (p - 1) else 0 := by
  have hd1 : DifferentiableAt ℝ (fun y : Vec3 => y j) x := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun r : ℝ => r ^ p) (x j) :=
    Real.differentiableAt_rpow_const_of_ne p hx
  rw [show (fun y : Vec3 => (y j) ^ p) =
    (fun r : ℝ => r ^ p) ∘ (fun y : Vec3 => y j) by rfl]
  rw [fderiv_comp x hd2 hd1]
  change (fderiv ℝ (fun r : ℝ => r ^ p) (x j))
      ((fderiv ℝ (fun y : Vec3 => y j) x) (basisVec i)) = _
  rw [vec3_coordDeriv]
  by_cases hji : j = i
  · subst i
    simp only [ContinuousLinearMap.proj_apply, basisVec_apply, ite_true]
    rw [fderiv_apply_one_eq_deriv, Real.deriv_rpow_const]
  · have hb : basisVec i j = 0 := by simp [basisVec_apply, hji]
    simp only [ContinuousLinearMap.proj_apply]
    rw [hb, map_zero]
    simp [hji]

private theorem tangentialQuadDeriv (x : Vec3) (i : Fin 3) :
    (fderiv ℝ (fun y : Vec3 => y 0 ^ 2 + y 1 ^ 2) x) (basisVec i) =
      (if i = 0 then 2 * x 0 else 0) + (if i = 1 then 2 * x 1 else 0) := by
  have h0 : DifferentiableAt ℝ (fun y : Vec3 => y 0 ^ 2) x := by fun_prop
  have h1 : DifferentiableAt ℝ (fun y : Vec3 => y 1 ^ 2) x := by fun_prop
  change (fderiv ℝ ((fun y : Vec3 => y 0 ^ 2) + (fun y => y 1 ^ 2)) x)
      (basisVec i) = _
  rw [fderiv_add h0 h1]
  simp only [add_apply]
  rw [vec3_coordSqDeriv x 0 i, vec3_coordSqDeriv x 1 i]
  fin_cases i <;> simp

/-- The explicit spatial gradient of the half-space phase on its domain. -/
theorem halfSpacePhase_spatialPartial (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) (i : Fin 3) :
    spatialPartial (halfSpacePhase a α) i z =
      if i = 2 then halfSpaceGradientTwo a α z else -z.1 i / (4 * z.2) := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hx2pos : 0 < z.1 2 := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hx2 : z.1 2 ≠ 0 := ne_of_gt hx2pos
  have hpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos htpos α)
  let c₁ : ℝ := -(8 * z.2)⁻¹
  let c₂ : ℝ := a * (1 - z.2) * (z.2 ^ α)⁻¹
  let Q : Vec3 → ℝ := fun y => y 0 ^ 2 + y 1 ^ 2
  let R : Vec3 → ℝ := fun y => y 2 ^ (2 * α)
  have hform : (fun y : Vec3 => halfSpacePhase a α (y, z.2)) =
      (fun y => c₁ • Q y + c₂ • R y) := by
    funext y
    dsimp [halfSpacePhase, c₁, c₂, Q, R]
    field_simp [ht0, hpow]
  change (fderiv ℝ (fun y : Vec3 => halfSpacePhase a α (y, z.2)) z.1) (basisVec i) = _
  rw [hform]
  change (fderiv ℝ ((fun y : Vec3 => c₁ • Q y) + (fun y => c₂ • R y)) z.1)
      (basisVec i) = _
  have hQ : DifferentiableAt ℝ Q z.1 := by fun_prop
  have hcoord : DifferentiableAt ℝ (fun y : Vec3 => y 2) z.1 := by fun_prop
  have hRpow : DifferentiableAt ℝ (fun r : ℝ => r ^ (2 * α)) (z.1 2) :=
    Real.differentiableAt_rpow_const_of_ne (2 * α) hx2
  have hR : DifferentiableAt ℝ R z.1 := by
    change DifferentiableAt ℝ ((fun r : ℝ => r ^ (2 * α)) ∘ (fun y : Vec3 => y 2)) z.1
    exact DifferentiableAt.comp (x := z.1) hRpow hcoord
  change fderiv ℝ (c₁ • Q + c₂ • R) z.1 (basisVec i) = _
  rw [fderiv_add (hQ.const_smul c₁) (hR.const_smul c₂)]
  change (fderiv ℝ (fun y => c₁ • Q y) z.1 +
      fderiv ℝ (fun y => c₂ • R y) z.1) (basisVec i) = _
  rw [fderiv_fun_const_smul hQ c₁, fderiv_fun_const_smul hR c₂]
  change c₁ * ((fderiv ℝ Q z.1) (basisVec i)) +
      c₂ * ((fderiv ℝ R z.1) (basisVec i)) = _
  rw [tangentialQuadDeriv z.1 i, coordRpowDeriv z.1 2 i (2 * α) hx2]
  fin_cases i <;> simp [halfSpaceGradientTwo, c₁, c₂] <;>
    field_simp [ht0, hpow] <;> ring


private theorem spatialPartial_coordRpow (c p : ℝ) (k j : Fin 3)
    {z : ParabolicPoint} (hx : z.1 k ≠ 0) :
    spatialPartial (fun w => c * w.1 k ^ p) j z =
      if k = j then c * p * z.1 k ^ (p - 1) else 0 := by
  change (fderiv ℝ (fun x : Vec3 => c • (x k ^ p)) z.1) (basisVec j) = _
  have hcoord : DifferentiableAt ℝ (fun x : Vec3 => x k) z.1 := by fun_prop
  have hp : DifferentiableAt ℝ (fun r : ℝ => r ^ p) (z.1 k) :=
    Real.differentiableAt_rpow_const_of_ne p hx
  have hpow : DifferentiableAt ℝ (fun x : Vec3 => (x k) ^ p) z.1 := by
    change DifferentiableAt ℝ ((fun r : ℝ => r ^ p) ∘ (fun x : Vec3 => x k)) z.1
    exact DifferentiableAt.comp (x := z.1) hp hcoord
  rw [fderiv_fun_const_smul hpow c]
  change c * ((fderiv ℝ (fun x : Vec3 => (x k) ^ p) z.1) (basisVec j)) = _
  rw [coordRpowDeriv z.1 k j p hx]
  by_cases hkj : k = j
  · subst j
    simp only [ite_true]
    ring
  · simp [hkj]

private theorem spatialPartial_coordLinear (c : ℝ) (k j : Fin 3)
    (z : ParabolicPoint) :
    spatialPartial (fun w => c * w.1 k) j z = if k = j then c else 0 := by
  change (fderiv ℝ (fun x : Vec3 => c • x k) z.1) (basisVec j) = _
  have hcoord : DifferentiableAt ℝ (fun x : Vec3 => x k) z.1 := by fun_prop
  rw [fderiv_fun_const_smul hcoord c]
  change c * ((fderiv ℝ (fun x : Vec3 => x k) z.1) (basisVec j)) = _
  rw [vec3_coordDeriv]
  by_cases hkj : k = j
  · subst j
    simp [basisVec_apply]
  · simp [hkj]

/-- The explicit spatial Hessian of the half-space phase on its domain. -/
theorem halfSpacePhase_spatialSecondPartial (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) (i j : Fin 3) :
    spatialSecondPartial (halfSpacePhase a α) i j z =
      if i = j then
        if i = 2 then
          2 * α * (2 * α - 1) * a * (1 - z.2) *
            z.1 2 ^ (2 * α - 2) / z.2 ^ α
        else -(1 / (4 * z.2))
      else 0 := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos htpos α)
  have hx2pos : 0 < z.1 2 := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hx2 : z.1 2 ≠ 0 := ne_of_gt hx2pos
  let cN : ℝ := 2 * α * a * (1 - z.2) * (z.2 ^ α)⁻¹
  let cT : ℝ := -(4 * z.2)⁻¹
  let F : Vec3 → ℝ := fun y =>
    if i = 2 then cN * y 2 ^ (2 * α - 1) else cT * y i
  have hopen : IsOpen {y : Vec3 | 1 < y 2} :=
    isOpen_lt continuous_const (continuous_apply 2)
  have hev : ∀ᶠ y : Vec3 in 𝓝 z.1, 1 < y 2 := hopen.eventually_mem hx
  have heq : (fun y : Vec3 => spatialPartial (halfSpacePhase a α) i (y, z.2)) =ᶠ[𝓝 z.1]
      F := by
    filter_upwards [hev] with y hy
    have hval := halfSpacePhase_spatialPartial a α
      (show ((y, z.2) : ParabolicPoint) ∈ halfSpaceDomain from ⟨hy, ht⟩) i
    by_cases hi : i = 2
    · subst i
      change spatialPartial (halfSpacePhase a α) 2 ((y, z.2) : ParabolicPoint) =
        2 * α * a * (1 - z.2) * y 2 ^ (2 * α - 1) / z.2 ^ α at hval
      change spatialPartial (halfSpacePhase a α) 2 ((y, z.2) : ParabolicPoint) =
        cN * y 2 ^ (2 * α - 1)
      rw [hval]
      dsimp [cN]
      field_simp [hpow]
    · simp only [Fin.isValue, hi, ↓reduceIte] at hval
      simp only [Fin.isValue, hi, ↓reduceIte, F]
      change spatialPartial (halfSpacePhase a α) i ((y, z.2) : ParabolicPoint) =
        -y i / (4 * z.2) at hval
      rw [hval]
      dsimp [cT]
      field_simp [ht0]
  have hFdiff : DifferentiableAt ℝ F z.1 := by
    by_cases hi : i = 2
    · subst i
      change DifferentiableAt ℝ (fun y : Vec3 => cN * y 2 ^ (2 * α - 1)) z.1
      fun_prop
    · simpa [F, hi] using
        (show DifferentiableAt ℝ (fun y : Vec3 => cT * y i) z.1 by fun_prop)
  have hFderiv := hFdiff.hasFDerivAt.congr_of_eventuallyEq heq
  have hfd : fderiv ℝ (fun y : Vec3 => spatialPartial (halfSpacePhase a α) i (y, z.2)) z.1 =
      fderiv ℝ F z.1 := hFderiv.fderiv
  change (fderiv ℝ (fun y : Vec3 => spatialPartial (halfSpacePhase a α) i (y, z.2)) z.1)
      (basisVec j) = _
  rw [hfd]
  change spatialPartial (fun w : ParabolicPoint =>
      if i = 2 then cN * w.1 2 ^ (2 * α - 1) else cT * w.1 i) j z = _
  by_cases hi : i = 2
  · subst i
    by_cases hj : j = 2
    · subst j
      change spatialPartial (fun w : ParabolicPoint => cN * w.1 2 ^ (2 * α - 1)) 2 z =
        2 * α * (2 * α - 1) * a * (1 - z.2) * z.1 2 ^ (2 * α - 2) / z.2 ^ α
      have h := spatialPartial_coordRpow cN (2 * α - 1) 2 2 (z := z) hx2
      have hexp : (2 * α - 1) - 1 = 2 * α - 2 := by ring
      rw [hexp] at h
      calc
        _ = cN * (2 * α - 1) * z.1 2 ^ (2 * α - 2) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
        _ = 2 * α * (2 * α - 1) * a * (1 - z.2) *
              z.1 2 ^ (2 * α - 2) / z.2 ^ α := by
          dsimp [cN]
          field_simp [hpow]
    · have h := spatialPartial_coordRpow cN (2 * α - 1) 2 j (z := z) hx2
      have hne : 2 ≠ j := Ne.symm hj
      simp only [Fin.isValue, hne, ↓reduceIte] at h ⊢
      exact h
  · simp only [Fin.isValue, hi, ↓reduceIte, one_div, mul_inv_rev] at ⊢
    by_cases hij : i = j
    · subst j
      simp at ⊢
      have h := spatialPartial_coordLinear cT i i z
      simpa [cT, ht0] using h
    · have h := spatialPartial_coordLinear cT i j z
      simp only [hij, ↓reduceIte] at h ⊢
      exact h


private theorem spatialPartial_const (c : ℝ) (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun _ : ParabolicPoint => c) i z = 0 := by
  change (fderiv ℝ (fun _ : Vec3 => c) z.1) (basisVec i) = 0
  simp

private theorem spatialPartial_eq_of_eventuallyEq
    {f g : ParabolicPoint → ℝ} {z : ParabolicPoint} (i : Fin 3)
    (heq : (fun x : Vec3 => f (x, z.2)) =ᶠ[𝓝 z.1]
      (fun x : Vec3 => g (x, z.2)))
    (hg : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) z.1) :
    spatialPartial f i z = spatialPartial g i z := by
  have hfd := hg.hasFDerivAt.congr_of_eventuallyEq heq
  change (fderiv ℝ (fun x : Vec3 => f (x, z.2)) z.1) (basisVec i) =
    (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)
  rw [hfd.fderiv]

private theorem halfSpacePhase_hessianGradient (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) (i j : Fin 3) :
    spatialPartial (fun y => spatialSecondPartial (halfSpacePhase a α) i i y) j z =
      if i = 2 ∧ j = 2 then
        2 * α * (2 * α - 1) * (2 * α - 2) * a * (1 - z.2) *
          z.1 2 ^ (2 * α - 3) / z.2 ^ α
      else 0 := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos htpos α)
  have hx2pos : 0 < z.1 2 := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hx2 : z.1 2 ≠ 0 := ne_of_gt hx2pos
  let cH : ℝ := 2 * α * (2 * α - 1) * a * (1 - z.2) * (z.2 ^ α)⁻¹
  let cT : ℝ := -(4 * z.2)⁻¹
  let H : ParabolicPoint → ℝ := fun w =>
    if i = 2 then cH * w.1 2 ^ (2 * α - 2) else cT
  have hopen : IsOpen {y : Vec3 | 1 < y 2} :=
    isOpen_lt continuous_const (continuous_apply 2)
  have hev : ∀ᶠ y : Vec3 in 𝓝 z.1, 1 < y 2 := hopen.eventually_mem hx
  have heq : (fun y : Vec3 => spatialSecondPartial (halfSpacePhase a α) i i (y, z.2)) =ᶠ[𝓝 z.1]
      (fun y => H (y, z.2)) := by
    filter_upwards [hev] with y hy
    have hval := halfSpacePhase_spatialSecondPartial a α
      (show ((y, z.2) : ParabolicPoint) ∈ halfSpaceDomain from ⟨hy, ht⟩) i i
    by_cases hi : i = 2
    · subst i
      change spatialSecondPartial (halfSpacePhase a α) 2 2 ((y, z.2) : ParabolicPoint) =
        2 * α * (2 * α - 1) * a * (1 - z.2) * y 2 ^ (2 * α - 2) / z.2 ^ α at hval
      change spatialSecondPartial (halfSpacePhase a α) 2 2 ((y, z.2) : ParabolicPoint) =
        cH * y 2 ^ (2 * α - 2)
      rw [hval]
      dsimp [cH]
      field_simp [hpow]
    · simp only [↓reduceIte, Fin.isValue, hi, one_div, mul_inv_rev] at hval
      simp only [Fin.isValue, hi, ↓reduceIte, H]
      rw [hval]
      dsimp [cT]
      field_simp [ht0]
  have hHdiff : DifferentiableAt ℝ (fun y : Vec3 => H (y, z.2)) z.1 := by
    by_cases hi : i = 2
    · subst i
      change DifferentiableAt ℝ (fun y : Vec3 => cH * y 2 ^ (2 * α - 2)) z.1
      fun_prop
    · simp [H, hi]
  have hpartial := spatialPartial_eq_of_eventuallyEq j heq hHdiff
  rw [hpartial]
  by_cases hi : i = 2
  · subst i
    by_cases hj : j = 2
    · subst j
      simp only [Fin.isValue, and_self, ↓reduceIte]
      change spatialPartial (fun w : ParabolicPoint => cH * w.1 2 ^ (2 * α - 2)) 2 z =
        2 * α * (2 * α - 1) * (2 * α - 2) * a * (1 - z.2) *
          z.1 2 ^ (2 * α - 3) / z.2 ^ α
      have h := spatialPartial_coordRpow cH (2 * α - 2) 2 2 (z := z) hx2
      have hexp : (2 * α - 2) - 1 = 2 * α - 3 := by ring
      rw [hexp] at h
      calc
        _ = cH * (2 * α - 2) * z.1 2 ^ (2 * α - 3) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
        _ = 2 * α * (2 * α - 1) * (2 * α - 2) * a * (1 - z.2) *
              z.1 2 ^ (2 * α - 3) / z.2 ^ α := by
          dsimp [cH]
          field_simp [hpow]
    · simp only [Fin.isValue, ↓reduceIte, hj, and_false, H] at ⊢
      have h := spatialPartial_coordRpow cH (2 * α - 2) 2 j (z := z) hx2
      simpa [Ne.symm hj] using h
  · simp only [Fin.isValue, hi, ↓reduceIte, false_and, H] at ⊢
    exact spatialPartial_const cT j z

/-- The explicit fourth spatial derivative of the diagonal Hessian entries. -/
theorem halfSpacePhase_spatialFourthDiagonal (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) (i j : Fin 3) :
    spatialSecondPartial
        (fun y => spatialSecondPartial (halfSpacePhase a α) i i y) j j z =
      if i = 2 ∧ j = 2 then
        2 * α * (2 * α - 1) * (2 * α - 2) * (2 * α - 3) * a * (1 - z.2) *
          z.1 2 ^ (2 * α - 4) / z.2 ^ α
      else 0 := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos htpos α)
  have hx2pos : 0 < z.1 2 := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hx2 : z.1 2 ≠ 0 := ne_of_gt hx2pos
  let cG : ℝ := 2 * α * (2 * α - 1) * (2 * α - 2) * a * (1 - z.2) *
    (z.2 ^ α)⁻¹
  let G : ParabolicPoint → ℝ := fun w =>
    if i = 2 ∧ j = 2 then cG * w.1 2 ^ (2 * α - 3) else 0
  have hopen : IsOpen {y : Vec3 | 1 < y 2} :=
    isOpen_lt continuous_const (continuous_apply 2)
  have hev : ∀ᶠ y : Vec3 in 𝓝 z.1, 1 < y 2 := hopen.eventually_mem hx
  have heq :
      (fun y : Vec3 => spatialPartial
        (fun w => spatialSecondPartial (halfSpacePhase a α) i i w) j (y, z.2)) =ᶠ[𝓝 z.1]
      (fun y => G (y, z.2)) := by
    filter_upwards [hev] with y hy
    have hval := halfSpacePhase_hessianGradient a α
      (show ((y, z.2) : ParabolicPoint) ∈ halfSpaceDomain from ⟨hy, ht⟩) i j
    by_cases hi : i = 2
    · subst i
      by_cases hj : j = 2
      · simp only [Fin.isValue, hj, and_self, ↓reduceIte, G] at hval ⊢
        rw [hval]
        dsimp [cG]
        field_simp [hpow]
      · simp only [Fin.isValue, hj, and_false, ↓reduceIte, G] at hval ⊢
        exact hval
    · simp only [Fin.isValue, hi, false_and, ↓reduceIte, G] at hval ⊢
      exact hval
  have hGdiff : DifferentiableAt ℝ (fun y : Vec3 => G (y, z.2)) z.1 := by
    by_cases hi : i = 2
    · subst i
      by_cases hj : j = 2
      · subst j
        change DifferentiableAt ℝ (fun y : Vec3 => cG * y 2 ^ (2 * α - 3)) z.1
        fun_prop
      · simp [G, hj]
    · simp [G, hi]
  have hpartial := spatialPartial_eq_of_eventuallyEq j heq hGdiff
  change spatialPartial
    (fun y => spatialPartial (fun w => spatialSecondPartial (halfSpacePhase a α) i i w) j y)
    j z = _
  rw [hpartial]
  by_cases hi : i = 2
  · subst i
    by_cases hj : j = 2
    · subst j
      simp only [Fin.isValue, and_self, ↓reduceIte]
      change spatialPartial (fun w : ParabolicPoint => cG * w.1 2 ^ (2 * α - 3)) 2 z =
        2 * α * (2 * α - 1) * (2 * α - 2) * (2 * α - 3) * a * (1 - z.2) *
          z.1 2 ^ (2 * α - 4) / z.2 ^ α
      have h := spatialPartial_coordRpow cG (2 * α - 3) 2 2 (z := z) hx2
      have hexp : (2 * α - 3) - 1 = 2 * α - 4 := by ring
      rw [hexp] at h
      calc
        _ = cG * (2 * α - 3) * z.1 2 ^ (2 * α - 4) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
        _ = 2 * α * (2 * α - 1) * (2 * α - 2) * (2 * α - 3) * a * (1 - z.2) *
              z.1 2 ^ (2 * α - 4) / z.2 ^ α := by
          dsimp [cG]
          field_simp [hpow]
    · have hGzero : G = fun _ : ParabolicPoint => 0 := by
        funext w
        simp [G, hj]
      rw [hGzero]
      simpa [hj] using spatialPartial_const 0 j z
  · have hGzero : G = fun _ : ParabolicPoint => 0 := by
      funext w
      simp [G, hi]
    rw [hGzero]
    simpa [hi] using spatialPartial_const 0 j z


private theorem timePartial_eq_deriv (f : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    timePartial f z = deriv (fun s : ℝ => f (z.1, s)) z.2 := by
  change (fderiv ℝ (fun s : ℝ => f (z.1, s)) z.2) 1 = _
  exact fderiv_apply_one_eq_deriv

/-- The first time derivative of the half-space phase on its domain. -/
theorem halfSpacePhase_timePartial (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) :
    timePartial (halfSpacePhase a α) z =
      ((z.1 0 ^ 2 + z.1 1 ^ 2) / 8) * z.2 ^ (-2 : ℝ) -
        a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 1) *
          (α + (1 - α) * z.2) := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  let Q : ℝ := z.1 0 ^ 2 + z.1 1 ^ 2
  let X : ℝ := z.1 2 ^ (2 * α)
  have hpos : ∀ᶠ s : ℝ in 𝓝 z.2, 0 < s := isOpen_Ioi.eventually_mem htpos
  have hEq : (fun s : ℝ => halfSpacePhase a α (z.1, s)) =ᶠ[𝓝 z.2]
      (fun s => -(Q / 8) * s ^ (-1 : ℝ) + a * X * (1 - s) * s ^ (-α : ℝ)) := by
    filter_upwards [hpos] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hpow : s ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs α)
    have hinv : s ^ (-1 : ℝ) = s⁻¹ := by
      rw [Real.rpow_neg hs.le (1 : ℝ), Real.rpow_one]
    have hpowneg : s ^ (-α : ℝ) = (s ^ α)⁻¹ := by
      rw [Real.rpow_neg hs.le α]
    have hgauss : -(Q) / (8 * s) = -(Q / 8) * s ^ (-1 : ℝ) := by
      calc
        -(Q) / (8 * s) = -(Q / 8) / s := by field_simp [hs0]
        _ = -(Q / 8) * s ^ (-1 : ℝ) := by
          rw [div_eq_mul_inv, ← hinv]
    have hnormal : a * (1 - s) * X / s ^ α = a * X * (1 - s) * s ^ (-α : ℝ) := by
      calc
        a * (1 - s) * X / s ^ α = a * X * (1 - s) * (s ^ α)⁻¹ := by
          field_simp [hpow]
        _ = a * X * (1 - s) * s ^ (-α : ℝ) := by rw [← hpowneg]
    dsimp [halfSpacePhase, Q, X]
    rw [hgauss, hnormal]
  have hInv : HasDerivAt (fun s : ℝ => s ^ (-1 : ℝ))
      ((-1 : ℝ) * z.2 ^ (-2 : ℝ)) z.2 := by
    convert Real.hasDerivAt_rpow_const (x := z.2) (p := (-1 : ℝ)) (Or.inl ht0)
      using 1
    congr 2
    ring
  have hLin : HasDerivAt (fun s : ℝ => 1 - s) (-1) z.2 := by
    convert (hasDerivAt_id z.2).const_sub 1 using 1
    norm_num
  have hPow : HasDerivAt (fun s : ℝ => s ^ (-α : ℝ))
      ((-α) * z.2 ^ (-α - 1)) z.2 :=
    Real.hasDerivAt_rpow_const (x := z.2) (p := (-α : ℝ)) (Or.inl ht0)
  have hModel : HasDerivAt
      (fun s : ℝ => -(Q / 8) * s ^ (-1 : ℝ) + a * X * (1 - s) * s ^ (-α : ℝ))
      (((Q / 8) * z.2 ^ (-2 : ℝ)) -
        a * X * z.2 ^ (-α - 1) * (α + (1 - α) * z.2)) z.2 := by
    have hTan := HasDerivAt.const_mul (-(Q / 8)) hInv
    have hNormal := HasDerivAt.const_mul (a * X) (hLin.mul hPow)
    have hsum := hTan.add hNormal
    convert hsum using 1
    · funext s
      dsimp
      ring
    · have hrpow : z.2 ^ (-α) = z.2 ^ (-α - 1) * z.2 := by
        calc
          z.2 ^ (-α) = z.2 ^ ((-α - 1) + 1) := by congr 1; ring
          _ = z.2 ^ (-α - 1) * z.2 ^ (1 : ℝ) := Real.rpow_add htpos _ _
          _ = z.2 ^ (-α - 1) * z.2 := by rw [Real.rpow_one]
      rw [hrpow]
      ring
  have hPhase := hModel.congr_of_eventuallyEq hEq
  rw [timePartial_eq_deriv]
  exact hPhase.deriv


/-- The second time derivative of the half-space phase on its domain. -/
theorem halfSpacePhase_timeSecondPartial (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) :
    timePartial (fun y => timePartial (halfSpacePhase a α) y) z =
      -((z.1 0 ^ 2 + z.1 1 ^ 2) / 4) * z.2 ^ (-3 : ℝ) +
        a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 2) *
          (α * (α + 1) + α * (1 - α) * z.2) := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  let Q : ℝ := z.1 0 ^ 2 + z.1 1 ^ 2
  let X : ℝ := z.1 2 ^ (2 * α)
  let F : ℝ → ℝ := fun s =>
    (Q / 8) * s ^ (-2 : ℝ) -
      a * X * s ^ (-α - 1) * (α + (1 - α) * s)
  have htime : ∀ᶠ s : ℝ in 𝓝 z.2, s ∈ Ioo 0 1 :=
    isOpen_Ioo.eventually_mem ht
  have hEq : (fun s : ℝ => timePartial (halfSpacePhase a α) (z.1, s)) =ᶠ[𝓝 z.2] F := by
    filter_upwards [htime] with s hs
    have hval := halfSpacePhase_timePartial a α
      (show ((z.1, s) : ParabolicPoint) ∈ halfSpaceDomain from ⟨hx, hs⟩)
    simpa [F, Q, X] using hval
  have hPow2 : HasDerivAt (fun s : ℝ => s ^ (-2 : ℝ))
      ((-2 : ℝ) * z.2 ^ (-3 : ℝ)) z.2 := by
    convert Real.hasDerivAt_rpow_const (x := z.2) (p := (-2 : ℝ)) (Or.inl ht0)
      using 1
    congr 2
    ring
  have hPowQ : HasDerivAt (fun s : ℝ => s ^ (-α - 1))
      ((-α - 1) * z.2 ^ ((-α - 1) - 1)) z.2 :=
    Real.hasDerivAt_rpow_const (x := z.2) (p := (-α - 1)) (Or.inl ht0)
  have hC : HasDerivAt (fun s : ℝ => α + (1 - α) * s) (1 - α) z.2 := by
    have hlin := HasDerivAt.const_mul (1 - α) (hasDerivAt_id z.2)
    have hconst : HasDerivAt (fun _ : ℝ => α) 0 z.2 := hasDerivAt_const z.2 α
    convert hconst.add hlin using 1
    · funext s
      rfl
    · simp
  have hModel : HasDerivAt F
      (-(Q / 4) * z.2 ^ (-3 : ℝ) +
        a * X * z.2 ^ (-α - 2) *
          (α * (α + 1) + α * (1 - α) * z.2)) z.2 := by
    have hTan := HasDerivAt.const_mul (Q / 8) hPow2
    have hNormal := HasDerivAt.const_mul (a * X) (hPowQ.mul hC)
    have hsum := hTan.sub hNormal
    convert hsum using 1
    · funext s
      dsimp [F]
      ring
    · have hexp : (-α - 1) - 1 = -α - 2 := by ring
      have hrpow : z.2 ^ (-α - 1) = z.2 ^ ((-α - 1) - 1) * z.2 := by
        calc
          z.2 ^ (-α - 1) = z.2 ^ (((-α - 1) - 1) + 1) := by congr 1; ring
          _ = z.2 ^ ((-α - 1) - 1) * z.2 ^ (1 : ℝ) := Real.rpow_add htpos _ _
          _ = z.2 ^ ((-α - 1) - 1) * z.2 := by rw [Real.rpow_one]
      rw [hexp, hrpow]
      ring_nf
  have hDerivative := hModel.congr_of_eventuallyEq hEq
  rw [timePartial_eq_deriv]
  exact hDerivative.deriv

/-- The time derivative of every spatial component of the half-space gradient. -/
theorem halfSpacePhase_timeSpatialPartial (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) (i : Fin 3) :
    timePartial (fun y => spatialPartial (halfSpacePhase a α) i y) z =
      if i = 2 then
        -2 * α * a * z.1 2 ^ (2 * α - 1) * z.2 ^ (-α - 1) *
          (α + (1 - α) * z.2)
      else z.1 i / 4 * z.2 ^ (-2 : ℝ) := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hx2pos : 0 < z.1 2 := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hx2 : z.1 2 ≠ 0 := ne_of_gt hx2pos
  let nC : ℝ := 2 * α * a * z.1 2 ^ (2 * α - 1)
  let F : ℝ → ℝ := fun s =>
    if i = 2 then nC * (1 - s) * s ^ (-α : ℝ)
    else (-z.1 i / 4) * s ^ (-1 : ℝ)
  have htime : ∀ᶠ s : ℝ in 𝓝 z.2, s ∈ Ioo 0 1 :=
    isOpen_Ioo.eventually_mem ht
  have hEq : (fun s : ℝ => spatialPartial (halfSpacePhase a α) i (z.1, s)) =ᶠ[𝓝 z.2] F := by
    filter_upwards [htime] with s hs
    have hval := halfSpacePhase_spatialPartial a α
      (show ((z.1, s) : ParabolicPoint) ∈ halfSpaceDomain from ⟨hx, hs⟩) i
    by_cases hi : i = 2
    · subst i
      change spatialPartial (halfSpacePhase a α) 2 ((z.1, s) : ParabolicPoint) =
        2 * α * a * (1 - s) * z.1 2 ^ (2 * α - 1) / s ^ α at hval
      simp only [F, ite_true]
      have hpowneg : s ^ (-α : ℝ) = (s ^ α)⁻¹ :=
        Real.rpow_neg (le_of_lt hs.1) α
      rw [hval]
      dsimp [nC]
      rw [hpowneg]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hs.1 α)]
    · simp only [Fin.isValue, hi, ↓reduceIte] at hval
      simp only [Fin.isValue, hi, ↓reduceIte, F]
      change spatialPartial (halfSpacePhase a α) i ((z.1, s) : ParabolicPoint) =
        -z.1 i / (4 * s) at hval
      rw [hval]
      have hinv : s ^ (-1 : ℝ) = s⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hs.1) (1 : ℝ), Real.rpow_one]
      rw [hinv]
      field_simp [ne_of_gt hs.1]
  have hLin : HasDerivAt (fun s : ℝ => 1 - s) (-1) z.2 := by
    convert (hasDerivAt_id z.2).const_sub 1 using 1
    norm_num
  have hPow : HasDerivAt (fun s : ℝ => s ^ (-α : ℝ))
      ((-α) * z.2 ^ (-α - 1)) z.2 :=
    Real.hasDerivAt_rpow_const (x := z.2) (p := (-α : ℝ)) (Or.inl ht0)
  have hInv : HasDerivAt (fun s : ℝ => s ^ (-1 : ℝ))
      ((-1 : ℝ) * z.2 ^ (-2 : ℝ)) z.2 := by
    convert Real.hasDerivAt_rpow_const (x := z.2) (p := (-1 : ℝ)) (Or.inl ht0)
      using 1
    congr 2
    ring
  have hModel : HasDerivAt F
      (if i = 2 then
        -nC * z.2 ^ (-α - 1) * (α + (1 - α) * z.2)
      else z.1 i / 4 * z.2 ^ (-2 : ℝ)) z.2 := by
    by_cases hi : i = 2
    · subst i
      simp only [F, ite_true]
      have hsum := (HasDerivAt.const_mul nC (hLin.mul hPow))
      have hrpow : z.2 ^ (-α) = z.2 ^ (-α - 1) * z.2 := by
        calc
          z.2 ^ (-α) = z.2 ^ ((-α - 1) + 1) := by congr 1; ring
          _ = z.2 ^ (-α - 1) * z.2 ^ (1 : ℝ) := Real.rpow_add htpos _ _
          _ = z.2 ^ (-α - 1) * z.2 := by rw [Real.rpow_one]
      convert hsum using 1
      · funext s
        dsimp
        ring
      · rw [hrpow]
        ring_nf
    · simp only [Fin.isValue, hi, ↓reduceIte, Real.rpow_neg_ofNat,
      Int.reduceNeg, zpow_neg, zpow_ofNat, F]
      have hTan := HasDerivAt.const_mul (-z.1 i / 4) hInv
      convert hTan using 1
      rw [Real.rpow_neg (le_of_lt htpos) (2 : ℝ)]
      field_simp [ht0]
      simp
  have hDerivative := hModel.congr_of_eventuallyEq hEq
  rw [timePartial_eq_deriv]
  simpa [nC] using hDerivative.deriv

end ESS
