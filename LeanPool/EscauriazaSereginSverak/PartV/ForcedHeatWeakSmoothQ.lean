/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughWeak

/-!
# Weak identities of smooth forced heat responses on the slab

For a smooth compactly supported tensor supported in positive times and a
smooth test function compactly supported in the slab `Q_τ`, the forced heat
response satisfies on `Q_τ`, in the CKN derivative conventions, the weak
gradient identity `∫ Z_i ∂_j φ = -∫ ∂_j Z_i φ` and the weak heat equation
`∫ -Z_i ∂_t φ + ∑_j ∂_j Z_i ∂_j φ + ∑_j G_ij ∂_j φ = 0` of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The spatial derivatives of a smooth forced heat response are differences of
those of its tensors: `∂_j (Z(G) - Z(G'))_i = ∂_j Z(G)_i - ∂_j Z(G')_i`. -/
theorem spatialPartial_forcedHeat_sub {G G' : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    (hG' : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G' i j p))
    (hGc' : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G' i j p))
    (i j : Fin 3) (z : ParabolicPoint) :
    CKN.spatialPartial (fun w => forcedHeat (G - G') w i) j z =
      CKN.spatialPartial (fun w => forcedHeat G w i) j z -
        CKN.spatialPartial (fun w => forcedHeat G' w i) j z := by
  have hfun : (fun w => forcedHeat (G - G') w i) =
      fun w => forcedHeat G w i - forcedHeat G' w i := by
    funext w
    have hneg : G - G' = G + (-1 : ℝ) • G' := by
      funext a b c
      simp [sub_eq_add_neg]
    rw [hneg, forcedHeat_add (forcedHeat_integrand_integrable hG hGc w) (fun a b => by
      have h := (forcedHeat_integrand_integrable hG' hGc' w a b).const_mul (-1 : ℝ)
      refine h.congr (Eventually.of_forall fun p => ?_)
      change -1 * (heatKernelSpaceDerivative p.1 p.2 b * G' a b (w.1 - p.1, w.2 - p.2)) =
        heatKernelSpaceDerivative p.1 p.2 b * (-1 * G' a b (w.1 - p.1, w.2 - p.2))
      ring), forcedHeat_smul]
    simp [sub_eq_add_neg]
  rw [hfun]
  have hd (H : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
      (hH : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => H i j p))
      (hHc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => H i j p)) :
      DifferentiableAt ℝ (fun x : Vec3 => forcedHeat H (x, z.2) i) z.1 := by
    have hsl : Differentiable ℝ (fun x : Vec3 => ((x, z.2) : Vec3 × ℝ)) :=
      differentiable_id.prodMk (differentiable_const _)
    have hF : Differentiable ℝ (fun p : Vec3 × ℝ => forcedHeat H p i) :=
      (forcedHeat_contDiff hH hHc i).differentiable (by simp)
    exact (hF.comp hsl) z.1
  change fderiv ℝ (fun x : Vec3 => forcedHeat G (x, z.2) i - forcedHeat G' (x, z.2) i) z.1
      (CKN.basisVec j) = _
  rw [fderiv_fun_sub (hd G hG hGc) (hd G' hG' hGc')]
  rfl

/-- The weak gradient identity and the weak heat equation on the slab for the
forced heat response of a smooth compactly supported tensor, against smooth
tests compactly supported in the slab. -/
theorem forcedHeat_smooth_weak_slab {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    {τ : ℝ} {φ : ParabolicPoint → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p))
    (hφc : HasCompactSupport (fun p : Vec3 × ℝ => φ p))
    (hφQ : tsupport (fun p : Vec3 × ℝ => φ p) ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 τ)
    (i : Fin 3) :
    (∀ j, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        forcedHeat G z i * CKN.spatialPartial φ j z =
      -∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        CKN.spatialPartial (fun w => forcedHeat G w i) j z * φ z) ∧
    ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
      (-(forcedHeat G z i * CKN.timePartial φ z) +
        ∑ j : Fin 3, CKN.spatialPartial (fun w => forcedHeat G w i) j z *
          CKN.spatialPartial φ j z +
        ∑ j : Fin 3, G i j z * CKN.spatialPartial φ j z) = 0 := by
  let ψ : Vec3 × ℝ → ℝ := fun p => φ p
  let g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j p => G i j p
  let U : Vec3 × ℝ → ℝ := causalHeatConv (vecTimeDiv g i)
  have hU : ContDiff ℝ (⊤ : ℕ∞) U :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hG i) (vecTimeDiv_hasCompactSupport hGc i)
  have hZ (z : ParabolicPoint) : forcedHeat G z i = U z :=
    forcedHeat_eq_causalHeatConv_vecTimeDiv hG hGc i z
  have hDZ (j : Fin 3) (z : ParabolicPoint) :
      CKN.spatialPartial (fun w => forcedHeat G w i) j z = fderiv ℝ U z (CKN.basisVec j, 0) :=
    spatialPartial_forcedHeat_eq hG hGc i j z
  have hDφ (j : Fin 3) (z : ParabolicPoint) :
      CKN.spatialPartial φ j z = fderiv ℝ ψ z (CKN.basisVec j, 0) :=
    spatialPartial_eq_fderiv_apply hφ j z.1 z.2
  have hTφ (z : ParabolicPoint) : CKN.timePartial φ z = fderiv ℝ ψ z (0, 1) :=
    timePartial_eq_fderiv_apply hφ z.1 z.2
  -- vanishing outside the slab
  have hout (z : Vec3 × ℝ) (hz : z ∉ (Set.univ : Set Vec3) ×ˢ Ioo 0 τ) :
      ψ z = 0 ∧ fderiv ℝ ψ z = 0 := by
    have hnot : z ∉ tsupport ψ := fun h => hz (hφQ h)
    refine ⟨image_eq_zero_of_notMem_tsupport hnot, ?_⟩
    by_contra hne
    exact hnot (support_fderiv_subset (𝕜 := ℝ) hne)
  constructor
  · intro j
    have hkey := integral_mul_fderiv_test (hU.of_le (by simp)) (hφ.of_le (by simp)) hφc
      (CKN.basisVec j, 0)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have h0 := (hout z hz).2
        simp [hDφ, h0]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have h0 := (hout z hz).1
        change _ * ψ z = 0
        rw [h0, mul_zero])]
    have e1 : (∫ z : ParabolicPoint, forcedHeat G z i * CKN.spatialPartial φ j z) =
        ∫ z : ParabolicPoint, U z * fderiv ℝ ψ z (CKN.basisVec j, 0) :=
      integral_congr_ae (Eventually.of_forall fun z => congrArg₂ (· * ·) (hZ z) (hDφ j z))
    have e2 : (∫ z : ParabolicPoint, CKN.spatialPartial (fun w => forcedHeat G w i) j z * φ z) =
        ∫ z : ParabolicPoint, fderiv ℝ U z (CKN.basisVec j, 0) * ψ z :=
      integral_congr_ae (Eventually.of_forall fun z => congrArg (· * φ z) (hDZ j z))
    rw [e1, e2]
    exact hkey
  · have hkey := response_weak_equation hG hGc hφ hφc i
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have h0 := (hout z hz).2
      simp [hTφ, hDφ, h0])]
    have e : (∫ z : ParabolicPoint,
        (-(forcedHeat G z i * CKN.timePartial φ z) +
          ∑ j : Fin 3, CKN.spatialPartial (fun w => forcedHeat G w i) j z *
            CKN.spatialPartial φ j z +
          ∑ j : Fin 3, G i j z * CKN.spatialPartial φ j z)) =
        ∫ z : ParabolicPoint, (-(U z * fderiv ℝ ψ z (0, 1)) +
          ∑ j : Fin 3, fderiv ℝ U z (CKN.basisVec j, 0) * fderiv ℝ ψ z (CKN.basisVec j, 0) +
          ∑ j : Fin 3, g i j z * fderiv ℝ ψ z (CKN.basisVec j, 0)) :=
      integral_congr_ae (Eventually.of_forall fun z => by
        simp only [hDZ, hTφ, hDφ]
        simp only [hZ]
        rfl)
    rw [e]
    exact hkey

end ESS

end
