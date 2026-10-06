/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceScaling
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallTime

public section
open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- Uniform slice `L²` and gradient `L²` control gives a uniform
space-time `L^(10/3)` bound on a ball cylinder. -/
theorem blowup_uniform_tenThirds_scalar
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    (J : Set ℝ) (hJ : OrdConnected J)
    (g : ℕ → Vec3 × ℝ → ℝ)
    (Dg : ℕ → Vec3 × ℝ → Vec3)
    (hgm : ∀ k, AEStronglyMeasurable (g k)
      (volume.restrict (vec3Ball x₀ r ×ˢ J)))
    (hDgm : ∀ k, AEStronglyMeasurable (Dg k)
      (volume.restrict (vec3Ball x₀ r ×ˢ J)))
    (hSlice : ∀ k, ∀ᵐ s ∂volume.restrict J,
      ∃ v : CKN.H1Function (vec3Ball x₀ r),
        (fun x => g k (x,s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
        (fun x => Dg k (x,s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad)
    (hg₂ : ∀ k, MemLp (g k) 2
      (volume.restrict (vec3Ball x₀ r ×ˢ J)))
    (hDg₂ : ∀ k, MemLp (Dg k) 2
      (volume.restrict (vec3Ball x₀ r ×ˢ J)))
    (A G : ℝ≥0∞) (hA : A < ⊤) (hG : G < ⊤)
    (hAsup : ∀ k,
      essSup (fun s => eLpNorm (fun x => g k (x,s)) 2
        (volume.restrict (vec3Ball x₀ r)))
        (volume.restrict J) ≤ A)
    (hGsup : ∀ k,
      eLpNorm (fun z => vec3EuclideanNorm (Dg k z)) 2
        (volume.restrict (vec3Ball x₀ r ×ˢ J)) ≤ G)
    (hJfin : volume J < ⊤) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ k, MemLp (g k) (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball x₀ r ×ˢ J)) ∧
        eLpNorm (g k) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (vec3Ball x₀ r ×ˢ J)) ^ (10 / 3 : ℝ) ≤ K := by
  obtain ⟨C, hC, hmain⟩ := CKN.ball_time_sobolev
  let K : ℝ≥0∞ := ENNReal.ofReal C *
    (A ^ (4 / 3 : ℝ) * G ^ (2 : ℝ) +
      ENNReal.ofReal (r ^ (-2 : ℝ)) * A ^ (10 / 3 : ℝ) * volume J)
  have hK : K < ⊤ := by
    dsimp [K]
    have hA4 : A ^ (4 / 3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne
    have hG2 : G ^ (2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG.ne
    have hA10 : A ^ (10 / 3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hA4 hG2,
        ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA10) hJfin⟩)
  refine ⟨K, hK, ?_⟩
  intro k
  let Aₖ := essSup (fun s => eLpNorm (fun x => g k (x,s)) 2
    (volume.restrict (vec3Ball x₀ r))) (volume.restrict J)
  have hAk : Aₖ < ⊤ := (hAsup k).trans_lt hA
  obtain ⟨hmem, hbound⟩ := hmain x₀ r hr J hJ (g k) (Dg k)
    (hgm k) (hDgm k) (hSlice k) (hg₂ k) (hDg₂ k) hAk
  refine ⟨hmem, hbound.trans ?_⟩
  dsimp [K]
  gcongr
  · exact hAsup k
  · exact hGsup k
  · exact hAsup k

end ESS
