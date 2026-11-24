/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxObstacle

/-! # Joint decreasing genuine smooth approximations of a maximum

The complete mathematical statement and proof preceded this file.
ROOT10 is strictly excluded from the fixed C90 batch.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.JointDecreasingSmoothMax

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax BedfordTaylor

variable {n : ℕ}

private theorem scaledSmoothMax_joint_mono {ε : ℝ} (hε : 0 < ε)
    {f f' g g' : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : f z ≤ f' z) (hg : g z ≤ g' z) :
    BedfordTaylor.scaledSmoothMax ε f g z ≤ BedfordTaylor.scaledSmoothMax ε f' g' z := by
  rw [BedfordTaylor.scaledSmoothMax_eq_smul hε, BedfordTaylor.scaledSmoothMax_eq_smul hε]
  change ε * smoothMax (ε⁻¹ • f) (ε⁻¹ • g) z ≤
    ε * smoothMax (ε⁻¹ • f') (ε⁻¹ • g') z
  refine mul_le_mul_of_nonneg_left (smoothMax_mono ?_ ?_) hε.le
  · simpa only [Pi.smul_apply, smul_eq_mul] using
      mul_le_mul_of_nonneg_left hf (inv_nonneg.2 hε.le)
  · simpa only [Pi.smul_apply, smul_eq_mul] using
      mul_le_mul_of_nonneg_left hg (inv_nonneg.2 hε.le)

/-- Two genuine decreasing smooth approximations produce a genuine approximation
of their maximum, with both branches varying at every stage. -/
theorem isDecApprox_joint_scaledSmoothMax {U : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} {F G : ℕ → ComplexModel n → ℝ}
    (hF : IsDecApprox U u F) (hG : IsDecApprox U v G) :
    IsDecApprox U (fun z ↦ max (u z) (v z))
      (fun j ↦ BedfordTaylor.scaledSmoothMax (maxScale j) (F j) (G j)) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun j ↦ ⟨?_, fun z hz ↦ ?_⟩, fun z hz j l hjl ↦ ?_,
    fun z hz ↦ ?_, fun K hK hKU ↦ ?_⟩
  · exact (hG.1 j).1.add (contDiffOn_const.mul (contDiff_posPart.comp_contDiffOn
      (((hF.1 j).1.sub (hG.1 j).1).div_const _)))
  · exact complexHessian_scaledSmoothMax_posSemidef
      (((hF.1 j).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
      (((hG.1 j).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
      ((hF.1 j).2 z hz) ((hG.1 j).2 z hz) (maxScale_pos j)
  · have hbranches := scaledSmoothMax_joint_mono (maxScale_pos l)
      (hF.2.1 z hz hjl) (hG.2.1 z hz hjl)
    have hscale := scaledPosPart_mono_left (maxScale_pos l)
      (maxScale_antitone hjl) (F j z - G j z)
    refine hbranches.trans ?_
    change G j z + scaledPosPart (maxScale l) (F j z - G j z) ≤
      G j z + scaledPosPart (maxScale j) (F j z - G j z)
    linarith
  · have hlim : Tendsto (fun j ↦ max (F j z) (G j z)) atTop (𝓝 (max (u z) (v z))) :=
      (hF.2.2.1 z hz).max (hG.2.2.1 z hz)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim
      (by simpa only [add_zero] using hlim.add tendsto_maxScale) (fun j ↦ ?_) (fun j ↦ ?_)
    · rw [max_eq_add_max_sub (F j z) (G j z)]
      change G j z + max (F j z - G j z) 0 ≤
        G j z + scaledPosPart (maxScale j) (F j z - G j z)
      have := max_le (le_scaledPosPart (maxScale_pos j) (F j z - G j z))
        (scaledPosPart_nonneg (maxScale_pos j).le (F j z - G j z))
      linarith
    · rw [max_eq_add_max_sub (F j z) (G j z)]
      change G j z + scaledPosPart (maxScale j) (F j z - G j z) ≤
        G j z + max (F j z - G j z) 0 + maxScale j
      have := scaledPosPart_le_max_add (maxScale_pos j) (F j z - G j z)
      linarith
  · obtain ⟨m, hm⟩ := hF.2.2.2 K hK hKU
    refine ⟨m, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hm ⟨z, hz, rfl⟩).trans (le_max_left _ _)

end SGPT.Foundations.Analysis.Pending.JointDecreasingSmoothMax
