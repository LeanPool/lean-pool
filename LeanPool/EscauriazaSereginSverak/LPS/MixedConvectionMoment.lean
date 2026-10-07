/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormSumMoment
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab

/-!
# Advective derivatives in mixed norms

Products of an energy-class velocity component and a weak-gradient component,
followed by the finite coordinate sum, retain the expected mixed exponents.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Each row of the advective derivative has the mixed norm obtained by
combining the velocity mixed norm with the space-time `L²` gradient norm. -/
theorem lps_mixed_convection_moment
    {T px pt qx qt : ℝ}
    (hpx : 1 ≤ px) (hpt : 1 ≤ pt) (hqx : 1 ≤ qx) (hqt : 1 ≤ qt)
    (hSpace : px⁻¹ + (2 : ℝ)⁻¹ = qx⁻¹)
    (hTime : pt⁻¹ + (2 : ℝ)⁻¹ = qt⁻¹)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    (hw : AEStronglyMeasurable w
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hDw : AEStronglyMeasurable Dw
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hwSlice : ∀ j, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => w (x,t) j) (ENNReal.ofReal px) volume)
    (hwMoment : ∀ j, (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => w (x,t) j) (ENNReal.ofReal px) volume ^ pt) < ⊤)
    (hDwSpaceTime : MemLp Dw 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) :
    ∀ k : Fin 3,
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        MemLp (fun x : Vec3 => ∑ j : Fin 3, w (x,t) j * Dw (x,t) k j)
          (ENNReal.ofReal qx) volume) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => ∑ j : Fin 3, w (x,t) j * Dw (x,t) k j)
          (ENNReal.ofReal qx) volume ^ qt) < ⊤ := by
  have hDwComponent (k j : Fin 3) :=
    lps_mixed_two_moment_of_memLp_two ((hDwSpaceTime.eval k).eval j)
  intro k
  have hProduct (j : Fin 3) :
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        MemLp (fun x : Vec3 => w (x,t) j * Dw (x,t) k j)
          (ENNReal.ofReal qx) volume) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => w (x,t) j * Dw (x,t) k j)
          (ENNReal.ofReal qx) volume ^ qt) < ⊤ := by
    have hwj : AEStronglyMeasurable (fun z : ParabolicPoint => w z j)
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
      (continuous_apply j).comp_aestronglyMeasurable hw
    have hDk : AEStronglyMeasurable (fun z : ParabolicPoint => Dw z k)
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
      (continuous_apply k).comp_aestronglyMeasurable hDw
    have hDkj : AEStronglyMeasurable (fun z : ParabolicPoint => Dw z k j)
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
      (continuous_apply j).comp_aestronglyMeasurable hDk
    have hDwSlice' : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        MemLp (fun x : Vec3 => Dw (x,t) k j) (ENNReal.ofReal (2 : ℝ)) volume := by
      simpa using (hDwComponent k j).1
    have hDwMoment' : (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => Dw (x,t) k j) (ENNReal.ofReal (2 : ℝ))
          volume ^ (2 : ℝ)) < ⊤ := by
      simpa using (hDwComponent k j).2
    exact @lps_mixed_product_moment T px (2 : ℝ) qx pt (2 : ℝ) qt
      hpx (by norm_num) hqx hpt (by norm_num) hqt hSpace hTime
      (fun z : ParabolicPoint => w z j) (fun z : ParabolicPoint => Dw z k j)
      hwj hDkj
      (hwSlice j) hDwSlice' (hwMoment j) hDwMoment'
  exact @lps_mixed_sum_three_moment T qt qx
    (fun j z => w z j * Dw z k j) hqt hqx
    (by
      intro j
      have hwj : AEStronglyMeasurable (fun z : ParabolicPoint => w z j)
          (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
        (continuous_apply j).comp_aestronglyMeasurable hw
      have hDk : AEStronglyMeasurable (fun z : ParabolicPoint => Dw z k)
          (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
        (continuous_apply k).comp_aestronglyMeasurable hDw
      have hDkj : AEStronglyMeasurable (fun z : ParabolicPoint => Dw z k j)
          (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
        (continuous_apply j).comp_aestronglyMeasurable hDk
      exact hwj.mul hDkj)
    (fun j => (hProduct j).1)
    (fun j => (hProduct j).2)

end ESS

end
