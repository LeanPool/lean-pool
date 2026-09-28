/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Applications.Development003
public import LeanPool.MovingSofa.Gerver.Applications.Development002

/-!
# Moving sofa: related mathematical developments

* `Gerver.Injectivity`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Injectivity
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- On the rotation interval the inner corner of the cap of Gerver's sofa is the certified
direct Gerver path.  The rotating-hallway coordinates of the inner corner are the cap's two
support values at `t` and `t + π / 2`, and `gerver_capSupport_identification` evaluates those
at the frame coordinates of the paper path. -/
theorem capInnerCorner_eq_paperGerverPath (K : RightAngleCapSpace)
    (hK : (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    capInnerCorner K t = paperGerverPath t := by
  obtain ⟨-, hGeq, -, -, hcapeq, -, hsup⟩ := gerver_capSupport_identification
  -- The certified cap is the outer half-plane cap, so its support values are the paper ones.
  have hKmem : (K.val : Set Point) ∈
      ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)) := by
    refine Or.inl ?_
    rw [hK, hGeq, hcapeq]
  have hangsum : (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, add_comm]
  rw [capInnerCorner,
    (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1, hangsum,
    (hsup _ hKmem t ht).1, (hsup _ hKmem t ht).2, add_sub_cancel_right,
    add_sub_cancel_right, inner_normalVector_smul_add_inner_tangentVector_smul]

/-- On the open rotation interval the inner-corner velocity of the cap of Gerver's sofa is the
velocity of the certified direct Gerver path. -/
theorem derivWithin_capInnerCorner_eq_deriv_paperGerverPath (K : RightAngleCapSpace)
    (hK : (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t = deriv paperGerverPath t := by
  have hcorner : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2), capInnerCorner K s = paperGerverPath s :=
    fun _ hs ↦ capInnerCorner_eq_paperGerverPath K hK hs
  rw [derivWithin_congr hcorner (hcorner t ⟨ht.1.le, ht.2.le⟩),
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

theorem paperGerverCap_injectivity :
    ∃ K : RightAngleCapSpace,
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      SatisfiesInjectivityCondition K := by
  obtain ⟨K, hKset, r, s, hdens, -, -⟩ := gerver_surface_densities
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K t = paperGerverPath t :=
    fun _ ht ↦ capInnerCorner_eq_paperGerverPath K hKset ht
  refine ⟨K, hKset, ⟨r, s, hdens, fun r' s' h' ↦ hdens.ae_eq h'⟩,
    contDiff_paperGerverPath.contDiffOn.congr hcorner, fun t ht ↦ ?_⟩
  rw [derivWithin_capInnerCorner_eq_deriv_paperGerverPath K hKset ht]
  exact ⟨(gerver_strict_velocity t ht).2.2.1, (gerver_strict_velocity t ht).2.2.2⟩

end MovingSofa

end

end

end
