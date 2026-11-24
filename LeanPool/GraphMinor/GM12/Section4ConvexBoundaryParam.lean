/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneDisc
public import Mathlib.Analysis.Convex.GaugeRescale
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A convex subdisc parametrization fixing its circle contacts

For the target discs of XII (4.5), page 253, shrinking a disc
must preserve the cyclic order of the four boundary marks.
A convex set containing a neighborhood of zero is radially
homeomorphic to the unit disc. If it is contained in the unit
disc, every common unit-circle point is on both frontiers and
has gauge one for both sets. The radial homeomorphism fixes
those points, giving a boundary parametrization that retains
their original circle parameters.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric Topology

/-- A closed bounded convex subset of the unit disc containing
a neighborhood of zero has a boundary parametrization fixing
all of its unit-circle contacts. This preserves the order of
the target marks when shrinking region discs in XII (4.5),
page 253. -/
theorem exists_convex_boundary_param_fixing_circle {K : Set ℂ}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : ℂ)) (hb : Bornology.IsBounded K)
    (hcl : IsClosed K) (hsub : K ⊆ closedBall 0 1) :
    IsClosedDisc K ∧ ∃ p : Circle → ℂ, Continuous p ∧ Function.Injective p ∧
      range p = discBd K ∧ ∀ w : Circle, (w : ℂ) ∈ K → p w = w := by
  have ht0 : closedBall (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ one_pos
  let hbc := NormedSpace.isVonNBounded_of_isBounded ℝ hb
  let hbt := NormedSpace.isVonNBounded_of_isBounded ℝ (isBounded_closedBall (x := (0 : ℂ)) (r := 1))
  let e := gaugeRescaleHomeomorph K (closedBall (0 : ℂ) 1)
    hc h0 hbc (convex_closedBall 0 1) ht0 hbt
  have heK : e '' K = closedBall 0 1 := by
    have h := image_gaugeRescaleHomeomorph_closure hc h0 hbc (convex_closedBall (0 : ℂ) 1) ht0 hbt
    rwa [hcl.closure_eq, isClosed_closedBall.closure_eq] at h
  have heunit : e.symm '' closedBall 0 1 = K := by
    rw [← heK, image_image]
    simp
  have hD := isClosedDisc_closedBall.1.image e.symm.continuous.continuousOn
    e.continuous.continuousOn (fun z _ => e.apply_symm_apply z)
  rw [heunit, isClosedDisc_closedBall.2] at hD
  let p : Circle → ℂ := fun w => e.symm w
  refine ⟨hD.1, p, e.symm.continuous.comp continuous_subtype_val,
    (fun a b h => Subtype.ext (e.symm.injective h)), ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [hD.2]
      exact mem_image_of_mem e.symm w.property
    · intro hz
      rw [hD.2] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨⟨w, hw⟩, rfl⟩
  · intro w hwK
    have hwfront : (w : ℂ) ∈ frontier K := by
      refine ⟨subset_closure hwK, ?_⟩
      intro hwint
      have hwball : (w : ℂ) ∈ ball (0 : ℂ) 1 := by
        have h := interior_mono hsub hwint
        rwa [interior_closedBall _ one_ne_zero] at h
      have hlt := mem_ball_zero_iff.mp hwball
      rw [Circle.norm_coe] at hlt
      exact (lt_irrefl (1 : ℝ)) hlt
    have hgK : gauge K (w : ℂ) = 1 := (gauge_eq_one_iff_mem_frontier hc h0).mpr hwfront
    have hgt : gauge (closedBall (0 : ℂ) 1) (w : ℂ) = 1 := by
      rw [gauge_closedBall zero_le_one, Circle.norm_coe, div_one]
    have hefix : e (w : ℂ) = w := by
      change gaugeRescale K (closedBall (0 : ℂ) 1) (w : ℂ) = w
      rw [gaugeRescale, hgK, hgt, div_one, one_smul]
    apply e.injective
    exact (e.apply_symm_apply (w : ℂ)).trans hefix.symm

end GraphMinor.GM12
