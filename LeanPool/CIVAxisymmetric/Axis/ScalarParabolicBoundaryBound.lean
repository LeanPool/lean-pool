/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AxisParabolicBoundary
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Setting.MeridionalNorm

/-!
# The parabolic-boundary bound for a scalar on the meridional half-disc

A scalar field `g` of class `C¹` on the unit cylinder, read along the meridional
embedding, is bounded on the parabolic boundary `axisParabolicBoundary R_* t_η s` of
`CIV.axisMaximumPrinciple` by `max (M_b, M_i)`: the lateral bound `M_b` on the
half-circle `{r² + z² = R_*²}` for `t_η < t ≤ s`, the initial bound `M_i` on the open
ball at `t = t_η`, and, at the corner where the two pieces meet, the initial bound again,
carried to the boundary sphere by continuity along the radial segment `c ↦ c·(r, z)`.

This is the scalar form of the swirl-profile boundary bound of `CIV/Closure/SwirlBound.lean`,
stripped of the `(−t)^η` weight and of the component selection, so that the circulation
instantiation of `lem:aniso:axis` can consume it directly.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



/-- At a corner point of the parabolic boundary — radius exactly `R_*`, time exactly the
initial time `τ` — the initial bound `M_i`, which is hypothesised on the *open* ball only,
still holds, by continuity of `g (·, τ)` along the radial segment. -/
theorem abs_scalar_boundary_corner_le (g : ParabolicPoint → ℝ)
    (hg1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder)
    (Rstar τ Mi : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (hτ1 : -1 < τ) (hτ2 : τ < 0)
    (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |g (x, τ)| ≤ Mi)
    (r z : ℝ) (hrz : r ^ 2 + z ^ 2 = Rstar ^ 2) :
    |g (meridional r z, τ)| ≤ Mi := by
  have hτmem : τ ∈ Ioo (-1 : ℝ) 0 := ⟨hτ1, hτ2⟩
  have hRsq : Rstar ^ 2 < 1 := by nlinarith only [hR1, hRpos]
  have hmem_cyl : ((meridional r z, τ) : ParabolicPoint) ∈ unitCylinder :=
    (meridional_mem_unitCylinder_iff r z τ).2 ⟨by linarith only [hrz, hRsq], hτ1, hτ2⟩
  have hspatial : ContDiffOn ℝ 1 (fun y : Vec3 => g (y, τ)) (vec3Ball 0 1) :=
    contDiffOn_spatialSlice hg1 hτmem
  have hcont : ContinuousAt (fun y : Vec3 => g (y, τ)) (meridional r z) :=
    hspatial.continuousOn.continuousAt ((isOpen_vec3Ball 0 1).mem_nhds hmem_cyl.1)
  have hpath : Continuous (fun c : ℝ => meridional (c * r) (c * z)) := by
    unfold meridional; fun_prop
  have hf_tendsto : Filter.Tendsto (fun c : ℝ => meridional (c * r) (c * z))
      (nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1)) (nhds (meridional r z)) := by
    have hbase : Filter.Tendsto (fun c : ℝ => meridional (c * r) (c * z)) (nhds (1 : ℝ))
        (nhds (meridional (1 * r) (1 * z))) := hpath.continuousAt
    rw [one_mul, one_mul] at hbase
    exact hbase.mono_left nhdsWithin_le_nhds
  have hcomp : Filter.Tendsto (fun c : ℝ => g (meridional (c * r) (c * z), τ))
      (nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1)) (nhds (g (meridional r z, τ))) :=
    hcont.tendsto.comp hf_tendsto
  have hbound : ∀ c ∈ Ioo (0 : ℝ) 1, |g (meridional (c * r) (c * z), τ)| ≤ Mi := by
    intro c hc
    refine hinit (meridional (c * r) (c * z)) ?_
    refine (meridional_mem_vec3Ball_zero_iff (c * r) (c * z) Rstar).2 ⟨?_, hRpos⟩
    have hcsq : (c * r) ^ 2 + (c * z) ^ 2 = c ^ 2 * Rstar ^ 2 := by
      rw [← hrz]; ring
    rw [hcsq]
    have hc2 : c ^ 2 < 1 := by nlinarith only [hc.1, hc.2]
    have hRsq_pos : (0 : ℝ) < Rstar ^ 2 := by positivity
    have := mul_lt_mul_of_pos_right hc2 hRsq_pos
    linarith only [this]
  have hnebot : (nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1)).NeBot :=
    right_nhdsWithin_Ioo_neBot (show (0 : ℝ) < 1 by norm_num)
  have habs_tendsto : Filter.Tendsto (fun c : ℝ => |g (meridional (c * r) (c * z), τ)|)
      (nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1)) (nhds |g (meridional r z, τ)|) :=
    (continuous_abs.tendsto _).comp hcomp
  exact le_of_tendsto habs_tendsto (Filter.eventually_of_mem self_mem_nhdsWithin hbound)

/-- The parabolic-boundary bound: on `axisParabolicBoundary R_* t_η s`, the meridional
reading of `g` is bounded by `max (M_b, M_i)`. -/
theorem abs_scalar_meridional_le_boundary (g : ParabolicPoint → ℝ)
    (hg1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder)
    (Rstar tη : ℝ) (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (htη1 : -1 < tη) (htη2 : tη < 0)
    (Mb Mi : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ), |g (x, t)| ≤ Mb)
    (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |g (x, tη)| ≤ Mi)
    (s : ℝ) (hs0 : s < 0) :
    ∀ p ∈ axisParabolicBoundary Rstar tη s, |g (meridional p.1.1 p.1.2, p.2)| ≤ max Mb Mi := by
  rintro ⟨⟨a, b⟩, t⟩ hp
  rcases hp with hinit_piece | hbdry_piece
  · obtain ⟨_ha0, hab, ht⟩ := hinit_piece
    have ht_eq : t = tη := ht
    subst ht_eq
    rcases hab.lt_or_eq with hab' | hab'
    · have hmem : meridional a b ∈ vec3Ball (0 : Vec3) Rstar :=
        (meridional_mem_vec3Ball_zero_iff a b Rstar).2 ⟨hab', hRpos⟩
      exact le_trans (hinit _ hmem) (le_max_right _ _)
    · have hcorner : |g (meridional a b, t)| ≤ Mi :=
        abs_scalar_boundary_corner_le g hg1 Rstar t Mi hRpos hR1 htη1 htη2 hinit a b hab'
      exact le_trans hcorner (le_max_right _ _)
  · obtain ⟨_ha0, hab, ht1, ht2⟩ := hbdry_piece
    have ht0 : t < 0 := lt_of_le_of_lt ht2 hs0
    rcases ht1.lt_or_eq with ht1' | ht1'
    · have hnorm : vec3EuclideanNorm (meridional a b) = Rstar := by
        rw [vec3EuclideanNorm_meridional, hab]
        exact Real.sqrt_sq hRpos.le
      exact le_trans (hbdry (meridional a b) hnorm t ⟨ht1', ht0⟩) (le_max_left _ _)
    · rw [← ht1']
      have hcorner : |g (meridional a b, tη)| ≤ Mi :=
        abs_scalar_boundary_corner_le g hg1 Rstar tη Mi hRpos hR1 htη1 htη2 hinit a b hab
      exact le_trans hcorner (le_max_right _ _)

end CIV
