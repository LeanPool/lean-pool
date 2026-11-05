/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicSphereProfile

/-!
# HarmonicSphereBump

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The radial test bump: a compactly supported `C^2` solution of `Delta psi = k`

Combining the radial Laplacian of `HarmonicSphereRadial` with the profile of
`HarmonicSphereProfile` gives, for every continuous annulus-supported density
`k` of vanishing radial moment, a compactly supported `C^2` function on
`Vec (m + 1)` whose coordinate Laplacian is exactly `x ↦ k (|x - z|)`.

This is the test function that the Green pairing of `HarmonicGreen` will be run
against.  Its existence is the whole content of the classical statement that a
radial density of vanishing mean is a Laplacian; the annulus support is what
makes the construction elementary, because the profile is then constant near the
origin and the Euclidean gauge is smooth on the support of the density.

## Contents

* `euclideanCoordLaplacian_radialPotential` -- `Delta psi = k (|· - z|)` at every
  point of the carrier, including the centre.
* `contDiff_radialPotential_comp` -- `psi` is `C^2`.
* `tsupport_radialPotential_comp_subset`,
  `hasCompactSupport_radialPotential_comp` -- `psi` is supported in the closed
  Euclidean ball of radius `b`.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {m : ℕ} {k : ℝ → ℝ} {a b : ℝ}

variable {m : ℕ} {k : ℝ → ℝ} {a b : ℝ}

/-- The radial potential solves the radial Laplace equation with right-hand side
`k` in dimension `m + 1`, at every point of the carrier. -/
theorem euclideanCoordLaplacian_radialPotential (hk : Continuous k) (ha : 0 < a)
    (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (z x : Vec (m + 1)) :
    euclideanCoordLaplacian
        (fun w : Vec (m + 1) => radialPotential m k b (euclideanNorm (w - z))) x =
      k (euclideanNorm (x - z)) := by
  by_cases hx : x = z
  · subst hx
    have hzero : euclideanCoordLaplacian
        (fun w : Vec (m + 1) => radialPotential m k b (euclideanNorm (w - x))) x = 0 := by
      refine euclideanCoordLaplacian_eq_zero_of_locally_const (c := radialPotential m k b 0)
        (isOpen_euclideanBall x a) (mem_euclideanBall_self ha) ?_
      intro y hy
      exact radialPotential_eq_of_le hk ha hk0
        (le_of_lt ((mem_euclideanBall_iff_euclideanNorm_lt ha.le).mp hy))
    rw [hzero]
    have hn : euclideanNorm (x - x) = 0 := by
      simp [euclideanNorm, vecNormSq, vecDot]
    rw [hn, hk0 0 ha.le]
  · rw [euclideanCoordLaplacian_radial (Φ' := radialSlope m k)
      (Φ'' := fun t => k t - (m : ℝ) * radialMoment m k t / t ^ (m + 1))
      (fun t _ => hasDerivAt_radialPotential hk ha hk0 b t)
      (fun t ht => hasDerivAt_radialSlope hk ht) hx]
    have hNne : euclideanNorm (x - z) ≠ 0 := ne_of_gt (euclideanNorm_pos (sub_ne_zero.mpr hx))
    rw [radialSlope, pow_succ]
    push_cast
    field_simp
    ring

theorem contDiff_radialPotential_comp (hk : Continuous k) (ha : 0 < a)
    (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (b : ℝ) (z : Vec (m + 1)) :
    ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞)
      (fun w : Vec (m + 1) => radialPotential m k b (euclideanNorm (w - z))) := by
  have htwo : ((2 : ℕ) : WithTop ℕ∞) = 2 := by norm_num
  rw [htwo]
  exact contDiff_radial ha (fun t ht => contDiffAt_radialPotential hk ha hk0 b ht)
    (fun t _ htlt => radialPotential_eq_of_le hk ha hk0 (le_of_lt htlt))

theorem tsupport_radialPotential_comp_subset (hk : Continuous k) (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (hmom : radialMoment m k b = 0) (z : Vec (m + 1)) :
    tsupport (fun w : Vec (m + 1) => radialPotential m k b (euclideanNorm (w - z))) ⊆
      euclideanClosedBall z b := by
  refine closure_minimal ?_ (isClosed_euclideanClosedBall z b)
  intro w hw
  rw [mem_euclideanClosedBall_iff_euclideanNorm_le hb.le]
  by_contra hnot
  exact hw (radialPotential_eq_zero_of_ge hk hkb hmom (le_of_lt (lt_of_not_ge hnot)))

theorem hasCompactSupport_radialPotential_comp (hk : Continuous k) (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (hmom : radialMoment m k b = 0) (z : Vec (m + 1)) :
    HasCompactSupport
      (fun w : Vec (m + 1) => radialPotential m k b (euclideanNorm (w - z))) :=
  IsCompact.of_isClosed_subset (isCompact_euclideanClosedBall z hb.le) isClosed_closure
    (tsupport_radialPotential_comp_subset hk hb hkb hmom z)

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
