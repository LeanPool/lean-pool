/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AnalyticOfBounds
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Axisymmetry on a fixed ball from axisymmetry on a shrinking core

The reduction of Section `sec:reduction:core`: at a fixed time `t` at which the velocity
slice `u(·, t)` is real analytic on `B(1)`, axisymmetry on a core ball `B(ρ)` with `ρ > 0`
propagates to all of `B(1)`.

The argument is the one printed after `eq:interior:defect`. For an angle `φ` the defect
`F_φ(x) = u(x, t) - Q_φ u(Q_φ^{-1} x, t)` is real analytic on `B(1)`, because the rotation
`Q_φ` is a continuous linear automorphism of the space which preserves the ball. On the core
ball `F_φ` vanishes, since there `u` agrees with its angular mean and the angular mean is
fixed by every rotation. The identity theorem on the connected set `B(1)` then gives
`F_φ ≡ 0` on `B(1)`; as `φ` is arbitrary, `u` is fixed by every rotation there, which is
axisymmetry.

The time variable is a spectator throughout: the analyticity radius and the core radius may
depend on `t` in any way, which is what `eq:interior:global:symmetry` needs.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Balls centred on the axis are connected -/

/-- The triangle inequality for the Euclidean norm of `Vec3`. -/
theorem vec3EuclideanNorm_add_le (x y : Vec3) :
    vec3EuclideanNorm (x + y) ≤ vec3EuclideanNorm x + vec3EuclideanNorm y := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

/-- A ball centred on the axis is convex. -/
theorem convex_vec3Ball_zero (r : ℝ) : Convex ℝ (vec3Ball (0 : Vec3) r) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_vec3Ball, sub_zero] at hx hy ⊢
  calc vec3EuclideanNorm (a • x + b • y)
      ≤ vec3EuclideanNorm (a • x) + vec3EuclideanNorm (b • y) := vec3EuclideanNorm_add_le _ _
    _ = a * vec3EuclideanNorm x + b * vec3EuclideanNorm y := by
        rw [vec3EuclideanNorm_smul, vec3EuclideanNorm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * max (vec3EuclideanNorm x) (vec3EuclideanNorm y)
          + b * max (vec3EuclideanNorm x) (vec3EuclideanNorm y) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = max (vec3EuclideanNorm x) (vec3EuclideanNorm y) := by rw [← add_mul, hab, one_mul]
    _ < r := max_lt hx hy

/-- A ball centred on the axis is connected, so the identity theorem applies on it. -/
theorem isPreconnected_vec3Ball_zero (r : ℝ) : IsPreconnected (vec3Ball (0 : Vec3) r) :=
  (convex_vec3Ball_zero r).isPreconnected

theorem zero_mem_vec3Ball_zero {r : ℝ} (hr : 0 < r) : (0 : Vec3) ∈ vec3Ball 0 r := by
  simpa [vec3EuclideanNorm_zero] using hr

/-- A space-time slab over a ball centred on the axis is rotation invariant. -/
theorem rotZ_mem_spaceTimeSet_vec3Ball_zero (r : ℝ) (I : Set ℝ) (φ : ℝ)
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet (vec3Ball 0 r) I) :
    (rotZ φ z.1, z.2) ∈ spaceTimeSet (vec3Ball 0 r) I :=
  ⟨(rotZ_mem_vec3Ball_zero_iff φ r z.1).2 hz.1, hz.2⟩

/-! ### Analyticity of the rotated slice -/

/-- If every component of the velocity slice `u(·, t)` is real analytic on a ball centred on
the axis, then so is every component of the rotated slice `(ℛ_φ u)(·, t)`: the rotation is a
continuous linear automorphism preserving the ball. -/
theorem analyticOnNhd_rotField_slice {u : ParabolicPoint → Vec3} {t r : ℝ}
    (hu : ∀ i : Fin 3, AnalyticOnNhd ℝ (fun x : Vec3 => u (x, t) i) (vec3Ball 0 r)) (φ : ℝ) :
    AnalyticOnNhd ℝ (fun x : Vec3 => rotField φ u (x, t)) (vec3Ball 0 r) := by
  have hpre : ((rotZEquiv (-φ)).toContinuousLinearMap) ⁻¹' vec3Ball (0 : Vec3) r
      = vec3Ball 0 r := Set.ext fun y => rotZ_mem_vec3Ball_zero_iff (-φ) r y
  have hcomp : AnalyticOnNhd ℝ (fun x : Vec3 => u (rotZ (-φ) x, t)) (vec3Ball 0 r) := by
    have h := (AnalyticOnNhd.pi hu).compContinuousLinearMap
      (u := (rotZEquiv (-φ)).toContinuousLinearMap)
    rwa [hpre] at h
  exact (ContinuousLinearMap.analyticOnNhd (rotZEquiv φ).toContinuousLinearMap univ).comp hcomp
    (mapsTo_univ _ _)

/-! ### The reduction -/

/-- **Axisymmetry from an axisymmetric core.** At a time `t` at which every component of
`u(·, t)` is real analytic on `B(1)`, axisymmetry on a core ball `B(ρ)` with `0 < ρ ≤ 1`
forces axisymmetry on all of `B(1)`; this is the step from `eq:interior:core` to
`eq:interior:global:symmetry` in the proof of `thm:main`. -/
theorem isAxisymmetric_slice_of_analytic_of_core {u : ParabolicPoint → Vec3} {t ρ : ℝ}
    (hu : ∀ i : Fin 3, AnalyticOnNhd ℝ (fun x : Vec3 => u (x, t) i) (vec3Ball 0 1))
    (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (hcore : IsAxisymmetricOn u (spaceTimeSet (vec3Ball 0 ρ) {t})) :
    IsAxisymmetricOn u (spaceTimeSet (vec3Ball 0 1) {t}) := by
  refine isAxisymmetricOn_of_forall_rotField_eq fun φ z hz => ?_
  obtain ⟨x, s⟩ := z
  obtain ⟨hx, hs⟩ : x ∈ vec3Ball 0 1 ∧ s ∈ ({t} : Set ℝ) := hz
  rw [mem_singleton_iff] at hs
  rw [hs]
  have hdefect : AnalyticOnNhd ℝ (fun y : Vec3 => u (y, t) - rotField φ u (y, t))
      (vec3Ball 0 1) := (AnalyticOnNhd.pi hu).sub (analyticOnNhd_rotField_slice hu φ)
  have hzero : EqOn (fun y : Vec3 => u (y, t) - rotField φ u (y, t)) 0 (vec3Ball 0 1) := by
    refine hdefect.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_vec3Ball_zero 1)
      (zero_mem_vec3Ball_zero one_pos) ?_
    filter_upwards [(isOpen_vec3Ball (0 : Vec3) ρ).mem_nhds (zero_mem_vec3Ball_zero hρ.1)]
      with y hy
    have hy' : ((y, t) : ParabolicPoint) ∈ spaceTimeSet (vec3Ball 0 ρ) {t} := ⟨hy, rfl⟩
    have := hcore.rotField_eq
      (fun ψ w hw => rotZ_mem_spaceTimeSet_vec3Ball_zero ρ {t} ψ hw) φ hy'
    simp [this]
  exact (sub_eq_zero.1 (hzero hx)).symm

/-- **The symmetry of `eq:interior:global:symmetry`.** If at every time of `(-1, 0)` the
velocity slice is real analytic on `B(1)` and axisymmetric on some core ball, then it is
axisymmetric on the whole unit cylinder `Q`. The two radii are allowed to degenerate as
`t ↑ 0`, at unrelated rates. -/
theorem isAxisymmetricOn_unitCylinder_of_analytic_of_core {u : ParabolicPoint → Vec3}
    (hu : ∀ t ∈ Ioo (-1 : ℝ) 0, ∀ i : Fin 3,
      AnalyticOnNhd ℝ (fun x : Vec3 => u (x, t) i) (vec3Ball 0 1))
    (hcore : ∀ t ∈ Ioo (-1 : ℝ) 0, ∃ ρ ∈ Ioo (0 : ℝ) 1,
      IsAxisymmetricOn u (spaceTimeSet (vec3Ball 0 ρ) {t})) :
    IsAxisymmetricOn u unitCylinder := by
  intro z hz
  obtain ⟨x, t⟩ := z
  obtain ⟨hx, ht⟩ : x ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1 : ℝ) 0 := hz
  obtain ⟨ρ, hρ, hρcore⟩ := hcore t ht
  exact isAxisymmetric_slice_of_analytic_of_core (hu t ht) (Ioo_subset_Ioc_self hρ) hρcore
    ((x, t) : ParabolicPoint) ⟨hx, rfl⟩

/-- The same conclusion from the quantitative form of the analyticity of the velocity: on each
ball `B(R')` with `R' < 1` the iterated spatial derivatives of every component obey a factorial
bound, with constants that may degenerate as `R' ↑ 1` and as `t ↑ 0`. This is the way
`eq:analytic:interior:velocity` is used in the proof of `thm:main`. -/
theorem isAxisymmetricOn_unitCylinder_of_iteratedFDeriv_bound {u : ParabolicPoint → Vec3}
    (hsmooth : ∀ t ∈ Ioo (-1 : ℝ) 0, ∀ i : Fin 3,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i) (vec3Ball 0 1))
    (hbound : ∀ t ∈ Ioo (-1 : ℝ) 0, ∀ i : Fin 3, ∀ R' : ℝ, R' < 1 → ∃ C K : ℝ, 0 < K ∧
      ∀ n : ℕ, ∀ x ∈ vec3Ball 0 R',
        ‖iteratedFDeriv ℝ n (fun y : Vec3 => u (y, t) i) x‖ ≤ C * K ^ n * (Nat.factorial n))
    (hcore : ∀ t ∈ Ioo (-1 : ℝ) 0, ∃ ρ ∈ Ioo (0 : ℝ) 1,
      IsAxisymmetricOn u (spaceTimeSet (vec3Ball 0 ρ) {t})) :
    IsAxisymmetricOn u unitCylinder :=
  isAxisymmetricOn_unitCylinder_of_analytic_of_core
    (fun t ht i => analyticOnNhd_vec3Ball_of_iteratedFDeriv_bound (hsmooth t ht i)
      (hbound t ht i)) hcore

end CIV
