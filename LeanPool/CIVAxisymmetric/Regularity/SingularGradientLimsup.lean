/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.SingularSliceSmall
public import LeanPool.CIVAxisymmetric.Regularity.TopCylinderSmallness
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The criterion the covering step consumes

At a point of the singular slice of the blow-up-time slice, the scale-invariant Dirichlet
integral of the spatial gradient over top-boundary cylinders cannot shrink to `0` faster than
linearly in the radius: its `limsup`, as the radius shrinks to `0` from the right, is bounded
below by a universal positive constant. This is the contrapositive of the top-cylinder
Theorem A smallness of `CIV.top_cylinder_smallness_of_gradient_small`, composed with the
Theorem A lower bound `CIV.lintegral_gt_of_mem_singularSlice` at a point of the singular
slice: were the `limsup` below the threshold, the gradient integral would eventually be small
enough on some `(0, r₀]` to feed the uniform interior Morrey decay chain, producing a radius at
which the Theorem A smallness quantity falls below its own universal lower bound at a singular
point, a contradiction.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The criterion the spatial Vitali covering step consumes: at a point of the singular slice
inside the open unit ball, the `limsup`, as the radius shrinks to `0` from the right, of the
scale-invariant Dirichlet integral of the spatial gradient over the top-boundary cylinder based
at that point, is bounded below by a universal positive constant `ε₁`. -/
theorem le_limsup_gradient_of_mem_singularSlice (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f →
        GlobalEnergyClass u Du p → ForceC2Bounded f →
        ContinuousOn (fun z : Vec3 × ℝ => u z) unitCylinder →
        ∀ x ∈ vec3Ball 0 1, x ∈ singularSlice u →
          ENNReal.ofReal ε₁ ≤
            Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
                  ENNReal.ofReal (spatialGradientSq u Du w)) (𝓝[>] (0 : ℝ)) := by
  obtain ⟨ε₀, hε₀, hexit⟩ := lintegral_gt_of_mem_singularSlice q hq
  obtain ⟨C₂₇, hC₂₇, hur6⟩ := top_cylinder_smallness_of_gradient_small q hq ε₀ hε₀
  have hstar : 0 < iterationEpsilonStar C₂₇ := iterationEpsilonStar_pos hC₂₇
  set ε₁ : ℝ := iterationEpsilonStar C₂₇ ^ (2 : ℕ) / 4 with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact div_pos (pow_pos hstar 2) (by norm_num)
  refine ⟨ε₁, hε₁pos, ?_⟩
  intro u Du p f hsol henergy hforce hcont x hx hxsing
  by_contra hcon
  rw [not_le] at hcon
  -- eventually near `0` from the right, the scale-invariant gradient integral is `< ε₁ r`
  have hev := Filter.eventually_lt_of_limsup_lt hcon
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨r₀, hr₀pos, hev'⟩ := hev
  -- a radius keeping the ball around `x` inside the unit ball
  have hx1 : vec3EuclideanNorm x < 1 := by
    have hx' : vec3EuclideanNorm (x - 0) < 1 := hx
    rwa [sub_zero] at hx'
  have hr₁pos : 0 < 1 - vec3EuclideanNorm x := by linarith only [hx1]
  have hballx : vec3Ball x (1 - vec3EuclideanNorm x) ⊆ vec3Ball 0 1 := by
    intro y hy
    have hy' : vec3EuclideanNorm (y - x) < 1 - vec3EuclideanNorm x := hy
    have htri : vec3EuclideanNorm y ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := by
      conv_lhs => rw [show y = (y - x) + x from by abel]
      exact vec3EuclideanNorm_add_le _ _
    refine mem_vec3Ball.mpr ?_
    rw [sub_zero]
    linarith only [htri, hy']
  set R : ℝ := min (r₀ / 2) (min (1 - vec3EuclideanNorm x) 1) with hRdef
  have hRpos : 0 < R := lt_min (by linarith only [hr₀pos]) (lt_min hr₁pos one_pos)
  have hRler0half : R ≤ r₀ / 2 := min_le_left _ _
  have hRle1 : R ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hRler1 : R ≤ 1 - vec3EuclideanNorm x := (min_le_right _ _).trans (min_le_left _ _)
  have hballR : vec3Ball x R ⊆ vec3Ball 0 1 := (vec3Ball_mono hRler1).trans hballx
  -- the uniform gradient smallness needed below, on `(0, R]`
  have hgrad : ∀ r : ℝ, 0 < r → r ≤ R →
      (∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (spatialGradientSq u Du w)) ≤ ENNReal.ofReal (ε₁ * r) := by
    intro r hrpos hrR
    have hrr0 : r < r₀ := by
      have hh : r ≤ r₀ / 2 := hrR.trans hRler0half
      linarith only [hh, hr₀pos]
    have hFr : (ENNReal.ofReal r)⁻¹ * ∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (spatialGradientSq u Du w) < ENNReal.ofReal ε₁ :=
      hev' (y := r) (by rw [Real.dist_eq, sub_zero, abs_of_pos hrpos]; exact hrr0) hrpos
    have hdiv : (∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
          ENNReal.ofReal (spatialGradientSq u Du w)) / (ENNReal.ofReal r) <
        ENNReal.ofReal ε₁ := by
      have hswap : (∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (spatialGradientSq u Du w)) / (ENNReal.ofReal r) =
          (ENNReal.ofReal r)⁻¹ * ∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (spatialGradientSq u Du w) := by
        rw [div_eq_mul_inv, mul_comm]
      rw [hswap]; exact hFr
    have hrne0 : (ENNReal.ofReal r) ≠ 0 := (ENNReal.ofReal_pos.mpr hrpos).ne'
    have hrnetop : (ENNReal.ofReal r) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmullt := (ENNReal.div_lt_iff (Or.inl hrne0) (Or.inl hrnetop)).mp hdiv
    have heq : ENNReal.ofReal ε₁ * ENNReal.ofReal r = ENNReal.ofReal (ε₁ * r) :=
      (ENNReal.ofReal_mul hε₁pos.le).symm
    rw [heq] at hmullt
    exact hmullt.le
  obtain ⟨ρ, hρpos, hρleR, hρbound⟩ :=
    hur6 u Du p f hsol henergy hforce x R hRpos hRle1 hballR hgrad
  have hρle1 : ρ ≤ 1 := hρleR.trans hRle1
  have hballρ : vec3Ball x ρ ⊆ vec3Ball 0 1 := (vec3Ball_mono hρleR).trans hballR
  exact absurd hρbound (not_le.2 (hexit u Du p f hsol hcont x ρ hρpos hρle1 hballρ hxsing))

end CIV

