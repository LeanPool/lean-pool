/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.WeakContL3
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# The local weakly continuous `L³` representative

This module upgrades the time-slice `L²` representative to `L³` and extends
its smooth-test continuity to all `L^{3/2}` pairings.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic

local instance : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩


noncomputable section

namespace ESS

/-- The spatial ball of radius `3/4` used for the weak continuity L3 conclusion. -/
@[expose] def weakContL3ResultSmallBall : Set Vec3 :=
  vec3Ball (0 : Vec3) (3 / 4 : ℝ)

private instance weakContL3ResultLargeBallFinite :
    IsFiniteMeasure (volume.restrict weakContL3SpatialBall) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top

private instance weakContL3ResultSmallBallFinite :
    IsFiniteMeasure (volume.restrict weakContL3ResultSmallBall) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top

private theorem weakContL3Result_holder_approximation
    {A ε d : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (hd : d ≤ ε / (3 * (A + 1))) : A * d ≤ ε / 3 := by
  have hfrac : A / (3 * (A + 1)) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hA]
  calc
    A * d ≤ A * (ε / (3 * (A + 1))) := mul_le_mul_of_nonneg_left hd hA
    _ = ε * (A / (3 * (A + 1))) := by ring
    _ ≤ ε * (1 / 3) := mul_le_mul_of_nonneg_left hfrac hε.le
    _ = ε / 3 := by ring

private theorem weakContL3Result_pairing_eq_on_small_ball
    (v₂ : Lp L2Vec3 2 (volume.restrict weakContL3SpatialBall))
    (hmem : MemLp (fun x : Vec3 => v₂ x) 3
      (volume.restrict weakContL3ResultSmallBall))
    (g : Vec3 → L2Vec3)
    (gExt : Vec3 → L2Vec3)
    (hgExt : gExt = weakContL3ResultSmallBall.indicator g)
    (gExt₂ : Lp L2Vec3 2 (volume.restrict weakContL3SpatialBall))
    (hgExtMem₂ : MemLp gExt 2
      (volume.restrict weakContL3SpatialBall))
    (hgExt₂ : gExt₂ = hgExtMem₂.toLp gExt) :
    inner ℝ v₂ gExt₂ =
      ∫ x, inner ℝ (hmem.toLp (fun x => v₂ x) x) (g x)
        ∂(volume.restrict weakContL3ResultSmallBall) := by
  rw [MeasureTheory.L2.inner_def]
  have hballmeas : MeasurableSet weakContL3ResultSmallBall :=
    (isOpen_vec3Ball _ _).measurableSet
  have hsmallsubset : weakContL3ResultSmallBall ⊆ weakContL3SpatialBall := by
    intro x hx
    have hxnorm : vec3EuclideanNorm (x - 0) < 3 / 4 := by
      simpa [weakContL3ResultSmallBall, mem_vec3Ball] using hx
    change vec3EuclideanNorm (x - 0) < 1
    exact lt_trans hxnorm (by norm_num)
  calc
    ∫ x, inner ℝ (v₂ x) (gExt₂ x)
        ∂(volume.restrict weakContL3SpatialBall) =
      ∫ x, inner ℝ (v₂ x) (gExt x)
        ∂(volume.restrict weakContL3SpatialBall) := by
          apply integral_congr_ae
          filter_upwards [hgExtMem₂.coeFn_toLp] with x hx
          rw [hgExt₂, hx]
    _ = ∫ x, inner ℝ (v₂ x) (g x)
        ∂(volume.restrict weakContL3ResultSmallBall) := by
          have hpoint (x : Vec3) :
              inner ℝ (v₂ x) (gExt x) =
                weakContL3ResultSmallBall.indicator
                  (fun y => inner ℝ (v₂ y) (g y)) x := by
            by_cases hx : x ∈ weakContL3ResultSmallBall <;>
              simp [hgExt, hx]
          calc
            _ = ∫ x, weakContL3ResultSmallBall.indicator
                  (fun y => inner ℝ (v₂ y) (g y)) x
                  ∂(volume.restrict weakContL3SpatialBall) := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall hpoint
            _ = ∫ x, inner ℝ (v₂ x) (g x)
                  ∂(volume.restrict weakContL3ResultSmallBall) := by
                    rw [integral_indicator hballmeas]
                    rw [Measure.restrict_restrict_of_subset hsmallsubset]
    _ = ∫ x, inner ℝ (hmem.toLp (fun x => v₂ x) x) (g x)
        ∂(volume.restrict weakContL3ResultSmallBall) := by
          apply integral_congr_ae
          filter_upwards [hmem.coeFn_toLp] with x hx₁
          rw [hx₁]

private theorem weakContL3Result_pairing_continuous
    (v₂ : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 2 (volume.restrict weakContL3SpatialBall))
    (hweak : ∀ w : Lp L2Vec3 2 (volume.restrict weakContL3SpatialBall),
      Continuous (fun t => inner ℝ (v₂ t) w))
    (hmem : ∀ t, MemLp (fun x : Vec3 => v₂ t x) 3
      (volume.restrict weakContL3ResultSmallBall))
    (M : ℝ≥0∞)
    (hbound : ∀ t,
      eLpNorm (fun x : Vec3 => v₂ t x) 3
        (volume.restrict weakContL3ResultSmallBall) ≤ M)
    (hMtop : M < ⊤) :
    ∀ w : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict weakContL3ResultSmallBall),
      Continuous (fun t => ∫ x, inner ℝ
        ((hmem t).toLp (fun x => v₂ t x) x) (w x)
        ∂(volume.restrict weakContL3ResultSmallBall)) := by
  intro w
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ : ℝ := ε / (3 * (M.toReal + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpTop : ENNReal.ofReal (3 / 2 : ℝ) ≠ ⊤ := by norm_num
  obtain ⟨g, hgcompact, hgsmooth, hgerr⟩ :=
    (Lp.memLp w).exist_eLpNorm_sub_le hpTop (by norm_num) hδ
  have hgMem₃₂ : MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict weakContL3ResultSmallBall) :=
    hgsmooth.continuous.memLp_of_hasCompactSupport hgcompact
  let g₃₂ : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict weakContL3ResultSmallBall) := hgMem₃₂.toLp g
  have hdist : dist w g₃₂ ≤ δ := by
    rw [Lp.dist_def]
    have heq : eLpNorm (⇑w - ⇑g₃₂)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict weakContL3ResultSmallBall) =
        eLpNorm (⇑w - g)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict weakContL3ResultSmallBall) := by
      apply eLpNorm_congr_ae
      filter_upwards [hgMem₃₂.coeFn_toLp] with x hx
      change w x - g₃₂ x = w x - g x
      rw [hx]
    rw [heq]
    calc
      (eLpNorm (fun x : Vec3 => w x - g x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict weakContL3ResultSmallBall)).toReal ≤
          (ENNReal.ofReal δ).toReal :=
            ENNReal.toReal_mono (ENNReal.ofReal_lt_top.ne) hgerr
      _ = δ := ENNReal.toReal_ofReal hδ.le
  have hgMem₂ : MemLp g 2 (volume.restrict weakContL3ResultSmallBall) := by
    exact hgsmooth.continuous.memLp_of_hasCompactSupport hgcompact
  have hballmeas : MeasurableSet weakContL3ResultSmallBall := by
    exact (isOpen_vec3Ball _ _).measurableSet
  have hsmallsubset : weakContL3ResultSmallBall ⊆ weakContL3SpatialBall := by
    intro x hx
    have hxnorm : vec3EuclideanNorm (x - 0) < 3 / 4 := by
      simpa [weakContL3ResultSmallBall, mem_vec3Ball] using hx
    change vec3EuclideanNorm (x - 0) < 1
    exact lt_trans hxnorm (by norm_num)
  let gExt : Vec3 → L2Vec3 := weakContL3ResultSmallBall.indicator g
  have hgExtMem₂ : MemLp gExt 2 (volume.restrict weakContL3SpatialBall) := by
    change MemLp (weakContL3ResultSmallBall.indicator g) 2
      (volume.restrict weakContL3SpatialBall)
    rw [memLp_indicator_iff_restrict hballmeas]
    rw [Measure.restrict_restrict_of_subset hsmallsubset]
    exact hgMem₂
  let gExt₂ : Lp L2Vec3 2 (volume.restrict weakContL3SpatialBall) :=
    hgExtMem₂.toLp gExt
  have hpairEq (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      inner ℝ (v₂ t) gExt₂ =
        ∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (g₃₂ x)
          ∂(volume.restrict weakContL3ResultSmallBall) := by
    calc
      inner ℝ (v₂ t) gExt₂ =
          ∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (g x)
        ∂(volume.restrict weakContL3ResultSmallBall) :=
        weakContL3Result_pairing_eq_on_small_ball
          (v₂ t) (hmem t) g gExt rfl gExt₂ hgExtMem₂ rfl
      _ = ∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (g₃₂ x)
          ∂(volume.restrict weakContL3ResultSmallBall) := by
            apply integral_congr_ae
            filter_upwards [hgMem₃₂.coeFn_toLp] with x hx
            rw [hx]
  let F (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :=
    ∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (w x)
      ∂(volume.restrict weakContL3ResultSmallBall)
  let G (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :=
    ∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (g₃₂ x)
      ∂(volume.restrict weakContL3ResultSmallBall)
  have hGcont : Continuous G := by
    have h := hweak gExt₂
    convert h using 1
    funext t
    exact (hpairEq t).symm
  have happrox (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      dist (F t) (G t) ≤ M.toReal * dist w g₃₂ := by
    have hIntW := weakContL3_integral_holder (hmem t) (Lp.memLp w)
    have hIntG := weakContL3_integral_holder (hmem t) hgMem₃₂
    have hIntDiff := weakContL3_integral_holder (hmem t) (Lp.memLp (w - g₃₂))
    have hIntW' : Integrable (fun x : Vec3 =>
        inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (w x))
        (volume.restrict weakContL3ResultSmallBall) := by
      apply hIntW.1.congr
      filter_upwards [(hmem t).coeFn_toLp] with x hx
      rw [hx]
    have hIntG' : Integrable (fun x : Vec3 =>
        inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (g₃₂ x))
        (volume.restrict weakContL3ResultSmallBall) := by
      apply hIntG.1.congr
      filter_upwards [(hmem t).coeFn_toLp, hgMem₃₂.coeFn_toLp]
        with x hx₁ hx₂
      rw [hx₁, hx₂]
    have hIntDiffEq :
        (∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x)
          ((w - g₃₂) x) ∂(volume.restrict weakContL3ResultSmallBall)) =
        ∫ x, inner ℝ (v₂ t x) ((w - g₃₂) x)
          ∂(volume.restrict weakContL3ResultSmallBall) := by
      apply integral_congr_ae
      filter_upwards [(hmem t).coeFn_toLp] with x hx
      rw [hx]
    have hdiff : F t - G t =
        ∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x)
          ((w - g₃₂) x) ∂(volume.restrict weakContL3ResultSmallBall) := by
      change
        (∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (w x)
          ∂(volume.restrict weakContL3ResultSmallBall)) -
        (∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (g₃₂ x)
          ∂(volume.restrict weakContL3ResultSmallBall)) = _
      calc
        _ = ∫ x, (inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (w x) -
            inner ℝ ((hmem t).toLp (fun x => v₂ t x) x) (g₃₂ x))
            ∂(volume.restrict weakContL3ResultSmallBall) := by
              rw [← integral_sub hIntW' hIntG']
        _ = ∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x)
            ((w - g₃₂) x) ∂(volume.restrict weakContL3ResultSmallBall) := by
              apply integral_congr_ae
              filter_upwards [Lp.coeFn_sub w g₃₂] with x hx
              have hx' : (w - g₃₂) x = w x - g₃₂ x := by
                change (w - g₃₂) x = w x - g₃₂ x at hx
                exact hx
              calc
                _ = inner ℝ ((hmem t).toLp (fun x => v₂ t x) x)
                    (w x - g₃₂ x) := by rw [← inner_sub_right]
                _ = inner ℝ ((hmem t).toLp (fun x => v₂ t x) x)
                    ((w - g₃₂) x) := by rw [← hx']
    change |F t - G t| ≤ M.toReal * dist w g₃₂
    have hnormEq :
        eLpNorm (fun x : Vec3 => ((hmem t).toLp (fun x => v₂ t x) x)) 3
          (volume.restrict weakContL3ResultSmallBall) =
        eLpNorm (fun x : Vec3 => v₂ t x) 3
          (volume.restrict weakContL3ResultSmallBall) :=
      eLpNorm_congr_ae (hmem t).coeFn_toLp
    have hnorm :
        (eLpNorm (fun x : Vec3 => ((hmem t).toLp (fun x => v₂ t x) x)) 3
          (volume.restrict weakContL3ResultSmallBall)).toReal ≤
          M.toReal := by
      rw [hnormEq]
      exact ENNReal.toReal_mono hMtop.ne (hbound t)
    have hIntDiffBound := hIntDiff.2
    rw [hnormEq.symm] at hIntDiffBound
    have hdiffnorm :
        (eLpNorm (fun x : Vec3 => (w - g₃₂) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict weakContL3ResultSmallBall)).toReal = dist w g₃₂ := by
      rw [Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae (Lp.coeFn_sub w g₃₂)
    calc
      |F t - G t| =
          |∫ x, inner ℝ ((hmem t).toLp (fun x => v₂ t x) x)
            ((w - g₃₂) x) ∂(volume.restrict weakContL3ResultSmallBall)| := by
              rw [hdiff]
      _ = |∫ x, inner ℝ (v₂ t x) ((w - g₃₂) x)
          ∂(volume.restrict weakContL3ResultSmallBall)| := by rw [hIntDiffEq]
      _ ≤
          (eLpNorm (fun x : Vec3 => ((hmem t).toLp (fun x => v₂ t x) x)) 3
            (volume.restrict weakContL3ResultSmallBall)).toReal *
          (eLpNorm (fun x : Vec3 => (w - g₃₂) x)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict weakContL3ResultSmallBall)).toReal := by
              exact hIntDiffBound
      _ ≤ M.toReal * dist w g₃₂ := by
        rw [hdiffnorm]
        exact mul_le_mul_of_nonneg_right hnorm (dist_nonneg)
  have happroxSmall :
      ∀ t : Icc (-(3 / 4 : ℝ) ^ 2) 0, dist (F t) (G t) ≤ ε / 3 := by
    intro t
    calc
      dist (F t) (G t) ≤
        M.toReal * dist w g₃₂ := happrox t
      _ ≤ ε / 3 := weakContL3Result_holder_approximation
        ENNReal.toReal_nonneg hε (by simpa [δ] using hdist)
  have hGat : ContinuousAt G t₀ := by
    exact hGcont.continuousAt
  obtain ⟨η, hη, hGη⟩ := Metric.continuousAt_iff.mp hGat (ε / 3) (by positivity)
  refine ⟨η, hη, fun t ht => ?_⟩
  have hmiddle : dist (G t) (G t₀) < ε / 3 := hGη ht
  have hlast : dist (G t₀) (F t₀) ≤ ε / 3 := by
    rw [dist_comm]
    exact happroxSmall t₀
  calc
    dist (F t) (F t₀) ≤ dist (F t) (G t) + dist (G t) (F t₀) :=
      dist_triangle _ _ _
    _ ≤ dist (F t) (G t) +
        (dist (G t) (G t₀) + dist (G t₀) (F t₀)) := by
          gcongr
          exact dist_triangle _ _ _
    _ < ε := by
      nlinarith only [happroxSmall t, hmiddle, hlast, hε]

/-- The local velocity has the all-time weakly continuous `L³` representative
from `lem:weak-cont-L3`. -/
theorem weakContL3
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1 : ℝ) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i)
          ∂volume = 0) :
    ∃ v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
        Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
      (∀ t, ‖v t‖ ≤ (weakContL3MomentBound (u := u)).toReal) ∧
      (∀ w : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
        Continuous (fun t => ∫ x, inner ℝ (v t x) (w x)
          ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
        ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
          ∃ huSlice : MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3
              (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
            v ⟨t, ht⟩ = huSlice.toLp _ := by
  classical
  let μ₁ : Measure Vec3 := volume.restrict weakContL3SpatialBall
  let μ₃ : Measure Vec3 := volume.restrict weakContL3ResultSmallBall
  let M : ℝ≥0∞ := weakContL3MomentBound (u := u)
  have hL3Moment : weakContL3MomentSup (u := u) < ⊤ := by
    simpa [weakContL3MomentSup, weakContL3SpatialBall] using hL3
  have hMtop : M < ⊤ := by
    dsimp [M, weakContL3MomentBound]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hL3Moment.ne
  have hS3' : ∀ Φ : ParabolicPoint → Vec3,
      Φ ∈ spaceTimeTestFunction (V := Vec3)
        weakContL3SpatialBall (Ioo (-1 : ℝ) 0) →
      ∫ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => Φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => Φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z)
          ∂volume = 0 := by
    intro Φ hΦ
    simpa [weakContL3SpatialBall, Pi.zero_apply] using hS3 Φ hΦ
  obtain ⟨v₂, _hv₂bound, hv₂continuous, hpairBound, hAgreement, hSliceL3⟩ :=
    weakContL3_l2Representative hu hDu henergy hL3Moment hp hgrad hS3'
  have hnorming (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      MemLp (fun x : Vec3 => v₂ t x) 3 μ₁ ∧
        eLpNorm (fun x : Vec3 => v₂ t x) 3 μ₁ ≤ M := by
    obtain ⟨hm, hbound⟩ := weakContL3_norming_bound (μ := μ₁)
      (v₂ t) M.toReal ENNReal.toReal_nonneg (hpairBound t)
    refine ⟨hm, ?_⟩
    calc
      eLpNorm (fun x : Vec3 => v₂ t x) 3 μ₁ ≤ ENNReal.ofReal M.toReal := hbound
      _ = M := ENNReal.ofReal_toReal hMtop.ne
  have hsmallsubset : weakContL3ResultSmallBall ⊆ weakContL3SpatialBall := by
    intro x hx
    have hxnorm : vec3EuclideanNorm (x - 0) < 3 / 4 := by
      simpa [weakContL3ResultSmallBall, mem_vec3Ball] using hx
    change vec3EuclideanNorm (x - 0) < 1
    exact lt_trans hxnorm (by norm_num)
  have hsmallmeasure : μ₃ ≤ μ₁ := by
    dsimp [μ₃, μ₁]
    exact (volume : Measure Vec3).restrict_mono_set hsmallsubset
  have hsmallAE : ae μ₃ ≤ ae μ₁ :=
    Measure.ae_le_iff_absolutelyContinuous.mpr
      (Measure.absolutelyContinuous_of_le hsmallmeasure)
  have hmemSmall (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) : MemLp
      (fun x : Vec3 => v₂ t x) 3 μ₃ :=
    (hnorming t).1.mono_measure hsmallmeasure
  have hboundSmall (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      eLpNorm (fun x : Vec3 => v₂ t x) 3 μ₃ ≤ M :=
    (eLpNorm_mono_measure _ hsmallmeasure).trans (hnorming t).2
  let v : Icc (-(3 / 4 : ℝ) ^ 2) 0 → Lp L2Vec3 3 μ₃ := fun t =>
    (hmemSmall t).toLp (fun x => v₂ t x)
  have hvbound (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) : ‖v t‖ ≤ M.toReal := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono hMtop.ne (hboundSmall t)
  have hpairContinuous := weakContL3Result_pairing_continuous
    v₂ hv₂continuous hmemSmall M hboundSmall hMtop
  have hχone : ∀ x ∈ weakContL3ResultSmallBall,
      (Classical.choose weakContL3_cutoff_exists) x = 1 := by
    obtain ⟨_, _, _, _, hχone⟩ := Classical.choose_spec weakContL3_cutoff_exists
    intro x hx
    exact hχone x (by simpa [weakContL3ResultSmallBall] using hx)
  have hχoneAE : ∀ᵐ x ∂μ₃,
      (Classical.choose weakContL3_cutoff_exists) x = 1 := by
    filter_upwards [ae_restrict_mem (isOpen_vec3Ball _ _).measurableSet]
      with x hx
    exact hχone x (by simpa [weakContL3ResultSmallBall] using hx)
  refine ⟨v, ?_, ?_⟩
  · intro t
    exact hvbound t
  constructor
  · intro w
    change Continuous (fun t => ∫ x, inner ℝ
      ((hmemSmall t).toLp (fun x => v₂ t x) x) (w x) ∂μ₃)
    exact hpairContinuous w
  · filter_upwards [hAgreement, hSliceL3] with t hA hS
    obtain ⟨ht, hmCut, hvA⟩ := hA
    obtain ⟨_, hmU, _⟩ := hS
    refine ⟨ht, hmU, ?_⟩
    apply Lp.ext
    have hclassAE :
        (fun x : Vec3 => v₂ ⟨t, ht⟩ x) =ᵐ[μ₃]
          (fun x : Vec3 => hmCut.toLp _ x) := by
      exact (Lp.ext_iff.mp hvA).filter_mono hsmallAE
    have hcutAE :
        (fun x : Vec3 => hmCut.toLp _ x) =ᵐ[μ₃]
          (fun x => (Classical.choose weakContL3_cutoff_exists) x •
            WithLp.toLp 2 (u (x, t))) := by
      filter_upwards [hmCut.coeFn_toLp.filter_mono
        hsmallAE]
        with x hx
      simpa [parabolicHomeomorph_symm_apply] using hx
    have hUAE :
        (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) =ᵐ[μ₃]
          (fun x => hmU.toLp _ x) := hmU.coeFn_toLp.symm
    filter_upwards [(hmemSmall ⟨t, ht⟩).coeFn_toLp,
      hclassAE, hcutAE, hχoneAE, hUAE] with x hvx hclass hcut hχ hU
    calc
      v ⟨t, ht⟩ x = v₂ ⟨t, ht⟩ x := hvx
      _ = hmCut.toLp _ x := hclass
      _ = (Classical.choose weakContL3_cutoff_exists) x •
          WithLp.toLp 2 (u (x, t)) := hcut
      _ = WithLp.toLp 2 (u (x, t)) := by rw [hχ, one_smul]
      _ = hmU.toLp _ x := hU

end ESS
