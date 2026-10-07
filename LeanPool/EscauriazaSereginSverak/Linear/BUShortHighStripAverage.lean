/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellWeightedAverage
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellAverageAlgebra
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRegionalSummability

/-!
# High-strip integrability from Gaussian averages

A Gaussian velocity average on every high-strip dyadic cell implies
integrability of each fixed weighted quadratic density on the entire
short-time high strip.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Gaussian velocity averages give global integrability of any fixed
nonnegative short-time weight with the cell-center Gaussian bound
(`lem:bu-small-time`). -/
theorem bu_short_high_strip_integrable_of_average
    (scale c b β G Cw Cg : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hc : 0 ≤ c) (hβ : 0 < β)
    (hGtan : G ≤ 1 / 16) (hGnorm : G ≤ β / 48)
    (hbβ : b ≤ β / 48)
    (hCw : 0 ≤ Cw) (hCg : 0 ≤ Cg)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hcont : ContinuousOn v
      ({x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) (3 / 2)))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)) v Dv D2v Dtv)
    (hlocal : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)))),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (Real.sqrt (spatialGradientSq v Dv z) +
          vec3EuclideanNorm (v z)))
    (hAvg : ∀ (k : ℤ), 1 ≤ k → ∀ (m : Fin 3 → ℤ) (ell : Fin 2048),
      (buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale).Nonempty →
      let d := Foundation.buSmallTimeDyadicScale k
      let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
      let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
      (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
        ∂(volume : Measure ParabolicPoint)) ≤
          Cg * d ^ 2 *
          Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
          Real.exp (-(β * Y 2 ^ 2 / (12 * d))))
    (W : ParabolicPoint → ℝ)
    (hWcont : ContinuousOn W
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2})
    (hW : ∀ (k : ℤ), 1 ≤ k → ∀ (m : Fin 3 → ℤ) (ell : Fin 2048)
      (z : ParabolicPoint),
      z ∈ buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale →
      0 ≤ W z ∧
        W z ≤ Cw *
          Real.exp (-(((Foundation.buSmallTimeDyadicCellCenter k m ell).1 0) ^ 2 +
            ((Foundation.buSmallTimeDyadicCellCenter k m ell).1 1) ^ 2) / 8) *
          Real.exp (b * ((Foundation.buSmallTimeDyadicCellCenter k m ell).1 2) ^ 2)) :
    IntegrableOn (fun z => W z *
      (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z))
      (buShortHighStrip scale) volume := by
  let E := fun z => vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  let F := fun z => W z * E z
  let Ce := 1 + 256 * (1 + c ^ 2 + 128)
  let a : ℝ := 1 / (16 * 16384)
  let b₀ : ℝ := β / (48 * 16384)
  let K₀ : ℝ := (Real.exp (a / 4) * (a + 2) / a) ^ 2 *
    (Real.exp (b₀ / 4) * (1 + 2 / b₀))
  let K := Cw * Ce * Cg * K₀
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  have hK : 0 ≤ K := by dsimp [K, K₀, a, b₀]; positivity
  have hE0 (z : ParabolicPoint) : 0 ≤ E z := by
    dsimp [E, spatialGradientSq]
    positivity
  have hCellInt (n : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
      IntegrableOn F
        (buShortShiftedDyadicCell (n + 1 : ℤ) m ell ∩
          buShortHighStrip scale) volume := by
    let k : ℤ := n + 1
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let B := Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
      Real.exp (b * Y 2 ^ 2)
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hBound (z : ParabolicPoint)
        (hz : z ∈ buShortShiftedDyadicCell k m ell ∩
          buShortHighStrip scale) : ‖W z‖ ≤ B := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hW k hk m ell z hz).1]
      exact (hW k hk m ell z hz).2
    exact bu_short_cell_fragment_density_integrable scale hscale k m ell
      hweak hlocal W hWcont B hBound
  have hCellBound (n : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
      (∫ z in buShortShiftedDyadicCell (n + 1 : ℤ) m ell ∩
        buShortHighStrip scale,
        ‖F z‖ ∂(volume : Measure ParabolicPoint)) ≤
          K * ((2 : ℝ) ^ (1 * (n + 1)) *
            Real.exp (-((β / 12) * (2 : ℝ) ^ (n + 1)))) *
              buShortSpatialProfile m := by
    let k : ℤ := n + 1
    let Cell := buShortShiftedDyadicCell k m ell
    let S := Cell ∩ buShortHighStrip scale
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hSmeas : MeasurableSet S :=
      (bu_short_shifted_dyadic_cell_measurable k m ell).inter
        (buShortHighStrip_measurable scale)
    have hNormEq : (∫ z in S, ‖F z‖ ∂(volume : Measure ParabolicPoint)) =
        ∫ z in S, F z ∂(volume : Measure ParabolicPoint) := by
      apply setIntegral_congr_fun hSmeas
      intro z hz
      change ‖F z‖ = F z
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (hW k hk m ell z hz).1 (hE0 z))]
    rw [hNormEq]
    by_cases hNonempty : S.Nonempty
    · obtain ⟨z₀, hz₀⟩ := hNonempty
      let d := Foundation.buSmallTimeDyadicScale k
      let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
      let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
      let B := Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
        Real.exp (b * Y 2 ^ 2)
      have hAvg' := hAvg k hk m ell ⟨z₀, hz₀⟩
      have hWeighted := bu_short_cell_weighted_average_bound scale c b Cw
        hscale hscale1 hc hCw k hk m ell hcont hweak hlocal hineq
        W hWcont (hW k hk m ell) z₀ hz₀
      have hYphys := (bu_short_high_cell_geometry scale hscale hscale1
        k hk m ell z₀ hz₀).1
      have hY : 2 ≤ Y 2 := by
        change 2 < scale * Y 2 at hYphys
        nlinarith only [hYphys, hscale1, hscale]
      have hAlg := bu_short_cell_average_algebra β G b Cw Ce Cg
        (∫ z in S, F z ∂(volume : Measure ParabolicPoint))
        (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint))
        hβ hGtan hGnorm hbβ hCw hCe hCg k hk m ell hY
        hWeighted hAvg'
      have hRewrite := bu_short_dyadic_tail_rewrite β K
        (buShortSpatialProfile m) n
      have hKDef : K = Cw * Ce * Cg * K₀ := rfl
      have hOut : (∫ z in S, F z ∂(volume : Measure ParabolicPoint)) ≤
          K / d * Real.exp (-(β / (12 * d))) *
            buShortSpatialProfile m := by
        simpa only [K, K₀, a, b₀, d] using hAlg
      calc
        _ ≤ K / d * Real.exp (-(β / (12 * d))) *
            buShortSpatialProfile m := hOut
        _ = K * ((2 : ℝ) ^ (1 * (n + 1)) *
            Real.exp (-((β / 12) * (2 : ℝ) ^ (n + 1)))) *
              buShortSpatialProfile m := by
          simpa only [k, one_mul, mul_assoc] using hRewrite
    · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hNonempty
      rw [hEmpty, setIntegral_empty]
      have hP : 0 ≤ buShortSpatialProfile m := by
        dsimp [buShortSpatialProfile]
        exact mul_nonneg (bu_short_int_profile_nonneg _)
          (mul_nonneg (bu_short_int_profile_nonneg _)
            (bu_short_int_profile_nonneg _))
      positivity
  have hSsub : buShortHighStrip scale ⊆
      (Set.univ ×ˢ Ioo (1 / 2 : ℝ) 1 : Set ParabolicPoint) := by
    intro z hz
    exact ⟨Set.mem_univ _, ⟨hz.2.1, hz.2.2⟩⟩
  exact bu_short_integrable_on_region_of_cell_bounds 1 (β / 12) K
    (by positivity) (buShortHighStrip scale)
    (buShortHighStrip_measurable scale) hSsub F hCellInt hCellBound

end ESS
