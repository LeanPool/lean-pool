/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGlobalDensities

/-!
# Negative-phase bound on compact positive-phase sets

Removing the lower-time and spatial cutoffs leaves only the
exponentially small negative-phase integral.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- A compact set in the normal cutoff plateau has only the
negative-phase contribution after both compact cutoffs are removed. -/
theorem bu_short_compact_mass_le_gap :
    ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ (M scale c₁ C₁ C₂ a : ℝ)
        (_hM : 0 < M) (_hscale : 0 < scale) (_hscale1 : scale ≤ 1)
        (_hc₁ : 0 ≤ c₁) (_hC₁ : 0 ≤ C₁)
        (_hN : ∀ scale y : ℝ,
          |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
        (_hC₂ : 0 ≤ C₂)
        (_hP : ∀ x : ℝ,
          |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
        (_hsmall : c * 36 * (c₁ * scale) ^ 2 ≤ 1 / 2)
        (_ha : max a₀ 1 < a)
        (w : ParabolicPoint → Vec3)
        (Dw : ParabolicPoint → Fin 3 → Vec3)
        (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtw : ParabolicPoint → Vec3)
        (_hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
        (_hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
        (_hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
          w Dw D2w Dtw)
        (_hL2 : ∀ S : Set ParabolicPoint,
          S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
          Bornology.IsBounded S →
          (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
            ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
        (_hineq : ∀ᵐ z ∂(volume.restrict
          (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
          vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
            c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
              vec3EuclideanNorm (w z)))
        (_hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
          vec3EuclideanNorm (w z) ≤
            Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
        (_hJ : IntegrableOn (buShortTangentialDensity scale w Dw)
          (buShortWideGapRegion scale) volume)
        (_hWP : IntegrableOn (buShortWeightedPolynomialDensity scale a w Dw)
          (buShortHighStrip scale) volume)
        (_hWQ : IntegrableOn (buShortWeightedDensity scale a w Dw)
          (buShortHighStrip scale) volume)
        (S : Set ParabolicPoint)
        (_hScompact : IsCompact S) (_hSne : S.Nonempty)
        (_hSgap : ∀ z ∈ S,
          parabolicHomeomorph z ∈ buShortAboveGap scale),
        let v := buAffineField (-scale ^ 2 / 2) scale w
        (∫ z in S, buShortShiftedWeight scale a z *
          vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint)) ≤
          16 * c * buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
            Real.exp (-(a * buShortD scale)) *
            (∫ z in buShortWideGapRegion scale,
              buShortTangentialDensity scale w Dw z
              ∂(volume : Measure ParabolicPoint)) := by
  obtain ⟨a₀, c, ha₀, hc, hCore⟩ := bu_short_core_mass_bound
  refine ⟨a₀, c, ha₀, hc, ?_⟩
  intro M scale c₁ C₁ C₂ a hM hscale hscale1 hc₁
    hC₁ hN hC₂ hP hsmall ha w Dw D2w Dtw
    hcont hinit hweak hL2 hineq hgrowth hJ hWP hWQ
    S hScompact hSne hSgap
  obtain ⟨R₀, ε₀, hR₀, hε₀, hgeometry⟩ :=
    bu_short_compact_subset_core_eventually scale S
      hScompact hSne hSgap
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt R₀
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let J : ℝ := ∫ z in buShortWideGapRegion scale,
    buShortTangentialDensity scale w Dw z
    ∂(volume : Measure ParabolicPoint)
  let N : ℝ := ∫ z in buShortHighStrip scale,
    buShortWeightedDensity scale a w Dw z
    ∂(volume : Measure ParabolicPoint)
  let L : ℝ := ∫ z in S, buShortShiftedWeight scale a z *
    vec3EuclideanNorm (v z) ^ 2
    ∂(volume : Measure ParabolicPoint)
  let A : ℝ := 16 * c * buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
    Real.exp (-(a * buShortD scale)) * J
  let shell : ℕ → ℝ := fun n =>
    16 * c * buShortShellCoeff scale ((n : ℝ) + 1) c₁ ^ 2 * N
  let early : ℕ → ℝ → ℝ := fun n ε =>
    8 * c * (∫ z in buCutSupportSet
      (buShortFullCutoff scale ((n : ℝ) + 1) (by positivity) ε),
      buShortShiftedWeight scale a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
      ∂(volume : Measure ParabolicPoint))
  have hshell : Tendsto shell atTop (𝓝 0) := by
    have h := (buShortShellCoeff_tendsto_zero scale c₁).pow 2
    have h' : Tendsto (fun n : ℕ =>
        16 * c * buShortShellCoeff scale ((n : ℝ) + 1) c₁ ^ 2 * N)
        atTop (𝓝 (16 * c * 0 ^ 2 * N)) :=
      (tendsto_const_nhds.mul h).mul tendsto_const_nhds
    simpa only [shell, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
      zero_mul] using h'
  have hearly (n : ℕ) : Tendsto (early n)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have h := bu_short_shifted_early_error_tendsto_zero
      M scale ((n : ℝ) + 1) a hM hscale hscale1 hR
      w Dw D2w Dtw hcont hinit hweak hL2 hgrowth
    have h' := h.const_mul (8 * c)
    simpa only [early, mul_zero] using h'
  have hbound (n : ℕ) (hn : n₀ ≤ n)
      (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < ε₀) :
      L ≤ A + shell n + early n ε := by
    let R := (n : ℝ) + 1
    have hR : 1 ≤ R := by
      have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      dsimp [R]
      linarith only [hnnonneg]
    have hRgeom : R₀ ≤ R := by
      have hcast : (n₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      dsimp [R]
      linarith only [hn₀, hcast]
    have hScore : ∀ z ∈ S,
        parabolicHomeomorph z ∈ buShortCoreRegion scale R ε :=
      hgeometry R hRgeom ε hε hεsmall
    have hbound' := hCore scale R ε c₁ C₁ C₂ a
      hscale hscale1 hR hε hc₁ hC₁ hN hC₂ hP
      hsmall ha w Dw D2w Dtw hcont hweak hL2 hineq
      hJ hWP hWQ S hScompact.isClosed.measurableSet hScore
    convert hbound' using 1
    simp only [A, shell, early, J, N, v, R,
      buShortTangentialDensity, buShortWeightedDensity,
      buShortQuadraticEnergy]
    ring
  have hmain := bu_short_two_parameter_limit
    L A shell early n₀ ε₀ hε₀ hshell hearly hbound
  simpa only [L, A, J, v] using hmain

end ESS
