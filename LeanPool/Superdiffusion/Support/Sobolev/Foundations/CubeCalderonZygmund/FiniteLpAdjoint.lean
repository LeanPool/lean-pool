/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpBelowTwo

/-!
# Adjoint transfer for supplied cube `Lᵖ` data

Derived from the Dirichlet and Neumann arguments ported from
scottnarmstrong/CoarseGraining at c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4.
The radial-truncation, Hölder and exponent calculations are independent of the
boundary condition. Clients supply the adjoint field, its estimate and the
cross-pairing identity. No prior `Lᵖ` membership of the field being estimated is
assumed.
-/

@[expose] public section

namespace HCPolySupport.CubeCalderonZygmund

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem cubeNormalizedVolume_eq_smul_openCubeVolume {d : ℕ} (Q : TriadicCube d) :
    (cubeBoundedMeasurableDomain Q).normalizedVolume =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (openCubeSet Q) := by
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem memLp_hilbertField_cubeNormalized_two {d : ℕ} {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (hilbertifyVecField F) 2 (cubeBoundedMeasurableDomain Q).normalizedVolume := by
  rw [cubeNormalizedVolume_eq_smul_openCubeVolume]
  exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure ENNReal.ofReal_ne_top

private theorem integrable_vecDot_cubeNormalized {d : ℕ} {Q : TriadicCube d}
    {F G : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    Integrable (fun x => vecDot (F x) (G x))
      (cubeBoundedMeasurableDomain Q).normalizedVolume := by
  rw [cubeNormalizedVolume_eq_smul_openCubeVolume]
  exact (integrableOn_vecDot_of_memVectorL2 hF hG).smul_measure ENNReal.ofReal_ne_top

private theorem normalizedEuclideanLpENorm_eq_eLpNorm_hilbertifyVecField
    {d : ℕ} (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) {f : Vec d → Vec d}
    (hf : AEStronglyMeasurable (hilbertifyVecField f) U.normalizedVolume) :
    U.normalizedEuclideanLpENorm p f = eLpNorm (hilbertifyVecField f) p U.normalizedVolume := by
  rw [← eLpNorm_norm _ hf]
  exact congrArg (eLpNorm · p U.normalizedVolume)
    (funext fun x => euclideanNorm_eq_norm_ofVec (f x))

private theorem eLpNorm_radialTruncation_eq_truncatedMoment_root
    {alpha : Type*} {d : ℕ} [MeasurableSpace alpha] {mu : Measure alpha}
    (q : FiniteLpExponent) (n : ℕ) (F : alpha → HilbertVec d)
    (hF : AEStronglyMeasurable F mu) :
    eLpNorm (INTERNAL.hilbertRadialTruncation q.exponent.toReal n F)
      q.conjugate.exponent mu =
        (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂mu) ^
          (1 - q.exponent.toReal⁻¹) := by
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hqreal : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hreal : q.exponent.toReal.HolderConjugate q.conjugate.exponent.toReal :=
    ENNReal.HolderConjugate.toReal hqreal
  have hexponent : (q.conjugate.exponent.toReal)⁻¹ = 1 - q.exponent.toReal⁻¹ := by
    have hsum := hreal.one_div_add_one_div
    rw [one_div] at hsum
    norm_num at hsum
    linarith
  have hnonzero : q.conjugate.exponent.toReal ≠ 0 := by
    exact ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt))
      q.conjugate.lt_top.ne |>.ne'
  calc
    eLpNorm (INTERNAL.hilbertRadialTruncation q.exponent.toReal n F)
        q.conjugate.exponent mu =
        ((eLpNorm (INTERNAL.hilbertRadialTruncation q.exponent.toReal n F)
          q.conjugate.exponent mu) ^ q.conjugate.exponent.toReal) ^
          (q.conjugate.exponent.toReal)⁻¹ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hnonzero, ENNReal.rpow_one]
    _ = _ := by
      rw [INTERNAL.eLpNorm_hilbertRadialTruncation_rpow_conjugate_eq_truncatedMoment q n F hF,
        hexponent]

/-- A finite adjoint bound and cross-pairing identity yield the supplied-field
`Lᵖ` estimate on any cube, independently of the adjoint boundary condition. -/
theorem cubeEuclideanLpENorm_le_of_adjoint_bound {d : ℕ} (Q : TriadicCube d)
    (q : FiniteLpExponent) (h : CubeEuclideanLpField Q q)
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hadjoint : ∀ (G : CubeEuclideanL2LpField Q q.conjugate),
      MemVectorL2 (openCubeSet Q) G.toField →
        ∃ V : Vec d → Vec d, MemVectorL2 (openCubeSet Q) V ∧
          (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.conjugate.exponent V ≤
            K * (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
              q.conjugate.exponent G.toField ∧
          (∫ x, vecDot (F x) (G.toField x) ∂(cubeBoundedMeasurableDomain Q).normalizedVolume) =
            ∫ x, vecDot (h.toField x) (V x) ∂(cubeBoundedMeasurableDomain Q).normalizedVolume) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F ≤
      K * (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent h.toField := by
  let mu := (cubeBoundedMeasurableDomain Q).normalizedVolume
  let FH := hilbertifyVecField F
  let H := hilbertifyVecField h.toField
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hqreal : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hFtwo : MemLp FH 2 mu := memLp_hilbertField_cubeNormalized_two hF
  have hFmeas := hFtwo.aestronglyMeasurable
  have hHq : MemLp H q.exponent mu := by
    simpa only [H, mu, cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hmain : eLpNorm FH q.exponent mu ≤ K * eLpNorm H q.exponent mu := by
    conv_lhs => rw [← ENNReal.ofReal_toReal q.lt_top.ne]
    apply INTERNAL.eLpNorm_le_of_truncated_cross_bound hqreal hFmeas
    intro n
    have hFraw := (memHilbertVectorL2_hilbertifyVecField hF).aestronglyMeasurable
    let Gfield := INTERNAL.cubeRadialTruncationL2LpField Q q F hFraw n
    let G := Gfield.toField
    have hGtwo : MemVectorL2 (openCubeSet Q) G :=
      INTERNAL.cubeRadialTruncation_memVectorL2 Q q F hFraw n
    have hpair := integrable_vecDot_cubeNormalized hF hGtwo
    have hpairNonneg : 0 ≤ᵐ[mu] fun x => vecDot (F x) (G x) := by
      filter_upwards with x
      change 0 ≤ vecDot (F x) (INTERNAL.vectorRadialTruncation q.exponent.toReal n F x)
      rw [vecDot_comm, INTERNAL.vecDot_vectorRadialTruncation_self hqreal]
      split_ifs
      · exact Real.rpow_nonneg (euclideanNorm_nonneg _) _
      · exact le_rfl
    have hpoint : ∀ᵐ x ∂mu, ENNReal.ofReal (vecDot (F x) (G x)) =
        INTERNAL.truncatedMoment q.exponent.toReal n FH x := by
      filter_upwards with x
      simpa only [FH, G, Gfield] using!
        INTERNAL.ofReal_vecDot_vectorRadialTruncation_eq_truncatedMoment hqreal n F x
    have hmoment : (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n FH x ∂mu) =
        ENNReal.ofReal (∫ x, vecDot (F x) (G x) ∂mu) :=
      INTERNAL.lintegral_truncatedMoment_eq_ofReal_integral hpair hpairNonneg hpoint
    refine ⟨by rw [hmoment]; exact ENNReal.ofReal_ne_top, ?_⟩
    obtain ⟨V, hVtwo, hVbound, hcross⟩ := hadjoint Gfield hGtwo
    have hVmeas := (memLp_hilbertField_cubeNormalized_two hVtwo).aestronglyMeasurable
    have hGq : MemLp (hilbertifyVecField G) q.conjugate.exponent mu := by
      simpa only [mu, G, cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        hilbertifyVecField] using! Gfield.euclideanMemLp
    rw [normalizedEuclideanLpENorm_eq_eLpNorm_hilbertifyVecField
        (cubeBoundedMeasurableDomain Q) _ hVmeas,
      normalizedEuclideanLpENorm_eq_eLpNorm_hilbertifyVecField
        (cubeBoundedMeasurableDomain Q) _ hGq.aestronglyMeasurable] at hVbound
    have hVq : MemLp (hilbertifyVecField V) q.conjugate.exponent mu := by
      apply lt_of_le_of_lt hVbound
      exact ENNReal.mul_lt_top hK.lt_top hGq.eLpNorm_lt_top
    have hholder := INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul hHq hVq
    have hGnorm : eLpNorm (hilbertifyVecField G) q.conjugate.exponent mu =
        (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n FH x ∂mu) ^
          (1 - q.exponent.toReal⁻¹) := by
      simpa only [FH, G, Gfield, hilbertifyVecField] using!
        eLpNorm_radialTruncation_eq_truncatedMoment_root q n FH hFmeas
    calc
      (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n FH x ∂mu) =
          ENNReal.ofReal (∫ x, vecDot (F x) (G x) ∂mu) := hmoment
      _ = ENNReal.ofReal (∫ x, vecDot (h.toField x) (V x) ∂mu) := by rw [hcross]
      _ ≤ ENNReal.ofReal |∫ x, vecDot (h.toField x) (V x) ∂mu| :=
        ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ENNReal.ofReal ((eLpNorm H q.exponent mu).toReal *
          (eLpNorm (hilbertifyVecField V) q.conjugate.exponent mu).toReal) :=
        ENNReal.ofReal_le_ofReal hholder
      _ = eLpNorm H q.exponent mu * eLpNorm (hilbertifyVecField V) q.conjugate.exponent mu := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hHq.eLpNorm_lt_top.ne,
          ENNReal.ofReal_toReal hVq.eLpNorm_lt_top.ne]
      _ ≤ eLpNorm H q.exponent mu *
          (K * eLpNorm (hilbertifyVecField G) q.conjugate.exponent mu) := by gcongr
      _ = (K * eLpNorm H q.exponent mu) *
          (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n FH x ∂mu) ^
            (1 - q.exponent.toReal⁻¹) := by rw [hGnorm]; ac_rfl
  rw [normalizedEuclideanLpENorm_eq_eLpNorm_hilbertifyVecField
      (cubeBoundedMeasurableDomain Q) _ hFmeas,
    normalizedEuclideanLpENorm_eq_eLpNorm_hilbertifyVecField
      (cubeBoundedMeasurableDomain Q) _ hHq.aestronglyMeasurable]
  exact hmain

end

end HCPolySupport.CubeCalderonZygmund
