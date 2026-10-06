/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakChild
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffOscillation
public import LeanPool.HighContrastHomogenization.Provider.Response.MeanDefect

/-!
# High-contrast homogenization: Provider.Response.AdaptedLinearOscillation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Linear cutoff oscillation on an adapted child

An aligned physical child pulls back to an ordinary triadic descendant.  The
cutoff loses one full power of the child depth, while the endpoint field norm
uses a half-power weight.  Oscillation duality therefore controls the literal
cutoff readout by the terminal adapted weak seminorm.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem memVectorL2_constMatVecMul (A : Mat d) {U : Set (Vec d)}
    {v : Vec d → Vec d} (hv : MemVectorL2 U v) :
    MemVectorL2 U (fun x ↦ matVecMul A (v x)) := by
  let L : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  refine MemLp.of_le_mul (c := ‖L‖) hv ?_ ?_
  · exact (continuous_matVecMul A).comp_aestronglyMeasurable hv.aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [L, matVecMul] using! L.le_opNorm (v x)

/-- An aligned child label gives the corresponding ordinary descendant of the
terminal reference cube. -/
theorem translateCube_mem_descendantsAtDepth_of_mem_alignedIndex
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q s t) :
    translateCube w (originCube d s) ∈
      descendantsAtDepth (originCube d t) (Int.toNat (t - s)) := by
  have hgap : (Int.toNat (t - s) : ℤ) = t - s := by omega
  have hwOne : w ∈ alignedIndex (1 : Mat d) s t := by
    rw [alignedIndex_one_eq hq hst]
    exact hw
  have himage : translateCube w
      (originCube d (t - (Int.toNat (t - s) : ℤ))) ∈
      (alignedIndex (1 : Mat d) (t - (Int.toNat (t - s) : ℤ)) t).image
        (fun z ↦ translateCube z
          (originCube d (t - (Int.toNat (t - s) : ℤ)))) := by
    apply Finset.mem_image.mpr
    exact ⟨w, by simpa [hgap] using hwOne, rfl⟩
  rw [image_translateCube_alignedIndex_one_eq_descendantsAtDepth] at himage
  simpa [hgap] using himage

private theorem cutoffDecay_le_depthWeight (R : TriadicCube d) {H : ℤ}
    (C : ℝ) (hC : 0 ≤ C) (j : ℕ) :
    C * (3 : ℝ) ^ (-(H + (j : ℤ))) ≤
      C * (3 : ℝ) ^ (-H) *
        (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹ *
          cubeBesovCircDepthWeight R (1 / 2) (j + 1) := by
  have hweight : ∀ n : ℕ, 0 < cubeBesovCircDepthWeight R (1 / 2) n := by
    intro n
    unfold cubeBesovCircDepthWeight cubeScaleFactor
    positivity
  have hthird : (3 : ℝ)⁻¹ ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  induction j with
  | zero =>
      simp only [Nat.cast_zero, add_zero]
      calc
        C * (3 : ℝ) ^ (-H) ≤ C * (3 : ℝ) ^ (-H) := le_rfl
        _ = C * (3 : ℝ) ^ (-H) *
            (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹ *
              cubeBesovCircDepthWeight R (1 / 2) 1 := by
          rw [mul_assoc, inv_mul_cancel₀ (hweight 1).ne', mul_one]
  | succ j ih =>
      have hpow : (3 : ℝ) ^ (-(H + ((j + 1 : ℕ) : ℤ))) =
          (3 : ℝ)⁻¹ * (3 : ℝ) ^ (-(H + (j : ℤ))) := by
        rw [show -(H + ((j + 1 : ℕ) : ℤ)) = -1 + -(H + (j : ℤ)) by omega,
          zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, zpow_one]
      have hbase : 0 ≤ C * (3 : ℝ) ^ (-H) *
          (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹ *
            cubeBesovCircDepthWeight R (1 / 2) (j + 1) := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hC (zpow_nonneg (by norm_num) _))
            (inv_nonneg.mpr (hweight 1).le)) (hweight (j + 1)).le
      calc
        C * (3 : ℝ) ^ (-(H + ((j + 1 : ℕ) : ℤ))) =
            (3 : ℝ)⁻¹ * (C * (3 : ℝ) ^ (-(H + (j : ℤ)))) := by
          rw [hpow]
          ring
        _ ≤ (3 : ℝ)⁻¹ * (C * (3 : ℝ) ^ (-H) *
              (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹ *
                cubeBesovCircDepthWeight R (1 / 2) (j + 1)) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C * (3 : ℝ) ^ (-H) *
              (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹ *
                cubeBesovCircDepthWeight R (1 / 2) (j + 1)) :=
          mul_le_mul_of_nonneg_right hthird hbase
        _ = C * (3 : ℝ) ^ (-H) *
            (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹ *
              cubeBesovCircDepthWeight R (1 / 2) (j + 1 + 1) := by
          rw [cubeBesovCircDepthWeight_succ R (1 / 2) (j + 1)]
          ring

/-- The literal cutoff-oscillation readout on an aligned adapted child is
controlled by the terminal metric weak seminorm.  All child-cardinality,
scale, cutoff, and affine-metric factors remain explicit. -/
theorem ofReal_abs_volumeAverage_adaptedCellAt_cutoffOscillation_le
    [NeZero d] {q S : Mat d} (hq : q.PosDef) (hS : S.PosDef)
    {s t : ℤ} (hst : s ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q s t) (F : Vec d → BlockVec d)
    (alpha : BlockCoord d)
    (hF₁ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S (F x).1))
    (hF₂ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S⁻¹ (F x).2)) :
    ENNReal.ofReal |volumeAverage (adaptedCellAt q s w) (fun x ↦
        (adaptedPreYoungCutoff q hq t x -
          volumeAverage (adaptedCellAt q s w)
            (adaptedPreYoungCutoff q hq t)) *
          toFullBlockVec (F x) alpha)| ≤
      ENNReal.ofReal
          (1024 * (d : ℝ) ^ 4 *
            (max 1 (max smoothTransitionProfile.derivBound
              smoothTransitionProfile.secondDerivBound)) ^ 2 *
            (3 : ℝ) ^ (-(t - s)) *
            (cubeBesovCircDepthWeight
              (translateCube w (originCube d s)) (1 / 2) 1)⁻¹) *
        (ENNReal.ofReal (Real.sqrt
            ((descendantsAtDepth (originCube d t) (Int.toNat (t - s))).card : ℝ)) *
          ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          ENNReal.ofReal (Real.sqrt (max
            (matrixFrobeniusNormSq S⁻¹) (matrixFrobeniusNormSq S))) *
          adaptedWeakSeminorm q t (1 / 2) (fun x ↦
            ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d))) := by
  classical
  let H : ℕ := Int.toNat (t - s)
  let R : TriadicCube d := translateCube w (originCube d s)
  let phi : Vec d → ℝ := fun y ↦
    adaptedPreYoungCutoff q hq t (matVecMul q y)
  let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
  let G : Vec d → ℝ := fun y ↦ toFullBlockVec (F (matVecMul q y)) alpha
  let Cd : ℝ := 1024 * (d : ℝ) ^ 4 *
    (max 1 (max smoothTransitionProfile.derivBound
      smoothTransitionProfile.secondDerivBound)) ^ 2
  let K : ℝ := Cd * (3 : ℝ) ^ (-(t - s)) *
    (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹
  let B : ℝ≥0∞ :=
    ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t) H).card : ℝ)) *
      ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
      ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
      ENNReal.ofReal (Real.sqrt (max
        (matrixFrobeniusNormSq S⁻¹) (matrixFrobeniusNormSq S))) *
      adaptedWeakSeminorm q t (1 / 2) (fun x ↦
        ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d))
  have hR : R ∈ descendantsAtDepth (originCube d t) H := by
    exact translateCube_mem_descendantsAtDepth_of_mem_alignedIndex hq hst hw
  have hgap : (H : ℤ) = t - s := by dsimp only [H]; omega
  have hRscale : R.scale = s := rfl
  have hCd : 0 ≤ Cd := by dsimp only [Cd]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg hCd (zpow_nonneg (by norm_num) _))
      (inv_nonneg.mpr (cubeBesovCircDepthWeight_nonneg R (1 / 2) 1))
  have hKpos : 0 < K := by
    have hCdpos : 0 < Cd := by
      dsimp only [Cd]
      have hd : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.out : d ≠ 0)
      positivity
    have hwpos : 0 < cubeBesovCircDepthWeight R (1 / 2) 1 := by
      unfold cubeBesovCircDepthWeight cubeScaleFactor
      positivity
    exact mul_pos (mul_pos hCdpos (zpow_pos (by norm_num) _)) (inv_pos.mpr hwpos)
  have hphiCont : Continuous phi := by
    exact (adaptedPreYoungCutoff_smooth hq t).continuous.comp (continuous_matVecMul q)
  have hphiInt : IntegrableOn phi (cubeSet R) volume := by
    exact (hphiCont.continuousOn.integrableOn_compact
      (isBounded_cubeSet R).isCompact_closure).mono_set subset_closure
  have hphiAvg0 : 0 ≤ cubeAverage R phi :=
    le_cubeAverage_of_le R hphiInt (fun y ↦ adaptedPreYoungCutoff_nonneg hq t _)
  have hphiAvg2 : cubeAverage R phi ≤ 2 :=
    cubeAverage_le_of_le R hphiInt (fun y ↦ adaptedPreYoungCutoff_le_two hq t _)
  have hfTopR : MemLp f ∞ (normalizedCubeMeasure R) := by
    apply memLp_top_of_bound (hphiCont.sub continuous_const).aestronglyMeasurable 2
    exact _root_.Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · change -2 ≤ adaptedPreYoungCutoff q hq t (matVecMul q y) - cubeAverage R phi
        linarith only [adaptedPreYoungCutoff_nonneg hq t (matVecMul q y), hphiAvg2]
      · change adaptedPreYoungCutoff q hq t (matVecMul q y) - cubeAverage R phi ≤ 2
        linarith only [adaptedPreYoungCutoff_le_two hq t (matVecMul q y), hphiAvg0]
  have hf : MemLp f 1 (normalizedCubeMeasure R) :=
    hfTopR.mono_exponent (by norm_num)
  have hfInt : IntegrableOn f (cubeSet R) volume :=
    (hphiInt.sub (integrableOn_const (volume_cubeSet_lt_top R).ne)).congr
      (_root_.Filter.Eventually.of_forall fun y ↦ rfl)
  have hfBound : ∀ y ∈ cubeSet R, |f y| ≤ 2 := by
    intro y hy
    rw [abs_le]
    constructor <;>
      linarith only [adaptedPreYoungCutoff_nonneg hq t (matVecMul q y),
        adaptedPreYoungCutoff_le_two hq t (matVecMul q y), hphiAvg0, hphiAvg2]
  have hfFluct : ∀ j : ℕ, ∀ T ∈ descendantsAtDepth R j,
      MemLp (cubeFluctuation T f) ∞ (normalizedCubeMeasure T) := by
    intro j T hT
    change MemLp (f - fun x => cubeAverage T f) ∞ (normalizedCubeMeasure T)
    exact (memLp_on_descendant_of_memLp hT hfTopR).sub
      (memLp_const (cubeAverage T f))
  have hmean : cubeAverage R f = 0 := by
    simpa only [f, cubeFluctuation] using! cubeAverage_cubeFluctuation R phi
  have hres : ∀ j : ℕ, ∀ y ∈ cubeSet R,
      |cubeProjectionResidual R j f y| ≤
        K * cubeBesovCircDepthWeight R (1 / 2) (j + 1) := by
    intro j y hy
    obtain ⟨T, hT, hyT⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hy
    have hphiTopT : MemLp phi ∞ (normalizedCubeMeasure T) := by
      apply memLp_top_of_bound hphiCont.aestronglyMeasurable 2
      exact _root_.Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (adaptedPreYoungCutoff_nonneg hq t _)]
        exact adaptedPreYoungCutoff_le_two hq t _
    have hphiTwoT : MemLp phi 2 (normalizedCubeMeasure T) :=
      hphiTopT.mono_exponent (by norm_num)
    have hTscale : T.scale = s - (j : ℤ) := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hT, hRscale]
    have hosc := adaptedPreYoungCutoff_pullback_sub_cubeAverage
      (s := s - (j : ℤ)) (t := t) (H := (t - s) + (j : ℤ))
      hq hTscale (by omega) hyT
    have hdecay := cutoffDecay_le_depthWeight (H := t - s) R Cd hCd j
    unfold cubeProjectionResidual
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hT hyT]
    have havg : cubeAverage T f = cubeAverage T phi - cubeAverage R phi := by
      simpa only [f] using
        cubeAverage_sub_const_of_memLp_two T hphiTwoT (cubeAverage R phi)
    rw [havg]
    calc
      |(phi y - cubeAverage R phi) -
          (cubeAverage T phi - cubeAverage R phi)| =
          |cubeAverage T phi - phi y| := by
        rw [show (phi y - cubeAverage R phi) -
            (cubeAverage T phi - cubeAverage R phi) =
              -(cubeAverage T phi - phi y) by ring, abs_neg]
      _ ≤ Cd * (3 : ℝ) ^ (-((t - s) + (j : ℤ))) := by
        simpa only [phi, Cd, Real.norm_eq_abs] using hosc
      _ ≤ K * cubeBesovCircDepthWeight R (1 / 2) (j + 1) := by
        simpa only [K] using hdecay
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hraw₁ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).1) := by
    have h := memVectorL2_constMatVecMul S⁻¹ hF₁
    simpa only [matVecMul_mul, Matrix.nonsing_inv_mul S hSdet, matVecMul_one] using h
  have hraw₂ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).2) := by
    have h := memVectorL2_constMatVecMul S hF₂
    simpa only [matVecMul_mul, Matrix.mul_nonsing_inv S hSdet, matVecMul_one] using h
  have hchildSub := adaptedCellAt_subset_of_mem_alignedIndex hq hst hw
  have hqdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hU : MeasurableSet (adaptedCellAt q s w) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet
  have hpull₁ := memVectorL2_affinePullback hqdet hU
    (memVectorL2_mono hchildSub hraw₁)
  have hpull₂ := memVectorL2_affinePullback hqdet hU
    (memVectorL2_mono hchildSub hraw₂)
  rw [matImage_inv_adaptedCellAt_eq hq s w] at hpull₁ hpull₂
  have hidentityCell : adaptedCellAt (1 : Mat d) s w = openCubeSet R := by
    dsimp only [R]
    rw [Recurrence.adaptedCellAt_eq_image]
    have hone : matVecMul (1 : Mat d) = id :=
      funext fun x ↦ matVecMul_one x
    rw [hone, Set.image_id]
    rfl
  have hGInt : IntegrableOn G (cubeSet R) volume := by
    cases alpha with
    | inl i =>
        have hi := integrableOn_component
          (U := adaptedDomainAt Matrix.PosDef.one s w) hpull₁ i
        change Integrable (fun y ↦ (F (matVecMul q y)).1 i)
          (volume.restrict (cubeSet R))
        rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
        simpa only [adaptedDomainAt_carrier, hidentityCell] using! hi
    | inr i =>
        have hi := integrableOn_component
          (U := adaptedDomainAt Matrix.PosDef.one s w) hpull₂ i
        change Integrable (fun y ↦ (F (matVecMul q y)).2 i)
          (volume.restrict (cubeSet R))
        rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
        simpa only [adaptedDomainAt_carrier, hidentityCell] using! hi
  have hchild : ∀ N : ℕ,
      ENNReal.ofReal (cubeBesovCircPartialNorm R (1 / 2) 1 1 N G) ≤ B := by
    intro N
    simpa only [R, H, G, B] using
      ofReal_cubeBesovCircPartialNorm_child_rawPullback_le
        hq hS rfl hR N F alpha hF₁ hF₂
  have hpair : ENNReal.ofReal |cubeBesovPairing R f G| ≤ ENNReal.ofReal K * B := by
    by_cases hB : B = ⊤
    · calc
        ENNReal.ofReal |cubeBesovPairing R f G| ≤ ⊤ := le_top
        _ = ENNReal.ofReal K * B := by
          rw [hB]
          exact (ENNReal.mul_top
            (ENNReal.ofReal_ne_zero_iff.mpr hKpos)).symm
    · have hW : ∀ N : ℕ, cubeBesovCircPartialNorm R (1 / 2) 1 1 N G ≤ B.toReal := by
        intro N
        have hmono := ENNReal.toReal_mono hB (hchild N)
        rw [ENNReal.toReal_ofReal
          (cubeBesovCircPartialNorm_nonneg R (1 / 2) 1 1 N G)] at hmono
        exact hmono
      have hdual := abs_cubeBesovPairing_le_mul_of_uniform_cubeBesovCircPartialNorm_bound
        R f G hK (by norm_num : (0 : ℝ) ≤ 2) hGInt hfInt hf hfBound hfFluct hmean hres hW
      have hof := ENNReal.ofReal_le_ofReal hdual
      rw [ENNReal.ofReal_mul hK] at hof
      simpa [ENNReal.ofReal_toReal hB] using hof
  have hphysical : volumeAverage (adaptedCellAt q s w) (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
        toFullBlockVec (F x) alpha) = cubeBesovPairing R f G := by
    rw [volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq,
      volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq]
    rfl
  rw [hphysical]
  simpa only [K, Cd, R, H, B] using hpair

end

end HCPolySupport.HighContrast.Response
