/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedLinearOscillation
public import LeanPool.HighContrastHomogenization.Provider.Response.LocalizedOptimizerObservables
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileFiniteness

/-!
# High-contrast homogenization: Provider.Response.SplitReadoutIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability of the adapted cutoff-split readouts

The terminal weak quantity controls every aligned-child mean and cutoff
oscillation.  Sample measurability then turns these pointwise bounds into the
four integrability families used by the primal and adjoint cutoff splits.
-/
namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem memVectorL2_matVecMul (A : Mat d) {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x ↦ matVecMul A (f x)) := by
  let L : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  refine MemLp.of_le_mul (c := ‖L‖) hf ?_ ?_
  · simpa only [L, matVecMul] using!
      L.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [L, matVecMul] using! L.le_opNorm (f x)

private theorem blockDiag_apply (A B : Mat d) (X : BlockVec d) :
    blockMatVecMul (blockDiag A B) X =
      ((matVecMul A X.1, matVecMul B X.2) : BlockVec d) := by
  apply Prod.ext
  · change matVecMul A X.1 + matVecMul 0 X.2 = matVecMul A X.1
    rw [zero_matVecMul, add_zero]
  · change matVecMul 0 X.1 + matVecMul B X.2 = matVecMul B X.2
    rw [zero_matVecMul, zero_add]

private theorem integrable_of_enorm_le_finite_mul_root
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} {root : Ω → ℝ≥0∞} {C : ℝ≥0∞}
    (hZ : AEStronglyMeasurable Z μ) (hC : C ≠ ⊤)
    (hroot : eLpNorm root 2 μ ≠ ⊤)
    (hbound : ∀ a, ENNReal.ofReal |Z a| ≤ C * root a) :
    Integrable Z μ := by
  have hnorm : eLpNorm Z 2 μ ≤ C * eLpNorm root 2 μ := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (μ := μ)
      (f := Z) (g := root) (c := C.toNNReal) (p := (2 : ℝ≥0∞)) hZ
      (_root_.Filter.Eventually.of_forall fun a ↦ by
        simpa only [Real.enorm_eq_ofReal_abs, enorm_eq_self,
          ENNReal.coe_toNNReal hC] using hbound a)
    simpa only [ENNReal.smul_def, ENNReal.coe_toNNReal hC] using h
  have hlt : C * eLpNorm root 2 μ < ⊤ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC)
      (lt_top_iff_ne_top.mpr hroot)
  have hmem : MemLp Z 2 μ := hnorm.trans_lt hlt
  exact hmem.integrable (by norm_num)

private theorem weakRoot_ne_top_of_quantity_ne_top {P : Measure (CoeffSpace d)}
    {root : CoeffSpace d → ℝ≥0∞}
    (h : eLpNorm root 2 P ^ (2 : ℕ) ≠ ⊤) :
    eLpNorm root 2 P ≠ ⊤ :=
  (ENNReal.pow_ne_top_iff.mp h).resolve_right (by norm_num)

private theorem cutoffOscillation_average_centering
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q s t)
    (X : Vec d → BlockVec d) (center : BlockVec d) (alpha : BlockCoord d)
    (hcentered₁ : MemVectorL2 (adaptedCell q t) (fun x ↦ (X x - center).1))
    (hcentered₂ : MemVectorL2 (adaptedCell q t) (fun x ↦ (X x - center).2)) :
    volumeAverage (adaptedCellAt q s w) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) * toFullBlockVec (X x) alpha) =
      volumeAverage (adaptedCellAt q s w) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) * toFullBlockVec (X x - center) alpha) := by
  let F : Vec d → BlockVec d := fun x ↦ X x - center
  let U := adaptedCellAt q s w
  let eta : Vec d → ℝ := fun x ↦ adaptedPreYoungCutoff q hq t x -
    volumeAverage U (adaptedPreYoungCutoff q hq t)
  have hUdom := Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w
  have hcut : IntegrableOn (adaptedPreYoungCutoff q hq t) U volume :=
    ((adaptedPreYoungCutoff_smooth hq t).continuous.continuousOn.integrableOn_compact
      hUdom.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  have hconst : IntegrableOn (fun _ : Vec d ↦
      volumeAverage U (adaptedPreYoungCutoff q hq t)) U volume :=
    integrableOn_const hUdom.volume_lt_top.ne (by simp)
  have heta : IntegrableOn eta U volume := hcut.sub hconst
  have havgEta : volumeAverage U eta = 0 := by
    rw [show eta = (adaptedPreYoungCutoff q hq t) -
        fun _ ↦ volumeAverage U (adaptedPreYoungCutoff q hq t) by rfl]
    rw [volumeAverage_sub hcut hconst,
      volumeAverage_const
        (ENNReal.toReal_pos (Recurrence.volume_adaptedCellAt_pos hq s w).ne'
          hUdom.volume_lt_top.ne).ne']
    ring
  have hcomp : IntegrableOn (fun x ↦ toFullBlockVec (F x) alpha) U volume := by
    cases alpha with
    | inl i =>
        simpa only [toFullBlockVec, adaptedDomainAt_carrier] using
          integrableOn_component (U := adaptedDomainAt hq s w)
            (memVectorL2_mono
              (adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) hcentered₁) i
    | inr i =>
        simpa only [toFullBlockVec, adaptedDomainAt_carrier] using
          integrableOn_component (U := adaptedDomainAt hq s w)
            (memVectorL2_mono
              (adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) hcentered₂) i
  have hetaMeas := heta.aestronglyMeasurable
  have hetaBound : ∀ᵐ x ∂volume.restrict U,
      ‖eta x‖ ≤ 2 + |volumeAverage U (adaptedPreYoungCutoff q hq t)| :=
    _root_.Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;>
        linarith only [adaptedPreYoungCutoff_nonneg hq t x,
          adaptedPreYoungCutoff_le_two hq t x,
          neg_abs_le (volumeAverage U (adaptedPreYoungCutoff q hq t)),
          le_abs_self (volumeAverage U (adaptedPreYoungCutoff q hq t))]
  have hetaF : IntegrableOn
      (fun x ↦ eta x * toFullBlockVec (F x) alpha) U volume := by
    simpa only [mul_comm] using! hcomp.bdd_mul hetaMeas hetaBound
  have hetaConst : IntegrableOn
      (fun x ↦ toFullBlockVec center alpha * eta x) U volume :=
    heta.const_mul _
  have hcoord : ∀ x, toFullBlockVec (X x) alpha =
      toFullBlockVec (F x) alpha + toFullBlockVec center alpha := by
    intro x
    cases alpha <;>
      simp only [F, toFullBlockVec, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply,
        sub_add_cancel]
  have hpoint : (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage U (adaptedPreYoungCutoff q hq t)) *
        toFullBlockVec (X x) alpha) =
    (fun x ↦ eta x * toFullBlockVec (F x) alpha) +
      fun x ↦ toFullBlockVec center alpha * eta x := by
    funext x
    rw [hcoord]
    dsimp only [eta, Pi.add_apply]
    ring
  have havgConst : volumeAverage U
      (fun x ↦ toFullBlockVec center alpha * eta x) =
      toFullBlockVec center alpha * volumeAverage U eta := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      volumeAverage_smul U (toFullBlockVec center alpha) eta
  rw [hpoint, volumeAverage_add hetaF hetaConst, havgConst, havgEta,
    mul_zero, add_zero]

/-- The centered child mean and its cutoff oscillation are bounded pointwise by
finite geometric factors times the normalized adapted weak root. -/
theorem centeredChild_readout_enorm_bounds [NeZero d]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {s t : ℤ} (hst : s ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q s t) (b : CoeffSpace d)
    (p r : Vec d) (center : BlockVec d) (alpha : BlockCoord d) :
    let X := diagonalWeakState hq t b p r
    let root := ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
      adaptedWeakSeminorm q t (1 / 2) (fun x ↦
        blockMatVecMul (blockDiag (matSqrt m0) (matSqrt m0)⁻¹)
          (X x - center))
    let R := translateCube w (originCube d s)
    let cardRoot := ENNReal.ofReal
      (Real.sqrt ((descendantsAtDepth (originCube d t)
        (Int.toNat (t - s))).card : ℝ))
    let metricRoot := ENNReal.ofReal (Real.sqrt (max
      (matrixFrobeniusNormSq (matSqrt m0)⁻¹)
      (matrixFrobeniusNormSq (matSqrt m0))))
    let meanCoeff := ENNReal.ofReal
      (cubeBesovScaleWeight (-(1 / 2 : ℝ)) R)⁻¹ * cardRoot *
        ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
          metricRoot
    let oscCoeff := ENNReal.ofReal
      (1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-(t - s)) *
        (cubeBesovCircDepthWeight R (1 / 2) 1)⁻¹) * cardRoot *
      ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
        metricRoot
    ENNReal.ofReal |toFullBlockVec
        (blockCellAverage (adaptedCellAt q s w) X) alpha -
          toFullBlockVec center alpha| ≤ meanCoeff * root ∧
      ENNReal.ofReal |volumeAverage (adaptedCellAt q s w) (fun x ↦
        (adaptedPreYoungCutoff q hq t x -
          volumeAverage (adaptedCellAt q s w)
            (adaptedPreYoungCutoff q hq t)) *
          toFullBlockVec (X x) alpha)| ≤ oscCoeff * root := by
  classical
  let X := diagonalWeakState hq t b p r
  let F : Vec d → BlockVec d := fun x ↦ X x - center
  let S := matSqrt m0
  let R := translateCube w (originCube d s)
  let H := Int.toNat (t - s)
  let G : Vec d → ℝ := fun y ↦ toFullBlockVec (F (matVecMul q y)) alpha
  have hS : S.PosDef := posDef_matSqrt hm0
  obtain ⟨hX₁, hX₂⟩ := diagonalWeakState_memVectorL2 hq t b p r
  have hdom := Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t
  have hcentered₁ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).1) := by
    change MemVectorL2 (adaptedCell q t) (fun x ↦ (X x).1 - center.1)
    exact memVectorL2_sub_const hdom hX₁ center.1
  have hcentered₂ : MemVectorL2 (adaptedCell q t) (fun x ↦ (F x).2) := by
    change MemVectorL2 (adaptedCell q t) (fun x ↦ (X x).2 - center.2)
    exact memVectorL2_sub_const hdom hX₂ center.2
  have hF₁ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S (F x).1) := memVectorL2_matVecMul S hcentered₁
  have hF₂ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S⁻¹ (F x).2) := memVectorL2_matVecMul S⁻¹ hcentered₂
  have hmetric : (fun x ↦
      ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d)) =
      fun x ↦ blockMatVecMul (blockDiag S S⁻¹) (F x) := by
    funext x
    exact (blockDiag_apply S S⁻¹ (F x)).symm
  have hR : R ∈ descendantsAtDepth (originCube d t) H :=
    translateCube_mem_descendantsAtDepth_of_mem_alignedIndex hq hst hw
  have hpartial := ofReal_cubeBesovCircPartialNorm_child_rawPullback_le
    hq hS rfl hR 0 F alpha hF₁ hF₂
  have hweight : 0 < cubeBesovScaleWeight (-(1 / 2 : ℝ)) R := by
    unfold cubeBesovScaleWeight cubeScaleFactor
    positivity
  have hzero :=
    cubeBesovCircPartialNorm_one_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage
      R (1 / 2) 1 G (by norm_num) (by norm_num)
  have havg : |cubeAverage R G| =
      (cubeBesovScaleWeight (-(1 / 2 : ℝ)) R)⁻¹ *
        cubeBesovCircPartialNorm R (1 / 2) 1 1 0 G := by
    rw [hzero]
    rw [← mul_assoc, inv_mul_cancel₀ hweight.ne', one_mul, Real.norm_eq_abs]
  have hchildMean : ENNReal.ofReal |cubeAverage R G| ≤
      ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) R)⁻¹ *
        (ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t) H).card : ℝ)) *
          ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          ENNReal.ofReal (Real.sqrt (max
            (matrixFrobeniusNormSq S⁻¹) (matrixFrobeniusNormSq S))) *
          adaptedWeakSeminorm q t (1 / 2)
            (fun x ↦ blockMatVecMul (blockDiag S S⁻¹) (F x))) := by
    rw [havg, ENNReal.ofReal_mul (inv_nonneg.mpr hweight.le)]
    rw [hmetric] at hpartial
    exact mul_le_mul_right hpartial _
  have hmeanPhysical : toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w) X) alpha -
        toFullBlockVec center alpha = cubeAverage R G := by
    have hsub := blockCellAverage_sub_const (U := adaptedDomainAt hq s w)
      center (Recurrence.volume_adaptedCellAt_pos hq s w).ne'
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).volume_lt_top.ne
      (memVectorL2_mono (adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) hX₁)
      (memVectorL2_mono (adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) hX₂)
    calc
      _ = toFullBlockVec
          (blockCellAverage (adaptedCellAt q s w) X - center) alpha := by
        cases alpha <;> rfl
      _ = toFullBlockVec (blockCellAverage (adaptedCellAt q s w) F) alpha := by
        apply congrArg (fun Z ↦ toFullBlockVec Z alpha)
        simpa only [adaptedDomainAt_carrier, F, X] using hsub.symm
      _ = volumeAverage (adaptedCellAt q s w)
          (fun x ↦ toFullBlockVec (F x) alpha) :=
        Selection.toFullBlockVec_blockCellAverage _ _ _
      _ = cubeAverage R G := by
        simpa only [G] using
          volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq s w
            (fun x ↦ toFullBlockVec (F x) alpha)
  have hoscCentered :=
    ofReal_abs_volumeAverage_adaptedCellAt_cutoffOscillation_le
      hq hS hst hw F alpha hF₁ hF₂
  have hoscEq : volumeAverage (adaptedCellAt q s w) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) * toFullBlockVec (X x) alpha) =
      volumeAverage (adaptedCellAt q s w) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) * toFullBlockVec (F x) alpha) :=
    cutoffOscillation_average_centering hq hst hw X center alpha hcentered₁ hcentered₂
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [hmeanPhysical]
    have hexp : -((1 / 2 : ℝ) * (t : ℝ)) =
        -(1 / 2 : ℝ) * (t : ℝ) := by ring
    rw [hexp] at hchildMean
    dsimp only [X, F, S, R, H] at hchildMean
    convert hchildMean using 1
    all_goals ac_rfl
  · rw [hoscEq]
    rw [hmetric] at hoscCentered
    have hexp : -((1 / 2 : ℝ) * (t : ℝ)) =
        -(1 / 2 : ℝ) * (t : ℝ) := by ring
    rw [hexp] at hoscCentered
    dsimp only [X, F, S, R, H] at hoscCentered
    convert hoscCentered using 1
    all_goals ac_rfl

/-- Every primal child mean and cutoff-oscillation readout required by the
adapted five-term split is integrable under finiteness of the profile weak
quantity. -/
theorem integrable_primal_adaptedFiveTermSplit_readouts [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {q m0 : Mat d}
    (hq : q.PosDef) (hm0 : m0.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)) alpha) P) ∧
    (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ volumeAverage
      (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
          toFullBlockVec (diagonalWeakState hq t (a.subSkew g hg) p r x) alpha)) P) := by
  let center := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
  let root := profilePrimalWeakRoot m0 hq t (fun a ↦ a.subSkew g hg) p r center
  have hroot : eLpNorm root 2 P ≠ ⊤ := weakRoot_ne_top_of_quantity_ne_top (by
    simpa only [root, center, profilePrimalWeakQuantity_eq] using hweak)
  refine ⟨?_, ?_⟩ <;> intro w hw alpha
  · let C := ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ))
        (translateCube w (originCube d s)))⁻¹ *
      ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t)
        (Int.toNat (t - s))).card : ℝ)) *
      ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
      ENNReal.ofReal (Real.sqrt (max (matrixFrobeniusNormSq (matSqrt m0)⁻¹)
        (matrixFrobeniusNormSq (matSqrt m0))))
    have hC : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top
    have hcentered := integrable_of_enorm_le_finite_mul_root
      ((Selection.aestronglyMeasurable_blockCellAverage_diagonalWeakState_subSkew_alignedIndex
        hq hst P g hg p r hw alpha).sub aestronglyMeasurable_const)
      hC hroot (fun a ↦ by
        simpa only [C, root, center, profilePrimalWeakRoot] using!
          (centeredChild_readout_enorm_bounds hq hm0 hst hw
            (a.subSkew g hg) p r center alpha).1)
    exact (hcentered.add (integrable_const _)).congr
      (_root_.Filter.Eventually.of_forall fun _ ↦ by dsimp; ring)
  · let C := ENNReal.ofReal (1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-(t - s)) *
        (cubeBesovCircDepthWeight (translateCube w (originCube d s)) (1 / 2) 1)⁻¹) *
      ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t)
        (Int.toNat (t - s))).card : ℝ)) *
      ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
      ENNReal.ofReal (Real.sqrt (max (matrixFrobeniusNormSq (matSqrt m0)⁻¹)
        (matrixFrobeniusNormSq (matSqrt m0))))
    have hC : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top
    let eta := fun x ↦ adaptedPreYoungCutoff q hq t x -
      volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)
    let : IsFiniteMeasure (volumeMeasureOn (adaptedCell q t)) :=
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isFiniteMeasure_restrict_volume
    exact integrable_of_enorm_le_finite_mul_root
      (Selection.aestronglyMeasurable_volumeAverage_weighted_diagonalWeakState_subSkew_alignedIndex
        hq hst P g hg p r hw alpha
          (Selection.memScalarL2_indicator_cutoffOscillation hq t
            (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet))
      hC hroot (fun a ↦ by
        simpa only [C, root, center, eta, profilePrimalWeakRoot] using
          (centeredChild_readout_enorm_bounds hq hm0 hst hw
            (a.subSkew g hg) p r center alpha).2)

end

end HCPolySupport.HighContrast.Response
