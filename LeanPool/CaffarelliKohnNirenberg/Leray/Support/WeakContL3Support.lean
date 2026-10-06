/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyWeakGradient
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyMollifiedData
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.PressureSplitTensor
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeak
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Dual
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSupSmoothBoundSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Weak continuity of the local velocity

The momentum identity gives a weakly continuous representative of the velocity in
`L^3` through the terminal time, as in `lem:weak-cont-L3` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩

noncomputable section

namespace CKN
/-- The spatial ball on which the momentum identities are tested. -/
@[expose]
def weakContL3SpatialBall : Set Vec3 := vec3Ball (0 : Vec3) 1

private instance weakContL3SpatialBall_isFiniteMeasure :
    IsFiniteMeasure (volume.restrict weakContL3SpatialBall) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top

private instance weakContL3Time_isFiniteMeasure :
    IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 0)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self)
    isCompact_Icc.measure_lt_top

@[expose]
def weakContL3InnerClosedBall : Set Vec3 :=
  closure (vec3Ball (0 : Vec3) (7 / 8 : ℝ))
/-- A smooth cutoff equals one on the smaller ball and is supported in the test ball. -/
theorem weakContL3_cutoff_exists :
    ∃ χ : Vec3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ weakContL3SpatialBall ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ), χ x = 1) := by
  let B : Set Vec3 := weakContL3SpatialBall
  let K : Set Vec3 := weakContL3InnerClosedBall
  have hB : IsOpen B := by
    exact isOpen_vec3Ball _ _
  have hKcompact : IsCompact K := by
    change IsCompact (closure (vec3Ball (0 : Vec3) (7 / 8 : ℝ)))
    exact isCompact_closure_vec3Ball (by norm_num)
  have hKB : K ⊆ B := by
    intro x hx
    change x ∈ closure (vec3Ball (0 : Vec3) (7 / 8 : ℝ)) at hx
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 7 / 8)] at hx
    change vec3EuclideanNorm (x - 0) < 1
    have hnorm : vec3EuclideanNorm (x - 0) ≤ 7 / 8 := by
      simpa using hx
    exact lt_of_le_of_lt hnorm (by norm_num)
  obtain ⟨χ, hχsmooth, hχcompact, hχrange, hχsupport, W, hWopen, hKW,
      hWU, hχone⟩ :=
    CKN.Foundation.Heat.exists_smooth_cutoff_one_near_compact hKcompact hB hKB
  refine ⟨χ, hχsmooth, hχcompact, hχsupport, ?_, ?_⟩
  · intro x
    exact hχrange x
  · intro x hx
    have hxnorm : vec3EuclideanNorm (x - 0) < 3 / 4 := by
      simpa [mem_vec3Ball] using hx
    have hxK : x ∈ K := by
      change x ∈ closure (vec3Ball (0 : Vec3) (7 / 8 : ℝ))
      rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 7 / 8)]
      change vec3EuclideanNorm (x - 0) ≤ 7 / 8
      linarith only [hxnorm]
    exact (hχone x (hKW hxK))
/-- A scalar function with a weakly integrable derivative has a continuous almost-everywhere representative. -/
theorem weakContL3_scalarTrace_exists {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) {f g : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hweak : HasWeakDerivOn (Ioo a b) f g) :
    ∃ ell : ℝ → ℝ, Continuous ell ∧
      ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = ell t := by
  let gFull : ℝ → ℝ := (Ioo a b).indicator g
  have hgFullInt : Integrable gFull volume := by
    exact hg.integrable_indicator measurableSet_Ioo
  have hgFullLoc : LocallyIntegrableOn gFull (Ioo a b) volume := by
    exact hgFullInt.locallyIntegrable.locallyIntegrableOn _
  have hweakFull : HasWeakDerivOn (Ioo a b) f gFull := by
    intro φ hφ
    have hIntEq : (∫ t in Ioo a b, gFull t * φ t) =
        ∫ t in Ioo a b, g t * φ t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp [gFull, ht]
    rw [hIntEq]
    exact hweak φ hφ
  obtain ⟨C, hC⟩ :=
    exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hab ht₀ hf hgFullLoc hweakFull
  let ell : ℝ → ℝ := fun t => C + ∫ s in t₀..t, gFull s
  refine ⟨ell, ?_, ?_⟩
  · exact continuous_const.add (hgFullInt.continuous_primitive t₀)
  · filter_upwards [hC] with t ht
    intro htI
    simpa [ell] using ht htI
/-- The spatially integrated momentum pairing inherits its time weak derivative. -/
theorem weakContL3_productWeakDeriv
    {a b : ℝ} (μx : Measure Vec3) [SFinite μx]
    {F G : Vec3 × ℝ → ℝ}
    (hF : Integrable F (μx.prod (volume.restrict (Ioo a b))))
    (hG : Integrable G (μx.prod (volume.restrict (Ioo a b))))
    (hweak : ∀ η : ℝ → ℝ, IsIntervalTest (Ioo a b) η →
      (∫ z, -(F z * deriv η z.2) - G z * η z.2
        ∂(μx.prod (volume.restrict (Ioo a b)))) = 0) :
    LocallyIntegrableOn (fun t => ∫ x, F (x, t) ∂μx) (Ioo a b) volume ∧
      IntegrableOn (fun t => ∫ x, G (x, t) ∂μx) (Ioo a b) volume ∧
      HasWeakDerivOn (Ioo a b)
      (fun t => ∫ x, F (x, t) ∂μx)
      (fun t => ∫ x, G (x, t) ∂μx) := by
  let μt : Measure ℝ := volume.restrict (Ioo a b)
  let f : ℝ → ℝ := fun t => ∫ x, F (x, t) ∂μx
  let g : ℝ → ℝ := fun t => ∫ x, G (x, t) ∂μx
  have hf : Integrable f μt := hF.integral_prod_right
  have hg : Integrable g μt := hG.integral_prod_right
  have hfOn : IntegrableOn f (Ioo a b) volume := by
    simpa [IntegrableOn, μt] using hf
  have hgOn : IntegrableOn g (Ioo a b) volume := by
    simpa [IntegrableOn, μt] using hg
  have hfLoc : LocallyIntegrableOn f (Ioo a b) volume :=
    hfOn.locallyIntegrableOn
  refine ⟨hfLoc, hgOn, ?_⟩
  intro η hη
  have hηderivCompact : HasCompactSupport (deriv η) := by
    have hηfderiv : HasCompactSupport (fun t => fderiv ℝ η t (1 : ℝ)) :=
      hη.2.1.fderiv_apply (𝕜 := ℝ) (1 : ℝ)
    simpa only [fderiv_apply_one_eq_deriv] using hηfderiv
  have hηderivCont : Continuous (deriv η) :=
    hη.1.continuous_deriv (by norm_num)
  obtain ⟨Cη, hCη⟩ := hηderivCompact.exists_bound_of_continuous hηderivCont
  have hηbound (z : Vec3 × ℝ) : ‖deriv η z.2‖ ≤ Cη := hCη z.2
  have hηmeas : AEStronglyMeasurable (fun z : Vec3 × ℝ => deriv η z.2)
      (μx.prod μt) :=
    (hηderivCont.comp continuous_snd).aestronglyMeasurable
  have hηmeas' : AEStronglyMeasurable (fun z : Vec3 × ℝ => η z.2)
      (μx.prod μt) :=
    (hη.1.continuous.comp continuous_snd).aestronglyMeasurable
  have hFη : Integrable (fun z => F z * deriv η z.2) (μx.prod μt) :=
    hF.mul_bdd hηmeas (Eventually.of_forall hηbound)
  have hGη : Integrable (fun z => G z * η z.2) (μx.prod μt) := by
    have hηcompact : HasCompactSupport η := hη.2.1
    obtain ⟨C, hC⟩ := hηcompact.exists_bound_of_continuous hη.1.continuous
    have hηBound (z : Vec3 × ℝ) : ‖η z.2‖ ≤ C := hC z.2
    have hηmeasG : AEStronglyMeasurable (fun z : Vec3 × ℝ => η z.2)
        (μx.prod μt) := hηmeas'
    exact hG.mul_bdd hηmeasG (Eventually.of_forall hηBound)
  have hFprod :
      (∫ z, F z * deriv η z.2 ∂(μx.prod μt)) =
        ∫ t, f t * deriv η t ∂μt := by
    rw [integral_prod_symm _ hFη]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [f]
    rw [integral_mul_const]
  have hGprod :
      (∫ z, G z * η z.2 ∂(μx.prod μt)) =
        ∫ t, g t * η t ∂μt := by
    rw [integral_prod_symm _ hGη]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [g]
    rw [integral_mul_const]
  have hsplit :
      (∫ z, -(F z * deriv η z.2) - G z * η z.2
        ∂(μx.prod μt)) =
        -(∫ z, F z * deriv η z.2 ∂(μx.prod μt))
          - ∫ z, G z * η z.2 ∂(μx.prod μt) := by
    have hFneg : Integrable (fun z => -(F z * deriv η z.2))
        (μx.prod μt) := hFη.neg
    have hsplit' := integral_sub hFneg hGη
    simpa only [integral_neg] using hsplit'
  have hzero := hweak η hη
  rw [hsplit] at hzero
  have htimeZero :
      (∫ t, f t * deriv η t ∂μt) + ∫ t, g t * η t ∂μt = 0 := by
    rw [← hFprod, ← hGprod]
    linarith only [hzero]
  change (∫ t in Ioo a b, f t * deriv η t ∂volume) =
    -(∫ t in Ioo a b, g t * η t ∂volume)
  simpa [f, g, μt] using (eq_neg_iff_add_eq_zero.mpr htimeZero)
/-- The space of smooth compactly supported spatial L²-valued tests. -/
@[expose]
def weakContL3SmoothTest : Submodule ℝ (Vec3 → L2Vec3) where
  carrier := {φ | HasCompactSupport φ ∧ ContDiff ℝ (⊤ : ℕ∞) φ}
  zero_mem' := ⟨HasCompactSupport.zero, contDiff_const⟩
  add_mem' := by
    intro φ ψ hφ hψ
    exact ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  smul_mem' := by
    intro c φ hφ
    exact ⟨HasCompactSupport.smul_left hφ.1, hφ.2.const_smul c⟩

@[expose]
def weakContL3SmoothLpSet (μ : Measure Vec3) :
    Set (Lp L2Vec3 2 μ) :=
  {v | ∃ g : Vec3 → L2Vec3, v =ᵐ[μ] g ∧ HasCompactSupport g ∧
    ContDiff ℝ (⊤ : ℕ∞) g}

private instance weakContL3SmoothLpSet_nonempty (μ : Measure Vec3) :
    Nonempty (weakContL3SmoothLpSet μ) := by
  refine ⟨⟨0, ?_⟩⟩
  exact ⟨(0 : Vec3 → L2Vec3),
    (show (⇑(0 : Lp L2Vec3 2 μ) =ᵐ[μ]
      (0 : Vec3 → L2Vec3)) from Lp.coeFn_zero L2Vec3 2 μ),
    HasCompactSupport.zero, contDiff_const⟩

private instance weakContL3SmoothLpSet_secondCountable (μ : Measure Vec3)
    [IsSeparable μ] :
    SecondCountableTopology (weakContL3SmoothLpSet μ) := by
  let : TopologicalSpace.SeparableSpace L2Vec3 :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  infer_instance

private instance weakContL3SmoothLpSet_separable (μ : Measure Vec3)
    [IsSeparable μ] :
    TopologicalSpace.SeparableSpace (weakContL3SmoothLpSet μ) :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

private theorem weakContL3_smoothLpSet_dense
    (μ : Measure Vec3) [IsFiniteMeasureOnCompacts μ] [IsSeparable μ] :
    Dense (weakContL3SmoothLpSet μ) := by
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  simpa [weakContL3SmoothLpSet] using
    Lp.dense_hasCompactSupport_contDiff
      (μ := μ) (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top

/-- Smooth compactly supported spatial tests define elements of spatial `L²`. -/
theorem weakContL3_smoothTest_memLp
    {μ : Measure Vec3} [IsFiniteMeasureOnCompacts μ]
    (φ : weakContL3SmoothTest) : MemLp (φ : Vec3 → L2Vec3) 2 μ :=
  φ.property.2.continuous.memLp_of_hasCompactSupport φ.property.1
/-- A countable family of smooth compactly supported tests is dense in spatial L². -/
theorem weakContL3_exists_countable_dense_tests
    (μ : Measure Vec3) [IsFiniteMeasureOnCompacts μ] :
    ∃ ψ : ℕ → Vec3 → L2Vec3,
      (∀ n, HasCompactSupport (ψ n) ∧ ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧
      ∃ hψ : ∀ n, MemLp (ψ n) 2 μ,
        DenseRange (fun n => (hψ n).toLp) := by
  classical
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let σ : ℕ → weakContL3SmoothLpSet μ :=
    TopologicalSpace.denseSeq (weakContL3SmoothLpSet μ)
  let ψ : ℕ → Vec3 → L2Vec3 := fun n => Classical.choose (σ n).property
  have hprop (n : ℕ) : (σ n).val =ᵐ[μ] ψ n ∧
      HasCompactSupport (ψ n) ∧ ContDiff ℝ (⊤ : ℕ∞) (ψ n) :=
    Classical.choose_spec (σ n).property
  have hreg : ∀ n, HasCompactSupport (ψ n) ∧
      ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n => (hprop n).2
  let hψ : ∀ n, MemLp (ψ n) 2 μ := fun n =>
    (hreg n).2.continuous.memLp_of_hasCompactSupport (hreg n).1
  have hclass (n : ℕ) : (hψ n).toLp = (σ n).val := by
    apply Lp.ext
    filter_upwards [(hψ n).coeFn_toLp, (hprop n).1] with x h₁ h₂
    exact h₁.trans h₂.symm
  have hseq : DenseRange σ := TopologicalSpace.denseRange_denseSeq _
  have hdense : Dense (weakContL3SmoothLpSet μ) :=
    weakContL3_smoothLpSet_dense μ
  refine ⟨ψ, hreg, hψ, ?_⟩
  change Dense (Set.range fun n => (hψ n).toLp)
  have hsubset : weakContL3SmoothLpSet μ ⊆
      closure (Set.range fun n => (hψ n).toLp) := by
    intro x hx
    have hxSubtype : (⟨x, hx⟩ : weakContL3SmoothLpSet μ) ∈
        closure (Set.range σ) := by
      change Dense (Set.range σ) at hseq
      rw [dense_iff_closure_eq] at hseq
      simp [hseq]
    have hxVals := closure_subtype.1 hxSubtype
    have hset : (fun y : weakContL3SmoothLpSet μ => y.val) ''
        Set.range σ = Set.range (fun n => (σ n).val) := by
      ext y
      constructor
      · rintro ⟨a, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨σ n, ⟨n, rfl⟩, rfl⟩
    rw [hset] at hxVals
    have heqRange : Set.range (fun n => (σ n).val) =
        Set.range (fun n => (hψ n).toLp) := by
      ext y
      simp only [Set.mem_range]
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, hclass n⟩
      · rintro ⟨n, rfl⟩
        exact ⟨n, (hclass n).symm⟩
    rw [heqRange] at hxVals
    exact hxVals
  rw [dense_iff_closure_eq]
  have hdense' : closure (weakContL3SmoothLpSet μ) = Set.univ :=
    hdense.closure_eq
  rw [← hdense']
  have hrange : Set.range (fun n => (hψ n).toLp) ⊆
      weakContL3SmoothLpSet μ := by
    rintro y ⟨n, rfl⟩
    exact ⟨ψ n, (hψ n).coeFn_toLp, (hreg n).1, (hreg n).2⟩
  exact le_antisymm
    (closure_minimal (hrange.trans subset_closure) isClosed_closure)
    (closure_minimal hsubset isClosed_closure)

private theorem weakContL3_separatedTest_mem
    {ψ : Vec3 → Vec3} {η : ℝ → ℝ}
    (hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ)
    (hψsupport : tsupport ψ ⊆ weakContL3SpatialBall)
    (hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ Ioo (-1 : ℝ) 0) :
    (fun z : Vec3 × ℝ => η z.2 • ψ z.1) ∈
      spaceTimeTestFunction (V := Vec3) weakContL3SpatialBall (Ioo (-1 : ℝ) 0) := by
  let Φ : Vec3 × ℝ → Vec3 := fun z => η z.2 • ψ z.1
  have htsSupport : Function.support Φ ⊆ tsupport ψ ×ˢ tsupport η := by
    intro z hz
    have hΦ : η z.2 • ψ z.1 ≠ 0 := by
      simpa [Φ] using Function.mem_support.mp hz
    have hη : η z.2 ≠ 0 := by
      intro hzero
      apply hΦ
      simp [hzero]
    have hψ : ψ z.1 ≠ 0 := by
      intro hzero
      apply hΦ
      simp [hzero]
    exact ⟨subset_tsupport ψ (Function.mem_support.mpr hψ),
      subset_tsupport η (Function.mem_support.mpr hη)⟩
  have hts : tsupport Φ ⊆ tsupport ψ ×ˢ tsupport η :=
    closure_minimal htsSupport ((isClosed_tsupport ψ).prod (isClosed_tsupport η))
  have hΦcompact : HasCompactSupport Φ := by
    apply HasCompactSupport.of_support_subset_isCompact
      (hψcompact.isCompact.prod hηcompact.isCompact)
    exact htsSupport
  refine ⟨?_, hΦcompact, ?_⟩
  · exact (hηsmooth.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff).smul
      (hψsmooth.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff)
  · change tsupport Φ ⊆ weakContL3SpatialBall ×ˢ Ioo (-1 : ℝ) 0
    exact hts.trans (Set.prod_mono hψsupport hηsupport)

/-- Convert the `L²` normed encoding of Vec3 to its coordinate representation. -/
@[expose]
noncomputable def weakContL3OfLp : L2Vec3 →L[ℝ] Vec3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap

/-- The canonical continuous linear map from velocity vectors to `L²` vectors. -/
@[expose]
noncomputable def weakContL3VecToLp : Vec3 →L[ℝ] L2Vec3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

/-- Multiply a smooth spatial test by the fixed scalar cutoff. -/
@[expose]
def weakContL3CutoffTest (χ : Vec3 → ℝ)
    (φ : weakContL3SmoothTest) : Vec3 → Vec3 :=
  fun x => χ x • weakContL3OfLp (φ.val x)

private theorem weakContL3_cutoffTest_smooth
    {χ : Vec3 → ℝ} (hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : weakContL3SmoothTest) :
    ContDiff ℝ (⊤ : ℕ∞) (weakContL3CutoffTest χ φ) := by
  let ψ : Vec3 → Vec3 := fun x =>
    weakContL3OfLp (φ.val x)
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    exact weakContL3OfLp.contDiff.comp φ.property.2
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • ψ x)
  exact hχsmooth.smul hψsmooth

private theorem weakContL3_cutoffTest_compact
    {χ : Vec3 → ℝ} (hχcompact : HasCompactSupport χ)
    (φ : weakContL3SmoothTest) :
    HasCompactSupport (weakContL3CutoffTest χ φ) := by
  let ψ : Vec3 → Vec3 := fun x => weakContL3OfLp (φ.val x)
  change HasCompactSupport (fun x => χ x • ψ x)
  change IsCompact (tsupport (fun x => χ x • ψ x))
  exact hχcompact.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset_left χ ψ)

private theorem weakContL3_cutoffTest_tsupport
    {χ : Vec3 → ℝ} (hχsupport : tsupport χ ⊆ weakContL3SpatialBall)
    (φ : weakContL3SmoothTest) :
    tsupport (weakContL3CutoffTest χ φ) ⊆ weakContL3SpatialBall := by
  let ψ : Vec3 → Vec3 := fun x => weakContL3OfLp (φ.val x)
  have hresultSupport : tsupport (fun x => χ x • ψ x) ⊆ weakContL3SpatialBall := by
    exact (tsupport_smul_subset_left χ ψ).trans hχsupport
  change tsupport (fun x => χ x • ψ x) ⊆ weakContL3SpatialBall
  exact hresultSupport
/-- The spatial velocity pairing used in the momentum identity. -/
@[expose]
def weakContL3MomentumPairing
    (u : ParabolicPoint → Vec3) (χ : Vec3 → ℝ)
    (φ : weakContL3SmoothTest) (z : Vec3 × ℝ) : ℝ :=
  ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
    weakContL3CutoffTest χ φ z.1 i
/-- The spatial momentum flux paired with a compactly supported test. -/
@[expose]
def weakContL3MomentumFlux
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (χ : Vec3 → ℝ)
    (φ : weakContL3SmoothTest) (z : Vec3 × ℝ) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3,
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
        spatialDeriv (fun x => weakContL3CutoffTest χ φ x i) j z.1)
    - (∑ i : Fin 3, ∑ j : Fin 3,
        Du (parabolicHomeomorph.symm z) i j *
          spatialDeriv (fun x => weakContL3CutoffTest χ φ x i) j z.1)
    + p (parabolicHomeomorph.symm z) * ∑ i : Fin 3,
        spatialDeriv (fun x => weakContL3CutoffTest χ φ x i) i z.1
/-- The velocity pairing and momentum flux are integrable for smooth spatial tests. -/
theorem weakContL3_momentumTerms_integrable
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    {μx : Measure Vec3} [IsFiniteMeasure μx]
    {μt : Measure ℝ} [IsFiniteMeasure μt]
    (hU4 : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 4
      (μx.prod μt))
    (hDu2 : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2
      (μx.prod μt))
    (hp : MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (μx.prod μt))
    {χ : Vec3 → ℝ} (hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (φ : weakContL3SmoothTest) :
    Integrable (weakContL3MomentumPairing u χ φ) (μx.prod μt) ∧
      Integrable (weakContL3MomentumFlux u Du p χ φ) (μx.prod μt) := by
  let ψ : Vec3 → Vec3 := weakContL3CutoffTest χ φ
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    weakContL3_cutoffTest_smooth hχsmooth φ
  have hψcompact : HasCompactSupport ψ :=
    weakContL3_cutoffTest_compact hχcompact φ
  have hψcont : Continuous ψ := hψsmooth.continuous
  have hψbound : ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C :=
    hψcompact.exists_bound_of_continuous hψcont
  obtain ⟨Cψ, hCψ⟩ := hψbound
  have hψi_cont (i : Fin 3) : Continuous (fun x : Vec3 => ψ x i) :=
    (continuous_apply i).comp hψcont
  have hψi_meas (i : Fin 3) : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => ψ z.1 i) (μx.prod μt) :=
    (hψi_cont i).comp continuous_fst |>.aestronglyMeasurable
  have hψi_bound (i : Fin 3) (z : Vec3 × ℝ) :
      ‖ψ z.1 i‖ ≤ Cψ := by
    exact (norm_le_pi_norm (ψ z.1) i).trans (hCψ z.1)
  have hUi4 (i : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i) 4
      (μx.prod μt) := (memLp_pi_iff.mp hU4) i
  have hUij2 (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
        u (parabolicHomeomorph.symm z) j) 2 (μx.prod μt) := by
    have hholder : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
      have h : (4 : ℝ).HolderTriple 4 2 := by
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      simpa using h.ennrealOfReal
    exact (hUi4 i).mul (hUi4 j) (hpqr := hholder)
  have hDuij2 (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z) i j) 2
      (μx.prod μt) := (memLp_pi_iff.mp (memLp_pi_iff.mp hDu2 i)) j
  have hpint : Integrable (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (μx.prod μt) := hp.integrable (by norm_num)
  have hFterm (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i * ψ z.1 i)
      (μx.prod μt) := by
    exact (hUi4 i).integrable (by norm_num) |>.mul_bdd
      (hψi_meas i) (Eventually.of_forall (fun z => hψi_bound i z))
  have hF : Integrable (weakContL3MomentumPairing u χ φ) (μx.prod μt) := by
    change Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
        weakContL3CutoffTest χ φ z.1 i) (μx.prod μt)
    exact integrable_finsetSum Finset.univ (fun i _ => hFterm i)
  have hderiv (i j : Fin 3) : Continuous
      (fun x : Vec3 => spatialDeriv (fun y => ψ y i) j x) := by
    have hcomponent : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => ψ y i) :=
      (contDiff_apply ℝ ℝ i).comp hψsmooth
    exact (CKN.contDiff_spatialDeriv_smooth hcomponent j).continuous
  have hderiv_bound (i j : Fin 3) : ∃ C : ℝ, ∀ x : Vec3,
      ‖spatialDeriv (fun y => ψ y i) j x‖ ≤ C := by
    have hcomponentSupport : tsupport (fun y : Vec3 => ψ y i) ⊆ tsupport ψ := by
      apply closure_minimal
      · intro x hx
        by_contra hnot
        apply hx
        have hzero : ψ x = 0 := image_eq_zero_of_notMem_tsupport hnot
        simp [hzero]
      · exact isClosed_tsupport ψ
    have hcomponentCompact : HasCompactSupport (fun y : Vec3 => ψ y i) :=
      HasCompactSupport.of_support_subset_isCompact hψcompact.isCompact
        ((subset_tsupport _).trans hcomponentSupport)
    have hderivCompact : HasCompactSupport
        (fun x : Vec3 => spatialDeriv (fun y => ψ y i) j x) :=
      CKN.hasCompactSupport_spatialDeriv hcomponentCompact j
    exact hderivCompact.exists_bound_of_continuous (hderiv i j)
  have hGconv (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
        u (parabolicHomeomorph.symm z) j *
          spatialDeriv (fun y => ψ y i) j z.1) (μx.prod μt) := by
    obtain ⟨C, hC⟩ := hderiv_bound i j
    exact (hUij2 i j).integrable (by norm_num) |>.mul_bdd
      ((hderiv i j).comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hGgrad (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z) i j *
        spatialDeriv (fun y => ψ y i) j z.1) (μx.prod μt) := by
    obtain ⟨C, hC⟩ := hderiv_bound i j
    exact (hDuij2 i j).integrable (by norm_num) |>.mul_bdd
      ((hderiv i j).comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hGpressure (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z) *
        spatialDeriv (fun y => ψ y i) i z.1) (μx.prod μt) := by
    obtain ⟨C, hC⟩ := hderiv_bound i i
    exact hpint.mul_bdd
      ((hderiv i i).comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hG : Integrable (weakContL3MomentumFlux u Du p χ φ) (μx.prod μt) := by
    change Integrable
      ((fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j z.1) -
        (fun z : Vec3 × ℝ =>
          ∑ i : Fin 3, ∑ j : Fin 3,
            Du (parabolicHomeomorph.symm z) i j *
              spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j z.1) +
        (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z) *
          ∑ i : Fin 3,
            spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i z.1))
      (μx.prod μt)
    have hconv : Integrable (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j z.1)
        (μx.prod μt) := integrable_finsetSum Finset.univ fun i _ =>
          integrable_finsetSum Finset.univ fun j _ => hGconv i j
    have hgrad : Integrable (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j *
            spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j z.1)
        (μx.prod μt) := integrable_finsetSum Finset.univ fun i _ =>
          integrable_finsetSum Finset.univ fun j _ => hGgrad i j
    have hpressureTerm (i : Fin 3) : Integrable
        (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z) *
          spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i z.1)
        (μx.prod μt) := hGpressure i
    have hpressureSum : Integrable (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, p (parabolicHomeomorph.symm z) *
          spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i z.1)
        (μx.prod μt) :=
      integrable_finsetSum Finset.univ (fun i _ => hpressureTerm i)
    have hpressure : Integrable (fun z : Vec3 × ℝ =>
        p (parabolicHomeomorph.symm z) *
          ∑ i : Fin 3,
            spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i z.1)
        (μx.prod μt) := hpressureSum.congr (Eventually.of_forall fun z => by
          simp only [Finset.mul_sum])
    exact (hconv.sub hgrad).add hpressure
  exact ⟨hF, hG⟩
/-- The momentum identity gives a one-dimensional weak derivative for each spatial test. -/
theorem weakContL3_momentum_gives_productWeak
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hS3 : ∀ Φ : ParabolicPoint → Vec3,
      Φ ∈ spaceTimeTestFunction (V := Vec3)
        weakContL3SpatialBall (Ioo (-1 : ℝ) 0) →
      ∫ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => Φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => Φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z)
          ∂volume = 0)
    {χ : Vec3 → ℝ} (hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ weakContL3SpatialBall)
    (φ : weakContL3SmoothTest) :
    ∀ η : ℝ → ℝ, IsIntervalTest (Ioo (-1 : ℝ) 0) η →
      (∫ z,
        -(weakContL3MomentumPairing u χ φ z * deriv η z.2)
          - weakContL3MomentumFlux u Du p χ φ z * η z.2
        ∂((volume.restrict weakContL3SpatialBall).prod
          (volume.restrict (Ioo (-1 : ℝ) 0)))) = 0 := by
  intro η hη
  have hψsmooth := weakContL3_cutoffTest_smooth hχsmooth φ
  have hψcompact := weakContL3_cutoffTest_compact hχcompact φ
  have hψsupport := weakContL3_cutoffTest_tsupport hχsupport φ
  have htest : (fun z : Vec3 × ℝ =>
      η z.2 • weakContL3CutoffTest χ φ z.1) ∈
      spaceTimeTestFunction (V := Vec3)
        weakContL3SpatialBall (Ioo (-1 : ℝ) 0) :=
    weakContL3_separatedTest_mem hψsmooth hψcompact hψsupport
      hη.1 hη.2.1 hη.2.2
  let Φ : ParabolicPoint → Vec3 := fun z => η z.2 • weakContL3CutoffTest χ φ z.1
  have htest' : Φ ∈ spaceTimeTestFunction (V := Vec3)
      weakContL3SpatialBall (Ioo (-1 : ℝ) 0) := htest
  have hS3test := hS3 Φ htest'
  have hmeasure :
      (volume.restrict weakContL3SpatialBall).prod
        (volume.restrict (Ioo (-1 : ℝ) 0)) =
        (volume : Measure (Vec3 × ℝ)).restrict
          (weakContL3SpatialBall ×ˢ Ioo (-1 : ℝ) 0) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  rw [setIntegral_parabolic_to_product] at hS3test
  rw [← hmeasure] at hS3test
  have hproduct (i : Fin 3) :
      (fun y : ParabolicPoint => Φ y i) =
        (fun y : ParabolicPoint =>
          weakContL3CutoffTest χ φ y.1 i * η y.2) := by
    funext y
    simp [Φ, Pi.smul_apply]
    ring
  have hψcomponent (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => weakContL3CutoffTest χ φ x i) :=
    (contDiff_apply ℝ ℝ i).comp hψsmooth
  have htime (i : Fin 3) (z : ParabolicPoint) :
      timePartial (fun y : ParabolicPoint => Φ y i) z =
        weakContL3CutoffTest χ φ z.1 i * deriv η z.2 := by
    rw [hproduct i]
    have h := CKN.Core.Endgame.timePartial_separatedProduct
      (fun x => weakContL3CutoffTest χ φ x i) hη.1 (parabolicHomeomorph z)
    convert h using 1 <;> rfl
  have hspace (i j : Fin 3) (z : ParabolicPoint) :
      spatialPartial (fun y : ParabolicPoint => Φ y i) j z =
        spatialDeriv (fun x => weakContL3CutoffTest χ φ x i) j z.1 * η z.2 := by
    rw [hproduct i]
    have h := CKN.Core.Endgame.spatialPartial_separatedProduct η
      (hψcomponent i) j (parabolicHomeomorph z)
    convert h using 1 <;> rfl
  have htestFormula (z : ParabolicPoint) :
      (-(∑ i : Fin 3, u z i *
            timePartial (fun y : ParabolicPoint => Φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j *
              spatialPartial (fun y : ParabolicPoint => Φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j *
              spatialPartial (fun y : ParabolicPoint => Φ y i) j z
      - p z *
            ∑ i : Fin 3,
              spatialPartial (fun y : ParabolicPoint => Φ y i) i z)
      =
        -(weakContL3MomentumPairing u χ φ (z.1, z.2) * deriv η z.2)
          - weakContL3MomentumFlux u Du p χ φ (z.1, z.2) * η z.2 := by
    simp only [htime, hspace]
    cases z with
    | mk x t =>
      simp only [weakContL3MomentumPairing, weakContL3MomentumFlux,
        parabolicHomeomorph_symm_apply]
      ring_nf
      have hconvAlg :
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (x, t) i * u (x, t) j *
              spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j x * η t) =
          (η t * (∑ i : Fin 3, ∑ j : Fin 3,
            u (x, t) i * u (x, t) j *
              spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j x)) := by
        calc
          (∑ i : Fin 3, ∑ j : Fin 3,
              u (x, t) i * u (x, t) j *
                spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j x * η t) =
              (∑ i : Fin 3, ∑ j : Fin 3,
                η t * u (x, t) i * u (x, t) j *
                  spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j x) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = η t * (∑ i : Fin 3, ∑ j : Fin 3,
                u (x, t) i * u (x, t) j *
                  spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j x) := by
            symm
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      have hgradAlg :
          η t * (∑ i : Fin 3, ∑ j : Fin 3,
            Du (x, t) i j *
              spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j x) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            η t * Du (x, t) i j *
              spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) j x := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      have hpressureAlg :
          p (x, t) * (∑ i : Fin 3,
            η t * spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i x) =
          η t * p (x, t) * (∑ i : Fin 3,
            spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i x) := by
        calc
          p (x, t) * (∑ i : Fin 3,
              η t * spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i x) =
              ∑ i : Fin 3, p (x, t) *
                (η t * spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i x) := by
            rw [Finset.mul_sum]
          _ = ∑ i : Fin 3, (η t * p (x, t)) *
                spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i x := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = η t * p (x, t) * (∑ i : Fin 3,
                spatialDeriv (fun y => weakContL3CutoffTest χ φ y i) i x) := by
            rw [Finset.mul_sum]
      have htimeAlg :
          deriv η t * (∑ i : Fin 3,
            u (x, t) i * weakContL3CutoffTest χ φ x i) =
          ∑ i : Fin 3,
            deriv η t * u (x, t) i * weakContL3CutoffTest χ φ x i := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hconvAlg, hgradAlg, hpressureAlg, htimeAlg]
      ring_nf
  have hrewrite :
      (∫ z,
        (-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
              timePartial (fun y : ParabolicPoint => Φ y i) (parabolicHomeomorph.symm z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
                spatialPartial (fun y : ParabolicPoint => Φ y i) j (parabolicHomeomorph.symm z)
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du (parabolicHomeomorph.symm z) i j *
                spatialPartial (fun y : ParabolicPoint => Φ y i) j (parabolicHomeomorph.symm z)
          - p (parabolicHomeomorph.symm z) *
              ∑ i : Fin 3,
                spatialPartial (fun y => Φ y i) i (parabolicHomeomorph.symm z))
        ∂((volume.restrict weakContL3SpatialBall).prod
          (volume.restrict (Ioo (-1 : ℝ) 0)))) =
        (∫ z,
          -(weakContL3MomentumPairing u χ φ z * deriv η z.2)
            - weakContL3MomentumFlux u Du p χ φ z * η z.2
          ∂((volume.restrict weakContL3SpatialBall).prod
            (volume.restrict (Ioo (-1 : ℝ) 0)))) := by
    apply integral_congr_ae
    filter_upwards [] with z
    cases z with
    | mk x t =>
      simpa only [parabolicHomeomorph.apply_symm_apply,
        parabolicHomeomorph_symm_apply, Prod.mk.eta] using
        htestFormula (parabolicHomeomorph.symm (x, t))
  rw [hrewrite] at hS3test
  exact hS3test
end CKN
