/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.L2CompactnessTools
public import LeanPool.CutoffRigidity.TransportMoments
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual zero extension from a finite-measure compact domain into L²

This bounded extension transfers the proved Arzelà--Ascoli compactness to
families of functions with a common compact support in a noncompact space.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set Function
open scoped BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {K : Set X}

/-- Extend a bounded continuous function on `K` by zero outside `K`. -/
@[expose] noncomputable def compactZeroExtend (f : K →ᵇ ℝ) : X → ℝ :=
  Function.extend (Subtype.val : K → X) f 0

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactZeroExtend_apply (f : K →ᵇ ℝ) (x : K) :
    compactZeroExtend f (x : X) = f x :=
  Subtype.val_injective.extend_apply f 0 x

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactZeroExtend_of_notMem (f : K →ᵇ ℝ) {x : X} (hx : x ∉ K) :
    compactZeroExtend f x = 0 :=
  Function.extend_apply' (f := (Subtype.val : K → X)) f (0 : X → ℝ) x
    (by rintro ⟨y, rfl⟩; exact hx y.property)

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactZeroExtend_apply_of_mem (f : K →ᵇ ℝ) {x : X} (hx : x ∈ K) :
    compactZeroExtend f x = f ⟨x, hx⟩ := compactZeroExtend_apply f ⟨x, hx⟩

theorem compactZeroExtend_stronglyMeasurable (hK : MeasurableSet K) (f : K →ᵇ ℝ) :
    StronglyMeasurable (compactZeroExtend f) :=
  (MeasurableEmbedding.subtype_coe hK).stronglyMeasurable_extend
    f.continuous.measurable.stronglyMeasurable stronglyMeasurable_const

theorem compactZeroExtend_memLp (hK : MeasurableSet K) (hfin : μ K ≠ ⊤) (f : K →ᵇ ℝ) :
    MemLp (compactZeroExtend f) 2 μ := by
  have hI := memLp_indicator_const (μ := μ) 2 hK.nullMeasurableSet ‖f‖ (Or.inr hfin)
  apply hI.mono' (compactZeroExtend_stronglyMeasurable hK f).aestronglyMeasurable
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
    have hf := f.norm_coe_le_norm ⟨x, hx⟩
    simpa only [compactZeroExtend_apply_of_mem f hx] using hf
  · rw [indicator_of_notMem hx, compactZeroExtend_of_notMem f hx, norm_zero]

/-- The ambient `L²` class of the zero extension from the measurable, finite-measure set `K`. -/
@[expose] noncomputable def compactZeroExtendLp (hK : MeasurableSet K) (hfin : μ K ≠ ⊤)
    (f : K →ᵇ ℝ) : X →₂[μ] ℝ :=
  (compactZeroExtend_memLp μ hK hfin f).toLp (compactZeroExtend f)

theorem compactZeroExtend_norm_sq_le (hK : MeasurableSet K) (hfin : μ K ≠ ⊤)
    (f : K →ᵇ ℝ) : ‖compactZeroExtendLp μ hK hfin f‖ ^ 2 ≤ μ.real K * ‖f‖ ^ 2 := by
  change ‖(compactZeroExtend_memLp μ hK hfin f).toLp (compactZeroExtend f)‖ ^ 2 ≤ _
  rw [norm_toLp_sq]
  have heq : (∫ x, compactZeroExtend f x ^ 2 ∂μ) = ∫ x in K, compactZeroExtend f x ^ 2 ∂μ := by
    rw [← integral_indicator hK]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, compactZeroExtend_of_notMem f hx]
      norm_num
  rw [heq]
  have hfint : IntegrableOn (fun x => compactZeroExtend f x ^ 2) K μ :=
    (compactZeroExtend_memLp μ hK hfin f).integrable_sq.integrableOn
  have hconst : IntegrableOn (fun _ : X => ‖f‖ ^ 2) K μ := by
    have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hfin.lt_top⟩
    exact integrable_const _
  calc
    _ ≤ ∫ _ : X in K, ‖f‖ ^ 2 ∂μ := by
      apply setIntegral_mono_on hfint hconst hK
      intro x hx
      have hn : ‖compactZeroExtend f x‖ ≤ ‖f‖ := by
        simpa only [compactZeroExtend_apply_of_mem f hx] using f.norm_coe_le_norm ⟨x, hx⟩
      simpa only [← pow_two, Real.norm_eq_abs, sq_abs] using mul_self_le_mul_self (norm_nonneg _) hn
    _ = _ := by simp [Measure.real, mul_comm]

theorem compactZeroExtendLp_sub (hK : MeasurableSet K) (hfin : μ K ≠ ⊤)
    (f g : K →ᵇ ℝ) :
    compactZeroExtendLp μ hK hfin (f - g) =
      compactZeroExtendLp μ hK hfin f - compactZeroExtendLp μ hK hfin g := by
  apply Lp.ext
  filter_upwards [(compactZeroExtend_memLp μ hK hfin (f - g)).coeFn_toLp,
    Lp.coeFn_sub (compactZeroExtendLp μ hK hfin f) (compactZeroExtendLp μ hK hfin g),
    (compactZeroExtend_memLp μ hK hfin f).coeFn_toLp,
    (compactZeroExtend_memLp μ hK hfin g).coeFn_toLp] with x hx hsub hf hg
  change (compactZeroExtend_memLp μ hK hfin (f - g)).toLp _ x = _
  rw [hx, hsub]
  change compactZeroExtend (f - g) x =
    (compactZeroExtend_memLp μ hK hfin f).toLp (compactZeroExtend f) x -
    (compactZeroExtend_memLp μ hK hfin g).toLp (compactZeroExtend g) x
  rw [hf, hg]
  by_cases h : x ∈ K
  · simpa only [compactZeroExtend_apply_of_mem _ h] using (show (f - g) ⟨x, h⟩ = f ⟨x, h⟩ - g ⟨x,
    h⟩ from rfl)
  · simp only [compactZeroExtend_of_notMem _ h, sub_zero]

theorem compactZeroExtendLp_lipschitz (hK : MeasurableSet K) (hfin : μ K ≠ ⊤) :
    LipschitzWith (Real.toNNReal (Real.sqrt (μ.real K))) (compactZeroExtendLp μ hK hfin) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm, ← compactZeroExtendLp_sub, dist_eq_norm]
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have hs := compactZeroExtend_norm_sq_le μ hK hfin (f - g)
  have hsqrt := Real.sq_sqrt (show 0 ≤ μ.real K from ENNReal.toReal_nonneg)
  have hn := norm_nonneg (compactZeroExtendLp μ hK hfin (f - g))
  have hm := mul_nonneg (Real.sqrt_nonneg (μ.real K)) (norm_nonneg (f - g))
  nlinarith [sq_nonneg (Real.sqrt (μ.real K) * ‖f - g‖ - ‖compactZeroExtendLp μ hK hfin (f - g)‖)]

/-- Actual global L² compactness of zero-extended bounded Lipschitz
families on one compact support set. -/
theorem isCompact_closure_zeroExtendLp (hK : IsCompact K) (hfin : μ K ≠ ⊤)
    (A : Set (K →ᵇ ℝ)) (B : ℝ) (L : NNReal)
    (hbound : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hLip : ∀ f ∈ A, LipschitzWith L f) :
    IsCompact (closure ((compactZeroExtendLp μ hK.isClosed.measurableSet hfin) '' A)) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc := (isCompact_closure_of_uniform_bound_lipschitz A B L hbound hLip).image
    (compactZeroExtendLp_lipschitz μ hK.isClosed.measurableSet hfin).continuous
  exact hc.closure_of_subset (image_mono subset_closure)

/-- Restriction to the compact domain as a genuine bounded continuous function. -/
@[expose] noncomputable def restrictCompactFunction (hK : IsCompact K)
    (f : X → ℝ) (hf : Continuous f) : K →ᵇ ℝ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact BoundedContinuousFunction.mkOfCompact ⟨fun x => f x, hf.comp continuous_subtype_val⟩

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactZeroExtend_restrict_eq (hK : IsCompact K) (f : X → ℝ) (hf : Continuous f)
    (hsupp : ∀ x ∉ K, f x = 0) : compactZeroExtend (restrictCompactFunction hK f hf) = f := by
  funext x
  by_cases hx : x ∈ K
  · rw [compactZeroExtend_apply_of_mem _ hx]
    rfl
  · rw [compactZeroExtend_of_notMem _ hx, hsupp x hx]

/-- Actual L² membership follows from continuity, boundedness on the
compact support and its finite measure. -/
theorem continuous_commonSupport_memLp (hK : IsCompact K) (hfin : μ K ≠ ⊤)
    (f : X → ℝ) (hf : Continuous f) (hsupp : ∀ x ∉ K, f x = 0) : MemLp f 2 μ := by
  rw [← compactZeroExtend_restrict_eq hK f hf hsupp]
  exact compactZeroExtend_memLp μ hK.isClosed.measurableSet hfin _

/-- A uniformly bounded, uniformly Lipschitz family with one actual compact
support has compact closure in genuine ambient L², even when the ambient
measure is infinite. This is the local smoothing compactness step. -/
theorem isCompact_closure_commonSupport_L2_family {ι : Type*}
    (hK : IsCompact K) (hfin : μ K ≠ ⊤) (F : ι → X → ℝ)
    (hF : ∀ i, Continuous (F i)) (hsupp : ∀ i x, x ∉ K → F i x = 0)
    (B : ℝ) (L : NNReal) (hbound : ∀ i x, |F i x| ≤ B)
    (hLip : ∀ i, LipschitzWith L (F i)) :
    IsCompact (closure (Set.range (fun i =>
      (continuous_commonSupport_memLp μ hK hfin (F i) (hF i) (hsupp i)).toLp (F i)))) := by
  let A := Set.range (fun i => restrictCompactFunction hK (F i) (hF i))
  have hb : ∀ f ∈ A, ∀ x, |f x| ≤ B := by
    rintro f ⟨i, rfl⟩ x
    exact hbound i x
  have hl : ∀ f ∈ A, LipschitzWith L f := by
    rintro f ⟨i, rfl⟩
    change LipschitzWith L (fun x : K => F i x)
    simpa only [mul_one, Function.comp_def] using (hLip i).comp (LipschitzWith.subtype_val K)
  have hc := isCompact_closure_zeroExtendLp μ hK hfin A B L hb hl
  have heq : (compactZeroExtendLp μ hK.isClosed.measurableSet hfin) '' A =
      Set.range (fun i =>
        (continuous_commonSupport_memLp μ hK hfin (F i) (hF i) (hsupp i)).toLp (F i)) := by
    have hi (i : ι) : compactZeroExtendLp μ hK.isClosed.measurableSet hfin
        (restrictCompactFunction hK (F i) (hF i)) =
        (continuous_commonSupport_memLp μ hK hfin (F i) (hF i) (hsupp i)).toLp (F i) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall (congrFun (compactZeroExtend_restrict_eq hK (F i) (hF i)
        (hsupp i)))
    ext u
    constructor
    · rintro ⟨f, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hi i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hi i⟩
  rwa [heq] at hc

end CutoffRigidity
