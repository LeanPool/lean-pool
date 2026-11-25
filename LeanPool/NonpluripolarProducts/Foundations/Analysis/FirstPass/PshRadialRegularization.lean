/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocallyUniformUpperBounds
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshSmoothApproximation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.GermPshLeviPositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition

/-!
# Smooth PSH regularization on relatively compact domains

This file isolates the part of local PSH regularization already supported by
the checked convolution and distributional-Levi infrastructure.  A real-valued
PSH function is locally integrable without a connectedness assumption, since
the argument may be made on a small ball at each point.  On every relatively
compact subdomain, compact localization and shrinking smooth kernels then give
globally smooth PSH functions converging almost everywhere.

For a continuous PSH function the convergence can be made uniform on the inner
domain.  Choosing the convolution errors geometrically small and adding an
explicit decreasing geometric constant makes the resulting sequence pointwise
decreasing while preserving smooth PSH regularity.  The corresponding theorem
has exactly the conclusion used by the local Bedford--Taylor interface.

The remaining general locally bounded case requires the classical monotonicity
of convolution by *radial* kernels as their radii decrease.  Mathlib's bundled
`ContDiffBump` API records symmetry and support, but deliberately does not record
radiality or this monotonicity, so no such property is assumed here.
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- A locally bounded real-valued PSH function is uniformly bounded in absolute
value on every compact subset of its domain. -/
theorem IsLocallyBoundedPshOn.exists_compact_abs_bound
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |u x| ≤ C := by
  have hlocal : FirstPass.LocallyUniformlyBoundedAbove
      {fun x : ComplexModel n => ((|u x| : ℝ) : EReal)}
      (Ω : Set (ComplexModel n)) := by
    intro x hx
    obtain ⟨V, hxV, hVΩ, C, hC⟩ := hu.2 x hx
    refine ⟨(V : Set (ComplexModel n)),
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨V, V.isOpen.mem_nhds hxV, by simp⟩, max C 0, ?_⟩
    intro f hf y hy
    rw [Set.mem_singleton_iff.mp hf]
    exact EReal.coe_le_coe_iff.mpr
      ((hC y hy.1).trans (le_max_left C 0))
  obtain ⟨C, hC⟩ :=
    hlocal.exists_uniform_upper_bound_on_compact hK hKΩ
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x hx
  have hxC := hC (fun y : ComplexModel n => ((|u y| : ℝ) : EReal))
    (Set.mem_singleton _) x hx
  exact (EReal.coe_le_coe_iff.mp hxC).trans (le_max_left C 0)

/-- A finite-valued PSH function is locally integrable on an arbitrary open
set.  Connectedness is unnecessary: around each point, apply the existing
integrability theorem on a contained ball. -/
theorem locallyIntegrableOn_of_plurisubharmonicOn_real
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn (fun z ↦ (u z : EReal)) Ω) :
    LocallyIntegrableOn u Ω volume := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen z hz
  have hzball : z ∈ ball z r := mem_ball_self hr
  have hpshBall : PlurisubharmonicOn (fun x ↦ (u x : EReal)) (ball z r) :=
    hu.mono hball
  have hlocal := hpshBall.locallyIntegrableOn_toReal volume
    (convex_ball z r).isPreconnected ⟨z, hzball, by simp⟩ z hzball
  simpa only [EReal.toReal_coe,
    nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds hzball),
    nhdsWithin_eq_nhds.mpr (Ω.isOpen.mem_nhds hz)] using hlocal

/-- A real-valued PSH function has nonnegative distributional Levi form on its
open domain.  The a.e. finiteness premise of the general theorem is automatic. -/
theorem hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn (fun z ↦ (u z : EReal)) Ω) :
    HasNonnegativeDistributionalLevi
      (regularDistribution volume u
        (locallyIntegrableOn_of_plurisubharmonicOn_real hu)) := by
  apply hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable
    (locallyIntegrableOn_of_plurisubharmonicOn_real hu)
  filter_upwards with z
  simp

/-- On a relatively compact subdomain, a real-valued PSH function has globally
smooth PSH convolution approximants converging almost everywhere on the inner
domain.  This is the strongest unconditional conclusion furnished by the
current non-radial bump API. -/
theorem exists_smoothPsh_aeApproximation
    {Ω U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hU : RelativelyCompactIn U Ω) :
    ∃ f : ℕ → ComplexModel n → ℝ,
      (∀ j, IsSmoothPshOn U (f j)) ∧
        ∀ᵐ z ∂volume.restrict (U : Set (ComplexModel n)),
          Tendsto (fun j ↦ f j z) atTop (𝓝 (u z)) := by
  let huL : LocallyIntegrableOn u Ω volume :=
    locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have hT : HasNonnegativeDistributionalLevi (regularDistribution volume u huL) := by
    apply hu.1.hasNonnegativeDistributionalLevi_of_locallyIntegrable huL
    filter_upwards with z
    simp
  obtain ⟨V, f, hV, hclUV, hVΩ, hsmooth, _hdisc, hpsh, hlim⟩ :=
    exists_smooth_psh_ae_approximation huL hT hU.1 hU.2
  have hUV : (U : Set (ComplexModel n)) ⊆ V := subset_closure.trans hclUV
  refine ⟨f, fun j ↦ isSmoothPshOn_of_psh (hsmooth j).contDiffOn
    ((hpsh j).mono hUV), ?_⟩
  exact ae_mono (Measure.restrict_mono hUV le_rfl) hlim

/-- On a compact subset of the domain, a locally bounded real-valued PSH
function admits one compactly localized sequence of globally smooth
approximants which is uniformly bounded on the whole ambient space.  The
approximants are PSH on a common open neighborhood of the compact set and
converge almost everywhere, globally, to the compact cutoff of the original
function. -/
theorem exists_uniformlyBounded_smoothPsh_aeApproximation_on_compact
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {S : Set (ComplexModel n)}
    (hS : IsCompact S) (hSΩ : S ⊆ Ω) :
    ∃ (U K : Set (ComplexModel n)) (f : ℕ → ComplexModel n → ℝ) (C : ℝ),
      IsOpen U ∧ S ⊆ U ∧ U ⊆ K ∧ IsCompact K ∧ K ⊆ Ω ∧ 0 ≤ C ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) ∧
      (∀ j, DiscPshOn (fun x ↦ (f j x : EReal)) U) ∧
      (∀ j, PlurisubharmonicOn (fun x ↦ (f j x : EReal)) U) ∧
      (∀ j x, |f j x| ≤ C) ∧
      ∀ᵐ x ∂volume,
        Tendsto (fun j ↦ f j x) atTop (𝓝 (K.indicator u x)) := by
  let huL : LocallyIntegrableOn u Ω volume :=
    locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have hT : HasNonnegativeDistributionalLevi
      (regularDistribution volume u huL) :=
    hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu.1
  let : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR, U, K, hU, hSU, hUK, hK, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood hS Ω.isOpen hSΩ
  obtain ⟨C, hC, huC⟩ := hu.exists_compact_abs_bound hK hKΩ
  let g : ComplexModel n → ℝ := K.indicator u
  have hgint : Integrable g volume :=
    integrable_indicator_of_locallyIntegrableOn_isCompact huL hK hKΩ
  have hgC : ∀ x, |g x| ≤ C := by
    intro x
    by_cases hx : x ∈ K
    · simpa only [g, indicator_of_mem hx] using huC x hx
    · simp only [g, indicator_of_notMem hx, abs_zero, hC]
  let f : ℕ → ComplexModel n → ℝ := fun j ↦
    mollify volume g (shrinkingBump R hR j)
  have hs (j : ℕ) (z : ComplexModel n) (hz : z ∈ U) :
      tsupport (fun x ↦
        (shrinkingBump R hR j).normed volume (x - z)) ⊆ K :=
    (tsupport_mollifier_translate_subset volume (shrinkingBump R hR j) z).trans
      ((closedBall_subset_closedBall
        (shrinkingBump_rOut_le (E := ComplexModel n) R hR j)).trans
          (hball z hz))
  have hfdisc (j : ℕ) : DiscPshOn (fun x ↦ (f j x : EReal)) U :=
    discPshOn_translationPairing_indicator huL hT
      (shrinkingBump R hR j).hasCompactSupport_normed
      (shrinkingBump R hR j).contDiff_normed
      (shrinkingBump R hR j).nonneg_normed hK hKΩ (hs j)
  refine ⟨U, K, f, C, hU, hSU, hUK, hK, hKΩ, hC, ?_, hfdisc, ?_, ?_, ?_⟩
  · intro j
    exact contDiff_mollify volume hgint.locallyIntegrable (shrinkingBump R hR j)
  · intro j
    exact (hfdisc j).plurisubharmonicOn hU
  · intro j x
    exact abs_mollify_le_of_ae_abs_le volume hgint.locallyIntegrable
      (ae_of_all volume hgC) (shrinkingBump R hR j) x
  · simpa only [f] using ae_tendsto_mollify volume hgint.locallyIntegrable R hR

/-- A quantitative uniform approximation can be corrected by an explicit
geometric constant to become pointwise decreasing.  The error budget `1/8`
leaves room between two successive corrections. -/
theorem isDecreasingApproximation_geometricCorrection
    {U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    {g : ℕ → ComplexModel n → ℝ}
    (hg : ∀ j, IsSmoothPshOn U (g j))
    (herr : ∀ j z, z ∈ U →
      dist (g j z) (u z) ≤ ((2 : ℝ)⁻¹ ^ j) / 8) :
    IsDecreasingApproximation U u
      (fun j z ↦ g j z + (2 : ℝ)⁻¹ ^ j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    apply isSmoothPshOn_of_psh
    · exact (hg j).1.add contDiffOn_const
    · have hc : PlurisubharmonicOn
          (fun _ : ComplexModel n ↦ (((2 : ℝ)⁻¹ ^ j : ℝ) : EReal)) U :=
        fun z _ ↦ plurisubharmonicAt_const _ (EReal.coe_ne_top _) z
      simpa only [EReal.coe_add] using (hg j).2.1.add hc
  · intro z hz
    apply antitone_nat_of_succ_le
    intro j
    have hj := herr j z hz
    have hjs := herr (j + 1) z hz
    rw [Real.dist_eq] at hj hjs
    have hj' := (abs_le.mp hj).1
    have hjs' := (abs_le.mp hjs).2
    have hpow : 0 ≤ (2 : ℝ)⁻¹ ^ j := pow_nonneg (by positivity) _
    change g (j + 1) z + (2 : ℝ)⁻¹ ^ (j + 1) ≤
      g j z + (2 : ℝ)⁻¹ ^ j
    rw [pow_succ] at hjs' ⊢
    norm_num at hjs' ⊢
    nlinarith
  · intro z hz
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hpow : Tendsto (fun j : ℕ ↦ (2 : ℝ)⁻¹ ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have hboundlim : Tendsto
        (fun j : ℕ ↦ (2 : ℝ)⁻¹ ^ j + ((2 : ℝ)⁻¹ ^ j) / 8)
        atTop (𝓝 0) := by
      simpa using hpow.add (hpow.div_const 8)
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ ?_) hboundlim
    calc
      dist (g j z + (2 : ℝ)⁻¹ ^ j) (u z) ≤
          dist (g j z + (2 : ℝ)⁻¹ ^ j) (g j z) + dist (g j z) (u z) :=
        dist_triangle _ _ _
      _ ≤ (2 : ℝ)⁻¹ ^ j + ((2 : ℝ)⁻¹ ^ j) / 8 :=
        add_le_add (by
          rw [Real.dist_eq, add_sub_cancel_left,
            abs_of_nonneg (pow_nonneg (by positivity) j)]) (herr j z hz)

/-- A continuous real-valued PSH function admits an actual decreasing smooth
PSH approximation on every relatively compact subdomain.  Continuity is used
only to make the compactly localized convolution error uniform; the geometric
correction above then supplies monotonicity without any radiality assumption on
the bundled bump kernel. -/
theorem exists_decreasingApproximation_of_continuousOn
    {Ω U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hcont : ContinuousOn u Ω)
    (hU : RelativelyCompactIn U Ω) :
    ∃ f : ℕ → ComplexModel n → ℝ, IsDecreasingApproximation U u f := by
  let huL : LocallyIntegrableOn u Ω volume :=
    locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have hT : HasNonnegativeDistributionalLevi (regularDistribution volume u huL) := by
    apply hu.1.hasNonnegativeDistributionalLevi_of_locallyIntegrable huL
    filter_upwards with z
    simp
  let : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR, V, K, hV, hclUV, hVK, hK, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood hU.1 Ω.isOpen hU.2
  have hgint : Integrable (K.indicator u) volume :=
    integrable_indicator_of_locallyIntegrableOn_isCompact huL hK hKΩ
  have huc : UniformContinuousOn u K :=
    hK.uniformContinuousOn_of_continuous (hcont.mono hKΩ)
  have hchoice : ∀ j : ℕ, ∃ m : ℕ, ∀ z ∈ V,
      dist (mollify volume (K.indicator u) (shrinkingBump R hR m) z) (u z) ≤
        ((2 : ℝ)⁻¹ ^ j) / 8 := by
    intro j
    have he : 0 < ((2 : ℝ)⁻¹ ^ j) / 8 := by positivity
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc _ he
    have hevent : ∀ᶠ m : ℕ in atTop,
        (shrinkingBump (E := ComplexModel n) R hR m).rOut < δ :=
      (tendsto_shrinkingBump_rOut (E := ComplexModel n) R hR).eventually
        (Iio_mem_nhds hδ)
    obtain ⟨m, hm⟩ := Filter.Eventually.exists hevent
    refine ⟨m, ?_⟩
    intro z hz
    have hzK : z ∈ K := hVK hz
    rw [mollify_eq_convolution, ← indicator_of_mem hzK u]
    apply ContDiffBump.dist_normed_convolution_le hgint.aestronglyMeasurable
    intro x hx
    have hxK : x ∈ K := hball z hz (by
      exact mem_closedBall.mpr (((mem_ball.mp hx).trans_le
        (shrinkingBump_rOut_le (E := ComplexModel n) R hR m)).le))
    have hdist : dist (u x) (u z) ≤ ((2 : ℝ)⁻¹ ^ j) / 8 :=
      (hmod x hxK z hzK ((mem_ball.mp hx).trans hm)).le
    simpa only [indicator_of_mem hxK, indicator_of_mem hzK] using hdist
  choose m hm using hchoice
  let g : ℕ → ComplexModel n → ℝ := fun j ↦
    mollify volume (K.indicator u) (shrinkingBump R hR (m j))
  have hsupp (j : ℕ) (z : ComplexModel n) (hz : z ∈ V) :
      tsupport (fun x ↦
        (shrinkingBump R hR (m j)).normed volume (x - z)) ⊆ K :=
    (tsupport_mollifier_translate_subset volume (shrinkingBump R hR (m j)) z).trans
      ((closedBall_subset_closedBall
        (shrinkingBump_rOut_le (E := ComplexModel n) R hR (m j))).trans
          (hball z hz))
  have hdisc (j : ℕ) : DiscPshOn (fun z ↦ (g j z : EReal)) V :=
    discPshOn_translationPairing_indicator huL hT
      (shrinkingBump R hR (m j)).hasCompactSupport_normed
      (shrinkingBump R hR (m j)).contDiff_normed
      (shrinkingBump R hR (m j)).nonneg_normed hK hKΩ (hsupp j)
  have hUV : (U : Set (ComplexModel n)) ⊆ V := subset_closure.trans hclUV
  have hg (j : ℕ) : IsSmoothPshOn U (g j) :=
    isSmoothPshOn_of_psh
      (contDiff_mollify volume hgint.locallyIntegrable
        (shrinkingBump R hR (m j))).contDiffOn
      ((hdisc j).plurisubharmonicOn hV |>.mono hUV)
  refine ⟨_, isDecreasingApproximation_geometricCorrection hg ?_⟩
  intro j z hz
  exact hm j z (hUV hz)

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
