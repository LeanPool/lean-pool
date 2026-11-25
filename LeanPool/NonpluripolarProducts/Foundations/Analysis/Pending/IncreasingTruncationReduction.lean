/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.NonPluripolarLimit
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IncreasingPshBallSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.VaguePortmanteau

/-!
# Lower semicontinuity of non-pluripolar measures from bounded increasing convergence

Let `v_j` be an increasing sequence of plurisubharmonic functions on an open set
`Ω ⊆ ℂⁿ` and `V = (sup_j v_j)^*` its regularized limit.  We show that on open sets
`O ⊆ Ω`

  `⟨(ddᶜ V)ⁿ⟩(O) ≤ liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`,

assuming the Bedford–Taylor convergence theorem for *bounded* increasing sequences:
if locally bounded plurisubharmonic `w_j` increase almost everywhere to a locally
bounded plurisubharmonic `W`, then `(ddᶜ w_j)ⁿ → (ddᶜ W)ⁿ` and
`w_j (ddᶜ w_j)ⁿ → W (ddᶜ W)ⁿ` vaguely on `Ω` (Błocki, *The complex Monge–Ampère
operator in pluripotential theory*, Theorem 2.2.5).
The truncation argument is a local adaptation of
[Darvas–Di Nezza–Lu, Theorem 2.6](https://arxiv.org/html/2303.11584#S2.Thmtheorem6),
which assumes convergence in capacity and bounded quasi-continuous weights. It concerns
the unweighted local version of [Xia's semicontinuity theorem](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L459-L478).

**Proof.**  Fix levels `k < K` and put `W = max(V, -K)`, `w_j = max(v_j, -K)`.  Since
`sup_j v_j = V` Lebesgue-almost everywhere (`ae_uscRegularization_iSup_eq_on_ball`),
`w_j ↑ W` almost everywhere.  Let `O ⊆ Ω` be open with `V ≤ c` on `O`.  By
plurifine locality, the `k`-th truncation measure of `V` on `O` is
`μ_W(O ∩ {V > -k})`, and `W + K ≥ K - k` on `{V > -k}`, so

  `(K - k) · ⟨V⟩_k(O) ≤ ((W + K) μ_W)(O) ≤ liminf_j ((w_j + K) μ_{w_j})(O)`

by the open-set portmanteau inequality, the positive measures `(w_j + K) μ_{w_j}`
converging vaguely to `(W + K) μ_W` by the assumed bounded convergence.  The weight
`w_j + K` vanishes off `{v_j > -K}` and is at most `c + K` on `O`, whence
`((w_j + K) μ_{w_j})(O) ≤ (c + K) ⟨v_j⟩_K(O) ≤ (c + K) ⟨(ddᶜ v_j)ⁿ⟩(O)`.  Dividing by
`K - k` and letting `K → ∞` gives `⟨V⟩_k(O) ≤ liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`.  Finally
`O` is exhausted by compact sets, each contained in a relatively compact open
subset on which `V` is bounded above, and `k → ∞`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingTruncationLimit

open MeasureLocality (integrable_of_tsupport_subset)

open FirstPass FirstPass.MongeAmpere MongeAmpere VaguePortmanteau

/-- The zero extension of a real function whose extended-real coercion is upper
semicontinuous on an open set is Borel measurable. -/
theorem measurable_indicator_of_upperSemicontinuousOn_coe {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ}
    (hf : UpperSemicontinuousOn (fun z => (f z : EReal)) Ω) :
    Measurable (Ω.indicator f) := by
  refine measurable_of_Iio fun a => ?_
  have hopen : IsOpen (Ω ∩ {z | f z < a}) := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have h := hf z hz.1 (a : EReal) (EReal.coe_lt_coe_iff.mpr hz.2)
    rw [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hz.1)] at h
    filter_upwards [h, hΩ.mem_nhds hz.1] with y hy hyΩ
    exact ⟨hyΩ, EReal.coe_lt_coe_iff.mp hy⟩
  have heq : Ω.indicator f ⁻¹' Iio a = (Ω ∩ {z | f z < a}) ∪ (Ωᶜ ∩ {_z | (0 : ℝ) < a}) := by
    ext z
    by_cases hz : z ∈ Ω <;> simp [hz]
  rw [heq]
  exact hopen.measurableSet.union (hΩ.measurableSet.compl.inter (MeasurableSet.const _))

variable {n : ℕ}

/-- The density `z ↦ w(z) + K` (with `w` extended by zero off `Ω`). -/
def shiftedDensity (Ω : Opens (ComplexModel n)) (w : ComplexModel n → ℝ) (K : ℕ) :
    ComplexModel n → ℝ≥0∞ :=
  fun z => ENNReal.ofReal ((Ω : Set (ComplexModel n)).indicator w z + K)

theorem measurable_shiftedDensity {Ω : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn Ω w) (K : ℕ) : Measurable (shiftedDensity Ω w K) :=
  ((measurable_indicator_of_upperSemicontinuousOn_coe Ω.isOpen
    hw.1.upperSemicontinuousOn).add_const _).ennreal_ofReal

/-- Against a nonnegative continuous compactly supported test, the weighted measure
`(w + K) μ_w` of a locally bounded psh `w ≥ -K` has the expected integral. -/
theorem lintegral_ofReal_withDensity_shiftedDensity {Ω : Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Ω w) {K : ℕ}
    (hwK : ∀ z ∈ Ω, -(K : ℝ) ≤ w z) {φ : ComplexModel n → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) (hφ0 : ∀ z, 0 ≤ φ z) :
    ∫⁻ z, ENNReal.ofReal (φ z)
        ∂((canonicalBedfordTaylorMeasure Ω w hw).withDensity (shiftedDensity Ω w K)) =
      ENNReal.ofReal (∫ z, φ z * w z ∂(canonicalBedfordTaylorMeasure Ω w hw) +
        K * ∫ z, φ z ∂(canonicalBedfordTaylorMeasure Ω w hw)) := by
  set μ := canonicalBedfordTaylorMeasure Ω w hw with hμ
  set Ωs : Set (ComplexModel n) := (Ω : Set (ComplexModel n))
  have hmeas : Measurable (Ωs.indicator w) :=
    measurable_indicator_of_upperSemicontinuousOn_coe Ω.isOpen hw.1.upperSemicontinuousOn
  obtain ⟨C, -, hC⟩ := hw.1.exists_nonnegative_compact_upper_bound hφc hφΩ
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  set g : ComplexModel n → ℝ := fun z => φ z * (Ωs.indicator w z + K) with hg
  have hind : ∀ z, φ z * Ωs.indicator w z = φ z * w z := by
    intro z
    by_cases hz : z ∈ Ωs
    · rw [indicator_of_mem hz]
    · have : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφΩ h))
      simp [this]
  have hg0 : ∀ z, 0 ≤ g z := by
    intro z
    refine mul_nonneg (hφ0 z) ?_
    by_cases hz : z ∈ Ωs
    · rw [indicator_of_mem hz]; linarith [hwK z hz]
    · rw [indicator_of_notMem hz]; positivity
  have hgi : Integrable g μ := by
    rw [← integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left _ _).trans (subset_tsupport φ))]
    refine Measure.integrableOn_of_bounded (M := M * (C + K))
      (canonicalBedfordTaylorMeasure_finiteOnCompacts hw hφc hφΩ).ne
      (hφ.measurable.mul (hmeas.add_const _)).aestronglyMeasurable
      (ae_restrict_of_forall_mem (isClosed_tsupport φ).measurableSet fun z hz => ?_)
    have hzΩ : z ∈ Ωs := hφΩ hz
    rw [indicator_of_mem hzΩ, Real.norm_eq_abs, abs_mul]
    have h1 : |w z + K| ≤ C + K := by
      rw [abs_of_nonneg (by linarith [hwK z hzΩ])]
      linarith [EReal.coe_le_coe_iff.mp (hC z hz)]
    exact mul_le_mul (hM z) h1 (abs_nonneg _) ((abs_nonneg _).trans (hM z))
  have hφi : Integrable φ μ :=
    integrable_of_tsupport_subset (fun _ hK hKΩ =>
      canonicalBedfordTaylorMeasure_finiteOnCompacts hw hK hKΩ) hφ hφc hφΩ
  have hφwi : Integrable (fun z => φ z * w z) μ := by
    refine (hgi.sub (hφi.const_mul K)).congr (Eventually.of_forall fun z => ?_)
    simp only [hg, Pi.sub_apply]
    rw [mul_add, hind]
    ring
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_shiftedDensity hw K)
    hφ.measurable.ennreal_ofReal]
  have hpt : ∀ z, (shiftedDensity Ω w K * fun z => ENNReal.ofReal (φ z)) z =
      ENNReal.ofReal (g z) := by
    intro z
    simp only [Pi.mul_apply, shiftedDensity, hg]
    rw [mul_comm, ← ENNReal.ofReal_mul (hφ0 z)]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)]
  congr 1
  have hsplit : g = fun z => φ z * w z + K * φ z := by
    funext z
    simp only [hg]
    rw [mul_add, hind]
    ring
  rw [hsplit, integral_add hφwi (hφi.const_mul _), integral_const_mul]

/-- The members of an increasing sequence lie below its regularized limit. -/
theorem le_of_eqOn_uscRegularization_iSup {Ω : Opens (ComplexModel n)}
    {v : ℕ → ComplexModel n → EReal} {V : ComplexModel n → EReal}
    (hVeq : EqOn V (uscRegularization (⨆ j, v j)) Ω) (j : ℕ) {z : ComplexModel n}
    (hz : z ∈ Ω) : v j z ≤ V z := by
  rw [hVeq hz]
  refine le_trans ?_ (le_uscRegularization _ z)
  rw [iSup_apply]
  exact le_iSup (fun i => v i z) j

/-- Along an increasing sequence of plurisubharmonic functions, the truncations at a
fixed level converge Lebesgue-almost everywhere on `Ω` to the truncation of the
regularized limit: the supremum agrees with its regularization almost everywhere. -/
theorem ae_tendsto_truncationReal_of_monotone {Ω : Opens (ComplexModel n)}
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hmono : ∀ z ∈ Ω, Monotone fun j => v j z)
    {V : ComplexModel n → EReal} (hVeq : EqOn V (uscRegularization (⨆ j, v j)) Ω)
    (hV : PlurisubharmonicOn V Ω) (K : ℕ) :
    ∀ᵐ z, z ∈ Ω → Tendsto (fun j => truncationReal (v j) K z) atTop
      (𝓝 (truncationReal V K z)) := by
  have hS : ∀ z : Ω, ∃ S : ℝ, 0 < S ∧ closedBall (z : ComplexModel n) S ⊆ Ω := by
    intro z
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen z z.2
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose S hSpos hSsub using hS
  have hloc : ∀ z : Ω, ∀ᵐ x, x ∈ ball (z : ComplexModel n) (S z / 2) →
      V x = ⨆ j, v j x := by
    intro z
    obtain ⟨C, -, hC⟩ := hV.exists_nonnegative_compact_upper_bound
      (isCompact_closedBall _ _) (hSsub z)
    have h := ae_uscRegularization_iSup_eq_on_ball (u := v) (U := (Ω : Set (ComplexModel n)))
      (fun j => (hv j).discPshOn) hmono volume (z : ComplexModel n) (hSpos z)
      (ball_subset_closedBall.trans (hSsub z))
      (fun j y hy => (le_of_eqOn_uscRegularization_iSup hVeq j
        (hSsub z (ball_subset_closedBall hy))).trans (hC y (ball_subset_closedBall hy)))
    filter_upwards [h] with x hx hxb
    have hxΩ : x ∈ Ω := hSsub z (ball_subset_closedBall
      (ball_subset_ball (half_le_self (hSpos z).le) hxb))
    rw [hVeq hxΩ, ← hx hxb]
    congr 1
    funext y
    exact iSup_apply
  obtain ⟨T, hTc, hTU⟩ := isOpen_iUnion_countable
    (fun z : Ω => ball (z : ComplexModel n) (S z / 2)) (fun _ => isOpen_ball)
  have hae : ∀ᵐ x, x ∈ Ω → V x = ⨆ j, v j x := by
    filter_upwards [(ae_ball_iff hTc).mpr fun i _ => hloc i] with x hx hxΩ
    have hmem : x ∈ ⋃ i ∈ T, ball (i : ComplexModel n) (S i / 2) := by
      rw [hTU]
      exact mem_iUnion.mpr ⟨⟨x, hxΩ⟩, mem_ball_self (half_pos (hSpos _))⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hmem
    exact hx i hi hxi
  filter_upwards [hae] with z hz hzΩ
  have h1 : Tendsto (fun j => v j z) atTop (𝓝 (V z)) := by
    rw [hz hzΩ]
    exact tendsto_atTop_iSup (hmono z hzΩ)
  have h2 : Tendsto (fun j => truncation (v j) K z) atTop (𝓝 (truncation V K z)) :=
    h1.max tendsto_const_nhds
  have h3 : Tendsto (fun j => ((truncationReal (v j) K z : ℝ) : EReal)) atTop
      (𝓝 ((truncationReal V K z : ℝ) : EReal)) := by
    rw [coe_truncationReal hV K hzΩ]
    exact h2.congr fun j => (coe_truncationReal (hv j) K hzΩ).symm
  exact EReal.tendsto_coe.mp h3

/-- The hypothesis supplied by the Bedford–Taylor convergence theorem for bounded
increasing sequences: vague convergence on `Ω` of the Monge–Ampère measures and of
the measures weighted by the potentials. -/
def BoundedIncreasingConvergence (Ω : Opens (ComplexModel n)) : Prop :=
  ∀ (w : ℕ → ComplexModel n → ℝ) (W : ComplexModel n → ℝ)
    (hw : ∀ j, IsLocallyBoundedPshOn Ω (w j)) (hW : IsLocallyBoundedPshOn Ω W),
    (∀ z ∈ Ω, Monotone fun j => w j z) →
    (∀ᵐ z, z ∈ Ω → Tendsto (fun j => w j z) atTop (𝓝 (W z))) →
    ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
      tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
      Tendsto (fun j => ∫ z, χ z ∂(canonicalBedfordTaylorMeasure Ω (w j) (hw j))) atTop
          (𝓝 (∫ z, χ z ∂(canonicalBedfordTaylorMeasure Ω W hW))) ∧
        Tendsto (fun j => ∫ z, χ z * w j z ∂(canonicalBedfordTaylorMeasure Ω (w j) (hw j)))
          atTop (𝓝 (∫ z, χ z * W z ∂(canonicalBedfordTaylorMeasure Ω W hW)))

theorem truncationReal_ge_neg {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) (K : ℕ) {z : ComplexModel n} (hz : z ∈ Ω) :
    -(K : ℝ) ≤ truncationReal u K z := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncationReal hu K hz]
  exact truncation_lower_bound u K z

/-- **Main estimate at two levels.** On an open `O ⊆ Ω` where `V ≤ c`, for levels
`k ≤ K`: `(K - k) ⟨V⟩_k(O) ≤ (c + K) liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`. -/
theorem ofReal_mul_truncationMeasure_le {Ω : Opens (ComplexModel n)}
    (hconv : BoundedIncreasingConvergence Ω)
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hmono : ∀ z ∈ Ω, Monotone fun j => v j z)
    {V : ComplexModel n → EReal} (hVeq : EqOn V (uscRegularization (⨆ j, v j)) Ω)
    (hV : PlurisubharmonicOn V Ω)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) {c : ℝ}
    (hc : ∀ z ∈ O, V z ≤ c) {k K : ℕ} (hkK : k ≤ K) :
    ENNReal.ofReal (K - k) * truncationMeasure Ω V hV k O ≤
      ENNReal.ofReal (c + K) *
        liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop := by
  set W := truncationReal V K with hWdef
  have hW := truncationReal_isLocallyBoundedPshOn hV K
  set w : ℕ → ComplexModel n → ℝ := fun j => truncationReal (v j) K with hwdef
  have hw : ∀ j, IsLocallyBoundedPshOn Ω (w j) := fun j =>
    truncationReal_isLocallyBoundedPshOn (hv j) K
  have hwmono : ∀ z ∈ Ω, Monotone fun j => w j z := by
    intro z hz i j hij
    apply EReal.coe_le_coe_iff.mp
    simp only [hwdef]
    rw [coe_truncationReal (hv i) K hz, coe_truncationReal (hv j) K hz]
    exact max_le_max (hmono z hz hij) le_rfl
  have hconv' := hconv w W hw hW hwmono (ae_tendsto_truncationReal_of_monotone hv hmono hVeq hV K)
  set μW := canonicalBedfordTaylorMeasure Ω W hW with hμW
  -- the truncation measure of `V` is dominated by the weighted measure of `W`
  have step1 : ENNReal.ofReal (K - k) * truncationMeasure Ω V hV k O ≤
      (μW.withDensity (shiftedDensity Ω W K)) O := by
    rw [withDensity_apply _ hO.measurableSet, truncationMeasure,
      ← bedfordTaylor_truncation_restrict hV hkK, Measure.restrict_apply hO.measurableSet,
      ← setLIntegral_const]
    refine le_trans (setLIntegral_mono (measurable_shiftedDensity hW K) fun z hz => ?_)
      (lintegral_mono_set inter_subset_left)
    obtain ⟨hzΩ, hzV⟩ := hz.2
    simp only [shiftedDensity, indicator_of_mem (show z ∈ (Ω : Set (ComplexModel n)) from hzΩ)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : -(k : ℝ) ≤ W z := by
      apply EReal.coe_le_coe_iff.mp
      rw [hWdef, coe_truncationReal hV K hzΩ]
      exact hzV.le.trans (le_max_left _ _)
    linarith
  -- open-set portmanteau for the weighted measures
  have step2 : (μW.withDensity (shiftedDensity Ω W K)) O ≤
      liminf (fun j => ((canonicalBedfordTaylorMeasure Ω (w j) (hw j)).withDensity
        (shiftedDensity Ω (w j) K)) O) atTop := by
    refine measure_le_liminf_of_le_liminf_lintegral hO fun φ hφ hφc hφO hφ01 => ?_
    have hφΩ := hφO.trans hOΩ
    have hφ0 : ∀ z, 0 ≤ φ z := fun z => (hφ01 z).1
    rw [lintegral_ofReal_withDensity_shiftedDensity hW (fun z hz => truncationReal_ge_neg hV K hz)
      hφ hφc hφΩ hφ0]
    have hj : ∀ j, ∫⁻ z, ENNReal.ofReal (φ z) ∂((canonicalBedfordTaylorMeasure Ω (w j)
        (hw j)).withDensity (shiftedDensity Ω (w j) K)) =
        ENNReal.ofReal (∫ z, φ z * w j z ∂(canonicalBedfordTaylorMeasure Ω (w j) (hw j)) +
          K * ∫ z, φ z ∂(canonicalBedfordTaylorMeasure Ω (w j) (hw j))) := fun j =>
      lintegral_ofReal_withDensity_shiftedDensity (hw j)
        (fun z hz => truncationReal_ge_neg (hv j) K hz) hφ hφc hφΩ hφ0
    simp_rw [hj]
    obtain ⟨h1, h2⟩ := hconv' φ hφ hφc hφΩ
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      (h2.add (h1.const_mul (K : ℝ)))).liminf_eq.ge
  -- the weight vanishes off the strict locus of `v_j` and is at most `c + K` on `O`
  have step3 : ∀ j, ((canonicalBedfordTaylorMeasure Ω (w j) (hw j)).withDensity
      (shiftedDensity Ω (w j) K)) O ≤
        ENNReal.ofReal (c + K) * truncationLimitMeasure Ω (v j) (hv j) O := by
    intro j
    have hSK := measurableSet_strictTruncationLocus (hv j) K
    refine le_trans ?_ (mul_le_mul_right (Measure.le_iff'.mp
      (truncationMeasure_le_limit (hv j) K) O) _)
    rw [withDensity_apply _ hO.measurableSet, truncationMeasure,
      Measure.restrict_apply hO.measurableSet, inter_comm,
      ← Measure.restrict_apply hSK, ← lintegral_indicator_const hSK]
    refine setLIntegral_mono' hO.measurableSet fun z hz => ?_
    have hzΩ : z ∈ Ω := hOΩ hz
    simp only [shiftedDensity, indicator_of_mem (show z ∈ (Ω : Set (ComplexModel n)) from hzΩ)]
    by_cases hzS : z ∈ strictTruncationLocus Ω (v j) K
    · rw [indicator_of_mem hzS]
      refine ENNReal.ofReal_le_ofReal ?_
      have : w j z ≤ c := by
        apply EReal.coe_le_coe_iff.mp
        simp only [hwdef]
        rw [coe_truncationReal (hv j) K hzΩ, truncation_eq_on_strictLocus K hzS]
        exact (le_of_eqOn_uscRegularization_iSup hVeq j hzΩ).trans (hc z hz)
      linarith
    · rw [indicator_of_notMem hzS]
      have hle : v j z ≤ ((-(K : ℝ) : ℝ) : EReal) := not_lt.mp fun h => hzS ⟨hzΩ, h⟩
      have : w j z = -(K : ℝ) := by
        apply EReal.coe_injective
        simp only [hwdef]
        rw [coe_truncationReal (hv j) K hzΩ, truncation, max_eq_right hle]
      simp [this]
  calc ENNReal.ofReal (K - k) * truncationMeasure Ω V hV k O
      ≤ (μW.withDensity (shiftedDensity Ω W K)) O := step1
    _ ≤ _ := step2
    _ ≤ liminf (fun j => ENNReal.ofReal (c + K) *
          truncationLimitMeasure Ω (v j) (hv j) O) atTop :=
        liminf_le_liminf (Eventually.of_forall step3)
    _ = _ := ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top

/-- **Fixed level.** On an open `O ⊆ Ω` where `V` is bounded above, every truncation
measure of `V` is at most `liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`: let the upper level `K → ∞`. -/
theorem truncationMeasure_le_liminf_of_increasingConvergence {Ω : Opens (ComplexModel n)}
    (hconv : BoundedIncreasingConvergence Ω)
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hmono : ∀ z ∈ Ω, Monotone fun j => v j z)
    {V : ComplexModel n → EReal} (hVeq : EqOn V (uscRegularization (⨆ j, v j)) Ω)
    (hV : PlurisubharmonicOn V Ω)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ z ∈ O, V z ≤ c) (k : ℕ) :
    truncationMeasure Ω V hV k O ≤
      liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop := by
  set L := liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop with hL
  set x := truncationMeasure Ω V hV k O with hx
  rcases eq_or_ne L ⊤ with hLt | hLt
  · rw [hLt]; exact le_top
  have hcore : ∀ K : ℕ, k ≤ K →
      ENNReal.ofReal (K - k) * x ≤ ENNReal.ofReal (c + K) * L := fun K hK =>
    ofReal_mul_truncationMeasure_le hconv hv hmono hVeq hV hO hOΩ hc hK
  have hxt : x ≠ ⊤ := by
    intro hxt
    have h := hcore (k + 1) (Nat.le_succ k)
    rw [hxt] at h
    have h1 : ENNReal.ofReal (((k + 1 : ℕ) : ℝ) - k) = 1 := by push_cast; simp
    rw [h1, one_mul, top_le_iff] at h
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLt h
  have hreal : ∀ K : ℕ, k < K → x.toReal ≤ (c + K) / (K - k) * L.toReal := by
    intro K hK
    have hpos : (0 : ℝ) < K - k := sub_pos.mpr (Nat.cast_lt.mpr hK)
    have h := hcore K hK.le
    rw [← ENNReal.ofReal_toReal hxt, ← ENNReal.ofReal_toReal hLt,
      ← ENNReal.ofReal_mul hpos.le, ← ENNReal.ofReal_mul (by positivity)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith
  have hlim : Tendsto (fun K : ℕ => (c + K) / (K - k) * L.toReal) atTop
      (𝓝 ((1 + 0) * L.toReal)) := by
    have hden : Tendsto (fun K : ℕ => (K : ℝ) - k) atTop atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-(k : ℝ)) tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun K : ℕ => (c + k) / ((K : ℝ) - k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    refine ((tendsto_const_nhds.add h0).mul_const _).congr' ?_
    filter_upwards [eventually_gt_atTop k] with K hK
    have hpos : (K : ℝ) - k ≠ 0 := (sub_pos.mpr (Nat.cast_lt.mpr hK)).ne'
    field_simp
    ring
  rw [add_zero, one_mul] at hlim
  have hle : x.toReal ≤ L.toReal :=
    ge_of_tendsto hlim ((eventually_gt_atTop k).mono fun K hK => hreal K hK)
  exact (ENNReal.toReal_le_toReal hxt hLt).mp hle

/-- **Lower semicontinuity of the non-pluripolar Monge–Ampère measure along increasing
sequences, from bounded increasing Bedford–Taylor convergence.** -/
theorem truncationLimitMeasure_le_liminf_of_increasingConvergence
    {Ω : Opens (ComplexModel n)}
    (hconv : ∀ (w : ℕ → ComplexModel n → ℝ) (W : ComplexModel n → ℝ)
      (hw : ∀ j, IsLocallyBoundedPshOn Ω (w j)) (hW : IsLocallyBoundedPshOn Ω W),
      (∀ z ∈ Ω, Monotone fun j => w j z) →
      (∀ᵐ z, z ∈ Ω → Tendsto (fun j => w j z) atTop (𝓝 (W z))) →
      ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
        tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
        Tendsto (fun j => ∫ z, χ z ∂(canonicalBedfordTaylorMeasure Ω (w j) (hw j))) atTop
            (𝓝 (∫ z, χ z ∂(canonicalBedfordTaylorMeasure Ω W hW))) ∧
          Tendsto (fun j => ∫ z, χ z * w j z ∂(canonicalBedfordTaylorMeasure Ω (w j) (hw j)))
            atTop (𝓝 (∫ z, χ z * W z ∂(canonicalBedfordTaylorMeasure Ω W hW))))
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hmono : ∀ z ∈ Ω, Monotone fun j => v j z)
    {V : ComplexModel n → EReal} (hVeq : EqOn V (uscRegularization (⨆ j, v j)) Ω)
    (hV : PlurisubharmonicOn V Ω)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) :
    truncationLimitMeasure Ω V hV O ≤
      liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop := by
  rw [truncationLimitMeasure_apply]
  refine iSup_le fun k => ?_
  obtain ⟨Kc, hKc, hKcl, hKO, hKmono, hKU⟩ := hO.exists_monotone_isCompact_iUnion_eq
  have hsup : truncationMeasure Ω V hV k O = ⨆ m, truncationMeasure Ω V hV k (Kc m) := by
    conv_lhs => rw [← hKU]
    exact hKmono.measure_iUnion
  rw [hsup]
  refine iSup_le fun m => ?_
  obtain ⟨δ, hδ, hδO⟩ := (hKc m).exists_cthickening_subset_open hO (hKO m)
  obtain ⟨C, hC0, hC⟩ := hV.exists_nonnegative_compact_upper_bound (hKc m).cthickening
    (hδO.trans hOΩ)
  have hUO : thickening δ (Kc m) ⊆ O := (thickening_subset_cthickening δ _).trans hδO
  calc truncationMeasure Ω V hV k (Kc m)
      ≤ truncationMeasure Ω V hV k (thickening δ (Kc m)) :=
        measure_mono (self_subset_thickening hδ _)
    _ ≤ liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) (thickening δ (Kc m))) atTop :=
        truncationMeasure_le_liminf_of_increasingConvergence hconv hv hmono hVeq hV
          isOpen_thickening (hUO.trans hOΩ) hC0
          (fun z hz => hC z (thickening_subset_cthickening δ _ hz)) k
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall fun j => measure_mono hUO)

end SGPT.Foundations.Analysis.Pending.IncreasingTruncationLimit
