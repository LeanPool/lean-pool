/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DDCOverlap
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshUltrafilterLimit
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.FormPullbackFunctorial
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.NonKahlerLocus

/-!
# Gluing chart weak limits into a `θ`-plurisubharmonic function

Source: Demailly, CADG I.4 (weak limits of distributions, change of variables) and I.5.8
(a distribution with nonnegative Levi form is a plurisubharmonic function,
`Pending.PshRepresentative`); the gluing of local potentials is the uniqueness of
plurisubharmonic representatives (`IsPshRepresentative.unique`).  TN.4 plan, step B6, finding F6
route (i), piece (i-4'): the normalized potentials
`v_ε` of the currents `R_ε` have weak limits in every chart, and the limit current
`R = θ' + dd^c V` needs ONE global `θ'`-psh potential `V`.

Let `v_i : M → ℝ` be functions on a complex manifold and `l` a nontrivial filter (in the
application an ultrafilter).  Suppose that in every chart `e` the chart functions
`v_i ∘ e⁻¹` converge weakly to a distribution `T_e` (`IsChartLimit`), and that near every point
of every chart `T_e + ρ` has nonnegative Levi form for a smooth local potential `ρ` of `θ`.
Then (`exists_isThetaPshPotential_of_isChartLimit`) there is a `θ`-psh potential `V`, finite
almost everywhere, whose chart functions represent every `T_e`.

## The argument

* **Change of variables** (`integral_mul_eq_integral_pullFun`): for a chart transition `F` and a
  function `ψ` supported in its target, `∫ ψ h = ∫ (J · ψ ∘ F) (h ∘ F)` with `J = |det DF|`;
  `J · ψ ∘ F` is again a test function (`pullTest`; `J` is smooth: `contDiff_det`).
* **Compatibility of the chart limits** (`IsChartLimit.apply_pullTest`): `T_f ψ = T_e (J · ψ ∘ F)`,
  because the identity holds for every `v_i` and limits are unique.  Consequently a density of
  `T_f` transports to a density of `T_e` (`IsChartLimit.apply_eq_integral_comp`).
* **Local representatives** (`LocalRep`): near every point, `T_e + ρ` has a psh representative `u`
  (CADG I.5.8).
* **Identification** (`LocalRep.eq_transport`): for representatives in two charts `e`, `d`,
  `u_e = u_d ∘ F - ρ_d ∘ F + ρ_e` everywhere on a ball: both sides are psh (holomorphic pullback,
  and `ρ_e - ρ_d ∘ F` is pluriharmonic) and represent the same distribution, so they agree
  (`IsPshRepresentative.unique`).
* **Gluing**: `V(x) := u_x(e_x x) - ρ_x(e_x x)` in the preferred chart `e_x` at `x`; by the
  identification, `V ∘ e⁻¹ + ρ = u` on every local representative in every chart.

`exists_isChartLimit` produces the chart limits along an ultrafilter from uniform `L¹` bounds on
compact subsets of the charts (`PshUltrafilterLimit.exists_tendsto_regularDistribution`).
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing

open FirstPass FirstPass.HolomorphicMaps LocalCurrents

noncomputable section

/-! ### Distribution helpers -/

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}

/-- A test function times a locally integrable function is integrable. -/
theorem integrable_testFunction_mul {f : E → ℝ} (hf : LocallyIntegrableOn f Ω μ)
    (φ : 𝓓(Ω, ℝ)) : Integrable (fun x => φ x * f x) μ := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hint : IntegrableOn f (tsupport φ) μ :=
    hf.integrableOn_compact_subset φ.tsupport_subset hK
  have h2 : IntegrableOn (fun x => φ x * f x) (tsupport φ) μ :=
    hint.continuousOn_mul φ.continuous.continuousOn hK
  exact h2.integrable_of_forall_notMem_eq_zero fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]

theorem regularDistribution_add {f g : E → ℝ} (hf : LocallyIntegrableOn f Ω μ)
    (hg : LocallyIntegrableOn g Ω μ) :
    regularDistribution μ (fun x => f x + g x) (hf.add hg) =
      regularDistribution μ f hf + regularDistribution μ g hg := by
  ext φ
  change _ = regularDistribution μ f hf φ + regularDistribution μ g hg φ
  simp only [regularDistribution_apply, mul_add]
  exact integral_add (integrable_testFunction_mul hf φ) (integrable_testFunction_mul hg φ)

theorem regularDistribution_sub {f g : E → ℝ} (hf : LocallyIntegrableOn f Ω μ)
    (hg : LocallyIntegrableOn g Ω μ) :
    regularDistribution μ (fun x => f x - g x) (hf.sub hg) =
      regularDistribution μ f hf - regularDistribution μ g hg := by
  ext φ
  change _ = regularDistribution μ f hf φ - regularDistribution μ g hg φ
  simp only [regularDistribution_apply, mul_sub]
  exact integral_sub (integrable_testFunction_mul hf φ) (integrable_testFunction_mul hg φ)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem restrictDistribution_add {U : Opens E} (S T : 𝓓'(Ω, ℝ)) (h : U ≤ Ω) :
    restrictDistribution (S + T) h = restrictDistribution S h + restrictDistribution T h := by
  ext φ
  rfl

omit [OpensMeasurableSpace E] in
omit [MeasurableSpace E] in
/-- Restrictions to a chart cover determine the distribution on the domain. -/
theorem distribution_eq_of_restrict_eq [FiniteDimensional ℝ E]
    {T S : 𝓓'(Ω, ℝ)} {ι : Type*}
    (U : ι → Opens E) (hUΩ : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i)
    (hlocal : ∀ i,
      restrictDistribution T (hUΩ i) = restrictDistribution S (hUΩ i)) :
    T = S :=
  SGPT.Foundations.Analysis.Pending.distribution_eq_of_restrict_eq_on_openCover U hUΩ hcover hlocal

end Helpers

/-! ### Extended-real bookkeeping -/

theorem ereal_add_coe_neg_add_coe (a : EReal) (r : ℝ) :
    a + ((-r : ℝ) : EReal) + (r : EReal) = a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

theorem ereal_eq_add_coe_neg_of_add_coe_eq {a b : EReal} {r : ℝ} (h : a + (r : EReal) = b) :
    a = b + ((-r : ℝ) : EReal) := by
  rw [← h]
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

theorem ereal_add_coe_finite {a : EReal} (ha : a ≠ ⊤ ∧ a ≠ ⊥) (r : ℝ) :
    a + (r : EReal) ≠ ⊤ ∧ a + (r : EReal) ≠ ⊥ := by
  lift a to ℝ using ha
  rw [← EReal.coe_add]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

theorem ereal_toReal_add_coe {a : EReal} (ha : a ≠ ⊤ ∧ a ≠ ⊥) (r : ℝ) :
    (a + (r : EReal)).toReal = a.toReal + r := by
  lift a to ℝ using ha
  rw [← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]

/-! ### The Jacobian of a chart transition -/

/-- The determinant is a smooth function of the linear map (a polynomial in the matrix
entries). -/
theorem contDiff_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ContDiff ℝ ∞ (fun A : E →L[ℝ] E => A.det) := by
  classical
  let b := Module.finBasis ℝ E
  have h : (fun A : E →L[ℝ] E => A.det) = fun A =>
      ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) * ∏ i, b.coord (σ i) (A (b i)) := by
    funext A
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [LinearMap.toMatrix_apply]
  rw [h]
  have hc : ∀ i j, ContDiff ℝ ∞ (fun A : E →L[ℝ] E => b.coord i (A (b j))) := fun i j =>
    ((LinearMap.toContinuousLinearMap (b.coord i)).comp
      (ContinuousLinearMap.apply ℝ E (b j))).contDiff
  fun_prop

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The real Jacobian `|det DF|` of the transition `F` from the chart `e` to the chart `f`. -/
def transitionJac (e f : ComplexChart n M) (x : ComplexModel n) : ℝ :=
  |(chartTransitionDerivative e f x).det|

theorem contDiffOn_transitionJac (e f : ComplexChart n M) :
    ContDiffOn ℝ ∞ (transitionJac e f) (chartTransition e f).source := by
  have hF : ContDiffOn ℝ ∞ (chartTransition e f) (chartTransition e f).source := fun y hy =>
    (chartTransition_contDiffAt_real e f hy).contDiffWithinAt
  have hD : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (chartTransition e f) x)
      (chartTransition e f).source :=
    hF.fderiv_of_isOpen (chartTransition e f).open_source (by simp)
  refine (contDiff_det.comp_contDiffOn hD).congr fun x hx => ?_
  simp only [transitionJac, Function.comp_apply]
  exact abs_of_nonneg (GlobalCurrents.chartTransitionDerivative_det_nonneg e f hx)

/-! ### Jacobian-weighted pullback of test functions -/

/-- `x ↦ J(x) ψ(F x)` on the source of the transition `F`, extended by zero. -/
def pullFun (e f : ComplexChart n M) (ψ : ComplexModel n → ℝ) (x : ComplexModel n) : ℝ :=
  open Classical in
  if x ∈ (chartTransition e f).source then transitionJac e f x * ψ (chartTransition e f x)
  else 0

omit [IsComplexManifold n M] in
theorem pullFun_of_mem (e f : ComplexChart n M) (ψ : ComplexModel n → ℝ) {x : ComplexModel n}
    (hx : x ∈ (chartTransition e f).source) :
    pullFun e f ψ x = transitionJac e f x * ψ (chartTransition e f x) := by
  simp [pullFun, hx]

omit [IsComplexManifold n M] in
theorem pullFun_of_notMem (e f : ComplexChart n M) (ψ : ComplexModel n → ℝ) {x : ComplexModel n}
    (hx : x ∉ (chartTransition e f).source) : pullFun e f ψ x = 0 := by
  simp [pullFun, hx]

omit [IsComplexManifold n M] in
theorem image_tsupport_subset_source (e f : ComplexChart n M) {ψ : ComplexModel n → ℝ}
    (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    (chartTransition e f).symm '' tsupport ψ ⊆ (chartTransition e f).source := by
  rintro _ ⟨y, hy, rfl⟩
  exact (chartTransition e f).map_target (hψ hy)

omit [IsComplexManifold n M] in
theorem isCompact_image_tsupport (e f : ComplexChart n M) {ψ : ComplexModel n → ℝ}
    (hψc : HasCompactSupport ψ) (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    IsCompact ((chartTransition e f).symm '' tsupport ψ) :=
  hψc.isCompact.image_of_continuousOn ((chartTransition e f).symm.continuousOn.mono hψ)

omit [IsComplexManifold n M] in
theorem pullFun_eq_zero_of_notMem_image (e f : ComplexChart n M) {ψ : ComplexModel n → ℝ}
    {x : ComplexModel n} (hx : x ∉ (chartTransition e f).symm '' tsupport ψ) :
    pullFun e f ψ x = 0 := by
  by_cases hxs : x ∈ (chartTransition e f).source
  · have : chartTransition e f x ∉ tsupport ψ := fun h =>
      hx ⟨_, h, (chartTransition e f).left_inv hxs⟩
    rw [pullFun_of_mem e f ψ hxs, image_eq_zero_of_notMem_tsupport this, mul_zero]
  · exact pullFun_of_notMem e f ψ hxs

omit [IsComplexManifold n M] in
theorem tsupport_pullFun_subset (e f : ComplexChart n M) {ψ : ComplexModel n → ℝ}
    (hψc : HasCompactSupport ψ) (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    tsupport (pullFun e f ψ) ⊆ (chartTransition e f).symm '' tsupport ψ := by
  refine closure_minimal (fun x hx => ?_) (isCompact_image_tsupport e f hψc hψ).isClosed
  by_contra h
  exact hx (pullFun_eq_zero_of_notMem_image e f h)

theorem contDiff_pullFun (e f : ComplexChart n M) {ψ : ComplexModel n → ℝ}
    (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    ContDiff ℝ ∞ (pullFun e f ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ (chartTransition e f).source
  · have hev : pullFun e f ψ =ᶠ[𝓝 x] fun z => transitionJac e f z * ψ (chartTransition e f z) := by
      filter_upwards [(chartTransition e f).open_source.mem_nhds hx] with z hz
      exact pullFun_of_mem e f ψ hz
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((contDiffOn_transitionJac e f).contDiffAt
      ((chartTransition e f).open_source.mem_nhds hx)).mul
      (hψs.contDiffAt.comp x (chartTransition_contDiffAt_real e f hx))
  · have hxK : x ∉ (chartTransition e f).symm '' tsupport ψ := fun h =>
      hx (image_tsupport_subset_source e f hψ h)
    have hev : pullFun e f ψ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isCompact_image_tsupport e f hψc hψ).isClosed.isOpen_compl.mem_nhds hxK]
        with z hz
      exact pullFun_eq_zero_of_notMem_image e f hz
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The Jacobian-weighted pullback `J · ψ ∘ F` of a test function supported in the target of the
transition `F`, as a test function on any open set containing `F⁻¹(supp ψ)`. -/
def pullTest (e f : ComplexChart n M) {Ωf Ωe : Opens (ComplexModel n)} (ψ : 𝓓(Ωf, ℝ))
    (hψ : tsupport ψ ⊆ (chartTransition e f).target)
    (hΩe : (chartTransition e f).symm '' tsupport ψ ⊆ Ωe) : 𝓓(Ωe, ℝ) :=
  ⟨pullFun e f ψ, contDiff_pullFun e f ψ.contDiff ψ.hasCompactSupport hψ,
    IsCompact.of_isClosed_subset (isCompact_image_tsupport e f ψ.hasCompactSupport hψ)
      (isClosed_tsupport _) (tsupport_pullFun_subset e f ψ.hasCompactSupport hψ),
    (tsupport_pullFun_subset e f ψ.hasCompactSupport hψ).trans hΩe⟩

@[simp] theorem pullTest_apply (e f : ComplexChart n M) {Ωf Ωe : Opens (ComplexModel n)}
    (ψ : 𝓓(Ωf, ℝ)) (hψ : tsupport ψ ⊆ (chartTransition e f).target)
    (hΩe : (chartTransition e f).symm '' tsupport ψ ⊆ Ωe) (x : ComplexModel n) :
    pullTest e f ψ hψ hΩe x = pullFun e f ψ x := rfl

omit [IsComplexManifold n M] in
theorem image_tsupport_subset_chartTarget (e f : ComplexChart n M) {ψ : ComplexModel n → ℝ}
    (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    (chartTransition e f).symm '' tsupport ψ ⊆ (chartTarget e : Set (ComplexModel n)) :=
  fun _ hx => (image_tsupport_subset_source e f hψ hx).1

/-- **Change of variables along a chart transition.** -/
theorem integral_mul_eq_integral_pullFun (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (e f : ComplexChart n M) {ψ : ComplexModel n → ℝ}
    (hψ : tsupport ψ ⊆ (chartTransition e f).target) (h : ComplexModel n → ℝ) :
    ∫ y, ψ y * h y ∂μ = ∫ x, pullFun e f ψ x * h (chartTransition e f x) ∂μ := by
  set F := chartTransition e f with hFdef
  have hderiv : ∀ x ∈ F.source, HasFDerivAt F (chartTransitionDerivative e f x) x := fun x hx =>
    ((chartTransition_contDiffAt_real e f hx).differentiableAt (by simp)).hasFDerivAt
  calc ∫ y, ψ y * h y ∂μ = ∫ y in F.target, ψ y * h y ∂μ := by
        rw [← integral_indicator F.open_target.measurableSet]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ F.target
        · simp [hy]
        · simp [hy, image_eq_zero_of_notMem_tsupport fun h => hy (hψ h)]
    _ = ∫ x in F.source, |(chartTransitionDerivative e f x).det| • (ψ (F x) * h (F x)) ∂μ :=
        integral_target_eq_integral_abs_det_fderiv_smul μ hderiv _
    _ = ∫ x in F.source, pullFun e f ψ x * h (F x) ∂μ := by
        refine setIntegral_congr_fun F.open_source.measurableSet fun x hx => ?_
        rw [pullFun_of_mem e f ψ hx, smul_eq_mul, transitionJac, mul_assoc]
    _ = ∫ x, pullFun e f ψ x * h (F x) ∂μ := by
        rw [← integral_indicator F.open_source.measurableSet]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ F.source
        · simp [hx]
        · simp [hx, pullFun_of_notMem e f ψ hx]

/-! ### Chart limits and their compatibility -/

variable (μ : Measure (ComplexModel n))

/-- `T` is the weak limit along `l` of the chart functions `v i ∘ e⁻¹` of the family `v`. -/
def IsChartLimit {ι : Type*} (l : Filter ι) (v : ι → M → ℝ) (e : ComplexChart n M)
    (T : 𝓓'(chartTarget e, ℝ)) : Prop :=
  ∀ φ : 𝓓(chartTarget e, ℝ),
    Tendsto (fun i => ∫ z, φ z * v i (e.val.symm z) ∂μ) l (𝓝 (T φ))

variable {μ}

omit [IsComplexManifold n M] in
theorem chartTransition_apply_eq (e f : ComplexChart n M) (x : ComplexModel n) :
    chartTransition e f x = f.val (e.val.symm x) := rfl

omit [IsComplexManifold n M] in
theorem symm_chartTransition_apply {e f : ComplexChart n M} {x : ComplexModel n}
    (hx : x ∈ (chartTransition e f).source) :
    f.val.symm (chartTransition e f x) = e.val.symm x :=
  f.val.left_inv hx.2

/-- **Compatibility of chart limits**: `T_f ψ = T_e (J · ψ ∘ F)`. -/
theorem IsChartLimit.apply_pullTest [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} [l.NeBot]
    {v : ι → M → ℝ} {e f : ComplexChart n M} {Te : 𝓓'(chartTarget e, ℝ)}
    {Tf : 𝓓'(chartTarget f, ℝ)} (he : IsChartLimit μ l v e Te) (hf : IsChartLimit μ l v f Tf)
    (ψ : 𝓓(chartTarget f, ℝ)) (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    Tf ψ = Te (pullTest e f ψ hψ (image_tsupport_subset_chartTarget e f hψ)) := by
  refine tendsto_nhds_unique (hf ψ) ((he _).congr fun i => ?_)
  rw [integral_mul_eq_integral_pullFun μ e f hψ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [pullTest_apply]
  by_cases hx : x ∈ (chartTransition e f).source
  · rw [symm_chartTransition_apply hx]
  · simp [pullFun_of_notMem e f _ hx]

omit [IsComplexManifold n M] in
theorem chartTransition_target_eq_source (e f : ComplexChart n M) :
    (chartTransition f e).target = (chartTransition e f).source := by
  ext x
  simp [chartTransition]

omit [IsComplexManifold n M] in
theorem chartTransition_symm_eq (e f : ComplexChart n M) (x : ComplexModel n) :
    (chartTransition f e).symm x = chartTransition e f x := by
  simp [chartTransition]

/-- **Transport of a density.**  If `T_f = g` on an open `W`, then `T_e φ = ∫ φ · g ∘ F` for every
test function `φ` of the chart `e` supported where `F` maps into `W`. -/
theorem IsChartLimit.apply_eq_integral_comp [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι}
    [l.NeBot] {v : ι → M → ℝ} {e f : ComplexChart n M} {Te : 𝓓'(chartTarget e, ℝ)}
    {Tf : 𝓓'(chartTarget f, ℝ)} (he : IsChartLimit μ l v e Te) (hf : IsChartLimit μ l v f Tf)
    {W : Opens (ComplexModel n)} (hW : W ≤ chartTarget f) {g : ComplexModel n → ℝ}
    (hg : LocallyIntegrableOn g W μ) (hTg : restrictDistribution Tf hW = regularDistribution μ g
      hg)
    (φ : 𝓓(chartTarget e, ℝ))
    (hφ : ∀ x ∈ tsupport φ, x ∈ (chartTransition e f).source ∧ chartTransition e f x ∈ W) :
    Te φ = ∫ x, φ x * g (chartTransition e f x) ∂μ := by
  have hφG : tsupport φ ⊆ (chartTransition f e).target := by
    rw [chartTransition_target_eq_source]
    exact fun x hx => (hφ x hx).1
  have himW : (chartTransition f e).symm '' tsupport φ ⊆ (W : Set (ComplexModel n)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [chartTransition_symm_eq]
    exact (hφ x hx).2
  have hcompat := IsChartLimit.apply_pullTest hf he φ hφG
  have hmono : (pullTest f e φ hφG (image_tsupport_subset_chartTarget f e hφG) :
      𝓓(chartTarget f, ℝ)) = TestFunction.monoCLM ℝ (pullTest f e φ hφG himW) := by
    apply TestFunction.ext
    intro y
    rw [congrFun (testFunction_inclusion_coe hW (pullTest f e φ hφG himW)) y]
    simp only [pullTest_apply]
  rw [hcompat, hmono, ← restrictDistribution_apply Tf hW, hTg, regularDistribution_apply,
    integral_mul_eq_integral_pullFun μ f e hφG (fun x => g (chartTransition e f x))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [pullTest_apply]
  by_cases hy : y ∈ (chartTransition f e).source
  · congr 2
    rw [chartTransition_apply_eq e f, symm_chartTransition_apply hy, f.val.right_inv hy.1]
  · simp [pullFun_of_notMem f e _ hy]

/-! ### Local plurisubharmonic representatives and their identification -/

/-- Local potentials of `θ` transport along chart transitions. -/
theorem isSmoothLocalPotential_comp_transition {θ : SmoothRealForm n M 2} (e d : ComplexChart n M)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ d W ρ) :
    IsSmoothLocalPotential θ e ((chartTransition e d).source ∩ chartTransition e d ⁻¹' W)
      (ρ ∘ chartTransition e d) :=
  (SmoothRealForm.pullback_id_geometricallyEq θ).localPotential_iff e _ _ |>.mp
    (LocalPotentialPullback.isSmoothLocalPotential_pullback contMDiff_id e hρ)

/-- A psh function of the chart `d`, corrected by a local potential of `θ` there, transports to a
psh function of the chart `e` corrected by a local potential of `θ` in `e`. -/
theorem plurisubharmonicOn_transport {θ : SmoothRealForm n M 2} (e d : ComplexChart n M)
    {Wd : Set (ComplexModel n)} {ρd : ComplexModel n → ℝ} (hρd : IsSmoothLocalPotential θ d Wd ρd)
    {ud : ComplexModel n → EReal} (hud : PlurisubharmonicOn ud Wd)
    {B : Set (ComplexModel n)} (hB : IsOpen B)
    (hBF : ∀ y ∈ B, y ∈ (chartTransition e d).source ∧ chartTransition e d y ∈ Wd)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ e B ρ) :
    PlurisubharmonicOn (fun y => ud (chartTransition e d y) +
      ((-ρd (chartTransition e d y) : ℝ) : EReal) + (ρ y : EReal)) B := by
  set F := chartTransition e d with hFdef
  have hF : DifferentiableOn ℂ F B := fun y hy =>
    ((chartTransition_contDiffAt e d (hBF y hy).1).differentiableAt
      (by simp)).differentiableWithinAt
  have h1 : PlurisubharmonicOn (fun y => ud (F y)) B :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hB hF (fun y hy => (hBF y hy).2) hud
  have hpot : IsSmoothLocalPotential θ e B (ρd ∘ F) :=
    (isSmoothLocalPotential_comp_transition e d hρd).mono hB fun y hy => hBF y hy
  refine (smoothLocalPotential_psh_iff θ e B (ρd ∘ F) ρ hpot hρ
    (fun y => ud (F y) + ((-ρd (F y) : ℝ) : EReal))).mp ?_
  simpa only [Function.comp_apply, ereal_add_coe_neg_add_coe] using h1

variable (μ)

/-- A local plurisubharmonic representative of `T_e + ρ` near a point of the chart `e`, `ρ` a
smooth local potential of `θ`. -/
structure LocalRep (θ : SmoothRealForm n M 2) (e : ComplexChart n M) (Te : 𝓓'(chartTarget e, ℝ))
    where
  /-- The open set. -/
  W : Opens (ComplexModel n)
  hW : W ≤ chartTarget e
  /-- The local potential. -/
  ρ : ComplexModel n → ℝ
  hρi : LocallyIntegrableOn ρ W μ
  pot : IsSmoothLocalPotential θ e W ρ
  /-- The psh representative. -/
  u : ComplexModel n → EReal
  rep : IsPshRepresentative μ (restrictDistribution Te hW + regularDistribution μ ρ hρi) u

variable {μ}

/-- The chart distribution `T_e` on the domain of a local representative is `u - ρ`. -/
theorem LocalRep.restrict_eq {θ : SmoothRealForm n M 2}
    {e : ComplexChart n M} {Te : 𝓓'(chartTarget e, ℝ)} (R : LocalRep μ θ e Te) :
    restrictDistribution Te R.hW = regularDistribution μ (fun z => (R.u z).toReal - R.ρ z)
      (R.rep.2.2.1.sub R.hρi) := by
  rw [regularDistribution_sub R.rep.2.2.1 R.hρi]
  obtain ⟨_, _, hloc, heq⟩ := R.rep
  have : regularDistribution μ (fun z => (R.u z).toReal) R.rep.2.2.1 =
      regularDistribution μ (fun z => (R.u z).toReal) hloc := rfl
  rw [this, ← heq]
  abel

/-- **Identification of local representatives in two charts.** -/
theorem LocalRep.eq_transport [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} [l.NeBot]
    {v : ι → M → ℝ} {θ : SmoothRealForm n M 2} {e d : ComplexChart n M}
    {Te : 𝓓'(chartTarget e, ℝ)} {Td : 𝓓'(chartTarget d, ℝ)}
    (he : IsChartLimit μ l v e Te) (hd : IsChartLimit μ l v d Td)
    (R : LocalRep μ θ e Te) (S : LocalRep μ θ d Td) {y : ComplexModel n} (hyR : y ∈ R.W)
    (hyF : y ∈ (chartTransition e d).source) (hFy : chartTransition e d y ∈ S.W) :
    R.u y = S.u (chartTransition e d y) + ((-S.ρ (chartTransition e d y) : ℝ) : EReal) +
      (R.ρ y : EReal) := by
  set F := chartTransition e d with hFdef
  -- a ball around `y` where everything is defined
  have hO : IsOpen ((R.W : Set (ComplexModel n)) ∩ (F.source ∩ F ⁻¹' S.W)) :=
    R.W.isOpen.inter (F.continuousOn.isOpen_inter_preimage F.open_source S.W.isOpen)
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y ⟨hyR, hyF, hFy⟩
  let B : Opens (ComplexModel n) := ⟨ball y r, isOpen_ball⟩
  have hBR : B ≤ R.W := fun z hz => (hrO hz).1
  have hBF : ∀ z ∈ (B : Set (ComplexModel n)), z ∈ F.source ∧ F z ∈ S.W := fun z hz =>
    (hrO hz).2
  have hBe : B ≤ chartTarget e := hBR.trans R.hW
  have hBpre : IsPreconnected (B : Set (ComplexModel n)) := (convex_ball y r).isPreconnected
  have hyB : y ∈ B := mem_ball_self hr
  -- the transported function
  set g₂ : ComplexModel n → EReal := fun z => S.u (F z) + ((-S.ρ (F z) : ℝ) : EReal) +
    (R.ρ z : EReal) with hg₂def
  have hpotB : IsSmoothLocalPotential θ e B R.ρ := R.pot.mono isOpen_ball hBR
  have hg₂ : PlurisubharmonicOn g₂ B :=
    plurisubharmonicOn_transport e d S.pot S.rep.1 isOpen_ball hBF hpotB
  have hF : DifferentiableOn ℂ F B := fun z hz =>
    ((chartTransition_contDiffAt e d (hBF z hz).1).differentiableAt
      (by simp)).differentiableWithinAt
  have hSuF : PlurisubharmonicOn (fun z => S.u (F z)) B :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_ball hF
      (fun z hz => (hBF z hz).2) S.rep.1
  -- `S.u ∘ F` is not identically `-∞` on `B`
  have hne : ∃ z ∈ (B : Set (ComplexModel n)), S.u (F z) ≠ ⊥ := by
    have hsub : F '' B ⊆ S.W := by rintro _ ⟨z, hz, rfl⟩; exact (hBF z hz).2
    have hopen : IsOpen (F '' B) :=
      F.isOpen_image_of_subset_source isOpen_ball fun z hz => (hBF z hz).1
    have hpos : μ.restrict S.W (F '' B) ≠ 0 := by
      rw [Measure.restrict_apply' S.W.isOpen.measurableSet, inter_eq_left.mpr hsub]
      exact (hopen.measure_pos μ ⟨F y, y, hyB, rfl⟩).ne'
    obtain ⟨_, ⟨z, hz, rfl⟩, hfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae S.rep.2.1)
    exact ⟨z, hz, hfin.2⟩
  obtain ⟨z₀, hz₀, hz₀ne⟩ := hne
  have hSuF_fin := hSuF.ae_finite μ hBpre ⟨z₀, hz₀, hz₀ne⟩
  have hSuF_loc := hSuF.locallyIntegrableOn_toReal μ hBpre ⟨z₀, hz₀, hz₀ne⟩
  have hg₂ne : ∃ a ∈ (B : Set (ComplexModel n)), g₂ a ≠ ⊥ := by
    refine ⟨z₀, hz₀, ?_⟩
    simp only [hg₂def]
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.add_ne_bot_iff.mpr ⟨hz₀ne, EReal.coe_ne_bot _⟩,
      EReal.coe_ne_bot _⟩
  have hg₂fin := hg₂.ae_finite μ hBpre hg₂ne
  have hg₂loc := hg₂.locallyIntegrableOn_toReal μ hBpre hg₂ne
  -- the density `k = (S.u - S.ρ) ∘ F` of `T_e` on `B`
  have hρScont : ContinuousOn (fun z => S.ρ (F z)) B :=
    S.pot.2.2.1.continuousOn.comp (F.continuousOn.mono fun z hz => (hBF z hz).1)
      fun z hz => (hBF z hz).2
  have hk : LocallyIntegrableOn (fun z => (S.u (F z)).toReal - S.ρ (F z)) B μ :=
    hSuF_loc.sub (hρScont.locallyIntegrableOn isOpen_ball.measurableSet)
  have hρR : LocallyIntegrableOn R.ρ B μ := R.hρi.mono_set hBR
  have hTe : restrictDistribution Te hBe =
      regularDistribution μ (fun z => (S.u (F z)).toReal - S.ρ (F z)) hk := by
    ext φ
    rw [restrictDistribution_apply, regularDistribution_apply]
    refine (IsChartLimit.apply_eq_integral_comp he hd S.hW (S.rep.2.2.1.sub S.hρi)
      S.restrict_eq _ fun x hx => ?_).trans ?_
    · have hxB : x ∈ (B : Set (ComplexModel n)) := by
        have := (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)).tsupport_subset
        rw [show ((TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) : ComplexModel n → ℝ) = φ
          from testFunction_inclusion_coe hBe φ] at hx
        exact φ.tsupport_subset hx
      exact hBF x hxB
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      rw [congrFun (testFunction_inclusion_coe hBe φ) x]
  -- both `R.u` and `g₂` represent `T_e + R.ρ` on `B`
  have hRrep := R.rep.restrict μ hBR
  rw [restrictDistribution_add, restrictDistribution_trans,
    restrictDistribution_regularDistribution μ R.hρi hBR, hTe,
    ← regularDistribution_add hk hρR] at hRrep
  have hg₂rep : IsPshRepresentative μ (regularDistribution μ
      (fun z => (S.u (F z)).toReal - S.ρ (F z) + R.ρ z) (hk.add hρR)) g₂ := by
    refine ⟨hg₂, hg₂fin, hg₂loc, regularDistribution_congr_ae_on _ _ ?_⟩
    filter_upwards [hSuF_fin] with z hz
    simp only [hg₂def]
    rw [ereal_toReal_add_coe (ereal_add_coe_finite hz _), ereal_toReal_add_coe hz]
    ring
  exact hRrep.unique hg₂rep hyB

/-! ### Gluing -/

variable (μ)

/-- **`T_e` is locally `θ`-psh as a distribution**: near every point of the chart there are an
open set `W` and a smooth local potential `ρ` of `θ` on `W` such that `T_e + ρ` has nonnegative
distributional Levi form on `W`. -/
def IsLocallyThetaPshDistribution (θ : SmoothRealForm n M 2) (e : ComplexChart n M)
    (Te : 𝓓'(chartTarget e, ℝ)) : Prop :=
  ∀ z ∈ e.val.target, ∃ (W : Opens (ComplexModel n)) (hW : W ≤ chartTarget e)
    (ρ : ComplexModel n → ℝ) (hρ : LocallyIntegrableOn ρ W μ), z ∈ W ∧
      IsSmoothLocalPotential θ e W ρ ∧
      HasNonnegativeDistributionalLevi (restrictDistribution Te hW + regularDistribution μ ρ hρ)

variable {μ}

/-- Local representatives exist (CADG I.5.8, `Pending.exists_pshRepresentative`). -/
theorem IsLocallyThetaPshDistribution.exists_localRep [μ.IsAddHaarMeasure]
    {θ : SmoothRealForm n M 2} {e : ComplexChart n M} {Te : 𝓓'(chartTarget e, ℝ)}
    (h : IsLocallyThetaPshDistribution μ θ e Te) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ R : LocalRep μ θ e Te, z ∈ R.W := by
  obtain ⟨W, hW, ρ, hρ, hzW, hpot, hL⟩ := h z hz
  obtain ⟨u, hu⟩ := exists_pshRepresentative μ hL
  exact ⟨⟨W, hW, ρ, hρ, hpot, u, hu⟩, hzW⟩

/-- **Gluing of chart weak limits into a `θ`-psh potential** (F6, piece (i-4')).  If the chart
functions of `v_i` converge weakly in every chart along a nontrivial filter, and every chart limit
is locally `θ`-psh as a distribution, then there is a `θ`-psh potential `V`, finite almost
everywhere in every chart, whose chart functions represent every chart limit. -/
theorem exists_isThetaPshPotential_of_isChartLimit [μ.IsAddHaarMeasure] {ι : Type*}
    {l : Filter ι} [l.NeBot] (v : ι → M → ℝ) {θ : SmoothRealForm n M 2}
    (T : ∀ e : ComplexChart n M, 𝓓'(chartTarget e, ℝ))
    (hT : ∀ e, IsChartLimit μ l v e (T e))
    (hLevi : ∀ e, IsLocallyThetaPshDistribution μ θ e (T e)) :
    ∃ V : M → EReal, IsThetaPshPotential θ V ∧ ∀ e : ComplexChart n M,
      (∀ᵐ z ∂μ.restrict (chartTarget e), chartFunction V e z ≠ ⊤ ∧ chartFunction V e z ≠ ⊥) ∧
      ∃ hV : LocallyIntegrableOn (fun z => (chartFunction V e z).toReal) (chartTarget e) μ,
        T e = regularDistribution μ (fun z => (chartFunction V e z).toReal) hV := by
  classical
  have hrep : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∃ R : LocalRep μ θ e (T e), z ∈ R.W := fun e _ hz => (hLevi e).exists_localRep hz
  choose R hR using hrep
  have hx : ∀ x : M, (complexChartAt (n := n) x).val x ∈ (complexChartAt (n := n) x).val.target :=
    fun x => (complexChartAt x).val.map_source (mem_complexChartAt_source x)
  -- the preferred local representative at `x`
  let P : ∀ x : M, LocalRep μ θ (complexChartAt (n := n) x) (T (complexChartAt x)) := fun x =>
    R (complexChartAt x) ((complexChartAt x).val x) (hx x)
  let V : M → EReal := fun x =>
    (P x).u ((complexChartAt (n := n) x).val x) +
      ((-(P x).ρ ((complexChartAt (n := n) x).val x) : ℝ) : EReal)
  -- every local representative in every chart is `V ∘ e⁻¹ + ρ`
  have hkey : ∀ (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target),
      ∀ y ∈ (R e z hz).W, chartFunction V e y + ((R e z hz).ρ y : EReal) = (R e z hz).u y := by
    intro e z hz y hy
    have hyF : y ∈ (chartTransition e (complexChartAt (n := n) (e.val.symm y))).source :=
      ⟨(R e z hz).hW hy, mem_complexChartAt_source _⟩
    have hFyW : chartTransition e (complexChartAt (n := n) (e.val.symm y)) y ∈
        (P (e.val.symm y)).W := hR _ _ (hx _)
    rw [LocalRep.eq_transport (hT e) (hT _) (R e z hz) (P (e.val.symm y)) hy hyF hFyW]
    rfl
  have hpsh : ThetaPlurisubharmonic θ V := by
    intro e z hz
    refine ⟨(R e z hz).W, (R e z hz).ρ, hR e z hz, (R e z hz).pot, fun y hy => ?_⟩
    refine ((R e z hz).rep.1 y hy).congr ?_
    filter_upwards [(R e z hz).W.isOpen.mem_nhds hy] with w hw
    exact (hkey e z hz w hw).symm
  have hchart : ∀ e : ComplexChart n M,
      (∀ᵐ z ∂μ.restrict (chartTarget e), chartFunction V e z ≠ ⊤ ∧ chartFunction V e z ≠ ⊥) ∧
      ∃ hV : LocallyIntegrableOn (fun z => (chartFunction V e z).toReal) (chartTarget e) μ,
        T e = regularDistribution μ (fun z => (chartFunction V e z).toReal) hV := by
    intro e
    have heq : ∀ z (hz : z ∈ e.val.target), ∀ y ∈ (R e z hz).W,
        chartFunction V e y = (R e z hz).u y + ((-(R e z hz).ρ y : ℝ) : EReal) :=
      fun z hz y hy => ereal_eq_add_coe_neg_of_add_coe_eq (hkey e z hz y hy)
    have hfinW : ∀ z (hz : z ∈ e.val.target), ∀ᵐ y ∂μ.restrict (R e z hz).W,
        chartFunction V e y ≠ ⊤ ∧ chartFunction V e y ≠ ⊥ := by
      intro z hz
      filter_upwards [(R e z hz).rep.2.1,
        ae_restrict_mem (R e z hz).W.isOpen.measurableSet] with y hy hyW
      rw [heq z hz y hyW]
      exact ereal_add_coe_finite hy _
    have htoReal : ∀ z (hz : z ∈ e.val.target),
        (fun y => ((R e z hz).u y).toReal - (R e z hz).ρ y) =ᵐ[μ.restrict (R e z hz).W]
          fun y => (chartFunction V e y).toReal := by
      intro z hz
      filter_upwards [(R e z hz).rep.2.1,
        ae_restrict_mem (R e z hz).W.isOpen.measurableSet] with y hy hyW
      rw [heq z hz y hyW, ereal_toReal_add_coe hy]
      ring
    have hloc : LocallyIntegrableOn (fun z => (chartFunction V e z).toReal) (chartTarget e) μ := by
      intro z hz
      have hlocW : LocallyIntegrableOn (fun y => (chartFunction V e y).toReal)
          (R e z hz).W μ :=
        ((R e z hz).rep.2.2.1.sub (R e z hz).hρi).congr (htoReal z hz)
      have h1 := hlocW z (hR e z hz)
      rw [(R e z hz).W.isOpen.nhdsWithin_eq (hR e z hz)] at h1
      rw [(chartTarget e).isOpen.nhdsWithin_eq hz]
      exact h1
    refine ⟨ae_restrict_of_open_neighborhood_ae fun z hz =>
      ⟨(R e z hz).W, (R e z hz).W.isOpen, hR e z hz, hfinW z hz⟩, hloc, ?_⟩
    apply distribution_eq_of_restrict_eq
      (fun p : (chartTarget e : Set (ComplexModel n)) => (R e p.1 p.2).W)
      (fun p => (R e p.1 p.2).hW)
    · intro z hz
      exact ⟨⟨z, hz⟩, hR e z hz⟩
    · intro p
      rw [(R e p.1 p.2).restrict_eq, restrictDistribution_regularDistribution μ hloc]
      exact regularDistribution_congr_ae_on _ _ (htoReal p.1 p.2)
  have hnd : LocallyNondegenerate V := by
    intro x U hU hxU
    set d := complexChartAt (n := n) x with hddef
    have hO : IsOpen (d.val '' (d.val.source ∩ U)) := d.val.isOpen_image_source_inter hU
    have hsub : d.val '' (d.val.source ∩ U) ⊆ (chartTarget d : Set (ComplexModel n)) := by
      rintro _ ⟨y, hy, rfl⟩
      exact d.val.map_source hy.1
    have hpos : μ.restrict (chartTarget d) (d.val '' (d.val.source ∩ U)) ≠ 0 := by
      rw [Measure.restrict_apply' (chartTarget d).isOpen.measurableSet, inter_eq_left.mpr hsub]
      exact (hO.measure_pos μ ⟨d.val x, x, ⟨mem_complexChartAt_source x, hxU⟩, rfl⟩).ne'
    obtain ⟨_, ⟨y, hy, rfl⟩, hfin⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hchart d).1)
    refine ⟨y, hy.2, ?_⟩
    have hVy : chartFunction V d (d.val y) = V y := by
      simp only [chartFunction, d.val.left_inv hy.1]
    rw [← hVy]
    exact hfin.2
  exact ⟨V, ⟨hpsh, hnd⟩, hchart⟩

omit [IsComplexManifold n M] in
/-- **Chart limits along an ultrafilter** from uniform `L¹` bounds on compact subsets of the
charts (`PshUltrafilterLimit.exists_tendsto_regularDistribution`). -/
theorem exists_isChartLimit {ι : Type*} (U : Ultrafilter ι) (v : ι → M → ℝ)
    (hloc : ∀ i (e : ComplexChart n M),
      LocallyIntegrableOn (fun z => v i (e.val.symm z)) (chartTarget e) μ)
    (hbound : ∀ (e : ComplexChart n M) (K : Set (ComplexModel n)), IsCompact K →
      K ⊆ e.val.target → ∃ B : ℝ, ∀ i, ∫ z in K, |v i (e.val.symm z)| ∂μ ≤ B) :
    ∃ T : ∀ e : ComplexChart n M, 𝓓'(chartTarget e, ℝ),
      ∀ e, IsChartLimit μ (U : Filter ι) v e (T e) := by
  have h : ∀ e : ComplexChart n M, ∃ T : 𝓓'(chartTarget e, ℝ),
      IsChartLimit μ (U : Filter ι) v e T := by
    intro e
    obtain ⟨T, hT⟩ := PshUltrafilterLimit.exists_tendsto_regularDistribution μ U
      (fun i z => v i (e.val.symm z)) (fun i => hloc i e) fun K hK hKe => hbound e K hK hKe
    exact ⟨T, fun φ => by simpa only [regularDistribution_apply] using hT φ⟩
  choose T hT using h
  exact ⟨T, hT⟩

/-- **A Kähler current from chart weak limits** (the form in which F6 ends, `KahlerCurrent`).  If
the chart limits of `v_i` are locally `(θ₀ - ω_δ)`-psh as distributions, the class of `θ₀` contains
a Kähler current with representative `θ₀` and lower bound `ω_δ`, whose potential represents every
chart limit. -/
theorem exists_kahlerCurrent_of_isChartLimit [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι}
    [l.NeBot] (v : ι → M → ℝ) (θ₀ : ClosedRealOneOneForm n M) (ωδ :
      PositiveClasses.KahlerBackground n M)
    (T : ∀ e : ComplexChart n M, 𝓓'(chartTarget e, ℝ))
    (hT : ∀ e, IsChartLimit μ l v e (T e))
    (hLevi : ∀ e, IsLocallyThetaPshDistribution μ (θ₀ - ωδ.form).val e (T e)) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative θ₀),
      K.representative = θ₀ ∧ K.lowerBound = ωδ ∧ ∀ e : ComplexChart n M,
        ∃ hV : LocallyIntegrableOn (fun z => (chartFunction K.potential e z).toReal)
          (chartTarget e) μ,
          T e = regularDistribution μ (fun z => (chartFunction K.potential e z).toReal) hV := by
  obtain ⟨V, hV, hrep⟩ := exists_isThetaPshPotential_of_isChartLimit v T hT hLevi
  exact ⟨⟨θ₀, rfl, V, ωδ, hV⟩, rfl, rfl, fun e => (hrep e).2⟩

end

end SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
