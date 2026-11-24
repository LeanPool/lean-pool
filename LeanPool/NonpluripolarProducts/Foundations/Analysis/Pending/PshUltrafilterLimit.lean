/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshRepresentative
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularDistribution

/-!
# Weak limits of locally `L¹`-bounded plurisubharmonic functions

Source: Demailly, CADG I.4 (weak compactness of locally bounded families of distributions,
I.4.18--4.21) and I.5.8 (a distribution with nonnegative Levi form is a plurisubharmonic
function, `Pending.PshRepresentative`).  TN.4 plan, step B6, finding F6 route (i)
: the normalized potentials `v_ε` of the currents
`R_ε` have a weak limit, chart by chart, and that limit is again (represented by) a
plurisubharmonic function.

* `exists_tendsto_regularDistribution` — on an open set `Ω` of a finite-dimensional space, a family
  of locally integrable functions `f i` with uniformly bounded integrals of `|f i|` over every
  compact `K ⊆ Ω` has, along any ultrafilter, a limit distribution `T`:
  `∫ φ f i dμ → T φ` for every test function `φ`.  No Hartogs-type convergence theorem is used:
  bounded real sequences converge along ultrafilters, and the limit functional is continuous on
  each `𝓓_K` because `|T φ| ≤ B_K ‖φ‖_∞`.
* `HasNonnegativeDistributionalLevi.of_tendsto` — nonnegativity of the Levi form passes to weak
  limits.
* `exists_isPshRepresentative_of_tendsto` — **weak compactness of plurisubharmonic functions**:
  if the `w i` are plurisubharmonic on a preconnected `Ω`, not identically `-∞`, with uniformly
  bounded `∫_K |w i|`, their regular distributions converge along the ultrafilter to a
  distribution with a plurisubharmonic representative.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions BoundedContinuousFunction

namespace SGPT.Foundations.Analysis.Pending.PshUltrafilterLimit

noncomputable section

section Limit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] (μ : Measure E) {Ω : Opens E}

/-- The sup norm of a test function. -/
def supNorm (φ : 𝓓(Ω, ℝ)) : ℝ := ‖TestFunction.toBoundedContinuousFunctionCLM ℝ φ‖

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem abs_apply_le_supNorm (φ : 𝓓(Ω, ℝ)) (x : E) : |φ x| ≤ supNorm φ := by
  have := (TestFunction.toBoundedContinuousFunctionCLM ℝ φ).norm_coe_le_norm x
  simpa [supNorm, Real.norm_eq_abs] using this

omit [OpensMeasurableSpace E] in
/-- **The pairing with a locally integrable function is bounded by the sup norm** times the
`L¹` norm over any compact `K ⊆ Ω` containing the support. -/
theorem abs_integral_le {f : E → ℝ} (hf : LocallyIntegrableOn f Ω μ) (φ : 𝓓(Ω, ℝ)) {K : Set E}
    (hKc : IsCompact K) (hKΩ : K ⊆ Ω) (hK : tsupport φ ⊆ K) :
    |∫ x, φ x * f x ∂μ| ≤ supNorm φ * ∫ x in K, |f x| ∂μ := by
  have hint : IntegrableOn f K μ := hf.integrableOn_compact_subset hKΩ hKc
  have hzero : ∀ x ∉ K, φ x * f x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hK h)), zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc |∫ x in K, φ x * f x ∂μ| ≤ ∫ x in K, |φ x * f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x in K, supNorm φ * |f x| ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hint.abs.const_mul _) (Eventually.of_forall fun x => ?_)
        change |φ x * f x| ≤ supNorm φ * |f x|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_apply_le_supNorm φ x) (abs_nonneg _)
    _ = supNorm φ * ∫ x in K, |f x| ∂μ := integral_const_mul _ _

variable {ι : Type*} (U : Ultrafilter ι)

/-- **Limits of locally `L¹`-bounded families of functions, as distributions.**  Along any
ultrafilter, a family of locally integrable functions with uniformly bounded `∫_K |f i|` on every
compact `K ⊆ Ω` has a limit distribution. -/
theorem exists_tendsto_regularDistribution (f : ι → E → ℝ)
    (hf : ∀ i, LocallyIntegrableOn (f i) Ω μ)
    (hbound : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ B : ℝ, ∀ i, ∫ x in K, |f i x| ∂μ ≤ B) :
    ∃ T : 𝓓'(Ω, ℝ), ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => regularDistribution μ (f i) (hf i) φ) U (𝓝 (T φ)) := by
  set a : 𝓓(Ω, ℝ) → ι → ℝ := fun φ i => regularDistribution μ (f i) (hf i) φ with ha
  -- uniform bounds on the values, from a compact containing the support
  have hbd : ∀ (φ : 𝓓(Ω, ℝ)) (K : Set E), IsCompact K → K ⊆ Ω → tsupport φ ⊆ K →
      ∀ B : ℝ, (∀ i, ∫ x in K, |f i x| ∂μ ≤ B) → ∀ i, |a φ i| ≤ supNorm φ * B := by
    intro φ K hKc hKΩ hK B hB i
    change |regularDistribution μ (f i) (hf i) φ| ≤ _
    rw [regularDistribution_apply]
    exact (abs_integral_le μ (hf i) φ hKc hKΩ hK).trans
      (mul_le_mul_of_nonneg_left (hB i) (norm_nonneg _))
  have hlim : ∀ φ : 𝓓(Ω, ℝ), ∃ y : ℝ, Tendsto (a φ) U (𝓝 y) := by
    intro φ
    obtain ⟨B, hB⟩ := hbound (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
    set R := supNorm φ * B
    have hmem : ∀ i, a φ i ∈ Icc (-R) R := fun i =>
      abs_le.mp (hbd φ _ φ.hasCompactSupport φ.tsupport_subset subset_rfl B hB i)
    obtain ⟨y, -, hy⟩ := (isCompact_Icc (a := -R) (b := R)).ultrafilter_le_nhds (U.map (a φ))
      (by
        rw [Ultrafilter.coe_map, le_principal_iff]
        exact Filter.mem_map.mpr (Filter.univ_mem' fun i => hmem i))
    exact ⟨y, by rwa [Ultrafilter.coe_map] at hy⟩
  choose T₀ hT₀ using hlim
  have hadd : ∀ φ ψ, T₀ (φ + ψ) = T₀ φ + T₀ ψ := by
    intro φ ψ
    refine tendsto_nhds_unique (hT₀ (φ + ψ)) ?_
    have : a (φ + ψ) = fun i => a φ i + a ψ i := by
      funext i; simp [ha, map_add]
    rw [this]
    exact (hT₀ φ).add (hT₀ ψ)
  have hsmul : ∀ (c : ℝ) φ, T₀ (c • φ) = c • T₀ φ := by
    intro c φ
    refine tendsto_nhds_unique (hT₀ (c • φ)) ?_
    have : a (c • φ) = fun i => c * a φ i := by
      funext i; simp [ha, map_smul]
    rw [this, smul_eq_mul]
    exact (hT₀ φ).const_mul c
  let Tlin : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ := ⟨⟨T₀, hadd⟩, hsmul⟩
  have hcont : ∀ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
      Continuous (T₀ ∘ TestFunction.ofSupportedIn K_sub_Ω) := by
    intro K hKΩ
    obtain ⟨B, hB⟩ := hbound K K.isCompact hKΩ
    set L : ContDiffMapSupportedIn E ℝ ⊤ K →ₗ[ℝ] ℝ :=
      Tlin.comp (TestFunction.ofSupportedInCLM ℝ hKΩ : _ →L[ℝ] 𝓓(Ω, ℝ)).toLinearMap with hL
    have hLapp : ∀ g, L g = T₀ (TestFunction.ofSupportedIn hKΩ g) := fun _ => rfl
    have hbT : ∀ g, |L g| ≤ supNorm (TestFunction.ofSupportedIn hKΩ g) * B := by
      intro g
      rw [hLapp]
      have hsupp : tsupport (TestFunction.ofSupportedIn hKΩ g : E → ℝ) ⊆ K :=
        g.tsupport_subset
      exact le_of_tendsto (((continuous_abs.tendsto _).comp (hT₀ _)))
        (Eventually.of_forall fun i =>
          hbd _ K K.isCompact hKΩ hsupp B hB i)
    have hsn : Continuous fun g : ContDiffMapSupportedIn E ℝ ⊤ K =>
        supNorm (TestFunction.ofSupportedIn hKΩ g) :=
      continuous_norm.comp ((TestFunction.toBoundedContinuousFunctionCLM ℝ).continuous.comp
        (TestFunction.ofSupportedInCLM ℝ hKΩ).continuous)
    have h0 : supNorm (TestFunction.ofSupportedIn hKΩ (0 : ContDiffMapSupportedIn E ℝ ⊤ K))
      = 0 := by
      have : TestFunction.ofSupportedIn hKΩ (0 : ContDiffMapSupportedIn E ℝ ⊤ K) = 0 :=
        map_zero (TestFunction.ofSupportedInCLM ℝ hKΩ)
      rw [this, supNorm, map_zero, norm_zero]
    have hL : Continuous L := by
      refine continuous_of_continuousAt_zero L ?_
      rw [ContinuousAt, map_zero]
      refine squeeze_zero_norm (fun g => ?_) (?_ : Tendsto (fun g => supNorm
        (TestFunction.ofSupportedIn hKΩ g) * |B|) (𝓝 0) (𝓝 0))
      · rw [Real.norm_eq_abs]
        refine (hbT g).trans (mul_le_mul_of_nonneg_left (le_abs_self B) (norm_nonneg _))
      · have := (hsn.tendsto 0).mul_const |B|
        rwa [h0, zero_mul] at this
    exact hL
  refine ⟨TestFunction.mkCLM ℝ T₀ hadd hsmul hcont, fun φ => ?_⟩
  exact hT₀ φ

end Limit

section Levi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] {Ω : Opens E}

/-- The Levi form of a weak limit is the limit of the Levi forms. -/
theorem tendsto_distributionalLeviCLM {ι : Type*} {l : Filter ι} {S : ι → 𝓓'(Ω, ℝ)}
    {T : 𝓓'(Ω, ℝ)} (h : ∀ φ, Tendsto (fun i => S i φ) l (𝓝 (T φ))) (v : E) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun i => distributionalLeviCLM v (S i) φ) l (𝓝 (distributionalLeviCLM v T φ)) := by
  simp only [distributionalLeviCLM_apply]
  exact ((h _).add (h _)).const_mul _

/-- **Nonnegativity of the Levi form passes to weak limits.** -/
theorem HasNonnegativeDistributionalLevi.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {S : ι → 𝓓'(Ω, ℝ)} {T : 𝓓'(Ω, ℝ)} (h : ∀ φ, Tendsto (fun i => S i φ) l (𝓝 (T φ)))
    (hS : ∀ᶠ i in l, HasNonnegativeDistributionalLevi (S i)) :
    HasNonnegativeDistributionalLevi T := fun v φ hφ =>
  ge_of_tendsto (tendsto_distributionalLeviCLM h v φ) (hS.mono fun _ hi => hi v φ hφ)

end Levi

section Psh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- A plurisubharmonic function, not identically `-∞` on the preconnected `Ω`, represents its own
regular distribution. -/
theorem isPshRepresentative_pshRegularDistribution (hΩ : IsPreconnected (Ω : Set E))
    {w : E → EReal} (hw : PlurisubharmonicOn w Ω) (hne : ∃ a ∈ Ω, w a ≠ ⊥) :
    IsPshRepresentative μ (pshRegularDistribution hw μ hΩ hne) w :=
  ⟨hw, hw.ae_finite μ hΩ hne, hw.locallyIntegrableOn_toReal μ hΩ hne, rfl⟩

/-- **Weak compactness of plurisubharmonic functions** (CADG I.4, I.5.8).  Along any ultrafilter,
plurisubharmonic functions `w i` on a preconnected open `Ω`, none identically `-∞`, with uniformly
bounded `∫_K |w i|` on every compact `K ⊆ Ω`, have regular distributions converging to a
distribution `T` which has a plurisubharmonic representative `u`. -/
theorem exists_isPshRepresentative_of_tendsto (hΩ : IsPreconnected (Ω : Set E)) {ι : Type*}
    (U : Ultrafilter ι) (w : ι → E → EReal) (hw : ∀ i, PlurisubharmonicOn (w i) Ω)
    (hne : ∀ i, ∃ a ∈ Ω, w i a ≠ ⊥)
    (hbound : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      ∃ B : ℝ, ∀ i, ∫ x in K, |(w i x).toReal| ∂μ ≤ B) :
    ∃ (T : 𝓓'(Ω, ℝ)) (u : E → EReal), IsPshRepresentative μ T u ∧
      ∀ φ : 𝓓(Ω, ℝ),
        Tendsto (fun i => pshRegularDistribution (hw i) μ hΩ (hne i) φ) U (𝓝 (T φ)) := by
  obtain ⟨T, hT⟩ := exists_tendsto_regularDistribution μ U (fun i x => (w i x).toReal)
    (fun i => (hw i).locallyIntegrableOn_toReal μ hΩ (hne i)) hbound
  have hLevi : HasNonnegativeDistributionalLevi T :=
    HasNonnegativeDistributionalLevi.of_tendsto hT (Eventually.of_forall fun i =>
      (isPshRepresentative_pshRegularDistribution μ hΩ (hw i) (hne
        i)).hasNonnegativeDistributionalLevi)
  obtain ⟨u, hu⟩ := exists_pshRepresentative μ hLevi
  exact ⟨T, u, hu, hT⟩

end Psh

end

end SGPT.Foundations.Analysis.Pending.PshUltrafilterLimit
