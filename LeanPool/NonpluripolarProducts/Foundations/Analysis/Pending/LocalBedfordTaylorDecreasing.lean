/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscLipschitzMajorants
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LocalPshDiscControl

/-!
# Continuity of the recursive Bedford--Taylor product under decreasing sequences

On an open `U ⊆ ℂⁿ`, for the currents of `Pending.LocalProductCurrents` and the recursive product
`B(u₁, …, u_q; T)` of `Pending.LocalBedfordTaylorProducts` (`bt:decreasing-continuity`,
`demailly-cadg:III.3.7`, `demailly-cadg:III.3.9`):

* `eventually_integral_lt_of_antitone` — **upper semicontinuous domination** (eventual form of
  `bt:usc-domination`): for finite measures `μ_k → μ` weakly on continuous functions, carried by a
  compact `K`, and weights `f_k ↓ f` upper semicontinuous and uniformly bounded on `K`,
  `limsup ∫ f_k dμ_k ≤ ∫ f dμ`.
* `formMeasure` — the positive measure `S(Ψ)` of a variable strongly positive test form
  `Ψ = ∑ᵢ φᵢ γᵢ` against a positive current `S`; `sum_mulBorel_eq_integral_formMeasure`
  (`∑ᵢ (f S)(γᵢ)(φᵢ) = ∫ f dS(Ψ)`), `tendsto_integral_formMeasure` (weak convergence).
* `weakTendsto_of_local` — weak convergence is local (smooth partition of unity).
* `weakTendsto_btProduct_of_antitone` / `weakTendsto_mulBorel_btProduct_of_antitone` —
  **the decreasing continuity theorem**: for `T` positive closed and locally bounded PSH
  `u_j^k ↓ u_j`, `B(u^k; T) → B(u; T)` and `u_1^k B(u_2^k, …; T) → u_1 B(u_2, …; T)` weakly.
  The proof squeezes every coefficient between the upper bound from usc domination and the lower
  bound on the trace from the collar comparison (`LocalBedfordTaylorCollar.collar_comparison`); no
  weak compactness is used.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  CoordinateWedgeAssoc ClosedProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorLocality LocalCurrentLebesgue ConstantFormProducts LocalBedfordTaylorForms
  LocalBedfordTaylorContinuity LocalBedfordTaylorCollar LocalBedfordTaylorMass

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U : Opens (ComplexModel n)}

/-! ### Upper semicontinuous domination -/

section Usc

/-- A locally bounded PSH function is upper semicontinuous on its domain. -/
theorem upperSemicontinuousOn_of_isLocallyBoundedPshOn {u : E → ℝ}
    (hu : IsLocallyBoundedPshOn U u) : UpperSemicontinuousOn u U := by
  intro x hx c hc
  have h := hu.1.upperSemicontinuousOn x hx (c : EReal) (EReal.coe_lt_coe_iff.mpr hc)
  filter_upwards [h] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

theorem ae_mem_of_compl_eq_zero {μ : Measure E} {K : Set E} (h : μ Kᶜ = 0) : ∀ᵐ x ∂μ, x ∈ K := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with x hx
  simpa using hx

/-- **Upper semicontinuous domination**, eventual form (`bt:usc-domination`): let `μ_k`, `μ` be
finite measures carried by a nonempty compact `K` with `∫ g dμ_k → ∫ g dμ` for every continuous
    `g`,
and let `f_k ↓ f` on `K` be measurable, upper semicontinuous on `K` and uniformly bounded on `K`.
Then `∫ f_k dμ_k < b` eventually, for every `b > ∫ f dμ`. -/
theorem eventually_integral_lt_of_antitone {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {μ : ℕ → Measure E} {μ₀ : Measure E} [∀ k, IsFiniteMeasure (μ k)] [IsFiniteMeasure μ₀]
    (hμK : ∀ k, μ k Kᶜ = 0) (hμ₀K : μ₀ Kᶜ = 0)
    (hconv : ∀ g : E → ℝ, Continuous g →
      Tendsto (fun k => ∫ x, g x ∂μ k) atTop (𝓝 (∫ x, g x ∂μ₀)))
    {f : ℕ → E → ℝ} {f₀ : E → ℝ} (hf : ∀ k, Measurable (f k))
    (husc : ∀ k, UpperSemicontinuousOn (f k) K) (hanti : ∀ x ∈ K, Antitone fun k => f k x)
    (hlim : ∀ x ∈ K, Tendsto (fun k => f k x) atTop (𝓝 (f₀ x)))
    {C : ℝ} (hC : ∀ k, ∀ x ∈ K, |f k x| ≤ C) {b : ℝ} (hb : ∫ x, f₀ x ∂μ₀ < b) :
    ∀ᶠ k in atTop, ∫ x, f k x ∂μ k < b := by
  have hK₀ := ae_mem_of_compl_eq_zero hμ₀K
  -- step 1: `∫ f_k dμ → ∫ f dμ`
  have h1 : Tendsto (fun k => ∫ x, f k x ∂μ₀) atTop (𝓝 (∫ x, f₀ x ∂μ₀)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun k => (hf k).aestronglyMeasurable) (integrable_const C) (fun k => ?_) ?_
    · filter_upwards [hK₀] with x hx
      rw [Real.norm_eq_abs]
      exact hC k x hx
    · filter_upwards [hK₀] with x hx
      exact hlim x hx
  obtain ⟨k₀, hk₀⟩ := (h1.eventually (gt_mem_nhds hb)).exists
  -- step 2: Lipschitz majorants of `f_{k₀}` on `K`
  set g : ℕ → E → ℝ := fun ℓ => uscLipschitzMajorant K (f k₀) (ℓ : ℝ) with hg_def
  have hgc : ∀ ℓ, Continuous (g ℓ) := fun ℓ =>
    continuous_uscLipschitzMajorant hK hKne (husc k₀) (Nat.cast_nonneg ℓ)
  have hgle : ∀ ℓ, ∀ x ∈ K, f k₀ x ≤ g ℓ x := fun ℓ x hx =>
    le_uscLipschitzMajorant hK (husc k₀) (Nat.cast_nonneg ℓ) hx
  have hgub : ∀ ℓ, ∀ x, g ℓ x ≤ C := fun ℓ x => by
    simp only [hg_def, uscLipschitzMajorant]
    refine csSup_le (hKne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have := (le_abs_self (f k₀ y)).trans (hC k₀ y hy)
    have hd : 0 ≤ (ℓ : ℝ) * dist x y := mul_nonneg (Nat.cast_nonneg ℓ) dist_nonneg
    linarith
  have hgabs : ∀ ℓ, ∀ x ∈ K, |g ℓ x| ≤ C := fun ℓ x hx => by
    rw [abs_le]
    constructor
    · have := (neg_abs_le (f k₀ x)).trans (hgle ℓ x hx)
      linarith [hC k₀ x hx]
    · exact hgub ℓ x
  have h2 : Tendsto (fun ℓ => ∫ x, g ℓ x ∂μ₀) atTop (𝓝 (∫ x, f k₀ x ∂μ₀)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun ℓ => (hgc ℓ).aestronglyMeasurable) (integrable_const C) (fun ℓ => ?_) ?_
    · filter_upwards [hK₀] with x hx
      rw [Real.norm_eq_abs]
      exact hgabs ℓ x hx
    · filter_upwards [hK₀] with x hx
      exact tendsto_uscLipschitzMajorant_nat hK hKne (husc k₀) hx
  obtain ⟨ℓ, hℓ⟩ := (h2.eventually (gt_mem_nhds hk₀)).exists
  -- step 3: compare along the sequence
  filter_upwards [(hconv (g ℓ) (hgc ℓ)).eventually (gt_mem_nhds hℓ), eventually_ge_atTop k₀]
    with k hk hkk
  have hKk := ae_mem_of_compl_eq_zero (hμK k)
  have hfi : Integrable (f k) (μ k) := Integrable.of_bound (hf k).aestronglyMeasurable C (by
    filter_upwards [hKk] with x hx
    rw [Real.norm_eq_abs]
    exact hC k x hx)
  have hgi : Integrable (g ℓ) (μ k) := Integrable.of_bound (hgc ℓ).aestronglyMeasurable C (by
    filter_upwards [hKk] with x hx
    rw [Real.norm_eq_abs]
    exact hgabs ℓ x hx)
  refine lt_of_le_of_lt (integral_mono_ae hfi hgi ?_) hk
  filter_upwards [hKk] with x hx
  exact (hanti x hx hkk).trans (hgle ℓ x hx)

end Usc

/-! ### The positive measure of a variable test form -/

section FormMeasure

variable {m : ℕ}

/-- The density `x ↦ ∑ᵢ φᵢ(x) L_x(γᵢ)` of the coefficient measure of a variable test form
`Ψ = ∑ᵢ φᵢ γᵢ` against a positive current `S` (with respect to its trace measure). -/
def formDensity {S : LocalProductCurrent n U m} (hS : IsPositive S) {ι : Type*} [Fintype ι]
    (γ : ι → formSpan n m) (φ : ι → 𝓓(U, ℝ)) (x : E) : ℝ :=
  ∑ i, φ i x * densityForm hS x (γ i)

/-- **The measure `S(Ψ)`** of a variable test form `Ψ = ∑ᵢ φᵢ γᵢ` against a positive current `S`
(positive when `Ψ` is strongly positive at every point). -/
def formMeasure {S : LocalProductCurrent n U m} (hS : IsPositive S) {ι : Type*} [Fintype ι]
    (γ : ι → formSpan n m) (φ : ι → 𝓓(U, ℝ)) : Measure E :=
  hS.traceMeasure.withDensity (posDensity (formDensity hS γ φ))

variable {S : LocalProductCurrent n U m} {ι : Type*} [Fintype ι] {γ : ι → formSpan n m}
  {φ : ι → 𝓓(U, ℝ)}

theorem measurable_formDensity (hS : IsPositive S) (γ : ι → formSpan n m) (φ : ι → 𝓓(U, ℝ)) :
    Measurable (formDensity hS γ φ) :=
  Finset.measurable_sum _ fun i _ => (φ i).continuous.measurable.mul (measurable_densityForm hS _)

theorem ae_formDensity_nonneg (hS : IsPositive S)
    (hpos : ∀ x, ∑ i, φ i x • (γ i : RealForm n (2 * m)) ∈ spCone m) :
    ∀ᵐ x ∂hS.traceMeasure, 0 ≤ formDensity hS γ φ x := by
  filter_upwards [ae_densityForm_nonneg hS] with x hx
  have hmem : (∑ i, φ i x • γ i : formSpan n m) ∈ posCone n m := by
    change ((∑ i, φ i x • γ i : formSpan n m) : RealForm n (2 * m)) ∈ spCone m
    rw [Submodule.coe_sum]
    simpa only [Submodule.coe_smul] using hpos x
  have h := hx _ hmem
  rw [map_sum] at h
  simpa only [formDensity, map_smul, smul_eq_mul] using h

theorem integral_formMeasure (hS : IsPositive S)
    (hpos : ∀ x, ∑ i, φ i x • (γ i : RealForm n (2 * m)) ∈ spCone m) (f : E → ℝ) :
    ∫ x, f x ∂formMeasure hS γ φ = ∫ x, formDensity hS γ φ x * f x ∂hS.traceMeasure := by
  rw [formMeasure, integral_withDensity_posDensity _ (measurable_formDensity hS γ φ)]
  refine integral_congr_ae ?_
  filter_upwards [ae_formDensity_nonneg hS hpos] with x hx
  rw [max_eq_left hx]

/-- **`∑ᵢ (f S)(γᵢ)(φᵢ) = ∫ f dS(Ψ)`.** -/
theorem sum_mulBorel_eq_integral_formMeasure (hS : IsPositive S)
    (hpos : ∀ x, ∑ i, φ i x • (γ i : RealForm n (2 * m)) ∈ spCone m) {f : E → ℝ}
    (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    ∑ i, mulBorel S f (γ i) (φ i) = ∫ x, f x ∂formMeasure hS γ φ := by
  rw [integral_formMeasure hS hpos]
  simp only [mulBorel_apply hS hf hfb]
  rw [← integral_finsetSum _ fun i _ => hS.integrable_mul_density hf hfb (γ i) (φ i)]
  refine integral_congr_ae ?_
  have hall : ∀ᵐ x ∂hS.traceMeasure, ∀ i, densityForm hS x (γ i) = hS.density (γ i) x :=
    ae_all_iff.mpr fun i => densityForm_ae hS (γ i)
  filter_upwards [hall] with x hx
  simp only [formDensity, hx, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The measure `S(Ψ)` is carried by any compact set off which all the `φᵢ` vanish. -/
theorem formMeasure_compl {K : Set E} (hK : IsCompact K) (hS : IsPositive S)
    (hφK : ∀ i, ∀ x ∉ K, φ i x = 0) : formMeasure hS γ φ Kᶜ = 0 := by
  rw [formMeasure, withDensity_apply _ hK.measurableSet.compl]
  refine (setLIntegral_congr_fun hK.measurableSet.compl fun x hx => ?_).trans (lintegral_zero)
  simp [posDensity, formDensity, hφK _ x hx]

theorem isFiniteMeasure_formMeasure {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : IsPositive S) (hφK : ∀ i, ∀ x ∉ K, φ i x = 0) : IsFiniteMeasure (formMeasure hS γ φ)
      := by
  choose C _ hC using fun i => exists_abs_densityForm_le hS (γ i)
  choose Φ hΦ using fun i => (φ i).continuous.bounded_above_of_compact_support (φ
    i).hasCompactSupport
  have hbd : ∀ x ∈ K, |formDensity hS γ φ x| ≤ ∑ i, |Φ i| * C i := fun x _ => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul ((by simpa [Real.norm_eq_abs] using hΦ i x : |φ i x| ≤ Φ i).trans
      (le_abs_self _)) (hC i x) (abs_nonneg _) (abs_nonneg _)
  have hlt := withDensity_posDensity_lt_top hS.traceMeasure hK.measurableSet
    (hS.traceMeasure_lt_top hK hKU) hbd
  refine ⟨lt_of_le_of_lt (measure_univ_le_add_compl K) ?_⟩
  rw [show formMeasure hS γ φ Kᶜ = 0 from formMeasure_compl hK hS hφK, add_zero]
  exact hlt

/-- **Weak convergence of the measures `S_k(Ψ)`** on continuous functions, for `S_k → S`. -/
theorem tendsto_integral_formMeasure {S : ℕ → LocalProductCurrent n U m}
    {S₀ : LocalProductCurrent n U m} (hS : ∀ k, IsPositive (S k)) (hS₀ : IsPositive S₀)
    (hconv : WeakTendsto S S₀)
    (hpos : ∀ x, ∑ i, φ i x • (γ i : RealForm n (2 * m)) ∈ spCone m) {g : E → ℝ}
    (hg : Continuous g) :
    Tendsto (fun k => ∫ x, g x ∂formMeasure (hS k) γ φ) atTop
      (𝓝 (∫ x, g x ∂formMeasure hS₀ γ φ)) := by
  have hgb : IsLocallyBoundedOn g U := fun K hK _ => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  simp only [← sum_mulBorel_eq_integral_formMeasure _ hpos hg.measurable hgb]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact weakTendsto_mulBorel hS hconv (fun _ => hg.measurable) (fun _ => hgb) hg.measurable
    hg.continuousOn (fun u hu x _ => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ =>
      refl_mem_uniformity hu⟩) (γ i) (φ i)

end FormMeasure

/-! ### Weak convergence is local -/

section Local

variable {q : ℕ}

/-- **Splitting a test function along an open cover** (smooth partition of unity). -/
theorem exists_sum_extTest {ι : Type*} (V : ι → Opens (ComplexModel n)) (hVU : ∀ i, V i ≤ U)
    (hcover : ∀ x ∈ (U : Set E), ∃ i, x ∈ V i) (φ : 𝓓(U, ℝ)) :
    ∃ (s : Finset ι) (ψ : ∀ i, 𝓓(V i, ℝ)), φ = ∑ i ∈ s, extTest (hVU i) (ψ i) := by
  have hcover_support : tsupport φ ⊆ ⋃ i, (V i : Set E) := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x (φ.tsupport_subset hx)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, _, ψ, _, _, hsum⟩ :=
    exists_weighted_test_partition V hVU φ.hasCompactSupport hcover_support
      (fun _ : Unit ↦ φ) (fun _ ↦ subset_rfl)
  exact ⟨s, fun i ↦ ψ i (), hsum ()⟩

/-- **Weak convergence is local**: if every point of `U` has an open neighbourhood `V ≤ U` on
whose test functions `R_k → R`, then `R_k → R` weakly on `U`. -/
theorem weakTendsto_of_local {R : ℕ → LocalProductCurrent n U q} {R₀ : LocalProductCurrent n U q}
    (hloc : ∀ x ∈ (U : Set E), ∃ (V : Opens (ComplexModel n)) (hVU : V ≤ U), x ∈ V ∧
      ∀ γ (ψ : 𝓓(V, ℝ)), Tendsto (fun k => R k γ (extTest hVU ψ)) atTop
        (𝓝 (R₀ γ (extTest hVU ψ)))) :
    WeakTendsto R R₀ := by
  classical
  choose! V hVU hxV hV using hloc
  intro γ φ
  let ι := (U : Set E)
  obtain ⟨s, ψ, hφ⟩ := exists_sum_extTest (fun i : ι => V i) (fun i => hVU i i.2)
    (fun x hx => ⟨⟨x, hx⟩, hxV x hx⟩) φ
  rw [hφ]
  simp only [map_sum]
  exact tendsto_finsetSum _ fun i _ => hV i i.2 γ (ψ i)

end Local

/-! ### Locality tools -/

section Locality

/-- `dd^c(u T)` depends only on `u` on `U`. -/
theorem ddcMul_congr {k : ℕ} (T : LocalProductCurrent n U (k + 1)) {f f' : E → ℝ}
    (h : ∀ x ∈ (U : Set E), f x = f' x) : ddcMul T f = ddcMul T f' := by
  have e : (U : Set E).indicator f = (U : Set E).indicator f' := by
    funext x
    by_cases hx : x ∈ (U : Set E)
    · simp [hx, h x hx]
    · simp [hx]
  simp only [ddcMul, e]

/-- `B(u; T)` depends only on the potentials on `U`. -/
theorem btProduct_congr : ∀ (q r : ℕ) (u u' : Fin q → E → ℝ) (T : LocalProductCurrent n U (r + q)),
    (∀ i, ∀ x ∈ (U : Set E), u i x = u' i x) → btProduct q r u T = btProduct q r u' T
  | 0, _, _, _, _, _ => rfl
  | q + 1, r, u, u', T, h => by
    rw [btProduct_succ, btProduct_succ, ddcMul_congr (k := r + q) T (h (Fin.last q))]
    exact btProduct_congr q r _ _ _ fun i => h _

/-- **Locality of the recursive product**: on an open `W ≤ U` where `u_i = u'_i + c_i`,
`B(u; T) = B(u'; T)`. -/
theorem restrict_btProduct_eq {W : Opens (ComplexModel n)} (hWU : W ≤ U) (q r : ℕ)
    (u u' : Fin q → E → ℝ) (c : Fin q → ℝ) (T : LocalProductCurrent n U (r + q))
    (hT : IsPositive T) (hTc : IsClosedAny (r + q) T) (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    (hu' : ∀ i, IsLocallyBoundedPshOn U (u' i)) (h : ∀ i, ∀ x ∈ (W : Set E), u i x = u' i x + c i)
      :
    restrict hWU (btProduct q r u T) = restrict hWU (btProduct q r u' T) := by
  rw [← btProduct_restrict hWU q r u T hT hTc hu, ← btProduct_restrict hWU q r u' T hT hTc hu',
    btProduct_congr q r u (fun i x => u' i x + c i) _ (fun i x hx => h i x hx),
    btProduct_add_const q r u' c _ (isPositive_restrict hT hWU) (isClosedAny_restrict hTc hWU)
      (fun i => isLocallyBoundedPshOn_mono (hu' i) hWU)]

/-- **Locality of the multiplication**: if `S = S'` on an open `W ≤ U` and `f = f' + c` on `W`,
then `(f S)(γ)(ψ) = (f' S')(γ)(ψ) + c S'(γ)(ψ)` for every test function `ψ` supported in `W`. -/
theorem mulBorel_extTest_eq {m : ℕ} {W : Opens (ComplexModel n)} (hWU : W ≤ U)
    {S S' : LocalProductCurrent n U m} (hS : IsPositive S) (hS' : IsPositive S')
    (hSS' : restrict hWU S = restrict hWU S') {f f' : E → ℝ} (hf : Measurable f)
    (hfb : IsLocallyBoundedOn f U) (hf' : Measurable f') (hf'b : IsLocallyBoundedOn f' U) {c : ℝ}
    (hc : ∀ x ∈ (W : Set E), f x = f' x + c) (γ : formSpan n m) (ψ : 𝓓(W, ℝ)) :
    mulBorel S f γ (extTest hWU ψ) =
      mulBorel S' f' γ (extTest hWU ψ) + c * S' γ (extTest hWU ψ) := by
  have hSW := isPositive_restrict hS' hWU
  have hcm : Measurable (fun _ : E => c) := measurable_const
  have hcb : IsLocallyBoundedOn (fun _ : E => c) W := fun _ _ _ => ⟨|c|, fun _ _ => le_rfl⟩
  have e1 : mulBorel S f γ (extTest hWU ψ) = mulBorel (restrict hWU S) f γ ψ := by
    rw [mulBorel_restrict hS hWU hf hfb]
    rfl
  have e2 : mulBorel (restrict hWU S') f =
      mulBorel (restrict hWU S') f' + c • restrict hWU S' := by
    rw [mulBorel_congr hSW hf (isLocallyBoundedOn_mono hfb hWU) (hf'.add hcm)
      (fun K hK hKW => by
        obtain ⟨M, hM⟩ := isLocallyBoundedOn_mono hf'b hWU K hK hKW
        exact ⟨M + |c|, fun x hx => (abs_add_le _ _).trans (by linarith [hM x hx])⟩) hc]
    rw [mulBorel_add hSW hf' (isLocallyBoundedOn_mono hf'b hWU) hcm hcb, mulBorel_const hSW]
  rw [e1, hSS', e2, LinearMap.add_apply, _root_.add_apply, mulBorel_restrict hS' hWU hf' hf'b,
    LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul]
  rfl

/-- The trace measures of two positive currents agreeing on an open `W ≤ U` agree on `W`. -/
theorem setIntegral_eq_of_restrict_eq {m : ℕ} {W : Opens (ComplexModel n)} (hWU : W ≤ U)
    {S S' : LocalProductCurrent n U m} (hS : IsPositive S) (hS' : IsPositive S')
    (h : restrict hWU S = restrict hWU S') (F : E → ℝ) :
    ∫ x in (W : Set E), F x ∂hS.traceMeasure = ∫ x in (W : Set E), F x ∂hS'.traceMeasure := by
  rw [← traceMeasure_restrict hS hWU, ← traceMeasure_restrict hS' hWU,
    IsPositive.traceMeasure_congr _ (isPositive_restrict hS' hWU) h]

/-- Upper semicontinuity on `K` only sees the values on `K`. -/
theorem upperSemicontinuousOn_congr {f g : E → ℝ} {K : Set E} (hf : UpperSemicontinuousOn f K)
    (h : ∀ x ∈ K, f x = g x) : UpperSemicontinuousOn g K := by
  intro x hx c hc
  rw [← h x hx] at hc
  filter_upwards [hf x hx c hc, self_mem_nhdsWithin] with y hy hyK
  rwa [← h y hyK]

/-- **Splitting off the collar**: for `χ` continuous, supported in `B` and equal to one on a closed
set `K`, `∫_B g S ∧ ω₀^m = ∫ χ g S ∧ ω₀^m + ∫_{B \ K} (1 - χ) g S ∧ ω₀^m`. -/
theorem traceIntegral_eq_add {m : ℕ} {B : Opens (ComplexModel n)} (hB : RelativelyCompactIn B U)
    {S : LocalProductCurrent n U m} (hS : IsPositive S) {g : E → ℝ}
    (hg : IsLocallyBoundedPshOn U g) {χ : E → ℝ} (hχ : Continuous χ)
    (hχB : ∀ x ∉ (B : Set E), χ x = 0) {K : Set E} (hχK : ∀ x ∈ K, χ x = 1) :
    traceIntegral B g S = ∫ x, χ x * g x ∂hS.traceMeasure +
      ∫ x in (B : Set E) \ K, (1 - χ x) * g x ∂hS.traceMeasure := by
  have h1 := integrableOn_mul_of_isLocallyBoundedPshOn hS hB hχ.continuousOn hg
  have h1χ : ContinuousOn (fun x => 1 - χ x) U := continuousOn_const.sub hχ.continuousOn
  have h2 := integrableOn_mul_of_isLocallyBoundedPshOn hS hB h1χ hg
  rw [traceIntegral_of_isPositive _ _ hS]
  have e : ∫ x in (B : Set E), g x ∂hS.traceMeasure =
      ∫ x in (B : Set E), (χ x * g x + (1 - χ x) * g x) ∂hS.traceMeasure := by
    congr 1
    funext x
    ring
  rw [e, integral_add h1 h2, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hχB x hx, zero_mul]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero B.isOpen.measurableSet
      (s := (B : Set E) \ K) sdiff_subset (fun x hx => by
        have hxK : x ∈ K := by
          by_contra hxK
          exact hx.2 ⟨hx.1, hxK⟩
        rw [hχK x hxK, sub_self, zero_mul])]

/-- `∫ χ f d(S ∧ ω₀^m)` as the value of `f S` on `χ ω₀^m`. -/
theorem integral_eq_mulBorel_kahlerPower {m : ℕ} {S : LocalProductCurrent n U m}
    (hS : IsPositive S) {f : E → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U)
    (χ : 𝓓(U, ℝ)) :
    mulBorel S f (kahlerPower n m) χ = ∫ x, χ x * f x ∂hS.traceMeasure := by
  have hd : IsLocalDensity (U := U) hS.traceMeasure (fun _ => 1) :=
    ⟨hS.traceMeasure_compl, fun K hK hKU => hS.traceMeasure_lt_top hK hKU,
      measurable_const, fun K _ _ => ⟨1, fun _ _ => by simp⟩⟩
  rw [mulBorel_apply_of_integral_eq hS _ hd (fun ψ => by
    rw [← hS.integral_traceMeasure]
    simp) hf hfb χ]
  simp only [mul_one]

end Locality

/-! ### The squeeze on a ball after the collar modification -/

section Squeeze

open Metric

variable {z₀ : ComplexModel n} {R A : ℝ}

theorem collarMax_eq_ballPot {a : E → ℝ} {z : E} (hz : z ∈ ball z₀ R)
    (hzK : z ∉ collarCore A z₀ R) (ha : a z ≤ -1) : collarMax A z₀ R a z = ballPot A z₀ R z :=
  max_eq_left (by linarith [lt_ballPot_of_notMem_collarCore (A := A) hz hzK])

/-- The ball as an open set, relatively compact in `U` when its closure lies in `U`. -/
theorem relativelyCompactIn_ball (hR : 0 < R) (hBU : closedBall z₀ R ⊆ U) :
    RelativelyCompactIn (⟨ball z₀ R, isOpen_ball⟩ : Opens (ComplexModel n)) U := by
  refine ⟨?_, ?_⟩
  · change IsCompact (closure (ball z₀ R))
    rw [closure_ball z₀ hR.ne']
    exact isCompact_closedBall _ _
  · change closure (ball z₀ R) ⊆ U
    rw [closure_ball z₀ hR.ne']
    exact hBU

private theorem scaledForm_sub_mem_spCone {m : ℕ} {β γ : RealForm n (2 * m)}
    {C bound x : ℝ} (hβ : β ∈ spCone m) (hC : 0 ≤ C)
    (hsub : C • β - γ ∈ spCone m) (hadd : C • β + γ ∈ spCone m)
    (hx : |x| ≤ bound) : (bound * C) • β + (-x) • γ ∈ spCone m := by
  rcases le_total 0 x with h | h
  · have heq : (bound * C) • β + (-x) • γ =
        (bound - x) • (C • β) + x • (C • β - γ) := by module
    rw [heq]
    exact (spCone m).add_mem (smul_mem_spCone (smul_mem_spCone hβ hC)
      (by linarith [le_abs_self x])) (smul_mem_spCone hsub h)
  · have heq : (bound * C) • β + (-x) • γ =
        (bound + x) • (C • β) + (-x) • (C • β + γ) := by module
    rw [heq]
    exact (spCone m).add_mem (smul_mem_spCone (smul_mem_spCone hβ hC)
      (by linarith [neg_abs_le x])) (smul_mem_spCone hadd (neg_nonneg.mpr h))

/-- **The squeeze** (`bt:decreasing-continuity`, after the collar modification): on a ball
`B = B(z₀, R)` with `BBar ⊆ U`, for locally bounded PSH `a_k ↓ a₀` with `a_k ≤ -1` on `BBar`, put
`w_k = max(h, a_k)`, `v = max(h, a₀)` (`h = A(|z - z₀|² - R²)`).  If
`B(w_{k,1}, …, w_{k,q}; T) → B(v_1, …, v_q; T)` weakly, then
`w_{k,0} B(w_{k,1}, …; T) → v_0 B(v_1, …; T)` on every test function supported in `B`: the trace
on a cutoff is bounded below by `collar_comparison`, and the values on `M C χ ω₀^m ∓ φ γ` are
bounded above in the limit by upper semicontinuous domination. -/
theorem tendsto_mulBorel_collarMax {q m : ℕ} (hR : 0 < R) (hA : 0 < A)
    (hBU : closedBall z₀ R ⊆ U) (T : LocalProductCurrent n U (m + q)) (hT : IsPositive T)
    (hTc : IsClosedAny (m + q) T) (a : ℕ → Fin (q + 1) → E → ℝ) (a₀ : Fin (q + 1) → E → ℝ)
    (ha : ∀ k i, IsLocallyBoundedPshOn U (a k i)) (ha₀ : ∀ i, IsLocallyBoundedPshOn U (a₀ i))
    (ha1 : ∀ k i, ∀ z ∈ closedBall z₀ R, a k i z ≤ -1)
    (hanti : ∀ i, ∀ z ∈ (U : Set E), Antitone fun k => a k i z)
    (hlim : ∀ i, ∀ z ∈ (U : Set E), Tendsto (fun k => a k i z) atTop (𝓝 (a₀ i z)))
    (hIH : WeakTendsto (fun k => btProduct q m (fun i => collarMax A z₀ R (a k i.succ)) T)
      (btProduct q m (fun i => collarMax A z₀ R (a₀ i.succ)) T))
    (γ : formSpan n m) (φ : 𝓓(U, ℝ)) (hφB : tsupport φ ⊆ ball z₀ R) :
    Tendsto (fun k => mulBorel (btProduct q m (fun i => collarMax A z₀ R (a k i.succ)) T)
        ((U : Set E).indicator (collarMax A z₀ R (a k 0))) γ φ) atTop
      (𝓝 (mulBorel (btProduct q m (fun i => collarMax A z₀ R (a₀ i.succ)) T)
        ((U : Set E).indicator (collarMax A z₀ R (a₀ 0))) γ φ)) := by
  classical
  -- notation and basic facts
  set w : ℕ → Fin (q + 1) → E → ℝ := fun k i => collarMax A z₀ R (a k i) with hw_def
  set v : Fin (q + 1) → E → ℝ := fun i => collarMax A z₀ R (a₀ i) with hv_def
  set h : E → ℝ := ballPot A z₀ R with h_def
  have hKU : closedBall z₀ R ⊆ (U : Set E) := hBU
  have hle : ∀ k i, ∀ z ∈ (U : Set E), a₀ i z ≤ a k i z := fun k i z hz =>
    (hanti i z hz).le_of_tendsto (hlim i z hz) k
  have ha₀1 : ∀ i, ∀ z ∈ closedBall z₀ R, a₀ i z ≤ -1 := fun i z hz =>
    (hle 0 i z (hKU hz)).trans (ha1 0 i z hz)
  have hw : ∀ k i, IsLocallyBoundedPshOn U (w k i) := fun k i =>
    isLocallyBoundedPshOn_collarMax hA.le z₀ R (ha k i)
  have hv : ∀ i, IsLocallyBoundedPshOn U (v i) := fun i =>
    isLocallyBoundedPshOn_collarMax hA.le z₀ R (ha₀ i)
  have hh : IsLocallyBoundedPshOn U h := isLocallyBoundedPshOn_ballPot hA.le z₀ R
  set S : ℕ → LocalProductCurrent n U m := fun k => btProduct q m (fun i => w k i.succ) T
    with hS_def
  set S₀ : LocalProductCurrent n U m := btProduct q m (fun i => v i.succ) T with hS₀_def
  have hS : ∀ k, IsPositive (S k) ∧ IsClosedAny m (S k) := fun k =>
    isPositive_btProduct q m _ T hT hTc fun i => hw k _
  have hS₀ : IsPositive S₀ ∧ IsClosedAny m S₀ := isPositive_btProduct q m _ T hT hTc fun i => hv _
  set f : ℕ → E → ℝ := fun k => (U : Set E).indicator (w k 0) with hf_def
  set f₀ : E → ℝ := (U : Set E).indicator (v 0) with hf₀_def
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_indicator_of_isLocallyBoundedPshOn (hw k
    0)
  have hfb : ∀ k, IsLocallyBoundedOn (f k) U := fun k => isLocallyBoundedOn_indicator (hw k 0)
  have hf₀m : Measurable f₀ := measurable_indicator_of_isLocallyBoundedPshOn (hv 0)
  have hf₀b : IsLocallyBoundedOn f₀ U := isLocallyBoundedOn_indicator (hv 0)
  -- the ball and the cutoff
  let B : Opens (ComplexModel n) := ⟨ball z₀ R, isOpen_ball⟩
  have hB : RelativelyCompactIn B U := relativelyCompactIn_ball hR hBU
  have hK' : IsCompact (collarCore A z₀ R ∪ tsupport φ) :=
    (isCompact_collarCore A z₀ R).union φ.hasCompactSupport
  obtain ⟨χ, hχ, hχ1, hχB, hχ01⟩ := exists_cutoff_unit hK' isOpen_ball
    (union_subset (collarCore_subset_ball hA z₀ R) hφB)
  have hχc : HasCompactSupport χ := (isCompact_closedBall z₀ R).of_isClosed_subset
    (isClosed_tsupport χ) (hχB.trans ball_subset_closedBall)
  let χ' : 𝓓(U, ℝ) :=
    { toFun := χ, contDiff' := hχ, hasCompactSupport' := hχc,
      tsupport_subset' := (hχB.trans ball_subset_closedBall).trans hKU }
  have hχ'_apply : ∀ x, χ' x = χ x := fun x => rfl
  have hχ0 : ∀ x ∉ ball z₀ R, χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hχB h)
  -- the collar part does not depend on `k`
  let W : Opens (ComplexModel n) :=
    ⟨ball z₀ R \ collarCore A z₀ R, isOpen_ball.sdiff (isCompact_collarCore A z₀ R).isClosed⟩
  have hWU : W ≤ U := fun z hz => hKU (ball_subset_closedBall hz.1)
  set Sh : LocalProductCurrent n U m := btProduct q m (fun _ => h) T with hSh_def
  have hSh : IsPositive Sh := (isPositive_btProduct q m _ T hT hTc fun _ => hh).1
  have hcollar : ∀ (b : Fin (q + 1) → E → ℝ), (∀ i, IsLocallyBoundedPshOn U (b i)) →
      (∀ i, ∀ z ∈ closedBall z₀ R, b i z ≤ -1) →
      ∀ hP : IsPositive (btProduct q m (fun i => collarMax A z₀ R (b i.succ)) T),
      ∫ x in (W : Set E), (1 - χ x) * collarMax A z₀ R (b 0) x ∂hP.traceMeasure =
        ∫ x in (W : Set E), (1 - χ x) * h x ∂hSh.traceMeasure := by
    intro b hb hb1 hP
    have hres : restrict hWU (btProduct q m (fun i => collarMax A z₀ R (b i.succ)) T) =
        restrict hWU Sh :=
      restrict_btProduct_eq hWU q m _ _ (fun _ => 0) T hT hTc
        (fun i => isLocallyBoundedPshOn_collarMax hA.le z₀ R (hb _)) (fun _ => hh)
        fun i z hz => by
          rw [collarMax_eq_ballPot hz.1 hz.2 (hb1 _ z (ball_subset_closedBall hz.1)), add_zero]
    rw [← setIntegral_eq_of_restrict_eq hWU hP hSh hres]
    refine setIntegral_congr_fun W.isOpen.measurableSet fun z hz => ?_
    rw [collarMax_eq_ballPot hz.1 hz.2 (hb1 0 z (ball_subset_closedBall hz.1))]
  -- the lower bound on the trace: `A₀ ≤ A_k`
  set Ak : ℕ → ℝ := fun k => mulBorel (S k) (f k) (kahlerPower n m) χ' with hAk_def
  set A₀ : ℝ := mulBorel S₀ f₀ (kahlerPower n m) χ' with hA₀_def
  have htrace : ∀ (b : Fin (q + 1) → E → ℝ), (∀ i, IsLocallyBoundedPshOn U (b i)) →
      ∀ hP : IsPositive (btProduct q m (fun i => collarMax A z₀ R (b i.succ)) T),
      mulBorel (btProduct q m (fun i => collarMax A z₀ R (b i.succ)) T)
          ((U : Set E).indicator (collarMax A z₀ R (b 0))) (kahlerPower n m) χ' =
        ∫ x, χ x * collarMax A z₀ R (b 0) x ∂hP.traceMeasure := by
    intro b hb hP
    have hb0 := isLocallyBoundedPshOn_collarMax hA.le z₀ R (hb 0)
    rw [integral_eq_mulBorel_kahlerPower hP (measurable_indicator_of_isLocallyBoundedPshOn hb0)
      (isLocallyBoundedOn_indicator hb0)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hχ'_apply]
    by_cases hx : x ∈ ball z₀ R
    · rw [Set.indicator_of_mem (hKU (ball_subset_closedBall hx))]
    · rw [hχ0 x hx, zero_mul, zero_mul]
  have hlow : ∀ k, A₀ ≤ Ak k := by
    intro k
    have hcmp := collar_comparison hR hA hBU T hT hTc a₀ (a k) ha₀ (ha k)
      (fun i z hz => hle k i z (hKU hz)) (ha1 k)
    have e1 := traceIntegral_eq_add hB hS₀.1 (hv 0) hχ.continuous hχ0 (fun x hx => hχ1 x (Or.inl
      hx))
    have e2 := traceIntegral_eq_add hB (hS k).1 (hw k 0) hχ.continuous hχ0
      (fun x hx => hχ1 x (Or.inl hx))
    have c1 := hcollar a₀ ha₀ ha₀1 hS₀.1
    have c2 := hcollar (a k) (ha k) (ha1 k) (hS k).1
    have t1 := htrace a₀ ha₀ hS₀.1
    have t2 := htrace (a k) (ha k) (hS k).1
    change traceIntegral (B : Set E) (v 0) S₀ ≤ traceIntegral (B : Set E) (w k 0) (S k) at hcmp
    rw [e1, e2] at hcmp
    have c1' : ∫ x in (B : Set E) \ collarCore A z₀ R, (1 - χ x) * v 0 x ∂hS₀.1.traceMeasure =
        ∫ x in (W : Set E), (1 - χ x) * h x ∂hSh.traceMeasure := c1
    have c2' : ∫ x in (B : Set E) \ collarCore A z₀ R, (1 - χ x) * w k 0 x ∂(hS k).1.traceMeasure =
        ∫ x in (W : Set E), (1 - χ x) * h x ∂hSh.traceMeasure := c2
    rw [c1', c2'] at hcmp
    have hmain : ∫ x, χ x * v 0 x ∂hS₀.1.traceMeasure ≤
        ∫ x, χ x * w k 0 x ∂(hS k).1.traceMeasure := by linarith
    calc A₀ = ∫ x, χ x * v 0 x ∂hS₀.1.traceMeasure := t1
      _ ≤ ∫ x, χ x * w k 0 x ∂(hS k).1.traceMeasure := hmain
      _ = Ak k := t2.symm
  -- the weights on the closed ball
  have hfK : ∀ k, ∀ x ∈ closedBall z₀ R, f k x = w k 0 x := fun k x hx =>
    Set.indicator_of_mem (hKU hx) _
  have hf₀K : ∀ x ∈ closedBall z₀ R, f₀ x = v 0 x := fun x hx => Set.indicator_of_mem (hKU hx) _
  obtain ⟨Mv, hMv⟩ := hf₀b _ (isCompact_closedBall z₀ R) hKU
  obtain ⟨Mw, hMw⟩ := hfb 0 _ (isCompact_closedBall z₀ R) hKU
  have hfbd : ∀ k, ∀ x ∈ closedBall z₀ R, |f k x| ≤ max Mv Mw := by
    intro k x hx
    have h1 : v 0 x ≤ w k 0 x := max_le_max le_rfl (hle k 0 x (hKU hx))
    have h2 : w k 0 x ≤ w 0 0 x := max_le_max le_rfl (hanti 0 x (hKU hx) (Nat.zero_le k))
    have h3 := hMv x hx
    have h4 := hMw x hx
    rw [hf₀K x hx] at h3
    rw [hfK 0 x hx] at h4
    rw [hfK k x hx, abs_le]
    rw [abs_le] at h3 h4
    constructor <;> linarith [le_max_left Mv Mw, le_max_right Mv Mw]
  have husc : ∀ k, UpperSemicontinuousOn (f k) (closedBall z₀ R) := fun k =>
    upperSemicontinuousOn_congr ((upperSemicontinuousOn_of_isLocallyBoundedPshOn (hw k 0)).mono
      hKU)
      fun x hx => (hfK k x hx).symm
  have hantiK : ∀ x ∈ closedBall z₀ R, Antitone fun k => f k x := fun x hx i j hij => by
    simp only [hfK _ x hx]
    exact max_le_max le_rfl (hanti 0 x (hKU hx) hij)
  have hlimK : ∀ x ∈ closedBall z₀ R, Tendsto (fun k => f k x) atTop (𝓝 (f₀ x)) := fun x hx => by
    simp only [hfK _ x hx, hf₀K x hx]
    exact tendsto_const_nhds.max (hlim 0 x (hKU hx))
  -- the order unit and the test forms `c χ ω₀^m ∓ φ γ`
  obtain ⟨C, hC0, hCm, hCp⟩ := exists_orderUnit γ.2
  obtain ⟨Φ, hΦ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hΦ' : ∀ x, |φ x| ≤ Φ := fun x => by simpa [Real.norm_eq_abs] using hΦ x
  have hΦ0 : 0 ≤ Φ := (abs_nonneg _).trans (hΦ' z₀)
  set c := Φ * C with hc_def
  have hc0 : 0 ≤ c := mul_nonneg hΦ0 hC0
  have hω : formPower (kahlerForm n) m ∈ spCone m :=
    formPower_mem_spCone isSemipositiveOneOne_kahlerForm m
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ b, c * A₀ + -s * mulBorel S₀ f₀ γ φ < b →
      ∀ᶠ k in atTop, c * Ak k + -s * mulBorel (S k) (f k) γ φ < b := by
    intro s hs b hb
    set γs : Fin 2 → formSpan n m := ![kahlerPower n m, γ] with hγs
    set φs : Fin 2 → 𝓓(U, ℝ) := ![c • χ', (-s) • φ] with hφs
    have hpos : ∀ x, ∑ i, φs i x • (γs i : RealForm n (2 * m)) ∈ spCone m := by
      intro x
      have e : ∑ i, φs i x • (γs i : RealForm n (2 * m)) =
          (c * χ x) • formPower (kahlerForm n) m + (-s * φ x) • (γ : RealForm n (2 * m)) := by
        rw [Fin.sum_univ_two]
        simp only [hγs, hφs, Matrix.cons_val_zero, Matrix.cons_val_one,
          FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hχ'_apply]
        rfl
      rw [e]
      by_cases hx : φ x = 0
      · rw [hx, mul_zero, zero_smul, add_zero]
        exact smul_mem_spCone hω (mul_nonneg hc0 (hχ01 x).1)
      · have hχx : χ x = 1 := hχ1 x (Or.inr (subset_tsupport _ hx))
        have hst : |s * φ x| ≤ Φ := by
          rcases hs with rfl | rfl <;> simpa [abs_mul] using hΦ' x
        rw [hχx, mul_one]
        simpa only [hc_def, neg_mul] using scaledForm_sub_mem_spCone hω hC0 hCm hCp hst
    have hφK : ∀ i, ∀ x ∉ closedBall z₀ R, φs i x = 0 := by
      intro i x hx
      have hxb : x ∉ ball z₀ R := fun h => hx (ball_subset_closedBall h)
      fin_cases i
      · simp [hφs, hχ'_apply, hχ0 x hxb]
      · simp [hφs, image_eq_zero_of_notMem_tsupport fun h => hxb (hφB h)]
    have hfin : ∀ k, IsFiniteMeasure (formMeasure (hS k).1 γs φs) := fun k =>
      isFiniteMeasure_formMeasure (isCompact_closedBall z₀ R) hKU (hS k).1 hφK
    have hfin₀ : IsFiniteMeasure (formMeasure hS₀.1 γs φs) :=
      isFiniteMeasure_formMeasure (isCompact_closedBall z₀ R) hKU hS₀.1 hφK
    have hsum : ∀ (P : LocalProductCurrent n U m) (hP : IsPositive P) (F : E → ℝ),
        Measurable F → IsLocallyBoundedOn F U →
        c * mulBorel P F (kahlerPower n m) χ' + -s * mulBorel P F γ φ =
          ∫ x, F x ∂formMeasure hP γs φs := by
      intro P hP F hF hFb
      rw [← sum_mulBorel_eq_integral_formMeasure hP hpos hF hFb, Fin.sum_univ_two]
      simp only [hγs, hφs, Matrix.cons_val_zero, Matrix.cons_val_one, map_smul,
        smul_eq_mul]
    rw [hsum S₀ hS₀.1 f₀ hf₀m hf₀b] at hb
    have hev := eventually_integral_lt_of_antitone (isCompact_closedBall z₀ R)
      (nonempty_closedBall.mpr hR.le)
      (fun k => formMeasure_compl (isCompact_closedBall z₀ R) (hS k).1 hφK)
      (formMeasure_compl (isCompact_closedBall z₀ R) hS₀.1 hφK)
      (fun g hg => tendsto_integral_formMeasure (fun k => (hS k).1) hS₀.1 hIH hpos hg) hfm husc
      hantiK hlimK hfbd hb
    filter_upwards [hev] with k hk
    rw [hsum (S k) (hS k).1 (f k) (hfm k) (hfb k)]
    exact hk
  -- the squeeze
  rw [tendsto_order]
  refine ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
  · have hev := key 1 (Or.inl rfl) (c * A₀ + -1 * mulBorel S₀ f₀ γ φ +
      (mulBorel S₀ f₀ γ φ - a')) (by linarith)
    filter_upwards [hev] with k hk
    have := mul_le_mul_of_nonneg_left (hlow k) hc0
    linarith
  · have hev := key (-1) (Or.inr rfl) (c * A₀ + - -1 * mulBorel S₀ f₀ γ φ +
      (b' - mulBorel S₀ f₀ γ φ)) (by linarith)
    filter_upwards [hev] with k hk
    have := mul_le_mul_of_nonneg_left (hlow k) hc0
    linarith

end Squeeze

/-! ### The decreasing continuity theorem -/

section Decreasing

open Metric

/-- Adding a real constant preserves local boundedness and plurisubharmonicity. -/
theorem isLocallyBoundedPshOn_add_const {f : E → ℝ} (hf : IsLocallyBoundedPshOn U f) (c : ℝ) :
    IsLocallyBoundedPshOn U fun z => f z + c := by
  refine ⟨?_, fun z hz => ?_⟩
  · have hc : PlurisubharmonicOn (fun _ : E => ((c : ℝ) : EReal)) U :=
      fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) x
    simpa only [EReal.coe_add] using hf.1.add hc
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    exact ⟨V, hzV, hVΩ, C + |c|, fun y hy => (abs_add_le _ _).trans (by linarith [hC y hy])⟩

theorem exists_bound_on_compact {f : E → ℝ} (hf : IsLocallyBoundedPshOn U f) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ M, ∀ x ∈ K, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isLocallyBoundedOn_indicator hf K hK hKU
  exact ⟨M, fun x hx => by simpa [Set.indicator_of_mem (hKU hx)] using hM x hx⟩

variable (n) in
/-- **Decreasing continuity of the recursive product** with `q` potentials: on every open `U`, for
`T` positive closed and locally bounded PSH `u_j^k ↓ u_j`, `B(u^k; T) → B(u; T)` weakly. -/
def DecreasingContinuity (q : ℕ) : Prop :=
  ∀ (U : Opens (ComplexModel n)) (m : ℕ) (T : LocalProductCurrent n U (m + q)), IsPositive T →
    IsClosedAny (m + q) T → ∀ (u : ℕ → Fin q → ComplexModel n → ℝ)
    (u₀ : Fin q → ComplexModel n → ℝ), (∀ k i, IsLocallyBoundedPshOn U (u k i)) →
    (∀ i, IsLocallyBoundedPshOn U (u₀ i)) →
    (∀ i, ∀ z ∈ (U : Set (ComplexModel n)), Antitone fun k => u k i z) →
    (∀ i, ∀ z ∈ (U : Set (ComplexModel n)), Tendsto (fun k => u k i z) atTop (𝓝 (u₀ i z))) →
    WeakTendsto (fun k => btProduct q m (u k) T) (btProduct q m u₀ T)

/-- **The weighted step** (`bt:decreasing-continuity`): decreasing continuity for `q` potentials
gives `u_0^k B(u_1^k, …, u_q^k; T) → u_0 B(u_1, …, u_q; T)` weakly. -/
theorem weakTendsto_mulBorel_of_decreasingContinuity {q : ℕ} (hP : DecreasingContinuity n q)
    (U : Opens (ComplexModel n)) (m : ℕ) (T : LocalProductCurrent n U (m + q))
    (hT : IsPositive T) (hTc : IsClosedAny (m + q) T) (u : ℕ → Fin (q + 1) → E → ℝ)
    (u₀ : Fin (q + 1) → E → ℝ) (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i))
    (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hanti : ∀ i, ∀ z ∈ (U : Set E), Antitone fun k => u k i z)
    (hlim : ∀ i, ∀ z ∈ (U : Set E), Tendsto (fun k => u k i z) atTop (𝓝 (u₀ i z))) :
    WeakTendsto (fun k => mulBorel (btProduct q m (Fin.tail (u k)) T)
        ((U : Set E).indicator (u k 0)))
      (mulBorel (btProduct q m (Fin.tail u₀) T) ((U : Set E).indicator (u₀ 0))) := by
  classical
  refine weakTendsto_of_local fun x hx => ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  set R := r / 2 with hR_def
  have hR : 0 < R := by positivity
  have hBU : closedBall x R ⊆ (U : Set E) :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hle : ∀ k i, ∀ z ∈ (U : Set E), u₀ i z ≤ u k i z := fun k i z hz =>
    (hanti i z hz).le_of_tendsto (hlim i z hz) k
  -- normalization constants
  choose M hM using fun i => exists_bound_on_compact (hu 0 i) (isCompact_closedBall x R) hBU
  choose L hL using fun i => exists_bound_on_compact (hu₀ i) (isCompact_closedBall x R) hBU
  set c : ℝ := 1 + ∑ i, |M i| with hc_def
  set L' : ℝ := ∑ i, |L i| with hL'_def
  have hMi : ∀ i, |M i| ≤ ∑ j, |M j| := fun i =>
    Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hLi : ∀ i, |L i| ≤ L' := fun i =>
    Finset.single_le_sum (f := fun j => |L j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  set a : ℕ → Fin (q + 1) → E → ℝ := fun k i z => u k i z + -c with ha_def
  set a₀ : Fin (q + 1) → E → ℝ := fun i z => u₀ i z + -c with ha₀_def
  have ha : ∀ k i, IsLocallyBoundedPshOn U (a k i) := fun k i =>
    isLocallyBoundedPshOn_add_const (hu k i) (-c)
  have ha₀ : ∀ i, IsLocallyBoundedPshOn U (a₀ i) := fun i =>
    isLocallyBoundedPshOn_add_const (hu₀ i) (-c)
  have ha1 : ∀ k i, ∀ z ∈ closedBall x R, a k i z ≤ -1 := fun k i z hz => by
    have h1 := hanti i z (hBU hz) (Nat.zero_le k)
    have h2 := (le_abs_self _).trans (hM i z hz)
    have h3 := (le_abs_self (M i)).trans (hMi i)
    simp only [ha_def]
    linarith
  have hlow : ∀ k i, ∀ z ∈ closedBall x R, -(L' + c) ≤ a k i z := fun k i z hz => by
    have h1 := hle k i z (hBU hz)
    have h2 := neg_abs_le (u₀ i z)
    have h3 := (hL i z hz).trans ((le_abs_self (L i)).trans (hLi i))
    simp only [ha_def]
    linarith
  have hlow₀ : ∀ i, ∀ z ∈ closedBall x R, -(L' + c) ≤ a₀ i z := fun i z hz => by
    have h2 := neg_abs_le (u₀ i z)
    have h3 := (hL i z hz).trans ((le_abs_self (L i)).trans (hLi i))
    simp only [ha₀_def]
    linarith
  have hantia : ∀ i, ∀ z ∈ (U : Set E), Antitone fun k => a k i z := fun i z hz k l hkl => by
    simp only [ha_def]
    linarith [hanti i z hz hkl]
  have hlima : ∀ i, ∀ z ∈ (U : Set E), Tendsto (fun k => a k i z) atTop (𝓝 (a₀ i z)) :=
    fun i z hz => (hlim i z hz).add_const _
  -- the collar modification, unchanged near `x`
  obtain ⟨A, hA, V', hV'o, hV'K, hV'⟩ := collarMax_eq_of_le hR (isCompact_closedBall x (R / 2))
    (closedBall_subset_ball (by linarith)) (L' + c)
  set w : ℕ → Fin (q + 1) → E → ℝ := fun k i => collarMax A x R (a k i) with hw_def
  set v : Fin (q + 1) → E → ℝ := fun i => collarMax A x R (a₀ i) with hv_def
  have hw : ∀ k i, IsLocallyBoundedPshOn U (w k i) := fun k i =>
    isLocallyBoundedPshOn_collarMax hA.le x R (ha k i)
  have hv : ∀ i, IsLocallyBoundedPshOn U (v i) := fun i =>
    isLocallyBoundedPshOn_collarMax hA.le x R (ha₀ i)
  let W : Opens (ComplexModel n) := ⟨V' ∩ ball x R, hV'o.inter isOpen_ball⟩
  have hWU : W ≤ U := fun z hz => hBU (ball_subset_closedBall hz.2)
  have hxW : x ∈ W := ⟨hV'K (mem_closedBall_self (by positivity)), mem_ball_self hR⟩
  have hwW : ∀ k i, ∀ z ∈ (W : Set E), u k i z = w k i z + c := fun k i z hz => by
    change u k i z = collarMax A x R (a k i) z + c
    rw [hV' A le_rfl (a k i) z hz.1 (hlow k i z (ball_subset_closedBall hz.2))]
    simp only [ha_def]
    ring
  have hvW : ∀ i, ∀ z ∈ (W : Set E), u₀ i z = v i z + c := fun i z hz => by
    change u₀ i z = collarMax A x R (a₀ i) z + c
    rw [hV' A le_rfl (a₀ i) z hz.1 (hlow₀ i z (ball_subset_closedBall hz.2))]
    simp only [ha₀_def]
    ring
  -- the inductive hypothesis for the modified families
  have hIH : WeakTendsto (fun k => btProduct q m (fun i => collarMax A x R (a k i.succ)) T)
      (btProduct q m (fun i => collarMax A x R (a₀ i.succ)) T) :=
    hP U m T hT hTc (fun k i => w k i.succ) (fun i => v i.succ) (fun k i => hw k _)
      (fun i => hv _) (fun i z hz k l hkl => max_le_max le_rfl (hantia _ z hz hkl))
      fun i z hz => tendsto_const_nhds.max (hlima _ z hz)
  refine ⟨W, hWU, hxW, fun γ ψ => ?_⟩
  -- the values on `ψ`
  have hdec : ∀ (b : Fin (q + 1) → E → ℝ) (b' : Fin (q + 1) → E → ℝ),
      (∀ i, IsLocallyBoundedPshOn U (b i)) → (∀ i, IsLocallyBoundedPshOn U (b' i)) →
      (∀ i, ∀ z ∈ (W : Set E), b i z = b' i z + c) →
      mulBorel (btProduct q m (Fin.tail b) T) ((U : Set E).indicator (b 0)) γ (extTest hWU ψ) =
        mulBorel (btProduct q m (Fin.tail b') T) ((U : Set E).indicator (b' 0)) γ
            (extTest hWU ψ) + c * btProduct q m (Fin.tail b') T γ (extTest hWU ψ) := by
    intro b b' hb hb' hbb'
    have hPb := (isPositive_btProduct q m (Fin.tail b) T hT hTc fun i => hb _).1
    have hPb' := (isPositive_btProduct q m (Fin.tail b') T hT hTc fun i => hb' _).1
    refine mulBorel_extTest_eq hWU hPb hPb'
      (restrict_btProduct_eq hWU q m (Fin.tail b) (Fin.tail b') (fun _ => c) T hT hTc
        (fun i => hb _) (fun i => hb' _) fun i z hz => hbb' _ z hz)
      (measurable_indicator_of_isLocallyBoundedPshOn (hb 0)) (isLocallyBoundedOn_indicator (hb 0))
      (measurable_indicator_of_isLocallyBoundedPshOn (hb' 0))
      (isLocallyBoundedOn_indicator (hb' 0)) (fun z hz => ?_) γ ψ
    rw [Set.indicator_of_mem (hWU hz), Set.indicator_of_mem (hWU hz), hbb' 0 z hz]
  simp only [hdec (u _) (w _) (hu _) (hw _) (hwW _), hdec u₀ v hu₀ hv hvW]
  have hsupp : tsupport (extTest hWU ψ : E → ℝ) ⊆ ball x R := by
    have hφe : (extTest hWU ψ : E → ℝ) = ψ := funext (extTest_apply hWU ψ)
    rw [hφe]
    exact ψ.tsupport_subset.trans inter_subset_right
  exact (tendsto_mulBorel_collarMax hR hA hBU T hT hTc a a₀ ha ha₀ ha1 hantia hlima hIH γ
    (extTest hWU ψ) hsupp).add ((hIH γ (extTest hWU ψ)).const_mul c)

/-- **Decreasing continuity of the recursive Bedford--Taylor product** (`bt:decreasing-continuity`,
`demailly-cadg:III.3.7`), for every number of potentials, by induction: the product with `q + 1`
potentials is `dd^c` of the weighted product with `q` (`btProduct_succ_eq_ddcMul`). -/
theorem decreasingContinuity : ∀ q, DecreasingContinuity n q
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ _ => tendsto_const_nhds
  | q + 1 => fun U m T hT hTc u u₀ hu hu₀ hanti hlim => by
    have hmq : m + (q + 1) = m + 1 + q := by omega
    have e : ∀ v : Fin (q + 1) → E → ℝ, btProduct (q + 1) m v T =
        ddc (mulBorel (btProduct q (m + 1) (Fin.tail v) (castLPC hmq T))
          ((U : Set E).indicator (v 0))) := fun v =>
      btProduct_succ_eq_ddcMul q m v T _ (heq_castLPC hmq T)
    simp only [e]
    exact weakTendsto_ddc (weakTendsto_mulBorel_of_decreasingContinuity (decreasingContinuity q)
      U (m + 1) (castLPC hmq T) (isPositive_castLPC hmq hT) (isClosedAny_castLPC hmq hTc) u u₀ hu
      hu₀ hanti hlim)

/-- **Continuity under decreasing sequences, product form** (`bt:decreasing-continuity`): for `T`
positive closed of bidimension `(m + q, m + q)` and locally bounded PSH `u_j^k ↓ u_j` on `U`,
`B(u_1^k, …, u_q^k; T) → B(u_1, …, u_q; T)` weakly. -/
theorem weakTendsto_btProduct_of_antitone (q m : ℕ) (T : LocalProductCurrent n U (m + q))
    (hT : IsPositive T) (hTc : IsClosedAny (m + q) T) (u : ℕ → Fin q → E → ℝ)
    (u₀ : Fin q → E → ℝ) (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i))
    (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hanti : ∀ i, ∀ z ∈ (U : Set E), Antitone fun k => u k i z)
    (hlim : ∀ i, ∀ z ∈ (U : Set E), Tendsto (fun k => u k i z) atTop (𝓝 (u₀ i z))) :
    WeakTendsto (fun k => btProduct q m (u k) T) (btProduct q m u₀ T) :=
  decreasingContinuity q U m T hT hTc u u₀ hu hu₀ hanti hlim

/-- **Continuity under decreasing sequences, weighted form** (`bt:decreasing-continuity`):
`u_0^k B(u_1^k, …, u_q^k; T) → u_0 B(u_1, …, u_q; T)` weakly (the weight extended by zero off
    `U`). -/
theorem weakTendsto_mulBorel_btProduct_of_antitone (q m : ℕ)
    (T : LocalProductCurrent n U (m + q)) (hT : IsPositive T) (hTc : IsClosedAny (m + q) T)
    (u : ℕ → Fin (q + 1) → E → ℝ) (u₀ : Fin (q + 1) → E → ℝ)
    (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i)) (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hanti : ∀ i, ∀ z ∈ (U : Set E), Antitone fun k => u k i z)
    (hlim : ∀ i, ∀ z ∈ (U : Set E), Tendsto (fun k => u k i z) atTop (𝓝 (u₀ i z))) :
    WeakTendsto (fun k => mulBorel (btProduct q m (Fin.tail (u k)) T)
        ((U : Set E).indicator (u k 0)))
      (mulBorel (btProduct q m (Fin.tail u₀) T) ((U : Set E).indicator (u₀ 0))) :=
  weakTendsto_mulBorel_of_decreasingContinuity (decreasingContinuity q) U m T hT hTc u u₀ hu hu₀
    hanti hlim

end Decreasing

/-! ### Monge--Ampère measures -/

section MongeAmpere

/-- **Weak convergence of positive currents gives vague convergence of their trace measures**:
`∫ g dσ_{S_k} → ∫ g dσ_S` for every continuous `g` with compact support in `U`. -/
theorem tendsto_integral_traceMeasure_of_weakTendsto {m : ℕ} {S : ℕ → LocalProductCurrent n U m}
    {S₀ : LocalProductCurrent n U m} (hS : ∀ k, IsPositive (S k)) (hS₀ : IsPositive S₀)
    (hconv : WeakTendsto S S₀) {g : E → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) :
    Tendsto (fun k => ∫ x, g x ∂(hS k).traceMeasure) atTop (𝓝 (∫ x, g x ∂hS₀.traceMeasure)) := by
  obtain ⟨L, hL, hgL, hLU⟩ := exists_compact_between hgc U.isOpen hgU
  obtain ⟨χ, hχ, hχ1, hχL, -⟩ := exists_cutoff_unit hgc isOpen_interior hgL
  let χ' : 𝓓(U, ℝ) :=
    { toFun := χ, contDiff' := hχ, hasCompactSupport' := hL.of_isClosed_subset
        (isClosed_tsupport χ) (hχL.trans interior_subset),
      tsupport_subset' := (hχL.trans interior_subset).trans hLU }
  have hgb : IsLocallyBoundedOn g U := fun K hK _ => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  have e : ∀ (P : LocalProductCurrent n U m) (hP : IsPositive P),
      ∫ x, g x ∂hP.traceMeasure = mulBorel P g (kahlerPower n m) χ' := by
    intro P hP
    rw [integral_eq_mulBorel_kahlerPower hP hg.measurable hgb χ']
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x = χ x * g x
    by_cases hx : x ∈ tsupport g
    · rw [hχ1 x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  simp only [e]
  exact weakTendsto_mulBorel hS hconv (fun _ => hg.measurable) (fun _ => hgb) hg.measurable
    hg.continuousOn (fun u hu x _ => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ =>
      refl_mem_uniformity hu⟩) (kahlerPower n m) χ'

/-- A smooth PSH function on `U` is locally bounded PSH on `U`. -/
theorem isLocallyBoundedPshOn_of_isSmoothPshOn {f : E → ℝ} (hf : IsSmoothPshOn U f) :
    IsLocallyBoundedPshOn U f := by
  refine ⟨hf.2.1, fun z hz => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen z hz
  have hcb : Metric.closedBall z (r / 2) ⊆ (U : Set E) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
    (hf.1.continuousOn.mono hcb)
  exact ⟨⟨Metric.ball z (r / 2), Metric.isOpen_ball⟩, Metric.mem_ball_self (by linarith),
    fun w hw => hcb (Metric.ball_subset_closedBall hw), C, fun w hw => by
      simpa [Real.norm_eq_abs] using hC w (Metric.ball_subset_closedBall hw)⟩

/-- **The locally bounded Monge--Ampère measure is the limit for every decreasing sequence**
(`bt:decreasing-continuity`, last assertion): for locally bounded PSH `u_k ↓ u` on `U`,
`(dd^c u_k)^n = B(u_k, …, u_k; [1]) → (dd^c u)^n` weakly as currents and vaguely as Radon measures
(trace measures against continuous functions with compact support in `U`). -/
theorem tendsto_integral_mongeAmpere_of_antitone (f : ℕ → E → ℝ) (u : E → ℝ)
    (hf : ∀ k, IsLocallyBoundedPshOn U (f k)) (hu : IsLocallyBoundedPshOn U u)
    (hanti : ∀ z ∈ (U : Set E), Antitone fun k => f k z)
    (hlim : ∀ z ∈ (U : Set E), Tendsto (fun k => f k z) atTop (𝓝 (u z))) :
    WeakTendsto (fun k => btProduct n 0 (fun _ => f k) (oneCurrentOf (U := U) (Nat.zero_add n)))
        (btProduct n 0 (fun _ => u) (oneCurrentOf (U := U) (Nat.zero_add n))) ∧
      ∀ (hP : ∀ k, IsPositive (btProduct n 0 (fun _ => f k)
          (oneCurrentOf (U := U) (Nat.zero_add n))))
        (hP₀ : IsPositive (btProduct n 0 (fun _ => u) (oneCurrentOf (U := U) (Nat.zero_add n))))
        {g : E → ℝ}, Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        Tendsto (fun k => ∫ x, g x ∂(hP k).traceMeasure) atTop
          (𝓝 (∫ x, g x ∂hP₀.traceMeasure)) := by
  have hconv := weakTendsto_btProduct_of_antitone n 0 (oneCurrentOf (U := U) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (fun k _ => f k) (fun _ => u)
    (fun k _ => hf k) (fun _ => hu) (fun _ => hanti) (fun _ => hlim)
  exact ⟨hconv, fun hP hP₀ g hg hgc hgU =>
    tendsto_integral_traceMeasure_of_weakTendsto hP hP₀ hconv hg hgc hgU⟩

/-- In particular for every decreasing smooth PSH approximation (`IsDecreasingApproximation`). -/
theorem tendsto_integral_mongeAmpere_of_isDecreasingApproximation {u : E → ℝ}
    (hu : IsLocallyBoundedPshOn U u) {f : ℕ → E → ℝ} (hf : IsDecreasingApproximation U u f) :
    WeakTendsto (fun k => btProduct n 0 (fun _ => f k) (oneCurrentOf (U := U) (Nat.zero_add n)))
        (btProduct n 0 (fun _ => u) (oneCurrentOf (U := U) (Nat.zero_add n))) ∧
      ∀ (hP : ∀ k, IsPositive (btProduct n 0 (fun _ => f k)
          (oneCurrentOf (U := U) (Nat.zero_add n))))
        (hP₀ : IsPositive (btProduct n 0 (fun _ => u) (oneCurrentOf (U := U) (Nat.zero_add n))))
        {g : E → ℝ}, Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        Tendsto (fun k => ∫ x, g x ∂(hP k).traceMeasure) atTop
          (𝓝 (∫ x, g x ∂hP₀.traceMeasure)) :=
  tendsto_integral_mongeAmpere_of_antitone f u
    (fun k => isLocallyBoundedPshOn_of_isSmoothPshOn (hf.1 k)) hu hf.2.1 hf.2.2

end MongeAmpere

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
