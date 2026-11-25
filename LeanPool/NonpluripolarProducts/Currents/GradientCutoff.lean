/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Currents.GradientChainRule

/-!
# The cutoff estimate for bounded psh functions against closed positive currents

Source: Xia, *Foundations of pluripotential theory*, `lem:bounded-psh-current-chain-rule`
(`eq:current-gradient-cauchy-schwarz`, `eq:bounded-current-chain-rule`) and the gradient bound
of `thm:nonpluripolar-product-closed`.

For a positive closed current `T` of bidimension `(q+1,q+1)` on `U ⊆ ℂⁿ`, a constant strongly
positive `(q,q)`-form `γ`, a real linear form `ℓ`, test functions `φ, τ` with `τ ≥ 0` and
`τ = 1` on the support of `φ`, a smooth `ζ : ℝ → ℝ` and `t > 0`:

* `abs_sum_integral_le_of_contDiff` — for smooth `g ≥ 0`, psh at the points of the support of
  `τ`,
  `|∑_a ∫ ∂_a φ ζ(g) L_x(γ ∧ Π₁₁(e^a ∧ ℓ)) dσ_T| ≤ (t/4) ∫ g² A_τ dσ_T
     + (1/2t) ∫ φ² ζ'(g)² L_x(Q(η_ℓ, η_ℓ)) dσ_T`:
  the chain rule `d(ζ(g) T) = ζ'(g) dg ∧ T`, the pointwise Cauchy–Schwarz inequality for the
  density matrix of `γ ∧ T` and the gradient energy bound;
* `abs_sum_integral_le` — **the same estimate for a locally bounded psh `w ≥ 0`** on an open
  `V ⊇ supp τ` (FPT `eq:current-gradient-cauchy-schwarz` with `a = ζ'(w)` and the gradient bound
  `∫ τ E_Θ(w) ≤ ½ ∫ w² dd^c τ ∧ Θ`): smooth psh `w_j ↓ w` near `supp τ` (TN's
  `HolomorphicPullback.exists_decreasingMollifierApproximation`), made globally smooth by a cutoff,
  and dominated convergence in the three integrals.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Currents.Gradient

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

variable {U : Opens (ComplexModel n)} {q : ℕ} {T : LocalProductCurrent n U (q + 1)}

/-- `φ² · c · L_x(β)` is integrable for a test function `φ` and `c` continuous. -/
theorem integrable_sq_mul_mul_densityForm (hT : IsPositive T) (φ : 𝓓(U, ℝ)) {c : (ComplexModel n)
    → ℝ}
    (hc : Measurable c) (hcb : ∃ M, ∀ x ∈ tsupport φ, |c x| ≤ M) (β : formSpan n (q + 1)) :
    Integrable (fun x => φ x ^ 2 * c x * densityForm hT x β) hT.traceMeasure := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT β
  obtain ⟨M, hM⟩ := hcb
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have h := hT.integrable_mul_of_bounded (ψ := φ) (w := fun x => φ x * c x * densityForm hT x β)
    φ.continuous φ.hasCompactSupport φ.tsupport_subset
    ((φ.continuous.measurable.mul hc).mul (measurable_densityForm hT β)).aestronglyMeasurable
    ⟨Cφ * M * C, fun x hx => by
      have h1 : |φ x| ≤ Cφ := by simpa [Real.norm_eq_abs] using hCφ x
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul h1 (hM x hx) (abs_nonneg _) ((abs_nonneg _).trans h1))
        (hC x) (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans h1)
          ((abs_nonneg _).trans (hM x hx)))⟩
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- **The cutoff estimate for smooth functions.** -/
theorem abs_sum_integral_le_of_contDiff (hT : IsPositive T) (hTc : IsClosedCurrent T)
    {γ : formSpan n q} (hγ : γ ∈ posCone n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (φ τ : 𝓓(U, ℝ))
    (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x ∈ tsupport φ, τ x = 1) {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    {g : (ComplexModel n) → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x ∈ tsupport τ, 0 ≤ g x)
    (hgp : ∀ x ∈ tsupport τ, IsSemipositiveOneOne (smoothDDC g x)) {t : ℝ} (ht : 0 < t) :
    |∑ a, ∫ x, dTest (realBasis n a) φ x * (ζ (g x) * densityForm hT x (testWedge γ ℓ a))
        ∂hT.traceMeasure| ≤
      t / 4 * ∫ x, g x ^ 2 * hessWeight hT γ τ x ∂hT.traceMeasure +
        1 / (2 * t) * ∫ x, φ x ^ 2 * deriv ζ (g x) ^ 2 *
          densityForm hT x (quadForm q γ (dualCoeff ℓ) (dualCoeff ℓ)) ∂hT.traceMeasure := by
  rw [sum_integral_dTest_mul_comp hT hTc γ ℓ φ hζ hg]
  set σ := hT.traceMeasure
  set η := dualCoeff ℓ
  have hζ' : Continuous (deriv ζ) := hζ.continuous_deriv (by simp)
  set R₁ : (ComplexModel n) → ℝ := fun x => τ x * densityForm hT x (quadForm q γ (gradVec g x)
    (gradVec g x))
    with hR₁def
  set R₂ : (ComplexModel n) → ℝ := fun x => φ x ^ 2 * deriv ζ (g x) ^ 2 * densityForm hT x
    (quadForm q γ η η)
    with hR₂def
  have hR₁ : Integrable R₁ σ := integrable_mul_densityForm_quadForm_grad hT γ τ hg
  have hR₂ : Integrable R₂ σ := by
    obtain ⟨M, hM⟩ := (φ.hasCompactSupport.isCompact).exists_bound_of_continuousOn
      ((hζ'.comp hg.continuous).pow 2).continuousOn
    exact integrable_sq_mul_mul_densityForm hT φ ((hζ'.comp hg.continuous).pow 2).measurable
      ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩ _
  have hpt : ∀ᵐ x ∂σ, |φ x * deriv ζ (g x) * densityForm hT x (quadForm q γ (gradVec g x) η)| ≤
      t / 2 * R₁ x + 1 / (2 * t) * R₂ x := by
    filter_upwards [ae_two_mul_abs_densityForm_quadForm_le hT hγ,
      ae_densityForm_quadForm_nonneg hT hγ] with x hcs hnn
    by_cases hφx : φ x = 0
    · rw [hφx, zero_mul, zero_mul, abs_zero]
      have h1 : 0 ≤ R₁ x := mul_nonneg (hτ0 x) (hnn _)
      have h2 : 0 ≤ R₂ x := by
        simp only [hR₂def]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hnn _)
      have h3 : 0 < 1 / (2 * t) := by positivity
      nlinarith
    · have hτx : τ x = 1 := hτ1 x (subset_tsupport _ hφx)
      set s := φ x * deriv ζ (g x) with hs
      have key := hcs (gradVec g x) (s • η) t ht
      have hQ : densityForm hT x (quadForm q γ (s • η) (s • η)) =
          s ^ 2 * densityForm hT x (quadForm q γ η η) := by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      have hQ' : densityForm hT x (quadForm q γ (gradVec g x) (s • η)) =
          s * densityForm hT x (quadForm q γ (gradVec g x) η) := by
        simp only [map_smul, smul_eq_mul]
      rw [hQ, hQ'] at key
      simp only [hR₁def, hR₂def, hτx, one_mul]
      have e : s ^ 2 * densityForm hT x (quadForm q γ η η) / t =
          2 * (1 / (2 * t) * (φ x ^ 2 * deriv ζ (g x) ^ 2 * densityForm hT x (quadForm q γ η η)))
            := by
        rw [hs]
        field_simp
      rw [e] at key
      linarith
  have hE := integral_mul_densityForm_quadForm_grad_le hT hTc hγ τ hτ0 hg hg0 hgp
  calc |∫ x, φ x * deriv ζ (g x) * densityForm hT x (quadForm q γ (gradVec g x) η) ∂σ| ≤
        ∫ x, |φ x * deriv ζ (g x) * densityForm hT x (quadForm q γ (gradVec g x) η)| ∂σ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, (t / 2 * R₁ x + 1 / (2 * t) * R₂ x) ∂σ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          ((hR₁.const_mul _).add (hR₂.const_mul _)) hpt
    _ = t / 2 * ∫ x, R₁ x ∂σ + 1 / (2 * t) * ∫ x, R₂ x ∂σ := by
        rw [integral_add (hR₁.const_mul _) (hR₂.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        have ht2 : 0 ≤ t / 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hE ht2]

/-- **The cutoff estimate for locally bounded psh functions** (FPT
`eq:current-gradient-cauchy-schwarz` with `a = ζ'(w)`, combined with the gradient bound of
`thm:nonpluripolar-product-closed`): for `w ≥ 0` locally bounded psh on an open `V ⊇ supp τ`,
`|∑_a ∫ ∂_a φ ζ(w) L_x(γ ∧ Π₁₁(e^a ∧ ℓ)) dσ_T| ≤ (t/4) ∫ w² A_τ dσ_T
   + (1/2t) ∫ φ² ζ'(w)² L_x(Q(η_ℓ, η_ℓ)) dσ_T`. -/
theorem abs_sum_integral_le (hT : IsPositive T) (hTc : IsClosedCurrent T)
    {γ : formSpan n q} (hγ : γ ∈ posCone n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (φ τ : 𝓓(U, ℝ))
    (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x ∈ tsupport φ, τ x = 1) {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    {V : Opens (ComplexModel n)} (hτV : tsupport τ ⊆ V) {w : (ComplexModel n) → ℝ} (hw :
      IsLocallyBoundedPshOn V w)
    (hw0 : ∀ x ∈ V, 0 ≤ w x) {t : ℝ} (ht : 0 < t) :
    |∑ a, ∫ x, dTest (realBasis n a) φ x * (ζ (w x) * densityForm hT x (testWedge γ ℓ a))
        ∂hT.traceMeasure| ≤
      t / 4 * ∫ x, w x ^ 2 * hessWeight hT γ τ x ∂hT.traceMeasure +
        1 / (2 * t) * ∫ x, φ x ^ 2 * deriv ζ (w x) ^ 2 *
          densityForm hT x (quadForm q γ (dualCoeff ℓ) (dualCoeff ℓ)) ∂hT.traceMeasure := by
  set σ := hT.traceMeasure
  set η := dualCoeff ℓ
  set K₁ := tsupport (τ : (ComplexModel n) → ℝ) with hK₁def
  have hK₁ : IsCompact K₁ := τ.hasCompactSupport
  have hφK : tsupport (φ : (ComplexModel n) → ℝ) ⊆ K₁ := fun x hx =>
    subset_tsupport _ (by rw [Function.mem_support, hτ1 x hx]; exact one_ne_zero)
  obtain ⟨A, hAo, hK₁A, hAV, hAc⟩ := exists_open_between_and_isCompact_closure hK₁ V.isOpen hτV
  let A' : Opens (ComplexModel n) := ⟨A, hAo⟩
  have hrel : RelativelyCompactIn A' V := ⟨hAc, hAV⟩
  obtain ⟨f, hfs, hfanti, hflim⟩ :=
    HolomorphicPullback.exists_decreasingMollifierApproximation hw hrel
  obtain ⟨χ, hχ, hχ1, hχA⟩ := exists_cutoff hK₁ hAo hK₁A
  set G : ℕ → (ComplexModel n) → ℝ := fun j x => χ x * f j x with hGdef
  have hGs : ∀ j, ContDiff ℝ ∞ (G j) := fun j =>
    contDiff_mul_of_tsupport_subset hAo hχ hχA (hfs j).1
  have hGK : ∀ j, ∀ x ∈ K₁, G j =ᶠ[𝓝 x] f j := fun j x hx =>
    (hχ1 x hx).mono fun y hy => by simp [hGdef, hy]
  have hGeq : ∀ j, ∀ x ∈ K₁, G j x = f j x := fun j x hx => (hGK j x hx).eq_of_nhds
  obtain ⟨M, hM⟩ := hK₁.exists_bound_of_continuousOn ((hfs 0).1.continuousOn.mono hK₁A)
  have hGbd : ∀ j, ∀ x ∈ K₁, 0 ≤ G j x ∧ G j x ≤ M ∧ w x ≤ G j x := by
    intro j x hx
    have hxA : x ∈ A' := hK₁A hx
    have h1 : f j x ≤ f 0 x := hfanti x hxA (Nat.zero_le j)
    have h2 : w x ≤ f j x := (hfanti x hxA).le_of_tendsto (hflim x hxA) j
    have h3 : 0 ≤ w x := hw0 x (hτV hx)
    have h4 : f 0 x ≤ M := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x hx)
    rw [hGeq j x hx]
    exact ⟨h3.trans h2, h1.trans h4, h2⟩
  have hIcc : ∀ j, ∀ x ∈ K₁, G j x ∈ Icc 0 M := fun j x hx =>
    ⟨(hGbd j x hx).1, (hGbd j x hx).2.1⟩
  have hconv : ∀ x ∈ K₁, Tendsto (fun j => G j x) atTop (𝓝 (w x)) := fun x hx =>
    (hflim x (hK₁A hx)).congr fun j => (hGeq j x hx).symm
  -- the smooth estimates
  have hj : ∀ j, |∑ a, ∫ x, dTest (realBasis n a) φ x *
      (ζ (G j x) * densityForm hT x (testWedge γ ℓ a)) ∂σ| ≤
      t / 4 * ∫ x, G j x ^ 2 * hessWeight hT γ τ x ∂σ +
        1 / (2 * t) * ∫ x, φ x ^ 2 * deriv ζ (G j x) ^ 2 *
          densityForm hT x (quadForm q γ η η) ∂σ := fun j =>
    abs_sum_integral_le_of_contDiff hT hTc hγ ℓ φ τ hτ0 hτ1 hζ (hGs j)
      (fun x hx => (hGbd j x hx).1)
      (fun x hx => by
        rw [smoothDDC_congr (hGK j x hx)]
        exact isSemipositiveOneOne_smoothDDC (hfs j).1 (hfs j).2.1 (hK₁A hx)) ht
  have hζ' : Continuous (deriv ζ) := hζ.continuous_deriv (by simp)
  obtain ⟨Mζ, hMζ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
    hζ.continuous.continuousOn
  obtain ⟨Mζ', hMζ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
    hζ'.continuousOn
  -- (i) the closedness defects
  have hL : Tendsto (fun j => |∑ a, ∫ x, dTest (realBasis n a) φ x *
      (ζ (G j x) * densityForm hT x (testWedge γ ℓ a)) ∂σ|) atTop
      (𝓝 |∑ a, ∫ x, dTest (realBasis n a) φ x *
        (ζ (w x) * densityForm hT x (testWedge γ ℓ a)) ∂σ|) := by
    refine (continuous_abs.tendsto _).comp (tendsto_finsetSum _ fun a _ => ?_)
    set ψ := dTest (realBasis n a) φ
    have hψK : ∀ x, x ∉ tsupport φ → ψ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_dTest_subset _ _ h))
    obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT (testWedge γ ℓ a)
    have hbi : Integrable (fun x => ψ x * (Mζ * C)) σ :=
      hT.integrable_mul_of_bounded ψ.continuous ψ.hasCompactSupport ψ.tsupport_subset
        aestronglyMeasurable_const ⟨|Mζ * C|, fun _ _ => le_rfl⟩
    refine tendsto_integral_of_dominated_convergence (fun x => ‖ψ x * (Mζ * C)‖) (fun j => ?_)
      hbi.norm (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ψ.continuous.aestronglyMeasurable.mul
        ((hζ.continuous.comp (hGs j).continuous).aestronglyMeasurable.mul
          (measurable_densityForm hT _).aestronglyMeasurable)
    · by_cases hx : x ∈ tsupport φ
      · have h1 : ‖ζ (G j x)‖ ≤ Mζ := hMζ _ (hIcc j x (hφK hx))
        have h2 : ‖densityForm hT x (testWedge γ ℓ a)‖ ≤ C := by
          rw [Real.norm_eq_abs]; exact hC x
        rw [norm_mul, norm_mul, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.norm_eq_abs (Mζ * C), abs_mul]
        exact mul_le_mul (h1.trans (le_abs_self _)) (h2.trans (le_abs_self _)) (norm_nonneg _)
          (abs_nonneg _)
      · rw [hψK x hx]
        simp
    · by_cases hx : x ∈ tsupport φ
      · exact tendsto_const_nhds.mul
          (((hζ.continuous.tendsto _).comp (hconv x (hφK hx))).mul tendsto_const_nhds)
      · simp only [hψK x hx, zero_mul]
        exact tendsto_const_nhds
  -- (ii) the gradient terms
  have hE : Tendsto (fun j => ∫ x, G j x ^ 2 * hessWeight hT γ τ x ∂σ) atTop
      (𝓝 (∫ x, w x ^ 2 * hessWeight hT γ τ x ∂σ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M ^ 2 * hessWeight hT γ τ x)
      (fun j => ?_) ((integrable_hessWeight hT γ τ).const_mul _)
      (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ((hGs j).continuous.pow 2).aestronglyMeasurable.mul
        (measurable_hessWeight hT γ τ).aestronglyMeasurable
    · by_cases hx : x ∈ K₁
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hessWeight_nonneg _ _ _ _), abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (hGbd j x hx).1 (hGbd j x hx).2.1 2) (hessWeight_nonneg _ _ _ _)
      · rw [hessWeight_eq_zero hT γ τ hx]
        simp
    · by_cases hx : x ∈ K₁
      · exact ((hconv x hx).pow 2).mul tendsto_const_nhds
      · simp only [hessWeight_eq_zero hT γ τ hx, mul_zero]
        exact tendsto_const_nhds
  -- (iii) the cutoff terms
  have hY : Tendsto (fun j => ∫ x, φ x ^ 2 * deriv ζ (G j x) ^ 2 *
      densityForm hT x (quadForm q γ η η) ∂σ) atTop
      (𝓝 (∫ x, φ x ^ 2 * deriv ζ (w x) ^ 2 * densityForm hT x (quadForm q γ η η) ∂σ)) := by
    obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT (quadForm q γ η η)
    obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    have hbi : Integrable (fun x => φ x * (φ x * (Mζ' ^ 2 * C))) σ :=
      hT.integrable_mul_of_bounded φ.continuous φ.hasCompactSupport φ.tsupport_subset
        (φ.continuous.measurable.mul measurable_const).aestronglyMeasurable
        ⟨Cφ * |Mζ' ^ 2 * C|, fun x _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCφ x)
            (abs_nonneg _)⟩
    refine tendsto_integral_of_dominated_convergence (fun x => ‖φ x * (φ x * (Mζ' ^ 2 * C))‖)
      (fun j => ?_) hbi.norm (fun j => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact ((φ.continuous.pow 2).mul ((hζ'.comp (hGs j).continuous).pow
      2)).aestronglyMeasurable.mul
        (measurable_densityForm hT _).aestronglyMeasurable
    · by_cases hx : x ∈ tsupport φ
      · have h1 : |deriv ζ (G j x)| ≤ Mζ' := by
          simpa [Real.norm_eq_abs] using hMζ' _ (hIcc j x (hφK hx))
        have h2 : |densityForm hT x (quadForm q γ η η)| ≤ C := hC x
        have hC0 : 0 ≤ C := (abs_nonneg _).trans h2
        have hM0 : 0 ≤ Mζ' := (abs_nonneg _).trans h1
        simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hC0, abs_of_nonneg hM0]
        have h1' : |deriv ζ (G j x)| ^ 2 ≤ Mζ' ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        calc |φ x| ^ 2 * |deriv ζ (G j x)| ^ 2 * |densityForm hT x (quadForm q γ η η)| ≤
              |φ x| ^ 2 * Mζ' ^ 2 * C := by gcongr
          _ = |φ x| * (|φ x| * (Mζ' ^ 2 * C)) := by ring
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
    · by_cases hx : x ∈ tsupport φ
      · exact (tendsto_const_nhds.mul
          (((hζ'.tendsto _).comp (hconv x (hφK hx))).pow 2)).mul tendsto_const_nhds
      · simp only [image_eq_zero_of_notMem_tsupport hx]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' hL ((hE.const_mul _).add (hY.const_mul _)) hj

end SGPT.Currents.Gradient
