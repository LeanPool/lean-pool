/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorProducts

/-!
# Smooth factors in the recursive Bedford--Taylor product

On an open `U ⊆ ℂⁿ`:

* `mulSmoothOnCLM` — multiplication of test functions by a function smooth on `U` is a continuous
  linear map of `𝓓(U)` (on each `𝓓_K(U)` it is multiplication by a globally smooth cutoff
  multiple, `ContDiffMapSupportedIn.bilinLeftCLM`, assembled with `TestFunction.limitCLM`);
* `ddcWedge S g` — the current `dd^c g ∧ S` for `g` smooth on `U`:
  `(dd^c g ∧ S)(γ)(φ) = S(φ γ ∧ dd^c g) = -(1/4π) ∑_{a,b} S(γ ∧ P_{ab})(φ ∂_a∂_b g)`;
* `ddcMul_eq_ddcWedge` — for `S` positive closed, `dd^c(g S) = dd^c g ∧ S` (`g` smooth on `U`);
* `smoothProduct`, `btProduct_eq_smoothProduct` — **when all the potentials are smooth, the
  recursive product is the usual wedge product** `dd^c g₀ ∧ (dd^c g₁ ∧ ⋯ (dd^c g_{q-1} ∧ T))`
  (`bt:recursive-product`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U : Opens (ComplexModel n)}

/-! ### Multiplication of test functions by functions smooth on `U` -/

/-- A cutoff equal to one near the compact `K ⊆ U`, supported in `U`. -/
def cutoffOf (K : Compacts E) (hK : (K : Set E) ⊆ U) : E → ℝ :=
  Classical.choose (exists_cutoff K.isCompact U.isOpen hK)

theorem cutoffOf_spec (K : Compacts E) (hK : (K : Set E) ⊆ U) :
    ContDiff ℝ ∞ (cutoffOf K hK) ∧ (∀ x ∈ (K : Set E), cutoffOf K hK =ᶠ[𝓝 x] 1) ∧
      tsupport (cutoffOf K hK) ⊆ U :=
  Classical.choose_spec (exists_cutoff K.isCompact U.isOpen hK)

theorem contDiff_cutoffOf_mul {h : E → ℝ} (hh : ContDiffOn ℝ ∞ h U) (K : Compacts E)
    (hK : (K : Set E) ⊆ U) : ContDiff ℝ ∞ (fun x => cutoffOf K hK x * h x) :=
  contDiff_mul_of_tsupport_subset U.isOpen (cutoffOf_spec K hK).1 (cutoffOf_spec K hK).2.2 hh

/-- **Multiplication by a function smooth on `U`** as a continuous linear map of `𝓓(U)`. -/
def mulSmoothOnCLM {h : E → ℝ} (hh : ContDiffOn ℝ ∞ h U) : 𝓓(U, ℝ) →L[ℝ] 𝓓(U, ℝ) :=
  TestFunction.limitCLM ℝ (fun φ => smoothMulTest U.isOpen hh φ φ.tsupport_subset)
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ hK).comp
      (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ)
        (contDiff_cutoffOf_mul hh K hK)))
    (fun K hK f => by
      ext x
      change f x * h x = f x * (cutoffOf K hK x * h x)
      by_cases hx : x ∈ (K : Set E)
      · rw [((cutoffOf_spec K hK).2.1 x hx).eq_of_nhds]
        simp
      · have : f x = 0 := f.zero_on_compl hx
        simp [this])

@[simp] theorem mulSmoothOnCLM_apply {h : E → ℝ} (hh : ContDiffOn ℝ ∞ h U) (φ : 𝓓(U, ℝ))
    (x : E) : mulSmoothOnCLM hh φ x = φ x * h x := rfl

/-! ### `dd^c g ∧ S` for `g` smooth on `U` -/

section Wedge

variable {q : ℕ}

theorem contDiffOn_dFun {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (v : E) :
    ContDiffOn ℝ ∞ (dFun v g) U :=
  (hg.fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_hessFun {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (a b : Fin (n * 2)) :
    ContDiffOn ℝ ∞ (hessFun a b g) U :=
  contDiffOn_dFun (contDiffOn_dFun hg _) _

/-- Precomposition of distributions with a continuous linear map of test functions. -/
def precompLM (M : 𝓓(U, ℝ) →L[ℝ] 𝓓(U, ℝ)) : 𝓓'(U, ℝ) →ₗ[ℝ] 𝓓'(U, ℝ) where
  toFun T := T.comp M
  map_add' _ _ := ContinuousLinearMap.add_comp _ _ _
  map_smul' _ _ := ContinuousLinearMap.smul_comp _ _ _

/-- **`dd^c g ∧ S`** for `g` smooth on `U`: `(dd^c g ∧ S)(γ)(φ) = S(φ γ ∧ dd^c g)`, i.e.
`-(1/4π) ∑_{a,b} S(γ ∧ P_{ab})(φ ∂_a∂_b g)` (`smoothDDC_eq_sum`). -/
def ddcWedge (S : LocalProductCurrent n U (q + 1)) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    LocalProductCurrent n U q :=
  ∑ a, ∑ b, (-(1 / (4 * Real.pi))) •
    (precompLM (mulSmoothOnCLM (contDiffOn_hessFun hg a b)) ∘ₗ S ∘ₗ
      wedgeLM q (isOneOne_coeffForm a b))

theorem ddcWedge_apply (S : LocalProductCurrent n U (q + 1)) {g : E → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    ddcWedge S hg γ φ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      S (wedgeLM q (isOneOne_coeffForm a b) γ) (mulSmoothOnCLM (contDiffOn_hessFun hg a b) φ) := by
  rw [ddcWedge]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rfl

theorem measurable_indicator_of_continuousOn {g : E → ℝ} (hg : ContinuousOn g U) :
    Measurable ((U : Set E).indicator g) := by
  classical
  have h := hg.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) U.isOpen.measurableSet
  convert h using 1
  ext x
  by_cases hx : x ∈ (U : Set E) <;> simp [Set.piecewise, hx]

theorem isLocallyBoundedOn_indicator_of_continuousOn {g : E → ℝ} (hg : ContinuousOn g U) :
    IsLocallyBoundedOn ((U : Set E).indicator g) U := fun K hK hKU => by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.mono hKU)
  exact ⟨C, fun x hx => by
    rw [Set.indicator_of_mem (hKU hx)]
    simpa [Real.norm_eq_abs] using hC x hx⟩

/-- **`dd^c(g S) = dd^c g ∧ S`** for a positive closed `S` and `g` smooth on `U`. -/
theorem ddcMul_eq_ddcWedge {S : LocalProductCurrent n U (q + 1)} (hS : IsPositive S)
    (hSc : IsClosedCurrent S) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    ddcMul S g = ddcWedge S hg := by
  ext γ φ
  obtain ⟨χ, hχ, hχ1, hχU⟩ := exists_cutoff φ.hasCompactSupport U.isOpen φ.tsupport_subset
  have hg' : ContDiff ℝ ∞ (fun x => χ x * g x) := contDiff_mul_of_tsupport_subset U.isOpen hχ hχU
    hg
  have heq : ∀ x ∈ tsupport φ, (fun y => χ y * g y) =ᶠ[𝓝 x] g := fun x hx =>
    (hχ1 x hx).mono fun y hy => by simp [hy]
  -- step 1: replace `g` by the global `χ g`
  have hA : ddcMul S g γ φ = ddcMul S (fun x => χ x * g x) γ φ := by
    rw [ddcMul, ddcMul, ddc_apply_apply, ddc_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mulBorel_apply hS (measurable_indicator_of_continuousOn hg.continuousOn)
        (isLocallyBoundedOn_indicator_of_continuousOn hg.continuousOn),
      mulBorel_apply hS (measurable_indicator_of_continuousOn hg'.continuous.continuousOn)
        (isLocallyBoundedOn_indicator_of_continuousOn hg'.continuous.continuousOn)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · have hv : χ x * g x = g x := (heq x hx).eq_of_nhds
      simp only [Set.indicator_of_mem (φ.tsupport_subset hx)]
      rw [hv]
    · have hψ : dTest (realBasis n b) (dTest (realBasis n a) φ) x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h =>
          hx (((tsupport_dTest_subset _ _).trans (tsupport_dTest_subset _ _)) h)
      simp only [hψ, zero_mul]
  rw [hA, ddcMul_apply_of_contDiff hS hSc hg', ddcWedge_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 2
  ext x
  rw [mulTest_apply, mulSmoothOnCLM_apply]
  by_cases hx : x ∈ tsupport φ
  · have h1 : ∀ v, dFun v (fun y => χ y * g y) =ᶠ[𝓝 x] dFun v g := fun v =>
      ((heq x hx).fderiv (𝕜 := ℝ)).mono fun y hy => by simp only [dFun, hy]
    have h2 : hessFun a b (fun y => χ y * g y) x = hessFun a b g x := by
      change fderiv ℝ (dFun (realBasis n b) (fun y => χ y * g y)) x (realBasis n a) =
        fderiv ℝ (dFun (realBasis n b) g) x (realBasis n a)
      rw [(h1 _).fderiv_eq]
    rw [h2]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

end Wedge

/-! ### Smooth potentials: the recursive product is the usual wedge product -/

section SmoothProduct

/-- The iterated smooth product `dd^c g₀ ∧ (dd^c g₁ ∧ ⋯ (dd^c g_{q-1} ∧ T))`. -/
def smoothProduct : (q r : ℕ) → (g : Fin q → E → ℝ) → (∀ i, ContDiffOn ℝ ∞ (g i) U) →
    LocalProductCurrent n U (r + q) → LocalProductCurrent n U r
  | 0, _, _, _, T => T
  | q + 1, r, g, hg, T =>
    smoothProduct q r (Fin.init g) (fun _ => hg _) (ddcWedge T (hg (Fin.last q)))

/-- **Agreement with the smooth product** (`bt:recursive-product`): when all the potentials are
smooth (and locally bounded PSH), the recursive product is the usual wedge product. -/
theorem btProduct_eq_smoothProduct : ∀ (q r : ℕ) (g : Fin q → E → ℝ)
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U), (∀ i, IsLocallyBoundedPshOn U (g i)) →
    ∀ (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
    btProduct q r g T = smoothProduct q r g hg T
  | 0, _, _, _, _, _, _, _ => rfl
  | q + 1, r, g, hg, hgp, T, hT, hTc => by
    rw [btProduct_succ]
    have hS := isPositive_ddcMul (m := r + q) hT hTc (hgp (Fin.last q))
    have e : ddcMul T (g (Fin.last q)) = ddcWedge T (hg (Fin.last q)) :=
      ddcMul_eq_ddcWedge (q := r + q) hT hTc (hg _)
    rw [btProduct_eq_smoothProduct q r (Fin.init g) (fun i => hg _) (fun i => hgp _) _ hS.1 hS.2,
      e]
    rfl

end SmoothProduct

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
