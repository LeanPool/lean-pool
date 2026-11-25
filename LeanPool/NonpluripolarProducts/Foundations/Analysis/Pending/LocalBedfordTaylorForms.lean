/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConstantFormProducts
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentLebesgue

/-!
# Currents wedged with smooth forms; the recursive product commutes with closed positive forms

On an open `U ⊆ ℂⁿ`, for the currents of `Pending.LocalProductCurrents` (linear maps from the
constant forms `Λ_m` to the distributions on `U`):

* `sum_apply_eq_of_forall` — **a current applied to a variable test form depends only on the
  pointwise form**: if `∑ⱼ ψⱼ(x) Xⱼ = ∑ₗ χₗ(x) Yₗ` for all `x ∈ U`, then
  `∑ⱼ R(Xⱼ)(ψⱼ) = ∑ₗ R(Yₗ)(χₗ)` for every current `R` (expansion in a basis of `Λ_m`).
* `formCoeff` — the coefficients, smooth on `U`, of a form `α` smooth on `U` with values in `Λ_k`
  in the basis `formBasis n k`.
* `wedgeForm h S hα` — **the current `S ∧ α`** of bidimension `(r,r)` for `S` of bidimension
  `(m,m)`, `r + k = m`: `(S ∧ α)(γ)(φ) = ∑ᵢ S(γ ∧ bᵢ)(cᵢ φ)` for `α = ∑ᵢ cᵢ bᵢ`;
  `wedgeForm_apply_eq` (any representation of `α` gives the same current);
  `isPositive_wedgeForm` (positive for `S` positive and `α` strongly positive);
  `isClosedCurrent_wedgeForm` (closed for `S` closed and `α` closed, `extDeriv α = 0` on `U`).
* `ddc_wedgeForm` — **the Leibniz identity** `dd^c(R ∧ α) = dd^c R ∧ α` for EVERY current `R`
  when `α` is a closed form of type `(k,k)`.
* `mulBorel_apply_of_integral_eq` — `u T` does not depend on the representing measure of a
  coefficient; `mulBorel_wedgeForm` — `u (T ∧ α) = (u T) ∧ α`.
* `ddcMul_wedgeForm`, `btProduct_wedgeForm` — **multiplication by a smooth closed strongly
  positive form commutes with the recursive Bedford--Taylor product** (`bt:recursive-product`):
  `B(u; T ∧ α) = B(u; T) ∧ α`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  CoordinateWedgeAssoc ClosedProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorLocality LocalCurrentLebesgue ConstantFormProducts

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U : Opens (ComplexModel n)}

/-! ### Currents on variable test forms -/

section Pointwise

/-- **A current applied to a variable test form with zero pointwise value vanishes.** -/
theorem sum_apply_eq_zero_of_forall {m : ℕ} (R : LocalProductCurrent n U m) {ι : Type*}
    [Fintype ι] (X : ι → formSpan n m) (ψ : ι → 𝓓(U, ℝ))
    (h : ∀ x, ∑ j, ψ j x • (X j : RealForm n (2 * m)) = 0) : ∑ j, R (X j) (ψ j) = 0 := by
  classical
  set b := formBasis n m
  have hexp : ∀ j, R (X j) (ψ j) = ∑ k, R (b k) (b.repr (X j) k • ψ j) := by
    intro j
    conv_lhs => rw [← b.sum_repr (X j)]
    rw [map_sum, _root_.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, _root_.smul_apply, smul_eq_mul, map_smul, smul_eq_mul]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← map_sum]
  have hz : ∑ j, b.repr (X j) k • ψ j = 0 := by
    ext x
    rw [_root_.sum_apply]
    simp only [_root_.smul_apply, smul_eq_mul, zero_apply]
    have h0 : (∑ j, ψ j x • X j : formSpan n m) = 0 := by
      ext1
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simpa only [Submodule.coe_smul] using h x
    let coefficient : formSpan n m →ₗ[ℝ] ℝ := (Finsupp.lapply k).comp b.repr.toLinearMap
    have evaluated := congrArg coefficient h0
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at evaluated
    simpa only [coefficient, LinearMap.comp_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe, mul_comm] using evaluated
  rw [hz, map_zero]

/-- **A current applied to a variable test form depends only on the pointwise form** on `U`. -/
theorem sum_apply_eq_of_forall {m : ℕ} (R : LocalProductCurrent n U m) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (X : ι → formSpan n m) (ψ : ι → 𝓓(U, ℝ))
    (Y : κ → formSpan n m) (χ : κ → 𝓓(U, ℝ))
    (h : ∀ x ∈ U, ∑ j, ψ j x • (X j : RealForm n (2 * m)) =
      ∑ l, χ l x • (Y l : RealForm n (2 * m))) :
    ∑ j, R (X j) (ψ j) = ∑ l, R (Y l) (χ l) := by
  classical
  have h0 := sum_apply_eq_zero_of_forall R (Sum.elim X Y)
    (Sum.elim ψ (fun l => (-1 : ℝ) • χ l))
    (fun x => by
      rw [Fintype.sum_sum_type]
      have e2 : ∀ l, ((-1 : ℝ) • χ l) x • (Y l : RealForm n (2 * m)) =
          -(χ l x • (Y l : RealForm n (2 * m))) := fun l => by
        rw [_root_.smul_apply, smul_eq_mul, neg_one_mul]
        exact neg_smul (χ l x) (Y l : RealForm n (2 * m))
      simp only [Sum.elim_inl, Sum.elim_inr]
      simp only [e2, Finset.sum_neg_distrib]
      by_cases hx : x ∈ U
      · rw [h x hx, add_neg_cancel]
      · simp only [testFunction_eq_zero_of_notMem _ hx, zero_smul, Finset.sum_const_zero,
          neg_zero, add_zero])
  rw [Fintype.sum_sum_type] at h0
  simp only [Sum.elim_inl, Sum.elim_inr, map_smul, smul_eq_mul, neg_one_mul,
    Finset.sum_neg_distrib] at h0
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0)

end Pointwise

/-! ### Coefficients of forms with values in `Λ_k` -/

section Coefficients

variable (n) in
/-- A linear projection of the forms of degree `2k` onto `Λ_k`. -/
def formProj (k : ℕ) : RealForm n (2 * k) →ₗ[ℝ] formSpan n k :=
  Classical.choose (LinearMap.exists_leftInverse_of_injective (formSpan n k).subtype
    (Submodule.ker_subtype _))

theorem formProj_coe {k : ℕ} (γ : formSpan n k) : formProj n k (γ : RealForm n (2 * k)) = γ :=
  LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_leftInverse_of_injective
    (formSpan n k).subtype (Submodule.ker_subtype _))) γ

variable (n) in
/-- The `i`-th coefficient in the basis `formBasis n k`, as a continuous linear form. -/
def coeffCLM (k : ℕ) (i : Fin (Module.finrank ℝ (formSpan n k))) : RealForm n (2 * k) →L[ℝ] ℝ :=
  haveI := ProductTestForms.realForm_finiteDimensional (n := n) (2 * k)
  LinearMap.toContinuousLinearMap ((formBasis n k).coord i ∘ₗ formProj n k)

/-- The coefficients of a form `α` in the basis `formBasis n k` of `Λ_k`. -/
def formCoeff {k : ℕ} (α : E → RealForm n (2 * k)) (i : Fin (Module.finrank ℝ (formSpan n k)))
    (x : E) : ℝ :=
  coeffCLM n k i (α x)

theorem formCoeff_apply {k : ℕ} (α : E → RealForm n (2 * k))
    (i : Fin (Module.finrank ℝ (formSpan n k))) (x : E) :
    formCoeff α i x = (formBasis n k).repr (formProj n k (α x)) i := rfl

theorem contDiffOn_formCoeff {k : ℕ} {α : E → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (i : Fin (Module.finrank ℝ (formSpan n k))) : ContDiffOn ℝ ∞ (formCoeff α i) U :=
  (coeffCLM n k i).contDiff.comp_contDiffOn hα

/-- A form with values in `Λ_k` is the sum of its coefficients times the basis forms. -/
theorem eq_sum_formCoeff {k : ℕ} {α : E → RealForm n (2 * k)} {x : E}
    (hx : α x ∈ formSpan n k) :
    α x = ∑ i, formCoeff α i x • ((formBasis n k i : formSpan n k) : RealForm n (2 * k)) := by
  have e : formProj n k (α x) = ⟨α x, hx⟩ := formProj_coe ⟨α x, hx⟩
  have hc : ((formProj n k (α x) : formSpan n k) : RealForm n (2 * k)) = α x := by rw [e]
  conv_lhs => rw [← hc, ← (formBasis n k).sum_repr (formProj n k (α x))]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul]
  rfl

theorem differentiableAt_formCoeff {k : ℕ} {α : E → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) (i : Fin (Module.finrank ℝ (formSpan n k))) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ (formCoeff α i) x :=
  ((contDiffOn_formCoeff hα i).differentiableOn (by simp)).differentiableAt
    (U.isOpen.mem_nhds hx)

end Coefficients

/-! ### The current `S ∧ α` -/

section Wedge

variable {r k m : ℕ}

/-- **The current `S ∧ α`** for a current `S` of bidimension `(m,m)` and a form `α` smooth on `U`
of degree `2k`, `r + k = m`: `(S ∧ α)(γ)(φ) = ∑ᵢ S(γ ∧ bᵢ)(cᵢ φ)`, `cᵢ` the coefficients of `α`
in the basis `bᵢ = formBasis n k i` of `Λ_k`. -/
def wedgeForm (h : r + k = m) (S : LocalProductCurrent n U m) {α : E → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) : LocalProductCurrent n U r :=
  ∑ i, precompLM (mulSmoothOnCLM (contDiffOn_formCoeff hα i)) ∘ₗ S ∘ₗ
    (wedgeSpan n h).flip (formBasis n k i)

theorem wedgeForm_apply (h : r + k = m) (S : LocalProductCurrent n U m)
    {α : E → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U) (γ : formSpan n r) (φ : 𝓓(U, ℝ)) :
    wedgeForm h S hα γ φ = ∑ i, S (wedgeSpan n h γ (formBasis n k i))
      (mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ) := by
  rw [wedgeForm, LinearMap.sum_apply, _root_.sum_apply]
  rfl

/-- The pointwise form of `S ∧ α` on `φ γ`. -/
theorem sum_mulSmoothOnCLM_smul_wedgeSpan (h : r + k = m) {α : E → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) (hαS : ∀ x ∈ U, α x ∈ formSpan n k) (γ : formSpan n r)
    (φ : 𝓓(U, ℝ)) (h2 : 2 * r + 2 * k = 2 * m) {x : E} (hx : x ∈ U) :
    ∑ i, mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ x •
        (wedgeSpan n h γ (formBasis n k i) : RealForm n (2 * m)) =
      φ x • wedgeTo h2 (γ : RealForm n (2 * r)) (α x) := by
  rw [eq_sum_formCoeff (hαS x hx), wedgeTo_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_wedgeSpan_apply h _ _ h2, wedgeTo_smul_right, smul_smul, mulSmoothOnCLM_apply]

/-- **Any representation of `α` computes `S ∧ α`**: if `α = ∑ⱼ fⱼ βⱼ` on `U` with `fⱼ` smooth on
`U` and `βⱼ ∈ Λ_k`, then `(S ∧ α)(γ)(φ) = ∑ⱼ S(γ ∧ βⱼ)(fⱼ φ)`. -/
theorem wedgeForm_apply_eq (h : r + k = m) (S : LocalProductCurrent n U m)
    {α : E → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U) (hαS : ∀ x ∈ U, α x ∈ formSpan n k)
    {κ : Type*} [Fintype κ] (f : κ → E → ℝ) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U)
    (β : κ → formSpan n k) (hrep : ∀ x ∈ U, α x = ∑ j, f j x • (β j : RealForm n (2 * k)))
    (γ : formSpan n r) (φ : 𝓓(U, ℝ)) :
    wedgeForm h S hα γ φ = ∑ j, S (wedgeSpan n h γ (β j)) (mulSmoothOnCLM (hf j) φ) := by
  rw [wedgeForm_apply]
  refine sum_apply_eq_of_forall S _ _ _ _ fun x hx => ?_
  have h2 : 2 * r + 2 * k = 2 * m := by omega
  rw [sum_mulSmoothOnCLM_smul_wedgeSpan h hα hαS γ φ h2 hx, hrep x hx, wedgeTo_sum_right,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coe_wedgeSpan_apply h _ _ h2, wedgeTo_smul_right, smul_smul, mulSmoothOnCLM_apply]

/-- **`S ∧ α` is positive** for `S` positive and `α` strongly positive at every point of `U`. -/
theorem isPositive_wedgeForm (h : r + k = m) {S : LocalProductCurrent n U m} (hS : IsPositive S)
    {α : E → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U) (hαp : ∀ x ∈ U, α x ∈ spCone k) :
    IsPositive (wedgeForm h S hα) := by
  classical
  intro ι _ γ φ hγ
  have h2 : 2 * r + 2 * k = 2 * m := by omega
  have hαS : ∀ x ∈ U, α x ∈ formSpan n k := fun x hx => mem_formSpan_of_mem_spCone (hαp x hx)
  simp only [wedgeForm_apply]
  rw [← Fintype.sum_prod_type']
  refine hS (ι × Fin (Module.finrank ℝ (formSpan n k)))
    (fun j => wedgeSpan n h (γ j.1) (formBasis n k j.2))
    (fun j => mulSmoothOnCLM (contDiffOn_formCoeff hα j.2) (φ j.1)) fun x => ?_
  rw [Fintype.sum_prod_type]
  by_cases hx : x ∈ U
  · have e : ∀ l, ∑ i, mulSmoothOnCLM (contDiffOn_formCoeff hα i) (φ l) x •
        (wedgeSpan n h (γ l) (formBasis n k i) : RealForm n (2 * m)) =
        φ l x • wedgeTo h2 (γ l : RealForm n (2 * r)) (α x) := fun l =>
      sum_mulSmoothOnCLM_smul_wedgeSpan h hα hαS (γ l) (φ l) h2 hx
    simp only [e]
    simp only [← wedgeTo_smul_left]
    rw [← wedgeTo_sum_left]
    exact wedgeTo_mem_spCone k r m (hγ x) (hαp x hx) h2
  · simp only [testFunction_eq_zero_of_notMem _ hx, zero_smul, Finset.sum_const_zero]
    exact (spCone (n := n) m).zero_mem

end Wedge

/-! ### Calculus of functions and forms smooth on `U` -/

section Calculus

/-- **The Leibniz rule** for the multiplication of test functions by a function smooth on `U`:
`∂_v(g φ) = g ∂_v φ + (∂_v g) φ`. -/
theorem dTest_mulSmoothOnCLM {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (v : E) (φ : 𝓓(U, ℝ)) :
    dTest v (mulSmoothOnCLM hg φ) =
      mulSmoothOnCLM hg (dTest v φ) + mulSmoothOnCLM (contDiffOn_dFun hg v) φ := by
  ext x
  rw [dTest_apply, _root_.add_apply, mulSmoothOnCLM_apply, mulSmoothOnCLM_apply, dTest_apply]
  have hf : (mulSmoothOnCLM hg φ : E → ℝ) = fun y => φ y * g y :=
    funext (mulSmoothOnCLM_apply hg φ)
  rw [hf]
  by_cases hx : x ∈ tsupport φ
  · have hxU : x ∈ (U : Set E) := φ.tsupport_subset hx
    have hφd : DifferentiableAt ℝ (φ : E → ℝ) x :=
      (φ.contDiff.differentiable (by simp)).differentiableAt
    have hgd : DifferentiableAt ℝ g x :=
      (hg.differentiableOn (by simp)).differentiableAt (U.isOpen.mem_nhds hxU)
    have hd : HasFDerivAt (fun y => φ y * g y)
        (φ x • fderiv ℝ g x + g x • fderiv ℝ (φ : E → ℝ) x) x :=
      hφd.hasFDerivAt.mul hgd.hasFDerivAt
    rw [hd.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, dFun]
    ring
  · have h0 : (φ : E → ℝ) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have h1 : (fun y => φ y * g y) =ᶠ[𝓝 x] fun _ => 0 := h0.mono fun y hy => by
      simp only [Pi.zero_apply] at hy
      simp [hy]
    rw [h1.fderiv_eq, h0.fderiv_eq, image_eq_zero_of_notMem_tsupport hx]
    simp

theorem dTest_add (v : E) (φ ψ : 𝓓(U, ℝ)) : dTest v (φ + ψ) = dTest v φ + dTest v ψ :=
  map_add _ _ _

theorem dTest_sub (v : E) (φ ψ : 𝓓(U, ℝ)) : dTest v (φ - ψ) = dTest v φ - dTest v ψ :=
  map_sub _ _ _

/-- The second-order Leibniz rule. -/
theorem dTest_dTest_mulSmoothOnCLM {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (v w : E)
    (φ : 𝓓(U, ℝ)) :
    dTest w (dTest v (mulSmoothOnCLM hg φ)) =
      mulSmoothOnCLM hg (dTest w (dTest v φ)) + mulSmoothOnCLM (contDiffOn_dFun hg w) (dTest v φ) +
        mulSmoothOnCLM (contDiffOn_dFun hg v) (dTest w φ) +
        mulSmoothOnCLM (contDiffOn_dFun (contDiffOn_dFun hg v) w) φ := by
  rw [dTest_mulSmoothOnCLM, dTest_add, dTest_mulSmoothOnCLM, dTest_mulSmoothOnCLM]
  abel

/-- The derivative of a form with values in `Λ_k` through its coefficients. -/
theorem fderiv_apply_eq_sum {k : ℕ} {α : E → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (hαS : ∀ x ∈ U, α x ∈ formSpan n k) {x : E} (hx : x ∈ U) (v : E) :
    fderiv ℝ α x v = ∑ i, dFun v (formCoeff α i) x •
      ((formBasis n k i : formSpan n k) : RealForm n (2 * k)) := by
  have heq : α =ᶠ[𝓝 x] fun y => ∑ i, formCoeff α i y •
      ((formBasis n k i : formSpan n k) : RealForm n (2 * k)) :=
    Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun y hy => eq_sum_formCoeff (hαS y hy)
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ (formSpan n k)))),
      DifferentiableAt ℝ (fun y => formCoeff α i y •
        ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) x := fun i _ =>
    (differentiableAt_formCoeff hα i hx).smul_const _
  rw [heq.fderiv_eq, fderiv_fun_sum hd, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : fderiv ℝ (fun y => formCoeff α i y •
      ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) x =
      (fderiv ℝ (formCoeff α i) x).smulRight
        ((formBasis n k i : formSpan n k) : RealForm n (2 * k)) :=
    ((differentiableAt_formCoeff hα i hx).hasFDerivAt.smul_const
      ((formBasis n k i : formSpan n k) : RealForm n (2 * k))).fderiv
  rw [e]
  rfl

/-- If a finite sum `∑ⱼ cⱼ Wⱼ` (constant `Wⱼ`) vanishes near `x`, so do its derivatives. -/
theorem sum_dFun_smul_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
    [Fintype ι] {c : ι → E → ℝ} (W : ι → F) {x : E} (hc : ∀ j, DifferentiableAt ℝ (c j) x)
    (h0 : (fun y => ∑ j, c j y • W j) =ᶠ[𝓝 x] fun _ => 0) (v : E) :
    ∑ j, dFun v (c j) x • W j = 0 := by
  have hfd : HasFDerivAt (fun y => ∑ j, c j y • W j)
      (∑ j, (fderiv ℝ (c j) x).smulRight (W j)) x :=
    HasFDerivAt.fun_sum fun j _ => (hc j).hasFDerivAt.smul_const (W j)
  have e := hfd.fderiv
  rw [h0.fderiv_eq, fderiv_const_apply] at e
  have := congrArg (fun L : E →L[ℝ] F => L v) e
  simp only [_root_.sum_apply, _root_.zero_apply,
    ContinuousLinearMap.smulRight_apply] at this
  exact this.symm

/-- `oneWedge ℓ` is linear. -/
theorem oneWedge_sum_smul {p : ℕ} (ℓ : E →L[ℝ] ℝ) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (B : ι → RealForm n p) :
    oneWedge ℓ (∑ i ∈ s, c i • B i) = ∑ i ∈ s, c i • oneWedge ℓ (B i) := by
  ext v
  simp only [oneWedge, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [zsmul_eq_mul]
  ring

variable {k : ℕ} {α : ComplexModel n → RealForm n (2 * k)}

/-- **Closedness in coefficients**: `∑_a e^a ∧ ∑ᵢ ∂_a cᵢ(x) bᵢ = 0` on `U`. -/
theorem sum_oneWedge_dFun_eq_zero (hα : ContDiffOn ℝ ∞ α U) (hαS : ∀ x ∈ U, α x ∈ formSpan n k)
    (hαc : ∀ x ∈ U, extDeriv α x = 0) {x : E} (hx : x ∈ U) :
    ∑ a, oneWedge (coordCLM n a) (∑ i, dFun (realBasis n a) (formCoeff α i) x •
      ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) = 0 := by
  rw [← hαc x hx, extDeriv_eq_sum_oneWedge]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_apply_eq_sum hα hαS hx]

/-- **Closedness in coefficients, differentiated**: `∑_a e^a ∧ ∑ᵢ ∂_w ∂_a cᵢ(x) bᵢ = 0` on `U`. -/
theorem sum_oneWedge_dFun_dFun_eq_zero (hα : ContDiffOn ℝ ∞ α U)
    (hαS : ∀ x ∈ U, α x ∈ formSpan n k) (hαc : ∀ x ∈ U, extDeriv α x = 0) {x : E} (hx : x ∈ U)
    (w : E) :
    ∑ a, oneWedge (coordCLM n a) (∑ i, dFun w (dFun (realBasis n a) (formCoeff α i)) x •
      ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) = 0 := by
  classical
  set W : Fin (n * 2) × Fin (Module.finrank ℝ (formSpan n k)) → RealForm n (2 * k + 1) :=
    fun j => oneWedge (coordCLM n j.1) ((formBasis n k j.2 : formSpan n k) : RealForm n (2 * k))
  have hsplit : ∀ (f : Fin (n * 2) → Fin (Module.finrank ℝ (formSpan n k)) → ℝ),
      ∑ a, oneWedge (coordCLM n a) (∑ i, f a i •
        ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) = ∑ j, f j.1 j.2 • W j := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [oneWedge_sum_smul]
  have hdiff : ∀ j : Fin (n * 2) × Fin (Module.finrank ℝ (formSpan n k)),
      DifferentiableAt ℝ (dFun (realBasis n j.1) (formCoeff α j.2)) x := fun j =>
    ((contDiffOn_dFun (contDiffOn_formCoeff hα j.2) _).differentiableOn (by simp)).differentiableAt
      (U.isOpen.mem_nhds hx)
  have hG : (fun y => ∑ j, dFun (realBasis n j.1) (formCoeff α j.2) y • W j) =ᶠ[𝓝 x]
      fun _ => 0 := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    rw [← hsplit (fun a i => dFun (realBasis n a) (formCoeff α i) y)]
    exact sum_oneWedge_dFun_eq_zero hα hαS hαc hy
  rw [hsplit (fun a i => dFun w (dFun (realBasis n a) (formCoeff α i)) x)]
  exact sum_dFun_smul_eq_zero W hdiff hG w

end Calculus

/-! ### Closedness of `S ∧ α` -/

section Closed

variable {r k m : ℕ} {α : ComplexModel n → RealForm n (2 * k)}

theorem coeff_sum_mem_formSpan (c : Fin (Module.finrank ℝ (formSpan n k)) → ℝ) :
    ∑ i, c i • ((formBasis n k i : formSpan n k) : RealForm n (2 * k)) ∈ formSpan n k :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (formBasis n k i).2

/-- The forms `(γ ∧ T) ∧ bᵢ` and `(γ ∧ bᵢ) ∧ T` agree (`T` a real `(1,1)`-form). -/
theorem wedgeSpan_wedgeLM (h : r + 1 + k = m + 1) (h' : r + k = m) {T : RealForm n 2}
    (hT : IsOneOne T) (γ : formSpan n r) (β : formSpan n k) :
    wedgeSpan n h (wedgeLM r hT γ) β = wedgeLM m hT (wedgeSpan n h' γ β) := by
  ext1
  rw [coe_wedgeSpan_apply h _ _ (by omega), coe_wedgeLM_apply, coe_wedgeLM_apply,
    coe_wedgeSpan_apply h' _ _ (by omega)]
  exact wedgeTo_wedgeTo_comm (γ : RealForm n (2 * r)) T β.2 rfl _ _ rfl

/-- The vanishing of `∑_a (P ∧ Π₁₁(e^a ∧ ℓ)) ∧ D_a` when `∑_a e^a ∧ D_a = 0`, `D_a ∈ Λ_k`. -/
theorem sum_wedgeTo_coordinateWedge_testForm_eq_zero (D : Fin (n * 2) → RealForm n (2 * k))
    (hD : ∀ a, D a ∈ formSpan n k) (h0 : ∑ a, oneWedge (coordCLM n a) (D a) = 0)
    (ℓ : E →L[ℝ] ℝ) (P : RealForm n (2 * r)) (h2 : 2 * r + 2 + 2 * k = 2 * (m + 1)) :
    ∑ a, wedgeTo h2 (coordinateWedge P (testForm a ℓ) : RealForm n (2 * r + 2)) (D a) = 0 := by
  have hassoc : ∀ a,
      wedgeTo h2 (coordinateWedge P (testForm a ℓ) : RealForm n (2 * r + 2)) (D a) =
        wedgeTo (by omega : 2 * r + (2 + 2 * k) = 2 * (m + 1)) P
          (wedgeTo (rfl : 2 + 2 * k = 2 + 2 * k) (testForm a ℓ) (D a)) := fun a =>
    wedgeTo_assoc rfl h2 rfl _ P (testForm a ℓ) (D a)
  simp_rw [hassoc]
  rw [← wedgeTo_sum_right, sum_wedgeTo_testForm_eq_zero D
    (fun a => formSpan_le_jInvariant k (hD a)) h0 ℓ rfl, wedgeTo_zero_right]

/-- The pointwise identity behind the closedness of `S ∧ α`: for `x ∈ U`,
`∑_a ((γ ∧ Π₁₁(e^a ∧ ℓ)) ∧ ∂_a α(x)) = 0`. -/
theorem sum_wedgeTo_testForm_dFun_eq_zero (hα : ContDiffOn ℝ ∞ α U)
    (hαS : ∀ x ∈ U, α x ∈ formSpan n k) (hαc : ∀ x ∈ U, extDeriv α x = 0) {x : E} (hx : x ∈ U)
    (ℓ : E →L[ℝ] ℝ) (P : RealForm n (2 * r)) (h2 : 2 * r + 2 + 2 * k = 2 * (m + 1)) :
    ∑ a, wedgeTo h2 (coordinateWedge P (testForm a ℓ) : RealForm n (2 * r + 2))
      (∑ i, dFun (realBasis n a) (formCoeff α i) x •
        ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) = 0 :=
  sum_wedgeTo_coordinateWedge_testForm_eq_zero _ (fun _ => coeff_sum_mem_formSpan _)
    (sum_oneWedge_dFun_eq_zero hα hαS hαc hx) ℓ P h2

/-- **`S ∧ α` is closed** for a closed current `S` and a closed form `α` (`extDeriv α = 0` on `U`)
with values in `Λ_k`. -/
theorem isClosedCurrent_wedgeForm (h : r + 1 + k = m + 1) {S : LocalProductCurrent n U (m + 1)}
    (hS : LocalBedfordTaylorProducts.IsClosedCurrent S) (hα : ContDiffOn ℝ ∞ α U)
    (hαS : ∀ x ∈ U, α x ∈ formSpan n k) (hαc : ∀ x ∈ U, extDeriv α x = 0) :
    LocalBedfordTaylorProducts.IsClosedCurrent (wedgeForm h S hα) := by
  classical
  intro ℓ γ
  have h' : r + k = m := by omega
  ext φ
  rw [_root_.sum_apply, _root_.zero_apply]
  simp only [dDist_apply, wedgeForm_apply, wedgeSpan_wedgeLM h h']
  simp_rw [show ∀ a i, mulSmoothOnCLM (contDiffOn_formCoeff hα i) (dTest (realBasis n a) φ) =
      dTest (realBasis n a) (mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ) -
        mulSmoothOnCLM (contDiffOn_dFun (contDiffOn_formCoeff hα i) (realBasis n a)) φ from
    fun a i => by rw [dTest_mulSmoothOnCLM]; abel, map_sub, Finset.sum_sub_distrib]
  have hA : ∑ a, ∑ i, S (wedgeLM m (isOneOne_testForm a ℓ) (wedgeSpan n h' γ (formBasis n k i)))
      (dTest (realBasis n a) (mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => hS.apply_eq_zero ℓ _ _
  have hB : ∑ a, ∑ i, S (wedgeLM m (isOneOne_testForm a ℓ) (wedgeSpan n h' γ (formBasis n k i)))
      (mulSmoothOnCLM (contDiffOn_dFun (contDiffOn_formCoeff hα i) (realBasis n a)) φ) = 0 := by
    have key := sum_apply_eq_zero_of_forall S
      (fun j : Fin (n * 2) × Fin (Module.finrank ℝ (formSpan n k)) =>
        wedgeLM m (isOneOne_testForm j.1 ℓ) (wedgeSpan n h' γ (formBasis n k j.2)))
      (fun j => mulSmoothOnCLM (contDiffOn_dFun (contDiffOn_formCoeff hα j.2) (realBasis n j.1)) φ)
      (fun x => by
        by_cases hx : x ∈ U
        · rw [Fintype.sum_prod_type]
          have e : ∀ a i,
              mulSmoothOnCLM (contDiffOn_dFun (contDiffOn_formCoeff hα i) (realBasis n a)) φ x •
                (wedgeLM m (isOneOne_testForm a ℓ) (wedgeSpan n h' γ (formBasis n k i)) :
                  RealForm n (2 * (m + 1))) =
              φ x • wedgeTo (by omega : 2 * r + 2 + 2 * k = 2 * (m + 1))
                (coordinateWedge (γ : RealForm n (2 * r)) (testForm a ℓ) : RealForm n (2 * r + 2))
                (dFun (realBasis n a) (formCoeff α i) x •
                  ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) := by
            intro a i
            rw [← wedgeSpan_wedgeLM h h', coe_wedgeSpan_apply h _ _ (by omega), coe_wedgeLM_apply,
              wedgeTo_smul_right, smul_smul, mulSmoothOnCLM_apply]
          simp only [e, ← Finset.smul_sum, ← wedgeTo_sum_right]
          rw [sum_wedgeTo_testForm_dFun_eq_zero hα hαS hαc hx ℓ _ _, smul_zero]
        · simp only [testFunction_eq_zero_of_notMem _ hx, zero_smul, Finset.sum_const_zero])
    rw [Fintype.sum_prod_type] at key
    exact key
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, hA, hB, sub_zero, neg_zero]

end Closed

/-! ### The Leibniz identity `dd^c(R ∧ α) = dd^c R ∧ α` -/

section Leibniz

variable {r k m : ℕ} {α : ComplexModel n → RealForm n (2 * k)}

/-- The form `(γ ∧ T) ∧ bᵢ` read through `wedgeTo`. -/
theorem coe_wedgeSpan_wedgeLM (h : r + 1 + k = m + 1) {T : RealForm n 2} (hT : IsOneOne T)
    (γ : formSpan n r) (β : formSpan n k) (h2 : 2 * r + 2 + 2 * k = 2 * (m + 1)) :
    (wedgeSpan n h (wedgeLM r hT γ) β : RealForm n (2 * (m + 1))) =
      wedgeTo h2 (coordinateWedge (γ : RealForm n (2 * r)) T : RealForm n (2 * r + 2))
        (β : RealForm n (2 * k)) := by
  rw [coe_wedgeSpan_apply h _ _ h2, coe_wedgeLM_apply]

/-- A pointwise identity: `∑ᵢ (s * fᵢ) • ((γ ∧ T) ∧ bᵢ) = s • ((γ ∧ T) ∧ ∑ᵢ fᵢ bᵢ)`. -/
theorem sum_smul_wedgeSpan_wedgeLM (h : r + 1 + k = m + 1) {T : RealForm n 2} (hT : IsOneOne T)
    (γ : formSpan n r) (s : ℝ) (f : Fin (Module.finrank ℝ (formSpan n k)) → ℝ)
    (h2 : 2 * r + 2 + 2 * k = 2 * (m + 1)) :
    ∑ i, (s * f i) • (wedgeSpan n h (wedgeLM r hT γ) (formBasis n k i) : RealForm n (2 * (m + 1)))
      =
      s • wedgeTo h2 (coordinateWedge (γ : RealForm n (2 * r)) T : RealForm n (2 * r + 2))
        (∑ i, f i • ((formBasis n k i : formSpan n k) : RealForm n (2 * k))) := by
  rw [wedgeTo_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_wedgeSpan_wedgeLM h hT γ _ h2, wedgeTo_smul_right, smul_smul]

/-- **The Leibniz identity** `dd^c(R ∧ α) = dd^c R ∧ α` for every current `R` of bidimension
`(m+1,m+1)` and every closed form `α` smooth on `U` with values in `Λ_k`: the first-order terms
`∂_a cᵢ ∂_b φ` and the term `∂_b∂_a cᵢ φ` of `∂_b∂_a(cᵢ φ)` pair to zero with `R`, because
`∑_a Π₁₁(e^a ∧ ℓ) ∧ ∂_a α = 0` and `∑_a Π₁₁(e^a ∧ ℓ) ∧ ∂_a ∂_b α = 0` pointwise
(`sum_wedgeTo_testForm_eq_zero`). -/
theorem ddc_wedgeForm (h : r + 1 + k = m + 1) (h' : r + k = m) (R : LocalProductCurrent n U (m +
    1))
    (hα : ContDiffOn ℝ ∞ α U) (hαS : ∀ x ∈ U, α x ∈ formSpan n k)
    (hαc : ∀ x ∈ U, extDeriv α x = 0) :
    ddc (wedgeForm h R hα) = wedgeForm h' (ddc R) hα := by
  classical
  ext γ φ
  set c₀ : ℝ := -(1 / (4 * Real.pi))
  have hc : ∀ i, ContDiffOn ℝ ∞ (formCoeff α i) U := fun i => contDiffOn_formCoeff hα i
  let X : Fin (n * 2) → Fin (n * 2) → Fin (Module.finrank ℝ (formSpan n k)) →
      formSpan n (m + 1) := fun a b' i =>
    wedgeSpan n h (wedgeLM r (isOneOne_coeffForm a b') γ) (formBasis n k i)
  have h2 : 2 * r + 2 + 2 * k = 2 * (m + 1) := by omega
  -- the two sides in the order `∑ a, ∑ b', ∑ i`
  have hL : ddc (wedgeForm h R hα) γ φ =
      c₀ * ∑ a, ∑ b', ∑ i, R (X a b' i)
        (mulSmoothOnCLM (hc i) (dTest (realBasis n b') (dTest (realBasis n a) φ))) := by
    rw [ddc_apply_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [wedgeForm_apply]
  have hR : wedgeForm h' (ddc R) hα γ φ =
      c₀ * ∑ a, ∑ b', ∑ i, R (X a b' i)
        (dTest (realBasis n b') (dTest (realBasis n a) (mulSmoothOnCLM (hc i) φ))) := by
    rw [wedgeForm_apply]
    simp only [ddc_apply_apply, ← wedgeSpan_wedgeLM h h']
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.mul_sum]
  rw [hL, hR]
  congr 1
  simp only [dTest_dTest_mulSmoothOnCLM, map_add, Finset.sum_add_distrib]
  -- the three extra sums vanish
  have hE1 : ∑ a, ∑ b', ∑ i, R (X a b' i)
      (mulSmoothOnCLM (contDiffOn_dFun (hc i) (realBasis n b')) (dTest (realBasis n a) φ))
        = 0 := by
    have key := sum_apply_eq_zero_of_forall R (fun j : Fin (n * 2) × Fin (n * 2)
      × Fin (Module.finrank ℝ (formSpan n k)) =>
        X j.1 j.2.1 j.2.2)
      (fun j => mulSmoothOnCLM (contDiffOn_dFun (hc j.2.2) (realBasis n j.2.1))
        (dTest (realBasis n j.1) φ)) (fun x => by
        by_cases hx : x ∈ U
        · rw [Fintype.sum_prod_type]
          simp only [Fintype.sum_prod_type, mulSmoothOnCLM_apply, X]
          rw [Finset.sum_eq_zero fun a _ => ?_]
          rw [Finset.sum_congr rfl fun b' _ => sum_smul_wedgeSpan_wedgeLM h
            (isOneOne_coeffForm a b') γ (dTest (realBasis n a) φ x)
            (fun i => dFun (realBasis n b') (formCoeff α i) x) h2, ← Finset.smul_sum]
          have e : ∀ b', coordinateWedge (γ : RealForm n (2 * r)) (coeffForm a b') =
              (coordinateWedge (γ : RealForm n (2 * r)) (testForm b' (coordJ n a)) :
                RealForm n (2 * r + 2)) := fun b' => by rw [coeffForm_comm]; rfl
          simp only [e]
          rw [sum_wedgeTo_coordinateWedge_testForm_eq_zero _
            (fun _ => coeff_sum_mem_formSpan _) (sum_oneWedge_dFun_eq_zero hα hαS hαc hx) _ _ h2,
            smul_zero]
        · simp only [testFunction_eq_zero_of_notMem _ hx, zero_smul, Finset.sum_const_zero])
    simp only [Fintype.sum_prod_type] at key
    exact key
  have hE2 : ∑ a, ∑ b', ∑ i, R (X a b' i)
      (mulSmoothOnCLM (contDiffOn_dFun (hc i) (realBasis n a)) (dTest (realBasis n b') φ))
        = 0 := by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ =>
      Finset.sum_congr rfl fun i _ => ?_).trans hE1
    have hX : X b' a i = X a b' i := by
      dsimp only [X]
      rw [wedgeLM_congr _ _ (coeffForm_comm b' a) γ]
    rw [hX]
  have hE3 : ∑ a, ∑ b', ∑ i, R (X a b' i)
      (mulSmoothOnCLM (contDiffOn_dFun (contDiffOn_dFun (hc i) (realBasis n a)) (realBasis n b'))
        φ) = 0 := by
    have key := sum_apply_eq_zero_of_forall R (fun j : Fin (n * 2) × Fin (n * 2)
      × Fin (Module.finrank ℝ (formSpan n k)) =>
        X j.2.1 j.1 j.2.2)
      (fun j => mulSmoothOnCLM
        (contDiffOn_dFun (contDiffOn_dFun (hc j.2.2) (realBasis n j.2.1)) (realBasis n j.1)) φ)
      (fun x => by
        by_cases hx : x ∈ U
        · rw [Fintype.sum_prod_type]
          simp only [Fintype.sum_prod_type, mulSmoothOnCLM_apply, X]
          rw [Finset.sum_eq_zero fun b' _ => ?_]
          rw [Finset.sum_congr rfl fun a _ => sum_smul_wedgeSpan_wedgeLM h
            (isOneOne_coeffForm a b') γ (φ x)
            (fun i => dFun (realBasis n b') (dFun (realBasis n a) (formCoeff α i)) x) h2,
            ← Finset.smul_sum]
          have e : ∀ a, coordinateWedge (γ : RealForm n (2 * r)) (coeffForm a b') =
              (coordinateWedge (γ : RealForm n (2 * r)) (testForm a (coordJ n b')) :
                RealForm n (2 * r + 2)) := fun a => rfl
          simp only [e]
          rw [sum_wedgeTo_coordinateWedge_testForm_eq_zero _
            (fun _ => coeff_sum_mem_formSpan _)
            (sum_oneWedge_dFun_dFun_eq_zero hα hαS hαc hx (realBasis n b'))
            (coordJ n b') _ h2, smul_zero]
        · simp only [testFunction_eq_zero_of_notMem _ hx, zero_smul, Finset.sum_const_zero])
    simp only [Fintype.sum_prod_type] at key
    rw [Finset.sum_comm]
    exact key
  rw [hE1, hE2, hE3]
  simp

end Leibniz

/-! ### `u T` does not depend on the representing measure -/

section MulBorel

/-- A bounded measurable function vanishing off a set of finite measure is integrable. -/
theorem integrable_of_bounded_of_vanishing {ρ : Measure E} {K : Set E} (hρK : ρ K < ⊤)
    {w : E → ℝ} (hw : Measurable w) {M : ℝ} (hM : ∀ x, |w x| ≤ M) (hsupp : ∀ x ∉ K, w x = 0) :
    Integrable w ρ := by
  have hon : IntegrableOn w K ρ := Measure.integrableOn_of_bounded hρK.ne hw.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM x)
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).mp hon
  by_contra h
  exact hx (hsupp x h)

/-- The positive part of a real density, as a density of measures. -/
def posDensity (d : E → ℝ) (x : E) : ENNReal := ((d x).toNNReal : ENNReal)

theorem integral_withDensity_posDensity (ρ : Measure E) {d : E → ℝ} (hd : Measurable d)
    (w : E → ℝ) : ∫ x, w x ∂(ρ.withDensity (posDensity d)) = ∫ x, max (d x) 0 * w x ∂ρ := by
  change ∫ x, w x ∂(ρ.withDensity fun x => ((d x).toNNReal : ENNReal)) = _
  rw [integral_withDensity_eq_integral_smul hd.real_toNNReal w]
  simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]

theorem withDensity_posDensity_lt_top (ρ : Measure E) {K : Set E} (hK : MeasurableSet K)
    (hρK : ρ K < ⊤) {d : E → ℝ} {M : ℝ} (hdM : ∀ x ∈ K, |d x| ≤ M) :
    ρ.withDensity (posDensity d) K < ⊤ := by
  rw [withDensity_apply _ hK]
  calc ∫⁻ x in K, posDensity d x ∂ρ ≤ ∫⁻ _ in K, ((M.toNNReal : NNReal) : ENNReal) ∂ρ :=
        setLIntegral_mono measurable_const fun x hx => by
          simp only [posDensity, ENNReal.coe_le_coe]
          exact Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hdM x hx))
    _ = (M.toNNReal : ENNReal) * ρ K := setLIntegral_const K _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hρK

/-- A positive measure carried by `U`, finite on the compact subsets of `U`, with a measurable
density bounded on the compact subsets of `U`. -/
structure IsLocalDensity (ρ : Measure E) (d : E → ℝ) : Prop where
  compl : ρ ((U : Set E)ᶜ) = 0
  lt_top : ∀ K : Set E, IsCompact K → K ⊆ U → ρ K < ⊤
  measurable : Measurable d
  bounded : IsLocallyBoundedOn d U

/-- A measurable bounded function vanishing off a compact subset of `U`. -/
structure IsTestWeight (w : E → ℝ) : Prop where
  measurable : Measurable w
  bounded : ∃ M, ∀ x, |w x| ≤ M
  support : ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧ ∀ x ∉ K, w x = 0

theorem IsLocalDensity.neg {ρ : Measure E} {d : E → ℝ} (h : IsLocalDensity (U := U) ρ d) :
    IsLocalDensity (U := U) ρ (fun x => -d x) where
  compl := h.compl
  lt_top := h.lt_top
  measurable := h.measurable.neg
  bounded K hK hKU := by
    obtain ⟨M, hM⟩ := h.bounded K hK hKU
    exact ⟨M, fun x hx => by rw [abs_neg]; exact hM x hx⟩

theorem IsLocalDensity.pos {ρ : Measure E} {d : E → ℝ} (h : IsLocalDensity (U := U) ρ d) :
    IsLocalDensity (U := U) ρ (fun x => max (d x) 0) where
  compl := h.compl
  lt_top := h.lt_top
  measurable := h.measurable.max measurable_const
  bounded K hK hKU := by
    obtain ⟨M, hM⟩ := h.bounded K hK hKU
    refine ⟨M, fun x hx => ?_⟩
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hM x hx)) ((abs_nonneg _).trans (hM x hx))

/-- A test function times a function bounded on the compact subsets of `U` is a test weight. -/
theorem isTestWeight_mul (ψ : 𝓓(U, ℝ)) {c : E → ℝ} (hc : Measurable c)
    (hcb : IsLocallyBoundedOn c U) : IsTestWeight (U := U) (fun x => ψ x * c x) := by
  obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  obtain ⟨M, hM⟩ := hcb _ ψ.hasCompactSupport ψ.tsupport_subset
  refine ⟨ψ.continuous.measurable.mul hc, ⟨|C| * |M|, fun x => ?_⟩, tsupport ψ,
    ψ.hasCompactSupport, ψ.tsupport_subset, fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩
  by_cases hx : x ∈ tsupport ψ
  · rw [abs_mul]
    have h1 : |ψ x| ≤ |C| := by simpa [Real.norm_eq_abs] using (hC x).trans (le_abs_self C)
    exact mul_le_mul h1 ((hM x hx).trans (le_abs_self M)) (abs_nonneg _) (abs_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, abs_zero]
    positivity

theorem isTestWeight_testFunction (ψ : 𝓓(U, ℝ)) : IsTestWeight (U := U) (fun x => ψ x) := by
  have h := isTestWeight_mul ψ (c := fun _ => (1 : ℝ)) measurable_const
    (fun _ _ _ => ⟨1, fun _ _ => by simp⟩)
  simpa only [mul_one] using h

theorem IsLocalDensity.integrable {ρ : Measure E} {d : E → ℝ} (h : IsLocalDensity (U := U) ρ d)
    {w : E → ℝ} (hw : IsTestWeight (U := U) w) : Integrable (fun x => d x * w x) ρ := by
  obtain ⟨Mw, hMw⟩ := hw.bounded
  obtain ⟨K, hK, hKU, hwK⟩ := hw.support
  obtain ⟨Md, hMd⟩ := h.bounded K hK hKU
  refine integrable_of_bounded_of_vanishing (h.lt_top K hK hKU) (h.measurable.mul hw.measurable)
    (M := |Md| * |Mw|) (fun x => ?_) (fun x hx => by simp [hwK x hx])
  by_cases hx : x ∈ K
  · rw [abs_mul]
    exact mul_le_mul ((hMd x hx).trans (le_abs_self _)) ((hMw x).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  · rw [hwK x hx, mul_zero, abs_zero]
    positivity

theorem IsLocalDensity.integrable_withDensity {ρ : Measure E} {d : E → ℝ}
    (h : IsLocalDensity (U := U) ρ d) {w : E → ℝ} (hw : IsTestWeight (U := U) w) :
    Integrable w (ρ.withDensity (posDensity d)) := by
  obtain ⟨Mw, hMw⟩ := hw.bounded
  obtain ⟨K, hK, hKU, hwK⟩ := hw.support
  obtain ⟨Md, hMd⟩ := h.bounded K hK hKU
  exact integrable_of_bounded_of_vanishing
    (withDensity_posDensity_lt_top ρ hK.measurableSet (h.lt_top K hK hKU) hMd) hw.measurable hMw
      hwK

theorem IsLocalDensity.integral_sub_pos_neg {ρ : Measure E} {d : E → ℝ}
    (h : IsLocalDensity (U := U) ρ d) {w : E → ℝ} (hw : IsTestWeight (U := U) w) :
    ∫ x, max (d x) 0 * w x ∂ρ - ∫ x, max (-d x) 0 * w x ∂ρ = ∫ x, d x * w x ∂ρ := by
  rw [← integral_sub (h.pos.integrable hw) (h.neg.pos.integrable hw)]
  congr 1
  funext x
  rw [← sub_mul, max_zero_sub_eq_self]

/-- **Uniqueness of signed Radon measures on `U`**: two locally bounded densities against positive
Radon measures on `U` with the same integrals of all test functions have the same integrals of all
bounded measurable functions vanishing off a compact subset of `U`. -/
theorem integral_eq_of_forall_testFunction {σ ν : Measure E} {f g : E → ℝ}
    (hf : IsLocalDensity (U := U) σ f) (hg : IsLocalDensity (U := U) ν g)
    (h : ∀ ψ : 𝓓(U, ℝ), ∫ x, f x * ψ x ∂σ = ∫ x, g x * ψ x ∂ν) {w : E → ℝ}
    (hw : IsTestWeight (U := U) w) : ∫ x, f x * w x ∂σ = ∫ x, g x * w x ∂ν := by
  set μ₁ := σ.withDensity (posDensity f) + ν.withDensity (posDensity (fun x => -g x))
  set μ₂ := σ.withDensity (posDensity (fun x => -f x)) + ν.withDensity (posDensity g)
  have hexp : ∀ {v : E → ℝ}, IsTestWeight (U := U) v →
      ∫ x, v x ∂μ₁ - ∫ x, v x ∂μ₂ = ∫ x, f x * v x ∂σ - ∫ x, g x * v x ∂ν := by
    intro v hv
    rw [integral_add_measure (hf.integrable_withDensity hv) (hg.neg.integrable_withDensity hv),
      integral_add_measure (hf.neg.integrable_withDensity hv) (hg.integrable_withDensity hv),
      integral_withDensity_posDensity _ hf.measurable,
      integral_withDensity_posDensity _ hg.neg.measurable,
      integral_withDensity_posDensity _ hf.neg.measurable,
      integral_withDensity_posDensity _ hg.measurable,
      ← hf.integral_sub_pos_neg hv, ← hg.integral_sub_pos_neg hv]
    ring
  have hcompl : ∀ (ρ : Measure E) (d : E → ℝ), ρ ((U : Set E)ᶜ) = 0 →
      ρ.withDensity (posDensity d) ((U : Set E)ᶜ) = 0 := fun ρ d hρ =>
    withDensity_absolutelyContinuous ρ _ hρ
  have hfin : ∀ (ρ : Measure E) (d : E → ℝ), IsLocalDensity (U := U) ρ d → ∀ K : Set E,
      IsCompact K → K ⊆ U → ρ.withDensity (posDensity d) K < ⊤ := fun ρ d hd K hK hKU => by
    obtain ⟨M, hM⟩ := hd.bounded K hK hKU
    exact withDensity_posDensity_lt_top ρ hK.measurableSet (hd.lt_top K hK hKU) hM
  have hμ : μ₁ = μ₂ := by
    apply eq_of_forall_testFunction_integral_eq (U := U)
    · rw [add_apply, hcompl σ _ hf.compl, hcompl ν _ hg.compl, add_zero]
    · rw [add_apply, hcompl σ _ hf.compl, hcompl ν _ hg.compl, add_zero]
    · intro K hK hKU
      rw [add_apply]
      exact ENNReal.add_lt_top.mpr ⟨hfin σ f hf K hK hKU, hfin ν _ hg.neg K hK hKU⟩
    · intro K hK hKU
      rw [add_apply]
      exact ENNReal.add_lt_top.mpr ⟨hfin σ _ hf.neg K hK hKU, hfin ν g hg K hK hKU⟩
    · intro ψ
      have := hexp (isTestWeight_testFunction ψ)
      rw [h ψ, sub_self] at this
      exact sub_eq_zero.mp this
  have := hexp hw
  rw [hμ, sub_self] at this
  exact (sub_eq_zero.mp this.symm)

/-- **`u T` does not depend on the representing measure**: if the coefficient `T(γ)` is the
signed measure `g ν` (`ν` a positive Radon measure on `U`, `g` locally bounded), then
`(u T)(γ) = u g ν`. -/
theorem mulBorel_apply_of_integral_eq {q : ℕ} {T : LocalProductCurrent n U q} (hT : IsPositive T)
    (γ : formSpan n q) {ν : Measure E} {g : E → ℝ} (hg : IsLocalDensity (U := U) ν g)
    (hrep : ∀ ψ : 𝓓(U, ℝ), T γ ψ = ∫ x, ψ x * g x ∂ν) {u : E → ℝ} (hu : Measurable u)
    (hub : IsLocallyBoundedOn u U) (φ : 𝓓(U, ℝ)) :
    mulBorel T u γ φ = ∫ x, φ x * (u x * g x) ∂ν := by
  have hf : IsLocalDensity (U := U) hT.traceMeasure (hT.density γ) :=
    ⟨hT.traceMeasure_compl, fun K hK hKU => hT.traceMeasure_lt_top hK hKU,
      hT.measurable_density γ, fun K _ _ => by
        obtain ⟨C, -, hC⟩ := hT.exists_abs_density_le γ
        exact ⟨C, fun x _ => hC x⟩⟩
  have key := integral_eq_of_forall_testFunction hf hg (fun ψ => by
      have e1 := hT.apply_eq_integral_density γ ψ
      rw [hrep ψ] at e1
      rw [show (fun x => hT.density γ x * ψ x) = fun x => ψ x * hT.density γ x from
          funext fun x => mul_comm _ _,
        show (fun x => g x * ψ x) = fun x => ψ x * g x from funext fun x => mul_comm _ _]
      exact e1.symm) (isTestWeight_mul φ hu hub)
  rw [mulBorel_apply hT hu hub]
  calc ∫ x, φ x * (u x * hT.density γ x) ∂hT.traceMeasure =
        ∫ x, hT.density γ x * (φ x * u x) ∂hT.traceMeasure :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
    _ = ∫ x, g x * (φ x * u x) ∂ν := key
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by ring)

end MulBorel

/-! ### Multiplication by a smooth closed strongly positive form commutes with the recursion -/

section Recursion

variable {r k m : ℕ} {α : ComplexModel n → RealForm n (2 * k)}

/-- **`u (T ∧ α) = (u T) ∧ α`** for a positive current `T`, a form `α` smooth on `U` and strongly
positive at every point of `U`, and a measurable `u` bounded on the compact subsets of `U`. -/
theorem mulBorel_wedgeForm (h : r + k = m) {T : LocalProductCurrent n U m} (hT : IsPositive T)
    (hα : ContDiffOn ℝ ∞ α U) (hαp : ∀ x ∈ U, α x ∈ spCone k) {u : E → ℝ} (hu : Measurable u)
    (hub : IsLocallyBoundedOn u U) :
    mulBorel (wedgeForm h T hα) u = wedgeForm h (mulBorel T u) hα := by
  classical
  have hTα := isPositive_wedgeForm h hT hα hαp
  ext γ φ
  set c' : Fin (Module.finrank ℝ (formSpan n k)) → E → ℝ := fun i =>
    (U : Set E).indicator (formCoeff α i)
  have hc'm : ∀ i, Measurable (c' i) := fun i =>
    measurable_indicator_of_continuousOn (contDiffOn_formCoeff hα i).continuousOn
  have hc'b : ∀ i, IsLocallyBoundedOn (c' i) U := fun i =>
    isLocallyBoundedOn_indicator_of_continuousOn (contDiffOn_formCoeff hα i).continuousOn
  have hc' : ∀ (ψ : 𝓓(U, ℝ)) i x, ψ x * formCoeff α i x = ψ x * c' i x := by
    intro ψ i x
    by_cases hx : x ∈ (U : Set E)
    · simp only [c', Set.indicator_of_mem hx]
    · simp only [testFunction_eq_zero_of_notMem ψ hx, zero_mul]
  set f : Fin (Module.finrank ℝ (formSpan n k)) → E → ℝ := fun i =>
    hT.density (wedgeSpan n h γ (formBasis n k i))
  set g : E → ℝ := fun x => ∑ i, c' i x * f i x
  have hfi : ∀ i, IsLocalDensity (U := U) hT.traceMeasure (f i) := fun i =>
    ⟨hT.traceMeasure_compl, fun K hK hKU => hT.traceMeasure_lt_top hK hKU,
      hT.measurable_density _, fun K _ _ => by
        obtain ⟨C, -, hC⟩ := hT.exists_abs_density_le (wedgeSpan n h γ (formBasis n k i))
        exact ⟨C, fun x _ => hC x⟩⟩
  have hg : IsLocalDensity (U := U) hT.traceMeasure g := by
    refine ⟨hT.traceMeasure_compl, fun K hK hKU => hT.traceMeasure_lt_top hK hKU,
      Finset.measurable_sum _ fun i _ => (hc'm i).mul (hfi i).measurable, fun K hK hKU => ?_⟩
    choose M hM using fun i => hc'b i K hK hKU
    choose C hC using fun i => (hfi i).bounded K hK hKU
    refine ⟨∑ i, |M i| * |C i|, fun x hx => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul ((hM i x hx).trans (le_abs_self _)) ((hC i x hx).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have hint : ∀ (ψ : 𝓓(U, ℝ)) (w : E → ℝ), Measurable w → IsLocallyBoundedOn w U →
      ∀ i, Integrable (fun x => f i x * (ψ x * w x * c' i x)) hT.traceMeasure := by
    intro ψ w hw hwb i
    refine (hfi i).integrable (isTestWeight_mul ψ (c := fun x => w x * c' i x) (hw.mul (hc'm i))
      fun K hK hKU => ?_) |>.congr
      (ae_of_all _ fun x => by simp only; ring)
    obtain ⟨M₁, hM₁⟩ := hwb K hK hKU
    obtain ⟨M₂, hM₂⟩ := hc'b i K hK hKU
    exact ⟨|M₁| * |M₂|, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul ((hM₁ x hx).trans (le_abs_self _)) ((hM₂ x hx).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)⟩
  have hrep : ∀ ψ : 𝓓(U, ℝ), wedgeForm h T hα γ ψ = ∫ x, ψ x * g x ∂hT.traceMeasure := by
    intro ψ
    rw [wedgeForm_apply]
    simp only [hT.apply_eq_integral_density, mulSmoothOnCLM_apply, hc']
    rw [← integral_finsetSum _ fun i _ => (hint ψ (fun _ => 1) measurable_const
      (fun _ _ _ => ⟨1, fun _ _ => by simp⟩) i).congr (ae_of_all _ fun x => by simp only; ring)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [f]; ring
  rw [mulBorel_apply_of_integral_eq hTα γ hg hrep hu hub φ, wedgeForm_apply]
  simp only [mulBorel_apply hT hu hub, mulSmoothOnCLM_apply, hc']
  rw [← integral_finsetSum _ fun i _ => (hint φ u hu hub i).congr
    (ae_of_all _ fun x => by simp only; ring)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [g, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [f]; ring

/-- **One step of the recursion commutes with `∧ α`**: `dd^c(u (T ∧ α)) = dd^c(u T) ∧ α` for a
positive current `T` and a smooth closed strongly positive form `α`. -/
theorem ddcMul_wedgeForm (h : r + 1 + k = m + 1) (h' : r + k = m)
    {T : LocalProductCurrent n U (m + 1)} (hT : IsPositive T) (hα : ContDiffOn ℝ ∞ α U)
    (hαp : ∀ x ∈ U, α x ∈ spCone k) (hαc : ∀ x ∈ U, extDeriv α x = 0) {u : E → ℝ}
    (hu : IsLocallyBoundedPshOn U u) :
    ddcMul (wedgeForm h T hα) u = wedgeForm h' (ddcMul T u) hα := by
  rw [ddcMul, ddcMul, mulBorel_wedgeForm h hT hα hαp
    (measurable_indicator_of_isLocallyBoundedPshOn hu)
    (isLocallyBoundedOn_indicator hu),
    ddc_wedgeForm h h' _ hα (fun x hx => mem_formSpan_of_mem_spCone (hαp x hx)) hαc]

/-- `S ∧ α` is closed in every bidimension (for `S` closed and `α` closed). -/
theorem isClosedAny_wedgeForm (h : r + k = m) {S : LocalProductCurrent n U m}
    (hS : IsClosedAny m S) (hα : ContDiffOn ℝ ∞ α U) (hαS : ∀ x ∈ U, α x ∈ formSpan n k)
    (hαc : ∀ x ∈ U, extDeriv α x = 0) : IsClosedAny r (wedgeForm h S hα) := by
  cases r with
  | zero => trivial
  | succ r =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact isClosedCurrent_wedgeForm h hS hα hαS hαc

/-- **Multiplication by a smooth closed strongly positive form commutes with the recursive
Bedford--Taylor product** (`bt:recursive-product`): for `T` positive and closed of bidimension
`(r + k + q, r + k + q)`, `α` smooth on `U`, closed and strongly positive of degree `2k`, and
`u₁, …, u_q` locally bounded PSH on `U`, `B(u; T ∧ α) = B(u; T) ∧ α`. -/
theorem btProduct_wedgeForm (hα : ContDiffOn ℝ ∞ α U) (hαp : ∀ x ∈ U, α x ∈ spCone k)
    (hαc : ∀ x ∈ U, extDeriv α x = 0) : ∀ (q r : ℕ) (u : Fin q → E → ℝ)
    (T : LocalProductCurrent n U (r + k + q)) (h : r + q + k = r + k + q), IsPositive T →
    IsClosedAny (r + k + q) T → (∀ i, IsLocallyBoundedPshOn U (u i)) →
    btProduct q r u (wedgeForm h T hα) = wedgeForm rfl (btProduct q (r + k) u T) hα
  | 0, _, _, _, _, _, _, _ => rfl
  | q + 1, r, u, T, h, hT, hTc, hu => by
    rw [btProduct_succ, btProduct_succ,
      ddcMul_wedgeForm (r := r + q) (m := r + k + q) h (by omega) hT hα hαp hαc (hu (Fin.last q))]
    obtain ⟨h1, h2⟩ := isPositive_ddcMul (m := r + k + q) hT hTc (hu (Fin.last q))
    exact btProduct_wedgeForm hα hαp hαc q r (Fin.init u) _ (by omega) h1 h2 fun i => hu _

/-- `T ∧ α` is a positive closed current, so `B(u; T ∧ α)` is defined, positive and closed. -/
theorem isPositive_btProduct_wedgeForm (hα : ContDiffOn ℝ ∞ α U) (hαp : ∀ x ∈ U, α x ∈ spCone k)
    (hαc : ∀ x ∈ U, extDeriv α x = 0) (q r : ℕ) (u : Fin q → E → ℝ)
    (T : LocalProductCurrent n U (r + k + q)) (h : r + q + k = r + k + q) (hT : IsPositive T)
    (hTc : IsClosedAny (r + k + q) T) (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    IsPositive (btProduct q r u (wedgeForm h T hα)) ∧
      IsClosedAny r (btProduct q r u (wedgeForm h T hα)) :=
  isPositive_btProduct q r u _ (isPositive_wedgeForm h hT hα hαp)
    (isClosedAny_wedgeForm h hTc hα (fun x hx => mem_formSpan_of_mem_spCone (hαp x hx)) hαc) hu

end Recursion

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
