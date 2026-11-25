/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentLebesgue

/-!
# The gradient pairing of a positive current and its Cauchy–Schwarz inequality

Xia's gradient density and pairing formulas describe a positive semidefinite density
matrix for a positive current. The Lean lemma below gives a pointwise, real bilinear estimate
with a parameter `t > 0`. It is related to the pointwise pairing used in
[Xia's proof of the integrated Cauchy–Schwarz estimate](https://github.com/MingchenXia/foundations-of-pluripotential-theory/blob/5d7f16338ae82d4933193a0cb331365e737824db/chapters/inputs/q08-current-gradients.tex#L92-L99),
which combines the pointwise pairing with integral Cauchy–Schwarz for the weighted test.

Let `T` be a positive current of bidimension `(q+1,q+1)` on an open set `U ⊆ ℂⁿ`
(`SGPT.Foundations.Analysis.Pending.LocalProductCurrents`: `T(β)(φ) = ⟨T, φ β⟩` for constant real
`(q+1,q+1)`-forms `β`), with trace measure `σ_T` and pointwise density form `L_x`
(`LocalCurrentLebesgue.densityForm`, nonnegative on the strongly positive cone for
`σ_T`-almost every `x`).  Fix a constant strongly positive `(q,q)`-form `γ`; then `γ ∧ T` is a
positive current of bidimension `(1,1)`.  In the real coordinates `x_a` of `ℂⁿ`
(`LocalBedfordTaylorProducts.realBasis`) put `P_{ab} = Π₁₁(e^a ∧ e^b ∘ i)`
(`coeffForm`), so that `dd^c u = -(1/4π) ∑ ∂_a∂_b u P_{ab}`.

* `quadForm γ ξ ζ = -∑_{a,b} ξ_a ζ_b γ ∧ P_{ab}` is a symmetric bilinear map with values in the
  constant `(q+1,q+1)`-forms (`quadForm_comm`); for `ξ = ∂u(x)` it is `4π γ ∧ du ∧ d^c u` up to
  the normalization, and `quadForm γ ξ ξ` is strongly positive (`quadForm_mem_posCone`:
  `-∑ ξ_a ξ_b P_{ab}(v, iv) = ξ(v)² + ξ(iv)²`).  Hence `(ξ, ζ) ↦ L_x(quadForm γ ξ ζ)` is the
  positive semidefinite density matrix `H(x)` of FPT for `σ_T`-almost every `x`
  (`ae_densityForm_quadForm_nonneg`).
* **The Cauchy–Schwarz inequality** in the arithmetic–geometric form
  `2 |L_x(Q(ξ, ζ))| ≤ t L_x(Q(ξ, ξ)) + L_x(Q(ζ, ζ)) / t` for all `t > 0`
  (`ae_two_mul_abs_densityForm_quadForm_le`), from the general
  `two_mul_abs_le_of_nonneg` for positive semidefinite symmetric bilinear forms.
* **The gradient pairing**: for the derivative `dw ∧ ℓ` of a function against a real linear form
  `ℓ`, the `(1,1)`-part is `∑_a ∂_a w Π₁₁(e^a ∧ ℓ)` (`testForm`), and
  `∑_a ξ_a L_x(γ ∧ Π₁₁(e^a ∧ ℓ)) = -L_x(Q(ξ, η_ℓ))` with the coefficients
  `η_ℓ = (-ℓ(i b_b))_b` of `ℓ` in the basis `e^b ∘ i` (`sum_mul_densityForm_testWedge`,
  `sum_dualCoeff_smul_coordJ`).
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
open SGPT.Foundations.Analysis.Pending.ClosedProductCurrents

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-! ### Real linear forms in the basis `e^b ∘ i` -/

section Dual

/-- The coefficients of a real linear form `ℓ` in the basis `e^b ∘ i` of the real dual:
`η_b = -ℓ(i b_b)`. -/
def dualCoeff (ℓ : (ComplexModel n) →L[ℝ] ℝ) (b : Fin (n * 2)) : ℝ := -ℓ (Complex.I • realBasis n
    b)

theorem I_smul_I_smul (v : (ComplexModel n)) : Complex.I • (Complex.I • v) = -v := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- `ℓ = ∑_b η_b (e^b ∘ i)`. -/
theorem sum_dualCoeff_smul_coordJ (ℓ : (ComplexModel n) →L[ℝ] ℝ) : ∑ b, dualCoeff ℓ b • coordJ n b
    = ℓ := by
  ext v
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, coordJ_apply, smul_eq_mul, dualCoeff]
  have h := sum_coordCLM_smul (n := n) (Complex.I • v)
  have e : ℓ (Complex.I • (Complex.I • v)) =
      ∑ b, coordCLM n b (Complex.I • v) * ℓ (Complex.I • realBasis n b) := by
    conv_lhs => rw [← h]
    rw [Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm, map_smul, smul_eq_mul]
  rw [I_smul_I_smul, map_neg] at e
  rw [show ℓ v = -(-ℓ v) by ring, e, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `Π₁₁(e^a ∧ ℓ)` is linear in `ℓ`. -/
theorem testForm_sum_smul (a : Fin (n * 2)) (c : Fin (n * 2) → ℝ)
    (ℓ : Fin (n * 2) → (ComplexModel n) →L[ℝ] ℝ) :
    testForm a (∑ b, c b • ℓ b) = ∑ b, c b • testForm a (ℓ b) := by
  ext w
  rw [ClosedProductCurrents.eq_vec_two w, testForm_apply]
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    testForm_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `Π₁₁(e^a ∧ ℓ) = ∑_b η_b P_{ab}`. -/
theorem testForm_eq_sum_coeffForm (a : Fin (n * 2)) (ℓ : (ComplexModel n) →L[ℝ] ℝ) :
    testForm a ℓ = ∑ b, dualCoeff ℓ b • coeffForm a b := by
  conv_lhs => rw [← sum_dualCoeff_smul_coordJ ℓ]
  rw [testForm_sum_smul]
  rfl

end Dual

/-! ### The forms `γ ∧ P_{ab}` and the quadratic form -/

section Quad

variable {q : ℕ}

/-- `γ ∧ P_{ab}`. -/
def coeffWedge (γ : formSpan n q) (a b : Fin (n * 2)) : formSpan n (q + 1) :=
  wedgeLM q (isOneOne_coeffForm a b) γ

/-- `γ ∧ Π₁₁(e^a ∧ ℓ)`: the `(q+1,q+1)`-forms tested by closedness (`IsClosedCurrent`). -/
def testWedge (γ : formSpan n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (a : Fin (n * 2))
    : formSpan n (q + 1) :=
  wedgeLM q (isOneOne_testForm a ℓ) γ

theorem coe_sum_smul_wedgeLM {ι : Type*} (s : Finset ι) (c : ι → ℝ) {β : ι → RealForm n 2}
    (hβ : ∀ i, IsOneOne (β i)) (γ : formSpan n q) :
    ((∑ i ∈ s, c i • wedgeLM q (hβ i) γ : formSpan n (q + 1)) : RealForm n (2 * (q + 1))) =
      coordinateWedge (γ : RealForm n (2 * q)) (∑ i ∈ s, c i • β i) := by
  rw [← wedgeBilin_apply, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, coe_wedgeLM_apply, map_smul, wedgeBilin_apply]

theorem testWedge_eq_sum (γ : formSpan n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (a : Fin (n * 2)) :
    testWedge γ ℓ a = ∑ b, dualCoeff ℓ b • coeffWedge γ a b := by
  ext1
  rw [show (∑ b, dualCoeff ℓ b • coeffWedge γ a b) =
      ∑ b, dualCoeff ℓ b • wedgeLM q (isOneOne_coeffForm a b) γ from rfl,
    coe_sum_smul_wedgeLM _ _ (fun b => isOneOne_coeffForm a b), testWedge, coe_wedgeLM_apply,
    testForm_eq_sum_coeffForm]

theorem testWedge_add (γ γ' : formSpan n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (a : Fin (n * 2)) :
    testWedge (γ + γ') ℓ a = testWedge γ ℓ a + testWedge γ' ℓ a := map_add _ _ _

theorem testWedge_smul (c : ℝ) (γ : formSpan n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (a : Fin (n * 2))
    :
    testWedge (c • γ) ℓ a = c • testWedge γ ℓ a := map_smul _ _ _

theorem coeffWedge_comm (γ : formSpan n q) (a b : Fin (n * 2)) :
    coeffWedge γ a b = coeffWedge γ b a := by
  ext1
  simp only [coeffWedge, coe_wedgeLM_apply, coeffForm_comm a b]

variable (q) in
/-- The bilinear map `Q(ξ, ζ) = -∑_{a,b} ξ_a ζ_b γ ∧ P_{ab}`. -/
def quadForm (γ : formSpan n q) :
    (Fin (n * 2) → ℝ) →ₗ[ℝ] (Fin (n * 2) → ℝ) →ₗ[ℝ] formSpan n (q + 1) :=
  LinearMap.mk₂ ℝ (fun ξ ζ => ∑ a, ∑ b, (-(ξ a * ζ b)) • coeffWedge γ a b)
    (fun ξ ξ' ζ => by
      simp only [Pi.add_apply, add_mul, neg_add, add_smul, Finset.sum_add_distrib])
    (fun c ξ ζ => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      ring)
    (fun ξ ζ ζ' => by
      simp only [Pi.add_apply, mul_add, neg_add, add_smul, Finset.sum_add_distrib])
    (fun c ξ ζ => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      ring)

theorem quadForm_apply (γ : formSpan n q) (ξ ζ : Fin (n * 2) → ℝ) :
    quadForm q γ ξ ζ = ∑ a, ∑ b, (-(ξ a * ζ b)) • coeffWedge γ a b := rfl

theorem quadForm_comm (γ : formSpan n q) (ξ ζ : Fin (n * 2) → ℝ) :
    quadForm q γ ξ ζ = quadForm q γ ζ ξ := by
  rw [quadForm_apply, quadForm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [coeffWedge_comm γ b a, mul_comm (ξ b) (ζ a)]

/-- The real two-form `-∑_{a,b} ξ_a ξ_b P_{ab}`. -/
def quadTwoForm (ξ : Fin (n * 2) → ℝ) : RealForm n 2 :=
  ∑ a, ∑ b, (-(ξ a * ξ b)) • coeffForm a b

theorem quadTwoForm_apply_line (ξ : Fin (n * 2) → ℝ) (v : (ComplexModel n)) :
    quadTwoForm ξ ![v, Complex.I • v] =
      (∑ a, ξ a * coordCLM n a v) ^ 2 + (∑ a, ξ a * coordCLM n a (Complex.I • v)) ^ 2 := by
  simp only [quadTwoForm, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    coeffForm_apply, I_smul_I_smul, map_neg, smul_eq_mul, sq, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem isSemipositiveOneOne_quadTwoForm (ξ : Fin (n * 2) → ℝ) :
    IsSemipositiveOneOne (quadTwoForm ξ) := by
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · simp only [quadTwoForm, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, isOneOne_coeffForm _ _ u v]
  · change 0 ≤ quadTwoForm ξ ![v, Complex.I • v]
    rw [quadTwoForm_apply_line]
    positivity

theorem coe_quadForm_self (γ : formSpan n q) (ξ : Fin (n * 2) → ℝ) :
    (quadForm q γ ξ ξ : RealForm n (2 * (q + 1))) =
      coordinateWedge (γ : RealForm n (2 * q)) (quadTwoForm ξ) := by
  rw [quadForm_apply, quadTwoForm, ← wedgeBilin_apply, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Submodule.coe_smul, coeffWedge, coe_wedgeLM_apply, map_smul, wedgeBilin_apply]

/-- **`Q(ξ, ξ)` is strongly positive** when `γ` is. -/
theorem quadForm_mem_posCone {γ : formSpan n q} (hγ : γ ∈ posCone n q) (ξ : Fin (n * 2) → ℝ) :
    quadForm q γ ξ ξ ∈ posCone n (q + 1) := by
  change (quadForm q γ ξ ξ : RealForm n (2 * (q + 1))) ∈ spCone (q + 1)
  rw [coe_quadForm_self]
  exact wedge_mem_spCone hγ (isSemipositiveOneOne_quadTwoForm ξ)

end Quad

/-! ### Cauchy–Schwarz for positive semidefinite symmetric bilinear forms -/

section CauchySchwarz

/-- **Cauchy–Schwarz, arithmetic–geometric form**: for a symmetric bilinear form with
`B v v ≥ 0`, `2 |B u v| ≤ t B u u + B v v / t` for every `t > 0`. -/
theorem two_mul_abs_le_of_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u) (hpos : ∀ v, 0 ≤ B v v)
    (u v : V) {t : ℝ} (ht : 0 < t) : 2 * |B u v| ≤ t * B u u + B v v / t := by
  have h1 := hpos (t • u - v)
  have h2 := hpos (t • u + v)
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at h1 h2
  rw [hsymm v u] at h1 h2
  have key : 2 * t * |B u v| ≤ t * t * B u u + B v v := by
    rcases abs_cases (B u v) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith
  rw [div_eq_mul_inv, ← sub_nonneg]
  have e : t * B u u + B v v * t⁻¹ - 2 * |B u v| =
      t⁻¹ * (t * t * B u u + B v v - 2 * t * |B u v|) := by
    field_simp
  rw [e]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (by linarith)

end CauchySchwarz

/-! ### The density matrix of `γ ∧ T` -/

section Density

variable {U : Opens (ComplexModel n)} {q : ℕ} {T : LocalProductCurrent n U (q + 1)}

theorem densityForm_quadForm (hT : IsPositive T) (x : (ComplexModel n)) (γ : formSpan n q)
    (ξ ζ : Fin (n * 2) → ℝ) :
    densityForm hT x (quadForm q γ ξ ζ) =
      ∑ a, ∑ b, (-(ξ a * ζ b)) * densityForm hT x (coeffWedge γ a b) := by
  simp only [quadForm_apply, map_sum, map_smul, smul_eq_mul]

/-- **The density matrix is positive semidefinite** for `σ_T`-almost every point. -/
theorem ae_densityForm_quadForm_nonneg (hT : IsPositive T) {γ : formSpan n q}
    (hγ : γ ∈ posCone n q) :
    ∀ᵐ x ∂hT.traceMeasure, ∀ ξ : Fin (n * 2) → ℝ, 0 ≤ densityForm hT x (quadForm q γ ξ ξ) := by
  filter_upwards [ae_densityForm_nonneg hT] with x hx ξ
  exact hx _ (quadForm_mem_posCone hγ ξ)

/-- A pointwise Cauchy–Schwarz estimate for the density matrix. For `σ_T`-almost every `x`,
for all `ξ, ζ` and `t > 0`, it bounds `2 |L_x(Q(ξ, ζ))|` by
`t L_x(Q(ξ, ξ)) + L_x(Q(ζ, ζ)) / t`. This is a pointwise ingredient related to Xia's
integrated weighted estimate in `eq:current-gradient-cauchy-schwarz`. -/
theorem ae_two_mul_abs_densityForm_quadForm_le (hT : IsPositive T) {γ : formSpan n q}
    (hγ : γ ∈ posCone n q) :
    ∀ᵐ x ∂hT.traceMeasure, ∀ (ξ ζ : Fin (n * 2) → ℝ) (t : ℝ), 0 < t →
      2 * |densityForm hT x (quadForm q γ ξ ζ)| ≤
        t * densityForm hT x (quadForm q γ ξ ξ) + densityForm hT x (quadForm q γ ζ ζ) / t := by
  filter_upwards [ae_densityForm_quadForm_nonneg hT hγ] with x hx ξ ζ t ht
  exact two_mul_abs_le_of_nonneg ((quadForm q γ).compr₂ (densityForm hT x))
    (fun u v => by simp only [LinearMap.compr₂_apply, quadForm_comm γ u v]) hx ξ ζ ht

/-- **The gradient pairing**: `∑_a ξ_a L_x(γ ∧ Π₁₁(e^a ∧ ℓ)) = -L_x(Q(ξ, η_ℓ))`. -/
theorem sum_mul_densityForm_testWedge (hT : IsPositive T) (x : (ComplexModel n)) (γ : formSpan n q)
    (ℓ : (ComplexModel n) →L[ℝ] ℝ) (ξ : Fin (n * 2) → ℝ) :
    ∑ a, ξ a * densityForm hT x (testWedge γ ℓ a) =
      -densityForm hT x (quadForm q γ ξ (dualCoeff ℓ)) := by
  rw [densityForm_quadForm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [testWedge_eq_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

end Density

end SGPT.Currents.Gradient
