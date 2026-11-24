/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.OneOneFormMixedTrace
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentSemicontinuity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConstantFormProducts

/-!
# The determinant of the absolutely continuous part of a positive `(1,1)`-current

Blueprint `ana:one-one-density-duality`, `ana:ac-determinant-semicontinuity`
    (`blueprint/src/analytic.tex`; TN.5, toward
`ana:volume-semicontinuity`).  Source: Boucksom 2002 (`bou02-volume`), Lemma 3.5 (arXiv)
    / Prop. 2.1 (published): the
semicontinuity of `det(T_ac)^{1/n}` under weak convergence.

On `ℂⁿ`, `n = m + 1`, a current of bidimension `(m, m)` is recorded on the constant forms `Λ_m`
    (`LocalProductCurrents`), and
its absolutely continuous part has the pointwise density `acWeight(x) L_x`, a linear functional on
    `Λ_m`
(`LocalCurrentLebesgue`).

* `oneWedge_oneWedge_apply_cons_cons`, **`eq_zero_of_forall_topDensity_oneWedge`**: a form `γ` of
    degree `2n - 2` with
  `ℓ₁ ∧ ℓ₂ ∧ γ = 0` for all real covectors `ℓ₁, ℓ₂` is zero (extend a frame on which `γ` does not
    vanish to a basis);
* `topDensity_coordinateWedge_oneForms`, `pairing`, `pairing_injective`: the wedge pairing
    `Λ_m × Λ² → ℝ`,
  `(γ, α) ↦ ⟨γ ∧ α⟩`, is nondegenerate on the `Λ_m` side;
* **`exists_isOneOne_eq_topDensity`**: every linear functional on `Λ_m` is `γ ↦ ⟨γ ∧ α⟩` for a
    real `(1,1)`-form `α`
  (duality, then the `(1,1)`-part `Π₁₁ α`, using `det_ℝ J = 1` and the `J`-invariance of `Λ_m`);
* `posSemidef_of_nonneg`: if the functional is nonnegative on the strongly positive cone,
    `H_α` is positive semidefinite;
* `isGLB_topDensity_wedge_formPower_of_posSemidef`: `inf_β ⟨β^m ∧ α⟩ = (n!/πⁿ) det(H_α)^{1/n}`
    over the semipositive `β`
  with `H_β > 0`, `det H_β = 1`;
* for a positive current `T` of bidimension `(m, m)`: `exists_isOneOne_acDensity_eq` (at every
    point,
  `acWeight(x) L_x = ⟨· ∧ α_x⟩` for a `(1,1)`-form `α_x`), **`ae_acInf_detCone_eq`** (for almost
    every `x`, `H_{α_x} ≥ 0` and
  the infimum `D_C(T)(x)` of `ana:ac-density-liminf` over `C = detCone m` is
    `(n!/πⁿ) det(H_{α_x})^{1/n}`), and
  **`ae_liminf_rpow_det_le`**: Boucksom's semicontinuity
    `det(H_{α_x}(T))^{1/n} ≥ liminf_k det(H_{α_x}(T_k))^{1/n}` for
  almost every `x ∈ U` when `T_k → T` weakly;
* the same with a chosen representative: `acForm`, **`acMatrix`** (the density matrix `A_x` of
    `T_ac`, with
  `acWeight(x) L_x(β^m) = m! Re tr(A_x adj H_β) / πⁿ`), `ae_posSemidef_acMatrix`,
    `ae_acInf_detCone_eq_acMatrix` and
  **`ae_liminf_rpow_det_acMatrix_le`**.

Sorry-free.
-/

@[expose] public section

noncomputable section

open Finset Matrix Filter MeasureTheory TopologicalSpace
open scoped ComplexOrder MatrixOrder ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.LocalCurrentDeterminant

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
    TopDegreeDensity
  LocalProductCurrents LocalCurrentLebesgue LocalCurrentSemicontinuity ClosedProductCurrents
    ConstantFormProducts
  CoordinateWedgeAssoc OneOneFormMixedTrace DeterminantTraceInf

attribute [local instance] addCommGroupFormSpan

/-! ### Two covectors against a form of degree `2n - 2` -/

section Covectors

variable {n : ℕ}

/-- `(ℓ ∧ A)(x, w) = A(w)` when `ℓ(x) = 1` and `ℓ` vanishes on `w`. -/
theorem oneWedge_apply_cons {k : ℕ} (ℓ : ComplexModel n →L[ℝ] ℝ) (A : RealForm n k)
    (x : ComplexModel n)
    (w : Fin k → ComplexModel n) (hx : ℓ x = 1) (hw : ∀ i, ℓ (w i) = 0) :
    oneWedge ℓ A (Fin.cons x w) = A w := by
  rw [oneWedge, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  simp [hx, hw, Fin.removeNth_zero, Fin.tail_cons]

/-- `(ℓ₁ ∧ ℓ₂ ∧ γ)(x, y, v) = γ(v)` for covectors dual to `x, y` and vanishing on `v`. -/
theorem oneWedge_oneWedge_apply_cons_cons {k : ℕ} (ℓ₁ ℓ₂ : ComplexModel n →L[ℝ] ℝ)
    (γ : RealForm n k)
    (x y : ComplexModel n) (v : Fin k → ComplexModel n) (h₁x : ℓ₁ x = 1) (h₁y : ℓ₁ y = 0)
    (h₁v : ∀ i, ℓ₁ (v i) = 0) (h₂y : ℓ₂ y = 1) (h₂v : ∀ i, ℓ₂ (v i) = 0) :
    oneWedge ℓ₁ (oneWedge ℓ₂ γ) (Fin.cons x (Fin.cons y v)) = γ v := by
  rw [oneWedge_apply_cons ℓ₁ _ x _ h₁x, oneWedge_apply_cons ℓ₂ γ y v h₂y h₂v]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h₁y
  · simpa using h₁v j

/-- **A form of degree `2n - 2` killed by all `ℓ₁ ∧ ℓ₂ ∧ ·` is zero.** -/
theorem eq_zero_of_forall_topDensity_oneWedge {m : ℕ} (γ : RealForm (m + 1) (2 * m))
    (h : ∀ ℓ₁ ℓ₂ : ComplexModel (m + 1) →L[ℝ] ℝ, topDensity (n := m + 1) (oneWedge ℓ₁ (oneWedge ℓ₂
      γ)) = 0) :
    γ = 0 := by
  by_contra hγ
  obtain ⟨v, hv⟩ : ∃ v, γ v ≠ 0 := by
    by_contra hall
    exact hγ (ContinuousAlternatingMap.ext fun w => by
      by_contra hne
      exact hall ⟨w, hne⟩)
  have hli : LinearIndependent ℝ v := by
    by_contra hdep
    exact hv (γ.toAlternatingMap.map_linearDependent v hdep)
  have hfin : Module.finrank ℝ (ComplexModel (m + 1)) = 2 * m + 2 := by
    rw [Module.finrank_eq_card_basis (topBasis (m + 1)), Fintype.card_fin]
    ring
  obtain ⟨y, hy⟩ := exists_linearIndependent_cons_of_lt_finrank hli (by omega)
  obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank hy (by omega)
  have hcard : Fintype.card (Fin (2 * m + 1 + 1)) = Module.finrank ℝ (ComplexModel (m + 1)) := by
    rw [Fintype.card_fin, hfin]
  set b := basisOfLinearIndependentOfCardEqFinrank hx hcard with hb
  have hbapp : ∀ i, b i = (Fin.cons x (Fin.cons y v) : Fin (2 * m + 1 + 1) → ComplexModel (m + 1))
    i :=
    fun i => by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]
  set ℓ₁ : ComplexModel (m + 1) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 0)
  set ℓ₂ : ComplexModel (m + 1) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 1)
  have hcoord : ∀ i j, b.coord i (b j) = if j = i then 1 else 0 := fun i j => by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hx0 : x = b 0 := by rw [hbapp]; rfl
  have hy1 : y = b 1 := by rw [hbapp]; rfl
  have hvj : ∀ j, v j = b j.succ.succ := fun j => by rw [hbapp]; rfl
  have key : oneWedge ℓ₁ (oneWedge ℓ₂ γ) (Fin.cons x (Fin.cons y v)) = γ v := by
    refine oneWedge_oneWedge_apply_cons_cons ℓ₁ ℓ₂ γ x y v ?_ ?_ ?_ ?_ ?_
    · simp only [ℓ₁, LinearMap.coe_toContinuousLinearMap', hx0, hcoord, ite_eq_left]
    · simp only [ℓ₁, LinearMap.coe_toContinuousLinearMap', hy1, hcoord]
      exact ite_eq_right one_ne_zero
    · intro j
      simp only [ℓ₁, LinearMap.coe_toContinuousLinearMap', hvj, hcoord]
      exact ite_eq_right (Fin.succ_ne_zero _)
    · simp only [ℓ₂, LinearMap.coe_toContinuousLinearMap', hy1, hcoord, ite_eq_left]
    · intro j
      simp only [ℓ₂, LinearMap.coe_toContinuousLinearMap', hvj, hcoord]
      refine ite_eq_right fun hj => ?_
      have := congrArg Fin.val hj
      simp at this
  -- the top form `ℓ₁ ∧ ℓ₂ ∧ γ` vanishes, as its density does
  set η : RealForm (m + 1) (2 * (m + 1)) := oneWedge ℓ₁ (oneWedge ℓ₂ γ) with hη
  have hη0 : η.toAlternatingMap = 0 := by
    rw [AlternatingMap.eq_smul_basis_det (topBasis (m + 1)) η.toAlternatingMap]
    have h0 : η.toAlternatingMap (topBasis (m + 1)) = 0 := h ℓ₁ ℓ₂
    rw [h0, zero_smul]
  apply hv
  rw [← key]
  exact congrArg (fun f : (ComplexModel (m + 1)) [⋀^Fin (2 * (m + 1))]→ₗ[ℝ] ℝ => f (Fin.cons x
    (Fin.cons y v))) hη0

end Covectors

/-! ### The wedge pairing `Λ_m × Λ² → ℝ` and duality -/

section Pairing

variable {m : ℕ}

/-- `⟨γ ∧ (ℓ₁ ∧ ℓ₂)⟩ = ⟨ℓ₁ ∧ ℓ₂ ∧ γ⟩` for `γ ∈ Λ_m` (two-forms commute with `Λ_m`;
    associativity). -/
theorem topDensity_coordinateWedge_oneForms {γ : RealForm (m + 1) (2 * m)} (hγ : γ ∈ formSpan (m +
    1) m)
    (ℓ₁ ℓ₂ : ComplexModel (m + 1) →L[ℝ] ℝ) :
    topDensity (n := m + 1)
        (coordinateWedge γ (wedgeTo (rfl : 1 + 1 = 2) (oneForm (m + 1) ℓ₁) (oneForm (m + 1) ℓ₂))) =
      topDensity (n := m + 1) (oneWedge ℓ₁ (oneWedge ℓ₂ γ)) := by
  have h1 := wedgeTo_comm_of_mem_formSpan hγ
    (wedgeTo (rfl : 1 + 1 = 2) (oneForm (m + 1) ℓ₁) (oneForm (m + 1) ℓ₂)) (rfl : 2 * m + 2 = 2 * m
      + 2)
    (by ring : 2 + 2 * m = 2 * m + 2)
  have h2 := wedgeTo_assoc (rfl : 1 + 1 = 2) (by ring : 2 + 2 * m = 2 * m + 2) (by ring : 1 + 2 *
    m = 2 * m + 1)
    (by ring : 1 + (2 * m + 1) = 2 * m + 2) (oneForm (m + 1) ℓ₁) (oneForm (m + 1) ℓ₂) γ
  have h3 := wedgeTo_oneForm_eq_oneWedge (by ring : 1 + 2 * m = 2 * m + 1) ℓ₂ γ
  have h4 := wedgeTo_oneForm_eq_oneWedge (by ring : 1 + (2 * m + 1) = 2 * m + 1 + 1)
    ℓ₁ (oneWedge ℓ₂ γ)
  rw [h3] at h2
  have e : (coordinateWedge γ (wedgeTo (rfl : 1 + 1 = 2) (oneForm (m + 1) ℓ₁) (oneForm (m + 1)
    ℓ₂)) :
      RealForm (m + 1) (2 * m + 2)) = oneWedge ℓ₁ (oneWedge ℓ₂ γ) :=
    h1.trans (h2.trans h4)
  exact congrArg (topDensity (n := m + 1)) e

variable (m) in
/-- **The wedge pairing** `γ ↦ (α ↦ ⟨γ ∧ α⟩)` on `Λ_m`, `n = m + 1`. -/
def pairing : formSpan (m + 1) m →ₗ[ℝ] Module.Dual ℝ (RealForm (m + 1) 2) :=
  ((wedgeToBilin (m + 1) (rfl : 2 * m + 2 = 2 * m + 2)).compr₂ (topDensityLM (m + 1))).domRestrict
    (formSpan (m + 1) m)

theorem pairing_apply (γ : formSpan (m + 1) m) (α : RealForm (m + 1) 2) :
    pairing m γ α = topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α) :=
  rfl

/-- **The wedge pairing is nondegenerate on the `Λ_m` side.** -/
theorem pairing_injective : Function.Injective (pairing m) := by
  refine (injective_iff_map_eq_zero (pairing m)).mpr fun γ hγ => ?_
  have h0 : (γ : RealForm (m + 1) (2 * m)) = 0 := by
    refine eq_zero_of_forall_topDensity_oneWedge _ fun ℓ₁ ℓ₂ => ?_
    rw [← topDensity_coordinateWedge_oneForms γ.2, ← pairing_apply, hγ]
    rfl
  exact Subtype.ext h0

/-- **Duality**: every linear functional on `Λ_m` is `γ ↦ ⟨γ ∧ α⟩` for a real two-form `α`. -/
theorem exists_eq_topDensity (L : formSpan (m + 1) m →ₗ[ℝ] ℝ) :
    ∃ α : RealForm (m + 1) 2, ∀ γ : formSpan (m + 1) m,
      L γ = topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α) := by
  have := ProductTestForms.realForm_finiteDimensional (n := m + 1) 2
  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective (pairing_injective (m := m)) L
  obtain ⟨α, rfl⟩ := (Module.evalEquiv ℝ (RealForm (m + 1) 2)).surjective φ
  refine ⟨α, fun γ => ?_⟩
  rw [← hφ]
  rfl

end Pairing

/-! ### The `(1,1)`-part -/

section OneOne

/-- `det_ℝ J = 1` for the complex structure `J = i` of `ℂⁿ`. -/
theorem det_complexJ (n : ℕ) :
    LinearMap.det ((complexJ n : ComplexModel n →L[ℝ] ComplexModel n) : ComplexModel n →ₗ[ℝ]
      ComplexModel n) = 1 := by
  have h : ((complexJ n : ComplexModel n →L[ℝ] ComplexModel n) : ComplexModel n →ₗ[ℝ]
    ComplexModel n) =
      (Complex.I • LinearMap.id : ComplexModel n →ₗ[ℂ] ComplexModel n).restrictScalars ℝ := by
    ext v
    rfl
  rw [h, LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Algebra.norm_complex_apply,
    map_pow, Complex.normSq_I, one_pow]

/-- Top densities are invariant under `J`. -/
theorem topDensity_compJ {n : ℕ} (η : RealForm n (2 * n)) :
    topDensity (η.compContinuousLinearMap (complexJ n)) = topDensity η := by
  rw [topDensity_compContinuousLinearMap, det_complexJ, one_mul]

variable {m : ℕ}

/-- `⟨γ ∧ Π₁₁ α⟩ = ⟨γ ∧ α⟩` for `γ ∈ Λ_m`. -/
theorem topDensity_coordinateWedge_pi11 {γ : RealForm (m + 1) (2 * m)} (hγ : γ ∈ formSpan (m + 1)
    m)
    (α : RealForm (m + 1) 2) :
    topDensity (n := m + 1) (coordinateWedge γ (pi11 α)) = topDensity (n := m + 1)
      (coordinateWedge γ α) := by
  have hJ : γ.compContinuousLinearMap (complexJ (m + 1)) = γ := formSpan_le_jInvariant m hγ
  have e : (coordinateWedge γ α : RealForm (m + 1) (2 * m + 2)).compContinuousLinearMap (complexJ
    (m + 1)) =
      coordinateWedge γ (α.compContinuousLinearMap (complexJ (m + 1))) := by
    rw [coordinateWedge_compContinuousLinearMap, hJ]
  have e2 := topDensity_compJ (n := m + 1) (coordinateWedge γ α)
  have hJα : topDensity (n := m + 1) (coordinateWedge γ (α.compContinuousLinearMap (complexJ (m +
    1)))) =
      topDensity (n := m + 1) (coordinateWedge γ α) :=
    (congrArg (topDensity (n := m + 1)) e.symm).trans e2
  have hlin : coordinateWedge γ (pi11 α) =
      (1 / 2 : ℝ) • (coordinateWedge γ α + coordinateWedge γ (α.compContinuousLinearMap (complexJ
        (m + 1)))) := by
    rw [pi11, coordinateWedge_smul_right, coordinateWedge_add_right]
  have hlin' : topDensity (n := m + 1) (coordinateWedge γ (pi11 α)) =
      (1 / 2 : ℝ) * (topDensity (n := m + 1) (coordinateWedge γ α) +
        topDensity (n := m + 1) (coordinateWedge γ (α.compContinuousLinearMap (complexJ (m +
          1))))) :=
    congrArg (topDensity (n := m + 1)) hlin
  rw [hlin', hJα]
  ring

/-- **Every linear functional on `Λ_m` is `γ ↦ ⟨γ ∧ α⟩` for a real `(1,1)`-form `α`.** -/
theorem exists_isOneOne_eq_topDensity (L : formSpan (m + 1) m →ₗ[ℝ] ℝ) :
    ∃ α : RealForm (m + 1) 2, IsOneOne α ∧ ∀ γ : formSpan (m + 1) m,
      L γ = topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α) := by
  obtain ⟨α, hα⟩ := exists_eq_topDensity L
  exact ⟨pi11 α, isOneOne_pi11 α, fun γ => by rw [hα γ, topDensity_coordinateWedge_pi11 γ.2]⟩

/-- `adj B = det B • B⁻¹` for an invertible `B`. -/
theorem adjugate_eq_det_smul_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ} (hB :
    IsUnit B.det) :
    adjugate B = B.det • B⁻¹ := by
  rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hB, one_smul]

/-- **Positivity**: if the functional is nonnegative on the strongly positive cone,
    the coefficient matrix of its
`(1,1)`-form is positive semidefinite. -/
theorem posSemidef_of_nonneg {L : formSpan (m + 1) m →ₗ[ℝ] ℝ} (hL : ∀ γ ∈ posCone (m + 1) m,
    0 ≤ L γ)
    {α : RealForm (m + 1) 2} (hα : IsOneOne α)
    (hrep : ∀ γ : formSpan (m + 1) m,
      L γ = topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α)) :
    (normalizedHermitianMatrix α).PosSemidef := by
  set A := normalizedHermitianMatrix α with hAdef
  have hherm : A.IsHermitian := normalizedHermitianMatrix_isHermitian α hα
  -- `Re tr (A C) ≥ 0` for every positive definite `C`
  have h1 : ∀ C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, C.PosDef → 0 ≤ (A * C).trace.re := by
    intro C hC
    obtain ⟨β, hβ, hHβ⟩ := exists_isSemipositiveOneOne_normalizedHermitianMatrix_eq
      hC.inv.posSemidef
    have hsp : formPower β m ∈ spCone m := formPower_mem_spCone hβ m
    have hpos := hL ⟨formPower β m, mem_formSpan_of_mem_spCone hsp⟩ hsp
    rw [hrep] at hpos
    change 0 ≤ topDensity (n := m + 1) (coordinateWedge (formPower β m) α) at hpos
    rw [topDensity_wedge_formPower α β hα hβ.1, hHβ] at hpos
    have hdpos : 0 < C⁻¹.det := hC.inv.det_pos
    have hunit : IsUnit C⁻¹.det := isUnit_iff_ne_zero.mpr hdpos.ne'
    have hCunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hC.det_pos.ne'
    rw [adjugate_eq_det_smul_inv hunit, Matrix.nonsing_inv_nonsing_inv C hCunit, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, Complex.mul_re, ← (Complex.pos_iff.mp hdpos).2, zero_mul,
        sub_zero] at hpos
    have hre : 0 < C⁻¹.det.re := (Complex.pos_iff.mp hdpos).1
    by_contra hneg
    have hlt : (m.factorial : ℝ) * (C⁻¹.det.re * (A * C).trace.re) / Real.pi ^ (m + 1) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (mul_neg_of_pos_of_neg hre
        (not_le.mp hneg)))
        (by positivity)
    linarith
  -- positive semidefiniteness, through `C = v v* + t` and `t → 0`
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hherm, fun v => ?_⟩
  have him : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := hherm.im_star_dotProduct_mulVec_self v
  have ht : ∀ t : ℝ, 0 < t → 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re + t * A.trace.re := by
    intro t ht
    have h := h1 (vecMulVec v (star v) + (t : ℂ) • 1)
      (posDef_add_smul_one (posSemidef_vecMulVec_self_star v) ht)
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
      Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul,
        dotProduct_comm] at h
    exact h
  have hlim : Tendsto (fun t : ℝ => (star v ⬝ᵥ (A *ᵥ v)).re + t * A.trace.re) (𝓝[>] 0)
      (𝓝 ((star v ⬝ᵥ (A *ᵥ v)).re)) := by
    have hc : Continuous fun t : ℝ => (star v ⬝ᵥ (A *ᵥ v)).re + t * A.trace.re := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hre : 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht' => ht t ht')
  exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

/-- **`det^{1/n}` as an infimum over `β`** for a real `(1,1)`-form `α` with `H_α ≥ 0` (`n = m +
    1`): the infimum of
`⟨β^m ∧ α⟩` over the semipositive `β` with `H_β` positive definite of determinant `1` is
    `(n!/πⁿ) det(H_α)^{1/n}`. -/
theorem isGLB_topDensity_wedge_formPower_of_posSemidef {α : RealForm (m + 1) 2} (hα : IsOneOne α)
    (hA : (normalizedHermitianMatrix α).PosSemidef) :
    IsGLB {s : ℝ | ∃ β : RealForm (m + 1) 2, IsSemipositiveOneOne β ∧ (normalizedHermitianMatrix
      β).PosDef ∧
        (normalizedHermitianMatrix β).det = 1 ∧ s = topDensity (coordinateWedge (formPower β m) α)}
      (((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) *
        (normalizedHermitianMatrix α).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
  set A := normalizedHermitianMatrix α with hAdef
  set c : ℝ := ((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) with hcdef
  have hc : 0 < c := by positivity
  have hGLB := isGLB_re_trace_div hA
  rw [Fintype.card_fin] at hGLB
  have hval : ∀ β : RealForm (m + 1) 2, IsSemipositiveOneOne β → (normalizedHermitianMatrix
    β).PosDef →
      (normalizedHermitianMatrix β).det = 1 →
      topDensity (coordinateWedge (formPower β m) α) =
        c * (((normalizedHermitianMatrix β)⁻¹ * A).trace.re / ((m + 1 : ℕ) : ℝ)) := by
    intro β hβ hpd hdet
    have hadj : adjugate (normalizedHermitianMatrix β) = (normalizedHermitianMatrix β)⁻¹ := by
      rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    rw [topDensity_wedge_formPower α β hα hβ.1, hadj, Matrix.trace_mul_comm, hcdef,
      Nat.factorial_succ]
    push_cast
    field_simp
    rfl
  refine ⟨?_, fun b hb => ?_⟩
  · rintro s ⟨β, hβ, hpd, hdet, rfl⟩
    rw [hval β hβ hpd hdet]
    refine mul_le_mul_of_nonneg_left (hGLB.1 ⟨_, hpd.inv, ?_, rfl⟩) hc.le
    rw [Matrix.det_nonsing_inv, hdet, Ring.inverse_one]
  · have hlow : b / c ∈ lowerBounds {s : ℝ | ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
    B.PosDef ∧ B.det = 1 ∧
        s = (B * A).trace.re / ((m + 1 : ℕ) : ℝ)} := by
      rintro s ⟨B, hB, hdetB, rfl⟩
      obtain ⟨β, hβ, hHβ⟩ := exists_isSemipositiveOneOne_normalizedHermitianMatrix_eq
        hB.inv.posSemidef
      have hunit : IsUnit B.det := by rw [hdetB]; exact isUnit_one
      have hpd : (normalizedHermitianMatrix β).PosDef := by rw [hHβ]; exact hB.inv
      have hdet : (normalizedHermitianMatrix β).det = 1 := by
        rw [hHβ, Matrix.det_nonsing_inv, hdetB, Ring.inverse_one]
      have h := hb ⟨β, hβ, hpd, hdet, rfl⟩
      rw [hval β hβ hpd hdet, hHβ, Matrix.nonsing_inv_nonsing_inv B hunit] at h
      rw [div_le_iff₀ hc, mul_comm]
      exact h
    have := hGLB.2 hlow
    rw [div_le_iff₀ hc, mul_comm] at this
    exact this

end OneOne

/-! ### The density matrix of the absolutely continuous part of a positive `(1,1)`-current -/

section Currents

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

variable (m) in
/-- The constant forms `β^m` for the semipositive `(1,1)`-forms `β` with `H_β` positive definite
    of determinant `1`
(as elements of `Λ_m`). -/
def detCone : Set (formSpan (m + 1) m) :=
  {c | ∃ β : RealForm (m + 1) 2, IsSemipositiveOneOne β ∧ (normalizedHermitianMatrix β).PosDef ∧
    (normalizedHermitianMatrix β).det = 1 ∧ (c : RealForm (m + 1) (2 * m)) = formPower β m}

theorem detCone_subset_posCone : detCone m ⊆ posCone (m + 1) m := by
  rintro c ⟨β, hβ, -, -, hc⟩
  change (c : RealForm (m + 1) (2 * m)) ∈ spCone m
  rw [hc]
  exact formPower_mem_spCone hβ m

/-- **The density of `T_ac` is a `(1,1)`-form at every point**: `acWeight(x) L_x = ⟨· ∧ α_x⟩` on
    `Λ_m`. -/
theorem exists_isOneOne_acDensity_eq {T : LocalProductCurrent (m + 1) U m} (hT : IsPositive T)
    (x : ComplexModel (m + 1)) :
    ∃ α : RealForm (m + 1) 2, IsOneOne α ∧ ∀ γ : formSpan (m + 1) m,
      acWeight hT x * densityForm hT x γ =
        topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α) := by
  obtain ⟨α, hα, hrep⟩ := exists_isOneOne_eq_topDensity (acWeight hT x • densityForm hT x)
  exact ⟨α, hα, fun γ => by rw [← hrep γ]; rfl⟩

/-- **The infimum of `ana:ac-density-liminf` over `detCone` is `det^{1/n}` of the density
    matrix**: for almost every
`x`, every `(1,1)`-form `α` representing `acWeight(x) L_x` has `H_α ≥ 0` and
`D_{detCone}(T)(x) = (n!/πⁿ) det(H_α)^{1/n}`. -/
theorem ae_acInf_detCone_eq {T : LocalProductCurrent (m + 1) U m} (hT : IsPositive T) :
    ∀ᵐ x, ∀ α : RealForm (m + 1) 2, IsOneOne α →
      (∀ γ : formSpan (m + 1) m, acWeight hT x * densityForm hT x γ =
        topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α)) →
      (normalizedHermitianMatrix α).PosSemidef ∧
        acInf hT (detCone m) x = ENNReal.ofReal (((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) *
          (normalizedHermitianMatrix α).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
  filter_upwards [ae_volume_acDensity_nonneg hT] with x hx α hα hrep
  have hpsd : (normalizedHermitianMatrix α).PosSemidef :=
    posSemidef_of_nonneg (L := acWeight hT x • densityForm hT x) (fun γ hγ => hx γ hγ) hα hrep
  refine ⟨hpsd, ?_⟩
  have hglb := isGLB_topDensity_wedge_formPower_of_posSemidef hα hpsd
  set S := {s : ℝ | ∃ β : RealForm (m + 1) 2, IsSemipositiveOneOne β ∧ (normalizedHermitianMatrix
    β).PosDef ∧
    (normalizedHermitianMatrix β).det = 1 ∧ s = topDensity (coordinateWedge (formPower β m)
      α)} with hSdef
  set g := ((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) *
    (normalizedHermitianMatrix α).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹) with hgdef
  -- the values on `detCone` are the elements of `S`
  have hmemS : ∀ c ∈ detCone m, acWeight hT x * densityForm hT x c ∈ S := by
    rintro c ⟨β, hβ, hpd, hdet, hc⟩
    refine ⟨β, hβ, hpd, hdet, ?_⟩
    rw [hrep c, hc]
  have hSdc : ∀ s ∈ S, ∃ c ∈ detCone m, acWeight hT x * densityForm hT x c = s := by
    rintro s ⟨β, hβ, hpd, hdet, rfl⟩
    have hsp : formPower β m ∈ spCone m := formPower_mem_spCone hβ m
    refine ⟨⟨formPower β m, mem_formSpan_of_mem_spCone hsp⟩, ⟨β, hβ, hpd, hdet, rfl⟩, ?_⟩
    rw [hrep]
  obtain ⟨β₀, hβ₀, hH₀⟩ :=
    exists_isSemipositiveOneOne_normalizedHermitianMatrix_eq (Matrix.PosDef.one (n := Fin (m + 1))
      (R := ℂ)).posSemidef
  have hSne : S.Nonempty := ⟨_, β₀, hβ₀, by rw [hH₀]; exact Matrix.PosDef.one, by rw [hH₀,
    Matrix.det_one], rfl⟩
  have hSbdd : BddBelow S := ⟨g, hglb.1⟩
  have hgS : g = sInf S := (hglb.csInf_eq hSne).symm
  have hof : ENNReal.ofReal g = ⨅ s ∈ S, ENNReal.ofReal s := by
    rw [hgS, Monotone.map_csInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
      (fun a b hab => ENNReal.ofReal_le_ofReal hab) hSne hSbdd, sInf_image]
  rw [acInf, hof]
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun s hs => ?_
    obtain ⟨c, hc, hcs⟩ := hSdc s hs
    rw [← hcs]
    exact iInf₂_le c hc
  · exact le_iInf₂ fun c hc => iInf₂_le _ (hmemS c hc)

/-- **Boucksom's semicontinuity of `det(T_ac)^{1/n}`** (Lemma 3.5 of `bou02-volume`,
    liminf form): if positive currents
`T_k → T` of bidimension `(m, m)` on `U ⊆ ℂ^{m+1}` weakly, then for almost every `x ∈ U` and all
    `(1,1)`-forms `α_k`, `α`
representing the densities `acWeight(x) L_x` of `T_k`, `T` at `x`,
`liminf_k det(H_{α_k})^{1/n} ≤ det(H_α)^{1/n}`. -/
theorem ae_liminf_rpow_det_le {T : ℕ → LocalProductCurrent (m + 1) U m} {T₀ : LocalProductCurrent
    (m + 1) U m}
    (hT : ∀ k, IsPositive (T k)) (hT₀ : IsPositive T₀)
    (hconv : ∀ γ φ, Tendsto (fun k => T k γ φ) atTop (𝓝 (T₀ γ φ))) :
    ∀ᵐ x, x ∈ U → ∀ (α : ℕ → RealForm (m + 1) 2) (α₀ : RealForm (m + 1) 2), (∀ k, IsOneOne (α k))
      → IsOneOne α₀ →
      (∀ k (γ : formSpan (m + 1) m), acWeight (hT k) x * densityForm (hT k) x γ =
        topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) (α k))) →
      (∀ γ : formSpan (m + 1) m, acWeight hT₀ x * densityForm hT₀ x γ =
        topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α₀)) →
      liminf (fun k => ENNReal.ofReal ((normalizedHermitianMatrix (α k)).det.re ^ (((m + 1 : ℕ)
        : ℝ)⁻¹))) atTop ≤
        ENNReal.ofReal ((normalizedHermitianMatrix α₀).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
  have hall := ae_all_iff.mpr fun k => ae_acInf_detCone_eq (hT k)
  filter_upwards [ae_liminf_acInf_le hT hT₀ hconv detCone_subset_posCone, hall,
    ae_acInf_detCone_eq hT₀]
    with x hx hkx h0x hxU α α₀ hα hα₀ hrep hrep₀
  set c : ℝ := ((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) with hcdef
  have hc : 0 < c := by positivity
  have hlim := hx hxU
  rw [(h0x α₀ hα₀ hrep₀).2, ENNReal.ofReal_mul hc.le] at hlim
  have hseq : (fun k => acInf (hT k) (detCone m) x) = fun k => ENNReal.ofReal c *
      ENNReal.ofReal ((normalizedHermitianMatrix (α k)).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
    funext k
    rw [(hkx k (α k) (hα k) (hrep k)).2, ENNReal.ofReal_mul hc.le]
  rw [hseq, ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top] at hlim
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top).mp
    hlim

/-! #### A chosen density form and the density matrix -/

variable {T : LocalProductCurrent (m + 1) U m}

/-- A real `(1,1)`-form representing the density `acWeight(x) L_x` of `T_ac` at `x` (a choice). -/
def acForm (hT : IsPositive T) (x : ComplexModel (m + 1)) : RealForm (m + 1) 2 :=
  Classical.choose (exists_isOneOne_acDensity_eq hT x)

theorem isOneOne_acForm (hT : IsPositive T) (x : ComplexModel (m + 1)) : IsOneOne (acForm hT x) :=
  (Classical.choose_spec (exists_isOneOne_acDensity_eq hT x)).1

theorem acWeight_mul_densityForm_eq (hT : IsPositive T) (x : ComplexModel (m + 1))
    (γ : formSpan (m + 1) m) :
    acWeight hT x * densityForm hT x γ =
      topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) (acForm hT x)) :=
  (Classical.choose_spec (exists_isOneOne_acDensity_eq hT x)).2 γ

/-- **The density matrix of `T_ac`** at `x`: the coefficient matrix of `acForm hT x`. -/
def acMatrix (hT : IsPositive T) (x : ComplexModel (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
    ℂ :=
  normalizedHermitianMatrix (acForm hT x)

/-- The density of `T_ac` on `β^m` through the density matrix: `m! Re tr (A_x adj H_β) / πⁿ`. -/
theorem acWeight_mul_densityForm_formPower (hT : IsPositive T) (x : ComplexModel (m + 1))
    {β : RealForm (m + 1) 2}
    (hβ : IsSemipositiveOneOne β) :
    acWeight hT x * densityForm hT x ⟨formPower β m, mem_formSpan_of_mem_spCone
      (formPower_mem_spCone hβ m)⟩ =
      (m.factorial : ℝ) * (acMatrix hT x * adjugate (normalizedHermitianMatrix β)).trace.re /
        Real.pi ^ (m + 1) := by
  rw [acWeight_mul_densityForm_eq]
  exact topDensity_wedge_formPower (acForm hT x) β (isOneOne_acForm hT x) hβ.1

/-- The density matrix is positive semidefinite almost everywhere. -/
theorem ae_posSemidef_acMatrix (hT : IsPositive T) : ∀ᵐ x, (acMatrix hT x).PosSemidef := by
  filter_upwards [ae_acInf_detCone_eq hT] with x hx
  exact (hx _ (isOneOne_acForm hT x) (acWeight_mul_densityForm_eq hT x)).1

/-- **`D_{detCone}(T) = (n!/πⁿ) det(A_x)^{1/n}`** almost everywhere. -/
theorem ae_acInf_detCone_eq_acMatrix (hT : IsPositive T) :
    ∀ᵐ x, acInf hT (detCone m) x = ENNReal.ofReal (((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) *
      (acMatrix hT x).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
  filter_upwards [ae_acInf_detCone_eq hT] with x hx
  exact (hx _ (isOneOne_acForm hT x) (acWeight_mul_densityForm_eq hT x)).2

/-- **Boucksom's semicontinuity of `det(T_ac)^{1/n}`**, with the density matrices: if positive
    currents `T_k → T`
weakly, then `det(A_x(T))^{1/n} ≥ liminf_k det(A_x(T_k))^{1/n}` for almost every `x ∈ U`. -/
theorem ae_liminf_rpow_det_acMatrix_le {T : ℕ → LocalProductCurrent (m + 1) U m}
    {T₀ : LocalProductCurrent (m + 1) U m} (hT : ∀ k, IsPositive (T k)) (hT₀ : IsPositive T₀)
    (hconv : ∀ γ φ, Tendsto (fun k => T k γ φ) atTop (𝓝 (T₀ γ φ))) :
    ∀ᵐ x, x ∈ U →
      liminf (fun k => ENNReal.ofReal ((acMatrix (hT k) x).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹))) atTop ≤
        ENNReal.ofReal ((acMatrix hT₀ x).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
  filter_upwards [ae_liminf_rpow_det_le hT hT₀ hconv] with x hx hxU
  exact hx hxU (fun k => acForm (hT k) x) (acForm hT₀ x) (fun k => isOneOne_acForm (hT k) x)
    (isOneOne_acForm hT₀ x) (fun k => acWeight_mul_densityForm_eq (hT k) x)
      (acWeight_mul_densityForm_eq hT₀ x)

end Currents

end SGPT.Foundations.Analysis.Pending.LocalCurrentDeterminant

end
