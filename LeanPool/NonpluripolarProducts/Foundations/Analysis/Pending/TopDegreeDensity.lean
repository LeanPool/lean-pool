/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.StronglyPositiveForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoordinateDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientPositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityHermitian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.TopPowerDensityPositivity

/-!
# The density of a top-degree form, and its positivity on strongly positive forms

On the model space `ComplexModel n = ℂⁿ` a real alternating form of top degree `2n` is a
multiple of the determinant of the standard real frame `e₀, i e₀, …, e_{n-1}, i e_{n-1}`
(`FirstPass.MongeAmpere.coordinateRealBasis`, the standard complex orientation); its value on
that frame is its *density* `topDensity A`.  Pulling back along a real-linear map `L`
multiplies the density by `det L` (`topDensity_compContinuousLinearMap`), which is what
makes the ratio of two densities independent of the chart.

The strongly positive cone `StronglyPositiveForms.spCone` is defined by a recursion
(`SP_{q+1} = cone (SP_q ∧ semipositive (1,1)-forms)`).  Unfolding it, every strongly
positive form is a nonnegative combination of products `β₁ ∧ ⋯ ∧ β_q` of semipositive
real `(1,1)`-forms (`spCone_le_prodCone`).  In top degree such a product is the mixed
exterior product of the project (`FirstPass.MongeAmpere.coordinateWedgeFamily`) evaluated on
the standard frame, i.e. `actualMixedTopDensity β` (`topDensity_wedgeProd`), which is the
real part of the mixed coefficient of the normalized Hermitian matrices of the `βⱼ` divided
by `πⁿ` (`actualMixedTopDensity_eq_normalizedMixedTopDensity`).  Those matrices are positive
semidefinite (`normalizedHermitianMatrix_posSemidef`), so the density is nonnegative
(`MixedMongeAmpere.mixedCoefficient_re_nonneg`).  Hence the density of a strongly positive
top-degree form is `≥ 0` (`topDensity_nonneg_of_mem_spCone`): strongly positive forms are
positive (`demailly-cadg:III.1`, the inclusion of the strongly positive cone in the weakly
positive one, in top degree).

## Main results

* `topBasis`, `topDensity`, `topDensity_compContinuousLinearMap` (the Jacobian law).
* `coordinateWedge_unit_apply` — `1 ∧ B = B`.
* `wedgeProd` (products by the recursion of `spCone`), `wedgeProd_apply` (agreement with
  `coordinateWedgeFamily`), `topDensity_wedgeProd`, `formPower_eq_wedgeProd`,
  `topDensity_formPower` (`= actualTopPowerDensity`), `topDensity_formPower_pos`.
* `normalizedHermitianMatrix_posSemidef`, `actualMixedTopDensity_nonneg`.
* `prodCone`, `spCone_le_prodCone`, `topDensity_nonneg_of_mem_spCone`.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.TopDegreeDensity

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms

variable {n : ℕ}

/-! ### The density of a top-degree form -/

variable (n) in
/-- The standard real frame `e₀, i e₀, …`, indexed by `Fin (2 * n)`. -/
def topBasis : Module.Basis (Fin (2 * n)) ℝ (ComplexModel n) :=
  (coordinateRealBasis n).reindex (finCongr (mul_comm n 2))

theorem topBasis_apply (i : Fin (2 * n)) :
    topBasis n i = coordinateRealFrame (Fin.cast (mul_comm 2 n) i) := by
  simp only [topBasis, Module.Basis.reindex_apply, finCongr_symm, finCongr_apply,
    coe_coordinateRealBasis]

/-- The density of a top-degree real form: its value on the standard real frame. -/
def topDensity (A : RealForm n (2 * n)) : ℝ :=
  A (topBasis n)

@[simp] theorem topDensity_zero : topDensity (0 : RealForm n (2 * n)) = 0 := rfl

theorem topDensity_add (A B : RealForm n (2 * n)) :
    topDensity (A + B) = topDensity A + topDensity B := rfl

theorem topDensity_smul (c : ℝ) (A : RealForm n (2 * n)) :
    topDensity (c • A) = c * topDensity A := rfl

theorem topDensity_sub (A B : RealForm n (2 * n)) :
    topDensity (A - B) = topDensity A - topDensity B := rfl

variable (n) in
/-- The density, as a linear functional. -/
def topDensityLM : RealForm n (2 * n) →ₗ[ℝ] ℝ where
  toFun := topDensity
  map_add' := topDensity_add
  map_smul' := topDensity_smul

@[simp] theorem topDensityLM_apply (A : RealForm n (2 * n)) : topDensityLM n A = topDensity A :=
  rfl

/-- The wedge pairing `α ↦ ⟨γ ∧ α⟩` with a fixed form `γ` of degree `2m`, as a linear map on the
    real two-forms. -/
def wedgeDensity {m : ℕ} (γ : RealForm (m + 1) (2 * m)) : RealForm (m + 1) 2 →ₗ[ℝ] ℝ :=
  (topDensityLM (m + 1)).comp (wedgeBilin (m + 1) (2 * m) γ)

theorem wedgeDensity_apply {m : ℕ} (γ : RealForm (m + 1) (2 * m)) (α : RealForm (m + 1) 2) :
    wedgeDensity γ α = topDensity (n := m + 1) (coordinateWedge γ α) :=
  rfl

/-- The density is continuous (top-degree forms form a finite-dimensional space). -/
theorem continuous_topDensity : Continuous (topDensity (n := n)) :=
  (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ (topBasis n)).continuous

/-- **The Jacobian law.**  Pulling back a top-degree form along a real-linear map multiplies
its density by the real determinant. -/
theorem topDensity_compContinuousLinearMap (A : RealForm n (2 * n))
    (L : ComplexModel n →L[ℝ] ComplexModel n) :
    topDensity (A.compContinuousLinearMap L) =
      LinearMap.det (L : ComplexModel n →ₗ[ℝ] ComplexModel n) * topDensity A := by
  set b := topBasis n
  have hΦ := A.toAlternatingMap.eq_smul_basis_det b
  unfold topDensity
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change A.toAlternatingMap (L ∘ b) = _ * A.toAlternatingMap b
  rw [hΦ]
  simp only [_root_.smul_apply, smul_eq_mul, Module.Basis.det_self, mul_one]
  rw [show (⇑L ∘ ⇑b) = ⇑(L : ComplexModel n →ₗ[ℝ] ComplexModel n) ∘ ⇑b from rfl,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  ring

/-! ### The unit of the exterior product -/

/-- `1 ∧ B = B`. -/
theorem coordinateWedge_unit_apply {q : ℕ} (B : RealForm n q) (v : Fin (0 + q) → ComplexModel n) :
    coordinateWedge (coordinateWedgeUnit : RealForm n 0) B v =
      B (v ∘ Fin.cast (zero_add q).symm) := by
  classical
  rw [coordinateWedge_apply, coordinateWedgeSum_apply]
  set e : Fin 0 ⊕ Fin q ≃ Fin q := Equiv.emptySum (Fin 0) (Fin q)
  set w : Fin 0 ⊕ Fin q → ComplexModel n := v ∘ finSumFinEquiv
  have hw : w ∘ Sum.inr = v ∘ Fin.cast (zero_add q).symm := by
    funext i
    simp only [w, Function.comp_apply, finSumFinEquiv_apply_right]
    exact congrArg v (Fin.ext (by simp))
  have hterm : ∀ σ : Equiv.Perm (Fin 0 ⊕ Fin q),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((coordinateWedgeUnit : RealForm n 0)
        (w ∘ σ ∘ Sum.inl) * B (w ∘ σ ∘ Sum.inr)) = B (w ∘ Sum.inr) := by
    intro σ
    set τ : Equiv.Perm (Fin q) := e.permCongr σ
    have hστ : w ∘ σ ∘ Sum.inr = (w ∘ Sum.inr) ∘ τ := by
      funext i
      simp only [Function.comp_apply, τ, Equiv.permCongr_apply]
      congr 1
      rcases h : σ (Sum.inr i) with j | j
      · exact j.elim0
      · simp [e, h]
    have hsign : Equiv.Perm.sign τ = Equiv.Perm.sign σ := Equiv.Perm.sign_permCongr e σ
    have hunit : (coordinateWedgeUnit : RealForm n 0) (w ∘ σ ∘ Sum.inl) = 1 := rfl
    rw [hunit, one_mul, hστ]
    change ((Equiv.Perm.sign σ : ℤ) : ℝ) * B.toAlternatingMap ((w ∘ Sum.inr) ∘ τ) = _
    rw [AlternatingMap.map_perm, hsign, Units.smul_def, zsmul_eq_mul, ← mul_assoc]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
    ← hw]
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add]
  field_simp

/-! ### Products of two-forms -/

/-- The product `β₀ ∧ ⋯ ∧ β_{q-1}`, by the recursion of `spCone` (unit first). -/
def wedgeProd : (q : ℕ) → (Fin q → RealForm n 2) → RealForm n (2 * q)
  | 0, _ => coordinateWedgeUnit
  | q + 1, β => coordinateWedge (wedgeProd q fun i => β i.castSucc) (β (Fin.last q))

@[simp] theorem wedgeProd_zero (β : Fin 0 → RealForm n 2) :
    wedgeProd 0 β = coordinateWedgeUnit := rfl

theorem wedgeProd_succ (q : ℕ) (β : Fin (q + 1) → RealForm n 2) :
    wedgeProd (q + 1) β = coordinateWedge (wedgeProd q fun i => β i.castSucc) (β (Fin.last q)) :=
  rfl

theorem wedgeProd_snoc (q : ℕ) (γ : Fin q → RealForm n 2) (β : RealForm n 2) :
    wedgeProd (q + 1) (Fin.snoc γ β) = coordinateWedge (wedgeProd q γ) β := by
  rw [wedgeProd_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Transport of the left factor of an exterior product along an equality of degrees. -/
theorem coordinateWedge_congr_cast {p p' r : ℕ} (h : p = p') (A : RealForm n p)
    (C : RealForm n p') (hAC : ∀ v, A v = C (v ∘ Fin.cast h.symm)) (B : RealForm n r)
    (v : Fin (p + r) → ComplexModel n) :
    coordinateWedge A B v = coordinateWedge C B (v ∘ Fin.cast (by omega)) := by
  subst h
  have hAC' : A = C := by
    ext v
    rw [hAC v]
    rfl
  subst hAC'
  rfl

/-- **The two recursions agree**: the product by the recursion of `spCone` evaluates as the
project's mixed exterior product `coordinateWedgeFamily`. -/
theorem wedgeProd_apply : ∀ (q : ℕ) (β : Fin q → RealForm n 2) (v : Fin (2 * q) → ComplexModel n),
    wedgeProd q β v = coordinateWedgeFamily q β (v ∘ Fin.cast (mul_comm q 2))
  | 0, β, v => rfl
  | 1, β, v => by
    rw [wedgeProd_succ, coordinateWedgeFamily_one]
    change coordinateWedge (coordinateWedgeUnit : RealForm n 0) (β (Fin.last 0)) v = _
    rw [coordinateWedge_unit_apply]
    rfl
  | q + 2, β, v => by
    rw [wedgeProd_succ, coordinateWedgeFamily_add_two_apply,
      coordinateWedge_congr_cast (mul_comm 2 (q + 1)) _ _
        (fun v => wedgeProd_apply (q + 1) (fun i => β i.castSucc) v)]
    rfl

/-- **The product of two-forms is symmetric in its factors.** -/
theorem wedgeProd_comp_perm (q : ℕ) (β : Fin q → RealForm n 2) (σ : Equiv.Perm (Fin q)) :
    wedgeProd q (fun i => β (σ i)) = wedgeProd q β := by
  ext v
  rw [wedgeProd_apply, wedgeProd_apply, coordinateWedgeFamily_apply_eq_pairingSum,
    coordinateWedgeFamily_apply_eq_pairingSum, coordinatePairingSumFamily_comp_perm]

theorem wedgeProd_snoc_eq_cons (q : ℕ) (β : Fin q → RealForm n 2) (B : RealForm n 2) :
    wedgeProd (q + 1) (Fin.snoc β B) = wedgeProd (q + 1) (Fin.cons B β) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact wedgeProd_comp_perm (q + 1) (Fin.cons B β) (finRotate (q + 1))

/-- In top degree the density of a product is the mixed density of the factors. -/
theorem topDensity_wedgeProd (β : Fin n → RealForm n 2) :
    topDensity (wedgeProd n β) = actualMixedTopDensity β := by
  rw [topDensity, wedgeProd_apply, actualMixedTopDensity]
  congr 1
  funext i
  rw [Function.comp_apply, topBasis_apply]
  rfl

theorem formPower_eq_wedgeProd (ω : RealForm n 2) :
    ∀ q, formPower ω q = wedgeProd q (fun _ => ω)
  | 0 => rfl
  | q + 1 => by
    rw [formPower_succ, wedgeProd_succ, formPower_eq_wedgeProd ω q]

/-- The density of `ωⁿ` is the top-power density of the project. -/
theorem topDensity_formPower (ω : RealForm n 2) :
    topDensity (formPower ω n) = actualTopPowerDensity ω := by
  rw [formPower_eq_wedgeProd, topDensity_wedgeProd, actualMixedTopDensity_const]

/-- A strictly positive real `(1,1)`-form has positive top density. -/
theorem topDensity_formPower_pos {ω : RealForm n 2} (hω : IsOneOne ω)
    (hpos : IsStrictlyPositive ω) : 0 < topDensity (formPower ω n) := by
  rw [topDensity_formPower]
  exact actualTopPowerDensity_pos hω hpos

/-! ### Positivity -/

/-- **The normalized Hermitian matrix of a semipositive real `(1,1)`-form is positive
semidefinite.**  For `x ∈ ℂⁿ` and `y = ∑ xBarⱼ eⱼ`, `x* H x = π · A(y, i y) ≥ 0`. -/
theorem normalizedHermitianMatrix_posSemidef {A : RealForm n 2} (hA : IsSemipositiveOneOne A) :
    (normalizedHermitianMatrix A).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (normalizedHermitianMatrix_isHermitian A hA.1) fun x => ?_
  set y : ComplexModel n := ∑ j, (star (x j)) • coordinateVector j
  have hG : hermitianEntry A y y =
      ∑ j, star (x j) * ∑ k, x k * hermitianEntry A (coordinateVector j) (coordinateVector k) := by
    rw [hermitianEntry_sum_left hA.1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hermitianEntry_sum_right]
    simp only [Complex.star_def, RCLike.conj_conj]
  have hyy : A ![y, y] = 0 :=
    A.map_eq_zero_of_eq ![y, y] (i := 0) (j := 1) (by simp) (by decide)
  have hGreal : hermitianEntry A y y = ((A ![y, Complex.I • y] : ℝ) : ℂ) := by
    simp [hermitianEntry, hyy]
  have hdot : star x ⬝ᵥ (normalizedHermitianMatrix A *ᵥ x) =
      (Real.pi : ℂ) * hermitianEntry A y y := by
    rw [hG, Finset.mul_sum]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, normalizedHermitianMatrix_apply',
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hdot, hGreal, ← Complex.ofReal_mul]
  exact Complex.zero_le_real.mpr (mul_nonneg Real.pi_pos.le (hA.2 y))

/-- The mixed top density of semipositive real `(1,1)`-forms is nonnegative. -/
theorem actualMixedTopDensity_nonneg {A : Fin n → RealForm n 2}
    (hA : ∀ i, IsSemipositiveOneOne (A i)) : 0 ≤ actualMixedTopDensity A := by
  rw [actualMixedTopDensity_eq_normalizedMixedTopDensity A fun i => (hA i).1,
    normalizedMixedTopDensity]
  exact div_nonneg (Pending.MixedMongeAmpere.mixedCoefficient_re_nonneg _
    fun i => normalizedHermitianMatrix_posSemidef (hA i)) (by positivity)

/-- The cone generated by the products of semipositive real `(1,1)`-forms. -/
def prodCone (q : ℕ) : PointedCone ℝ (RealForm n (2 * q)) :=
  PointedCone.hull ℝ
    {P | ∃ β : Fin q → RealForm n 2, (∀ i, IsSemipositiveOneOne (β i)) ∧ P = wedgeProd q β}

theorem wedgeProd_mem_prodCone {q : ℕ} {β : Fin q → RealForm n 2}
    (hβ : ∀ i, IsSemipositiveOneOne (β i)) : wedgeProd q β ∈ prodCone q :=
  PointedCone.subset_hull ⟨β, hβ, rfl⟩

theorem wedge_mem_prodCone {q : ℕ} {P : RealForm n (2 * q)} (hP : P ∈ prodCone q)
    {β : RealForm n 2} (hβ : IsSemipositiveOneOne β) :
    coordinateWedge P β ∈ prodCone (q + 1) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    rw [← wedgeProd_snoc]
    refine wedgeProd_mem_prodCone fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]; exact hβ
    · rw [Fin.snoc_castSucc]; exact hγ j
  | zero =>
    rw [← wedgeBilin_apply, map_zero, LinearMap.zero_apply]
    exact (prodCone (q + 1)).zero_mem
  | add x y _ _ hx hy =>
    rw [coordinateWedge_add_left]
    exact (prodCone (q + 1)).add_mem hx hy
  | smul a x _ hx =>
    change coordinateWedge ((a : ℝ) • x) β ∈ _
    rw [coordinateWedge_smul_left]
    exact Submodule.smul_mem (prodCone (q + 1)) a hx

/-- **Strongly positive forms are nonnegative combinations of products** of semipositive
real `(1,1)`-forms. -/
theorem spCone_le_prodCone : ∀ q : ℕ, spCone (n := n) q ≤ prodCone q
  | 0 => by
    refine Submodule.span_le.mpr ?_
    rintro x rfl
    exact wedgeProd_mem_prodCone (β := Fin.elim0) fun i => i.elim0
  | q + 1 => by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨P, hP, β, hβ, rfl⟩
    exact wedge_mem_prodCone (spCone_le_prodCone q hP) hβ

/-- **Strongly positive top-degree forms have nonnegative density.** -/
theorem topDensity_nonneg_of_mem_spCone {P : RealForm n (2 * n)} (hP : P ∈ spCone n) :
    0 ≤ topDensity P := by
  have hP' := spCone_le_prodCone n hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    rw [topDensity_wedgeProd]
    exact actualMixedTopDensity_nonneg hβ
  | zero => exact le_rfl
  | add x y _ _ hx hy => rw [topDensity_add]; exact add_nonneg hx hy
  | smul a x _ hx =>
    change 0 ≤ topDensity ((a : ℝ) • x)
    rw [topDensity_smul]
    exact mul_nonneg a.2 hx

end SGPT.Foundations.Analysis.Pending.TopDegreeDensity
