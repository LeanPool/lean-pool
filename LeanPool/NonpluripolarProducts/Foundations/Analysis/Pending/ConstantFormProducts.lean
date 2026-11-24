/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Products of constant forms on `ℂⁿ`

Algebra of the exterior product `FirstPass.MongeAmpere.coordinateWedge` of real continuous
alternating forms on `ℂⁿ`, as needed for currents wedged with smooth forms
(`bt:recursive-product`, clause on smooth closed strongly positive forms).

* `castForm`, `wedgeTo` — the exterior product with its degree transported to any equal degree
  (`wedgeTo h A B = (A ∧ B)` read in degree `m`, `h : p + q = m`); all identities below hold for
  arbitrary proofs of the degree equations, so no cast has to be matched by hand.
* `wedgeTo_assoc` — associativity; `wedgeTo_unit_right`, `wedgeTo_unit_left` — the unit.
* `coordinateWedge_comm_two` — two-forms commute; `wedgeTo_comm_of_mem_formSpan` — a two-form
  commutes with every constant `(k,k)`-form of `Λ_k = span (spCone k)`.
* `wedgeTo_mem_spCone` — **the product of strongly positive forms is strongly positive**,
  `spCone p ∧ spCone k ⊆ spCone (p + k)`; `wedgeTo_mem_formSpan` and the bilinear map
  `wedgeSpan : Λ_p × Λ_k → Λ_m` (`p + k = m`).
* `compJ_eq_self_of_mem_formSpan` — the forms of `Λ_k` are invariant under the complex structure.
* `sum_perm_uncurry` — the alternation of an uncurried map is `p!` times
  `alternatizeUncurryFin`; hence `wedgeTo_oneForm_eq_oneWedge` (`ℓ ∧ A` by the alternating sum
  `∑ᵢ (-1)ⁱ ℓ(vᵢ) A(v without vᵢ)`) and **the coordinate formula for the exterior derivative**
  `extDeriv_eq_sum` (`dα(x) = ∑_a e^a ∧ ∂_a α(x)` for mathlib's `extDeriv`).
* `sum_wedgeTo_testForm_eq_zero` — if `∑_a e^a ∧ D_a = 0` for forms `D_a ∈ Λ_k` (the derivatives
  of a closed form of type `(k,k)`), then `∑_a Π₁₁(e^a ∧ ℓ) ∧ D_a = 0` for every real linear form
  `ℓ`: the `(k+1,k+1)`-part of `ℓ ∧ dα` and of `ℓ ∘ i ∧ (dα ∘ i)` vanish.
-/

@[expose] public section

noncomputable section

open Set Equiv Finset
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.ConstantFormProducts

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  CoordinateWedgeAssoc ClosedProductCurrents LocalBedfordTaylorProducts

variable {n : ℕ}

local notation "E" => ComplexModel n

/-! ### Forms of equal degrees -/

section Cast

/-- A real form of degree `a` read in an equal degree `b`. -/
def castForm {a b : ℕ} (h : a = b) : RealForm n a →ₗ[ℝ] RealForm n b where
  toFun A := h ▸ A
  map_add' A B := by subst h; rfl
  map_smul' c A := by subst h; rfl

theorem castForm_apply {a b : ℕ} (h : a = b) (A : RealForm n a) (v : Fin b → E) :
    castForm h A v = A (v ∘ Fin.cast h) := by
  subst h
  rfl

@[simp] theorem castForm_self {a : ℕ} (h : a = a) (A : RealForm n a) : castForm h A = A := rfl

theorem castForm_castForm {a b c : ℕ} (h : a = b) (h' : b = c) (A : RealForm n a) :
    castForm h' (castForm h A) = castForm (h.trans h') A := by
  subst h h'
  rfl

theorem castForm_compContinuousLinearMap {a b : ℕ} (h : a = b) (A : RealForm n a)
    (L : E →L[ℝ] E) :
    (castForm h A).compContinuousLinearMap L = castForm h (A.compContinuousLinearMap L) := by
  subst h
  rfl

end Cast

/-! ### The exterior product in a prescribed degree -/

section WedgeTo

variable {p q r m : ℕ}

/-- The exterior product `A ∧ B` read in the degree `m = p + q`. -/
def wedgeTo (h : p + q = m) (A : RealForm n p) (B : RealForm n q) : RealForm n m :=
  castForm h (coordinateWedge A B)

theorem wedgeTo_apply (h : p + q = m) (A : RealForm n p) (B : RealForm n q) (v : Fin m → E) :
    wedgeTo h A B v = coordinateWedge A B (v ∘ Fin.cast h) :=
  castForm_apply h _ v

@[simp] theorem wedgeTo_rfl (A : RealForm n p) (B : RealForm n q) :
    wedgeTo (rfl : p + q = p + q) A B = coordinateWedge A B := rfl

theorem wedgeTo_add_left (h : p + q = m) (A A' : RealForm n p) (B : RealForm n q) :
    wedgeTo h (A + A') B = wedgeTo h A B + wedgeTo h A' B := by
  rw [wedgeTo, coordinateWedge_add_left, map_add]
  rfl

theorem wedgeTo_add_right (h : p + q = m) (A : RealForm n p) (B B' : RealForm n q) :
    wedgeTo h A (B + B') = wedgeTo h A B + wedgeTo h A B' := by
  rw [wedgeTo, coordinateWedge_add_right, map_add]
  rfl

theorem wedgeTo_smul_left (h : p + q = m) (c : ℝ) (A : RealForm n p) (B : RealForm n q) :
    wedgeTo h (c • A) B = c • wedgeTo h A B := by
  rw [wedgeTo, coordinateWedge_smul_left, map_smul]
  rfl

theorem wedgeTo_smul_right (h : p + q = m) (c : ℝ) (A : RealForm n p) (B : RealForm n q) :
    wedgeTo h A (c • B) = c • wedgeTo h A B := by
  rw [wedgeTo, coordinateWedge_smul_right, map_smul]
  rfl

variable (n) in
/-- The exterior product in degree `m`, as a bilinear map. -/
def wedgeToBilin (h : p + q = m) : RealForm n p →ₗ[ℝ] RealForm n q →ₗ[ℝ] RealForm n m :=
  LinearMap.mk₂ ℝ (wedgeTo h) (wedgeTo_add_left h) (wedgeTo_smul_left h) (wedgeTo_add_right h)
    (wedgeTo_smul_right h)

@[simp] theorem wedgeToBilin_apply (h : p + q = m) (A : RealForm n p) (B : RealForm n q) :
    wedgeToBilin n h A B = wedgeTo h A B := rfl

theorem wedgeTo_zero_left (h : p + q = m) (B : RealForm n q) : wedgeTo h (0 : RealForm n p)
    B = 0 := by
  rw [← wedgeToBilin_apply, map_zero, LinearMap.zero_apply]

theorem wedgeTo_zero_right (h : p + q = m) (A : RealForm n p) : wedgeTo h A (0 : RealForm n q)
    = 0 := by
  rw [← wedgeToBilin_apply, map_zero]

theorem wedgeTo_neg_left (h : p + q = m) (A : RealForm n p) (B : RealForm n q) :
    wedgeTo h (-A) B = -wedgeTo h A B := by
  rw [← wedgeToBilin_apply, map_neg, LinearMap.neg_apply, wedgeToBilin_apply]

theorem wedgeTo_sum_left {ι : Type*} (s : Finset ι) (h : p + q = m) (A : ι → RealForm n p)
    (B : RealForm n q) : wedgeTo h (∑ i ∈ s, A i) B = ∑ i ∈ s, wedgeTo h (A i) B := by
  rw [← wedgeToBilin_apply, map_sum, LinearMap.sum_apply]
  rfl

theorem wedgeTo_sum_right {ι : Type*} (s : Finset ι) (h : p + q = m) (A : RealForm n p)
    (B : ι → RealForm n q) : wedgeTo h A (∑ i ∈ s, B i) = ∑ i ∈ s, wedgeTo h A (B i) := by
  rw [← wedgeToBilin_apply, map_sum]
  rfl

theorem wedgeTo_castForm_left {p' : ℕ} (h₀ : p = p') (h : p' + q = m) (h' : p + q = m)
    (A : RealForm n p) (B : RealForm n q) : wedgeTo h (castForm h₀ A) B = wedgeTo h' A B := by
  subst h₀ h
  rfl

theorem wedgeTo_castForm_right {q' : ℕ} (h₀ : q = q') (h : p + q' = m) (h' : p + q = m)
    (A : RealForm n p) (B : RealForm n q) : wedgeTo h A (castForm h₀ B) = wedgeTo h' A B := by
  subst h₀ h
  rfl

theorem castForm_wedgeTo {m' : ℕ} (h : p + q = m) (h' : m = m') (h'' : p + q = m')
    (A : RealForm n p) (B : RealForm n q) : castForm h' (wedgeTo h A B) = wedgeTo h'' A B := by
  subst h h'
  rfl

/-- The degree equation of `wedgeTo` is irrelevant. -/
theorem wedgeTo_congr (h h' : p + q = m) (A : RealForm n p) (B : RealForm n q) :
    wedgeTo h A B = wedgeTo h' A B := rfl

/-- **Associativity of the exterior product**, in prescribed degrees. -/
theorem wedgeTo_assoc {s t : ℕ} (h₁ : p + q = s) (h₂ : s + r = m) (h₃ : q + r = t)
    (h₄ : p + t = m) (A : RealForm n p) (B : RealForm n q) (C : RealForm n r) :
    wedgeTo h₂ (wedgeTo h₁ A B) C = wedgeTo h₄ A (wedgeTo h₃ B C) := by
  subst h₁ h₃ h₂
  ext v
  rw [wedgeTo_apply, wedgeTo_apply]
  simp only [wedgeTo_rfl]
  rw [coordinateWedge_assoc_apply]
  congr 1

/-- Pullback along a real-linear map commutes with the exterior product. -/
theorem wedgeTo_compContinuousLinearMap (h : p + q = m) (A : RealForm n p) (B : RealForm n q)
    (L : E →L[ℝ] E) :
    (wedgeTo h A B).compContinuousLinearMap L =
      wedgeTo h (A.compContinuousLinearMap L) (B.compContinuousLinearMap L) := by
  rw [wedgeTo, castForm_compContinuousLinearMap, coordinateWedge_compContinuousLinearMap]
  rfl

end WedgeTo

/-! ### The unit and two-forms -/

section Unit

variable {p q m : ℕ}

theorem form_map_perm {k : ℕ} (A : RealForm n k) (v : Fin k → E) (σ : Perm (Fin k)) :
    A (v ∘ σ) = ((Perm.sign σ : ℤ) : ℝ) * A v := by
  have h := A.toAlternatingMap.map_perm v σ
  rw [Units.smul_def, zsmul_eq_mul] at h
  exact h

/-- `A ∧ 1 = A`. -/
theorem coordinateWedge_unit_right (A : RealForm n p) :
    coordinateWedge A (coordinateWedgeUnit : RealForm n 0) = A := by
  ext v
  rw [coordinateWedge_apply_perm]
  have hterm : ∀ π : Perm (Fin (p + 0)), ((Perm.sign π : ℤ) : ℝ) *
      (A (v ∘ π ∘ finSumFinEquiv ∘ Sum.inl) *
        (coordinateWedgeUnit : RealForm n 0) (v ∘ π ∘ finSumFinEquiv ∘ Sum.inr)) = A v := by
    intro π
    have h1 : v ∘ π ∘ finSumFinEquiv ∘ Sum.inl = v ∘ π := by
      funext i
      simp only [Function.comp_apply, finSumFinEquiv_apply_left]
      rfl
    rw [h1, form_map_perm]
    have hu : (coordinateWedgeUnit : RealForm n 0) (v ∘ π ∘ finSumFinEquiv ∘ Sum.inr) = 1 := rfl
    rw [hu, mul_one, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, Int.cast_one, one_mul]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    Nat.factorial_zero, mul_one, ← mul_assoc]
  change ((p.factorial : ℝ))⁻¹ * (p.factorial : ℝ) * A v = A v
  rw [inv_mul_cancel₀ (by positivity), one_mul]

/-- `1 ∧ B = B`, read in degree `q`. -/
theorem coordinateWedge_unit_left (B : RealForm n q) :
    coordinateWedge (coordinateWedgeUnit : RealForm n 0) B = castForm (zero_add q).symm B := by
  ext v
  rw [TopDegreeDensity.coordinateWedge_unit_apply, castForm_apply]

theorem wedgeTo_unit_right (h : p + 0 = m) (h' : p = m) (A : RealForm n p) :
    wedgeTo h A (coordinateWedgeUnit : RealForm n 0) = castForm h' A := by
  rw [wedgeTo, coordinateWedge_unit_right]

theorem wedgeTo_unit_left (h : 0 + q = m) (h' : q = m) (B : RealForm n q) :
    wedgeTo h (coordinateWedgeUnit : RealForm n 0) B = castForm h' B := by
  rw [wedgeTo, coordinateWedge_unit_left, castForm_castForm]

/-- **Two-forms commute**: `A ∧ B = B ∧ A`. -/
theorem coordinateWedge_comm_two (A B : RealForm n 2) : coordinateWedge A B = coordinateWedge B A
    := by
  ext v
  rw [coordinateWedge_apply_perm, coordinateWedge_apply_perm]
  congr 1
  let c : Perm (Fin (2 + 2)) := swap 0 2 * swap 1 3
  refine Fintype.sum_equiv (Equiv.mulRight c) _ _ fun π => ?_
  have hc : Perm.sign c = 1 := by decide
  have h1 : ∀ i : Fin 2, c (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inr i) := by
    decide
  have h2 : ∀ i : Fin 2, c (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inl i) := by
    decide
  have e1 : v ∘ ⇑(π * c) ∘ finSumFinEquiv ∘ Sum.inl = v ∘ π ∘ finSumFinEquiv ∘ Sum.inr := by
    funext i
    simp only [Function.comp_apply, Perm.coe_mul, h1]
  have e2 : v ∘ ⇑(π * c) ∘ finSumFinEquiv ∘ Sum.inr = v ∘ π ∘ finSumFinEquiv ∘ Sum.inl := by
    funext i
    simp only [Function.comp_apply, Perm.coe_mul, h2]
  simp only [Equiv.coe_mulRight, Perm.sign_mul, hc, mul_one, e1, e2]
  ring

theorem wedgeTo_comm_two (h h' : 2 + 2 = m) (A B : RealForm n 2) :
    wedgeTo h A B = wedgeTo h' B A := by
  rw [wedgeTo, wedgeTo, coordinateWedge_comm_two]

end Unit

/-! ### Two-forms commute with constant `(k,k)`-forms -/

section Commute

/-- A two-form commutes with every strongly positive form. -/
theorem wedgeTo_comm_of_mem_spCone (T : RealForm n 2) :
    ∀ (k : ℕ) (P : RealForm n (2 * k)), P ∈ spCone k → ∀ (m : ℕ) (h₁ : 2 * k + 2 = m)
      (h₂ : 2 + 2 * k = m), wedgeTo h₁ P T = wedgeTo h₂ T P := by
  intro k
  induction k with
  | zero =>
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      intro m h₁ h₂
      rw [wedgeTo_unit_left h₁ (by omega), wedgeTo_unit_right h₂ (by omega)]
    | zero =>
      intro m h₁ h₂
      rw [wedgeTo_zero_left, wedgeTo_zero_right]
    | add x y _ _ hx hy =>
      intro m h₁ h₂
      rw [wedgeTo_add_left, wedgeTo_add_right, hx m h₁ h₂, hy m h₁ h₂]
    | smul a x _ hx =>
      intro m h₁ h₂
      rw [show a • x = (a : ℝ) • x from rfl, wedgeTo_smul_left, wedgeTo_smul_right, hx m h₁ h₂]
  | succ k ih =>
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Q, hQ, β, -, rfl⟩ := hx
      intro m h₁ h₂
      have e0 : (coordinateWedge Q β : RealForm n (2 * (k + 1))) =
          wedgeTo (rfl : 2 * k + 2 = 2 * k + 2) Q β := rfl
      rw [e0, wedgeTo_assoc rfl h₁ (rfl : 2 + 2 = 2 + 2) (by omega), wedgeTo_comm_two rfl rfl β T,
        ← wedgeTo_assoc (rfl : 2 * k + 2 = 2 * k + 2) (by omega) rfl (by omega),
        ih Q hQ (2 * k + 2) rfl (by omega),
        wedgeTo_assoc (by omega) (by omega) (rfl : 2 * k + 2 = 2 * k + 2) h₂]
    | zero =>
      intro m h₁ h₂
      rw [wedgeTo_zero_left, wedgeTo_zero_right]
    | add x y _ _ hx hy =>
      intro m h₁ h₂
      rw [wedgeTo_add_left, wedgeTo_add_right, hx m h₁ h₂, hy m h₁ h₂]
    | smul a x _ hx =>
      intro m h₁ h₂
      rw [show a • x = (a : ℝ) • x from rfl, wedgeTo_smul_left, wedgeTo_smul_right, hx m h₁ h₂]

/-- **A two-form commutes with every constant `(k,k)`-form** of `Λ_k = span (spCone k)`. -/
theorem wedgeTo_comm_of_mem_formSpan {k m : ℕ} {P : RealForm n (2 * k)} (hP : P ∈ formSpan n k)
    (T : RealForm n 2) (h₁ : 2 * k + 2 = m) (h₂ : 2 + 2 * k = m) :
    wedgeTo h₁ P T = wedgeTo h₂ T P := by
  induction hP using Submodule.span_induction with
  | mem x hx => exact wedgeTo_comm_of_mem_spCone T k x hx m h₁ h₂
  | zero => rw [wedgeTo_zero_left, wedgeTo_zero_right]
  | add x y _ _ hx hy => rw [wedgeTo_add_left, wedgeTo_add_right, hx, hy]
  | smul a x _ hx => rw [wedgeTo_smul_left, wedgeTo_smul_right, hx]

/-- Moving a two-form past a constant form: `(P ∧ T) ∧ Q = (P ∧ Q) ∧ T` for `Q ∈ Λ_k`. -/
theorem wedgeTo_wedgeTo_comm {p k m s t : ℕ} (P : RealForm n p) (T : RealForm n 2)
    {Q : RealForm n (2 * k)} (hQ : Q ∈ formSpan n k) (h₁ : p + 2 = s) (h₂ : s + 2 * k = m)
    (h₃ : p + 2 * k = t) (h₄ : t + 2 = m) :
    wedgeTo h₂ (wedgeTo h₁ P T) Q = wedgeTo h₄ (wedgeTo h₃ P Q) T := by
  rw [wedgeTo_assoc h₁ h₂ (rfl : 2 + 2 * k = 2 + 2 * k) (by omega),
    ← wedgeTo_comm_of_mem_formSpan hQ T (by omega : 2 * k + 2 = 2 + 2 * k) rfl,
    wedgeTo_assoc h₃ h₄ (by omega : 2 * k + 2 = 2 + 2 * k) (by omega)]

end Commute

/-! ### Products of strongly positive forms -/

section Products

/-- **The exterior product of strongly positive forms is strongly positive**:
`spCone r ∧ spCone k ⊆ spCone (r + k)`. -/
theorem wedgeTo_mem_spCone : ∀ (k r m : ℕ) {P : RealForm n (2 * r)}, P ∈ spCone r →
    ∀ {Q : RealForm n (2 * k)}, Q ∈ spCone k → ∀ (h : 2 * r + 2 * k = 2 * m),
      wedgeTo h P Q ∈ spCone m := by
  intro k
  induction k with
  | zero =>
    intro r m P hP Q hQ
    induction hQ using Submodule.span_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      intro h
      obtain rfl : m = r := by omega
      rw [wedgeTo_unit_right h rfl]
      exact hP
    | zero =>
      intro h
      rw [wedgeTo_zero_right]
      exact (spCone (n := n) m).zero_mem
    | add x y _ _ hx hy =>
      intro h
      rw [wedgeTo_add_right]
      exact (spCone (n := n) m).add_mem (hx h) (hy h)
    | smul a x _ hx =>
      intro h
      rw [show a • x = (a : ℝ) • x from rfl, wedgeTo_smul_right]
      exact smul_mem_spCone (hx h) a.2
  | succ k ih =>
    intro r m P hP Q hQ
    induction hQ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Q', hQ', β, hβ, rfl⟩ := hx
      intro h
      obtain rfl : m = r + k + 1 := by omega
      have e0 : (coordinateWedge Q' β : RealForm n (2 * (k + 1))) =
          wedgeTo (rfl : 2 * k + 2 = 2 * k + 2) Q' β := rfl
      rw [e0, ← wedgeTo_assoc (by omega : 2 * r + 2 * k = 2 * (r + k)) (by omega) rfl h]
      exact wedge_mem_spCone (ih r (r + k) hP hQ' (by omega)) hβ
    | zero =>
      intro h
      rw [wedgeTo_zero_right]
      exact (spCone (n := n) m).zero_mem
    | add x y _ _ hx hy =>
      intro h
      rw [wedgeTo_add_right]
      exact (spCone (n := n) m).add_mem (hx h) (hy h)
    | smul a x _ hx =>
      intro h
      rw [show a • x = (a : ℝ) • x from rfl, wedgeTo_smul_right]
      exact smul_mem_spCone (hx h) a.2

/-- The exterior product maps `Λ_r × Λ_k` into `Λ_m`, `r + k = m`. -/
theorem wedgeTo_mem_formSpan {r k m : ℕ} {P : RealForm n (2 * r)} (hP : P ∈ formSpan n r)
    {Q : RealForm n (2 * k)} (hQ : Q ∈ formSpan n k) (h : 2 * r + 2 * k = 2 * m) :
    wedgeTo h P Q ∈ formSpan n m := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    induction hQ using Submodule.span_induction with
    | mem y hy => exact mem_formSpan_of_mem_spCone (wedgeTo_mem_spCone k r m hx hy h)
    | zero => rw [wedgeTo_zero_right]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [wedgeTo_add_right]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [wedgeTo_smul_right]; exact Submodule.smul_mem _ _ hy
  | zero => rw [wedgeTo_zero_left]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [wedgeTo_add_left]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [wedgeTo_smul_left]; exact Submodule.smul_mem _ _ hx

variable (n) in
/-- **The exterior product of constant forms** `Λ_r × Λ_k → Λ_m` (`r + k = m`), bilinear. -/
def wedgeSpan {r k m : ℕ} (h : r + k = m) : formSpan n r →ₗ[ℝ] formSpan n k →ₗ[ℝ] formSpan n m :=
  LinearMap.mk₂ ℝ
    (fun γ β => ⟨wedgeTo (by omega : 2 * r + 2 * k = 2 * m) (γ : RealForm n (2 * r))
      (β : RealForm n (2 * k)), wedgeTo_mem_formSpan γ.2 β.2 _⟩)
    (fun γ γ' β => by ext1; exact wedgeTo_add_left _ _ _ _)
    (fun c γ β => by ext1; exact wedgeTo_smul_left _ _ _ _)
    (fun γ β β' => by ext1; exact wedgeTo_add_right _ _ _ _)
    (fun c γ β => by ext1; exact wedgeTo_smul_right _ _ _ _)

@[simp] theorem coe_wedgeSpan_apply {r k m : ℕ} (h : r + k = m) (γ : formSpan n r)
    (β : formSpan n k) (h' : 2 * r + 2 * k = 2 * m) :
    (wedgeSpan n h γ β : RealForm n (2 * m)) =
      wedgeTo h' (γ : RealForm n (2 * r)) (β : RealForm n (2 * k)) := rfl

end Products

/-! ### Invariance under the complex structure -/

section ComplexStructure

variable (n) in
/-- The forms invariant under the complex structure `J = i`. -/
def jInvariant (p : ℕ) : Submodule ℝ (RealForm n p) where
  carrier := {A | A.compContinuousLinearMap (complexJ n) = A}
  add_mem' {A B} hA hB := by
    change (A + B).compContinuousLinearMap (complexJ n) = A + B
    ext v
    have h1 := DFunLike.congr_fun hA v
    have h2 := DFunLike.congr_fun hB v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h1 h2 ⊢
    simp only [ContinuousAlternatingMap.add_apply, h1, h2]
  zero_mem' := by
    change (0 : RealForm n p).compContinuousLinearMap (complexJ n) = 0
    ext v
    rfl
  smul_mem' c A hA := by
    change (c • A).compContinuousLinearMap (complexJ n) = c • A
    ext v
    have h1 := DFunLike.congr_fun hA v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h1 ⊢
    simp only [ContinuousAlternatingMap.smul_apply, h1]

theorem mem_jInvariant_iff {p : ℕ} (A : RealForm n p) :
    A ∈ jInvariant n p ↔ A.compContinuousLinearMap (complexJ n) = A := Iff.rfl

theorem isOneOne_mem_jInvariant {β : RealForm n 2} (hβ : IsOneOne β) : β ∈ jInvariant n 2 := by
  rw [mem_jInvariant_iff]
  ext w
  rw [eq_vec_two w, ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two]
  exact hβ (w 0) (w 1)

theorem spCone_le_jInvariant : ∀ (k : ℕ) {P : RealForm n (2 * k)}, P ∈ spCone k →
    P ∈ jInvariant n (2 * k)
  | 0, P, hP => by
    induction hP using Submodule.span_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [mem_jInvariant_iff]
      ext v
      rfl
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ (a : ℝ) hx
  | k + 1, P, hP => by
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Q, hQ, β, hβ, rfl⟩ := hx
      rw [mem_jInvariant_iff, coordinateWedge_compContinuousLinearMap,
        (spCone_le_jInvariant k hQ : _), (isOneOne_mem_jInvariant hβ.1 : _)]
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ (a : ℝ) hx

/-- **The constant `(k,k)`-forms are invariant under the complex structure.** -/
theorem formSpan_le_jInvariant (k : ℕ) : formSpan n k ≤ jInvariant n (2 * k) :=
  Submodule.span_le.mpr fun _ hP => spCone_le_jInvariant k hP

end ComplexStructure

/-! ### The exterior derivative in coordinates -/

section ExtDeriv

variable {p : ℕ}

/-- **The alternation of an uncurried map**: for `f : E → Λᵖ` linear,
`∑_{π ∈ S_{p+1}} sgn π f(u_{π 0})(u ∘ π ∘ succ) = p! · (alternatizeUncurryFin f)(u)`. -/
theorem sum_perm_uncurry (f : E →L[ℝ] RealForm n p) (u : Fin (p + 1) → E) :
    ∑ π : Perm (Fin (p + 1)), ((Perm.sign π : ℤ) : ℝ) * f (u (π 0)) (u ∘ π ∘ Fin.succ) =
      (p.factorial : ℝ) * ContinuousAlternatingMap.alternatizeUncurryFin f u := by
  classical
  set G : Perm (Fin (p + 1)) → ℝ := fun π =>
    ((Perm.sign π : ℤ) : ℝ) * f (u (π 0)) (u ∘ π ∘ Fin.succ) with hG
  let e : Fin (p + 1) × Perm (Fin p) → Perm (Fin (p + 1)) := fun x =>
    x.1.cycleRange.symm * Perm.decomposeFin.symm (0, x.2)
  have he0 : ∀ x, e x 0 = x.1 := by
    rintro ⟨i, τ⟩
    simp [e, Perm.coe_mul]
  have hes : ∀ x (j : Fin p), e x j.succ = x.1.succAbove (x.2 j) := by
    rintro ⟨i, τ⟩ j
    simp [e, Perm.coe_mul]
  have he : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · rintro ⟨i, τ⟩ ⟨j, τ'⟩ hij
      have h0 : i = j := by
        have := congrArg (fun π : Perm (Fin (p + 1)) => π 0) hij
        simpa only [he0] using this
      subst h0
      have h1 : Perm.decomposeFin.symm ((0 : Fin (p + 1)), τ) =
          Perm.decomposeFin.symm ((0 : Fin (p + 1)), τ') := mul_left_cancel hij
      have h2 := Perm.decomposeFin.symm.injective h1
      simp only [Prod.mk.injEq, true_and] at h2
      rw [h2]
    · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_perm, Nat.factorial_succ]
  rw [← Fintype.sum_bijective e he (G ∘ e) G (fun _ => rfl), Fintype.sum_prod_type]
  have hterm : ∀ (i : Fin (p + 1)) (τ : Perm (Fin p)),
      (G ∘ e) (i, τ) = (-1) ^ (i : ℕ) * f (u i) (i.removeNth u) := by
    intro i τ
    have hsign : ((Perm.sign (e (i, τ)) : ℤ) : ℝ) =
        (-1) ^ (i : ℕ) * ((Perm.sign τ : ℤ) : ℝ) := by
      simp only [e, Perm.sign_mul, Perm.sign_symm, Fin.sign_cycleRange,
        Perm.decomposeFin.symm_sign, ite_true, one_mul, Units.val_mul, Int.cast_mul,
        Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg,
        Int.cast_one]
    have hcomp : u ∘ e (i, τ) ∘ Fin.succ = (i.removeNth u) ∘ τ := by
      funext j
      simp only [Function.comp_apply, hes, Fin.removeNth]
    simp only [Function.comp_apply, hG]
    rw [he0, hsign, hcomp, form_map_perm]
    have hsq : ((Perm.sign τ : ℤ) : ℝ) * ((Perm.sign τ : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    calc (-1) ^ (i : ℕ) * ((Perm.sign τ : ℤ) : ℝ) *
          (((Perm.sign τ : ℤ) : ℝ) * f (u i) (i.removeNth u)) =
        (-1) ^ (i : ℕ) * (((Perm.sign τ : ℤ) : ℝ) * ((Perm.sign τ : ℤ) : ℝ)) *
          f (u i) (i.removeNth u) := by ring
      _ = _ := by rw [hsq, mul_one]
  simp_rw [hterm]
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- **`ℓ ∧ A` by the alternating sum**: `(ℓ ∧ A)(v) = ∑ᵢ (-1)ⁱ ℓ(vᵢ) A(v without vᵢ)`, i.e. the
exterior product with a one-form (read in degree `p + 1`) is
`ClosedProductCurrents.oneWedge`. -/
theorem wedgeTo_oneForm_eq_oneWedge (h : 1 + p = p + 1) (ℓ : E →L[ℝ] ℝ) (A : RealForm n p) :
    wedgeTo h (oneForm n ℓ) A = oneWedge ℓ A := by
  ext u
  rw [wedgeTo_apply, coordinateWedge_apply_perm, oneWedge]
  have hsum := sum_perm_uncurry (ℓ.smulRight A) u
  have hfac : ((Nat.factorial 1 * p.factorial : ℕ) : ℝ) = p.factorial := by simp
  rw [hfac]
  suffices key : ∑ π : Perm (Fin (1 + p)), ((Perm.sign π : ℤ) : ℝ) *
      (oneForm n ℓ ((u ∘ Fin.cast h) ∘ π ∘ finSumFinEquiv ∘ Sum.inl) *
        A ((u ∘ Fin.cast h) ∘ π ∘ finSumFinEquiv ∘ Sum.inr)) =
      ∑ π : Perm (Fin (p + 1)), ((Perm.sign π : ℤ) : ℝ) *
        (ℓ.smulRight A) (u (π 0)) (u ∘ π ∘ Fin.succ) by
    rw [key, hsum, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  refine Fintype.sum_equiv (finCongr h).permCongr _ _ fun π => ?_
  rw [Perm.sign_permCongr]
  have h0 : (Fin.cast h (finSumFinEquiv (Sum.inl (0 : Fin 1)))) = 0 := Fin.ext (by simp)
  have hs : ∀ j : Fin p, Fin.cast h (finSumFinEquiv (Sum.inr j)) = j.succ :=
    fun j => Fin.ext (by simp)
  have hπ : ∀ x : Fin (1 + p),
      Fin.cast h (π x) = ((finCongr h).permCongr π) (Fin.cast h x) := by
    intro x
    simp [Equiv.permCongr_apply]
  have e1 : (u ∘ Fin.cast h ∘ π ∘ finSumFinEquiv ∘ Sum.inl) =
      fun _ : Fin 1 => u (((finCongr h).permCongr π) 0) := by
    funext i
    rw [Subsingleton.elim i 0]
    simp only [Function.comp_apply, hπ, h0]
  have e2 : (u ∘ Fin.cast h ∘ π ∘ finSumFinEquiv ∘ Sum.inr) =
      u ∘ ((finCongr h).permCongr π) ∘ Fin.succ := by
    funext j
    simp only [Function.comp_apply, hπ, hs]
  rw [show (u ∘ Fin.cast h) ∘ π ∘ finSumFinEquiv ∘ Sum.inl =
      u ∘ Fin.cast h ∘ π ∘ finSumFinEquiv ∘ Sum.inl from rfl,
    show (u ∘ Fin.cast h) ∘ π ∘ finSumFinEquiv ∘ Sum.inr =
      u ∘ Fin.cast h ∘ π ∘ finSumFinEquiv ∘ Sum.inr from rfl, e1, e2]
  simp only [oneForm_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- A linear map into forms, expanded in the coordinate forms: `f = ∑_a e^a ⊗ f(b_a)`. -/
theorem eq_sum_smulRight (f : E →L[ℝ] RealForm n p) :
    f = ∑ a, (coordCLM n a).smulRight (f (realBasis n a)) := by
  ext1 w
  rw [_root_.sum_apply]
  conv_lhs => rw [← sum_coordCLM_smul w]
  simp only [map_sum, map_smul, ContinuousLinearMap.smulRight_apply]

/-- **The uncurried alternation in coordinates**: `alternatizeUncurryFin f = ∑_a e^a ∧ f(b_a)`. -/
theorem alternatizeUncurryFin_eq_sum (f : E →L[ℝ] RealForm n p) (h : 1 + p = p + 1) :
    ContinuousAlternatingMap.alternatizeUncurryFin f =
      ∑ a, wedgeTo h (oneForm n (coordCLM n a)) (f (realBasis n a)) := by
  conv_lhs => rw [eq_sum_smulRight f]
  rw [show ContinuousAlternatingMap.alternatizeUncurryFin
      (∑ a, (coordCLM n a).smulRight (f (realBasis n a))) =
      ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ
        (∑ a, (coordCLM n a).smulRight (f (realBasis n a))) from rfl, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wedgeTo_oneForm_eq_oneWedge]
  rfl

/-- **The coordinate formula for the exterior derivative**: `dα(x) = ∑_a e^a ∧ ∂_a α(x)`, for
mathlib's `extDeriv`. -/
theorem extDeriv_eq_sum (α : E → RealForm n p) (x : E) (h : 1 + p = p + 1) :
    extDeriv α x = ∑ a, wedgeTo h (oneForm n (coordCLM n a)) (fderiv ℝ α x (realBasis n a)) :=
  alternatizeUncurryFin_eq_sum _ h

/-- The coordinate formula for the exterior derivative, with `oneWedge`. -/
theorem extDeriv_eq_sum_oneWedge (α : E → RealForm n p) (x : E) :
    extDeriv α x = ∑ a, oneWedge (coordCLM n a) (fderiv ℝ α x (realBasis n a)) := by
  rw [extDeriv_eq_sum α x (Nat.add_comm 1 p)]
  simp only [wedgeTo_oneForm_eq_oneWedge]

/-- Pullback commutes with `oneWedge`. -/
theorem oneWedge_compContinuousLinearMap (ℓ : E →L[ℝ] ℝ) (A : RealForm n p) (L : E →L[ℝ] E) :
    (oneWedge ℓ A).compContinuousLinearMap L =
      oneWedge (ℓ.comp L) (A.compContinuousLinearMap L) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, oneWedge,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.smul_apply, Function.comp_apply]
  rfl

theorem sum_compContinuousLinearMap {ι : Type*} (s : Finset ι) (F : ι → RealForm n p)
    (L : E →L[ℝ] E) :
    (∑ i ∈ s, F i).compContinuousLinearMap L = ∑ i ∈ s, (F i).compContinuousLinearMap L :=
  map_sum (ContinuousAlternatingMap.compContinuousLinearMapₗ (ι := Fin p) (N := ℝ) L) F s

/-- **The `(k+1,k+1)`-parts of `ℓ ∧ dα` vanish for a closed form of type `(k,k)`.**  If
`D_a ∈ Λ_k` (more generally `J`-invariant) and `∑_a e^a ∧ D_a = 0` (as `oneWedge`), then for
every real linear form `ℓ`, `∑_a Π₁₁(e^a ∧ ℓ) ∧ D_a = 0`. -/
theorem sum_wedgeTo_testForm_eq_zero {k m : ℕ} (D : Fin (n * 2) → RealForm n (2 * k))
    (hD : ∀ a, D a ∈ jInvariant n (2 * k)) (h0 : ∑ a, oneWedge (coordCLM n a) (D a) = 0)
    (ℓ : E →L[ℝ] ℝ) (h : 2 + 2 * k = m) : ∑ a, wedgeTo h (testForm a ℓ) (D a) = 0 := by
  have hJ : ∑ a, oneWedge (coordJ n a) (D a) = 0 := by
    have := congrArg (fun F : RealForm n (2 * k + 1) => F.compContinuousLinearMap (complexJ n)) h0
    simp only [sum_compContinuousLinearMap, oneWedge_compContinuousLinearMap] at this
    have hz : (0 : RealForm n (2 * k + 1)).compContinuousLinearMap (complexJ n) = 0 := by
      ext v
      rfl
    rw [hz] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hD a : _)]
    rfl
  have h1 : 1 + 2 * k = 2 * k + 1 := by omega
  have h2 : 1 + (2 * k + 1) = m := by omega
  have hone : ∀ (x y : RealForm n 1) (a : Fin (n * 2)),
      wedgeTo h (coordinateWedge x y : RealForm n 2) (D a) = -wedgeTo h2 y (wedgeTo h1 x (D a))
        := by
    intro x y a
    rw [show (coordinateWedge x y : RealForm n 2) = -coordinateWedge y x from
      coordinateWedge_comm_one x y, wedgeTo_neg_left]
    congr 1
    exact wedgeTo_assoc (rfl : 1 + 1 = 2) h (h1) h2 y x (D a)
  have e : ∀ a, wedgeTo h (testForm a ℓ) (D a) = (1 / 2 : ℝ) •
      (-wedgeTo h2 (oneForm n ℓ) (oneWedge (coordCLM n a) (D a)) -
        wedgeTo h2 (oneForm n (ℓ.comp (complexJ n))) (oneWedge (coordJ n a) (D a))) := by
    intro a
    rw [testForm_eq, wedgeTo_smul_left, wedgeTo_add_left, hone, hone,
      wedgeTo_oneForm_eq_oneWedge, wedgeTo_oneForm_eq_oneWedge]
    congr 1
  simp_rw [e]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← wedgeTo_sum_right, ← wedgeTo_sum_right, h0, hJ, wedgeTo_zero_right, wedgeTo_zero_right,
    neg_zero, sub_zero, smul_zero]

end ExtDeriv

end SGPT.Foundations.Analysis.Pending.ConstantFormProducts
