/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import LeanPool.RoyStrongSix.M2.ExpPoly
public import LeanPool.RoyStrongSix.Thm1.MultEst

/-!
# The geometric layer for Roy's proof

`G = K^{d₀} × (K^×)^{d₁}` is embedded in `K^{d₀ + 2 d₁}` by `pt (x, y) = (x, y, y⁻¹)`. Polynomials
live in
`B = K[X, Y, Z]` (`V3 d₀ d₁` variables).

* `pt`, `gmul`: the embedding and the group law.
* `vanish E`: the ideal of polynomials vanishing on `pt '' E`.
* `zeros 𝒫`: the points of `G` where every polynomial in `𝒫` vanishes.
* `IsSubgroupG`: a subgroup of `G`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial

namespace StrongSix.M2

open StrongSix.Thm1

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

/-- The variables `X₁..X_{d₀}, Y₁..Y_{d₁}, Z₁..Z_{d₁}`. -/
abbrev V3 (d0 d1 : ℕ) := Fin d0 ⊕ (Fin d1 ⊕ Fin d1)

/-- The embedding `(x, y) ↦ (x, y, y⁻¹)`. -/
def pt (g : GPt K d0 d1) : V3 d0 d1 → K :=
  Sum.elim g.1 (Sum.elim (fun j => (g.2 j : K)) fun j => ((g.2 j)⁻¹ : Kˣ))

/-- The group law of `G`. -/
def gmul (g h : GPt K d0 d1) : GPt K d0 d1 := (g.1 + h.1, g.2 * h.2)

/-- The inverse in `G`. -/
def ginv (g : GPt K d0 d1) : GPt K d0 d1 := (-g.1, g.2⁻¹)

/-- The ideal of polynomials vanishing on `E`. -/
def vanish (E : Set (GPt K d0 d1)) : Ideal (MvPolynomial (V3 d0 d1) K) where
  carrier := {P | ∀ g ∈ E, eval (pt g) P = 0}
  add_mem' ha hb g hg := by simp [ha g hg, hb g hg]
  zero_mem' g _ := by simp
  smul_mem' c P hP g hg := by simp [hP g hg]

/-- The zero set in `G` of a family of polynomials. -/
def zeros (Ps : Set (MvPolynomial (V3 d0 d1) K)) : Set (GPt K d0 d1) :=
  {g | ∀ P ∈ Ps, eval (pt g) P = 0}

/-- A subgroup of `G`. -/
structure IsSubgroupG (E : Set (GPt K d0 d1)) : Prop where
  one_mem : GPt.zero ∈ E
  mul_mem : ∀ g ∈ E, ∀ h ∈ E, gmul g h ∈ E
  inv_mem : ∀ g ∈ E, ginv g ∈ E

omit [CharZero K] in
theorem IsSubgroupG.toSubmonoidG {E : Set (GPt K d0 d1)} (h : IsSubgroupG E) : IsSubmonoidG E :=
  ⟨h.one_mem, h.mul_mem⟩

omit [CharZero K] in
theorem chr_add (y : Fin d1 → Kˣ) (a b : Fin d1 → ℤ) : chr y (a + b) = chr y a * chr y b := by
  simp only [chr, Pi.add_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (Units.ne_zero _) _ _

omit [CharZero K] in
theorem chr_sub (y : Fin d1 → Kˣ) (a b : Fin d1 → ℤ) : chr y (a - b) = chr y a / chr y b := by
  rw [eq_div_iff (chr_ne_zero y b), ← chr_add, sub_add_cancel]

omit [CharZero K] in
/-- The `Y, Z` part of a monomial evaluated at `pt (x, y)`. -/
theorem prod_pt (g : GPt K d0 d1) (m : V3 d0 d1 →₀ ℕ) :
    (∏ v, pt g v ^ m v) = (∏ k, g.1 k ^ m (Sum.inl k)) *
      chr g.2 (fun j => (m (Sum.inr (Sum.inl j)) : ℤ) - m (Sum.inr (Sum.inr j))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [pt, Sum.elim_inl, Sum.elim_inr, chr]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_sub₀ (Units.ne_zero _), zpow_natCast, zpow_natCast, Units.val_inv_eq_inv_val, inv_pow,
    div_eq_mul_inv]

omit [CharZero K] in
theorem eval_pt (g : GPt K d0 d1) (P : MvPolynomial (V3 d0 d1) K) :
    eval (pt g) P = ∑ m ∈ P.support, P.coeff m * ((∏ k, g.1 k ^ m (Sum.inl k)) *
      chr g.2 (fun j => (m (Sum.inr (Sum.inl j)) : ℤ) - m (Sum.inr (Sum.inr j)))) := by
  rw [eval_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← prod_pt]
  congr 1
  exact Finsupp.prod_fintype m (fun i e => pt g i ^ e) (fun _ => pow_zero _)

end StrongSix.M2

end LeanPool
