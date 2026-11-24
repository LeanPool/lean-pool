/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermNoetherNormalization

/-!
# Algebraic parametrization data of a prime ideal of `𝒪_n` in Noether position

Blueprint `lag:minimal-polynomial-weierstrass`, `lag:primitive-element`,
`lag:substitution-relations`, `lag:ideal-comparison` (Demailly, *Complex analytic and
differential geometry*, II.4.13--4.18).

Let `Q ⊆ 𝒪_n` be prime and in Noether position over `𝒪_d` (`IsNoetherNormalization Q d`).
`AlgebraicParametrization Q d` records the germ-level algebra that the local
parametrization theorem consumes, with `z = (z', z'')`, `z' ∈ ℂᵈ`:

* for each fibre coordinate `z_k` (`d ≤ k`), its minimal polynomial `Q_k ∈ 𝒪_d[T]`, a
  Weierstrass polynomial with `Q_k(z', z_k) ∈ Q`;
* a primitive element `u = ∑_{k ≥ d} c_k z_k` with constant `c_k ∈ ℂ`, whose minimal
  polynomial `W ∈ 𝒪_d[T]` is a Weierstrass polynomial of positive degree dividing every
  `F ∈ 𝒪_d[T]` with `F(u) ∈ Q`;
* `δ ∈ 𝒪_d \ 0` and `B_k ∈ 𝒪_d[T]`, `deg B_k < deg W`, with `δ z_k - B_k(u) ∈ Q`,
  `W ∣ ∑_k c_k B_k - δ T`, and `δ ∈ (W, ∂_T W)`;
* for `f ∉ Q` a nonzero `h ∈ 𝒪_d` with `h ∈ (f) + Q`;
* reduction: every germ is a polynomial in `z''` over `𝒪_d` modulo the `Q_k(z', z_k)`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace SGPT.Foundations.Analysis.Pending.GermAlgebraicParametrization

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open HolGerm

noncomputable section

/-- The germ of the coordinate `z_k`, `k : Fin n`. -/
abbrev coord {n : ℕ} (k : Fin n) : HolGerm (ComplexModel n) :=
  coordGerm n k.1 k.2

/-- The germ of the linear form `u = ∑_{k ≥ d} c_k z_k` on `ℂⁿ`. -/
def linearFormGerm (n d : ℕ) (c : Fin n → ℂ) : HolGerm (ComplexModel n) :=
  ∑ k : Fin n, if d ≤ k.1 then constHom (c k) * coord k else 0

/-- A polynomial over `𝒪_d` evaluated at a germ on `ℂⁿ`. -/
abbrev evalGerm (n : ℕ) {d : ℕ} (F : (HolGerm (ComplexModel d))[X])
    (g : HolGerm (ComplexModel n)) : HolGerm (ComplexModel n) :=
  F.eval₂ (projGerm n d) g

/-- A Weierstrass polynomial over `𝒪_d`: monic, with lower coefficients vanishing at `0`. -/
def IsWeierstrass {d : ℕ} (W : (HolGerm (ComplexModel d))[X]) : Prop :=
  W.Monic ∧ ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0

/-- **Algebraic parametrization data** of an ideal `Q ⊆ 𝒪_n` over `𝒪_d`. -/
structure AlgebraicParametrization {n : ℕ} (Q : Ideal (HolGerm (ComplexModel n))) (d : ℕ) where
  le : d ≤ n
  eq_zero_of_mem : ∀ c : HolGerm (ComplexModel d), projGerm n d c ∈ Q → c = 0
  /-- Minimal polynomials `Q_k` of the fibre coordinates. -/
  coordPoly : Fin n → (HolGerm (ComplexModel d))[X]
  isWeierstrass_coordPoly : ∀ k : Fin n, d ≤ k.1 → IsWeierstrass (coordPoly k)
  coordPoly_mem : ∀ k : Fin n, d ≤ k.1 → evalGerm n (coordPoly k) (coord k) ∈ Q
  /-- Coefficients of the primitive element `u`. -/
  coef : Fin n → ℂ
  /-- The minimal polynomial `W` of `u`. -/
  minpoly : (HolGerm (ComplexModel d))[X]
  isWeierstrass_minpoly : IsWeierstrass minpoly
  natDegree_minpoly_pos : 0 < minpoly.natDegree
  minpoly_mem : evalGerm n minpoly (linearFormGerm n d coef) ∈ Q
  dvd_of_mem : ∀ F : (HolGerm (ComplexModel d))[X],
    evalGerm n F (linearFormGerm n d coef) ∈ Q → minpoly ∣ F
  /-- The denominator `δ`. -/
  disc : HolGerm (ComplexModel d)
  disc_ne_zero : disc ≠ 0
  /-- The polynomials `B_k`. -/
  B : Fin n → (HolGerm (ComplexModel d))[X]
  natDegree_B_lt : ∀ k, (B k).natDegree < minpoly.natDegree
  disc_mul_sub_mem : ∀ k : Fin n, d ≤ k.1 →
    projGerm n d disc * coord k - evalGerm n (B k) (linearFormGerm n d coef) ∈ Q
  dvd_recover : minpoly ∣
    (∑ k : Fin n, if d ≤ k.1 then C (constHom (coef k)) * B k else 0) - C disc * X
  bezout : ∃ a b : (HolGerm (ComplexModel d))[X], a * minpoly + b * derivative minpoly = C disc
  exists_eqn : ∀ f ∉ Q, ∃ h : HolGerm (ComplexModel d), h ≠ 0 ∧
    ∃ g : HolGerm (ComplexModel n), projGerm n d h - f * g ∈ Q
  reduce : ∀ g : HolGerm (ComplexModel n),
    ∃ (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) (q : Fin n → HolGerm (ComplexModel n)),
      (∀ m ∈ R.support, ∀ i : Fin n, i.1 < d → m i = 0) ∧
      g = MvPolynomial.eval₂ (projGerm n d) coord R +
        ∑ k : Fin n, if d ≤ k.1 then q k * evalGerm n (coordPoly k) (coord k) else 0

end

end SGPT.Foundations.Analysis.Pending.GermAlgebraicParametrization
