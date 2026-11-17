/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring

/-!
# The multiplicity estimate on `G_a^{d₀} × G_m^{d₁}`

This file only *states* `MultEst K`, as a `Prop`. `Thm1/Main.lean` proves
`MultEst Qb → WaldschmidtTheorem1` (`StrongSix.Thm1.theorem1_of_multEst`), and `M2/` proves
`MultEst K` for every algebraically closed `K` of characteristic `0`
(`StrongSix.M2.multEst_of_isAlgClosed`, in `StrongSix/M2/Final.lean`), hence `MultEst Qb`.

## Source

P. Philippon, *Lemmes de zéros dans les groupes algébriques commutatifs*, Bull. SMF 114 (1986)
355–383, Théorème 2.1 (errata: Bull. SMF 115 (1987) 397–398). It is specialized to
`G = G_a^{d₀} × G_m^{d₁} ⊂ ℙ^{d₀} × ℙ^{d₁}`, so `p = 2` and `n = dim G = d₀ + d₁`:

> Let `T ≥ 1`. Suppose a polynomial `P` of bidegree `(D₀, D₁)` vanishes to order `≥ nT + 1` along
> `A` at every point of `Σ(n) = {σ₁ + ⋯ + σₙ}`, where `0 ∈ Σ`. Then there is a connected algebraic
> subgroup `G'` of `G`, contained in a translate of `G ∩ Z(P)` (so `G' ≠ G`), with
> `binom(T + c, c) · card((Σ + G')/G') · H(G'; D₀, D₁) ≤ H(G; c₀D₀, c₁D₁)`,
> where `c = codim_A(A ∩ G')`.

Translation to the form below:
* `A` is the analytic subgroup with Lie algebra `W`. Vanishing to order `≥ k` along `A` at `g` means
  `D_{w₁} ⋯ D_{w_r} P (g) = 0` for all `r < k` and `wᵢ ∈ W`. Here `D_w` is the invariant derivation
  `Σ wᵢ ∂/∂Xᵢ + Σ w'ⱼ Yⱼ ∂/∂Yⱼ`.
* The connected algebraic subgroups of `G` are `H = h₀ × T_U`. Here `h₀ ⊂ K^{d₀}` is a subspace,
  `U ⊂ ℚ^{d₁}` is a subspace of characters, and `T_U = {y : y^φ = 1 for all φ ∈ U ∩ ℤ^{d₁}}`.
  See Waldschmidt's notes *Linear independence of logarithms of algebraic numbers*, Prop. 8.3 (by
  Roy).
  * `Lie H = h₀ × U^⊥` and `dim H = dim h₀ + d₁ − dim U`.
  * `H(H; D₀, D₁) ≥ D₀^{dim h₀} D₁^{d₁ − dim U}` up to a constant.
  * `H(G; c₀D₀, c₁D₁)` is a constant times `D₀^{d₀} D₁^{d₁}`.
* `binom(T + c, c) ≥ T^c / c!`, and `card((Σ + H)/H)` is at least the size of any subset `F ⊆ Σ` of
  pairwise inequivalent points.

All constants depend only on `(d₀, d₁)` and are absorbed in `C`.

Philippon states the theorem over `ℂ` and `ℂ_p`. The proof (§§3–5) is algebraic, and the
obstruction `G'` comes from components of algebraic sets defined over the field of definition of
`P`, `Σ` and `W`. So the statement holds over any algebraically closed field of characteristic 0.
We use it over `K = Qbar = algebraicClosure ℚ ℂ`.
-/

@[expose] public section

namespace LeanPool

open Module

namespace StrongSix.Thm1

/-- The variables: `Sum.inl i` is the additive coordinate `Xᵢ`, `Sum.inr j` the multiplicative
coordinate `Yⱼ`. -/
abbrev Var (d0 d1 : ℕ) := Fin d0 ⊕ Fin d1

/-- The Lie algebra `K^{d₀} × K^{d₁}` of `G_a^{d₀} × G_m^{d₁}`. -/
abbrev LieG (K : Type*) (d0 d1 : ℕ) := (Fin d0 → K) × (Fin d1 → K)

/-- `K`-points of `G = G_a^{d₀} × G_m^{d₁}`. -/
abbrev GPt (K : Type*) [Monoid K] (d0 d1 : ℕ) := (Fin d0 → K) × (Fin d1 → Kˣ)

variable {K : Type*} [Field K] {d0 d1 : ℕ}

/-- The coordinates of a point, as a valuation of the variables. -/
def GPt.coords (g : GPt K d0 d1) : Var d0 d1 → K := Sum.elim g.1 fun j => (g.2 j : K)

/-- The neutral element `(0, 1)` of `G`. -/
def GPt.zero : GPt K d0 d1 := (0, 1)

/-- The group law of `G`, iterated: `σ₁ + ⋯ + σₖ`. -/
def gsum {k : ℕ} (σ : Fin k → GPt K d0 d1) : GPt K d0 d1 := (∑ i, (σ i).1, ∏ i, (σ i).2)

/-- The invariant derivation `D_w = Σ wᵢ ∂/∂Xᵢ + Σ w'ⱼ Yⱼ ∂/∂Yⱼ` for `w = (w, w')` in the Lie
algebra. -/
noncomputable def invDer (w : LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K) :
    MvPolynomial (Var d0 d1) K :=
  ∑ i, w.1 i • MvPolynomial.pderiv (Sum.inl i) P +
    ∑ j, w.2 j • (MvPolynomial.X (Sum.inr j) * MvPolynomial.pderiv (Sum.inr j) P)

/-- `D_{w₁} (D_{w₂} ( ⋯ (D_{w_r} P)))` for the list `[w₁, …, w_r]`. -/
noncomputable def invDers (l : List (LieG K d0 d1)) (P : MvPolynomial (Var d0 d1) K) :
    MvPolynomial (Var d0 d1) K :=
  l.foldr invDer P

/-- `P` vanishes to order `≥ k` along `W` at `g`: every derivative `D_{w₁} ⋯ D_{w_r} P` with
`r < k` and all `wᵢ ∈ W` vanishes at `g`. -/
def VanishesAlong (W : Submodule K (LieG K d0 d1)) (P : MvPolynomial (Var d0 d1) K) (k : ℕ)
    (g : GPt K d0 d1) : Prop :=
  ∀ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) → l.length < k →
    MvPolynomial.eval g.coords (invDers l P) = 0

/-- `P` has total degree `≤ D₀` in the `X`'s and `≤ D₁` in the `Y`'s. -/
def BidegLE (P : MvPolynomial (Var d0 d1) K) (D0 D1 : ℕ) : Prop :=
  ∀ m ∈ P.support, (∑ i, m (Sum.inl i)) ≤ D0 ∧ (∑ j, m (Sum.inr j)) ≤ D1

/-- The Lie algebra `U^⊥ = {v : Σ φⱼ vⱼ = 0 for all φ ∈ U}` of the torus `T_U`. -/
def torusLie (K : Type*) [Field K] (U : Submodule ℚ (Fin d1 → ℚ)) : Submodule K (Fin d1 → K) where
  carrier := {v | ∀ φ ∈ U, ∑ j, (φ j : K) * v j = 0}
  add_mem' {a b} ha hb φ hφ := by
    change ∑ j, (φ j : K) * (a j + b j) = 0
    rw [show (∑ j, (φ j : K) * (a j + b j)) =
        (∑ j, (φ j : K) * a j) + ∑ j, (φ j : K) * b j by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring,
      ha φ hφ, hb φ hφ, add_zero]
  zero_mem' φ _ := by simp
  smul_mem' c v hv φ hφ := by
    change ∑ j, (φ j : K) * (c * v j) = 0
    rw [show (∑ j, (φ j : K) * (c * v j)) = c * ∑ j, (φ j : K) * v j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hv φ hφ, mul_zero]

/-- `g ≡ g' (mod H)` for `H = h₀ × T_U`: `g − g' ∈ h₀` and `(g/g')^φ = 1` for every integral
`φ ∈ U`. -/
def EquivMod (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ))
    (g g' : GPt K d0 d1) : Prop :=
  g.1 - g'.1 ∈ h0 ∧
    ∀ φ : Fin d1 → ℤ, (fun j => (φ j : ℚ)) ∈ U → ∏ j, (g.2 j / g'.2 j) ^ φ j = 1

/-- **The multiplicity estimate on `G_a^{d₀} × G_m^{d₁}` over `K`** (Philippon 1986, Thm. 2.1, with
the constants absorbed). The obstruction is `H = h₀ × T_U ≠ G`, and
`c = dim W − dim (W ∩ Lie H)`. -/
def MultEst (K : Type*) [Field K] : Prop :=
  ∀ d0 d1 : ℕ, ∃ C : ℝ, ∀ (W : Submodule K (LieG K d0 d1)) (S : Finset (GPt K d0 d1))
    (P : MvPolynomial (Var d0 d1) K) (T D0 D1 : ℕ),
    GPt.zero ∈ S → P ≠ 0 → BidegLE P D0 D1 → 1 ≤ T → 1 ≤ D0 → 1 ≤ D1 →
    (∀ σ : Fin (d0 + d1) → GPt K d0 d1, (∀ i, σ i ∈ S) →
      VanishesAlong W P ((d0 + d1) * T + 1) (gsum σ)) →
    ∃ (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ)),
      (h0 ≠ ⊤ ∨ U ≠ ⊥) ∧
      ∀ F : Finset (GPt K d0 d1), F ⊆ S →
        (∀ g ∈ F, ∀ g' ∈ F, EquivMod h0 U g g' → g = g') →
        (T : ℝ) ^ (finrank K W - finrank K ↥(W ⊓ h0.prod (torusLie K U))) * F.card *
            (D0 : ℝ) ^ finrank K h0 * (D1 : ℝ) ^ (d1 - finrank ℚ U) ≤
          C * (D0 : ℝ) ^ d0 * (D1 : ℝ) ^ d1

end StrongSix.Thm1

end LeanPool
