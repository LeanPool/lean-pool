/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AnalyticGermDecomposition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularLocusDense

/-!
# Local parametrization of an irreducible germ: the pointwise data

Blueprint `lag:parametrization-sets` (Demailly, *Complex analytic and differential geometry*,
II.4.19).  In coordinates `z = (z', z'')`, `z' = π z ∈ ℂᵈ` the first `d` coordinates, the
algebra of an irreducible germ `A` at `0 ∈ ℂⁿ` (Noether normalization, the primitive element
`u`, its minimal polynomial `W`, the discriminant multiple `δ` and the polynomials `B_k`,
the minimal polynomials `Q_k` of the fibre coordinates, and the ideal comparison) yields
the following identities of holomorphic functions on a ball `ball 0 rad`.  They are all
that the geometric part of the parametrization theorem uses.

* `W(z', u(z)) = 0`, `δ(z') z_k = B_k(z', u(z))`, `Q_k(z', z_k) = 0` on `A`;
* for every root `t` of `W(x, ·)`: `u` recovers `t` from `B(x, t) / δ(x)`, the coordinates
  `B_k(x, t) / δ(x)` are roots of `Q_k(x, ·)`, and the root is simple when `δ(x) ≠ 0`;
* completeness: a point of the ball with `δ(z') ≠ 0` satisfying the first two identities
  lies in `A`;
* primality of the vanishing ideal, `I(A) ∩ 𝒪_d = 0`, and the integral equation over `𝒪_d`
  of a function vanishing on `A ∩ B`.

`SetsData` records the geometric consequences on a polydisc (blueprint
`lag:parametrization-sets`, `lag:parametrization-regular`).
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrizationData

open FirstPass RegularLocusDense AnalyticGermDecomposition

noncomputable section

/-- The monic polynomial `t ^ q + ∑_{j<q} a_j(x) t ^ j` with function coefficients. -/
def monicEval {E : Type*} (q : ℕ) (a : ℕ → E → ℂ) (x : E) (t : ℂ) : ℂ :=
  t ^ q + ∑ j ∈ Finset.range q, a j x * t ^ j

/-- The polynomial `∑_{j<q} b_j(x) t ^ j` with function coefficients. -/
def lowEval {E : Type*} (q : ℕ) (b : ℕ → E → ℂ) (x : E) (t : ℂ) : ℂ :=
  ∑ j ∈ Finset.range q, b j x * t ^ j

/-- The form `u(z) = ∑_{k ≥ d} c_k(z') z_k`, linear in the fibre coordinates. -/
def fibreForm {n : ℕ} (d : ℕ) (c : Fin n → ComplexModel d → ℂ) (z : ComplexModel n) : ℂ :=
  ∑ k : Fin n, if d ≤ k.1 then c k (coordinateProjection n d z) * z k else 0

/-- The polydisc `{‖z'‖ < r₁, |z_k| < r₂ for k ≥ d}`. -/
def polydisc (n d : ℕ) (r₁ r₂ : ℝ) : Set (ComplexModel n) :=
  {z | ‖coordinateProjection n d z‖ < r₁ ∧ ∀ k : Fin n, d ≤ k.1 → ‖z k‖ < r₂}

variable {n : ℕ}

/-- **Pointwise parametrization data** of a germ `A` at `0 ∈ ℂⁿ` in adapted coordinates. -/
structure ParametrizationData (A : Set (ComplexModel n)) where
  /-- The dimension `d`. -/
  dim : ℕ
  dim_le : dim ≤ n
  /-- The degree `q` of the covering. -/
  deg : ℕ
  deg_pos : 0 < deg
  /-- The radius of the ball on which the identities hold. -/
  rad : ℝ
  rad_pos : 0 < rad
  /-- Coefficients of the minimal polynomial `W` of the primitive element. -/
  w : ℕ → ComplexModel dim → ℂ
  differentiableOn_w : ∀ j, DifferentiableOn ℂ (w j) (ball 0 rad)
  w_zero : ∀ j < deg, w j 0 = 0
  /-- The discriminant multiple `δ`. -/
  disc : ComplexModel dim → ℂ
  differentiableOn_disc : DifferentiableOn ℂ disc (ball 0 rad)
  disc_not_eventually_zero : ¬ ∀ᶠ x in 𝓝 0, disc x = 0
  /-- Coefficients of the primitive element `u = ∑_{k ≥ d} c_k(z') z_k`. -/
  coef : Fin n → ComplexModel dim → ℂ
  differentiableOn_coef : ∀ k, DifferentiableOn ℂ (coef k) (ball 0 rad)
  /-- Coefficients of `B_k`, of degree `< q`. -/
  b : Fin n → ℕ → ComplexModel dim → ℂ
  differentiableOn_b : ∀ k j, DifferentiableOn ℂ (b k j) (ball 0 rad)
  /-- Degrees and coefficients of the minimal polynomials `Q_k` of the fibre coordinates. -/
  s : Fin n → ℕ
  /-- The linear coordinates used for the local projection. -/
  e : Fin n → ℕ → ComplexModel dim → ℂ
  differentiableOn_e : ∀ k j, DifferentiableOn ℂ (e k j) (ball 0 rad)
  e_zero : ∀ k, ∀ j < s k, e k j 0 = 0
  /-- `W(z', u(z)) = 0` on `A`. -/
  w_eq_zero : ∀ z ∈ A, z ∈ ball 0 rad →
    monicEval deg w (coordinateProjection n dim z) (fibreForm dim coef z) = 0
  /-- `δ(z') z_k = B_k(z', u(z))` on `A`. -/
  disc_mul_eq : ∀ z ∈ A, z ∈ ball 0 rad → ∀ k : Fin n, dim ≤ k.1 →
    disc (coordinateProjection n dim z) * z k =
      lowEval deg (b k) (coordinateProjection n dim z) (fibreForm dim coef z)
  /-- `Q_k(z', z_k) = 0` on `A`. -/
  e_eq_zero : ∀ z ∈ A, z ∈ ball 0 rad → ∀ k : Fin n, dim ≤ k.1 →
    monicEval (s k) (e k) (coordinateProjection n dim z) (z k) = 0
  /-- `∑_k c_k B_k ≡ δ T` modulo `W`. -/
  recover : ∀ x ∈ ball (0 : ComplexModel dim) rad, ∀ t : ℂ, monicEval deg w x t = 0 →
    ∑ k : Fin n, (if dim ≤ k.1 then coef k x * lowEval deg (b k) x t else 0) = disc x * t
  /-- The coordinates `B_k(x, t) / δ(x)` over a root are roots of `Q_k(x, ·)`. -/
  subst : ∀ x ∈ ball (0 : ComplexModel dim) rad, disc x ≠ 0 → ∀ t : ℂ,
    monicEval deg w x t = 0 → ∀ k : Fin n, dim ≤ k.1 →
      monicEval (s k) (e k) x (lowEval deg (b k) x t / disc x) = 0
  /-- Off the discriminant locus the roots of `W(x, ·)` are simple. -/
  simple : ∀ x ∈ ball (0 : ComplexModel dim) rad, disc x ≠ 0 → ∀ t : ℂ,
    monicEval deg w x t = 0 → deriv (monicEval deg w x) t ≠ 0
  /-- Completeness (ideal comparison). -/
  complete : ∀ z ∈ ball (0 : ComplexModel n) rad, disc (coordinateProjection n dim z) ≠ 0 →
    monicEval deg w (coordinateProjection n dim z) (fibreForm dim coef z) = 0 →
    (∀ k : Fin n, dim ≤ k.1 → disc (coordinateProjection n dim z) * z k =
      lowEval deg (b k) (coordinateProjection n dim z) (fibreForm dim coef z)) → z ∈ A
  /-- The germ is irreducible: its vanishing ideal is prime. -/
  prime : ∀ f g : ComplexModel n → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) →
    (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) → (∀ᶠ z in 𝓝 0, z ∈ A → f z * g z = 0) →
      (∀ᶠ z in 𝓝 0, z ∈ A → f z = 0) ∨ ∀ᶠ z in 𝓝 0, z ∈ A → g z = 0
  /-- `I(A) ∩ 𝒪_d = 0`. -/
  base : ∀ h : ComplexModel dim → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) →
    (∀ᶠ z in 𝓝 0, z ∈ A → h (coordinateProjection n dim z) = 0) → ∀ᶠ x in 𝓝 0, h x = 0
  /-- A function on `ℂᵈ`, not identically zero, vanishing on `A ∩ B` for `A ⊄ B`. -/
  exists_eqn_of_not_le : ∀ B : Set (ComplexModel n), IsAnalyticGerm B → ¬ A ≤ᶠ[𝓝 0] B →
    ∃ h : ComplexModel dim → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) ∧
      ¬ (∀ᶠ x in 𝓝 0, h x = 0) ∧
        ∀ᶠ z in 𝓝 0, z ∈ A → z ∈ B → h (coordinateProjection n dim z) = 0

variable {A : Set (ComplexModel n)}

/-- **The parametrizing sets** (blueprint `lag:parametrization-sets`,
`lag:parametrization-regular`): on a polydisc `Δ = polydisc n d r₁ r₂` inside the ball,
fibre coordinates of `A` are small over small base points, the fibres over the complement
of the discriminant locus have exactly `q` points, near each such point `A` is the graph of a
holomorphic section over the base, hence regular of dimension `d`, and the projection is open
on that part. -/
structure SetsData (P : ParametrizationData A) where
  /-- The radius of the inner coordinate polydisc. -/
  r₁ : ℝ
  /-- The radius of the outer coordinate polydisc. -/
  r₂ : ℝ
  r₁_pos : 0 < r₁
  r₂_pos : 0 < r₂
  polydisc_subset : polydisc n P.dim r₁ r₂ ⊆ ball 0 P.rad
  small : ∀ ε > 0, ∃ η > 0, ∀ z ∈ A ∩ polydisc n P.dim r₁ r₂,
    ‖coordinateProjection n P.dim z‖ < η → ∀ k : Fin n, P.dim ≤ k.1 → ‖z k‖ < ε
  finite_fibre : ∀ x : ComplexModel P.dim, ‖x‖ < r₁ → P.disc x ≠ 0 →
    (A ∩ polydisc n P.dim r₁ r₂ ∩ coordinateProjection n P.dim ⁻¹' {x}).Finite
  ncard_fibre : ∀ x : ComplexModel P.dim, ‖x‖ < r₁ → P.disc x ≠ 0 →
    (A ∩ polydisc n P.dim r₁ r₂ ∩ coordinateProjection n P.dim ⁻¹' {x}).ncard = P.deg
  local_graph : ∀ y ∈ A ∩ polydisc n P.dim r₁ r₂, P.disc (coordinateProjection n P.dim y) ≠ 0 →
    ∃ (U : Set (ComplexModel P.dim)) (V : Set (ComplexModel n))
      (g : ComplexModel P.dim → ComplexModel n),
      IsOpen U ∧ IsOpen V ∧ coordinateProjection n P.dim y ∈ U ∧ y ∈ V ∧
      V ⊆ polydisc n P.dim r₁ r₂ ∧ U ⊆ {x | ‖x‖ < r₁ ∧ P.disc x ≠ 0} ∧
      DifferentiableOn ℂ g U ∧ (∀ x ∈ U, coordinateProjection n P.dim (g x) = x) ∧
      (∀ x ∈ U, g x ∈ A ∩ polydisc n P.dim r₁ r₂) ∧
      ∀ z ∈ V, z ∈ A → coordinateProjection n P.dim z ∈ U ∧ g (coordinateProjection n P.dim z) = z
  regular : ∀ y ∈ A ∩ polydisc n P.dim r₁ r₂, P.disc (coordinateProjection n P.dim y) ≠ 0 →
    RegularAtDim (n := n) (M := ComplexModel n) (A ∩ polydisc n P.dim r₁ r₂) y P.dim
  isOpen_image : ∀ O : Set (ComplexModel n), IsOpen O →
    IsOpen (coordinateProjection n P.dim '' (O ∩ (A ∩ polydisc n P.dim r₁ r₂ ∩
      coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0})))

theorem isOpen_polydisc (n d : ℕ) (r₁ r₂ : ℝ) : IsOpen (polydisc n d r₁ r₂) := by
  have h1 : IsOpen {z : ComplexModel n | ‖coordinateProjection n d z‖ < r₁} :=
    isOpen_lt (continuous_norm.comp (coordinateProjection n d).continuous) continuous_const
  have h2 : IsOpen {z : ComplexModel n | ∀ k : Fin n, d ≤ k.1 → ‖z k‖ < r₂} := by
    simp only [ofPred_forall]
    refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun _ => ?_
    exact isOpen_lt (continuous_norm.comp (continuous_apply k |>.comp
      (PiLp.continuous_ofLp 2 _))) continuous_const
  exact h1.inter h2

theorem polydisc_mono {n d : ℕ} {r₁ r₁' r₂ : ℝ} (h : r₁ ≤ r₁') :
    polydisc n d r₁ r₂ ⊆ polydisc n d r₁' r₂ :=
  fun _ hz => ⟨hz.1.trans_le h, hz.2⟩

end

end SGPT.Foundations.Analysis.Pending.GermParametrizationData
