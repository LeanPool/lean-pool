/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Inverse
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Coefficients
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Symmetrization

/-!
# The Poisson iterates of BKL Section 3 in `L²`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 3, (30)–(37): the iterates
`h_{i+1} = α_{i+1} (-L)⁻¹ ∇₀ h_i` built from a function `h₁ = f`, here in `L²(ν)` from the operator
domain of `A = T†T` instead of the class `𝒜`. This module only makes definitions; their
properties (beyond `normSq_nonneg`) are proved in the sibling modules.

## Conventions

* `T : L²(ν) →ₗ.[ℝ] L²(ν; V)` is any linear partial map; the results use the closed unit-weight
  gradient `Tbar` of the heat model, for which `A = Tbar†Tbar = -ℒ`.
* A tensor field with `k` indices is the family of its components, `Field ν k`, indexed by
  `Fin k → Fin n` with `n = finrank ℝ V` and the fixed orthonormal basis `stdOrthonormalBasis ℝ V`.
  Its squared norm `normSq` is the squared Hilbert–Schmidt `L²` norm `Σ_I ‖u_I‖²`.
* Differentiation adds a new **first** index: `(gradField u) (Fin.cons j I) = ∂_j (u I)`.
* The operators are total: `weakGrad`, `gen` and `centeredInv` are `T`, `T†T` and the centered
  inverse of
  `T†T` on their domains and `0` elsewhere, so definitions need no domain proofs. Statements about
  them carry the domain facts as theorems.
* Indices are shifted by one against the source: `iter T f k` is the source's `h_{k+1}`, a field
  with `k` indices, and `scale T (iter T f k)` is `α_{k+2}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A tensor field with `k` indices over `Fin (finrank ℝ V)`, as the family of its components in
`L²(ν)`. -/
abbrev Field (ν : ProbabilityMeasure V) (k : ℕ) : Type _ :=
  (Fin k → Fin (Module.finrank ℝ V)) → Lp ℝ 2 (ν : Measure V)

variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))

/-- The squared Hilbert–Schmidt `L²` norm `Σ_I ‖u_I‖²` of a tensor field. -/
def normSq {k : ℕ} (u : Field ν k) : ℝ :=
  ∑ I, ‖u I‖ ^ 2

/-- The gradient `T u` on the domain of `T`, and `0` elsewhere. -/
def weakGrad (u : Lp ℝ 2 (ν : Measure V)) : Lp V 2 (ν : Measure V) :=
  if h : u ∈ T.domain then T ⟨u, h⟩ else 0

/-- The generator `T†T u` (`= -ℒ u` in the heat model) on its domain, and `0` elsewhere. -/
def gen (u : Lp ℝ 2 (ν : Measure V)) : Lp ℝ 2 (ν : Measure V) :=
  if h : u ∈ (adjointComp T).domain then adjointComp T ⟨u, h⟩ else 0

/-- The weak partial derivative `∂_j u = ⟪e_j, T u⟫` in the standard orthonormal basis. -/
def partialDeriv (j : Fin (Module.finrank ℝ V)) (u : Lp ℝ 2 (ν : Measure V)) :
    Lp ℝ 2 (ν : Measure V) :=
  (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (weakGrad T u)

/-- The centered inverse `(-L)⁻¹ g`: the centered `u ∈ D(T†T)` with `T†T u = g` when one exists
(it is unique when `T` is the closed heat-model gradient), and `0` otherwise. -/
def centeredInv (g : Lp ℝ 2 (ν : Measure V)) : Lp ℝ 2 (ν : Measure V) :=
  if h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g then
    (h.choose : Lp ℝ 2 (ν : Measure V))
  else 0

/-- The gradient `∇u` of a tensor field: a new first index. -/
def gradField {k : ℕ} (u : Field ν k) : Field ν (k + 1) :=
  fun J => partialDeriv T (J 0) (u (Fin.tail J))

/-- The centered gradient `∇₀u = ∇u - ∫ ∇u dν` (BKL (22)), componentwise. -/
def grad0 {k : ℕ} (u : Field ν k) : Field ν (k + 1) :=
  fun J => L2.center ν (gradField T u J)

/-- The generator applied componentwise, `-L u`. -/
def genField {k : ℕ} (u : Field ν k) : Field ν k :=
  fun I => gen T (u I)

/-- The centered inverse applied componentwise, `(-L)⁻¹ g`. -/
def invField {k : ℕ} (g : Field ν k) : Field ν k :=
  fun I => centeredInv T (g I)

/-- The normalizing coefficient `α` of BKL (31) for the step from `h`:
`‖∇₀h‖ / ‖∇(-L)⁻¹∇₀h‖`, and `0` when the denominator vanishes (in particular when `∇₀h = 0`,
the source's linear case). -/
def scale {k : ℕ} (h : Field ν k) : ℝ :=
  if normSq (gradField T (invField T (grad0 T h))) = 0 then 0
  else Real.sqrt (normSq (grad0 T h) / normSq (gradField T (invField T (grad0 T h))))

/-- One step of BKL (30): `h ↦ α (-L)⁻¹ ∇₀ h`. -/
def step {k : ℕ} (h : Field ν k) : Field ν (k + 1) :=
  scale T h • invField T (grad0 T h)

/-- The iterates: `iter T f k` is the source's `h_{k+1}`, with `h₁ = f`. -/
def iter (f : Lp ℝ 2 (ν : Measure V)) : (k : ℕ) → Field ν k
  | 0 => fun _ => f
  | k + 1 => step T (iter f k)

/-- The Dirichlet energy `v = ‖∇h‖²` (BKL (34)). -/
def energy {k : ℕ} (h : Field ν k) : ℝ :=
  normSq (gradField T h)

/-- The energy drop `p = |∫ ∇h dν|²` (BKL (35)), as the sum of the squared means of the
components of `∇h`. -/
def meanGradSq {k : ℕ} (h : Field ν k) : ℝ :=
  ∑ J, L2.mean ν (gradField T h J) ^ 2

/-- The defect `χ = ‖∇²h - α ∇h'‖²` of BKL (37) for `h' = step h` and `α = scale h`. -/
def defect {k : ℕ} (h : Field ν k) : ℝ :=
  normSq (gradField T (gradField T h) - scale T h • gradField T (step T h))

/-- Permuting the index positions of a tensor field: `(permField σ u) I = u (I ∘ σ)`. -/
def permField {k : ℕ} (σ : Equiv.Perm (Fin k)) (u : Field ν k) : Field ν k :=
  fun I => u (I ∘ σ)

/-- `S_q u`: the average of `u` over the permutations of its first `q` index positions. -/
def symField {k : ℕ} (q : ℕ) (u : Field ν k) : Field ν k :=
  ((fixingOutside (slots k 0 q)).card : ℝ)⁻¹ •
    ∑ σ ∈ fixingOutside (slots k 0 q), permField σ u

/-- The Taylor coefficient array `T_d u` of a tensor field (BKL (28), componentwise): the `d`
Taylor indices come first, followed by the `k` indices of `u`; the norm is Hilbert–Schmidt. -/
def taylorField (d : ℕ) {k : ℕ} (u : Field ν k) : Coord (Module.finrank ℝ V) (d + k) :=
  WithLp.toLp 2 fun J =>
    taylorTensor (ν : Measure V) (⇑(u fun i => J (Fin.natAdd d i))) d
      (fun i => stdOrthonormalBasis ℝ V (J (Fin.castAdd k i)))

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `normSq` is nonnegative. -/
theorem normSq_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end FunctionalInequalities.KLS.LogConcave.PoissonIterate
