/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.SecondOrder.HessianIncrement
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Mollification
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Approximation
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Positivity

/-!
# Weak third derivative and compact-local Hessian bounds

For a weak `C^{1,1}` Monge–Ampère potential `u` (supports for Letwin arXiv:2607.24164v1 Theorem
2.5):

* `exists_weak_third_derivative_on_range`, `exists_weak_third_derivative`: for `C¹` convex `u` with
  Lipschitz gradient,
  `C¹` `V` convex on a set containing every gradient value (respectively on all of space), Lipschitz
  exponent
  `−u + V(∇u)`, almost-everywhere positive definite Hessian with `log det ∇²u = −u + V(∇u)` and `∇²u
  ≤ K·Id` (`K > 0`),
  and the centered-difference bound `u(x+h) + u(x−h) − 2u(x) ≤ D‖h‖²`, every entry of `∇²u` has a
  weak derivative along
  every coordinate direction that is in `L²` on every compact set, i.e. `∇²u ∈ H¹_loc`;
* `ae_posSemidef_hessianMatrix_sub_of_log_det`: if a.e. `∇²u` is positive definite with `log det ∇²u
  = g` for a continuous
  `g` and `∇²u ≤ K·Id` (`K > 0`, positive dimension), then on every compact `S` there is `δ > 0`
  with `∇²u ≥ δ·Id` a.e.
  on `S`;
* `exists_compact_inverse_hessian_coefficient_bounds`: under the same data and continuity of `u`,
  compact-local constants
  `c₀, c₁ > 0` with `c₀·Id ≤ e^{−u} (∇²u)⁻¹ ≤ c₁·Id` a.e. on every compact `S`.

The integrated Hessian-increment energy behind the weak third derivative is in
`Analysis/Convex/SecondOrder/HessianIncrement.lean`.
-/

@[expose] public section

section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/--
**The Hessian of the `C^{1,1}` Monge–Ampère solution is in `H¹_loc`, convexity on the gradient
range**: as `exists_weak_third_derivative`, with `V` convex only on a set `Ω` containing every
gradient value `∇u x`. -/
theorem exists_weak_third_derivative_on_range {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hVc : ConvexOn ℝ Ω V) (hΩ : ∀ x, gradient u x ∈ Ω)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ}
    (hK : 0 < K)
    (hdata :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
          Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
            (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ,
      ∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hex :
    ∀ k i j : Fin n,
      ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) g
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro k i j
    refine
      exists_hasWeakDerivAlong_of_forall_cutoff
        (fun S hS => memLp_hessianMatrix_entry_of_isCompact hG i j hS)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ?_
    intro χ hχ hχc
    obtain ⟨C, _hC, hdiff⟩ :=
      exists_hessian_cutoff_sq_difference_bound_on_range hu hconv hG hV hVc hΩ hF hK hdata hw hχ
        hχc i j (EuclideanSpace.basisFun (Fin n) ℝ k)
    exact
      exists_hasWeakDerivAlong_of_sq_difference_le
        (memLp_cutoff_mul_hessianMatrix_entry hG i j hχ.continuous hχc)
        (EuclideanSpace.basisFun (Fin n) ℝ k) (C := C) hdiff
  refine ⟨fun x k i j => Classical.choose (hex k i j) x, ?_⟩
  intro k i j
  exact Classical.choose_spec (hex k i j)


/-- **The Hessian of the `C^{1,1}` Monge–Ampère solution is in `H¹_loc`**: every entry of `∇²u` has
a weak derivative along every coordinate direction, locally in
`L²`. -/
theorem exists_weak_third_derivative {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ, ∀ k i j,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
  exists_weak_third_derivative_on_range hu hconv hG hV hVc (fun x => mem_univ (gradient u x))
    hF hK hdata hw

/--
**Compact-local Hessian floor from log-determinant data**: if a.e. `∇²u` is positive definite with
`log det ∇²u = g` for a continuous `g` and `∇²u ≤ K·Id` (`K > 0`, positive dimension), then on every
compact `S` there is
`δ > 0` with `∇²u ≥ δ·Id` a.e. on `S`; `δ = exp(min_S g) / K^(n-1)` (empty `S` trivial). -/
theorem ae_posSemidef_hessianMatrix_sub_of_log_det {n : ℕ} (hn : 0 < n)
    {u g : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ} (hK : 0 < K) (hg : Continuous g)
    (hdata :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
          Real.log (hessianMatrix u x).det = g x ∧
            (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (hessianMatrix u x - δ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    let D : ℝ := Real.exp (g x₀)
    have hD : 0 < D := Real.exp_pos _
    refine ⟨D / K ^ (n - 1), div_pos hD (pow_pos hK _), ?_⟩
    filter_upwards [ae_restrict_of_ae hdata, ae_restrict_mem hS.measurableSet] with x hx hxS
    have hdet : D ≤ (hessianMatrix u x).det := by
      have he : Real.exp (g x) = (hessianMatrix u x).det := by
        rw [← hx.2.1, Real.exp_log hx.1.det_pos]
      rw [← he]
      exact Real.exp_le_exp.mpr (hmin hxS)
    exact posSemidef_sub_scalar_of_det_lower hn hx.1.posSemidef hK hD hx.2.2 hdet
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, zero_lt_one, ?_⟩
    simp [hempty]

end FunctionalInequalities.Analysis

section CompactInverseHessianCoefficient

open Matrix MeasureTheory Set
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/--
Weighted reciprocal bounds: `ρ A⁻¹` lies between `(r₀/β)·Id` and `(r₁/α)·Id` for `ρ ∈ [r₀, r₁]`, `ρ
≥ 0`. -/
private theorem weighted_inverse_posSemidef_bounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {α β ρ r₀ r₁ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hlower : (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hupper : (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) (hρ : 0 ≤ ρ) (h₀ : r₀ ≤ ρ)
    (h₁ : ρ ≤ r₁) :
    (ρ • A⁻¹ - (r₀ / β) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((r₁ / α) • (1 : Matrix (Fin n) (Fin n) ℝ) - ρ • A⁻¹).PosSemidef := by
  classical
  obtain ⟨hlo, hup⟩ := inverse_posSemidef_bounds hA hα hβ hlower hupper
  constructor
  · have h :=
      (hlo.smul hρ).add
        ((show (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef from Matrix.PosSemidef.one).smul
          (mul_nonneg (sub_nonneg.mpr h₀) (inv_nonneg.mpr hβ.le)))
    convert h using 1
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      div_eq_mul_inv]
    ring
  · have h :=
      (hup.smul hρ).add
        ((show (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef from Matrix.PosSemidef.one).smul
          (mul_nonneg (sub_nonneg.mpr h₁) (inv_nonneg.mpr hα.le)))
    convert h using 1
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      div_eq_mul_inv]
    ring

/--
**Compact-local bounds for the weighted inverse Hessian coefficient** (given `u`): if `u` is
continuous and a.e. `∇²u` is
positive definite with `log det ∇²u = g` for a continuous `g` and `∇²u ≤ K·Id` (`K > 0`, positive
dimension), then on every
compact `S` there are `c₀, c₁ > 0` with `c₀·Id ≤ e^{-u} (∇²u)⁻¹ ≤ c₁·Id` a.e. on `S`. For nonempty
`S`,
`c₀ = min_S e^{-u} / K` and `c₁ = max_S e^{-u} / δ_S` with `δ_S` the compact-local Hessian floor;
for empty `S` the constants
are `1`. -/
theorem exists_compact_inverse_hessian_coefficient_bounds {n : ℕ} (hn : 0 < n)
    {u g : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ} (hu : Continuous u) (hg : Continuous g)
    (hK : 0 < K)
    (hdata :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
          Real.log (hessianMatrix u x).det = g x ∧
            (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) :
    ∃ c₀ c₁ : ℝ,
      0 < c₀ ∧
        0 < c₁ ∧
          ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
            (Real.exp (-u x) • (hessianMatrix u x)⁻¹ -
                  c₀ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
              (c₁ • (1 : Matrix (Fin n) (Fin n) ℝ) -
                  Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨δ, hδ, hfloor⟩ := ae_posSemidef_hessianMatrix_sub_of_log_det hn hK hg hdata hS
    have hρ : Continuous (fun x => Real.exp (-u x)) := Real.continuous_exp.comp hu.neg
    obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hρ.continuousOn
    obtain ⟨x₁, hx₁, hmax⟩ := hS.exists_isMaxOn hne hρ.continuousOn
    refine
      ⟨Real.exp (-u x₀) / K, Real.exp (-u x₁) / δ, div_pos (Real.exp_pos _) hK,
        div_pos (Real.exp_pos _) hδ, ?_⟩
    filter_upwards [ae_restrict_of_ae hdata, hfloor, ae_restrict_mem hS.measurableSet] with x hx
      hfx hxS
    exact
      weighted_inverse_posSemidef_bounds hx.1 hδ hK hfx hx.2.2 (Real.exp_pos _).le (hmin hxS)
        (hmax hxS)
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    simp [he]

end FunctionalInequalities.Analysis

end CompactInverseHessianCoefficient
