/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Perron.Graph
public import LeanPool.StableManifold.Sequence.SuperposeContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of the stable manifold

Let `F x = A x + φ x` be a globally small Lipschitz perturbation (`StableManifold.Perturbation`)
of a linear map with a hyperbolic splitting, on a finite-dimensional real normed space `E`. If `φ`
is `Cⁿ` (`n ≤ ∞`), the map `graph` whose graph is the global stable manifold is `Cⁿ`
(`StableManifold.Perturbation.contDiff_graph`).

The bounded orbits solve `x - perronOp (φ ∘ x) = stableOrbit ξ`. The left side,
`perronSub x = x - perronOp (superpose φ x)`, is a Lipschitz perturbation of the identity of the
Banach space `ℕ →ᵇ E` by a `1/2`-Lipschitz map, hence a homeomorphism (`perronHomeomorph`, from
`ApproximatesLinearOn.toHomeomorph`), and `orbitSeq = perronHomeomorph⁻¹ ∘ stableOrbit`
(`orbitSeq_eq_perronHomeomorph_symm`). The superposition operator is `Cⁿ`
(`StableManifold.contDiff_superpose`), so `perronSub` is `Cⁿ`, with derivative
`1 - perronOp ∘ applySeq (Dφ ∘ x)` of the form `1 - T`, `‖T‖ ≤ 1/2`, invertible. The inverse
function theorem in the form `Homeomorph.contDiff_symm` makes `perronHomeomorph⁻¹` of class `Cⁿ`,
hence `orbitSeq` and `graph = (1 - P) ∘ eval₀ ∘ orbitSeq`. This replaces the fiber contraction
theorem and the `C^r` section theorem of Hirsch, Pugh and Shub: smoothness of every order comes
from the smoothness of the superposition operator on bounded sequences.

## Proofs

* `subsingleton_or_lt_inv_nnnorm_refl`: on a nontrivial space `‖id‖₊ = 1`
  (`ContinuousLinearMap.nnnorm_id`), and `1/2 < 1`.
* `approximatesLinearOn_perronSub`: `perronSub x - perronSub y - (x - y)` is
  `-perronOp (superpose φ x - superpose φ y)`, of norm `≤ S.bound L ‖x - y‖ ≤ ‖x - y‖ / 2`
  (`norm_perronOp_le`, `lipschitzWith_superpose`, `lip_mul_bound_le`).
* `perronHomeomorph`: `ApproximatesLinearOn.toHomeomorph` with the two lemmas above;
  `perronHomeomorph_apply` holds by definition.
* `orbitSeq_eq_perronHomeomorph_symm`: `perronHomeomorph (orbitSeq ξ) = stableOrbit ξ` is the
  fixed point equation `perronMap_orbitSeq`; then `Homeomorph.symm_apply_eq`.
* `norm_perronOp_comp_applySeq_le`: `‖Dφ y‖ ≤ L` (`norm_fderiv_le_of_lipschitz`), so
  `‖superpose (fderiv ℝ φ) x‖ ≤ L` (`superpose_apply_of_bound`,
  `BoundedContinuousFunction.norm_le`), and `‖perronOp ∘L applySeq (…)‖ ≤ S.bound L ≤ 1/2`
  (`ContinuousLinearMap.opNorm_comp_le`, `norm_applySeq_le`).
* `hasFDerivAt_perronSub`: `hasFDerivAt_id`, `hasFDerivAt_superpose` and the chain rule for the
  continuous linear map `perronOp`. `contDiff_perronSub`: `contDiff_id`, `contDiff_superpose`
  and `ContinuousLinearMap.contDiff`.
* `contDiff_orbitSeq`: `orbitSeq = perronHomeomorph.symm ∘ stableOrbit`. For `n = 0` this is
  continuity (`contDiff_zero`). For `n ≠ 0`, `φ` is `C¹`, and at every point the derivative
  `1 - T` of `perronSub` has `‖T‖ ≤ 1/2 < 1`, so it is a unit (`Units.oneSub`), that is, a
  continuous linear equivalence (`ContinuousLinearEquiv.unitsEquiv`); `Homeomorph.contDiff_symm`
  makes `perronHomeomorph.symm` of class `Cⁿ`; compose with the continuous linear map
  `stableOrbit`.
* `contDiff_graph`: `graph = (1 - P) ∘ evalCLM ℝ 0 ∘ orbitSeq`
  (`BoundedContinuousFunction.evalCLM`), compositions with continuous linear maps.
-/

@[expose] public section

open Filter Topology
open scoped NNReal BoundedContinuousFunction

universe u

namespace StableManifold

open BoundedContinuousFunction ContinuousLinearMap

/-- The identity of a normed space approximates itself with any constant `< 1`: the condition of
`ApproximatesLinearOn.toHomeomorph` for `f' = id` and `c = 1/2`. -/
theorem subsingleton_or_lt_inv_nnnorm_refl (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Subsingleton V ∨
      (1 / 2 : ℝ≥0) < ‖((ContinuousLinearEquiv.refl ℝ V).symm : V →L[ℝ] V)‖₊⁻¹ := by
  rcases subsingleton_or_nontrivial V with h | h
  · exact Or.inl h
  · right
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one]
    norm_num

namespace Perturbation

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E →L[ℝ] E} {S : A.HyperbolicSplitting} (F : Perturbation S)

/-- `x ↦ x - perronOp (φ ∘ x)` on bounded sequences: the bounded orbit through `ξ` is the solution
of `perronSub x = stableOrbit ξ`. -/
noncomputable def perronSub (x : ℕ →ᵇ E) : ℕ →ᵇ E :=
  x - S.perronOp (superpose F.φ x)

/-- `perronSub` is a `1/2`-Lipschitz perturbation of the identity. -/
theorem approximatesLinearOn_perronSub :
    ApproximatesLinearOn F.perronSub
      ((ContinuousLinearEquiv.refl ℝ (ℕ →ᵇ E) : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E))) Set.univ (1 / 2) := by
  intro x _ y _
  have h : F.perronSub x - F.perronSub y -
      ((ContinuousLinearEquiv.refl ℝ (ℕ →ᵇ E) : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E))) (x - y) =
      -S.perronOp (superpose F.φ x - superpose F.φ y) := by
    simp only [perronSub, ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply, map_sub]
    abel
  rw [h, norm_neg]
  calc ‖S.perronOp (superpose F.φ x - superpose F.φ y)‖
      ≤ S.bound * ‖superpose F.φ x - superpose F.φ y‖ :=
        (S.perronOp.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right S.norm_perronOp_le (norm_nonneg _))
    _ ≤ S.bound * (F.lip * ‖x - y‖) := mul_le_mul_of_nonneg_left
        ((lipschitzWith_superpose F.lipschitzWith).norm_sub_le x y) S.bound_pos.le
    _ = (F.lip * S.bound) * ‖x - y‖ := by ring
    _ ≤ ((1 / 2 : ℝ≥0) : ℝ) * ‖x - y‖ := by
        gcongr
        simpa using F.lip_mul_bound_le

/-- `perronSub` as a homeomorphism of the space of bounded sequences. -/
noncomputable def perronHomeomorph : (ℕ →ᵇ E) ≃ₜ (ℕ →ᵇ E) :=
  F.approximatesLinearOn_perronSub.toHomeomorph F.perronSub
    (subsingleton_or_lt_inv_nnnorm_refl (ℕ →ᵇ E))

theorem perronHomeomorph_apply (x : ℕ →ᵇ E) : F.perronHomeomorph x = F.perronSub x :=
  rfl

/-- The bounded orbit through `ξ` is `perronHomeomorph⁻¹ (stableOrbit ξ)`. -/
theorem orbitSeq_eq_perronHomeomorph_symm (ξ : E) :
    F.orbitSeq ξ = F.perronHomeomorph.symm (S.stableOrbit ξ) := by
  refine (F.perronHomeomorph.symm_apply_eq.2 ?_).symm
  rw [perronHomeomorph_apply, perronSub, eq_sub_iff_add_eq]
  exact F.perronMap_orbitSeq ξ

/-- `‖perronOp ∘L applySeq (superpose (fderiv ℝ φ) x)‖ ≤ 1/2`: the derivative of `perronSub` is
`1 - T` with `‖T‖ ≤ 1/2`. -/
theorem norm_perronOp_comp_applySeq_le (x : ℕ →ᵇ E) :
    ‖S.perronOp ∘L applySeq (superpose (fderiv ℝ F.φ) x)‖ ≤ 1 / 2 := by
  have hD : ∀ y, ‖fderiv ℝ F.φ y‖ ≤ F.lip := fun y ↦ norm_fderiv_le_of_lipschitz ℝ F.lipschitzWith
  have ha : ‖superpose (fderiv ℝ F.φ) x‖ ≤ F.lip := by
    refine (norm_le F.lip.coe_nonneg).2 fun n ↦ ?_
    rw [superpose_apply_of_bound ⟨F.lip, fun m ↦ hD (x m)⟩]
    exact hD (x n)
  calc ‖S.perronOp ∘L applySeq (superpose (fderiv ℝ F.φ) x)‖
      ≤ ‖S.perronOp‖ * ‖applySeq (superpose (fderiv ℝ F.φ) x)‖ := opNorm_comp_le _ _
    _ ≤ S.bound * F.lip := mul_le_mul S.norm_perronOp_le ((norm_applySeq_le _).trans ha)
        (norm_nonneg _) S.bound_pos.le
    _ ≤ 1 / 2 := by linarith [F.lip_mul_bound_le]

/-- The derivative of `perronSub`. -/
theorem hasFDerivAt_perronSub (hφ : ContDiff ℝ 1 F.φ) (x : ℕ →ᵇ E) :
    HasFDerivAt F.perronSub (1 - S.perronOp ∘L applySeq (superpose (fderiv ℝ F.φ) x)) x :=
  (hasFDerivAt_id x).sub (S.perronOp.hasFDerivAt.comp x (hasFDerivAt_superpose hφ x))

theorem contDiff_perronSub {n : ℕ∞} (hφ : ContDiff ℝ n F.φ) : ContDiff ℝ n F.perronSub :=
  contDiff_id.sub (S.perronOp.contDiff.comp (contDiff_superpose hφ))

/-- **The bounded orbits depend `Cⁿ` on the stable component.**

Proof: `Homeomorph.contDiff_symm` for `perronHomeomorph`, whose derivative `1 - T`, `‖T‖ ≤ 1/2`,
is invertible everywhere (`Units.oneSub`); continuity for `n = 0`. -/
theorem contDiff_orbitSeq {n : ℕ∞} (hφ : ContDiff ℝ n F.φ) : ContDiff ℝ n F.orbitSeq := by
  have h : F.orbitSeq = F.perronHomeomorph.symm ∘ S.stableOrbit :=
    funext F.orbitSeq_eq_perronHomeomorph_symm
  rw [h]
  rcases eq_or_ne n 0 with rfl | hn
  · exact contDiff_zero.2 (F.perronHomeomorph.symm.continuous.comp S.stableOrbit.continuous)
  have h1 : ContDiff ℝ 1 F.φ := hφ.of_le (by exact_mod_cast Order.one_le_iff_ne_zero.2 hn)
  have hT : ∀ x, ‖S.perronOp ∘L applySeq (superpose (fderiv ℝ F.φ) x)‖ < 1 := fun x ↦
    (F.norm_perronOp_comp_applySeq_le x).trans_lt (by norm_num)
  refine (F.perronHomeomorph.contDiff_symm
    (f₀' := fun x ↦ ContinuousLinearEquiv.unitsEquiv ℝ _ (Units.oneSub _ (hT x)))
    (fun x ↦ ?_) (F.contDiff_perronSub hφ)).comp S.stableOrbit.contDiff
  exact F.hasFDerivAt_perronSub h1 x

/-- **The stable manifold is `Cⁿ`**: if `φ` is `Cⁿ` (`n ≤ ∞`), so is `graph`.

Proof: `graph = (1 - P) ∘ evalCLM ℝ 0 ∘ orbitSeq` and `contDiff_orbitSeq`. -/
theorem contDiff_graph {n : ℕ∞} (hφ : ContDiff ℝ n F.φ) : ContDiff ℝ n F.graph := by
  have h : ContDiff ℝ n (evalCLM ℝ 0 ∘ F.orbitSeq) :=
    (evalCLM ℝ 0 : (ℕ →ᵇ E) →L[ℝ] E).contDiff.comp (F.contDiff_orbitSeq hφ)
  exact (1 - S.proj).contDiff.comp h

end Perturbation

end StableManifold
