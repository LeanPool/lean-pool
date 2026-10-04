/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Fredholm.Fredholm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic


/-!
# Rellich-Kondrachov reduction from the compact embedding to a compact `opK`

The Fredholm alternative of `Fredholm.lean` is conditioned on the abstract hypothesis
`IsCompactOperator (opK)`. This file traces that hypothesis to its single analytic source: the
**Rellich-Kondrachov compact embedding** `H₀¹(Ω) ↪ L²(Ω)`, encoded as the coordinate-`0` map
`embL2 Ω : H₀¹(Ω) →L[ℝ] L²(Ω)`.

* `embL2 Ω`: the embedding `U ↦ U 0`, the composition of the submodule inclusion with the
  `PiLp` projection onto coordinate `0`.
* `opT_eq_adjoint_comp`: the `L²` form operator factors as `opT = (embL2)† ∘ embL2`, because
  `⟪opT U, V⟫ = ⟪U₀, V₀⟫_{L²} = ⟪embL2 U, embL2 V⟫`.
* `opT_isCompact` / `opK_isCompact`: given `IsCompactOperator (embL2 Ω)`, both `opT` and
  `opK = γ·opE⁻¹·opT` are compact, by composing the compact embedding with bounded operators.
* `fredholm_alternative_rellich` / `fredholm_unique_imp_exists_rellich`: the Fredholm theorems
  re-stated to take the single hypothesis `IsCompactOperator (embL2 Ω)` in place of
  the opaque operator-level `IsCompactOperator (opK)`. The compact embedding for bounded `Ω` is
  the one analytic input (Rellich-Kondrachov), threaded as a hypothesis exactly as the Poincaré
  geometry input was, and deliberately not discharged here.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-- The coordinate-`0` embedding `H₀¹(Ω) ↪ L²(Ω)`, `U ↦ U 0`, as a continuous linear map:
the `PiLp` projection onto coordinate `0` precomposed with the submodule inclusion. -/
def embL2 (Ω : Set (EuclideanSpace ℝ (Fin d))) : H01 Ω →L[ℝ] L2D Ω :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) (0 : Fin (d + 1))).comp (H01 Ω).subtypeL

/-- Simp lemma: `embL2 Ω U = (U : H1amb Ω) 0`, the function coordinate of `U`. -/
@[simp] lemma embL2_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H01 Ω) :
    embL2 Ω U = (U : H1amb Ω) 0 := by
  simp only [embL2, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, PiLp.proj_apply]

/-- **Factorisation of the `L²` form through the embedding**: `opT = (embL2)† ∘ embL2`. Indeed
`⟪opT U, V⟫ = ⟪U₀, V₀⟫_{L²} = ⟪embL2 U, embL2 V⟫ = ⟪(embL2)† (embL2 U), V⟫`. -/
lemma opT_eq_adjoint_comp (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    FullEllipticOp.opT Ω = (embL2 Ω).adjoint.comp (embL2 Ω) := by
  refine ContinuousLinearMap.ext (fun U => ext_inner_right (𝕜 := ℝ) (fun V => ?_))
  rw [FullEllipticOp.inner_opT, FullEllipticOp.zerothForm_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    embL2_apply, embL2_apply]

/-- Given the Rellich compact embedding, the `L²` form operator `opT` is compact: it is the
compact `embL2` postcomposed with the bounded `(embL2)†`. -/
lemma opT_isCompact (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hRellich : IsCompactOperator (embL2 Ω)) :
    IsCompactOperator (FullEllipticOp.opT Ω) := by
  rw [opT_eq_adjoint_comp]
  exact hRellich.clm_comp (embL2 Ω).adjoint

namespace FullEllipticOp

variable (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- Given the Rellich compact embedding, the reduction operator `opK = γ·opE⁻¹·opT` is compact:
`opT` is compact and `opK` postcomposes it with the bounded `opE⁻¹` and scales it. -/
lemma opK_isCompact (hRellich : IsCompactOperator (embL2 Ω)) :
    IsCompactOperator (Op.opK Ω) := by
  have hT : IsCompactOperator (FullEllipticOp.opT Ω) := opT_isCompact Ω hRellich
  exact (hT.clm_comp ((Op.opE Ω).symm : H01 Ω →L[ℝ] H01 Ω)).smul Op.gardingγ

/-- **Fredholm alternative on the Rellich embedding hypothesis** (Evans §6.2.3,
Theorem 4). Identical to
`fredholm_alternative`, but conditioned on the single analytic input `IsCompactOperator (embL2 Ω)`
(the Rellich-Kondrachov compact embedding for bounded `Ω`) rather than the opaque
`IsCompactOperator (opK)`: either `Lu = 0` has a nontrivial weak solution, or `Lu = f` has a
unique weak solution for every `f`. -/
theorem fredholm_alternative_rellich (hRellich : IsCompactOperator (embL2 Ω)) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) :=
  Op.fredholm_alternative Ω (Op.opK_isCompact Ω hRellich)

/-- **Fredholm corollary on the Rellich embedding hypothesis**: if the homogeneous problem
`Lu = 0` has only the trivial weak solution, then `Lu = f` has a unique weak solution for every
`f`, assuming the Rellich-Kondrachov compact embedding. -/
theorem fredholm_unique_imp_exists_rellich (hRellich : IsCompactOperator (embL2 Ω))
    (huniq : ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = 0) → u = 0)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v :=
  Op.fredholm_unique_imp_exists Ω (Op.opK_isCompact Ω hRellich) huniq f

end FullEllipticOp

end EllipticPdes.Sobolev
