/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SkewPlaneRestriction
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Orthonormal assembly of a real rotation plane and its complement

All bases below are built from actual orthonormal vectors and the actual
orthogonal decomposition. The reindexing places the new plane at mode
zero and the old modes at successors. No block normal form is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Rotation plane basis. -/
def rotationPlaneBasis {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0) :
    OrthonormalBasis (Fin 2) ℝ (rotationPlane x y) :=
  OrthonormalBasis.mk (orthonormal_span (orthonormal_rotationPair hx hy hxy))
    ((Submodule.span_range_subtype_eq_top_iff (rotationPlane x y)
      (fun i => Submodule.subset_span (Set.mem_range_self i))).mpr rfl).ge

omit [FiniteDimensional ℝ E] in
@[simp] theorem rotationPlaneBasis_apply {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0) (i : Fin 2) :
    (rotationPlaneBasis hx hy hxy i : E) = (![x, y] : Fin 2 → E) i := by
  unfold rotationPlaneBasis
  exact congrArg Subtype.val (congrFun (OrthonormalBasis.coe_mk _ _) i)

/-- Rotation mode equivalence. -/
def rotationModeEquiv (m : ℕ) :
    (Fin (m + 1) × Fin 2) ≃ (Fin 2 ⊕ (Fin m × Fin 2)) where
  toFun p := Fin.cases (Sum.inl p.2) (fun i => Sum.inr (i, p.2)) p.1
  invFun p := Sum.elim (fun a => (0, a)) (fun q => (q.1.succ, q.2)) p
  left_inv := by
    rintro ⟨i, a⟩
    induction i using Fin.cases <;> rfl
  right_inv := by
    intro p
    cases p <;> rfl

@[simp] theorem rotationModeEquiv_zero (m : ℕ) (a : Fin 2) :
    rotationModeEquiv m (0, a) = Sum.inl a := rfl

@[simp] theorem rotationModeEquiv_succ {m : ℕ} (i : Fin m) (a : Fin 2) :
    rotationModeEquiv m (i.succ, a) = Sum.inr (i, a) := rfl

/-- Adjoin rotation basis. -/
def adjoinRotationBasis {m : ℕ} {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    (b : OrthonormalBasis (Fin m × Fin 2) ℝ (rotationPlane x y)ᗮ) :
    OrthonormalBasis (Fin (m + 1) × Fin 2) ℝ E :=
  (((rotationPlaneBasis hx hy hxy).prod b).map
    (rotationPlane x y).orthogonalDecomposition.symm).reindex (rotationModeEquiv m).symm

@[simp] theorem adjoinRotationBasis_zero {m : ℕ} {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    (b : OrthonormalBasis (Fin m × Fin 2) ℝ (rotationPlane x y)ᗮ) (a : Fin 2) :
    adjoinRotationBasis hx hy hxy b (0, a) = (![x, y] : Fin 2 → E) a := by
  simp [adjoinRotationBasis, OrthonormalBasis.reindex_apply,
    OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply]

@[simp] theorem adjoinRotationBasis_succ {m : ℕ} {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    (b : OrthonormalBasis (Fin m × Fin 2) ℝ (rotationPlane x y)ᗮ)
    (i : Fin m) (a : Fin 2) :
    adjoinRotationBasis hx hy hxy b (i.succ, a) = (b (i, a) : E) := by
  simp [adjoinRotationBasis, OrthonormalBasis.reindex_apply,
    OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply]

end VacuumBellSeparation.Gaussian
