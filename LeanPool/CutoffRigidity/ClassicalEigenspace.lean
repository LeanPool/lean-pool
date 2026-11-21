/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EigenfunctionC2Rigidity
public import LeanPool.CutoffRigidity.AffineEigenspace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Actual classical L² eigenspaces and their unique continuous representatives

The subspace consists of actual Gibbs L² classes admitting a C² solution of
the original pointwise eigenfunction PDE. Its canonical representative is
unique by full support. Identification with a self-adjoint generator domain
and spectral-gap attainment are separate statements.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Linearity of actual coordinate derivatives on differentiable functions. -/
theorem coordinateDerivative_add_classical {f g : E → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin d) :
    coordinateDerivative i (fun x => f x + g x) =
      fun x => coordinateDerivative i f x + coordinateDerivative i g x := by
  ext x
  simp only [coordinateDerivative, fderiv_fun_add (hf x) (hg x), add_apply]

/-- Scalar linearity of actual coordinate derivatives. -/
theorem coordinateDerivative_smul_classical {f : E → ℝ}
    (hf : Differentiable ℝ f) (r : ℝ) (i : Fin d) :
    coordinateDerivative i (fun x => r * f x) = fun x => r * coordinateDerivative i f x := by
  ext x
  simp only [coordinateDerivative, fderiv_const_mul (hf x), smul_apply, smul_eq_mul]

/-- The actual pointwise Langevin differential expression is additive. -/
theorem langevinDifferentialOperator_add_classical (V : E → ℝ) {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    langevinDifferentialOperator V (fun y => f y + g y) x =
      langevinDifferentialOperator V f x + langevinDifferentialOperator V g x := by
  have hf' := hf.differentiable (by norm_num)
  have hg' := hg.differentiable (by norm_num)
  have hDf (i : Fin d) := (c1_coordinateDerivative_of_c2 hf i).differentiable (by norm_num)
  have hDg (i : Fin d) := (c1_coordinateDerivative_of_c2 hg i).differentiable (by norm_num)
  have hG : gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => f y + g y) x) = _
    rw [fderiv_fun_add (hf' x) (hg' x), map_add]
    rfl
  simp only [langevinDifferentialOperator, hG, inner_add_right]
  change (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i (fun y => f y + g y)) x) - _ =
    ((∑ i : Fin d, coordinateDerivative i (coordinateDerivative i f) x) - _) +
      ((∑ i : Fin d, coordinateDerivative i (coordinateDerivative i g) x) - _)
  simp_rw [coordinateDerivative_add_classical hf' hg',
    coordinateDerivative_add_classical (hDf _) (hDg _)]
  rw [Finset.sum_add_distrib]
  ring

/-- The actual pointwise Langevin differential expression is scalar linear. -/
theorem langevinDifferentialOperator_smul_classical (V : E → ℝ) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (r : ℝ) (x : E) :
    langevinDifferentialOperator V (fun y => r * f y) x = r * langevinDifferentialOperator V f x
      := by
  have hf' := hf.differentiable (by norm_num)
  have hDf (i : Fin d) := (c1_coordinateDerivative_of_c2 hf i).differentiable (by norm_num)
  have hG : gradient (fun y => r * f y) x = r • gradient f x := by
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => r * f y) x) = _
    rw [fderiv_const_mul (hf' x), map_smul]
    rfl
  simp only [langevinDifferentialOperator, hG, inner_smul_right]
  change (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i (fun y => r * f y)) x) - _ =
    r * ((∑ i : Fin d, coordinateDerivative i (coordinateDerivative i f) x) - _)
  simp_rw [coordinateDerivative_smul_classical hf' r,
    coordinateDerivative_smul_classical (hDf _) r]
  rw [← Finset.mul_sum]
  ring

/-- Actual L² classes that admit a C² representative satisfying the original PDE. -/
@[expose] noncomputable def classicalL2Eigenspace (V : E → ℝ) (ρ : ℝ) :
    Submodule ℝ (E →₂[gibbsMeasure volume V] ℝ) where
  carrier := {u | ∃ f : E → ℝ, ContDiff ℝ 2 f ∧
    (∀ x, langevinDifferentialOperator V f x = -ρ * f x) ∧ f =ᵐ[gibbsMeasure volume V] u}
  zero_mem' := by
    refine ⟨fun _ => 0, contDiff_const, ?_, ?_⟩
    · intro x
      simp [langevinDifferentialOperator, euclideanLaplacian, gradient]
    · exact (Lp.coeFn_zero _ _ _).symm
  add_mem' := by
    rintro u v ⟨f, hf, hef, haef⟩ ⟨g, hg, heg, haeg⟩
    refine ⟨fun x => f x + g x, hf.add hg, ?_, ?_⟩
    · intro x
      rw [langevinDifferentialOperator_add_classical V hf hg, hef, heg]
      ring
    · filter_upwards [haef, haeg, Lp.coeFn_add u v] with x hx hy hxy
      simpa only [Pi.add_apply] using (hx ▸ hy ▸ hxy.symm)
  smul_mem' := by
    rintro r u ⟨f, hf, hef, haef⟩
    refine ⟨fun x => r * f x, contDiff_const.mul hf, ?_, ?_⟩
    · intro x
      rw [langevinDifferentialOperator_smul_classical V hf, hef]
      ring
    · filter_upwards [haef, Lp.coeFn_smul r u] with x hx hxy
      simpa only [Pi.smul_apply, smul_eq_mul] using (hx ▸ hxy.symm)

/-- The actual representative, chosen from the defining existence assertion. -/
@[expose] noncomputable def classicalEigenRepresentative (V : E → ℝ) (ρ : ℝ)
    (u : classicalL2Eigenspace V ρ) : E → ℝ := Classical.choose u.property

theorem classicalEigenRepresentative_spec (V : E → ℝ) (ρ : ℝ)
    (u : classicalL2Eigenspace V ρ) :
    ContDiff ℝ 2 (classicalEigenRepresentative V ρ u) ∧
      (∀ x, langevinDifferentialOperator V (classicalEigenRepresentative V ρ u) x =
        -ρ * classicalEigenRepresentative V ρ u x) ∧
      classicalEigenRepresentative V ρ u =ᵐ[gibbsMeasure volume V] (u : E →₂[gibbsMeasure volume V]
        ℝ) :=
  Classical.choose_spec u.property

/-- Full support makes the continuous representative unique everywhere. -/
theorem classicalEigenRepresentative_unique {V f : E → ℝ} (hV : Continuous V) (ρ : ℝ)
    (u : classicalL2Eigenspace V ρ) (hf : Continuous f)
    (hae : f =ᵐ[gibbsMeasure volume V] (u : E →₂[gibbsMeasure volume V] ℝ)) :
    f = classicalEigenRepresentative V ρ u := by
  exact gibbsMeasure_eq_of_ae_eq volume hV.measurable hf
    (classicalEigenRepresentative_spec V ρ u).1.continuous
    (hae.trans (classicalEigenRepresentative_spec V ρ u).2.2.symm)

/-- The canonical representative really belongs to the actual Gibbs L² space. -/
theorem classicalEigenRepresentative_memLp (V : E → ℝ) (ρ : ℝ)
    (u : classicalL2Eigenspace V ρ) :
    MemLp (classicalEigenRepresentative V ρ u) 2 (gibbsMeasure volume V) := by
  have h : MemLp (u : E →₂[gibbsMeasure volume V] ℝ) 2 (gibbsMeasure volume V) := Lp.memLp _
  exact (memLp_congr_ae (classicalEigenRepresentative_spec V ρ u).2.2).mpr h

/-- Full support makes the representative selection linear as actual functions. -/
@[expose] noncomputable def classicalEigenRepresentativeLinear (V : E → ℝ)
    (hV : Continuous V) (ρ : ℝ) : classicalL2Eigenspace V ρ →ₗ[ℝ] (E → ℝ) where
  toFun := classicalEigenRepresentative V ρ
  map_add' := by
    intro u v
    apply Eq.symm
    apply classicalEigenRepresentative_unique hV ρ (u + v)
    · exact (classicalEigenRepresentative_spec V ρ u).1.continuous.add
        (classicalEigenRepresentative_spec V ρ v).1.continuous
    · filter_upwards [(classicalEigenRepresentative_spec V ρ u).2.2,
        (classicalEigenRepresentative_spec V ρ v).2.2,
        Lp.coeFn_add (u : E →₂[gibbsMeasure volume V] ℝ) v] with x hx hy hxy
      simpa only [Pi.add_apply] using (hx ▸ hy ▸ hxy.symm)
  map_smul' := by
    intro r u
    apply Eq.symm
    apply classicalEigenRepresentative_unique hV ρ (r • u)
    · exact continuous_const.mul (classicalEigenRepresentative_spec V ρ u).1.continuous
    · filter_upwards [(classicalEigenRepresentative_spec V ρ u).2.2,
        Lp.coeFn_smul r (u : E →₂[gibbsMeasure volume V] ℝ)] with x hx hxy
      simpa only [Pi.smul_apply, smul_eq_mul] using (hx ▸ hxy.symm)

/-- Evaluation of the unique continuous representative is a genuine linear functional. -/
@[expose] noncomputable def classicalEigenEvaluation (V : E → ℝ)
    (hV : Continuous V) (ρ : ℝ) (x : E) : classicalL2Eigenspace V ρ →ₗ[ℝ] ℝ :=
  (LinearMap.proj x).comp (classicalEigenRepresentativeLinear V hV ρ)

/-- Actual gradients of the unique representatives define a linear coefficient map. -/
@[expose] noncomputable def classicalEigenGradient (V : E → ℝ)
    (hV : Continuous V) (ρ : ℝ) : classicalL2Eigenspace V ρ →ₗ[ℝ] E where
  toFun := fun u => gradient (classicalEigenRepresentative V ρ u) 0
  map_add' := by
    intro u v
    have hrep := (classicalEigenRepresentativeLinear V hV ρ).map_add u v
    change classicalEigenRepresentative V ρ (u + v) =
      classicalEigenRepresentative V ρ u + classicalEigenRepresentative V ρ v at hrep
    rw [hrep]
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ
      (classicalEigenRepresentative V ρ u + classicalEigenRepresentative V ρ v) 0) = _
    rw [fderiv_add ((classicalEigenRepresentative_spec V ρ u).1.differentiable (by norm_num) 0)
      ((classicalEigenRepresentative_spec V ρ v).1.differentiable (by norm_num) 0), map_add]
    rfl
  map_smul' := by
    intro r u
    have hrep := (classicalEigenRepresentativeLinear V hV ρ).map_smul r u
    change classicalEigenRepresentative V ρ (r • u) = r • classicalEigenRepresentative V ρ u at hrep
    rw [hrep]
    change (InnerProductSpace.toDual ℝ E).symm
      (fderiv ℝ (r • classicalEigenRepresentative V ρ u) 0) = _
    rw [fderiv_const_smul ((classicalEigenRepresentative_spec V ρ u).1.differentiable
      (by norm_num) 0),
      map_smul]
    rfl

/-- C² curvature rigidity applies to the actual unique representative. -/
theorem classicalEigenRepresentative_affine {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : classicalL2Eigenspace V ρ) (x : E) :
    classicalEigenRepresentative V ρ u x = classicalEigenRepresentative V ρ u 0 +
      inner ℝ (classicalEigenGradient V hV.continuous ρ u) x :=
  c2_L2_eigenfunction_is_affine hV (classicalEigenRepresentative_spec V ρ u).1
    (classicalEigenRepresentative_memLp V ρ u) ρ hρ hHess
    (classicalEigenRepresentative_spec V ρ u).2.1 x

/-- At a positive curvature eigenvalue, the actual L² class is determined
by its gradient coefficient. -/
theorem classicalEigenGradient_injective {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Function.Injective (classicalEigenGradient V hV.continuous ρ) := by
  apply (classicalEigenGradient V hV.continuous ρ).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  have hgrad : classicalEigenGradient V hV.continuous ρ u = 0 := hu
  have hc (x : E) : classicalEigenRepresentative V ρ u x = classicalEigenRepresentative V ρ u 0
    := by
    rw [classicalEigenRepresentative_affine hV ρ hρ.le hHess u x, hgrad]
    simp
  have heigen := (classicalEigenRepresentative_spec V ρ u).2.1 0
  rw [funext hc] at heigen
  simp [langevinDifferentialOperator, euclideanLaplacian, gradient] at heigen
  have hzero : classicalEigenRepresentative V ρ u 0 = 0 := heigen.resolve_left hρ.ne'
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(classicalEigenRepresentative_spec V ρ u).2.2,
    Lp.coeFn_zero ℝ 2 (gibbsMeasure volume V)] with x hx hz
  rw [← hx, hc x, hzero]
  exact hz.symm

/-- The actual classical eigenspace is finite dimensional, by its injective
coefficient map into the ambient Euclidean space. -/
theorem classicalL2Eigenspace_finiteDimensional {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    FiniteDimensional ℝ (classicalL2Eigenspace V ρ) :=
  FiniteDimensional.of_injective (classicalEigenGradient V hV.continuous ρ)
    (classicalEigenGradient_injective hV ρ hρ hHess)

/-- Evaluation is continuous for the actual L² norm on the classical eigenspace. -/
@[expose] noncomputable def classicalEigenEvaluationCLM {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) : classicalL2Eigenspace V ρ →L[ℝ] ℝ := by
  letI := classicalL2Eigenspace_finiteDimensional hV ρ hρ hHess
  exact (classicalEigenEvaluation V hV.continuous ρ x).toContinuousLinearMap

/-- The actual classical eigenspace has dimension at most the state dimension. -/
theorem classicalL2Eigenspace_finrank_le {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Module.finrank ℝ (classicalL2Eigenspace V ρ) ≤ d := by
  simpa using (LinearMap.finrank_le_finrank_of_injective
    (classicalEigenGradient_injective hV ρ hρ hHess))

/-- The gradient row and constant of the canonical representative satisfy
the actual affine eigenfunction constraints. -/
theorem classicalEigenRepresentative_coefficients {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : classicalL2Eigenspace V ρ) :
    classicalEigenGradient V hV.continuous ρ u ∈ affineEigenRows V ρ ∧
      classicalEigenRepresentative V ρ u 0 =
        affineEigenConstant V ρ (classicalEigenGradient V hV.continuous ρ u) := by
  apply (affineEigenRows_iff_eigenfunction V hρ _ _).mp
  have hrep : classicalEigenRepresentative V ρ u = fun x =>
      inner ℝ (classicalEigenGradient V hV.continuous ρ u) x +
        classicalEigenRepresentative V ρ u 0 := by
    ext x
    rw [classicalEigenRepresentative_affine hV ρ hρ.le hHess]
    ring
  intro x
  calc
    _ = langevinDifferentialOperator V (classicalEigenRepresentative V ρ u) x :=
      congrArg (fun F => langevinDifferentialOperator V F x) hrep.symm
    _ = -ρ * classicalEigenRepresentative V ρ u x :=
      (classicalEigenRepresentative_spec V ρ u).2.1 x
    _ = _ := by rw [classicalEigenRepresentative_affine hV ρ hρ.le hHess]; ring

/-- The actual coefficient map lands in precisely the affine row submodule. -/
@[expose] noncomputable def classicalEigenToRows {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    classicalL2Eigenspace V ρ →ₗ[ℝ] affineEigenRows V ρ :=
  (classicalEigenGradient V hV.continuous ρ).codRestrict (affineEigenRows V ρ)
    (fun u => (classicalEigenRepresentative_coefficients hV ρ hρ hHess u).1)

/-- Every actual affine row is attained by an actual Gibbs L² class. -/
theorem classicalEigenToRows_bijective {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Function.Bijective (classicalEigenToRows hV ρ hρ hHess) := by
  constructor
  · intro u v huv
    exact classicalEigenGradient_injective hV ρ hρ hHess (congrArg Subtype.val huv)
  · intro a
    let f : E → ℝ := fun x => inner ℝ (a : E) x + affineEigenConstant V ρ a
    have hf : ContDiff ℝ 2 f :=
      ((InnerProductSpace.toDual ℝ E) (a : E)).contDiff.add contDiff_const
    have heig := affineEigenRows_eigenfunction V hρ a
    have hLp : MemLp f 2 (gibbsMeasure volume V) :=
      affine_eigenfunction_memLp_all V (hV.differentiable (by norm_num)) _ _ ρ hρ heig hprob
    let u : classicalL2Eigenspace V ρ := ⟨hLp.toLp f, f, hf, heig, hLp.coeFn_toLp.symm⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    change gradient (classicalEigenRepresentative V ρ u) 0 = (a : E)
    have hrep : f = classicalEigenRepresentative V ρ u :=
      classicalEigenRepresentative_unique hV.continuous ρ u hf.continuous hLp.coeFn_toLp.symm
    rw [← hrep]
    exact gradient_inner_add_const _ _ _

/-- An exact linear equivalence between the actual classical L² eigenspace
and the actual affine row submodule. No generator-domain identification is assumed. -/
@[expose] noncomputable def classicalEigenRowsEquiv {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    classicalL2Eigenspace V ρ ≃ₗ[ℝ] affineEigenRows V ρ :=
  LinearEquiv.ofBijective (classicalEigenToRows hV ρ hρ hHess)
    (classicalEigenToRows_bijective hV ρ hρ hHess hprob)

/-- The actual canonical representative is the affine eigenfunction of its row. -/
theorem classicalEigenRepresentative_eq_row {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : classicalL2Eigenspace V ρ) (x : E) :
    classicalEigenRepresentative V ρ u x =
      inner ℝ (classicalEigenToRows hV ρ hρ hHess u : E) x +
        affineEigenConstant V ρ (classicalEigenToRows hV ρ hρ hHess u) := by
  rw [classicalEigenRepresentative_affine hV ρ hρ.le hHess,
    (classicalEigenRepresentative_coefficients hV ρ hρ hHess u).2]
  change affineEigenConstant V ρ (classicalEigenGradient V hV.continuous ρ u) +
      inner ℝ (classicalEigenGradient V hV.continuous ρ u) x =
    inner ℝ (classicalEigenGradient V hV.continuous ρ u) x +
      affineEigenConstant V ρ (classicalEigenGradient V hV.continuous ρ u)
  ring

/-- The genuine L² inner product agrees with the scaled row inner product. -/
theorem classicalEigen_inner_eq {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u v : classicalL2Eigenspace V ρ) :
    inner ℝ u v = inner ℝ (classicalEigenToRows hV ρ hρ hHess u)
      (classicalEigenToRows hV ρ hρ hHess v) / ρ := by
  change inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (v : E →₂[gibbsMeasure volume V] ℝ) = _
  rw [L2.inner_def]
  calc
    _ = ∫ x, classicalEigenRepresentative V ρ u x * classicalEigenRepresentative V ρ v x
        ∂gibbsMeasure volume V := by
      apply integral_congr_ae
      filter_upwards [(classicalEigenRepresentative_spec V ρ u).2.2,
        (classicalEigenRepresentative_spec V ρ v).2.2] with x hx hy
      rw [← hx, ← hy, Real.inner_apply]
    _ = _ := by
      simp_rw [classicalEigenRepresentative_eq_row hV ρ hρ hHess]
      exact affineEigenRows_cross_moment V (hV.differentiable (by norm_num)) hρ hprob _ _

/-- The normalized coefficient equivalence is an isometry for the actual
Gibbs L² norm. -/
@[expose] noncomputable def classicalEigenRowsIsometry {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    classicalL2Eigenspace V ρ ≃ₗᵢ[ℝ] affineEigenRows V ρ where
  toLinearEquiv := (classicalEigenRowsEquiv hV ρ hρ hHess hprob).trans
    (LinearEquiv.smulOfNeZero ℝ (affineEigenRows V ρ) (Real.sqrt ρ)⁻¹
      (inv_ne_zero (Real.sqrt_pos.mpr hρ).ne'))
  norm_map' := by
    intro u
    have hi := classicalEigen_inner_eq hV ρ hρ hHess hprob u u
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(Real.sqrt ρ)⁻¹ • classicalEigenToRows hV ρ hρ hHess u‖ ^ 2 = ‖u‖ ^ 2
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hρ),
      mul_pow, inv_pow, Real.sq_sqrt hρ.le]
    rw [hi]
    ring

/-- A genuine orthonormal basis of the classical Gibbs L² eigenspace. -/
@[expose] noncomputable def classicalEigenOrthonormalBasis {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    OrthonormalBasis (Fin (Module.finrank ℝ (affineEigenRows V ρ))) ℝ (classicalL2Eigenspace V ρ) :=
  (affineEigenRowsBasis V ρ).map (classicalEigenRowsIsometry hV ρ hρ hHess hprob).symm

/-- The evaluation eigenmap uses the unique continuous representatives of
an actual orthonormal basis, so evaluation never depends on arbitrary L² representatives. -/
@[expose] noncomputable def classicalEvaluationEigenmap {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (x : E) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (affineEigenRows V ρ))) :=
  WithLp.toLp 2 (fun i => classicalEigenRepresentative V ρ
    (classicalEigenOrthonormalBasis hV ρ hρ hHess hprob i) x)

/-- The canonical orthonormal-basis representatives are exactly the already
constructed normalized affine eigenfunctions, pointwise everywhere. -/
theorem classicalEigenOrthonormalBasis_representative {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (i : Fin (Module.finrank ℝ (affineEigenRows V ρ))) (x : E) :
    classicalEigenRepresentative V ρ (classicalEigenOrthonormalBasis hV ρ hρ hHess hprob i) x =
      affineEigenBasisFunction V ρ i x := by
  let u := classicalEigenOrthonormalBasis hV ρ hρ hHess hprob i
  have hi : classicalEigenRowsIsometry hV ρ hρ hHess hprob u = affineEigenRowsBasis V ρ i := by
    change (classicalEigenRowsIsometry hV ρ hρ hHess hprob)
      ((classicalEigenRowsIsometry hV ρ hρ hHess hprob).symm (affineEigenRowsBasis V ρ i)) = _
    exact (classicalEigenRowsIsometry hV ρ hρ hHess hprob).apply_symm_apply _
  change (Real.sqrt ρ)⁻¹ • classicalEigenToRows hV ρ hρ hHess u = affineEigenRowsBasis V ρ i at hi
  have hrow : classicalEigenToRows hV ρ hρ hHess u = affineEigenBasisCoefficient V ρ i := by
    have hh := congrArg (fun a : affineEigenRows V ρ => Real.sqrt ρ • a) hi
    simpa only [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hρ).ne', one_smul,
      affineEigenBasisCoefficient] using hh
  change classicalEigenRepresentative V ρ u x = _
  rw [classicalEigenRepresentative_eq_row hV ρ hρ hHess, hrow]
  rfl

/-- The actual evaluation eigenmap coincides everywhere with the affine
normalized eigenmap used in the Gaussian and dynamical arguments. -/
theorem classicalEvaluationEigenmap_eq_affine {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (x : E) :
    classicalEvaluationEigenmap hV ρ hρ hHess hprob x =
      WithLp.toLp 2 (fun i => affineEigenBasisFunction V ρ i x) := by
  unfold classicalEvaluationEigenmap
  simp_rw [classicalEigenOrthonormalBasis_representative hV ρ hρ hHess hprob]

end CutoffRigidity
