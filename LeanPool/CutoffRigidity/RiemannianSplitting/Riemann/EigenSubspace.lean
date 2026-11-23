/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.EigenLinear

/-! # Smooth eigenfunctions and their almost-everywhere classes in L² -/

@[expose] public section

open Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace CutCur

section EigenSubspace

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M]

/-- Smooth `L²` eigenfunctions with eigenvalue `lam` form a subspace of `M → ℝ`. -/
def eigenSub (μ : Measure M) (V : M → ℝ) (lam : ℝ) : Submodule ℝ (M → ℝ) where
  carrier := {f | IsMEigenfunction F μ V lam f}
  zero_mem' := by
    refine ⟨contMDiff_const, ?_, fun x => ?_⟩
    · exact MemLp.zero
    · simp only [Pi.zero_apply, mul_zero]
      exact mgenerator_zero F x
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨hf1.add hg1, hf2.add hg2, fun x => ?_⟩
    have := mgenerator_add F (V := V) hf1 hg1 x
    simp only [Pi.add_apply]
    rw [show (f + g) = fun y => f y + g y from rfl, this, hf3, hg3]; ring
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨(contMDiff_const (c := c)).mul hf1, hf2.const_smul c, fun x => ?_⟩
    have := mgenerator_const_mul F (V := V) c hf1 x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (c • f) = fun y => c * f y from rfl, this, hf3]; ring

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_eigenSub {μ : Measure M} {V : M → ℝ} {lam : ℝ} {f : M → ℝ} :
    f ∈ eigenSub F μ V lam ↔ IsMEigenfunction F μ V lam f := Iff.rfl

/-- The map taking smooth eigenfunctions to their almost-everywhere classes. -/
def eigenSubToLp (μ : Measure M) (V : M → ℝ) (lam : ℝ) :
    eigenSub F μ V lam →ₗ[ℝ] (M →₂[μ] ℝ) where
  toFun f := f.2.2.1.toLp f.1
  map_add' f g := MemLp.toLp_add f.2.2.1 g.2.2.1
  map_smul' c f := MemLp.toLp_const_smul c f.2.2.1

omit [MeasurableSpace F] [BorelSpace F] in
theorem eigenClasses_carrier_eq (μ : Measure M) (V : M → ℝ) (lam : ℝ) :
    {u : M →₂[μ] ℝ | ∃ f, IsMEigenfunction F μ V lam f ∧ f =ᵐ[μ] u} =
      ((eigenSubToLp F μ V lam).range : Set (M →₂[μ] ℝ)) := by
  ext u
  constructor
  · rintro ⟨f, hf, hfu⟩
    refine ⟨⟨f, hf⟩, ?_⟩
    change hf.2.1.toLp f = u
    exact Lp.ext ((MemLp.coeFn_toLp hf.2.1).trans hfu)
  · rintro ⟨f, rfl⟩
    exact ⟨f.1, f.2, (MemLp.coeFn_toLp f.2.2.1).symm⟩

/-- The `L²` classes of eigenfunctions, as a subspace of `L²(μ)`. -/
def eigenClasses (μ : Measure M) (V : M → ℝ) (lam : ℝ) : Submodule ℝ (M →₂[μ] ℝ) :=
  (eigenSubToLp F μ V lam).range.copy _ (eigenClasses_carrier_eq F μ V lam)

end EigenSubspace

end CutCur
