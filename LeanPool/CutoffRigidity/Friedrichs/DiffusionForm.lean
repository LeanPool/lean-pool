/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.DiffusionTestFunctions
public import LeanPool.CutoffRigidity.Friedrichs.EnergyForm

/-! # The test-core energy form of the weighted diffusion generator -/

@[expose] public section

open Bundle Filter MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal Topology

namespace CutoffRigidity.Riemann.Diff

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The operator `A = -𝓛` on `D = C_c^∞(M) ⊂ L²(μ)`. -/
noncomputable def diffA : (LinearMap.range (testToL2 F μ)) →ₗ[ℝ] (M →₂[μ] ℝ) :=
  (-((testToL2 F μ).comp (testGen F hV))).comp
    (LinearEquiv.ofInjective (testToL2 F μ) (testToL2_injective F hV hμ)).symm.toLinearMap

theorem diffA_toL2 (a : testSub F M) :
    diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩ = -(testToL2 F μ (testGen F hV a)) := by
  have : (⟨testToL2 F μ a, a, rfl⟩ : LinearMap.range (testToL2 F μ)) =
      LinearEquiv.ofInjective (testToL2 F μ) (testToL2_injective F hV hμ) a := rfl
  simp only [diffA, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearEquiv.symm_apply_apply,
    LinearMap.neg_apply]

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
private theorem carre_comm (f g : M → ℝ) (x : M) : carre F f g x = carre F g f x := by
  simp only [carre, real_inner_comm]

private theorem diffA_pairing (a b : testSub F M) :
    inner ℝ (diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩) (testToL2 F μ b) =
      ∫ x, carre F (a : M → ℝ) (b : M → ℝ) x ∂μ := by
  rw [diffA_toL2, real_inner_comm, inner_testGen F hV hμ b a]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ carre_comm F _ _ x)

/-- Form data of `-𝓛` on `L²(μ)`, with dense symmetric nonnegative core `C_c^∞(M)`. -/
noncomputable def diffFormData : FormData (M →₂[μ] ℝ) where
  D := LinearMap.range (testToL2 F μ)
  dense := by
    let : SigmaCompactSpace M := sigmaCompactSpace_of_finite_weightedVolume F hV hμ
    exact dense_test F
  A := diffA F hV hμ
  symm := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    change inner ℝ (diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩) (testToL2 F μ b) =
      inner ℝ (testToL2 F μ a) (diffA F hV hμ ⟨testToL2 F μ b, b, rfl⟩)
    calc
      _ = ∫ x, carre F (a : M → ℝ) (b : M → ℝ) x ∂μ := diffA_pairing F hV hμ a b
      _ = ∫ x, carre F (b : M → ℝ) (a : M → ℝ) x ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x ↦ carre_comm F _ _ x)
      _ = _ := (diffA_pairing F hV hμ b a).symm.trans (real_inner_comm _ _)
  nonneg := by
    rintro ⟨_, a, rfl⟩
    change 0 ≤ inner ℝ (diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩) (testToL2 F μ a)
    rw [diffA_pairing F hV hμ a a]
    exact integral_nonneg fun x ↦ carre_nonneg F (a : M → ℝ) x

/-- The core energy of the weighted diffusion generator is the integrated gradient pairing. -/
theorem en_diffFormData (a b : testSub F M) :
    let S := diffFormData F hV hμ
    inner ℝ (S.opA ⟨testToL2 F μ a, a, rfl⟩) (testToL2 F μ b) =
      ∫ x, carre F (a : M → ℝ) (b : M → ℝ) x ∂μ :=
  diffA_pairing F hV hμ a b

end CutoffRigidity.Riemann.Diff
