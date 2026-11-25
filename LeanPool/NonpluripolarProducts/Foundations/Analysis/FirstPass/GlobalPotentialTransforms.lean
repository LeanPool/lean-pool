/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPatchMeasures
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses

/-!
# Smooth changes of background representative and potential

For a genuine change `η = θ + ddᶜf`, replace the global potential `u` by `u-f`
and each local smooth correction `ρ` by `ρ+f`. The corrected extended-real
function is exactly unchanged, including at poles. Patch domains and their
coordinate-to-manifold measure transport are unchanged as well.

All background equalities are equalities of full alternating two-forms on
actual chart targets. No local dd-bar existence theorem or measure covariance
theorem is assumed or imported from Pending.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace GlobalPotentialTransforms

open PositiveClasses

@[simp] theorem smoothDDC_const (c : ℝ) (z : ComplexModel n) :
    smoothDDC (fun _ : ComplexModel n => c) z = 0 := by
  have hdc : smoothDc (fun _ : ComplexModel n => c) =
      smoothDc (fun _ : ComplexModel n => (0 : ℝ)) := by
    funext y
    ext v
    simp [smoothDc_apply]
  change extDeriv (smoothDc (fun _ : ComplexModel n => c)) z = 0
  rw [hdc]
  exact smoothDDC_zero z

/-- Subtracting a finite constant preserves the same raw theta-PSH class. -/
theorem thetaPlurisubharmonic_sub_const {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (c : ℝ) :
    ThetaPlurisubharmonic θ (fun x => u x - (c : EReal)) := by
  apply thetaPlurisubharmonic_sub_smooth (fun _ => contDiffOn_const) _ hu
  intro e z _
  rw [smoothDDC_const, add_zero]

end GlobalPotentialTransforms

namespace GlobalPotentialPatches.Patch

open GlobalPotentialTransforms PositiveClasses

variable {θ η : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
  {f : Fin n → M → ℝ}

/-- Change all background representatives and compensate all global potentials.
The chart and coordinate domain are preserved definitionally. -/
def changeRepresentative (P : Patch θ u) (hf : ∀ i, ChartSmooth (n := n) (f i))
    (hθη : ∀ (i : Fin n) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → (η i).val.coeff e z = (θ i).val.coeff e z +
        smoothDDC (fun y => f i (e.val.symm y)) z) :
    Patch η (fun i x => u i x - (f i x : EReal)) where
  chart := P.chart
  domain := P.domain
  domain_le_target := P.domain_le_target
  potential i z := P.potential i z + f i (P.chart.val.symm z)
  localPotential i :=
    isSmoothLocalPotential_add_chartSmooth (hf i) (hθη i) (P.localPotential i)
  plurisubharmonic i := by
    have heq : (fun z =>
        chartFunction (fun x => u i x - (f i x : EReal)) P.chart z +
          ((P.potential i z + f i (P.chart.val.symm z) : ℝ) : EReal)) =
        P.corrected i := by
      funext z
      exact sub_coe_add_coe _ _ _
    rw [heq]
    exact P.plurisubharmonic i

variable (P : Patch θ u) (hf : ∀ i, ChartSmooth (n := n) (f i))
  (hθη : ∀ (i : Fin n) (e : ComplexChart n M) (z : ComplexModel n),
    z ∈ e.val.target → (η i).val.coeff e z = (θ i).val.coeff e z +
      smoothDDC (fun y => f i (e.val.symm y)) z)

@[simp] theorem changeRepresentative_chart : (P.changeRepresentative hf hθη).chart = P.chart := rfl

@[simp] theorem changeRepresentative_domain : (P.changeRepresentative hf hθη).domain = P.domain :=
    rfl

@[simp] theorem changeRepresentative_source : (P.changeRepresentative hf hθη).source = P.source :=
    rfl

/-- Equality of the complete corrected tuple is pointwise everywhere; it does
not discard the pole sets or pass to real-valued representatives. -/
@[simp] theorem changeRepresentative_corrected :
    (P.changeRepresentative hf hθη).corrected = P.corrected := by
  funext i z
  exact sub_coe_add_coe _ _ _

/-- Transport of every coordinate measure is unchanged. This uses only the
identical domain and inverse chart, not any covariance theorem for products. -/
@[simp] theorem changeRepresentative_pushMeasure [MeasurableSpace M]
    (μ : Measure (ComplexModel n)) :
    (P.changeRepresentative hf hθη).pushMeasure μ = P.pushMeasure μ := rfl

end GlobalPotentialPatches.Patch

end

end SGPT.Foundations.Analysis.FirstPass
