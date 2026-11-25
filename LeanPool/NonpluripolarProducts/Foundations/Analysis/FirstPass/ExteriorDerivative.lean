/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicMaps
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GeometricForms

/-!
# Exterior differentiation of smooth forms on complex manifolds

Holomorphic chart changes have complex-linear real derivatives. Naturality of
the ordinary exterior derivative then proves the overlap law for differentiated
coefficients. This gives an actual global smooth form, with exterior derivative
squaring to zero on chart targets and respecting geometric equality.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The real derivative of a holomorphic chart change is complex-linear. -/
theorem chartTransitionDerivative_complex_smul
    (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) (c : ℂ) (v : ComplexModel n) :
    chartTransitionDerivative e f z (c • v) = c • chartTransitionDerivative e f z v :=
  HolomorphicMaps.coordinateMap_fderiv_map_smul_complex contMDiff_id e f hz c v

/-- Exterior derivatives satisfy the actual tensor transformation law. -/
theorem exteriorDerivative_compatible (form : SmoothRealForm n M k)
    (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) (v : Fin (k + 1) → ComplexModel n) :
    extDeriv (form.coeff e) z v =
      extDeriv (form.coeff f) (chartTransition e f z)
        (fun i => chartTransitionDerivative e f z (v i)) := by
  have heq : form.coeff e =ᶠ[𝓝 z]
      fun w => (form.coeff f (chartTransition e f w)).compContinuousLinearMap
        (fderiv ℝ (chartTransition e f) w) := by
    filter_upwards [(chartTransition e f).open_source.mem_nhds hz] with w hw
    ext u
    exact form.compatible e f w hw u
  have htarget : chartTransition e f z ∈ f.val.target :=
    HolomorphicMaps.coordinateMap_mem_target (f := id) hz
  have hdiff := ((form.smooth f).contDiffAt
    (f.val.open_target.mem_nhds htarget)).differentiableAt (by simp)
  have hnatural := extDeriv_pullback hdiff
    (HolomorphicMaps.chartTransition_contDiffAt_real e f hz)
    (by simp)
  rw [heq.extDeriv_eq, hnatural]
  rfl

namespace SmoothRealForm

/-- Differentiated coefficient forms remain smooth on each chart target. -/
theorem contDiffOn_extDeriv_coeff (form : SmoothRealForm n M k)
    (e : ComplexChart n M) : ContDiffOn ℝ ∞ (extDeriv (form.coeff e)) e.val.target := by
  have hderiv := (contDiffOn_infty_iff_fderiv_of_isOpen e.val.open_target).mp
    (form.smooth e)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ
    (ComplexModel n) ℝ).contDiff.comp_contDiffOn hderiv.2

/-- The genuine exterior derivative, bundled as a global smooth real form. -/
def exteriorDerivative (form : SmoothRealForm n M k) : SmoothRealForm n M (k + 1) where
  coeff := fun e => extDeriv (form.coeff e)
  smooth := contDiffOn_extDeriv_coeff form
  compatible := exteriorDerivative_compatible form

@[simp] theorem exteriorDerivative_coeff (form : SmoothRealForm n M k)
    (e : ComplexChart n M) : form.exteriorDerivative.coeff e = extDeriv (form.coeff e) :=
  rfl

/-- Exterior differentiation does not depend on off-chart extensions. -/
theorem GeometricallyEq.exteriorDerivative {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) : a.exteriorDerivative.GeometricallyEq b.exteriorDerivative :=
  h.extDeriv_eqOn

/-- Closedness is exactly vanishing of the global exterior derivative. -/
theorem isClosed_iff_exteriorDerivative_geometricallyEq_zero (form : SmoothRealForm n M k) :
    form.IsClosed ↔ form.exteriorDerivative.GeometricallyEq zero :=
  Iff.rfl

/-- The second exterior derivative vanishes geometrically. -/
theorem exteriorDerivative_sq_geometricallyEq_zero (form : SmoothRealForm n M k) :
    form.exteriorDerivative.exteriorDerivative.GeometricallyEq zero := by
  intro e z hz
  exact extDeriv_extDeriv_apply
    ((form.smooth e).contDiffAt (e.val.open_target.mem_nhds hz))
    (by simp)

/-- Every exact smooth form is closed. -/
theorem exteriorDerivative_isClosed (form : SmoothRealForm n M k) :
    form.exteriorDerivative.IsClosed :=
  (isClosed_iff_exteriorDerivative_geometricallyEq_zero form.exteriorDerivative).mpr
    form.exteriorDerivative_sq_geometricallyEq_zero

end SmoothRealForm

end

end SGPT.Foundations.Analysis.FirstPass
