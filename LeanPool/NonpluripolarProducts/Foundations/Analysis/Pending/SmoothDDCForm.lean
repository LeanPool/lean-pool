/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateDensityGeometry
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ExteriorDerivative
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicDDC

/-!
# `ddᶜ` of a chart-smooth function, as a genuine global smooth two-form

`FirstPass.BottChern` compares two closed real `(1,1)`-forms through the
*relation* `BottChernRel`, which only asserts that the coefficient families
differ by `smoothDDC` of a chart-smooth function in every chart. It never
produces `ddᶜψ` itself as a form, because that needs the overlap law for
`smoothDDC`.

That overlap law is available: `FirstPass.HolomorphicDDC.smoothDc_comp` is the
naturality of the normalized `dᶜ` under a holomorphic map, and chart changes of
a complex manifold are holomorphic. So the chartwise family `dᶜψ` really is a
global smooth one-form, and its exterior derivative — computed chartwise by the
already bundled `SmoothRealForm.exteriorDerivative` — is `ddᶜψ`.

The consumer is `Pending.UniformBoundedGlobalMass`: on a compact Kähler
manifold every chart-smooth function is quasi-plurisubharmonic, i.e. is
`(θ + Cω)`-PSH for a large enough `C`, which is exactly Kähler domination
applied to `ddᶜψ`. Without `ddcForm` that domination cannot even be stated
through `exists_isSemipositive_add_smul`, which consumes a bundled form.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SmoothDDCForm

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The normalized `dᶜ` depends only on the germ, since it depends only on the
first derivative. -/
theorem smoothDc_congr {h g : ComplexModel n → ℝ} {z : ComplexModel n}
    (heq : h =ᶠ[𝓝 z] g) : smoothDc h z = smoothDc g z := by
  simp only [smoothDc, heq.fderiv_eq]

/-- **`dᶜψ` as a global smooth one-form.** The overlap law is the naturality of
`smoothDc` under the holomorphic chart transitions. -/
def dcForm (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ) : SmoothRealForm n M 1 where
  coeff e := smoothDc fun z => ψ (e.val.symm z)
  smooth e := smoothDc_contDiffOn e.val.open_target (hψ e)
  compatible := by
    intro e f z hz v
    have hmem : chartTransition e f z ∈ f.val.target :=
      HolomorphicMaps.coordinateMap_mem_target (f := id) hz
    have hFz : DifferentiableAt ℂ (chartTransition e f) z :=
      (HolomorphicMaps.chartTransition_contDiffAt e f hz).differentiableAt (by simp)
    have hρ : DifferentiableAt ℝ (fun w => ψ (f.val.symm w)) (chartTransition e f z) :=
      ((hψ f).contDiffAt (f.val.open_target.mem_nhds hmem)).differentiableAt (by simp)
    have heq : (fun y => ψ (e.val.symm y)) =ᶠ[𝓝 z]
        fun y => (fun w => ψ (f.val.symm w)) (chartTransition e f y) := by
      filter_upwards [(chartTransition e f).open_source.mem_nhds hz] with y hy
      have hy' : e.val.symm y ∈ f.val.source := hy.2
      change ψ (e.val.symm y) = ψ (f.val.symm (f.val (e.val.symm y)))
      rw [f.val.left_inv hy']
    rw [smoothDc_congr heq, HolomorphicDDC.smoothDc_comp hFz hρ]
    rfl

@[simp] theorem dcForm_coeff (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ)
    (e : ComplexChart n M) :
    (dcForm ψ hψ).coeff e = smoothDc fun z => ψ (e.val.symm z) := rfl

/-- **`ddᶜψ` as a global smooth two-form.** -/
def ddcForm (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ) : SmoothRealForm n M 2 :=
  (dcForm ψ hψ).exteriorDerivative

@[simp] theorem ddcForm_coeff (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ)
    (e : ComplexChart n M) :
    (ddcForm ψ hψ).coeff e = smoothDDC fun z => ψ (e.val.symm z) := rfl

/-- **`ddᶜψ` of a chart-smooth function as a closed real `(1,1)`-form.**
`ddcForm` gives the overlap law, and `d² = 0` and `J`-invariance give the remaining fields. -/
def ddcClosedForm (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ) :
    ClosedRealOneOneForm n M :=
  ⟨ddcForm ψ hψ, SmoothRealForm.exteriorDerivative_isClosed _, by
    intro e z hz u v
    rw [ddcForm_coeff]
    exact MongeAmpere.smoothDDC_isOneOne
      (((hψ e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) u v⟩

@[simp] theorem ddcClosedForm_coeff (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ)
    (e : ComplexChart n M) :
    (ddcClosedForm ψ hψ).val.coeff e = smoothDDC fun z => ψ (e.val.symm z) := rfl

end

end SGPT.Foundations.Analysis.Pending.SmoothDDCForm
