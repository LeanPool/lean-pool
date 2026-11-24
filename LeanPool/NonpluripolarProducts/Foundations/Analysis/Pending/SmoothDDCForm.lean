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
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerDomination

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

open FirstPass FirstPass.PositiveClasses

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

variable [CompactSpace M]

/-- **Every chart-smooth function is quasi-plurisubharmonic.** On a compact
Kähler manifold a smooth function is `(θ + Cω)`-PSH for a large enough `C`,
uniformly over a finite family of backgrounds and functions. This is Kähler
domination applied to the backgrounds and to the `ddᶜ` of the functions. -/
theorem exists_pos_thetaPlurisubharmonic_smooth {ι : Type*} [Finite ι]
    (omega : KahlerBackground n M) (θ : ι → ClosedRealOneOneForm n M)
    (ψ : ι → M → ℝ) (hψ : ∀ i, ChartSmooth (n := n) (ψ i)) :
    ∃ C : ℝ, 0 < C ∧ (∀ i, (θ i + C • omega.form).val.IsSemipositive) ∧
      ∀ i, ThetaPlurisubharmonic (θ i + C • omega.form).val
        fun x => ((ψ i x : ℝ) : EReal) := by
  classical
  let := Fintype.ofFinite ι
  have hherm : omega.form.val.IsHermitian := omega.isKahler.1
  -- a constant dominating every background
  obtain ⟨A, hA, hAdom⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega θ
  -- a constant dominating every `ddᶜψ i`
  have hlocal : ∀ i : ι, ∃ B : ℝ, 0 < B ∧ ∀ (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → ∀ v : ComplexModel n,
        0 ≤ (ddcForm (ψ i) (hψ i)).coeff e z ![v, Complex.I • v] +
          B * omega.form.val.coeff e z ![v, Complex.I • v] := fun i =>
    KahlerDomination.exists_isSemipositive_add_smul _ _ hherm
  choose B hB hBdom using hlocal
  set C : ℝ := A + ∑ i, B i with hCdef
  have hBsum : (0 : ℝ) ≤ ∑ i, B i := Finset.sum_nonneg fun j _ => (hB j).le
  have hCpos : 0 < C := by rw [hCdef]; linarith
  -- the pointwise inequalities, in raw coefficient form
  have hω : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, 0 ≤ omega.form.val.coeff e z ![v, Complex.I • v] :=
    fun e z hz v => omega.isSemipositive e z hz v
  have hAi : ∀ (i : ι) (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, 0 ≤ (θ i).val.coeff e z ![v, Complex.I • v] +
        A * omega.form.val.coeff e z ![v, Complex.I • v] := by
    intro i e z hz v
    simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
      using hAdom i e z hz v
  have hgrow : ∀ (i : ι) (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, (A + B i) * omega.form.val.coeff e z ![v, Complex.I • v] ≤
        C * omega.form.val.coeff e z ![v, Complex.I • v] := by
    intro i e z hz v
    refine mul_le_mul_of_nonneg_right ?_ (hω e z hz v)
    have := Finset.single_le_sum (f := B) (fun j _ => (hB j).le) (Finset.mem_univ i)
    rw [hCdef]; linarith
  have hsemi : ∀ i, (θ i + C • omega.form).val.IsSemipositive := by
    intro i e z hz v
    have h1 := hAi i e z hz v
    have h2 : A * omega.form.val.coeff e z ![v, Complex.I • v] ≤
        C * omega.form.val.coeff e z ![v, Complex.I • v] := by
      refine mul_le_mul_of_nonneg_right ?_ (hω e z hz v)
      rw [hCdef]; linarith
    have : 0 ≤ (θ i).val.coeff e z ![v, Complex.I • v] +
        C * omega.form.val.coeff e z ![v, Complex.I • v] := by linarith
    simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] using this
  refine ⟨C, hCpos, hsemi, fun i => ?_⟩
  rw [LocalPotentials.thetaPlurisubharmonic_smooth_iff _ _ (hψ i)]
  intro e z hz v
  have h1 := hAi i e z hz v
  have h2 := hBdom i e z hz v
  have h3 := hgrow i e z hz v
  simp only [ddcForm_coeff] at h2
  have hfinal : 0 ≤ (θ i).val.coeff e z ![v, Complex.I • v] +
      C * omega.form.val.coeff e z ![v, Complex.I • v] +
      smoothDDC (fun y => ψ i (e.val.symm y)) z ![v, Complex.I • v] := by
    nlinarith [h1, h2, h3]
  simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] using hfinal

end

end SGPT.Foundations.Analysis.Pending.SmoothDDCForm
