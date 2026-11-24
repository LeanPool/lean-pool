/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SkodaElMirLimit
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SlotTestForms

/-!
# Positive currents carried by a set: what they cannot see

Let `T` be a positive current on a compact Kähler manifold whose trace measure is carried by a
measurable set `E` (`σ_T(M \ E) = 0`; e.g. `T = 𝟙_E S`, `CurrentRestriction`).

* **Multiples** (`apply_smulTest_eq_zero`): `T (g φ) = 0` for every test form `φ` and every
  chart-smooth `g` vanishing on `E` — the signed measure `T ∧ φ` is dominated by `σ_T`.
* **Normal derivatives** (`apply_slotForm_smulFun_exactPair_eq_zero`): if moreover `T` is closed,
  `T (h Π₁₁ (dg ∧ dF) ∧ β) = 0` for chart-smooth `h`, `F` and closed `β`
  (`d((hg) dF) = h dg ∧ dF + g dh ∧ dF`; CADG III.2.10: `dg ∧ Θ = d(gΘ) - g dΘ = 0`).

These are the first steps (S1), (S2) of the support theorem on the diagonal
(`demailly-cadg:III.2.10`, `III.2.13`; TN.4 step B4.4, `bou:diagonal-support`; plan
the Skoda–El Mir extension argument, "B4.4 PLAN").
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.CarriedCurrentTests

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents ClosedProductCurrents CurrentTraceMeasure
  CurrentRestriction SkodaElMirLimit SlotTestForms

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (w : KahlerBackground n M) {q : ℕ} {T : ProductCurrent n M q} (hT : IsPositive T)

omit [TopologicalSpace M] [CompactSpace M] [BorelSpace M] in
theorem integral_eq_zero_of_carried {μ : Measure M} {E : Set M} (hE : MeasurableSet E)
    (hμ : μ Eᶜ = 0) {g : M → ℝ} (hg : ∀ x ∈ E, g x = 0) : ∫ x, g x ∂μ = 0 := by
  have hres : μ.restrict E = μ := Measure.restrict_eq_self_of_ae_mem
    (measure_eq_zero_iff_ae_notMem.mp hμ |>.mono fun x hx => by simpa using hx)
  rw [← hres, setIntegral_congr_fun hE hg, integral_zero]

/-- **A current carried by `E` does not see multiples of functions vanishing on `E`.** -/
theorem apply_smulTest_eq_zero {E : Set M} (hE : MeasurableSet E)
    (hcar : traceMeasure w T hT Eᶜ = 0) (φ : testSpace n M q) {g : M → ℝ}
    (hg : ChartSmooth (n := n) g) (hg0 : ∀ x ∈ E, g x = 0) : T (smulTest g hg φ) = 0 := by
  have hc := restrictConst_add w φ
  obtain ⟨c', hc'0, hc'le, -⟩ := exists_const w (restrictConst w φ • kahlerTest w q + φ)
  have hle := testMeasure_le_smul_traceMeasure w T hT hc hc'0 hc'le
  have hμ : testMeasure w T hT _ hc Eᶜ = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc testMeasure w T hT _ hc Eᶜ ≤ (ENNReal.ofReal c' • traceMeasure w T hT) Eᶜ := hle Eᶜ
      _ = 0 := by rw [smul_apply, hcar, smul_zero]
  rw [apply_smulTest_eq w T hT φ hc hg, integral_eq_zero_of_carried hE hμ hg0,
    integral_eq_zero_of_carried hE hcar hg0, mul_zero, sub_zero]

/-- A current carried by `E` does not see a factor `g` equal to `1` on `E`. -/
theorem apply_smulTest_eq_of_eq_one {E : Set M} (hE : MeasurableSet E)
    (hcar : traceMeasure w T hT Eᶜ = 0) (φ : testSpace n M q) {g : M → ℝ}
    (hg : ChartSmooth (n := n) g) (hg1 : ∀ x ∈ E, g x = 1) : T (smulTest g hg φ) = T φ := by
  have h1g : ChartSmooth (n := n) (fun x => 1 - g x) := fun e => contDiffOn_const.sub (hg e)
  have h0 := apply_smulTest_eq_zero w hT hE hcar φ h1g fun x hx => by rw [hg1 x hx, sub_self]
  have hsplit : φ = smulTest g hg φ + smulTest (fun x => 1 - g x) h1g φ :=
    Subtype.ext (smoothRealForm_ext fun _ _ => by
      simp only [smulTest, Submodule.coe_add, coeff_add, smulFun_coeff]
      rw [← add_smul, add_sub_cancel, one_smul])
  conv_rhs => rw [hsplit]
  rw [map_add, h0, add_zero]

variable {k : ℕ} {S : ProductCurrent n M (k + 1)} (hS : IsPositive S)

/-- **Normal derivatives are invisible to a closed current carried by `E`**:
`S (h Π₁₁ (dg ∧ dF) ∧ β) = 0` when `g = 0` on `E` and the `βⱼ` are closed. -/
theorem apply_slotForm_smulFun_exactPair_eq_zero (hSc : IsClosedCurrent S) {E : Set M}
    (hE : MeasurableSet E) (hcar : traceMeasure w S hS Eᶜ = 0) {g h F : M → ℝ}
    (hg : ChartSmooth (n := n) g) (hh : ChartSmooth (n := n) h) (hF : ChartSmooth (n := n) F)
    (hg0 : ∀ x ∈ E, g x = 0) (β : Fin k → ClosedRealOneOneForm n M) :
    S (slotForm (smulFun h hh (exactPair g F hg hF)) k β) = 0 := by
  have hcongr := apply_slotForm_congr' hS β (γ := smulFun h hh (exactPair g F hg hF))
    (γ' := exactPair (fun x => h x * g x) F (chartSmooth_mul hh hg) hF -
      smulFun g hg (exactPair h F hh hF)) fun e z hz => by
    rw [coeff_sub, exactPair_mul_coeff hh hg hF e hz, smulFun_coeff, smulFun_coeff]
    abel
  rw [hcongr, slotForm_sub, map_sub, ← closedTestForm_eq_slotForm,
    (isClosedCurrent_succ_iff S).mp hSc, slotForm_smulFun,
    apply_smulTest_eq_zero w hS hE hcar _ hg hg0, sub_zero]

end SGPT.Foundations.Analysis.Pending.CarriedCurrentTests
