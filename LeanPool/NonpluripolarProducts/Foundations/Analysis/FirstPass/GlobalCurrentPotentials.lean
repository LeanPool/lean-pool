/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularDistribution

/-!
# Chartwise potential currents and coefficients of global currents

The model is the actual complex vector space `ComplexModel n`. One ordered real
basis fixes both the measure `b.addHaar` and the complementary-degree pairing.
No complex orientation is claimed for an arbitrary basis. Chart integrability is
an explicit input here; its consequence from quasi-PSH and nondegeneracy, and
holomorphic overlap compatibility, are separate Pending theorems.

Closedness, type `(1,1)`, and vector-square positivity below are predicates on
coefficients extracted from actual global currents. The last predicate does not
assert positivity against all complementary positive test forms. No inverse
pairing identity or distributional differential calculus is assumed in this file.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.FirstPass

open LocalCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- Real degree two is admissible exactly when the complex dimension is positive. -/
abbrev degreeTwo (hn : 0 < n) : CurrentDegree n :=
  ⟨2, by rw [complexModel_real_finrank]; omega⟩

@[simp] theorem degreeTwo_val (hn : 0 < n) : (degreeTwo hn).val = 2 := rfl

namespace GlobalCurrent

variable {k : CurrentDegree n}
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- Extract genuine scalar-distribution coefficients by contraction with the
basis volume. This construction does not assume that extraction inverts pairing. -/
def coefficients (T : GlobalCurrent n M k) (e : ComplexChart n M) :
    DistributionForm (chartTarget e) k.val := fromLocalCurrent b k (T.inChart e)

theorem coefficients_apply (T : GlobalCurrent n M k) (e : ComplexChart n M)
    (v : Fin k.val → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    T.coefficients b e v φ = T.inChart e (constantTestFormCLM
      (contractVolume (basisVolume (currentPairingBasis b k)) v) φ) := rfl

@[simp] theorem coefficients_zero (e : ComplexChart n M) :
    (0 : GlobalCurrent n M k).coefficients b e = 0 := by
  ext v φ
  rfl

@[simp] theorem coefficients_add (S T : GlobalCurrent n M k) (e : ComplexChart n M) :
    (S + T).coefficients b e = S.coefficients b e + T.coefficients b e := by
  ext v φ
  rfl

@[simp] theorem coefficients_smul (c : ℝ) (T : GlobalCurrent n M k)
    (e : ComplexChart n M) :
    (c • T).coefficients b e = c • T.coefficients b e := by
  ext v φ
  rfl

@[simp] theorem coefficients_neg (T : GlobalCurrent n M k) (e : ComplexChart n M) :
    (-T).coefficients b e = -T.coefficients b e := by
  ext v φ
  rfl

/-- Coefficient extraction commutes with restriction to any open chart subdomain.
The inclusion preserves the test itself; no coordinate-change assertion is used. -/
theorem coefficients_restrictChart (T : GlobalCurrent n M k) (e : ComplexChart n M)
    {U : Opens (ComplexModel n)} (hU : U ≤ chartTarget e)
    (v : Fin k.val → ComplexModel n) (φ : 𝓓(U, ℝ)) :
    fromLocalCurrent b k (T.restrictChart e hU) v φ =
      T.coefficients b e v (TestFunction.monoCLM ℝ φ) := by
  change T.inChart e (TestFunction.monoCLM ℝ (constantTestFormCLM _ φ)) =
    T.inChart e (constantTestFormCLM _ (TestFunction.monoCLM ℝ φ))
  congr 1
  ext x
  rw [testForm_inclusion_apply hU]
  simp only [constantTestFormCLM_apply]
  have hi := TestFunction.monoCLM_apply (𝕜 := ℝ) (n₂ := ⊤)
    (Ω₂ := chartTarget e) φ
  have hx := congrFun hi x
  simp only [le_refl, hU, and_self, ↓reduceIte] at hx
  rw [hx]

/-- Closedness of the extracted distribution-valued forms in every chart,
relative to the specified volume normalization. -/
def IsClosed (T : GlobalCurrent n M k) : Prop :=
  ∀ e, LocalCurrents.IsClosed (T.coefficients b e)

/-- Closedness is preserved by addition of actual global currents. -/
theorem IsClosed.add {S T : GlobalCurrent n M k}
    (hS : S.IsClosed b) (hT : T.IsClosed b) : (S + T).IsClosed b := by
  intro e
  have hd : exteriorDerivative (S.coefficients b e + T.coefficients b e) =
      exteriorDerivative (S.coefficients b e) + exteriorDerivative (T.coefficients b e) := by
    ext v φ
    simp [exteriorDerivative_apply, map_add, smul_add, Finset.sum_add_distrib]
  unfold LocalCurrents.IsClosed
  rw [coefficients_add, hd, hS e, hT e, add_zero]

/-- Closedness is preserved by every real scalar multiple. -/
theorem IsClosed.smul {T : GlobalCurrent n M k} (hT : T.IsClosed b) (c : ℝ) :
    (c • T).IsClosed b := by
  intro e
  have hd : exteriorDerivative (c • T.coefficients b e) =
      c • exteriorDerivative (T.coefficients b e) := by
    ext v : 1
    simp only [exteriorDerivative_apply, _root_.smul_apply,
      map_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  unfold LocalCurrents.IsClosed
  rw [coefficients_smul, hd, hT e, smul_zero]

theorem isClosed_zero : (0 : GlobalCurrent n M k).IsClosed b := by
  intro e
  unfold LocalCurrents.IsClosed
  rw [coefficients_zero]
  ext v φ
  simp [exteriorDerivative_apply]

/-- The closed currents form an actual subspace of the existing global current
space, with closedness tested on the extracted coefficient differential. -/
def closedSubmodule : Submodule ℝ (GlobalCurrent n M k) where
  carrier := {T | T.IsClosed b}
  zero_mem' := isClosed_zero b
  add_mem' := fun hS hT => hS.add b hT
  smul_mem' := fun c _ hT => hT.smul b c

/-- Type `(1,1)` of the extracted real degree-two coefficients. -/
def IsTypeOneOne (hn : 0 < n) (T : GlobalCurrent n M (degreeTwo hn)) : Prop :=
  ∀ e, LocalCurrents.IsOneOne (T.coefficients b e)

/-- Positivity on coefficient vector squares. This is not a definition of the
full positive cone of complementary-degree test forms. -/
def IsSquarePositive (hn : 0 < n) (T : GlobalCurrent n M (degreeTwo hn)) : Prop :=
  ∀ e, LocalCurrents.SquarePositive (T.coefficients b e)

theorem IsTypeOneOne.add {hn : 0 < n} {S T : GlobalCurrent n M (degreeTwo hn)}
    (hS : S.IsTypeOneOne b hn) (hT : T.IsTypeOneOne b hn) :
    (S + T).IsTypeOneOne b hn := by
  intro e v w
  rw [coefficients_add]
  change S.coefficients b e ![Complex.I • v, Complex.I • w] +
      T.coefficients b e ![Complex.I • v, Complex.I • w] =
    S.coefficients b e ![v, w] + T.coefficients b e ![v, w]
  rw [hS e v w, hT e v w]

theorem IsTypeOneOne.smul {hn : 0 < n} {T : GlobalCurrent n M (degreeTwo hn)}
    (hT : T.IsTypeOneOne b hn) (c : ℝ) : (c • T).IsTypeOneOne b hn := by
  intro e v w
  rw [coefficients_smul]
  change c • T.coefficients b e ![Complex.I • v, Complex.I • w] =
    c • T.coefficients b e ![v, w]
  rw [hT e v w]

theorem IsSquarePositive.add {hn : 0 < n} {S T : GlobalCurrent n M (degreeTwo hn)}
    (hS : S.IsSquarePositive b hn) (hT : T.IsSquarePositive b hn) :
    (S + T).IsSquarePositive b hn := by
  intro e r v f
  rw [coefficients_add]
  change 0 ≤ ∑ i, ∑ j, (S.coefficients b e ![v i, Complex.I • v j]
    (testProduct (f i) (f j)) + T.coefficients b e ![v i, Complex.I • v j]
    (testProduct (f i) (f j)))
  simpa only [Finset.sum_add_distrib] using add_nonneg (hS e r v f) (hT e r v f)

theorem IsSquarePositive.smul {hn : 0 < n} {T : GlobalCurrent n M (degreeTwo hn)}
    (hT : T.IsSquarePositive b hn) {c : ℝ} (hc : 0 ≤ c) :
    (c • T).IsSquarePositive b hn := by
  intro e r v f
  rw [coefficients_smul]
  change 0 ≤ ∑ i, ∑ j, c * T.coefficients b e ![v i, Complex.I • v j]
    (testProduct (f i) (f j))
  simpa only [Finset.mul_sum] using mul_nonneg hc (hT e r v f)

end GlobalCurrent

section Potentials

variable [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- Integrability is required only on chart targets, with exactly the measure
used to form the regular scalar distributions. -/
def ChartLocallyIntegrable (u : M → EReal) : Prop :=
  ∀ e : ComplexChart n M,
    LocallyIntegrableOn (fun z => (chartFunction u e z).toReal) (chartTarget e) b.addHaar

/-- The genuine normalized distribution-valued two-form of a chart potential. -/
def chartDDC (u : M → EReal) (e : ComplexChart n M)
    (hu : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal)
      (chartTarget e) b.addHaar) : DistributionForm (chartTarget e) 2 :=
  ddC (regularDistribution b.addHaar (fun z => (chartFunction u e z).toReal) hu)

variable [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The full alternating coefficient retains the revised `1/(4π)` factor. -/
theorem chartDDC_apply (u : M → EReal) (e : ComplexChart n M)
    (hu : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal)
      (chartTarget e) b.addHaar) (v w : ComplexModel n) :
    chartDDC b u e hu ![v, w] = (-1 / (4 * Real.pi) : ℝ) •
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • w)
            (regularDistribution b.addHaar (fun z => (chartFunction u e z).toReal) hu)) -
        Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • v)
            (regularDistribution b.addHaar (fun z => (chartFunction u e z).toReal) hu))) :=
  ddC_apply _ v w

omit [IsComplexManifold n M] in
/-- On complex lines the normalization is the distributional Levi operator / π. -/
theorem chartDDC_complexLine (u : M → EReal) (e : ComplexChart n M)
    (hu : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal)
      (chartTarget e) b.addHaar) (v : ComplexModel n) :
    chartDDC b u e hu ![v, Complex.I • v] = (1 / Real.pi : ℝ) •
      distributionalLeviCLM v
        (regularDistribution b.addHaar (fun z => (chartFunction u e z).toReal) hu) :=
  ddC_complexLine _ v

omit [IsComplexManifold n M] in
/-- Equality a.e. on the chart target suffices; off-target extensions do not matter. -/
theorem chartDDC_congr_ae {u w : M → EReal} (e : ComplexChart n M)
    (hu : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal)
      (chartTarget e) b.addHaar)
    (hw : LocallyIntegrableOn (fun z => (chartFunction w e z).toReal)
      (chartTarget e) b.addHaar)
    (huw : chartFunction u e =ᵐ[b.addHaar.restrict (chartTarget e)] chartFunction w e) :
    chartDDC b u e hu = chartDDC b w e hw := by
  unfold chartDDC
  rw [regularDistribution_congr_ae_on hu hw (huw.mono fun _ h => congrArg EReal.toReal h)]

/-- A chart family of actual degree-two currents, using the same basis as the
Haar density. No overlap compatibility is an input to this construction. -/
def ddCCurrentFamily (hn : 0 < n) (u : M → EReal) (hu : ChartLocallyIntegrable b u) :
    ChartCurrentFamily n M (degreeTwo hn) :=
  fun e => toLocalCurrent b (degreeTwo hn) (chartDDC b u e (hu e))

omit [IsComplexManifold n M] in
theorem ddCCurrentFamily_apply (hn : 0 < n) (u : M → EReal)
    (hu : ChartLocallyIntegrable b u) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - 2)) :
    ddCCurrentFamily b hn u hu e η = distributionTestPairing
      (((chartDDC b u e (hu e)).domCoprod (testFormAlternating η))
        (currentPairingBasis b (degreeTwo hn))) :=
  toLocalCurrent_eq_domCoprod b (degreeTwo hn) _ η

omit [IsComplexManifold n M] in
theorem ddCCurrentFamily_congr_ae (hn : 0 < n) {u w : M → EReal}
    (hu : ChartLocallyIntegrable b u) (hw : ChartLocallyIntegrable b w)
    (huw : ∀ e, chartFunction u e =ᵐ[b.addHaar.restrict (chartTarget e)] chartFunction w e) :
    ddCCurrentFamily b hn u hu = ddCCurrentFamily b hn w hw := by
  funext e
  unfold ddCCurrentFamily
  rw [chartDDC_congr_ae b e (hu e) (hw e) (huw e)]

/-- The concrete family θ + ddᶜu, with no closedness or local-potential assumption
on the specified smooth form θ. -/
def thetaDDCCurrentFamily (hn : 0 < n) (θ : SmoothRealForm n M 2)
    (u : M → EReal) (hu : ChartLocallyIntegrable b u) :
    ChartCurrentFamily n M (degreeTwo hn) :=
  smoothCurrentFamily b (k := degreeTwo hn) θ + ddCCurrentFamily b hn u hu

@[simp] theorem thetaDDCCurrentFamily_apply (hn : 0 < n) (θ : SmoothRealForm n M 2)
    (u : M → EReal) (hu : ChartLocallyIntegrable b u) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - 2)) :
    thetaDDCCurrentFamily b hn θ u hu e η =
      smoothCurrentFamily b (k := degreeTwo hn) θ e η + ddCCurrentFamily b hn u hu e η := rfl

end Potentials

end SGPT.Foundations.Analysis.FirstPass
