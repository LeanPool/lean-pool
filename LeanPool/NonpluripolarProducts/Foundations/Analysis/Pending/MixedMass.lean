/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalMeasureInvariance
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MassFromBoundedDifference
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedMassBoundedDifference
public import Mathlib.Basic.ENNReal.Real

/-!
# Total mass of the actual global mixed non-pluripolar measure

Mass means evaluation of the constructed measure on the whole manifold.
Its real-valued encoding is justified by the compact Kähler finiteness theorem;
no argument silently treats the `toReal` value of an infinite mass as its mass.

Total mass is monotone in the singularity order for a fixed tuple of background
forms and locally nondegenerate theta-PSH potentials on a compact Kähler
manifold (`globalMixedMass_mono`). The proof is elementary: bounded differences
do not change mixed mass (`Pending.MixedMassBoundedDifference`), and the general
order reduces to that case (`Pending.MassFromBoundedDifference`). Measures on
arbitrary subsets are not compared. Equality for the same singularity type is
derived from the two comparisons.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.MixedMass

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialTransforms GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The actual extended nonnegative total mass; the input potentials may be
degenerate, as permitted by the global measure constructor. -/
def globalMixedMass (θ : Fin n → ClosedRealOneOneForm n M)
    (u : Fin n → M → EReal) (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    ℝ≥0∞ := globalMixedMeasure θ u hu univ

/-- Real encoding of the total mass. Recovery of the original mass requires
finiteness, supplied below by a genuine Kähler background. -/
def globalMixedMassReal (θ : Fin n → ClosedRealOneOneForm n M)
    (u : Fin n → M → EReal) (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    ℝ := (globalMixedMass θ u hu).toReal

variable {θ : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}

theorem globalMixedMass_lt_top (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    globalMixedMass θ u hu < ⊤ :=
  globalMixedMeasure_apply_lt_top omega hu univ

omit [BorelSpace M] in
theorem globalMixedMassReal_nonneg
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    0 ≤ globalMixedMassReal θ u hu := ENNReal.toReal_nonneg

/-- Under the actual finiteness theorem, realification loses no mass. -/
theorem ofReal_globalMixedMassReal (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    ENNReal.ofReal (globalMixedMassReal θ u hu) = globalMixedMass θ u hu :=
  ENNReal.ofReal_toReal (globalMixedMass_lt_top omega hu).ne

section RepresentativeChanges

variable {η : Fin n → ClosedRealOneOneForm n M} {f : Fin n → M → ℝ}

/-- A compensated smooth representative change preserves actual total mass.
No Kähler mass bound or singularity comparison is used. -/
theorem globalMixedMass_changeRepresentative
    (hf : ∀ i, ChartSmooth (n := n) (f i))
    (hθη : ∀ (i : Fin n) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → (η i).val.coeff e z = (θ i).val.coeff e z +
        smoothDDC (fun y => f i (e.val.symm y)) z)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    globalMixedMass η (fun i x => u i x - (f i x : EReal))
        (fun i => thetaPlurisubharmonic_sub_smooth (hf i) (hθη i) (hu i)) =
      globalMixedMass θ u hu :=
  congrArg (fun μ : Measure M => μ univ)
    (GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative hf hθη hu)

/-- Equality of the real encodings follows from genuine total-mass equality,
not from an implication reversing the potentially noninjective `toReal` map. -/
theorem globalMixedMassReal_changeRepresentative
    (hf : ∀ i, ChartSmooth (n := n) (f i))
    (hθη : ∀ (i : Fin n) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → (η i).val.coeff e z = (θ i).val.coeff e z +
        smoothDDC (fun y => f i (e.val.symm y)) z)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    globalMixedMassReal η (fun i x => u i x - (f i x : EReal))
        (fun i => thetaPlurisubharmonic_sub_smooth (hf i) (hθη i) (hu i)) =
      globalMixedMassReal θ u hu :=
  congrArg ENNReal.toReal (globalMixedMass_changeRepresentative hf hθη hu)

theorem globalMixedMass_sub_const
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (c : Fin n → ℝ) :
    globalMixedMass θ (fun i x => u i x - (c i : EReal))
        (fun i => thetaPlurisubharmonic_sub_const (hu i) (c i)) =
      globalMixedMass θ u hu :=
  congrArg (fun μ : Measure M => μ univ)
    (GlobalMeasureInvariance.globalMixedMeasure_sub_const hu c)

theorem globalMixedMassReal_sub_const
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (c : Fin n → ℝ) :
    globalMixedMassReal θ (fun i x => u i x - (c i : EReal))
        (fun i => thetaPlurisubharmonic_sub_const (hu i) (c i)) =
      globalMixedMassReal θ u hu :=
  congrArg ENNReal.toReal (globalMixedMass_sub_const hu c)

end RepresentativeChanges

section Comparison

/-- **Mixed total-mass monotonicity in the singularity order**
(Darvas--Di Nezza--Lu, arXiv:1705.05796v3, `thm: BEGZ_monotonicity_full`;
Witt Nyström, arXiv:1703.01950, `compthm`, in the diagonal case).
The comparison concerns total masses and applies in every dimension. -/
theorem globalMixedMass_mono (omega : KahlerBackground n M)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, MoreSingularOn (u i) (v i) univ) :
    globalMixedMass θ u (fun i => (hu i).1) ≤
      globalMixedMass θ v (fun i => (hv i).1) :=
  MassFromBoundedDifference.globalMixedMeasure_univ_le_of_moreSingular hu hv huv
    fun _ _ ha hb _ ht hab hba =>
      (MixedMassBoundedDifference.globalMixedMeasure_univ_eq_of_le_add omega ha hb ht hab
        hba).le

/-- Equality of singularity type yields equality of total mass by applying
monotonicity in both directions; it does not yield equality of measures. -/
theorem globalMixedMass_eq_of_sameSingularityType (omega : KahlerBackground n M)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, SameSingularityTypeOn (u i) (v i) univ) :
    globalMixedMass θ u (fun i => (hu i).1) =
      globalMixedMass θ v (fun i => (hv i).1) :=
  le_antisymm
    (globalMixedMass_mono omega hu hv (fun i => (huv i).1))
    (globalMixedMass_mono omega hv hu (fun i => (huv i).2))

/-- The upper mass is finite before transferring its order to real numbers. -/
theorem globalMixedMassReal_mono (omega : KahlerBackground n M)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, MoreSingularOn (u i) (v i) univ) :
    globalMixedMassReal θ u (fun i => (hu i).1) ≤
      globalMixedMassReal θ v (fun i => (hv i).1) :=
  ENNReal.toReal_mono (globalMixedMass_lt_top omega (fun i => (hv i).1)).ne
    (globalMixedMass_mono omega hu hv huv)

theorem globalMixedMassReal_eq_of_sameSingularityType (omega : KahlerBackground n M)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, SameSingularityTypeOn (u i) (v i) univ) :
    globalMixedMassReal θ u (fun i => (hu i).1) =
      globalMixedMassReal θ v (fun i => (hv i).1) :=
  congrArg ENNReal.toReal (globalMixedMass_eq_of_sameSingularityType omega hu hv huv)

end Comparison

end

end SGPT.Foundations.Analysis.Pending.MixedMass
