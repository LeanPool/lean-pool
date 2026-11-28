/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Equivalent probability measures, and the one from a positive normalised density

`IsEquivProbMeasure P Q` (`Q` a probability measure with `Q ≪ P` and `P ≪ Q`) is the prefix every
equivalent-martingale-measure structure of the library extends.

A strictly-positive, `P`-integrable density `g` with `∫ g ∂P = 1` defines an
**equivalent probability measure** `P.withDensity (fun ω ↦ ENNReal.ofReal (g ω))`: it is a
probability measure (total mass `∫ g = 1`) and mutually absolutely continuous with `P`
(`withDensity` is always `≪ P`, and `P ≪` it because the density is a.e. nonzero).

This is the change-of-measure ritual shared by the equivalent-martingale-measure constructions
in the one-period FTAP files (`FTAPOnePeriod.lean`, `FTAPOnePeriodVector.lean`): each builds its
fair density (a logistic Esscher weight, or a `(1+‖Y‖)⁻¹` tempering for the `L¹` reduction),
normalises it, and then needs exactly `IsEquivProbMeasure P Q`.

An equivalence on a sub-σ-algebra `m` extends to the whole space: `P` weighted by the density
`d(Q|m)/d(P|m)` of the restrictions is equivalent to `P` everywhere and is `Q` on `m`
(`exists_isEquivProbMeasure_trim_eq`). A pricing measure up to a horizon `T` need only be equivalent
to the reference measure on the information `𝓕 T`, and this is how it meets the theorems stated for
measures equivalent on the whole space.

## Main definitions

* `IsEquivProbMeasure`: `Q` is a probability measure with `Q ≪ P` and `P ≪ Q`.

## Main results

* `absolutelyContinuous_withDensity_ofReal`: an a.e. strictly positive density makes `P`
  absolutely continuous with respect to `P.withDensity (ofReal g)`.
* `isEquivProbMeasure_withDensity_of_isProbabilityMeasure`: `P.withDensity (ofReal g)` for an a.e.
  strictly positive density `g` is equivalent to `P` as soon as it is a probability measure.
* `isEquivProbMeasure_withDensity`: for a strictly positive, `P`-integrable `g` with `∫ g ∂P = 1`,
  `P.withDensity (ofReal g)` is an equivalent probability measure.
* `trim_withDensity_rnDeriv_trim`: `P` weighted by `d(Q|m)/d(P|m)` restricts to `Q|m` on `m`, when
  `Q|m ≪ P|m`.
* `integral_rnDeriv_trim_mul`: `∫ (d(Q|m)/d(P|m)) * g ∂P = ∫ g ∂Q` for `m`-measurable `g`, when
  `Q|m ≪ P|m`.
* `exists_isEquivProbMeasure_trim_eq`: a probability measure equivalent to `P` on a sub-σ-algebra
  agrees there with one equivalent to `P` on the whole space.

## Tags

equivalent probability measure, mutual absolute continuity, density, withDensity,
equivalent martingale measure, MSC 28A25, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- A density that is a.e. strictly positive makes `P` absolutely continuous with respect to
`P.withDensity (fun ω ↦ ENNReal.ofReal (g ω))`: the density vanishes only on a `P`-null set.
(The other direction, `withDensity ≪ P`, is `withDensity_absolutelyContinuous` and needs
nothing.) -/
theorem absolutelyContinuous_withDensity_ofReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) {g : Ω → ℝ} (hmeas : AEMeasurable g P) (hpos : ∀ᵐ ω ∂P, 0 < g ω) :
    P ≪ P.withDensity (fun ω ↦ ENNReal.ofReal (g ω)) :=
  withDensity_absolutelyContinuous' hmeas.ennreal_ofReal
    (hpos.mono fun _ hω ↦ ENNReal.ofReal_pos.mpr hω |>.ne')

/-- `Q` is an **equivalent probability measure** for `P`: a probability measure with the same null
sets, `Q ≪ P` and `P ≪ Q`. The prefix shared by every equivalent-martingale-measure structure of
the library (`IsEMM`, at every time index, and `OnePeriodVector.IsEMM`), which `extend` it. -/
structure IsEquivProbMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω} (P Q : Measure Ω) : Prop where
  isProb : IsProbabilityMeasure Q
  ac : Q ≪ P
  ac' : P ≪ Q

/-- `Q = P.withDensity (ofReal g)` for an a.e. strictly positive density `g` is an equivalent
probability measure as soon as it is a probability measure: `≪ P` holds for every density
(`withDensity_absolutelyContinuous`), `P ≪` by positivity
(`absolutelyContinuous_withDensity_ofReal`). -/
theorem isEquivProbMeasure_withDensity_of_isProbabilityMeasure {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) {g : Ω → ℝ} (hmeas : AEMeasurable g P)
    (hpos : ∀ᵐ ω ∂P, 0 < g ω)
    (hQ : IsProbabilityMeasure (P.withDensity (fun ω ↦ ENNReal.ofReal (g ω)))) :
    IsEquivProbMeasure P (P.withDensity (fun ω ↦ ENNReal.ofReal (g ω))) :=
  ⟨hQ, withDensity_absolutelyContinuous _ _, absolutelyContinuous_withDensity_ofReal P hmeas hpos⟩

/-- A strictly-positive, `P`-integrable density `g` with `∫ g ∂P = 1` makes
`Q = P.withDensity (fun ω ↦ ENNReal.ofReal (g ω))` a probability measure equivalent to `P`.
(Measurability is not assumed: the integrability of `g` already makes it a.e.-measurable, which
is all `withDensity` needs.) -/
theorem isEquivProbMeasure_withDensity {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    {g : Ω → ℝ} (hpos : ∀ ω, 0 < g ω) (hint : Integrable g P)
    (hsum : ∫ ω, g ω ∂P = 1) :
    IsEquivProbMeasure P (P.withDensity (fun ω ↦ ENNReal.ofReal (g ω))) :=
  isEquivProbMeasure_withDensity_of_isProbabilityMeasure P hint.aemeasurable (ae_of_all _ hpos)
    ⟨by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω ↦ (hpos ω).le), hsum,
        ENNReal.ofReal_one]⟩

/-- **Weighting `P` by the density of the restrictions reproduces `Q` on `m`.** If `Q|m ≪ P|m`, the
measure `P.withDensity (d(Q|m)/d(P|m))` restricts to `Q|m` on `m ≤ m0`. -/
theorem trim_withDensity_rnDeriv_trim {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0)
    {P Q : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure Q] (hQP : Q.trim hm ≪ P.trim hm) :
    (P.withDensity ((Q.trim hm).rnDeriv (P.trim hm))).trim hm = Q.trim hm := by
  rw [trim_withDensity hm (Measure.measurable_rnDeriv _ _), Measure.withDensity_rnDeriv_eq _ _ hQP]

/-- **Change of measure on a sub-σ-algebra.** If `Q|m ≪ P|m`, an `m`-measurable `g` has
`P`-expectation against the density `d(Q|m)/d(P|m)` of the restrictions equal to its
`Q`-expectation. -/
theorem integral_rnDeriv_trim_mul {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0)
    {P Q : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure Q] (hQP : Q.trim hm ≪ P.trim hm)
    {g : Ω → ℝ} (hg : StronglyMeasurable[m] g) :
    ∫ ω, ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal * g ω ∂P = ∫ ω, g ω ∂Q := by
  have hf : Measurable[m] ((Q.trim hm).rnDeriv (P.trim hm)) := Measure.measurable_rnDeriv _ _
  calc ∫ ω, ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal * g ω ∂P
      = ∫ ω, g ω ∂P.withDensity ((Q.trim hm).rnDeriv (P.trim hm)) :=
        (integral_withDensity_eq_integral_toReal_smul (hf.mono hm le_rfl)
          (ae_of_ae_trim hm (Measure.rnDeriv_lt_top _ _)) g).symm
    _ = ∫ ω, g ω ∂(P.withDensity ((Q.trim hm).rnDeriv (P.trim hm))).trim hm :=
        integral_trim hm hg
    _ = ∫ ω, g ω ∂Q := by rw [trim_withDensity_rnDeriv_trim hm hQP, ← integral_trim hm hg]

/-- **An equivalence on a sub-σ-algebra extends to the whole space.** If the probability measure `Q`
has the null sets of `P` among the events of `m ≤ m0`, then `P` weighted by the density
`d(Q|m)/d(P|m)` of the restrictions is a probability measure equivalent to `P` on all of `m0` that
is `Q` on `m`. The density is positive `P`-almost everywhere because `P|m ≪ Q|m`. -/
theorem exists_isEquivProbMeasure_trim_eq {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0)
    {P Q : Measure Ω} [IsFiniteMeasure P] [IsProbabilityMeasure Q] (hQP : Q.trim hm ≪ P.trim hm)
    (hPQ : P.trim hm ≪ Q.trim hm) :
    ∃ Q' : Measure Ω, IsEquivProbMeasure P Q' ∧ Q'.trim hm = Q.trim hm := by
  have hf : Measurable[m] ((Q.trim hm).rnDeriv (P.trim hm)) := Measure.measurable_rnDeriv _ _
  have htrim := trim_withDensity_rnDeriv_trim hm hQP
  refine ⟨P.withDensity ((Q.trim hm).rnDeriv (P.trim hm)),
    ⟨⟨?_⟩, withDensity_absolutelyContinuous _ _, ?_⟩, htrim⟩
  · rw [← trim_measurableSet_eq hm (@MeasurableSet.univ _ m), htrim,
      trim_measurableSet_eq hm (@MeasurableSet.univ _ m), measure_univ]
  · exact withDensity_absolutelyContinuous' (hf.mono hm le_rfl).aemeasurable
      ((ae_of_ae_trim hm (hPQ.ae_le (Measure.rnDeriv_pos hQP))).mono fun _ h ↦ h.ne')

end MathFin
