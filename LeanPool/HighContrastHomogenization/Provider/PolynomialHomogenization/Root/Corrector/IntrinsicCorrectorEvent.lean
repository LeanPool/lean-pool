/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorInvariantEvent
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalLimit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LocalGradientTranslation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorAffineCubeGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalAffineH1sLoc
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Translation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.WeakGradientTranslation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.WeakSolutionTranslation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.Endomorphisms
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleTranslatedGradientIdentification
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineRegularityJointAssembly
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CorrectorEquationFamilyComposition

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.IntrinsicCorrectorEvent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The intrinsic convergence event of the physical corrector family

A coefficient sample carries a corrector family as soon as some triadic
coefficient family represents it on every centered cube, its finite affine
corrections converge locally, and the weak-error row is summable below the
threshold at which reverse Liouville classification identifies translated
gradients.  The datum recorded here is a property of the sample alone: it
mentions no homogenized matrix, no contrast exponent, no rate, no probability
law and no scale.

The event also mentions no *order*.  The good-tail
order at which the row is summable is a field of `RootCorrectorData`, hence
existentially quantified by `RootCorrectorEvent`, so the event, the selected
carrier `rootJointCarrier`, the pushforward core and the marker
`RootPushCorrectorFamilyPredicate` are all independent of it.  The order
survives only where it belongs — in the *supply*, which may choose it after the
contrast exponent `g`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The fixed private exponents -/

/-- The sublinear growth exponent used by the Liouville classification. -/
@[expose]
def rootCorrectorGrowth : ℝ := 1 / 2

theorem rootCorrectorGrowth_pos : (0 : ℝ) < rootCorrectorGrowth := by
  rw [rootCorrectorGrowth]; norm_num

theorem rootCorrectorGrowth_lt_one : rootCorrectorGrowth < 1 := by
  rw [rootCorrectorGrowth]; norm_num

/-! ### The tolerances, at a free good-tail order

The three tolerances below are functions of the
good-tail order `s`, admissible for every `s` in the corrector cone
`0 < s < 1/2`.  Nothing else about the construction changes: the order is
recorded as a *field* of the datum below, not as an index of the event, so the
event, the selected carrier and the pushforward marker stay order-free. -/

/-- The tolerance below which the translated-gradient identification applies
at the good-tail order `s` and the fixed growth exponent. -/
@[expose]
def rootCorrectorIdentificationTolerance (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs2 : s < 1 / 2) : ℝ :=
  Classical.choose
    (exists_scalarIdentityGoodTailLiouvilleTranslatedGradientIdentificationConstant
      d s rootCorrectorGrowth hs hs2 rootCorrectorGrowth_lt_one)

/-- The tolerance below which a good tail already produces the local Cauchy
property and the intrinsic normalization of every slope. -/
@[expose]
def rootCorrectorSlopeTolerance (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) : ℝ :=
  Classical.choose
    (exists_scalarIdentityGoodTailIntrinsicSlopeThreshold d s hs hs2)

/-- The tolerance used by the construction, at the order `s`. -/
@[expose]
def rootCorrectorTolerance (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) : ℝ :=
  min (rootCorrectorIdentificationTolerance d s hs hs2)
    (rootCorrectorSlopeTolerance d s hs hs2)

theorem rootCorrectorIdentification_spec (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs2 : s < 1 / 2) :
    rootCorrectorIdentificationTolerance d s hs hs2 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) (rootCorrectorIdentificationTolerance d s hs hs2) →
        ScalarIdentityGoodTail a s delta n →
        ∀ (PhiTarget : Vec d → NormalizedLocalH1Carrier d),
          IsFiniteAffineCorrectionJointLocalEquation a PhiTarget →
          ∀ {b : CoeffField d}, IsAELocallyUniformlyElliptic b →
            (∀ q : ℕ,
              Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
                =ᵐ[volume.restrict (localGradientCube d q)] b) →
            ∀ (PhiSource : NormalizedLocalH1Carrier d) (e t : Vec d)
              (sRow N : ℝ) (q0 : ℕ),
              0 < sRow → sRow < 1 / 2 →
              HasIntrinsicNormalizedSlope e PhiSource →
              (∀ e' : Vec d,
                HasIntrinsicNormalizedSlope e' (PhiTarget e')) →
              (∀ q : ℕ, q0 ≤ q →
                cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                    (originCube d (q : ℤ)) sRow
                    (fun x ↦ e + PhiSource.globalGradientRepresentative x) ≤ N) →
              ∀ {v : Vec d → ℝ},
                MemLiouvilleClass b rootCorrectorGrowth v
                  (fun x ↦ e + PhiSource.globalGradientRepresentative (x + t)) →
                (fun x ↦ PhiSource.globalGradientRepresentative (x + t))
                  =ᵐ[volume] (PhiTarget e).globalGradientRepresentative :=
  Classical.choose_spec
    (exists_scalarIdentityGoodTailLiouvilleTranslatedGradientIdentificationConstant
      d s rootCorrectorGrowth hs hs2 rootCorrectorGrowth_lt_one)

theorem rootCorrectorSlope_spec (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) :
    rootCorrectorSlopeTolerance d s hs hs2 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) (rootCorrectorSlopeTolerance d s hs hs2) →
        ScalarIdentityGoodTail a s delta n →
        ∀ e : Vec d,
          ∃ hloc : FiniteAffineCorrectionLocalCauchy a,
            HasIntrinsicNormalizedSlope e
              (finiteAffineCorrectionJointLocalLimit a hloc e) :=
  Classical.choose_spec
    (exists_scalarIdentityGoodTailIntrinsicSlopeThreshold d s hs hs2)

theorem rootCorrectorTolerance_pos (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) :
    0 < rootCorrectorTolerance d s hs hs2 :=
  lt_min (rootCorrectorIdentification_spec d s hs hs2).1.1
    (rootCorrectorSlope_spec d s hs hs2).1.1

theorem mem_identificationTolerance_of_mem [NeZero d] {s : ℝ} {hs : 0 < s}
    {hs2 : s < 1 / 2} {delta : ℝ}
    (h : delta ∈ Ioc (0 : ℝ) (rootCorrectorTolerance d s hs hs2)) :
    delta ∈ Ioc (0 : ℝ) (rootCorrectorIdentificationTolerance d s hs hs2) :=
  ⟨h.1, h.2.trans (min_le_left _ _)⟩

theorem mem_slopeTolerance_of_mem [NeZero d] {s : ℝ} {hs : 0 < s}
    {hs2 : s < 1 / 2} {delta : ℝ}
    (h : delta ∈ Ioc (0 : ℝ) (rootCorrectorTolerance d s hs hs2)) :
    delta ∈ Ioc (0 : ℝ) (rootCorrectorSlopeTolerance d s hs hs2) :=
  ⟨h.1, h.2.trans (min_le_right _ _)⟩

/-- A summable weak-error row below the tolerance already yields local
convergence of the finite affine corrections together with the intrinsic
normalization of every slope. -/
theorem exists_cauchy_intrinsic_of_goodTail [NeZero d] {s : ℝ} (hs : 0 < s)
    (hs2 : s < 1 / 2)
    (aFin : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ)
    (hmem : delta ∈ Ioc (0 : ℝ) (rootCorrectorTolerance d s hs hs2))
    (hgood : ScalarIdentityGoodTail aFin s delta n) :
    ∃ hCauchy : FiniteAffineCorrectionLocalCauchy aFin,
      ∀ e : Vec d, HasIntrinsicNormalizedSlope e
        (finiteAffineCorrectionJointLocalLimit aFin hCauchy e) := by
  obtain ⟨hbase, _hbaseSlope⟩ :=
    (rootCorrectorSlope_spec d s hs hs2).2 aFin delta n
      (mem_slopeTolerance_of_mem hmem) hgood 0
  refine ⟨hbase, fun e ↦ ?_⟩
  obtain ⟨hloc, hslope⟩ :=
    (rootCorrectorSlope_spec d s hs hs2).2 aFin delta n
      (mem_slopeTolerance_of_mem hmem) hgood e
  have hproof : hloc = hbase := Subsingleton.elim _ _
  simpa only [hproof] using hslope

/-! ## The zero carrier -/

/-- The zero normalized local carrier, used off the convergence event. -/
@[expose]
def zeroNormalizedCarrier (d : ℕ) : NormalizedLocalH1Carrier d where
  value := 0
  gradient := 0
  graph n := by
    have hzero :
        (LocalValueCarrier.component (0 : LocalValueCarrier d) n,
            LocalGradientCarrier.component (0 : LocalGradientCarrier d) n) =
          (0, 0) := rfl
    rw [hzero]
    exact Submodule.zero_mem _
  unitMeanZero := by
    have hzero :
        LocalValueCarrier.component (0 : LocalValueCarrier d) 0 = 0 := rfl
    rw [hzero, map_zero]

/-! ## The intrinsic datum -/

/-- Everything the construction reads off one coefficient sample: a triadic
family representing it, local convergence of the finite affine corrections,
a summable weak-error row below the identification tolerance, the intrinsic
normalization of every slope, and the two rows of the limit: the scale-linear
value growth and the weak gradient row. -/
structure RootCorrectorData (d : ℕ) [NeZero d] (a : CoeffSpace d) where
  /-- **The good-tail order.**  The order at which
  the weak-error row of this datum is read is a *field*, not an index: it is
  existentially quantified by `RootCorrectorEvent` below, so neither the event,
  nor the selected carrier, nor the pushforward marker mentions it.  Any order
  in the corrector cone `0 < s < 1/2` is admitted, and
  `CorrectorComposition.jointLocalLimit_eq_of_aeeq` shows that data of *different* orders
  for the same sample carry literally the same joint local limit — which is
  what makes the carrier well defined without an index. -/
  order : ℝ
  order_pos : 0 < order
  order_lt : order < 1 / 2
  /-- A triadic coefficient family for the sample. -/
  aFin : Book.Ch02.TriadicCoeffFamily d
  /-- Its finite affine corrections converge locally at every slope. -/
  hCauchy : FiniteAffineCorrectionLocalCauchy aFin
  /-- The weak-error tolerance. -/
  tolerance : ℝ
  /-- The generation at which the weak-error row is read. -/
  start : ℤ
  tolerance_mem :
    tolerance ∈ Ioc (0 : ℝ) (rootCorrectorTolerance d order order_pos order_lt)
  goodTail : ScalarIdentityGoodTail aFin order tolerance start
  coeff : ∀ q : ℕ,
    Book.Ch03.publicCoeffField (originCube d (q : ℤ)) aFin
      =ᵐ[volume.restrict (localGradientCube d q)] fun x ↦ a.1 x
  /-- **The all-cube representation.**  The reference family
  represents the sample on **every** triadic cube, not only on the origin
  cubes, and against `coeffOn` rather than `publicCoeffField`.  The converter
  that supplies the datum proves this *pointwise*
  (`exists_shiftedNormalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow`'s
  `hcoeffRef`); keeping it in the a.e. form is enough for every consumer, and
  it is what makes the selected datum's family a.e. equal to the certificate's
  exact-gauge family as a `Book.Ch02.TriadicCoeffFamily.AEEq`. -/
  coeffAll : ∀ Q : TriadicCube d,
    (aFin.coeffOn Q).toCoeffField =ᵐ[volume] fun x ↦ a.1 x
  intrinsic : ∀ e : Vec d,
    HasIntrinsicNormalizedSlope e
      (finiteAffineCorrectionJointLocalLimit aFin hCauchy e)
  valueGrowth : ∀ e : Vec d, ∃ (q0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ q : ℕ, q0 ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2
          (finiteAffineCorrectionJointLocalLimit aFin hCauchy
            e).globalValueRepresentative ≤ C * (3 : ℝ) ^ q
  /-- **The weak gradient row.**  The scale-uniform datum of the corrector
  gradient is its weak norm — the scale-normalized negative Besov norm of the
  affine-plus-corrector field — read at the datum's own order.  It is the row
  the paper's corrector estimates publish, and it is law-free: no pointwise
  ellipticity pair enters it. -/
  gradientGrowth : ∀ e : Vec d, ∃ (q0 : ℕ) (N : ℝ), 0 ≤ N ∧
    ∀ q : ℕ, q0 ≤ q →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (q : ℤ)) order
          (fun x ↦ e + (finiteAffineCorrectionJointLocalLimit aFin hCauchy
            e).globalGradientRepresentative x) ≤ N

/-- The intrinsic convergence event. -/
@[expose]
def RootCorrectorEvent (d : ℕ) [NeZero d] (a : CoeffSpace d) : Prop :=
  Nonempty (RootCorrectorData d a)

/-- The intrinsic datum is built from a summable weak-error row below the
tolerance, the coefficient representation, and the two rows of the limit; local
convergence and intrinsic normalization are discharged from the weak-error row
itself. -/
theorem rootCorrectorEvent_of_goodTail [NeZero d] {a : CoeffSpace d} {s : ℝ}
    (hs : 0 < s) (hs2 : s < 1 / 2)
    (aFin : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ)
    (hmem : delta ∈ Ioc (0 : ℝ) (rootCorrectorTolerance d s hs hs2))
    (hgood : ScalarIdentityGoodTail aFin s delta n)
    (hcoeff : ∀ q : ℕ,
      Book.Ch03.publicCoeffField (originCube d (q : ℤ)) aFin
        =ᵐ[volume.restrict (localGradientCube d q)] fun x ↦ a.1 x)
    (hcoeffAll : ∀ Q : TriadicCube d,
      (aFin.coeffOn Q).toCoeffField =ᵐ[volume] fun x ↦ a.1 x)
    (hvalue : ∀ (hC : FiniteAffineCorrectionLocalCauchy aFin) (e : Vec d),
      ∃ (q0 : ℕ) (C : ℝ), 0 ≤ C ∧
        ∀ q : ℕ, q0 ≤ q →
          cubeLpNorm (originCube d (q : ℤ)) 2
              (finiteAffineCorrectionJointLocalLimit aFin hC
                e).globalValueRepresentative ≤ C * (3 : ℝ) ^ q)
    (hgradient : ∀ (hC : FiniteAffineCorrectionLocalCauchy aFin) (e : Vec d),
      ∃ (q0 : ℕ) (N : ℝ), 0 ≤ N ∧
        ∀ q : ℕ, q0 ≤ q →
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d (q : ℤ)) s
              (fun x ↦ e + (finiteAffineCorrectionJointLocalLimit aFin hC
                e).globalGradientRepresentative x) ≤ N) :
    RootCorrectorEvent d a := by
  obtain ⟨hCauchy, hintrinsic⟩ :=
    exists_cauchy_intrinsic_of_goodTail hs hs2 aFin delta n hmem hgood
  exact ⟨⟨s, hs, hs2, aFin, hCauchy, delta, n, hmem, hgood, hcoeff, hcoeffAll,
    hintrinsic, hvalue hCauchy, hgradient hCauchy⟩⟩

/-! ## The selected family -/

/-- The datum selected on the intrinsic event. -/
@[expose]
def selectedRootCorrectorData [NeZero d] (a : CoeffSpace d)
    (h : RootCorrectorEvent d a) : RootCorrectorData d a :=
  Classical.choice h

/-- The event-totalized normalized carrier family: the selected joint local
limit on the event, the zero carrier off it.  The selection precedes the
slope. -/
@[expose]
def rootJointCarrier (d : ℕ) [NeZero d] (e : Vec d) (a : CoeffSpace d) :
    NormalizedLocalH1Carrier d := by
  classical
  exact if h : RootCorrectorEvent d a then
    finiteAffineCorrectionJointLocalLimit (selectedRootCorrectorData a h).aFin
      (selectedRootCorrectorData a h).hCauchy e
  else zeroNormalizedCarrier d

theorem rootJointCarrier_of_event [NeZero d] (e : Vec d) {a : CoeffSpace d}
    (h : RootCorrectorEvent d a) :
    rootJointCarrier d e a =
      finiteAffineCorrectionJointLocalLimit (selectedRootCorrectorData a h).aFin
        (selectedRootCorrectorData a h).hCauchy e := by
  simp only [rootJointCarrier, dite_eq_left h]

/-! ## Slope linearity of the selected family -/

theorem rootJointCarrier_add [NeZero d] (e e' : Vec d) {a : CoeffSpace d}
    (h : RootCorrectorEvent d a) :
    rootJointCarrier d (e + e') a =
      NormalizedLocalH1Carrier.addCarrier (rootJointCarrier d e a)
        (rootJointCarrier d e' a) := by
  simp only [rootJointCarrier_of_event _ h]
  exact finiteAffineCorrectionJointLocalLimit_add _ _ e e'

theorem rootJointCarrier_smul [NeZero d] (c : ℝ) (e : Vec d)
    {a : CoeffSpace d} (h : RootCorrectorEvent d a) :
    rootJointCarrier d (c • e) a =
      NormalizedLocalH1Carrier.smulCarrier c (rootJointCarrier d e a) := by
  simp only [rootJointCarrier_of_event _ h]
  exact finiteAffineCorrectionJointLocalLimit_smul _ _ c e

/-! ## The joint local equation of the selected family -/

/-- Every selected joint local limit satisfies the named joint local
equation. -/
theorem finiteAffineCorrectionJointLocalLimit_isJointLocalEquation
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) :
    IsFiniteAffineCorrectionJointLocalEquation a
      (finiteAffineCorrectionJointLocalLimit a hCauchy) := by
  constructor
  · exact finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy
  · intro e q
    simpa only [finiteAffineCorrectionJointLocalH1] using
      finiteAffineCorrectionJointLocalH1_isHarmonic a hCauchy e q

/-- On the intrinsic event the selected family is a global weak solution of
the corrector equation for the sample, and its canonical representatives are
a weak-gradient pair. -/
theorem rootJointCarrier_equation [NeZero d] {a : CoeffSpace d}
    (h : RootCorrectorEvent d a) (e : Vec d) :
    HasWeakGradientOn Set.univ
        (rootJointCarrier d e a).globalValueRepresentative
        (rootJointCarrier d e a).globalGradientRepresentative ∧
      IsWeakSolutionOn (fun x ↦ a.1 x) Set.univ
        (fun x ↦ e + (rootJointCarrier d e a).globalGradientRepresentative x) := by
  refine ⟨?_, ?_⟩
  · exact (rootJointCarrier d e a).hasWeakGradientOn_globalRepresentatives
  · have hEquation :=
      (finiteAffineCorrectionJointLocalLimit_isJointLocalEquation
        (selectedRootCorrectorData a h).aFin
        (selectedRootCorrectorData a h).hCauchy).isWeakSolutionOn_global
          (selectedRootCorrectorData a h).coeff e
    simpa only [rootJointCarrier_of_event e h] using hEquation

end

end Root
end HighContrast
end HCPolySupport
