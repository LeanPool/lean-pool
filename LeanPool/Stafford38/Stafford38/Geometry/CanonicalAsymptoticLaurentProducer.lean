/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.CanonicalSupportVanishingReduction
public import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalResidueExtension
public import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveDivisorOrderGap
public import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveEquationFormalChart
public import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveTangentInclusion


/-!
# The completed-boundary consumer for the Laurent producer

This file isolates the exact local certificate consumed by the asymptotic
Laurent step.  A certificate contains

* a one-parameter completed projective chart `q`;
* a finite homogeneous family of projective equations, with their vanishing
  at `q` and containment of the target affine ideal after dehomogenization;
* divisor-tangent columns `Z` and the strict projective order-gap data;
* one fixed derivative-compatible geometric witness `tau`, `C`, `ell`; and
* the one genuinely geometric comparison still needed by the consumer:
  the Zariski tangent space is *contained* in the span built from that same
  fixed transverse column `tau`.

The main theorem below turns this certificate into the exact output required
by `CanonicalAsymptoticLaurentProducer`.  It does not assume support
vanishing, a finite affine point on the axis, tangent-space equality, or a
heuristic derivative limit.  The certificate is therefore a non-circular
consumer interface, not a disguised proof of its own existence.

What is deliberately not asserted here is the global production theorem that
constructs such a certificate from normalization and projective closure.  In
particular, a DVR with residue field `K` naturally completes to `K[[X]]`;
specializing that chart to `k[[X]]`, constructing homogeneous equations, and
proving the tangent-span inclusion are separate geometric obligations.
`CanonicalBoundaryChartProduction` records exactly that remaining obligation.
-/

public section

namespace Stafford38.Geometry.CanonicalAsymptoticLaurentProducer

open Stafford38
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.ProjectiveTangentInclusion
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryRetractionSpecialization
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

/-! ## The exact local certificate -/

/--
A completed one-parameter projective boundary chart for an affine ideal in
`m` variables.

The finite equation and tangent-column indices are natural numbers so that
the certificate is entirely first-order data over the pinned Lean library;
no hidden finiteness or choice of an equation family is left to an
elaboration-side typeclass.

The formal tangent data are one fixed geometric witness.  In particular,
`tangent_inclusion` refers to the stored derivative-compatible transverse
column `tau`; it does not quantify over alternative, possibly nongeometric,
split columns.  The inclusion remains intentionally one-sided: it asks for
the actual Zariski tangent space to lie in the supplied span and never assumes
equality.
-/
abbrev CompletedProjectiveBoundaryChart
    (k : Type u) [Field k]
    (m : ℕ) (hm : 0 < m) (I : Ideal (MvPolynomial (Fin m) k)) :=
  LaurentConormalResidueExtension.CompletedProjectiveBoundaryChartOver
    (k := k) (K := k) m hm I

/-! ## Local consumer theorem -/

/--
The completed-DVR/projective certificate supplies the Laurent conormal axis.

The proof has four explicit interfaces: the projective order-gap theorem
constructs the formal annihilating row; homogeneous equation vanishing gives
the base-equation condition after dehomogenization; tangent inclusion feeds
the weaker Laurent conormal bridge; and the axis equation identifies the
regular fibre residue with the pure first momentum direction.
-/
theorem exists_conormalAxis_of_completedProjectiveBoundaryChart
    {k : Type u} [Field k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I) :
    ∃ (y : Fin m → LaurentSeries k)
      (xi : Fin m → PowerSeries k),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m))) ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  simpa [LaurentConormalResidueExtension.groundEquationConormalLocus,
    LaurentConormalResidueExtension.groundPolynomialMap,
    LaurentConormalResidueExtension.groundLaurentMap, scalarPolynomialMap] using
      LaurentConormalResidueExtension.exists_conormalAxis_of_completedProjectiveBoundaryChartOver
        (K := k) hm I W

/-! ## The remaining global production obligation -/

/--
The exact global theorem still needed to obtain the producer from boundary
geometry.  It asks normalization/projective-closure arguments to return the
certificate above for the canonical reduced base ideal, but it does not put
the desired support-vanishing conclusion among the certificate fields.

This is a definition rather than an axiom.  Consequently a caller must still
prove the actual completion, homogeneous-equation, and tangent-inclusion
construction; the adapter theorem above cannot discharge those obligations
by circular reasoning.
-/
def CanonicalBoundaryChartProduction : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N →
    IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
    Disjoint
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) →
    (orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N)).Nonempty →
    Nonempty (CompletedProjectiveBoundaryChart k (n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)))

/--
The exact adapter from global boundary-chart production to the canonical
Laurent producer.  All support hypotheses are used only to request a chart;
the chart-to-conormal proof itself has no support-vanishing premise.
-/
theorem canonicalAsymptoticLaurentProducer_of_boundaryChartProduction
    (hproduction : CanonicalBoundaryChartProduction.{u}) :
    CanonicalAsymptoticLaurentProducer.{u} := by
  intro k _ _ _ n N d hN hd hdisjoint hnonempty
  obtain ⟨W⟩ :=
    hproduction k n N d hN hd hdisjoint hnonempty
  obtain ⟨y, xi, hmem, haxis⟩ :=
    exists_conormalAxis_of_completedProjectiveBoundaryChart
      (k := k) (m := n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)) W
  exact ⟨y, xi, hmem, haxis⟩


end

end Stafford38.Geometry.CanonicalAsymptoticLaurentProducer
