/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Fourier.PeriodicH2

/-!
# Transporting torus `L²` data along the Haar/volume identification

`UnitAddTorus` carries two definitionally distinct measures: the ambient
`volume` used throughout this development and the additive Haar measure
`torusHaarMeasure` used by Mathlib's monomial Fourier basis.  The two agree
(`volume_unitAddTorus_eq_haar`), so every statement about the Mathlib basis
transports to the physical one along a `cast`.

This module collects the transport lemmas.  They are shared by the
product-torus Fourier analysis and by the weak-Leibniz theory, which is why
they live in their own module instead of being restated in each consumer.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- Casting a Hilbert basis along an equality of measures commutes with
evaluating the basis at an index. -/
lemma castHilbertBasis_apply {α I : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (h : μ = ν)
    (b : HilbertBasis I ℂ (Lp ℂ 2 ν)) (i : I) :
    (cast (congrArg (fun ρ : Measure α =>
      HilbertBasis I ℂ (Lp ℂ 2 ρ)) h.symm) b) i =
      cast (congrArg (fun ρ : Measure α => ↥(Lp ℂ 2 ρ)) h.symm) (b i) := by
  subst ν
  rfl

/-- Casting the `L²` class of a continuous function along an equality of
measures gives the `L²` class taken with respect to the other measure. -/
lemma castContinuousMapToLp {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α]
    [SecondCountableTopologyEither α ℂ] [CompactSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : μ = ν) (f : C(α, ℂ)) :
    cast (congrArg (fun ρ : Measure α => ↥(Lp ℂ 2 ρ)) h.symm)
      (ContinuousMap.toLp 2 ν ℂ f) =
        ContinuousMap.toLp 2 μ ℂ f := by
  subst ν
  rfl

/-- Transport of a transverse Haar-`L²` field to the physical (volume) `L²`
space. -/
def transverseHaarToPhysical
    (f : Lp ℂ 2 (torusHaarMeasure (Fin 2))) : TransverseScalarL2 :=
  cast (congrArg (fun μ : Measure TransverseTorus => ↥(Lp ℂ 2 μ))
    (volume_unitAddTorus_eq_haar (d := Fin 2)).symm) f

/-- The transverse Fourier basis is the transported Mathlib monomial
basis. -/
lemma transverseBasis_eq_haarMonomial (n : TransverseFrequency) :
    transverseScalarFourierBasis n =
      transverseHaarToPhysical
        (UnitAddTorus.mFourierBasis (d := Fin 2) n) := by
  apply eq_of_heq
  unfold transverseScalarFourierBasis transverseHaarToPhysical
  exact heq_of_eq (castHilbertBasis_apply
    (volume_unitAddTorus_eq_haar (d := Fin 2))
    (UnitAddTorus.mFourierBasis (d := Fin 2)) n)

/-- The physical `L²` class of the transverse Fourier monomial of a given
frequency. -/
def transversePhysicalMonomial (n : TransverseFrequency) :
    TransverseScalarL2 :=
  ContinuousMap.toLp 2 transverseMeasure ℂ (UnitAddTorus.mFourier n)

/-- The transverse Fourier basis vector is the physical `L²` class of the
corresponding monomial. -/
lemma transverseBasis_eq_physicalMonomial (n : TransverseFrequency) :
    transverseScalarFourierBasis n = transversePhysicalMonomial n := by
  let _ : IsFiniteMeasure (torusHaarMeasure (Fin 2)) := by
    rw [← volume_unitAddTorus_eq_haar]
    infer_instance
  rw [transverseBasis_eq_haarMonomial, UnitAddTorus.coe_mFourierBasis]
  exact castContinuousMapToLp
    (volume_unitAddTorus_eq_haar (d := Fin 2))
    (UnitAddTorus.mFourier n)

end

end FastDynamo
