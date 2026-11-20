/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartMultiplierDescent
public import LeanPool.FastDynamo.Global.TorusChartProjectionTransport

/-!
# The chart action bridge with abstract coefficient agreement

The proof of `lem:parametrix-error` uses the statement "the coefficients of the horizontal operator
on `T²` and the operator on `ℝ²` for the selected cell agree on `supp ψ_n`, since the added axial
velocity profile in the selected cell of `T²` is constant there and all other cells are disjoint" to
identify the torus operator `A_{ε,K_n}` with the selected whole-plane operator `A^{(n)}_{ε,n}` on
fields living inside the chart.

The argument of §7 is parametric in the transverse velocity `u`, so this module states that
identity with the coefficient agreement taken as a **hypothesis**:

* `ChartCoefficientAgreement s u v a` — on the set `s ⊆ ℝ²`, the two transverse velocity
  coordinates, the axial coordinate up to the constant `a`, and the two velocity gradient
  coefficients of the torus velocity `u` agree with those of the whole-plane record `v`;
* `H2StateSupportedIn s b` — the value and the two first weak derivatives of the chart-supported
  whole-plane jet `b` vanish off `s`.

Under those two hypotheses the three-component action identity

`reducedInductionAction u ε K (chart b) = wholePlaneToTorusL2 (A^{(n)}_{ε,K,a} b)`

holds verbatim, and its two-component conjugate follows by the fibre calculus of
`Global/WholePlaneHorizontalFibre.lean` and `Global/TorusChartC2Transfer.lean`.  The proof
combines the four termwise statements (diffusion, transverse transport, axial transport,
stretching), built from the quotient-safe multiplication atoms of
`Global/TorusChartMultiplierDescent.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set

namespace TorusChartActionBridge

open TorusChartMultiplierDescent
open TorusChartH2
open TorusChartL2
open WholePlaneAESupport

/-! ## The two hypotheses -/

/-- The value and the two stored first derivatives of a chart-supported whole-plane `H²` jet
vanish almost everywhere off `s`.  Second derivatives need no support hypothesis: diffusion has
constant coefficients. -/
structure H2StateSupportedIn (s : Set WholePlane) (b : ChartSupportedWholePlaneC3H2) : Prop where
  /-- The physical value vanishes off `s`. -/
  value : IsAEL2SupportedIn s (wholePlaneH2Embedding C3 b.1)
  /-- Each stored first weak derivative vanishes off `s`. -/
  firstDerivative : ∀ j : Fin 2,
    IsAEL2SupportedIn s (wholePlaneH2FirstDerivative C3 j b.1)

/-- Agreement, on `s` read through the chart, between a transverse `W^{1,∞}` velocity `u` and a
whole-plane velocity record `v` whose axial coordinate is offset by the constant `a`.  This is
the coefficient agreement on `supp ψ_n` of the proof of `lem:parametrix-error` in hypothesis
form. -/
structure ChartCoefficientAgreement (s : Set WholePlane) (u : TransverseRealW1Inf)
    (v : WholePlaneVelocityCoefficients) (a : ℝ) : Prop where
  /-- The two transverse velocity coordinates agree on `s`. -/
  transverseValue : ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
    torusWholePlaneRepresentative q ∈ s →
      (transverseW1InfComplexValueCoordLInf j.castSucc u : TransverseTorus → ℂ) q =
        (wholePlaneCoordLInf j.castSucc v.value : WholePlane → ℂ)
          (torusWholePlaneRepresentative q)
  /-- The axial velocity coordinates agree on `s` up to the constant plateau value `a`. -/
  axialValue : ∀ᵐ q ∂transverseMeasure,
    torusWholePlaneRepresentative q ∈ s →
      (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u : TransverseTorus → ℂ) q =
        (wholePlaneCoordLInf (2 : Fin 3) v.value : WholePlane → ℂ)
          (torusWholePlaneRepresentative q) + (a : ℂ)
  /-- The two stored velocity gradient coefficients agree on `s`. -/
  deriv : ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
    torusWholePlaneRepresentative q ∈ s →
      (transverseW1InfComplexDerivLInf j u : TransverseTorus → C3) q =
        (v.deriv j : WholePlane → C3) (torusWholePlaneRepresentative q)

/-! ## The four terms -/

variable {s : Set WholePlane} {u : TransverseRealW1Inf}
  {v : WholePlaneVelocityCoefficients} {a : ℝ}
  {b : ChartSupportedWholePlaneC3H2}

/-- Transverse transport intertwines through the chart on a state supported where the
coefficients agree. -/
theorem reducedInductionTransport_chart
    (hagree : ChartCoefficientAgreement s u v a) (hb : H2StateSupportedIn s b) :
    reducedInductionTransport u (wholePlaneChartToTransverseH2 b) =
      wholePlaneToTorusL2 (wholePlaneLocalTransport v b.1) := by
  rw [reducedInductionTransport_apply, wholePlaneLocalTransport_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hatom :
      scalarVectorMulTransverse (transverseW1InfComplexValueCoordLInf j.castSucc u)
          (wholePlaneToTorusL2 (wholePlaneH2FirstDerivative C3 j b.1)) =
        wholePlaneToTorusL2 (scalarVectorMulL2 (E := C3) volume
          (wholePlaneCoordLInf j.castSucc v.value)
          (wholePlaneH2FirstDerivative C3 j b.1)) :=
    scalarVectorMulTransverse_wholePlaneToTorusL2_eq
      (s := s) (aT := transverseW1InfComplexValueCoordLInf j.castSucc u)
      (aW := wholePlaneCoordLInf j.castSucc v.value)
      (f := wholePlaneH2FirstDerivative C3 j b.1)
      (hagree.transverseValue j) (hb.firstDerivative j)
  rw [transverseDerivFromH2_wholePlaneChartToTransverseH2, chartFirstDerivativeL2_apply,
    hatom]

/-- Axial transport intertwines as the whole-plane axial transport plus the constant axial
scalar `2π i K a`. -/
theorem reducedInductionAxialTransport_chart (K : ℤ)
    (hagree : ChartCoefficientAgreement s u v a) (hb : H2StateSupportedIn s b) :
    reducedInductionAxialTransport u K (wholePlaneChartToTransverseH2 b) =
      wholePlaneToTorusL2
          (wholePlaneLocalAxialTransport v (wholePlaneAxialWavenumber K) b.1) +
        (axialMultiplier K * (a : ℂ)) •
          wholePlaneToTorusL2 (wholePlaneH2Embedding C3 b.1) := by
  have hlocalAxial :
      axialMultiplier K • wholePlaneToTorusL2
          (scalarVectorMulL2 (E := C3) volume (wholePlaneCoordLInf (2 : Fin 3) v.value)
            (wholePlaneH2Embedding C3 b.1)) =
        wholePlaneToTorusL2
          (wholePlaneLocalAxialTransport v (wholePlaneAxialWavenumber K) b.1) := by
    rw [wholePlaneLocalAxialTransport_apply, map_smul,
      axialMultiplier_eq_i_mul_wholePlaneAxialWavenumber]
  have hscalar :
      scalarVectorMulTransverse (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u)
          (wholePlaneToTorusL2 (wholePlaneH2Embedding C3 b.1)) =
        wholePlaneToTorusL2 (scalarVectorMulL2 (E := C3) volume
            (wholePlaneCoordLInf (2 : Fin 3) v.value) (wholePlaneH2Embedding C3 b.1)) +
          (a : ℂ) • wholePlaneToTorusL2 (wholePlaneH2Embedding C3 b.1) :=
    scalarVectorMulTransverse_wholePlaneToTorusL2_eq_add_const
      (s := s) (aT := transverseW1InfComplexValueCoordLInf (2 : Fin 3) u)
      (aW := wholePlaneCoordLInf (2 : Fin 3) v.value)
      (f := wholePlaneH2Embedding C3 b.1) (a : ℂ)
      hagree.axialValue hb.value
  have hbase : reducedInductionAxialTransport u K (wholePlaneChartToTransverseH2 b) =
      axialMultiplier K • scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u)
        (wholePlaneToTorusL2 (wholePlaneH2Embedding C3 b.1)) := rfl
  calc reducedInductionAxialTransport u K (wholePlaneChartToTransverseH2 b)
      = axialMultiplier K • (wholePlaneToTorusL2
            (scalarVectorMulL2 (E := C3) volume (wholePlaneCoordLInf (2 : Fin 3) v.value)
              (wholePlaneH2Embedding C3 b.1)) +
          (a : ℂ) • wholePlaneToTorusL2 (wholePlaneH2Embedding C3 b.1)) :=
        hbase.trans (congrArg (fun x : TransverseC3L2 ↦ axialMultiplier K • x) hscalar)
    _ = axialMultiplier K • wholePlaneToTorusL2
            (scalarVectorMulL2 (E := C3) volume (wholePlaneCoordLInf (2 : Fin 3) v.value)
              (wholePlaneH2Embedding C3 b.1)) +
          axialMultiplier K • ((a : ℂ) • wholePlaneToTorusL2
            (wholePlaneH2Embedding C3 b.1)) := smul_add _ _ _
    _ = wholePlaneToTorusL2
            (wholePlaneLocalAxialTransport v (wholePlaneAxialWavenumber K) b.1) +
          axialMultiplier K • ((a : ℂ) • wholePlaneToTorusL2
            (wholePlaneH2Embedding C3 b.1)) :=
        congrArg (fun t : TransverseC3L2 ↦ t + axialMultiplier K •
          ((a : ℂ) • wholePlaneToTorusL2 (wholePlaneH2Embedding C3 b.1))) hlocalAxial
    _ = _ := congrArg (fun t : TransverseC3L2 ↦ wholePlaneToTorusL2
          (wholePlaneLocalAxialTransport v (wholePlaneAxialWavenumber K) b.1) + t)
        (smul_smul (axialMultiplier K) (a : ℂ)
          (wholePlaneToTorusL2 (wholePlaneH2Embedding C3 b.1)))

/-- Stretching intertwines because both stored velocity gradient coefficients agree on the
support of the state value. -/
theorem reducedInductionStretching_chart
    (hagree : ChartCoefficientAgreement s u v a) (hb : H2StateSupportedIn s b) :
    reducedInductionStretching u (wholePlaneChartToTransverseH2 b) =
      wholePlaneToTorusL2 (wholePlaneLocalStretching v b.1) := by
  rw [reducedInductionStretching_apply, wholePlaneLocalStretching_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hatom :
      vectorScalarMulTransverse (transverseW1InfComplexDerivLInf j u)
          (transverseCoordL2 j.castSucc (wholePlaneToTorusL2
            (wholePlaneH2Embedding C3 b.1))) =
        wholePlaneToTorusL2 (vectorScalarMulL2 (E := C3) volume (v.deriv j)
          (wholePlaneCoordL2 j.castSucc (wholePlaneH2Embedding C3 b.1))) :=
    vectorScalarMulTransverse_wholePlaneToTorusL2_eq
      (s := s) (aT := transverseW1InfComplexDerivLInf j u) (aW := v.deriv j)
      (f := wholePlaneH2Embedding C3 b.1) j.castSucc
      (hagree.deriv j) hb.value
  rw [transverseH2Embedding_wholePlaneChartToTransverseH2, chartValueL2_apply, hatom]

/-! ## The action identity -/

/-- **The chart action bridge.**  On a chart-supported whole-plane `H²` jet whose value and first
derivatives live where the coefficients agree, the torus action of `A_{ε,K}` on the chart image
is the chart image of the selected whole-plane action `A^{(n)}_{ε,K,a}`.  This is the
identification in the proof of `lem:parametrix-error`, with the coefficient agreement as a
hypothesis. -/
theorem reducedInductionAction_chart (epsilon : ℝ) (K : ℤ)
    (hagree : ChartCoefficientAgreement s u v a) (hb : H2StateSupportedIn s b) :
    reducedInductionAction u epsilon K (wholePlaneChartToTransverseH2 b) =
      wholePlaneToTorusL2 (selectedWholePlaneInductionAction v epsilon K a b.1) := by
  have hdiff := reducedInductionDiffusion_wholePlaneChartToTransverseH2 K b
  have htransport := reducedInductionTransport_chart hagree hb
  have haxial := reducedInductionAxialTransport_chart K hagree hb
  have hstretch := reducedInductionStretching_chart hagree hb
  have hshift : selectedWholePlaneAxialShift K a b.1 =
      (axialMultiplier K * (a : ℂ)) • wholePlaneH2Embedding C3 b.1 := rfl
  change (epsilon : ℂ) • reducedInductionDiffusion K (wholePlaneChartToTransverseH2 b) -
      reducedInductionTransport u (wholePlaneChartToTransverseH2 b) -
      reducedInductionAxialTransport u K (wholePlaneChartToTransverseH2 b) +
      reducedInductionStretching u (wholePlaneChartToTransverseH2 b) = _
  simp only [hdiff, htransport, haxial, hstretch]
  change _ = wholePlaneToTorusL2
    ((epsilon : ℂ) • wholePlaneLocalDiffusion (wholePlaneAxialWavenumber K) b.1 -
        wholePlaneLocalTransport v b.1 -
        wholePlaneLocalAxialTransport v (wholePlaneAxialWavenumber K) b.1 +
        wholePlaneLocalStretching v b.1 -
      selectedWholePlaneAxialShift K a b.1)
  rw [hshift]
  simp only [map_add, map_sub, map_smul]
  abel

end TorusChartActionBridge

end

end FastDynamo
