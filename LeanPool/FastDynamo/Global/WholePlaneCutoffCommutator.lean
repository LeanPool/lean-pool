/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartMultiplierDescent

/-!
# The whole-plane cut-off commutator of the local action

For a whole-plane `W²,∞` cut-off `a` and the whole-plane local action
`wholePlaneLocalAction v delta N` (diffusion `delta (Δ - N²)`, transverse transport, axial
transport and stretching), this module computes the commutator with multiplication by `a`,
with the convention `[A,a] = Aa - aA`:

`[A, a] b = delta (2 ∇a · ∇b + (Δa) b) - Σ_j v_j (∂_j a) b`
(`wholePlaneLocalAction_cutoffCommutator_apply`).

The `N²` part of the diffusion, the axial transport and the stretching are zeroth-order
multipliers and commute with `a`; only the diffusion commutator and the cut-off-gradient
transport interaction `wholePlaneTransportCutoffInteraction` remain.
`Global/TorusChartC2AuxiliaryCutoff.lean` uses the formula for the auxiliary output cut-off
`auxiliaryCutoff_n`, where `ψ_n` annihilates every term because each carries a derivative of
`auxiliaryCutoff_n`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Metric Set

namespace WholePlaneCutoffCommutator

open ConstantCoefficientBackground
open TorusChartL2
open TorusChartH2
open WholePlaneAESupport
open TorusChartMultiplierDescent
open LocalizedSummandAlgebra
open TorusSupportedH2Output
open ScaleFamily.TorusCellPlacement.FullVelocityConcrete
open ScaleFamily.TorusCellPlacement
open ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate

/-! ## Whole-plane cutoff-commutator calculus -/

/-- Two scalar `L∞` multipliers acting on a whole-plane vector `L²` field commute, since pointwise
scalar multiplication is commutative.
-/
private theorem wholePlaneScalarMulC3L2_commute
    (a d : WholePlaneScalarLInf) (f : WholePlaneC3L2) :
    wholePlaneScalarMulC3L2 a (wholePlaneScalarMulC3L2 d f) =
      wholePlaneScalarMulC3L2 d (wholePlaneScalarMulC3L2 a f) := by
  apply Lp.ext
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := C3) volume a
      (wholePlaneScalarMulC3L2 d f),
    scalarVectorMulL2_coe_ae (E := C3) volume d f,
    scalarVectorMulL2_coe_ae (E := C3) volume d
      (wholePlaneScalarMulC3L2 a f),
    scalarVectorMulL2_coe_ae (E := C3) volume a f]
      with x hleft hdf hright haf
  simp only [wholePlaneScalarMulC3L2] at hleft hdf hright haf ⊢
  rw [hleft, hdf, hright, haf, smul_smul, smul_smul, mul_comm]

/-- A scalar `L∞` multiplier passes through a vector-valued multiplier acting on a scalar field:
multiplying the result by `a` is the same as multiplying the scalar factor by `a` first.
-/
private theorem wholePlaneScalarMulC3L2_vectorScalarMul
    (a : WholePlaneScalarLInf) (v : WholePlaneC3LInf)
    (f : WholePlaneScalarL2) :
    wholePlaneScalarMulC3L2 a
        (vectorScalarMulL2 (E := C3) volume v f) =
      vectorScalarMulL2 (E := C3) volume v
        (wholePlaneScalarMulL2 a f) := by
  apply Lp.ext
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := C3) volume a
      (vectorScalarMulL2 (E := C3) volume v f),
    vectorScalarMulL2_coe_ae (E := C3) volume v f,
    vectorScalarMulL2_coe_ae (E := C3) volume v
      (wholePlaneScalarMulL2 a f),
    scalarVectorMulL2_coe_ae (E := ℂ) volume a f]
      with x hleft hvf hright haf
  simp only [wholePlaneScalarMulC3L2, wholePlaneScalarMulL2]
    at hleft hvf hright haf ⊢
  rw [hleft, hvf, hright, haf, smul_smul]
  simp [smul_eq_mul]

/-- The whole-plane analogue of the periodic cutoff-gradient transport
interaction. -/
def wholePlaneTransportCutoffInteraction
    (a : WholePlaneScalarW2InfCertificate)
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC3H2) :
    WholePlaneC3L2 :=
  ∑ j : Fin 2,
    wholePlaneScalarMulC3L2 (wholePlaneCoordLInf j.castSucc v.value)
      (wholePlaneScalarMulC3L2 (a.deriv j)
        (wholePlaneH2Embedding C3 b))

/-- The commutator of the fixed-mode diffusion `Δ - N²` with multiplication by a `W^{2,∞}` cutoff is
the classical first-order expression `2 ∇a · ∇b + (Δa) b`; the `N²` term commutes and drops out.
-/
private theorem wholePlaneLocalDiffusion_commutator_apply
    (a : WholePlaneScalarW2InfCertificate) (N : ℝ)
    (b : WholePlaneC3H2) :
    wholePlaneLocalDiffusion N (wholePlaneScalarMulC3H2 a b) -
      wholePlaneScalarMulC3L2 a.value (wholePlaneLocalDiffusion N b) =
    (2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
      wholePlaneScalarMulC3L2 a.laplacian
        (wholePlaneH2Embedding C3 b) := by
  have hlap := wholePlaneLaplacian_scalarMulC3H2 a b
  have hemb := wholePlaneH2Embedding_scalarMulC3H2 a b
  change
    (wholePlaneLaplacian C3 (wholePlaneScalarMulC3H2 a b) -
        ((N : ℂ) ^ 2) •
          wholePlaneH2Embedding C3 (wholePlaneScalarMulC3H2 a b)) -
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneLaplacian C3 b -
          ((N : ℂ) ^ 2) • wholePlaneH2Embedding C3 b) = _
  calc
    _ = ((wholePlaneScalarMulC3L2 a.value
            (wholePlaneLaplacian C3 b) +
          (2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
          wholePlaneScalarMulC3L2 a.laplacian
            (wholePlaneH2Embedding C3 b)) -
        ((N : ℂ) ^ 2) •
          wholePlaneH2Embedding C3 (wholePlaneScalarMulC3H2 a b)) -
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneLaplacian C3 b -
          ((N : ℂ) ^ 2) • wholePlaneH2Embedding C3 b) :=
      congrArg (fun L : WholePlaneC3L2 ↦
        (L - ((N : ℂ) ^ 2) •
            wholePlaneH2Embedding C3 (wholePlaneScalarMulC3H2 a b)) -
          wholePlaneScalarMulC3L2 a.value
            (wholePlaneLaplacian C3 b -
              ((N : ℂ) ^ 2) • wholePlaneH2Embedding C3 b)) hlap
    _ = ((wholePlaneScalarMulC3L2 a.value
            (wholePlaneLaplacian C3 b) +
          (2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
          wholePlaneScalarMulC3L2 a.laplacian
            (wholePlaneH2Embedding C3 b)) -
        ((N : ℂ) ^ 2) • wholePlaneScalarMulC3L2 a.value
          (wholePlaneH2Embedding C3 b)) -
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneLaplacian C3 b -
          ((N : ℂ) ^ 2) • wholePlaneH2Embedding C3 b) :=
      congrArg (fun E : WholePlaneC3L2 ↦
        ((wholePlaneScalarMulC3L2 a.value
              (wholePlaneLaplacian C3 b) +
            (2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
            wholePlaneScalarMulC3L2 a.laplacian
              (wholePlaneH2Embedding C3 b)) -
          ((N : ℂ) ^ 2) • E) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneLaplacian C3 b -
            ((N : ℂ) ^ 2) • wholePlaneH2Embedding C3 b)) hemb
    _ = _ := by
      simp only [map_sub, map_smul]
      abel

/-- One direction `j` of the transverse transport term commutes with cutoff multiplication up to the
interaction `v_j (∂_j a) b`, since the cutoff passes through the velocity multiplier and only
the Leibniz derivative of the cutoff survives.
-/
private theorem wholePlaneLocalTransport_summand_commutator_apply
    (a : WholePlaneScalarW2InfCertificate)
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC3H2)
    (j : Fin 2) :
    wholePlaneScalarMulC3L2 (wholePlaneCoordLInf j.castSucc v.value)
        (wholePlaneH2FirstDerivative C3 j
          (wholePlaneScalarMulC3H2 a b)) -
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneScalarMulC3L2
          (wholePlaneCoordLInf j.castSucc v.value)
          (wholePlaneH2FirstDerivative C3 j b)) =
    wholePlaneScalarMulC3L2 (wholePlaneCoordLInf j.castSucc v.value)
      (wholePlaneScalarMulC3L2 (a.deriv j)
        (wholePlaneH2Embedding C3 b)) := by
  have hfirst := wholePlaneH2FirstDerivative_scalarMulC3H2 a b j
  calc
    _ = wholePlaneScalarMulC3L2
          (wholePlaneCoordLInf j.castSucc v.value)
          (wholePlaneScalarMulC3H2FirstJet a b j) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneScalarMulC3L2
            (wholePlaneCoordLInf j.castSucc v.value)
            (wholePlaneH2FirstDerivative C3 j b)) :=
      congrArg (fun D : WholePlaneC3L2 ↦
        wholePlaneScalarMulC3L2
            (wholePlaneCoordLInf j.castSucc v.value) D -
          wholePlaneScalarMulC3L2 a.value
            (wholePlaneScalarMulC3L2
              (wholePlaneCoordLInf j.castSucc v.value)
              (wholePlaneH2FirstDerivative C3 j b))) hfirst
    _ = (wholePlaneScalarMulC3L2
            (wholePlaneCoordLInf j.castSucc v.value)
            (wholePlaneScalarMulC3L2 (a.deriv j)
              (wholePlaneH2Embedding C3 b)) +
          wholePlaneScalarMulC3L2
            (wholePlaneCoordLInf j.castSucc v.value)
            (wholePlaneScalarMulC3L2 a.value
              (wholePlaneH2FirstDerivative C3 j b))) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneScalarMulC3L2
            (wholePlaneCoordLInf j.castSucc v.value)
            (wholePlaneH2FirstDerivative C3 j b)) := by
      unfold wholePlaneScalarMulC3H2FirstJet
      rw [map_add]
    _ = _ := by
      have hcomm := wholePlaneScalarMulC3L2_commute
        (wholePlaneCoordLInf j.castSucc v.value) a.value
        (wholePlaneH2FirstDerivative C3 j b)
      calc
        _ = (wholePlaneScalarMulC3L2
                (wholePlaneCoordLInf j.castSucc v.value)
                (wholePlaneScalarMulC3L2 (a.deriv j)
                  (wholePlaneH2Embedding C3 b)) +
              wholePlaneScalarMulC3L2 a.value
                (wholePlaneScalarMulC3L2
                  (wholePlaneCoordLInf j.castSucc v.value)
                  (wholePlaneH2FirstDerivative C3 j b))) -
            wholePlaneScalarMulC3L2 a.value
              (wholePlaneScalarMulC3L2
                (wholePlaneCoordLInf j.castSucc v.value)
                (wholePlaneH2FirstDerivative C3 j b)) :=
          congrArg (fun Y : WholePlaneC3L2 ↦
            wholePlaneScalarMulC3L2
                (wholePlaneCoordLInf j.castSucc v.value)
                (wholePlaneScalarMulC3L2 (a.deriv j)
                  (wholePlaneH2Embedding C3 b)) + Y -
              wholePlaneScalarMulC3L2 a.value
                (wholePlaneScalarMulC3L2
                  (wholePlaneCoordLInf j.castSucc v.value)
                  (wholePlaneH2FirstDerivative C3 j b))) hcomm
        _ = _ := by abel

/-- Summing over both transverse directions, the commutator of transverse transport with cutoff
multiplication is exactly the cutoff-gradient interaction `Σ_j v_j (∂_j a) b`.
-/
private theorem wholePlaneLocalTransport_commutator_apply
    (a : WholePlaneScalarW2InfCertificate)
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC3H2) :
    wholePlaneLocalTransport v (wholePlaneScalarMulC3H2 a b) -
      wholePlaneScalarMulC3L2 a.value (wholePlaneLocalTransport v b) =
    wholePlaneTransportCutoffInteraction a v b := by
  rw [wholePlaneLocalTransport_apply, wholePlaneLocalTransport_apply,
    map_sum, ← Finset.sum_sub_distrib]
  unfold wholePlaneTransportCutoffInteraction
  apply Finset.sum_congr rfl
  intro j _hj
  exact wholePlaneLocalTransport_summand_commutator_apply a v b j

/-- Axial transport is multiplication by `iN v₃`, a zero-order operator, so it commutes exactly with
multiplication by a scalar cutoff.
-/
private theorem wholePlaneLocalAxialTransport_commutes
    (a : WholePlaneScalarW2InfCertificate)
    (v : WholePlaneVelocityCoefficients) (N : ℝ)
    (b : WholePlaneC3H2) :
    wholePlaneLocalAxialTransport v N (wholePlaneScalarMulC3H2 a b) =
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneLocalAxialTransport v N b) := by
  have hemb := wholePlaneH2Embedding_scalarMulC3H2 a b
  have hcomm := wholePlaneScalarMulC3L2_commute
    (wholePlaneCoordLInf (2 : Fin 3) v.value) a.value
    (wholePlaneH2Embedding C3 b)
  rw [wholePlaneLocalAxialTransport_apply,
    wholePlaneLocalAxialTransport_apply]
  calc
    _ = (Complex.I * (N : ℂ)) •
        wholePlaneScalarMulC3L2
          (wholePlaneCoordLInf (2 : Fin 3) v.value)
          (wholePlaneScalarMulC3L2 a.value
            (wholePlaneH2Embedding C3 b)) :=
      congrArg (fun E : WholePlaneC3L2 ↦
        (Complex.I * (N : ℂ)) •
          wholePlaneScalarMulC3L2
            (wholePlaneCoordLInf (2 : Fin 3) v.value) E) hemb
    _ = (Complex.I * (N : ℂ)) •
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneScalarMulC3L2
            (wholePlaneCoordLInf (2 : Fin 3) v.value)
            (wholePlaneH2Embedding C3 b)) :=
      congrArg (fun X : WholePlaneC3L2 ↦
        (Complex.I * (N : ℂ)) • X) hcomm
    _ = _ := by
      simp only [wholePlaneScalarMulC3L2]
      rw [map_smul]

/-- The stretching term is a zero-order matrix multiplier, so it commutes exactly with
multiplication by a scalar cutoff.
-/
private theorem wholePlaneLocalStretching_commutes
    (a : WholePlaneScalarW2InfCertificate)
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC3H2) :
    wholePlaneLocalStretching v (wholePlaneScalarMulC3H2 a b) =
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneLocalStretching v b) := by
  have hemb := wholePlaneH2Embedding_scalarMulC3H2 a b
  rw [wholePlaneLocalStretching_apply, wholePlaneLocalStretching_apply]
  calc
    _ = ∑ j : Fin 2,
        vectorScalarMulL2 (E := C3) volume (v.deriv j)
          (wholePlaneCoordL2 j.castSucc
            (wholePlaneScalarMulC3L2 a.value
              (wholePlaneH2Embedding C3 b))) :=
      congrArg (fun E : WholePlaneC3L2 ↦
        ∑ j : Fin 2,
          vectorScalarMulL2 (E := C3) volume (v.deriv j)
            (wholePlaneCoordL2 j.castSucc E)) hemb
    _ = ∑ j : Fin 2,
        wholePlaneScalarMulC3L2 a.value
          (vectorScalarMulL2 (E := C3) volume (v.deriv j)
            (wholePlaneCoordL2 j.castSucc
              (wholePlaneH2Embedding C3 b))) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [wholePlaneCoordL2_scalarMulC3L2]
      exact (wholePlaneScalarMulC3L2_vectorScalarMul a.value
        (v.deriv j) _).symm
    _ = _ := by
      exact (map_sum (wholePlaneScalarMulC3L2 a.value)
        (fun j : Fin 2 ↦
          vectorScalarMulL2 (E := C3) volume (v.deriv j)
            (wholePlaneCoordL2 j.castSucc
              (wholePlaneH2Embedding C3 b))) Finset.univ).symm

/-- Generic whole-plane local-action cutoff formula, with convention
`[A,a]=Aa-aA`. -/
theorem wholePlaneLocalAction_cutoffCommutator_apply
    (a : WholePlaneScalarW2InfCertificate)
    (v : WholePlaneVelocityCoefficients) (delta N : ℝ)
    (b : WholePlaneC3H2) :
    wholePlaneLocalAction v delta N (wholePlaneScalarMulC3H2 a b) -
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneLocalAction v delta N b) =
    (delta : ℂ) •
        ((2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
          wholePlaneScalarMulC3L2 a.laplacian
            (wholePlaneH2Embedding C3 b)) -
      wholePlaneTransportCutoffInteraction a v b := by
  simp only [wholePlaneLocalAction, add_apply, sub_apply, smul_apply,
    map_add, map_sub, map_smul]
  have hdiff := wholePlaneLocalDiffusion_commutator_apply a N b
  have htransport := wholePlaneLocalTransport_commutator_apply a v b
  have haxial := wholePlaneLocalAxialTransport_commutes a v N b
  have hstretch := wholePlaneLocalStretching_commutes a v b
  have hdiffScaled := congrArg
    (fun X : WholePlaneC3L2 ↦ (delta : ℂ) • X) hdiff
  have hdiffExpanded :
      (delta : ℂ) •
          wholePlaneLocalDiffusion N (wholePlaneScalarMulC3H2 a b) -
        (delta : ℂ) • wholePlaneScalarMulC3L2 a.value
          (wholePlaneLocalDiffusion N b) =
      (delta : ℂ) •
        ((2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
          wholePlaneScalarMulC3L2 a.laplacian
            (wholePlaneH2Embedding C3 b)) := by
    calc
      _ = (delta : ℂ) •
          (wholePlaneLocalDiffusion N (wholePlaneScalarMulC3H2 a b) -
            wholePlaneScalarMulC3L2 a.value
              (wholePlaneLocalDiffusion N b)) := (smul_sub _ _ _).symm
      _ = _ := hdiffScaled
  clear hdiff hdiffScaled
  calc
    _ = ((delta : ℂ) •
          wholePlaneLocalDiffusion N (wholePlaneScalarMulC3H2 a b) -
        (delta : ℂ) • wholePlaneScalarMulC3L2 a.value
          (wholePlaneLocalDiffusion N b)) -
      (wholePlaneLocalTransport v (wholePlaneScalarMulC3H2 a b) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneLocalTransport v b)) -
      (wholePlaneLocalAxialTransport v N (wholePlaneScalarMulC3H2 a b) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneLocalAxialTransport v N b)) +
      (wholePlaneLocalStretching v (wholePlaneScalarMulC3H2 a b) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneLocalStretching v b)) := by abel
    _ = (delta : ℂ) •
          ((2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
            wholePlaneScalarMulC3L2 a.laplacian
              (wholePlaneH2Embedding C3 b)) -
        wholePlaneTransportCutoffInteraction a v b -
      (wholePlaneLocalAxialTransport v N (wholePlaneScalarMulC3H2 a b) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneLocalAxialTransport v N b)) +
      (wholePlaneLocalStretching v (wholePlaneScalarMulC3H2 a b) -
        wholePlaneScalarMulC3L2 a.value
          (wholePlaneLocalStretching v b)) :=
      congrArg₂ (fun X Y : WholePlaneC3L2 ↦
        X - Y -
          (wholePlaneLocalAxialTransport v N
              (wholePlaneScalarMulC3H2 a b) -
            wholePlaneScalarMulC3L2 a.value
              (wholePlaneLocalAxialTransport v N b)) +
          (wholePlaneLocalStretching v
              (wholePlaneScalarMulC3H2 a b) -
            wholePlaneScalarMulC3L2 a.value
              (wholePlaneLocalStretching v b)))
        hdiffExpanded htransport
    _ = _ := by
      have haxialZero :
          wholePlaneLocalAxialTransport v N
                (wholePlaneScalarMulC3H2 a b) -
              wholePlaneScalarMulC3L2 a.value
                (wholePlaneLocalAxialTransport v N b) = 0 :=
        sub_eq_zero.mpr haxial
      have hstretchZero :
          wholePlaneLocalStretching v (wholePlaneScalarMulC3H2 a b) -
              wholePlaneScalarMulC3L2 a.value
                (wholePlaneLocalStretching v b) = 0 :=
        sub_eq_zero.mpr hstretch
      calc
        _ = (delta : ℂ) •
              ((2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
                wholePlaneScalarMulC3L2 a.laplacian
                  (wholePlaneH2Embedding C3 b)) -
            wholePlaneTransportCutoffInteraction a v b - 0 + 0 :=
          congrArg₂ (fun X Y : WholePlaneC3L2 ↦
            (delta : ℂ) •
                ((2 : ℂ) • wholePlaneScalarGradientDotC3H2 a b +
                  wholePlaneScalarMulC3L2 a.laplacian
                    (wholePlaneH2Embedding C3 b)) -
              wholePlaneTransportCutoffInteraction a v b - X + Y)
            haxialZero hstretchZero
        _ = _ := by abel

end WholePlaneCutoffCommutator

end

end FastDynamo
