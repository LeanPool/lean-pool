/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.Holder
public import LeanPool.FastDynamo.Analysis.PeriodicWeakDerivative

/-!
# Real periodic `W^{1,∞}` velocities on the transverse torus

This file bundles an essentially bounded real field together with essentially
bounded first weak derivatives.  The derivatives are not free data: after the
canonical inclusion into `L²` and coordinatewise complexification, every
Fourier coefficient must satisfy

`(partial_j u)_hat_i(n) = 2 * pi * I * n_j * u_hat_i(n)`.

Thus the space is a closed Fourier graph, parallel to `TransverseC3H2`.  Its
graph norm is complete, and its value and derivative projections are
continuous.  The coefficient formulation is exactly the notion needed by the
paper's fixed-axial-sector operator.  `PeriodicWeakDerivativeTest` proves that
it is equivalent to integration by parts against the complete Fourier
monomial family, and by finite linearity against every trigonometric
polynomial.  The qualifier "Fourier weak derivative" distinguishes this notion from
integration by parts against all smooth test functions.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Real-to-complex conversion -/

/-- Coordinatewise inclusion `R³ → C³`, regarded as a real linear map. -/
def complexifyR3LinearMap : R3 →ₗ[ℝ] C3 where
  toFun v := WithLp.toLp 2 (fun i ↦ (v i : ℂ))
  map_add' v w := by
    apply PiLp.ext
    intro i
    simp
  map_smul' r v := by
    apply PiLp.ext
    intro i
    simp

/-- Coordinatewise inclusion `R³ → C³` as a continuous real linear map. -/
def complexifyR3 : R3 →L[ℝ] C3 :=
  ⟨complexifyR3LinearMap,
    complexifyR3LinearMap.continuous_of_finiteDimensional⟩

/-- Complexification acts coordinatewise: the `i`th entry of `complexifyR3 v` is the
complex number `(v i : ℂ)`. -/
@[simp] theorem complexifyR3_apply (v : R3) (i : Fin 3) :
    complexifyR3 v i = (v i : ℂ) :=
  rfl

/-- Essentially bounded real vector fields on the transverse torus. -/
abbrev TransverseR3LInf := Lp R3 ∞ transverseMeasure

/-- Complexify an essentially bounded real transverse vector field. -/
def complexifyR3LInf : TransverseR3LInf →L[ℝ] TransverseC3LInf :=
  complexifyR3.compLpL ∞ transverseMeasure

/-- Complexify and include an essentially bounded real field into complex `L²`. -/
def complexifyR3LTwo : TransverseR3LInf →L[ℝ] TransverseC3L2 :=
  transverseC3LInfToL2.restrictScalars ℝ |>.comp complexifyR3LInf

/-- An almost everywhere representative of the complexified `L²` inclusion of a real
essentially bounded field: it is the coordinatewise complexification of any representative
of `u`. -/
theorem complexifyR3LTwo_coe_ae (u : TransverseR3LInf) :
    (complexifyR3LTwo u : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        fun x ↦ WithLp.toLp 2 (fun i ↦ ((u x i : ℝ) : ℂ)) := by
  have hinc := transverseC3LInfToL2_coe_ae (complexifyR3LInf u)
  have hcomp := complexifyR3.coeFn_compLpL u
  filter_upwards [hinc, hcomp] with x hi hc
  change ((transverseC3LInfToL2 (complexifyR3LInf u) :
    TransverseC3L2) : TransverseTorus → C3) x = _
  rw [hi]
  change (((complexifyR3.compLpL ∞ transverseMeasure) u :
    TransverseC3LInf) : TransverseTorus → C3) x = _
  rw [hc]
  rfl

/-! ## Closed Fourier graph -/

/-- Two essentially bounded real vector fields, one for each transverse derivative. -/
abbrev TransverseR3GradientLInf :=
  PiLp ∞ (fun _ : Fin 2 ↦ TransverseR3LInf)

/-- Ambient value/gradient pairs before imposing the weak derivative equations. -/
abbrev TransverseW1InfAmbient :=
  TransverseR3LInf × TransverseR3GradientLInf

/-- Extract the value field from the ambient graph space. -/
def transverseW1InfValueAmbient :
    TransverseW1InfAmbient →L[ℝ] TransverseR3LInf :=
  ContinuousLinearMap.fst ℝ TransverseR3LInf TransverseR3GradientLInf

/-- Extract one derivative field from the ambient graph space. -/
def transverseW1InfDerivAmbient (j : Fin 2) :
    TransverseW1InfAmbient →L[ℝ] TransverseR3LInf :=
  (PiLp.proj ∞ (fun _ : Fin 2 ↦ TransverseR3LInf) j).comp
    (ContinuousLinearMap.snd ℝ TransverseR3LInf TransverseR3GradientLInf)

/-- One Fourier coefficient of the complexification of a real `L∞` field. -/
def transverseRealCoeffCLM (n : TransverseFrequency) (i : Fin 3) :
    TransverseR3LInf →L[ℝ] ℂ :=
  (transverseCoeffCLM n i).restrictScalars ℝ |>.comp complexifyR3LTwo

/-- The equation asserting that one stored field is the `j`-th Fourier weak derivative. -/
def transverseW1InfConstraint (j : Fin 2) (n : TransverseFrequency)
    (i : Fin 3) : TransverseW1InfAmbient →L[ℝ] ℂ :=
  (transverseRealCoeffCLM n i).comp (transverseW1InfDerivAmbient j) -
    ((ContinuousLinearMap.mul ℝ ℂ)
      (2 * Real.pi * Complex.I * (n j : ℂ))).comp
        ((transverseRealCoeffCLM n i).comp transverseW1InfValueAmbient)

/-- The closed Fourier graph defining real periodic `W^{1,∞}`. -/
def transverseW1InfSubmodule : Submodule ℝ TransverseW1InfAmbient :=
  ⨅ j : Fin 2, ⨅ n : TransverseFrequency, ⨅ i : Fin 3,
    (transverseW1InfConstraint j n i).ker

/-- Membership in the closed Fourier graph is exactly the family of weak-derivative
equations `(∂_j u)^_i(n) = 2π i n_j û_i(n)`, for every transverse direction `j`, every
frequency `n` and every vector component `i`. -/
theorem mem_transverseW1InfSubmodule_iff
    (u : TransverseR3LInf) (du : TransverseR3GradientLInf) :
    (u, du) ∈ transverseW1InfSubmodule ↔
      ∀ (j : Fin 2) (n : TransverseFrequency) (i : Fin 3),
        transverseRealCoeffCLM n i (du j) =
          (2 * Real.pi * Complex.I * (n j : ℂ)) *
            transverseRealCoeffCLM n i u := by
  constructor
  · intro h j n i
    have hker : (u, du) ∈ (transverseW1InfConstraint j n i).ker := by
      exact (Submodule.mem_iInf _).mp
        ((Submodule.mem_iInf _).mp
          ((Submodule.mem_iInf _).mp h j) n) i
    change transverseRealCoeffCLM n i (du j) -
      (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseRealCoeffCLM n i u = 0 at hker
    exact sub_eq_zero.mp hker
  · intro h
    rw [transverseW1InfSubmodule, Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_iInf]
    intro n
    rw [Submodule.mem_iInf]
    intro i
    change transverseRealCoeffCLM n i (du j) -
      (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseRealCoeffCLM n i u = 0
    exact sub_eq_zero.mpr (h j n i)

/-- The `W^{1,∞}` graph is closed, being an intersection of kernels of the continuous
linear constraint functionals `transverseW1InfConstraint j n i`. -/
lemma isClosed_transverseW1InfSubmodule :
    IsClosed (transverseW1InfSubmodule : Set TransverseW1InfAmbient) := by
  simpa only [transverseW1InfSubmodule, Submodule.coe_iInf] using
    (isClosed_iInter fun j ↦ isClosed_iInter fun n ↦
      isClosed_iInter fun i ↦ (transverseW1InfConstraint j n i).isClosed_ker)

/-- Real periodic `W^{1,∞}` as a complete closed Fourier graph. -/
abbrev TransverseRealW1Inf := transverseW1InfSubmodule

/-- `TransverseRealW1Inf` is complete: it is a closed subspace of the complete ambient
value/gradient product. -/
instance : CompleteSpace TransverseRealW1Inf :=
  isClosed_transverseW1InfSubmodule.isComplete.completeSpace_coe

/-- The essentially bounded real value field. -/
def transverseW1InfValue : TransverseRealW1Inf →L[ℝ] TransverseR3LInf :=
  transverseW1InfValueAmbient.domRestrict transverseW1InfSubmodule

/-- One essentially bounded real Fourier weak derivative. -/
def transverseW1InfDeriv (j : Fin 2) :
    TransverseRealW1Inf →L[ℝ] TransverseR3LInf :=
  (transverseW1InfDerivAmbient j).domRestrict transverseW1InfSubmodule

/-- The complexification of the essentially bounded value field. -/
def transverseW1InfComplexValueLInf :
    TransverseRealW1Inf →L[ℝ] TransverseC3LInf :=
  complexifyR3LInf.comp transverseW1InfValue

/-- The complexification of one essentially bounded weak derivative. -/
def transverseW1InfComplexDerivLInf (j : Fin 2) :
    TransverseRealW1Inf →L[ℝ] TransverseC3LInf :=
  complexifyR3LInf.comp (transverseW1InfDeriv j)

/-- Extract one scalar component of a complex essentially bounded vector field. -/
def transverseCoordLInf (i : Fin 3) :
    TransverseC3LInf →L[ℂ] TransverseScalarLInf :=
  (EuclideanSpace.proj i).compLpL ∞ transverseMeasure

/-- One complex scalar component of the essentially bounded value field. -/
def transverseW1InfComplexValueCoordLInf (i : Fin 3) :
    TransverseRealW1Inf →L[ℝ] TransverseScalarLInf :=
  ((transverseCoordLInf i).restrictScalars ℝ).comp
    transverseW1InfComplexValueLInf

/-- One complex scalar component of an essentially bounded weak derivative. -/
def transverseW1InfComplexDerivCoordLInf (j : Fin 2) (i : Fin 3) :
    TransverseRealW1Inf →L[ℝ] TransverseScalarLInf :=
  ((transverseCoordLInf i).restrictScalars ℝ).comp
    (transverseW1InfComplexDerivLInf j)

/-- The complexified value field is the complexification of the real value field. -/
@[simp] theorem transverseW1InfComplexValueLInf_apply
    (u : TransverseRealW1Inf) :
    transverseW1InfComplexValueLInf u =
      complexifyR3LInf (transverseW1InfValue u) :=
  rfl

/-- The complexified `j`th weak derivative is the complexification of the real `j`th
derivative field. -/
@[simp] theorem transverseW1InfComplexDerivLInf_apply
    (j : Fin 2) (u : TransverseRealW1Inf) :
    transverseW1InfComplexDerivLInf j u =
      complexifyR3LInf (transverseW1InfDeriv j u) :=
  rfl

/-- The `i`th scalar component of the complexified value field is obtained by applying the
coordinate projection to that complexified field. -/
@[simp] theorem transverseW1InfComplexValueCoordLInf_apply
    (i : Fin 3) (u : TransverseRealW1Inf) :
    transverseW1InfComplexValueCoordLInf i u =
      transverseCoordLInf i (transverseW1InfComplexValueLInf u) :=
  rfl

/-- The `i`th scalar component of the complexified `j`th derivative field is obtained by
applying the coordinate projection to that complexified field. -/
@[simp] theorem transverseW1InfComplexDerivCoordLInf_apply
    (j : Fin 2) (i : Fin 3) (u : TransverseRealW1Inf) :
    transverseW1InfComplexDerivCoordLInf j i u =
      transverseCoordLInf i (transverseW1InfComplexDerivLInf j u) :=
  rfl

/-- Pointwise almost everywhere description of the complexified value field: it is
`complexifyR3` applied to a representative of the real value field. -/
theorem transverseW1InfComplexValueLInf_coe_ae
    (u : TransverseRealW1Inf) :
    (transverseW1InfComplexValueLInf u : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        fun x ↦ complexifyR3 ((transverseW1InfValue u) x) := by
  exact complexifyR3.coeFn_compLpL (transverseW1InfValue u)

/-- Pointwise almost everywhere description of the complexified `j`th derivative field: it
is `complexifyR3` applied to a representative of the real derivative field. -/
theorem transverseW1InfComplexDerivLInf_coe_ae
    (j : Fin 2) (u : TransverseRealW1Inf) :
    (transverseW1InfComplexDerivLInf j u : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        fun x ↦ complexifyR3 ((transverseW1InfDeriv j u) x) := by
  exact complexifyR3.coeFn_compLpL (transverseW1InfDeriv j u)

/-- The value projection returns the first component of the underlying ambient pair. -/
@[simp] theorem transverseW1InfValue_apply (u : TransverseRealW1Inf) :
    transverseW1InfValue u = u.1.1 :=
  rfl

/-- The `j`th derivative projection returns the `j`th entry of the gradient component of
the underlying ambient pair. -/
@[simp] theorem transverseW1InfDeriv_apply (j : Fin 2)
    (u : TransverseRealW1Inf) : transverseW1InfDeriv j u = u.1.2 j :=
  rfl

/-- The stored derivative satisfies the periodic Fourier weak-derivative equation. -/
theorem transverseW1Inf_fourier_weakDeriv (u : TransverseRealW1Inf)
    (j : Fin 2) (n : TransverseFrequency) (i : Fin 3) :
    transverseRealCoeffCLM n i (transverseW1InfDeriv j u) =
      (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseRealCoeffCLM n i (transverseW1InfValue u) := by
  exact (mem_transverseW1InfSubmodule_iff u.1.1 u.1.2).mp u.2 j n i

end

end FastDynamo
