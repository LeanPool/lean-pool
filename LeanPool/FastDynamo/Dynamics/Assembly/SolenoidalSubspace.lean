/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.InductionDivergence
public import LeanPool.FastDynamo.Finish.RealSolution

/-!
# The solenoidal subspace of the product three-torus model

The paper's induction semigroup acts on

`L²_σ(T³) := {B ∈ L²(T³;ℂ³) : Div B = 0}`,

not on the full vector-valued `L²`.  This module builds that space inside the
working model `ProductC3L2` and proves the two facts that make it a legitimate
carrier for a semigroup: it is a *closed* (hence complete) subspace, and it is
*invariant* under every state resolvent of the all-frequency induction operator
at a spectral parameter with positive real part.

The subspace is cheap to construct because `IsProductSolenoidal`
(`FastDynamo/Analysis/ProductVectorCalculus.lean`) is a family of scalar linear
equations in the Fourier coefficients of the field: for each transverse
frequency `n` and each axial frequency `k`, the combination

`∑_{j<2} 2πi n_j V̂_j(n,k) + 2πi k V̂_3(n,k)`

is a continuous linear functional of `V`, so `L²_σ` is an intersection of
kernels.  This is the same pattern already used for the Fourier graph domain in
`isClosed_productH2Submodule`.

Resolvent invariance is *not* an extra analytic input either.  It is the resolvent form of the
auxiliary solenoidality argument of `FastDynamo/Finish/RealSolution.lean`: taking the weak
divergence of the resolvent equation turns it into a scalar advection–diffusion equation for
`d := div B`, whose forcing term is the weak divergence of the solenoidal datum and therefore
vanishes; the energy endpoint `productScalarWeakEigenfunction_eq_zero` then forces `d = 0`.  No
new estimate is used, and in particular nothing from the product resolvent construction: the
statement is quantified over an arbitrary `HasResolventOn` certificate.  That solenoidality
argument is a result of the formalisation, with no counterpart in the paper,
which recovers the axial component in `lem:axial-recovery` instead.

## Contents

* **The subspace.**  `productSolenoidalFunctional` and its evaluation lemma,
  `productSolenoidalSubspace` as the infimum of their kernels,
  `mem_productSolenoidalSubspace_iff`, `isClosed_productSolenoidalSubspace` and
  the resulting `CompleteSpace` instance.
* **Resolvent invariance.**
  `stateResolvent_mem_productSolenoidalSubspace_of_re_pos`, for every spectral
  parameter with positive real part in the domain of any resolvent certificate,
  and its real-ray corollary `stateResolvent_mem_productSolenoidalSubspace`.
* **Eigenfunctions.**
  `productH2Embedding_mem_productSolenoidalSubspace_of_isEigenpair`, the
  membership form of `productInductionEigenpair_solenoidal`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The solenoidal subspace as an intersection of kernels -/

/--
The scalar constraint functional whose vanishing at `(n, k)` is the
distributional solenoidality of a product `L²` field in that single Fourier
mode: `V ↦ ∑_{j<2} 2πi n_j V̂_j(n,k) + 2πi k V̂_3(n,k)`.
-/
def productSolenoidalFunctional (n : TransverseFrequency) (k : ℤ) :
    ProductC3L2 →L[ℂ] ℂ :=
  (∑ j : Fin 2,
    (2 * Real.pi * Complex.I * (n j : ℂ)) • productCoeffCLM n k j.castSucc) +
  (2 * Real.pi * Complex.I * (k : ℂ)) • productCoeffCLM n k (2 : Fin 3)

/-- Evaluation of the solenoidality constraint functional, written with the
scalar multiplications displayed. -/
theorem productSolenoidalFunctional_apply (n : TransverseFrequency) (k : ℤ)
    (V : ProductC3L2) :
    productSolenoidalFunctional n k V =
      (∑ j : Fin 2, (2 * Real.pi * Complex.I * (n j : ℂ)) *
          productCoeffCLM n k j.castSucc V) +
        (2 * Real.pi * Complex.I * (k : ℂ)) * productCoeffCLM n k (2 : Fin 3) V := by
  simp [productSolenoidalFunctional]

/--
`L²_σ` in the product model: the solenoidal subspace of `ProductC3L2`, realized
as the intersection of the kernels of all the constraint functionals.
-/
def productSolenoidalSubspace : Submodule ℂ ProductC3L2 :=
  ⨅ n, ⨅ k, (productSolenoidalFunctional n k).ker

/-- Membership in the solenoidal subspace is exactly coefficientwise
distributional solenoidality. -/
theorem mem_productSolenoidalSubspace_iff (V : ProductC3L2) :
    V ∈ productSolenoidalSubspace ↔ IsProductSolenoidal V := by
  constructor
  · intro h n k
    have hk : V ∈ (productSolenoidalFunctional n k).ker :=
      (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h n) k
    rw [← productSolenoidalFunctional_apply]
    exact hk
  · intro h
    rw [productSolenoidalSubspace, Submodule.mem_iInf]
    intro n
    rw [Submodule.mem_iInf]
    intro k
    change productSolenoidalFunctional n k V = 0
    rw [productSolenoidalFunctional_apply]
    exact h n k

/-- The solenoidal subspace is closed, being an intersection of kernels of
continuous linear functionals. -/
theorem isClosed_productSolenoidalSubspace :
    IsClosed (productSolenoidalSubspace : Set ProductC3L2) := by
  simpa only [productSolenoidalSubspace, Submodule.coe_iInf] using
    (isClosed_iInter fun n => isClosed_iInter fun k =>
      (productSolenoidalFunctional n k).isClosed_ker)

/-- The solenoidal subspace is a Hilbert space in its own right, inherited from
closedness inside `ProductC3L2`.  This is what makes operator norms on `L²_σ`,
and hence the paper's growth rate, well typed. -/
instance : CompleteSpace productSolenoidalSubspace :=
  isClosed_productSolenoidalSubspace.completeSpace_coe

/-! ## Invariance of the solenoidal subspace under the state resolvents

The argument is the resolvent form of the auxiliary solenoidality theorem of
`FastDynamo/Finish/RealSolution.lean`, with the eigen-equation `A B = λ ι B` replaced by the
resolvent equation `A B = z ι B - x`.  The extra term `x` is annihilated by the weak divergence
precisely because `x` is solenoidal, so the scalar equation satisfied by `div B` is unchanged and
the energy endpoint applies verbatim.  Both shapes are instances of the one lemma
`productInductionAction_divergence_eq_zero`, so nothing of that argument is restated here.  The
statement is quantified over an arbitrary resolvent certificate, so it does not depend on any
particular construction of the product resolvent. -/

/--
**Solenoidal invariance of the state resolvent.**  If `x` is solenoidal and `z`
is a spectral parameter with positive real part at which the all-frequency
induction operator has a two-sided domain-valued resolvent, then the resolvent
image of `x` is again solenoidal.

The hypothesis on the diffusivity is only `0 ≤ ε`, matching
`productInductionEigenpair_divergence_eq_zero`.
-/
theorem stateResolvent_mem_productSolenoidalSubspace_of_re_pos
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    {ε : ℝ} (hε : 0 ≤ ε) {S : Set ℂ}
    (h : HasResolventOn (productInductionOperator u ε) S)
    {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.re)
    (x : ProductC3L2) (hx : x ∈ productSolenoidalSubspace) :
    h.stateResolvent z x ∈ productSolenoidalSubspace := by
  set B : ProductC3H2 := h.inv z x with hB
  have hpencil : (productInductionOperator u ε).pencil z B = x := by
    have := congrArg (fun T : ProductC3L2 →L[ℂ] ProductC3L2 => T x)
      (h.right_inv z hzS)
    simpa [DomainOperator.pencil, hB] using this
  have haction : productInductionAction u ε B = z • productH2Embedding B - x := by
    rw [DomainOperator.pencil] at hpencil
    rw [sub_apply, smul_apply] at hpencil
    change z • productH2Embedding B - productInductionAction u ε B = x at hpencil
    rw [← hpencil]
    abel
  have hdivx : productWeakDivergence x = 0 :=
    productWeakDivergence_eq_zero_of_solenoidal
      ((mem_productSolenoidalSubspace_iff x).1 hx)
  have hdivB : productDivergenceFromH2 B = 0 :=
    productInductionAction_divergence_eq_zero u hu ε hε z hz B x hdivx haction
  rw [mem_productSolenoidalSubspace_iff]
  exact (productDivergenceFromH2_eq_zero_iff B).1 hdivB

/--
Real-ray form of solenoidal invariance: the state resolvent at a positive real
spectral parameter preserves `L²_σ`.  This is the shape consumed by the
Hille--Yosida ray, whose resolvent set is a ray of the positive real axis.
-/
theorem stateResolvent_mem_productSolenoidalSubspace
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    {ε : ℝ} (hε : 0 ≤ ε) {S : Set ℂ}
    (h : HasResolventOn (productInductionOperator u ε) S)
    {r : ℝ} (hr : 0 < r) (hrS : (r : ℂ) ∈ S)
    (x : ProductC3L2) (hx : x ∈ productSolenoidalSubspace) :
    h.stateResolvent (r : ℂ) x ∈ productSolenoidalSubspace :=
  stateResolvent_mem_productSolenoidalSubspace_of_re_pos u hu hε h hrS
    (by simpa only [Complex.ofReal_re] using hr) x hx

/-! ## Unstable eigenfunctions lie in the solenoidal subspace -/

/--
Membership form of the auxiliary solenoidality theorem: the `L²` field underlying an
eigenfunction of the auxiliary induction operator with positive-real-part
eigenvalue belongs to `L²_σ`.
-/
theorem productH2Embedding_mem_productSolenoidalSubspace_of_isEigenpair
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    {ε : ℝ} (hε : 0 ≤ ε) {lam : ℂ} (hlam : 0 < lam.re) {B : ProductC3H2}
    (h : (productInductionOperator u ε).IsEigenpair lam B) :
    productH2Embedding B ∈ productSolenoidalSubspace :=
  (mem_productSolenoidalSubspace_iff _).2
    (productInductionEigenpair_solenoidal u hu ε hε lam hlam B h)

end

end FastDynamo
