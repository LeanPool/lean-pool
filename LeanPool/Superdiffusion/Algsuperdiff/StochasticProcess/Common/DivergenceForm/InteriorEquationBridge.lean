/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialLinftyBound
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationSequence
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ResolventH10Representative
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ScalarForcing

/-!
# InteriorEquationBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Interior bridge between the zero-trace weak formulation of the potential
problem and the divergence-form carrier of the interior Schauder chain.
-/

/-!
# Interior equation bridge for the potential problem

The potential problem is posed on `ZeroTraceSobolev U` with the pairing
`coefficientPairing`, while the interior Schauder chain consumes
`IsMatrixDivFormWeakSolutionZerothOrderOn`, an equation between explicit set
integrals against `H¹₀` test functions on an open window.  This file connects
the two.

The scalar source of the interior equation is `f - α u - q u`, obtained by
moving the mass term and the potential term of

`α ⟪u, φ⟫ + ∫ q u φ + coefficientPairing a U ∇u ∇φ = ⟪f, φ⟫`

to the right-hand side; the vector source is zero.

Three statements are provided:

* the plain bridge, valid for every `f ∈ L²(U)`;
* its bounded companion, which adds `‖g‖_{L^∞(W)} ≤ (2 + C/α) ‖f‖_{L^∞(U)}`
  under an essential bound on `f`; and
* the specialization to the penalization potential on a window inside the part
  domain, where the potential vanishes and the bound collapses to
  `2 ‖f‖_{L^∞(U)}`, uniformly in the penalization index.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} {V U : Set (Vec d)}

/-- The `L²` source of the interior equation: the forcing minus the mass and
potential contributions of the solution. -/
def interiorScalarSource (alpha : ℝ) {C : ℝ} (q : Vec d → ℝ)
    (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) (u : ZeroTraceSobolev U) : ScalarL2 U :=
  f - alpha • ZeroTraceSobolev.toL2 u - potentialMul q hq (ZeroTraceSobolev.toL2 u)

theorem interiorScalarSource_coeFn (alpha : ℝ) {C : ℝ} (q : Vec d → ℝ)
    (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) (u : ZeroTraceSobolev U) :
    interiorScalarSource alpha q hq f u =ᵐ[volumeMeasureOn U]
      fun x => f x - alpha * ZeroTraceSobolev.toL2 u x -
        q x * ZeroTraceSobolev.toL2 u x := by
  have hmul := potentialMul_coeFn (U := U) q hq (ZeroTraceSobolev.toL2 u)
  filter_upwards [Lp.coeFn_sub (f - alpha • ZeroTraceSobolev.toL2 u)
      (potentialMul q hq (ZeroTraceSobolev.toL2 u)),
    Lp.coeFn_sub f (alpha • ZeroTraceSobolev.toL2 u),
    Lp.coeFn_smul alpha (ZeroTraceSobolev.toL2 u), hmul] with x h1 h2 h3 h4
  rw [interiorScalarSource, h1, Pi.sub_apply, h2, Pi.sub_apply, h3,
    Pi.smul_apply, h4, smul_eq_mul]

/-- The interior equation on the whole domain, with the zero-trace solution
read through an `H¹₀` witness. -/
theorem isMatrixDivFormWeakSolutionZerothOrderOn_domain_of_isPotentialWeakSolution
    (a : CoeffField d)
    {alpha C : ℝ} (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) {u : ZeroTraceSobolev U}
    (hu : IsPotentialWeakSolution a alpha q U u f)
    (w : H10Function U)
    (hwgrad : w.toH1Function.gradToHilbertVectorL2 = ZeroTraceSobolev.gradient u) :
    IsMatrixDivFormWeakSolutionZerothOrderOn a U w.toH1Function
      (fun x => interiorScalarSource alpha q hq f u x) 0 := by
  intro phi
  have hphi := hu (ZeroTraceSobolev.ofH10Function phi)
  rw [shiftedPotentialBilin, ZeroTraceSobolev.toL2_ofH10Function,
    ZeroTraceSobolev.gradient_ofH10Function] at hphi
  -- the coefficient pairing as an explicit integral of `vecDot`
  have hpair : coefficientPairing a U (ZeroTraceSobolev.gradient u)
      phi.toH1Function.gradToHilbertVectorL2 =
      ∫ x in U, vecDot (matVecMul (a x) (w.toH1Function.grad x))
        (phi.toH1Function.grad x) ∂volume := by
    rw [coefficientPairing]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (U := U)
        (ZeroTraceSobolev.gradient u),
      coeFn_hilbertVectorL2ToVectorL2 (U := U)
        phi.toH1Function.gradToHilbertVectorL2,
      hwgrad ▸ w.toH1Function.coeFn_gradToHilbertVectorL2,
      phi.toH1Function.coeFn_gradToHilbertVectorL2] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    simp [hilbertifyVecField]
  -- the mass, potential and forcing terms as one inner product
  have hsource : ⟪interiorScalarSource alpha q hq f u,
      phi.toH1Function.toScalarL2⟫ =
      ⟪f, phi.toH1Function.toScalarL2⟫ -
        alpha * ⟪ZeroTraceSobolev.toL2 u, phi.toH1Function.toScalarL2⟫ -
        ∫ x, q x * ZeroTraceSobolev.toL2 u x * phi.toH1Function.toScalarL2 x
          ∂volumeMeasureOn U := by
    rw [interiorScalarSource, inner_sub_left, inner_sub_left,
      inner_potentialMul_eq_integral, real_inner_smul_left]
  have hpairEq : coefficientPairing a U (ZeroTraceSobolev.gradient u)
      phi.toH1Function.gradToHilbertVectorL2 =
      ⟪interiorScalarSource alpha q hq f u, phi.toH1Function.toScalarL2⟫ := by
    rw [hsource]
    linarith only [hphi]
  -- turn the inner product into an integral against the test function
  have hinner : ⟪interiorScalarSource alpha q hq f u,
      phi.toH1Function.toScalarL2⟫ =
      ∫ x in U, interiorScalarSource alpha q hq f u x *
        phi.toH1Function.toFun x ∂volume := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [phi.toH1Function.coeFn_toScalarL2] with x hx
    rw [hx, RCLike.inner_apply']
    simp
  have hzero : ∫ x in U, vecDot ((0 : Vec d → Vec d) x)
      (phi.toH1Function.grad x) ∂volume = 0 := by
    simp only [Pi.zero_apply, vecDot_zero_left, integral_zero]
  rw [hzero, sub_zero, ← hinner, ← hpairEq, hpair]

/-- An essential bound on a window gives membership in `L^∞` there together
with the corresponding bound on the essential supremum. -/
theorem memScalarLInfOn_of_ae_bound {W : Set (Vec d)} {g : Vec d → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hmeas : AEStronglyMeasurable g (volume.restrict W))
    (hbd : ∀ᵐ x ∂volume.restrict W, |g x| ≤ K) :
    MemScalarLInfOn W g ∧ scalarLInfSizeOn W g ≤ K := by
  have hnorm : ∀ᵐ x ∂volume.restrict W, ‖g x‖ ≤ K := by
    filter_upwards [hbd] with x hx
    simpa [Real.norm_eq_abs] using hx
  refine ⟨memLp_top_of_bound hmeas K hnorm, ?_⟩
  have hle : eLpNorm g ⊤ (volume.restrict W) ≤ ENNReal.ofReal K := by
    rw [eLpNorm_exponent_top hmeas]
    exact eLpNormEssSup_le_of_ae_bound hnorm
  unfold scalarLInfSizeOn
  exact ENNReal.toReal_le_of_le_ofReal hK hle

end

end DivergenceFormProcess.Form
