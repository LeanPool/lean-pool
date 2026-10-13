/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.BlockBesovSeminorm
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledAdjointEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledEnergyIdentity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.TruncationPoincareBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Dilation
public import LeanPool.HighContrastHomogenization.Support.Probability.LocalEllipticitySlices
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# DoubledCoarsePoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coarse-grained Poincare inequality in the doubled variables

ABK26 Remark `r.cg.poincare.doubled.variables`, display
`e.CG.Poincare.doubled.vars`: for `bfA_0` of the form `e.form.of.A.naught` with
`sigma_0` scalar and `kappa_0 = 0`, and every `X in S(cu_m)`,

```
3^{-sm}[bfA_0^{1/2} X]_{B^{-s}_{2,q}} + 3^{-sm}[bfA_0^{-1/2} bfA X]_{B^{-s}_{2,q}}
  <= 4 c_{s,q}^{-1/q} ( sigma_0^{1/2} lambda_{s,q}^{-1/2}(cu_m;a)
                        + sigma_0^{-1/2} Lambda_{s,q}^{1/2}(cu_m;a) )
       || bfA^{1/2} X ||_{L^2(cu_m)} .
```

The manuscript calls this "an immediate consequence of
`p.coarse.grained.Poincare`, the identity `e.bfA.magic.swapping` and the
characterization `e.findSfull`".  The three implicit ingredients are supplied by
the sibling modules:

* `BlockBesovSeminorm.lean` -- the block seminorm on `R^{2d}`-valued fields and
  the two splits of the left-hand side (alpha);
* `DoubledAdjointEllipticity.lean` -- `lambda_{s,q}(Q;a^t) = lambda_{s,q}(Q;a)`
  and `Lambda_{s,q}(Q;a^t) = Lambda_{s,q}(Q;a)`, which is what lets the adjoint
  half of the argument land on the display's primal constants (beta);
* `TruncationPoincareBridge.lean` -- `p.coarse.grained.Poincare` at `q = 2` on
  the concrete seminorm, together with the truncation bounds that make the
  supremum form of the triangle inequality available (gamma).

Along `e.findSfull` the doubled field is
`X = (grad v + grad v^*, a grad v - a^t grad v^*)` with `v` a solution of `a`
and `v^*` a solution of `a^t`, and by `e.bfA.magic.swapping`
`bfA X = (a grad v + a^t grad v^*, grad v - grad v^*)`.  Since `bfA_0` is the
diagonal `diag(sigma_0, sigma_0^{-1})` at scalar `sigma_0` and `kappa_0 = 0`,
its square roots act diagonally, which is the content of `doubledStateField`
and `doubledFluxField` below.

## The constant

The manuscript's `4 c_{s,q}^{-1/q}` is reached exactly: the two splits each
cost one factor `sqrt 2` (CoarseGraining proves the concrete `q = 2` triangle
inequality in the `sqrt 2` form), so the two block seminorms together cost `2
sqrt 2`, and the passage from the sum of the two scalar energies to the doubled
energy costs a further `sqrt 2` -- `2 sqrt 2 * sqrt 2 = 4`.

## Exponent window

`q = 2` throughout, and `s in (0,1)`: the CoarseGraining coarse Poincare
package carries the endpoint side condition `s = 1 -> q = 1`.  Step 2 of
`l.approximate.recurrence.formula` names `s = 1` but discards `s` to `s = gamma
< 1` in its next step, so the open window is what is consumed downstream.

## Main results

* `doubledStateField`, `doubledFluxField` -- the two `R^{2d}`-valued fields on
  the display's left-hand side.
* `doubledMuValue_doubledFieldOfSolutions` -- the integrated form of
  `blockEnergyDensityAt_doubledFieldOfSolutions`:
  `mu(X) = ||sigma^{1/2} grad v||^2 + ||sigma^{1/2} grad v^*||^2`, so that
  `|| bfA^{1/2} X ||_{L^2(Q)} = sqrt(2 mu(X))`.
* `doubledCoarsePoincare_le` -- the display with the doubled energy carried as
  a named premise `henergy`.
* `doubledCoarsePoincare_le_doubledEnergy` -- the display at the manuscript's own
  right-hand side, `henergy` discharged.

## References

* ABK26, `r.cg.poincare.doubled.variables`; `p.coarse.grained.Poincare`;
  `e.bfS`; `e.findSfull`; `e.form.of.A.naught`; `e.bfA.magic.swapping`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open HCPolySupport.Book
open HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The two scaled doubled fields -/

/-- **`bfA_0^{1/2} X`** along `e.findSfull`, at `bfA_0 = diag(sigma_0,
sigma_0^{-1})`:
`(sigma_0^{1/2}(grad v + grad v^*), sigma_0^{-1/2}(a grad v - a^t grad v^*))`. -/
def doubledStateField (sig0 : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a)) :
    Vec d → BlockVec d :=
  fun x =>
    (Real.sqrt sig0 • (solutionGradientField v x + solutionGradientField vStar x),
      (Real.sqrt sig0)⁻¹ •
        (solutionFluxField Q a v x - solutionFluxField Q (adjointFamily a) vStar x))

/-- **`bfA_0^{-1/2} bfA X`**, after the swapping identity `e.bfA.magic.swapping`:
`(sigma_0^{-1/2}(a grad v + a^t grad v^*), sigma_0^{1/2}(grad v - grad v^*))`. -/
def doubledFluxField (sig0 : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a)) :
    Vec d → BlockVec d :=
  fun x =>
    ((Real.sqrt sig0)⁻¹ •
        (solutionFluxField Q a v x + solutionFluxField Q (adjointFamily a) vStar x),
      Real.sqrt sig0 • (solutionGradientField v x - solutionGradientField vStar x))

/-! ## The doubled energy

`|| bfA^{1/2} X ||_{L^2(U)}^2` is twice the mu-value of `X`, and by the pointwise identity
of `DoubledEnergyIdentity.lean` that value is the sum of the two scalar
energies.  The two lemmas below integrate the pointwise identity and use it to
discharge the doubled-energy premise of the display. -/

/-- A Chapter 2 coefficient object is an almost-everywhere elliptic field on its
own domain. -/
private theorem coeffOn_isAEEllipticFieldOn (U : Ch02.Domain d) (a : Ch02.CoeffOn U) :
    IsAEEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField :=
  ⟨U.measurableSet, a.aeStronglyMeasurable, a.aeElliptic⟩

/-- The scalar energy integrand of a Chapter 2 solution is integrable on the
domain: the flux is in `L^2` by a.e. ellipticity, and the integrand is the
`vecDot` of two `L^2` fields. -/
theorem variationEnergyIntegrand_integrableOn (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (v : Ch02.Solution U a) :
    MeasureTheory.IntegrableOn (Ch02.variationEnergyIntegrand U a v)
      (U : Set (Vec d)) MeasureTheory.volume := by
  have hEll := coeffOn_isAEEllipticFieldOn U a
  have hflux : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x)) :=
    hEll.memVectorL2_matVecMul v.toH1.grad_memVectorL2
  have hUnsym :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (v.toH1.grad x) (matVecMul (a.toCoeffField x) (v.toH1.grad x)))
        (U : Set (Vec d)) MeasureTheory.volume :=
    integrableOn_vecDot_of_memVectorL2 v.toH1.grad_memVectorL2 hflux
  refine hUnsym.congr_fun ?_ U.measurableSet
  intro x _hx
  simp only [Ch02.variationEnergyIntegrand]
  exact (vecDot_matVecMul_symmPart (a.toCoeffField x) (v.toH1.grad x)).symm

private theorem average_add (U : Ch02.Domain d) {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f (U : Set (Vec d)) MeasureTheory.volume)
    (hg : MeasureTheory.IntegrableOn g (U : Set (Vec d)) MeasureTheory.volume) :
    Ch02.average U (fun x => f x + g x) = Ch02.average U f + Ch02.average U g := by
  unfold Ch02.average
  rw [MeasureTheory.integral_add hf hg]
  ring

/-- The scalar energy value of a Chapter 2 solution is nonnegative. -/
theorem variationEnergyValue_nonneg (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (v : Ch02.Solution U a) : 0 ≤ Ch02.variationEnergyValue U a v := by
  unfold Ch02.variationEnergyValue Ch02.average
  refine mul_nonneg (by positivity) ?_
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [a.aeElliptic] with x hx
  have h1 : a.lam * vecNormSq (v.toH1.grad x) ≤
      vecDot (v.toH1.grad x) (matVecMul (a.toCoeffField x) (v.toH1.grad x)) :=
    hx.2.2.1 (v.toH1.grad x)
  have h3 : 0 ≤ a.lam * vecNormSq (v.toH1.grad x) :=
    mul_nonneg a.lam_pos.le (vecNormSq_nonneg _)
  show 0 ≤ Ch02.variationEnergyIntegrand U a v x
  simp only [Ch02.variationEnergyIntegrand]
  rw [vecDot_matVecMul_symmPart]
  linarith

/-- **The doubled energy of `e.findSfull`'s field is the sum of the two scalar
energies.**  This is the integrated form of
`blockEnergyDensityAt_doubledFieldOfSolutions`. -/
theorem doubledMuValue_doubledFieldOfSolutions (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (v : Ch02.Solution U a) (vStar : Ch02.Solution U a.transpose) :
    Ch02.doubledMuValue U a (Ch02.doubledFieldOfSolutions a v vStar) =
      Ch02.variationEnergyValue U a v + Ch02.variationEnergyValue U a.transpose vStar := by
  have hae :
      (fun x => Ch02.blockEnergyDensityAt a
          ((Ch02.doubledFieldOfSolutions a v vStar).eval x) x)
        =ᵐ[volumeMeasureOn ((U : Set (Vec d)))]
      fun x => Ch02.variationEnergyIntegrand U a v x +
        Ch02.variationEnergyIntegrand U a.transpose vStar x := by
    filter_upwards [a.aeElliptic] with x hx
    exact blockEnergyDensityAt_doubledFieldOfSolutions a v vStar
      (HCPolySupport.isUnit_det_symmPart_of_isEllipticMatrix hx)
  unfold Ch02.doubledMuValue Ch02.variationEnergyValue
  rw [Ch02.average_eq_of_ae_eq hae,
    average_add U (variationEnergyIntegrand_integrableOn U a v)
      (variationEnergyIntegrand_integrableOn U a.transpose vStar)]

/-! ## The arithmetic of the display -/

/-- The arithmetic step of `e.CG.Poincare.doubled.vars`, isolated from the analysis:
two splits each losing a factor `K`, four single-variable Poincare bounds, and
the passage to the doubled energy. -/
private theorem doubled_arith
    (c lamInvHalf LamHalf sig0Half sig0InvHalf Ev EvStar blockE
      gv gvs fv fvs lhsState lhsFlux K : ℝ)
    (hc : 0 ≤ c) (hsh : 0 ≤ sig0Half) (hsih : 0 ≤ sig0InvHalf)
    (hlam : 0 ≤ lamInvHalf) (hLam : 0 ≤ LamHalf)
    (hEv : 0 ≤ Ev) (hEvStar : 0 ≤ EvStar) (hK0 : 0 ≤ K) (hK2 : K ≤ 2)
    (pgv : gv ≤ c * lamInvHalf * Ev) (pgvs : gvs ≤ c * lamInvHalf * EvStar)
    (pfv : fv ≤ c * LamHalf * Ev) (pfvs : fvs ≤ c * LamHalf * EvStar)
    (sg : lhsState ≤ K * (sig0Half * (gv + gvs) + sig0InvHalf * (fv + fvs)))
    (sf : lhsFlux ≤ K * (sig0Half * (gv + gvs) + sig0InvHalf * (fv + fvs)))
    (en : Ev + EvStar ≤ blockE) :
    lhsState + lhsFlux ≤
      4 * c * (sig0Half * lamInvHalf + sig0InvHalf * LamHalf) * blockE := by
  set coeff := sig0Half * lamInvHalf + sig0InvHalf * LamHalf with hcoeff
  have hcoeff_nn : 0 ≤ coeff :=
    add_nonneg (mul_nonneg hsh hlam) (mul_nonneg hsih hLam)
  have hgg : gv + gvs ≤ c * lamInvHalf * (Ev + EvStar) := by nlinarith [pgv, pgvs]
  have hff : fv + fvs ≤ c * LamHalf * (Ev + EvStar) := by nlinarith [pfv, pfvs]
  have hinner :
      sig0Half * (gv + gvs) + sig0InvHalf * (fv + fvs) ≤ c * coeff * (Ev + EvStar) := by
    have e :
        sig0Half * (c * lamInvHalf * (Ev + EvStar)) +
            sig0InvHalf * (c * LamHalf * (Ev + EvStar)) =
          c * coeff * (Ev + EvStar) := by rw [hcoeff]; ring
    calc
      sig0Half * (gv + gvs) + sig0InvHalf * (fv + fvs)
          ≤ sig0Half * (c * lamInvHalf * (Ev + EvStar)) +
              sig0InvHalf * (c * LamHalf * (Ev + EvStar)) :=
            add_le_add (mul_le_mul_of_nonneg_left hgg hsh)
              (mul_le_mul_of_nonneg_left hff hsih)
      _ = c * coeff * (Ev + EvStar) := e
  have hccoeff_nn : 0 ≤ c * coeff := mul_nonneg hc hcoeff_nn
  have hE_nn : 0 ≤ c * coeff * (Ev + EvStar) :=
    mul_nonneg hccoeff_nn (add_nonneg hEv hEvStar)
  have hlhsG : lhsState ≤ K * (c * coeff * (Ev + EvStar)) :=
    le_trans sg (mul_le_mul_of_nonneg_left hinner hK0)
  have hlhsF : lhsFlux ≤ K * (c * coeff * (Ev + EvStar)) :=
    le_trans sf (mul_le_mul_of_nonneg_left hinner hK0)
  have hKE : K * (c * coeff * (Ev + EvStar)) ≤ 2 * (c * coeff * (Ev + EvStar)) :=
    mul_le_mul_of_nonneg_right hK2 hE_nn
  have henergy : c * coeff * (Ev + EvStar) ≤ c * coeff * blockE :=
    mul_le_mul_of_nonneg_left en hccoeff_nn
  calc
    lhsState + lhsFlux ≤ 4 * (c * coeff * blockE) := by linarith
    _ = 4 * c * coeff * blockE := by ring

private theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    _ = 2 := h4

/-! ## The display -/

/-- **`e.CG.Poincare.doubled.vars` at `q = 2`.**

For `s in (0,1)`, a scalar `sigma_0 > 0`, a solution `v` of `a` and a solution
`v^*` of `a^t` on the cube `Q`, the two block negative Besov seminorms of
`bfA_0^{1/2} X` and `bfA_0^{-1/2} bfA X` are jointly controlled by

```
4 c_{s,2}^{-1/2} ( sigma_0^{1/2} lambda_{s,2}^{-1/2}(Q;a)
                   + sigma_0^{-1/2} Lambda_{s,2}^{1/2}(Q;a) ) * blockE ,
```

where `blockE` dominates the sum of the two scalar energies -- the manuscript's
`|| bfA^{1/2} X ||_{L^2(Q)}` (see the module header).

on `hs`, `hs1`, `_hsig0` and `henergy`.  `_hsig0` is the source's own
positivity of the scalar `sigma_0` (`e.form.of.A.naught` at a scalar matrix);
it is carried because it is what makes `bfA_0` the matrix of that display, and
it is inert in the proof, the two diagonal factors entering only through
`Real.sqrt sig0 >= 0`.  Everything else -- the four single-variable Poincare
bounds, the adjoint identification of the two ellipticity constants, the `L^2`
memberships and the truncation bounds -- is discharged internally. -/
theorem doubledCoarsePoincare_le [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a))
    {sig0 blockE : ℝ} (_hsig0 : 0 < sig0)
    (henergy : solutionEnergyNorm Q a v +
      solutionEnergyNorm Q (adjointFamily a) vStar ≤ blockE) :
    blockNegativeBesovTwo Q s (doubledStateField sig0 Q a v vStar) +
        blockNegativeBesovTwo Q s (doubledFluxField sig0 Q a v vStar) ≤
      4 * poincareDiscountFactor s (.finite 2) *
          (Real.sqrt sig0 * poincareLowerEllipticityFactor Q a s (.finite 2) +
            (Real.sqrt sig0)⁻¹ * poincareUpperEllipticityFactor Q a s (.finite 2)) *
        blockE := by
  classical
  set G : Vec d → Vec d := solutionGradientField v with hG
  set Gs : Vec d → Vec d := solutionGradientField vStar with hGs
  set Fv : Vec d → Vec d := solutionFluxField Q a v with hFv
  set Fvs : Vec d → Vec d := solutionFluxField Q (adjointFamily a) vStar with hFvs
  have hsq0 : 0 ≤ Real.sqrt sig0 := Real.sqrt_nonneg _
  have hsq0' : 0 ≤ (Real.sqrt sig0)⁻¹ := inv_nonneg.mpr hsq0
  -- `L^2` memberships and truncation bounds
  have hmG : MemVectorL2 (cubeSet Q) G := solutionGradientField_memVectorL2 Q a v
  have hmGs : MemVectorL2 (cubeSet Q) Gs :=
    solutionGradientField_memVectorL2 Q (adjointFamily a) vStar
  have hmF : MemVectorL2 (cubeSet Q) Fv := solutionFluxField_memVectorL2 Q a v
  have hmFs : MemVectorL2 (cubeSet Q) Fvs :=
    solutionFluxField_memVectorL2 Q (adjointFamily a) vStar
  have hbG := solutionGradientField_bddAbove Q a hs v
  have hbGs := solutionGradientField_bddAbove Q (adjointFamily a) hs vStar
  have hbF := solutionFluxField_bddAbove Q a hs v
  have hbFs := solutionFluxField_bddAbove Q (adjointFamily a) hs vStar
  -- the two splits
  have sg := blockNegativeBesovTwo_doubledState_le Q s G Gs Fv Fvs
    (Real.sqrt sig0) (Real.sqrt sig0)⁻¹ hsq0 hsq0' hmG hmGs hmF hmFs hbG hbGs hbF hbFs
  have sf := blockNegativeBesovTwo_doubledFlux_le Q s G Gs Fv Fvs
    (Real.sqrt sig0) (Real.sqrt sig0)⁻¹ hsq0 hsq0' hmG hmGs hmF hmFs hbG hbGs hbF hbFs
  -- the four single-variable Poincare bounds
  have pgv := cubeBesovNegativeVectorSeminormTwo_solutionGradientField_le Q a v hs hs1
  have pfv := cubeBesovNegativeVectorSeminormTwo_solutionFluxField_le Q a v hs hs1
  have pgvs :=
    cubeBesovNegativeVectorSeminormTwo_solutionGradientField_le Q (adjointFamily a)
      vStar hs hs1
  have pfvs :=
    cubeBesovNegativeVectorSeminormTwo_solutionFluxField_le Q (adjointFamily a)
      vStar hs hs1
  -- adjoint identification of the two ellipticity constants
  have hlamAdj : poincareLowerEllipticityFactor Q (adjointFamily a) s (.finite 2) =
      poincareLowerEllipticityFactor Q a s (.finite 2) := by
    unfold poincareLowerEllipticityFactor
    rw [lambdaSq_adjointFamily]
  have hLamAdj : poincareUpperEllipticityFactor Q (adjointFamily a) s (.finite 2) =
      poincareUpperEllipticityFactor Q a s (.finite 2) := by
    unfold poincareUpperEllipticityFactor
    rw [LambdaSq_adjointFamily]
  rw [hlamAdj] at pgvs
  rw [hLamAdj] at pfvs
  -- nonnegativity of the three scalar factors
  have hc : 0 ≤ poincareDiscountFactor s (.finite 2) := by
    unfold poincareDiscountFactor
    refine Real.rpow_nonneg ?_ _
    have h := HCPolySupport.geometricDiscount_pos
      (mul_pos hs (by norm_num : (0 : ℝ) < 2))
    have hpos : 0 < Ch02.geometricDiscount s 2 := by
      simpa [Ch02.geometricDiscount, HCPolySupport.geometricDiscount] using h
    exact hpos.le
  have hlam : 0 ≤ poincareLowerEllipticityFactor Q a s (.finite 2) := by
    unfold poincareLowerEllipticityFactor
    exact Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a hs (by norm_num)) _
  have hLam : 0 ≤ poincareUpperEllipticityFactor Q a s (.finite 2) := by
    unfold poincareUpperEllipticityFactor
    exact Real.rpow_nonneg (Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)) _
  have hEv : 0 ≤ solutionEnergyNorm Q a v := Real.sqrt_nonneg _
  have hEvStar : 0 ≤ solutionEnergyNorm Q (adjointFamily a) vStar := Real.sqrt_nonneg _
  exact doubled_arith (poincareDiscountFactor s (.finite 2))
    (poincareLowerEllipticityFactor Q a s (.finite 2))
    (poincareUpperEllipticityFactor Q a s (.finite 2))
    (Real.sqrt sig0) (Real.sqrt sig0)⁻¹
    (solutionEnergyNorm Q a v) (solutionEnergyNorm Q (adjointFamily a) vStar) blockE
    (cubeBesovNegativeVectorSeminormTwo Q s G) (cubeBesovNegativeVectorSeminormTwo Q s Gs)
    (cubeBesovNegativeVectorSeminormTwo Q s Fv) (cubeBesovNegativeVectorSeminormTwo Q s Fvs)
    _ _ (Real.sqrt 2)
    hc hsq0 hsq0' hlam hLam hEv hEvStar (Real.sqrt_nonneg _) sqrt_two_le_two
    pgv pgvs pfv pfvs sg sf henergy

/-- **`e.CG.Poincare.doubled.vars` at `q = 2`, with the doubled energy in place.**
The premise `henergy` of `doubledCoarsePoincare_le` is discharged at the
manuscript's own right-hand side `|| bfA^{1/2} X ||_{L^2(Q)} = sqrt(2 mu(X))`,
so the only remaining binders are the exponent window and the positivity of the
scalar `sigma_0`. -/
theorem doubledCoarsePoincare_le_doubledEnergy [NeZero d] (Q : TriadicCube d)
    (a : CoeffFamily d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a))
    {sig0 : ℝ} (hsig0 : 0 < sig0) :
    blockNegativeBesovTwo Q s (doubledStateField sig0 Q a v vStar) +
        blockNegativeBesovTwo Q s (doubledFluxField sig0 Q a v vStar) ≤
      4 * poincareDiscountFactor s (.finite 2) *
          (Real.sqrt sig0 * poincareLowerEllipticityFactor Q a s (.finite 2) +
            (Real.sqrt sig0)⁻¹ * poincareUpperEllipticityFactor Q a s (.finite 2)) *
        Real.sqrt (2 * Ch02.doubledMuValue (Ch02.cubeDomain Q) (a.coeffOn Q)
          (Ch02.doubledFieldOfSolutions (a.coeffOn Q) v vStar)) := by
  have hnnV : 0 ≤ Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) v :=
    variationEnergyValue_nonneg _ _ _
  have hnnVs : 0 ≤ Ch02.variationEnergyValue (Ch02.cubeDomain Q)
      (a.coeffOn Q).transpose vStar :=
    variationEnergyValue_nonneg _ _ _
  have hmu := doubledMuValue_doubledFieldOfSolutions (Ch02.cubeDomain Q) (a.coeffOn Q) v vStar
  have hstep := add_le_sqrt_two_mul_add_sq
    (A := solutionEnergyNorm Q a v)
    (B := solutionEnergyNorm Q (adjointFamily a) vStar)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsqV : (solutionEnergyNorm Q a v) ^ 2 =
      Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) v := by
    unfold solutionEnergyNorm
    exact Real.sq_sqrt hnnV
  have hsqVs : (solutionEnergyNorm Q (adjointFamily a) vStar) ^ 2 =
      Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q).transpose vStar := by
    unfold solutionEnergyNorm
    exact Real.sq_sqrt hnnVs
  have henergy : solutionEnergyNorm Q a v +
      solutionEnergyNorm Q (adjointFamily a) vStar ≤
      Real.sqrt (2 * Ch02.doubledMuValue (Ch02.cubeDomain Q) (a.coeffOn Q)
        (Ch02.doubledFieldOfSolutions (a.coeffOn Q) v vStar)) := by
    rw [hmu]
    calc
      solutionEnergyNorm Q a v + solutionEnergyNorm Q (adjointFamily a) vStar
          ≤ Real.sqrt (2 * ((solutionEnergyNorm Q a v) ^ 2 +
              (solutionEnergyNorm Q (adjointFamily a) vStar) ^ 2)) := hstep
      _ = Real.sqrt (2 *
            (Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) v +
              Ch02.variationEnergyValue (Ch02.cubeDomain Q)
                (a.coeffOn Q).transpose vStar)) := by
            rw [hsqV, hsqVs]
  exact doubledCoarsePoincare_le Q a hs hs1 v vStar hsig0 henergy

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
