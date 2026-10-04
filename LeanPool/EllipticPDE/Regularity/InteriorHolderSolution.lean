/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.HigherInterior
public import LeanPool.EllipticPDE.Regularity.InteriorHolderFinite


/-!
# Interior `C^{k,1/2}` estimate for the weak solution, in every dimension

`EllipticPdes.Regularity.exists_contDiffOn_holder_ball` is case (ii) of Guo's embedding
(Theorem IV.2.3) at `p = 2`: `m` orders of weak derivative on `V` give a `C^{k,1/2}`
representative on a ball whenever `k + 1 + ⌊d/2⌋ ≤ m`. It is stated over an abstract supply of
weak derivatives, which is what the iterated Sobolev ladder
`EllipticPdes.Embedding.memLp_of_gradClosed_fullStep` consumes: `⌊d/2⌋` rungs of the full step
`1/d`, one weak derivative each.

This file discharges that supply from the equation.
`EllipticPdes.Regularity.higher_interior_regularity` at order `j` gives `j + 2` orders of weak
derivative of the solution on any compact `V ⊆ Ω`, so
running it at `j = k + 1 + ⌊d/2⌋` covers the Guo condition with room to spare, and the composition
is the interior `C^{k,1/2}` estimate for the weak solution itself, in every dimension and at every
finite order `k`.

`EllipticPdes.Regularity.interior_smooth` is the same composition run at every order at once, and
concludes `C^∞` on the interior of `V`. The finite-order statement here asks finitely much of the
coefficients and of the datum, and adds the Hölder seminorm bound, which the `C^∞` statement drops.

## Main declarations

* `EllipticPdes.Regularity.interior_holder_of_weakSolution`: the interior `C^{k,1/2}` estimate for
  the weak solution, in every dimension.

## References

Y. Guo, *Partial Differential Equations*, Theorem IV.2.3(ii); L. C. Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {n : ℕ}

/-- **Interior `C^{k,1/2}` regularity of the weak solution in every dimension.** With
coefficients of enough `W^{k,∞}` regularity and a datum with enough weak derivatives, the weak
solution of `L u = f` has a representative on every interior ball that is `C^k` there and whose
`k`-th derivatives are Hölder of exponent `1/2`.

The order asked of the datum and the coefficients is the Guo threshold `k + 1 + ⌊d/2⌋` plus the
two orders `higher_interior_regularity` supplies from the equation, so the dimension enters the
hypotheses and not the conclusion. -/
theorem interior_holder_of_weakSolution (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) (k : ℕ)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1 + (n + 1) / 2 + 3))
    (hbc : IsWkInftyLower Op (k + 1 + (n + 1) / 2 + 2))
    (u : H01 Ω) (f : L2D Ω) (M : ℝ)
    (hfk : HasIteratedWeakDerivOn Ω (k + 1 + (n + 1) / 2) f) (hM : IteratedL2Bound hfk M)
    (hweak : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω)
    {c : EuclideanSpace ℝ (Fin (n + 1))} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hBV : Metric.ball c R ⊆ V) :
    ∃ w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)]
          (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (k : ℕ) w (Metric.ball c r) ∧
        ∃ Mh : ℝ≥0, HolderOnWith Mh (1 / 2 : ℝ≥0) w (Metric.ball c r) := by
  -- The equation supplies `k + 1 + ⌊d/2⌋ + 2` orders of weak derivative on `V`.
  obtain ⟨C, _hC0, hC⟩ :=
    higher_interior_regularity Op hΩm hΩo hA1 (k + 1 + (n + 1) / 2) (hA.mono (by omega))
      (hbc.mono (by omega)) hVc hVΩ
  obtain ⟨hu, _hbound⟩ := hC u f M hfk hM hweak
  -- Guo's embedding at the order the ladder needs.
  obtain ⟨w, hwae, hwcn, hwhol⟩ :=
    exists_contDiffOn_holder_ball (d := n + 1) (k := k) (Nat.succ_pos n) _ hu (by omega) hr hrR hBV
  refine ⟨w, ?_, hwcn, hwhol⟩
  -- The `V`-restriction agrees almost everywhere on the ball with the extension it came from.
  have hball : Metric.ball c r ⊆ V := (Metric.ball_subset_ball hrR.le).trans hBV
  have hres : (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))
        : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict (Metric.ball c r)]
        (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :=
    (coeFn_restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))).filter_mono
      (ae_mono (Measure.restrict_mono hball le_rfl))
  exact hwae.trans hres

end EllipticPdes.Regularity
