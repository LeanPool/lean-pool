/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# PerCubeFluctuationArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the per-cube fluctuation arithmetic of Step 2

Source displays in ABK26, inside Step 2 of `l.approximate.recurrence.formula`:

* The Euler--Lagrange identity followed by the block Besov duality bound
  ```
  fint tilde S_z . bfA_m tilde S_z
    = fint bfF_z . bfA_m tilde S_z
    <= [bfAhom^{1/2} bfF_z]_{H^1} [bfAhom^{-1/2} bfA_m tilde S_z]_{H^{-1}};
  ```

* The doubled coarse-grained Poincare inequality `e.CG.Poincare.doubled.vars`,
which bounds the `H^{-1}` factor **linearly** in `|| bfA_m^{1/2} tilde S_z ||`;
* The resulting bound on `|| bfA_m^{1/2} tilde S_z ||` itself, obtained by
  cancelling one power, and the companion cross-term bound for `P_z. fint bfA_m
  tilde S_z`;
* The display `e.lower.bound.localization.terms`, whose bracketed integrand is
  `2 P_z. fint bfA_m tilde S_z + fint tilde S_z. bfA_m tilde S_z`.

## Scope: arithmetic only

Everything below is **abstract real arithmetic** over bare real variables.  No
cube, no seminorm, no coefficient field, no minimizer and no gauge occurs, and
this module imports nothing but `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
The three analytic inputs of the displays above --- the block Besov duality
bound, the doubled coarse-grained Poincare inequality, and the Euler--Lagrange
identity that supplies the quadratic value --- appear here only as the named
real hypotheses `hquad`, `hpoin`, `hquadval` and `hcross`.  Each is a caller
obligation, to be discharged by the caller at whatever carrier it works on;
this module neither states nor proves any of them.  Isolating the algebra here
keeps every numeric tactic away from `Real.rpow` terms.

Under the intended instantiation `blockE = || bfA_m^{1/2} tilde S_z ||`,
`E = fint tilde S_z . bfA_m tilde S_z / 2`,
`Bu = [bfAhom^{-1/2} bfA_m tilde S_z]_{H^{-1}}`,
`Bg = [bfAhom^{1/2} bfF_z]_{H^1}`, `normP = | bfAhom^{1/2} P_z |`, `kappa` the
block Besov duality constant and `Theta` the doubled-Poincare ellipticity
factor.
-/

namespace Algsuperdiff.Section3.Provider.Variational

/-- **Self-improvement.**  A nonnegative quantity whose square is dominated by a
nonnegative multiple of itself is dominated by that multiple.  This is the step
that turns a quadratic bound plus a linear Poincare bound into a bound on the
quantity itself. -/
theorem le_of_mul_self_le_mul_of_nonneg {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A)
    (h : t * t ≤ A * t) : t ≤ A := by
  rcases eq_or_lt_of_le ht with hzero | hpos
  · exact hzero ▸ hA
  · exact le_of_mul_le_mul_right (by linarith only [h]) hpos

/-- **The self-improved bound on `|| bfA_m^{1/2} tilde S_z ||`, over abstract
reals.**  If the doubled energy `E` satisfies the duality bound `2E ≤ kappa (Bu
Bg)`, the Poincare bound `Bu ≤ Theta blockE` holds, and
`blockE² = 2E`, then `blockE ≤ kappa Theta Bg`.

Conditional helper A: `hsq`, `hquad` and `hpoin` are caller obligations. -/
theorem blockEnergyNorm_le_of_poincare_bound
    {E blockE Bu Bg kappa Theta : ℝ}
    (hblockE : 0 ≤ blockE) (hsq : blockE * blockE = 2 * E)
    (hkappa : 0 ≤ kappa) (hBg : 0 ≤ Bg) (hTheta : 0 ≤ Theta)
    (hquad : 2 * E ≤ kappa * (Bu * Bg))
    (hpoin : Bu ≤ Theta * blockE) :
    blockE ≤ kappa * Theta * Bg := by
  have hstep : blockE * blockE ≤ (kappa * Theta * Bg) * blockE := by
    have h1 : blockE * blockE ≤ kappa * (Bu * Bg) := hsq ▸ hquad
    have h2 : Bu * Bg ≤ (Theta * blockE) * Bg := mul_le_mul_of_nonneg_right hpoin hBg
    have h3 : kappa * (Bu * Bg) ≤ kappa * ((Theta * blockE) * Bg) :=
      mul_le_mul_of_nonneg_left h2 hkappa
    have h4 : kappa * ((Theta * blockE) * Bg) = (kappa * Theta * Bg) * blockE := by ring
    linarith only [h1, h3, h4.le, h4.ge]
  refine le_of_mul_self_le_mul_of_nonneg hblockE ?_ hstep
  exact mul_nonneg (mul_nonneg hkappa hTheta) hBg

/-- **The bracketed integrand, per cube, over abstract reals.** Combining the
cross-term bound, the duality bound coming from the Euler--Lagrange identity
and the Poincare self-improvement:

```
2 P_z . fint bfA_m tilde S_z + fint tilde S_z . bfA_m tilde S_z
  <= 2 kappa Theta² normP Bg + (kappa Theta Bg)² .
```

Both summands carry exactly the manuscript's power of the ellipticity factor:
once in the cross term and once in the quadratic term.

Conditional helper A: `hsq`, `hcross`, `hquad`, `hpoin` and `hquadval` are
caller obligations, to be discharged at the caller's carrier. -/
theorem perCube_fluct_le
    {cross quad E blockE Bu Bg kappa Theta normP : ℝ}
    (hnormP : 0 ≤ normP) (hkappa : 0 ≤ kappa) (hBg : 0 ≤ Bg) (hTheta : 0 ≤ Theta)
    (hblockE : 0 ≤ blockE) (hsq : blockE * blockE = 2 * E)
    (hcross : cross ≤ normP * Bu)
    (hquad : 2 * E ≤ kappa * (Bu * Bg))
    (hpoin : Bu ≤ Theta * blockE)
    (hquadval : quad = 2 * E) :
    2 * cross + quad ≤
      2 * (kappa * Theta * Theta) * normP * Bg
        + (kappa * Theta * Bg) * (kappa * Theta * Bg) := by
  have hblock : blockE ≤ kappa * Theta * Bg :=
    blockEnergyNorm_le_of_poincare_bound hblockE hsq hkappa hBg hTheta hquad hpoin
  have hBu : Bu ≤ Theta * (kappa * Theta * Bg) :=
    hpoin.trans (mul_le_mul_of_nonneg_left hblock hTheta)
  have hcross' : cross ≤ normP * (Theta * (kappa * Theta * Bg)) :=
    hcross.trans (mul_le_mul_of_nonneg_left hBu hnormP)
  have hquad' : quad ≤ (kappa * Theta * Bg) * (kappa * Theta * Bg) := by
    have hq : quad = blockE * blockE := by rw [hquadval, hsq]
    rw [hq]
    exact mul_le_mul hblock hblock hblockE
      (mul_nonneg (mul_nonneg hkappa hTheta) hBg)
  have heq : 2 * (normP * (Theta * (kappa * Theta * Bg)))
      = 2 * (kappa * Theta * Theta) * normP * Bg := by ring
  linarith only [hcross', hquad', heq.le, heq.ge]

end Algsuperdiff.Section3.Provider.Variational
