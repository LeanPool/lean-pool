/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ShellIncrementCap

/-!
# ShellProductControl

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The shell-corrector product of `e.lower.bound.pre2`

Step 5 of `l.approximate.recurrence.formula` needs

```
  limsup_K ( shom_{m-h}^{-2} E[ || h grad w_D^{(K)} ||^2_{L2(cu_K)} ]
             - E[ || grad w_D^{(K)} ||^2_{L2(cu_K)} ] )
    <= -(log 3) cstar shom_{m-h}^{-2} sum_{k=m-h+1}^m 3^{2 cgamma k}
       + C shom_{m-h}^{-4} h^2 3^{4 cgamma m} ,
```

"by `e.perturb.assumption`, `e.km.kn.Lp`, and Hoelder's inequality".  The
negative half is the fresh-shell corrector energy limit (lane `shellsum-limit`);
the positive half is the product estimate proved here, whose two factors are

* the corrector moment `E[|| grad w_D^{(K)} ||^4_{L4(cu_K)}]^{1/2}`, controlled
  by `e.nablaw.in.L.eight` at `C shom_{m-h}^{-2} h 3^{2 cgamma m}`.

The scale bookkeeping --- that the two factors multiply to the printed
`shom^{-4} h^2 3^{4 cgamma m}` --- is what this module proves, at the genuine
`Annealed.sigmaBar` carrier and with the genuine `rpow` exponents.  It is
unconditional: the two moment bounds enter as numeric binders, named after their
producers, and the Hoelder split itself enters as the numeric binder `hprod`.

## References

* ABK26, `e.lower.bound.pre2`; the Hoelder step.
* ABK26, `e.km.kn.Lp`; `e.nablaw.in.L.eight`.
* ABK26, `e.perturb.assumption`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The exponent bookkeeping -/

/-- The two shell factors `3^{2 cgamma m}` multiply to the printed
`3^{4 cgamma m}`. -/
theorem rpow_two_gamma_mul_self (gamma : ℝ) (m : ℝ) :
    (3 : ℝ) ^ (2 * gamma * m) * (3 : ℝ) ^ (2 * gamma * m) =
      (3 : ℝ) ^ (4 * gamma * m) := by
  rw [← Real.rpow_add (by norm_num)]
  ring_nf

/-- The two gauge factors `shom_n^{-2}` multiply to the printed
`shom_n^{-4}`. -/
theorem sigmaBar_inv_sq_mul_self (M : ABKModel d) (n : ℤ) :
    (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ =
      (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  field_simp

/-! ## The product control -/

/-- **The Hoelder product, at the recurrence carriers.**

`shellMoment` is `E[|| k_{n+h} - k_n ||^4_{L4}]^{1/2}` and `gradMoment` is
`E[|| grad w_D ||^4_{L4}]^{1/2}`; `hprod` is the Cauchy--Schwarz/Hoelder split
of `shom_n^{-2} E[|| h grad w_D ||^2_{L2}]`, whose left factor this bounds.

The conclusion is exactly the quadratic `h`-error printed in the second line of
`e.what.do.we.have` and carried by `Closure.Step5GaugeEndpoint` at `Fend = * C2`.

Binders, with their producers:

* `hgrad` --- `e.nablaw.in.L.eight` (at its own producer, not here);
* `hprod` --- the Hoelder split itself.

Unconditional. -/
theorem shellProduct_le_quadratic_error (M : ABKModel d) {n : ℤ} {h : ℕ}
    {C1 C2 shellMoment gradMoment prod : ℝ}
    (hC1 : 0 ≤ C1) (hgrad0 : 0 ≤ gradMoment)
    (hprod : prod ≤ shellMoment * gradMoment)
    (hshell : shellMoment ≤
      C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (hgrad : gradMoment ≤
      C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :
    (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * prod ≤
      (C1 * C2) * (h : ℝ) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
        (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hgauge0 : (0 : ℝ) < (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ := by positivity
  have hrpow0 : (0 : ℝ) <
      (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  -- the two factors multiply
  have hstep : shellMoment * gradMoment ≤
      (C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) *
        (C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
          (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) := by
    have hleft0 : (0 : ℝ) ≤
        C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
      positivity
    exact mul_le_mul hshell hgrad hgrad0 hleft0
  have hchain : prod ≤
      (C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) *
        (C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
          (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :=
    le_trans hprod hstep
  have hmul := mul_le_mul_of_nonneg_left hchain hgauge0.le
  refine le_trans hmul (le_of_eq ?_)
  have hgcollapse := sigmaBar_inv_sq_mul_self M n
  have hrcollapse :=
    rpow_two_gamma_mul_self M.gamma (((n + (h : ℤ) : ℤ) : ℝ))
  calc (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ *
      ((C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) *
        (C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
          (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))))
      = (C1 * C2) * (h : ℝ) ^ 2 *
          ((((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ *
            (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹) *
          ((3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) := by ring
    _ = (C1 * C2) * (h : ℝ) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
        rw [hgcollapse, hrcollapse]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
