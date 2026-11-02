/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# ShellIncrementCap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The signed shell increment of `e.what.do.we.have`, and its absolute cap

The quantity

```
  A_{n, n+h}  =  (log 3) cstar shom_n^{-2} sum_{k = n+1}^{n+h} 3^{2 cgamma k}
```

is the signed drift printed in both lines of `e.what.do.we.build` --- more
precisely of `e.what.do.we.have` --- and is exactly `shom_n^{-2}` times the
`A_{n,m}` of `e.A.def` which `l.integrate.approx.recurrence` consumes.

This module proves the one quantitative fact about it that Step 6 needs: on the
manuscript's own shell budget `h <= 6 cstar cgamma^{-1}`, and using the lower
branch of `e.shom.h.bounds` carried by
`Algsuperdiff.Frozen.Section3.inductionState`, the drift is bounded by an
**absolute** constant, free of the model, the scale, `cgamma`, `cstar` and `h`:

```
  A_{n, n+h}  <=  36 (log 3) 3^18  =  shellIncrementCap .
```

The cap is what lets `Closure.StepSixArithmetic.ratio_le_of_switch_upper` fold
the cross term `delta * A` of the switch factor into the printed flat error `C E^2
|log cgamma|^2 cgamma`.  It is used on the upper branch only; the lower branch
drops the same cross term by its sign and needs no cap.

The proof spends the repository's own absolute bound `cstar <= 3/2`
(`Provider.Disorder.cstar_le_three_halves`) to turn `cgamma h <= 6 cstar` into
`cgamma h <= 9`; no lower bound on `cstar` is used or available.

## References

* ABK26, `e.what.do.we.have`; `e.A.def`.
* ABK26, `e.shom.h.bounds`, via `d.mathcalS.def`.
* ABK26, the shell budget `h <= 6 cstar cgamma^{-1}`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The drift -/

/-- **The signed shell increment of `e.what.do.we.have`.**

`shellDrift M n h` is `(log 3) cstar shom_n^{-2} sum_{k=n+1}^{n+h} 3^{2 gamma
k}` at the genuine running diffusivity. -/
def shellDrift (M : ABKModel d) (n : ℤ) (h : ℕ) : ℝ :=
  Real.log 3 * Disorder.cstar M * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ *
    ∑ k ∈ Finset.Icc (n + 1) (n + (h : ℤ)), (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))

/-- The absolute cap of the shell increment. -/
def shellIncrementCap : ℝ := 36 * Real.log 3 * 3 ^ (18 : ℕ)

theorem shellIncrementCap_pos : 0 < shellIncrementCap := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold shellIncrementCap
  positivity

/-! ## Nonnegativity -/

theorem shellDrift_nonneg (M : ABKModel d) (n : ℤ) (h : ℕ) :
    0 ≤ shellDrift M n h := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hc : (0 : ℝ) ≤ Disorder.cstar M := (Disorder.cstar_characterization M).1.le
  have hs : (0 : ℝ) ≤ (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ := by positivity
  have hsum : (0 : ℝ) ≤
      ∑ k ∈ Finset.Icc (n + 1) (n + (h : ℤ)), (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) :=
    Finset.sum_nonneg fun k _ => (Real.rpow_pos_of_pos (by norm_num) _).le
  unfold shellDrift
  positivity

/-! ## The geometric sum over one shell -/

/-- Each term of the shell sum is below its top term, so the sum is below
`h 3^{2 gamma (n+h)}`. -/
theorem sum_shell_le (gamma : ℝ) (hgamma : 0 < gamma) (n : ℤ) (h : ℕ) :
    ∑ k ∈ Finset.Icc (n + 1) (n + (h : ℤ)), (3 : ℝ) ^ (2 * gamma * (k : ℝ)) ≤
      (h : ℝ) * (3 : ℝ) ^ (2 * gamma * ((n : ℝ) + (h : ℝ))) := by
  have hcard : (Finset.Icc (n + 1) (n + (h : ℤ))).card = h := by
    rw [Int.card_Icc]
    simp
  have hterm : ∀ k ∈ Finset.Icc (n + 1) (n + (h : ℤ)),
      (3 : ℝ) ^ (2 * gamma * (k : ℝ)) ≤
        (3 : ℝ) ^ (2 * gamma * ((n : ℝ) + (h : ℝ))) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkle : (k : ℝ) ≤ (n : ℝ) + (h : ℝ) := by
      have := hk.2
      have hcast : ((k : ℤ) : ℝ) ≤ ((n + (h : ℤ) : ℤ) : ℝ) := Int.cast_le.mpr this
      push_cast at hcast
      linarith
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h2g : (0 : ℝ) < 2 * gamma := by linarith
    exact mul_le_mul_of_nonneg_left hkle h2g.le
  calc ∑ k ∈ Finset.Icc (n + 1) (n + (h : ℤ)), (3 : ℝ) ^ (2 * gamma * (k : ℝ))
      ≤ ∑ _k ∈ Finset.Icc (n + 1) (n + (h : ℤ)),
          (3 : ℝ) ^ (2 * gamma * ((n : ℝ) + (h : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (h : ℝ) * (3 : ℝ) ^ (2 * gamma * ((n : ℝ) + (h : ℝ))) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-! ## The cap -/

/-- **The shell increment is bounded by an absolute constant.**

Binders: `hstate` is the induction state `S(m0, E)` of the manuscript
(`d.mathcalS.def`), whose first clause is `e.shom.h.bounds`; `hn` places the
reading scale in its range; `hh` is the manuscript's shell budget `h <= 6 cstar
cgamma^{-1}`.

Only the *lower* branch of `e.shom.h.bounds` is used, and only through its
`cstar cgamma^{-1} 3^{2 gamma n}` half; the `nu^2` half of the `max` and the
whole upper branch are discarded. -/
theorem shellDrift_le_cap (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n ≤ m0) {h : ℕ}
    (hh : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹) :
    shellDrift M n h ≤ shellIncrementCap := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hginv0 : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgamma0
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hlog0 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  -- the lower branch of `e.shom.h.bounds`, restricted to its geometric half
  have hlow := (hstate.1 n hn).1
  have hgeo : Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) ≤
      max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) (M.nu ^ 2) :=
    le_max_left _ _
  have hsig : (1 / 4 : ℝ) * (Disorder.cstar M * M.gamma⁻¹ *
      (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) ≤ (Annealed.sigmaBar M n : ℝ) ^ 2 := by
    refine le_trans ?_ hlow
    exact mul_le_mul_of_nonneg_left hgeo (by norm_num)
  have hgeopos : (0 : ℝ) < Disorder.cstar M * M.gamma⁻¹ *
      (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 3 by norm_num) (2 * M.gamma * (n : ℝ))
    positivity
  have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (1 / 4 : ℝ) * (Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) := by positivity
    linarith
  -- invert
  have hinv : (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ ≤
      4 * M.gamma * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ))) := by
    have hkey : (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ ≤
        ((1 / 4 : ℝ) * (Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))))⁻¹ := by
      refine inv_anti₀ ?_ hsig
      positivity
    refine le_trans hkey (le_of_eq ?_)
    rw [Real.rpow_neg (by norm_num)]
    field_simp
  -- the sum
  have hsum := sum_shell_le M.gamma hgamma0 n h
  have hsum0 : (0 : ℝ) ≤
      ∑ k ∈ Finset.Icc (n + 1) (n + (h : ℤ)), (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) :=
    Finset.sum_nonneg fun k _ => (Real.rpow_pos_of_pos (by norm_num) _).le
  -- the exponent collapse
  have hcollapse : (3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ))) *
      (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (h : ℝ))) =
      (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  -- `2 gamma h <= 18`
  have hgh : M.gamma * (h : ℝ) ≤ 9 := by
    have h1 : M.gamma * (h : ℝ) ≤ M.gamma * (6 * Disorder.cstar M * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hh hgamma0.le
    have h2 : M.gamma * (6 * Disorder.cstar M * M.gamma⁻¹) = 6 * Disorder.cstar M := by
      field_simp
    rw [h2] at h1
    linarith
  have hpow18 : (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) ≤ (3 : ℝ) ^ (18 : ℕ) := by
    have hmono : (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) ≤ (3 : ℝ) ^ ((18 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    rwa [Real.rpow_natCast] at hmono
  -- assemble
  have hpow0 : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hstep : shellDrift M n h ≤
      Real.log 3 * Disorder.cstar M *
        (4 * M.gamma * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ)))) *
        ((h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (h : ℝ)))) := by
    unfold shellDrift
    have hA : (0 : ℝ) ≤ Real.log 3 * Disorder.cstar M := by positivity
    have h1 : Real.log 3 * Disorder.cstar M * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ ≤
        Real.log 3 * Disorder.cstar M *
          (4 * M.gamma * (Disorder.cstar M)⁻¹ *
            (3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hinv hA
    have h2 : (0 : ℝ) ≤ Real.log 3 * Disorder.cstar M *
        (4 * M.gamma * (Disorder.cstar M)⁻¹ *
          (3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ)))) := by
      have := Real.rpow_pos_of_pos (show (0:ℝ) < 3 by norm_num)
        (-(2 * M.gamma * (n : ℝ)))
      positivity
    exact mul_le_mul h1 hsum hsum0 h2
  refine le_trans hstep ?_
  have hrewrite : Real.log 3 * Disorder.cstar M *
      (4 * M.gamma * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ)))) *
      ((h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (h : ℝ)))) =
      4 * Real.log 3 * (M.gamma * (h : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) := by
    have hcs : Disorder.cstar M * (Disorder.cstar M)⁻¹ = 1 :=
      mul_inv_cancel₀ hcstar0.ne'
    calc Real.log 3 * Disorder.cstar M *
        (4 * M.gamma * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ)))) *
        ((h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (h : ℝ))))
        = 4 * Real.log 3 * (Disorder.cstar M * (Disorder.cstar M)⁻¹) *
            (M.gamma * (h : ℝ)) *
            ((3 : ℝ) ^ (-(2 * M.gamma * (n : ℝ))) *
              (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (h : ℝ)))) := by ring
      _ = 4 * Real.log 3 * (M.gamma * (h : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) := by rw [hcs, hcollapse]; ring
  rw [hrewrite]
  have hgh0 : (0 : ℝ) ≤ M.gamma * (h : ℝ) := by positivity
  unfold shellIncrementCap
  have hstep1 : 4 * Real.log 3 * (M.gamma * (h : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) ≤
      4 * Real.log 3 * 9 * (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) := by
    have : 4 * Real.log 3 * (M.gamma * (h : ℝ)) ≤ 4 * Real.log 3 * 9 :=
      mul_le_mul_of_nonneg_left hgh (by linarith only [hlog0])
    exact mul_le_mul_of_nonneg_right this hpow0.le
  have hstep2 : 4 * Real.log 3 * 9 * (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) ≤
      4 * Real.log 3 * 9 * (3 : ℝ) ^ (18 : ℕ) := by
    have h0 : (0 : ℝ) ≤ 4 * Real.log 3 * 9 := by positivity
    exact mul_le_mul_of_nonneg_left hpow18 h0
  linarith only [hstep1, hstep2]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
