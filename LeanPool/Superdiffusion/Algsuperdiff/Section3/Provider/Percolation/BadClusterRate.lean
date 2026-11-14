/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.SiteFamilyTails
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.BadClusterGates

/-!
# BadClusterRate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The amended bad-cluster admissibility and the gates it discharges

ABK26's Lemma `l.percolation.bad.clusters` applies the abstract percolation
lemma at the rate `T^2 = c E^{-2} gamma^{-1}` under the printed admissibility
display `e.percolation.admissibility.bad.clusters`

```
E >= exp(C sigma^{-1}) or C c_star^{-1}      and      gamma <= E^{-5} .
```

## The additional admissibility requirement

```
E >= C b^{-1} ,
```

with `C = C(d)` still dimension-only, so the node contract's`C depends only on
d` stands unchanged.  The reason is the diameter half: the conclusion needs a
union bound over `~3^{dh}` lattice translates of the crossing event, uniformly
in `h`, and paying the entropy `d h log 3` against the gain `e^{-40/sigma} T^2
3^{(1-sigma) b h}` for ALL `h` requires (through `sup_h h 3^{-(1-sigma) b h} <=
((1-sigma) b log 3)^{-1}`) a rate of strength `T^2 >~ d e^{40/sigma} b^{-1}`.
The printed display is `b`-free and cannot supply the `b^{-1}`.

## Why the rate is not the sharp oscillation rate

The site family of `l.percolation.bad.clusters` is a union over the
nine-generation descendant tree of *two* branches, so its honest per-scale rate
is `badRateConst d / 2 = min(delta_osc^2/25, 1/512)/2`
(`SiteFamilyTails.lean`), further discounted by the reindexing shift.  This
module therefore re-derives every gate at the true rate `siteRateSq`, reusing
only the *rate-agnostic* lemmas `densityThreshold_of_le` and
`one_le_densityExponent` of `BadClusterGates.lean`.

## Main definitions

* `badClustersAmplitude`: the dimension-only quantity all gates are measured
  against.
* `badClustersConst`: the explicit `C(d)` of the amended admissibility display.

## Main results

* `le_cube_of_admissible`: the master arithmetic step
  `A e^{40/sigma} b^{-1} <= E^3`.
* `treeCountGate_of_admissible`, `four_le_siteRateSq`,
  `percolationGate_of_admissible'`, `densityAmplitude_le_sqrt_siteRateSq`,
  `densityExponentAmplitude_le_siteRateSq`, `entropyGate_of_admissible`: the six
  gates of the node, all at `badClustersConst d`.

## References

* ABK26, `l.percolation.bad.clusters`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open HCPolySupport
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The dimension-only amplitude and constant -/

/-- The dimension-only quantity that every gate of the node is measured
against.  The first summand is the descendant-tree count gate of
`SiteFamilyTails`; the second collects the five gates that are lower bounds on
the reindexed rate `siteRateSq`. -/
def badClustersAmplitude (d : ℕ) : ℝ :=
  2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) / badRateConst d +
    (4 + 32 * (d : ℝ) + 2 * (1 + 2 * (d : ℝ)) + densityAmplitude d ^ 2 +
      densityExponentAmplitude d) / siteRateBase d

/-- The explicit dimension-only `C(d)` of the amended admissibility display
`e.percolation.admissibility.bad.clusters` (as amended). -/
def badClustersConst (d : ℕ) : ℝ :=
  max (max 21 (admissibleConst d))
    ((80 + Real.log (badClustersAmplitude d)) / 4)

theorem twentyOne_le_badClustersConst (d : ℕ) : (21 : ℝ) ≤ badClustersConst d :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem badClustersConst_pos (d : ℕ) : 0 < badClustersConst d :=
  lt_of_lt_of_le (by norm_num) (twentyOne_le_badClustersConst d)

theorem admissibleConst_le_badClustersConst (d : ℕ) :
    admissibleConst d ≤ badClustersConst d :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem log_badClustersAmplitude_le (d : ℕ) :
    (80 + Real.log (badClustersAmplitude d)) / 4 ≤ badClustersConst d :=
  le_max_right _ _

/-! ## Positivity of the amplitude's ingredients -/

theorem densityExponentAmplitude_pos (hd : 2 ≤ d) : 0 < densityExponentAmplitude d := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hda : (0 : ℝ) < (d : ℝ) - 3 / 2 := by linarith
  have h1 : 0 < densityBoundExpConst d := densityBoundExpConst_pos (by omega)
  rw [densityExponentAmplitude]
  exact inv_pos.2 (mul_pos (mul_pos h1 (by norm_num)) (pow_pos hda 2))

/-- The bracket of the second summand of `badClustersAmplitude`. -/
def rateBracket (d : ℕ) : ℝ :=
  4 + 32 * (d : ℝ) + 2 * (1 + 2 * (d : ℝ)) + densityAmplitude d ^ 2 +
    densityExponentAmplitude d

private theorem log20_pos : (0 : ℝ) < Real.log 20 := Real.log_pos (by norm_num)


private theorem treeBranch_pos (d : ℕ) :
    0 < 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) / badRateConst d := by
  have h1 : (0 : ℝ) ≤ 9 * (d : ℝ) * Real.log 3 := by positivity
  have h2 := log20_pos
  have h3 := badRateConst_pos d
  have h4 : (0 : ℝ) < 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) := by linarith
  exact div_pos h4 h3

private theorem rateBracket_pos (hd : 2 ≤ d) : 0 < rateBracket d := by
  have h1 : (0 : ℝ) ≤ 32 * (d : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 * (1 + 2 * (d : ℝ)) := by positivity
  have h3 : (0 : ℝ) ≤ densityAmplitude d ^ 2 := sq_nonneg _
  have h4 := densityExponentAmplitude_pos hd
  rw [rateBracket]
  linarith


/-- Every gate on the rate is measured against `badClustersAmplitude d`. -/
private theorem div_siteRateBase_le_amplitude {x : ℝ}
    (hx : x ≤ rateBracket d) : x / siteRateBase d ≤ badClustersAmplitude d := by
  have hS : 0 < siteRateBase d := siteRateBase_pos d
  have hSinv : (0 : ℝ) ≤ (siteRateBase d)⁻¹ := (inv_pos.2 hS).le
  have h1 : x * (siteRateBase d)⁻¹ ≤ rateBracket d * (siteRateBase d)⁻¹ :=
    mul_le_mul_of_nonneg_right hx hSinv
  have h2 := treeBranch_pos d
  have hxd : x / siteRateBase d = x * (siteRateBase d)⁻¹ := div_eq_mul_inv _ _
  have hbd : rateBracket d / siteRateBase d = rateBracket d * (siteRateBase d)⁻¹ :=
    div_eq_mul_inv _ _
  have hamp : badClustersAmplitude d =
      2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) / badRateConst d +
        rateBracket d / siteRateBase d := rfl
  rw [hxd, hamp, hbd]
  linarith

/-! ## The master arithmetic step -/

/-- **The master step.**  The amended admissibility at `badClustersConst d`
turns any dimension-only amplitude `A` into the bound
`A e^{40/sigma} b^{-1} <= E^3`.  The `e^{40/sigma}` comes from `E >= exp(C/sigma)`
and `sigma <= 1/2`; the `b^{-1}` comes from the additional
requirement `E >= C b^{-1}`. -/
theorem le_cube_of_admissible {E sigma b A : ℝ}
    (hA0 : 0 < A) (hAle : A ≤ badClustersAmplitude d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E) :
    A * Real.exp (40 / sigma) / b ≤ E ^ 3 := by
  set C : ℝ := badClustersConst d with hCdef
  have hC21 : (21 : ℝ) ≤ C := twentyOne_le_badClustersConst d
  have hCpos : (0 : ℝ) < C := by linarith
  have hAmp : 0 < badClustersAmplitude d := lt_of_lt_of_le hA0 hAle
  have hbranch : (80 + Real.log (badClustersAmplitude d)) / 4 ≤ C :=
    log_badClustersAmplitude_le d
  have hlogA : Real.log A ≤ Real.log (badClustersAmplitude d) :=
    Real.log_le_log hA0 hAle
  have h4C : Real.log A ≤ 4 * C - 80 := by linarith
  have hAexp : A ≤ Real.exp (4 * C - 80) := by
    calc A = Real.exp (Real.log A) := (Real.exp_log hA0).symm
      _ ≤ Real.exp (4 * C - 80) := Real.exp_le_exp.2 h4C
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le (Real.exp_pos _) hE
  have hinv : (2 : ℝ) ≤ sigma⁻¹ := by
    have h1 := inv_anti₀ hsigma0 hsigma
    rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at h1
  have hsq : Real.exp (C / sigma) ^ 2 ≤ E ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hE 2
  have hCb0 : (0 : ℝ) < C / b := div_pos hCpos hb0
  have hcube : C / b * Real.exp (C / sigma) ^ 2 ≤ E ^ 3 := by
    have h := mul_le_mul hEb hsq (sq_nonneg _) hE0.le
    calc C / b * Real.exp (C / sigma) ^ 2 ≤ E * E ^ 2 := h
      _ = E ^ 3 := by ring
  have hsqid : Real.exp (C / sigma) ^ 2 = Real.exp (2 * (C / sigma)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsplit : Real.exp (2 * (C / sigma)) =
      Real.exp (2 * (C / sigma) - 40 / sigma) * Real.exp (40 / sigma) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsurplus : 4 * C - 80 ≤ 2 * (C / sigma) - 40 / sigma := by
    have hrw : 2 * (C / sigma) - 40 / sigma = (2 * C - 40) * sigma⁻¹ := by
      field_simp
    rw [hrw]
    linarith only [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * C - 40)
      (by linarith : (0 : ℝ) ≤ sigma⁻¹ - 2)]
  have hstep : A * Real.exp (40 / sigma) ≤ C * Real.exp (C / sigma) ^ 2 := by
    have h1 : A * Real.exp (40 / sigma) ≤ Real.exp (4 * C - 80) * Real.exp (40 / sigma) :=
      mul_le_mul_of_nonneg_right hAexp (Real.exp_pos _).le
    have h2 : Real.exp (4 * C - 80) * Real.exp (40 / sigma) ≤
        Real.exp (C / sigma) ^ 2 := by
      rw [hsqid, hsplit]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hsurplus) (Real.exp_pos _).le
    have h3 : Real.exp (C / sigma) ^ 2 ≤ C * Real.exp (C / sigma) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (by linarith)
    linarith
  have hbinv : (0 : ℝ) < b⁻¹ := inv_pos.2 hb0
  calc A * Real.exp (40 / sigma) / b = A * Real.exp (40 / sigma) * b⁻¹ := by
        rw [div_eq_mul_inv]
    _ ≤ C * Real.exp (C / sigma) ^ 2 * b⁻¹ := mul_le_mul_of_nonneg_right hstep hbinv.le
    _ = C / b * Real.exp (C / sigma) ^ 2 := by rw [div_eq_mul_inv]; ring
    _ ≤ E ^ 3 := hcube

/-- The master step with the `b^{-1}` slack discarded. -/
theorem le_cube_of_admissible_exp {E sigma b A : ℝ}
    (hA0 : 0 < A) (hAle : A ≤ badClustersAmplitude d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E) :
    A * Real.exp (40 / sigma) ≤ E ^ 3 := by
  have hbase := le_cube_of_admissible hA0 hAle hsigma0 hsigma hb0 hE hEb
  have hApos : (0 : ℝ) < A * Real.exp (40 / sigma) := by positivity
  have hle : A * Real.exp (40 / sigma) ≤ A * Real.exp (40 / sigma) / b := by
    rw [le_div_iff₀ hb0]
    exact mul_le_of_le_one_right hApos.le hb1
  linarith

/-- The master step with both slacks discarded. -/
theorem le_cube_of_admissible_plain {E sigma b A : ℝ}
    (hA0 : 0 < A) (hAle : A ≤ badClustersAmplitude d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E) :
    A ≤ E ^ 3 := by
  have hbase := le_cube_of_admissible_exp hA0 hAle hsigma0 hsigma hb0 hb1 hE hEb
  have hexp1 : (1 : ℝ) ≤ Real.exp (40 / sigma) := by
    have h0 : (0 : ℝ) ≤ 40 / sigma := by positivity
    have := Real.add_one_le_exp (40 / sigma)
    linarith
  calc A = A * 1 := (mul_one A).symm
    _ ≤ A * Real.exp (40 / sigma) := mul_le_mul_of_nonneg_left hexp1 hA0.le
    _ ≤ E ^ 3 := hbase

/-! ## The standing consequences of the amended display -/

/-- The amended display forces `E >= 1`. -/
theorem one_le_of_admissible {E sigma : ℝ} (hsigma0 : 0 < sigma)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E) : 1 ≤ E := by
  have hC : (0 : ℝ) < badClustersConst d := badClustersConst_pos d
  have hx : (0 : ℝ) ≤ badClustersConst d / sigma := le_of_lt (div_pos hC hsigma0)
  have hexp : Real.exp 0 ≤ Real.exp (badClustersConst d / sigma) := Real.exp_le_exp.2 hx
  rw [Real.exp_zero] at hexp
  linarith


/-! ## The six gates at the true rate -/

/-- **Gate 1: the descendant-tree count.**  The gate `hEabs` of
`measureReal_badScaleEvent_le`. -/
theorem treeCountGate_of_admissible {E sigma b : ℝ} (hd : 2 ≤ d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E) :
    2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) ≤ badRateConst d * E ^ 3 := by
  have hkappa : 0 < badRateConst d := badRateConst_pos d
  have hA0 := treeBranch_pos d
  have hAle : 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) / badRateConst d ≤
      badClustersAmplitude d := by
    have h2 : 0 < rateBracket d / siteRateBase d :=
      div_pos (rateBracket_pos hd) (siteRateBase_pos d)
    rw [badClustersAmplitude]
    rw [rateBracket] at h2
    linarith
  have hbase := le_cube_of_admissible_plain hA0 hAle hsigma0 hsigma hb0 hb1 hE hEb
  have hmul := mul_le_mul_of_nonneg_left hbase hkappa.le
  have heq : badRateConst d * (2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) /
      badRateConst d) = 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) := by
    field_simp
  rw [heq] at hmul
  exact hmul

/-- `siteRateSq` dominates the dimension-only multiple `siteRateBase d E^3`. -/
theorem siteRateBase_mul_cube_le (M : ABKModel d) {E : ℝ} (hE : 1 ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    siteRateBase d * E ^ 3 ≤ siteRateSq M E := by
  rw [siteRateSq]
  exact mul_le_mul_of_nonneg_left (cube_le_invSq_mul_gammaInv M hE hgamma)
    (siteRateBase_pos d).le

/-- The generic rate gate: any bracket-dominated amplitude, discounted by
`siteRateBase d`, is met by the rate. -/
private theorem rate_gate {M : ABKModel d} {E sigma b x : ℝ}
    (hx0 : 0 < x) (hx : x ≤ rateBracket d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    x ≤ siteRateSq M E := by
  have hS : 0 < siteRateBase d := siteRateBase_pos d
  have hA0 : 0 < x / siteRateBase d := div_pos hx0 hS
  have hAle := div_siteRateBase_le_amplitude hx
  have hcube := le_cube_of_admissible_plain hA0 hAle hsigma0 hsigma hb0 hb1 hE hEb
  have hbase := siteRateBase_mul_cube_le M (one_le_of_admissible hsigma0 hE) hgamma
  have hmul := mul_le_mul_of_nonneg_left hcube hS.le
  have heq : siteRateBase d * (x / siteRateBase d) = x := by field_simp
  rw [heq] at hmul
  linarith

/-- The generic rate gate with a factor `e^{40/sigma}`. -/
private theorem rate_gate_exp {M : ABKModel d} {E sigma b x : ℝ}
    (hx0 : 0 < x) (hx : x ≤ rateBracket d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    x * Real.exp (40 / sigma) ≤ siteRateSq M E := by
  have hS : 0 < siteRateBase d := siteRateBase_pos d
  have hA0 : 0 < x / siteRateBase d := div_pos hx0 hS
  have hAle := div_siteRateBase_le_amplitude hx
  have hcube := le_cube_of_admissible_exp hA0 hAle hsigma0 hsigma hb0 hb1 hE hEb
  have hbase := siteRateBase_mul_cube_le M (one_le_of_admissible hsigma0 hE) hgamma
  have hmul := mul_le_mul_of_nonneg_left hcube hS.le
  have heq : siteRateBase d * (x / siteRateBase d * Real.exp (40 / sigma)) =
      x * Real.exp (40 / sigma) := by field_simp
  rw [heq] at hmul
  linarith

/-- The generic rate gate with factors `e^{40/sigma}` and `b^{-1}`. -/
private theorem rate_gate_exp_div {M : ABKModel d} {E sigma b x : ℝ}
    (hx0 : 0 < x) (hx : x ≤ rateBracket d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    x * Real.exp (40 / sigma) / b ≤ siteRateSq M E := by
  have hS : 0 < siteRateBase d := siteRateBase_pos d
  have hA0 : 0 < x / siteRateBase d := div_pos hx0 hS
  have hAle := div_siteRateBase_le_amplitude hx
  have hcube := le_cube_of_admissible hA0 hAle hsigma0 hsigma hb0 hE hEb
  have hbase := siteRateBase_mul_cube_le M (one_le_of_admissible hsigma0 hE) hgamma
  have hmul := mul_le_mul_of_nonneg_left hcube hS.le
  have heq : siteRateBase d * (x / siteRateBase d * Real.exp (40 / sigma) / b) =
      x * Real.exp (40 / sigma) / b := by field_simp
  rw [heq] at hmul
  linarith

/-- **Gate 2: the unit rate.**  The abstract percolation layer needs `T >= 1`;
the amended admissibility gives the stronger `T^2 >= 4`. -/
theorem four_le_siteRateSq (M : ABKModel d) {E sigma b : ℝ} (hd : 2 ≤ d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    4 ≤ siteRateSq M E := by
  refine rate_gate (M := M) (by norm_num) ?_ hsigma0 hsigma hb0 hb1 hE hEb hgamma
  have h1 : (0 : ℝ) ≤ 32 * (d : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 * (1 + 2 * (d : ℝ)) := by positivity
  have h3 : (0 : ℝ) ≤ densityAmplitude d ^ 2 := sq_nonneg _
  have h4 := densityExponentAmplitude_pos hd
  rw [rateBracket]
  linarith

theorem one_le_siteRateSq (M : ABKModel d) {E sigma b : ℝ} (hd : 2 ≤ d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    1 ≤ siteRateSq M E := by
  have := four_le_siteRateSq M hd hsigma0 hsigma hb0 hb1 hE hEb hgamma
  linarith

/-- **Gate 3: the percolation threshold**, at the manuscript's own conclusion
exponent `b = 1 - sigma` of `e.diameter.bound` and at the T rate `siteRateSq`.
-/
theorem percolationGate_of_admissible' (M : ABKModel d) {E sigma b : ℝ} (hd : 2 ≤ d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    16 * (d : ℝ) * Real.exp (40 / (1 - (1 - sigma))) ≤ siteRateSq M E * (1 - sigma) := by
  have hbracket : 32 * (d : ℝ) ≤ rateBracket d := by
    have h3 : (0 : ℝ) ≤ densityAmplitude d ^ 2 := sq_nonneg _
    have h4 := densityExponentAmplitude_pos hd
    have h2 : (0 : ℝ) ≤ 2 * (1 + 2 * (d : ℝ)) := by positivity
    rw [rateBracket]
    linarith
  have hd0 : (0 : ℝ) < 32 * (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hgate := rate_gate_exp (M := M) hd0 hbracket hsigma0 hsigma hb0 hb1 hE hEb hgamma
  have hone : (1 : ℝ) - (1 - sigma) = sigma := by ring
  rw [hone]
  have hS0 : (0 : ℝ) ≤ siteRateSq M E := by
    have := one_le_siteRateSq M hd hsigma0 hsigma hb0 hb1 hE hEb hgamma
    linarith
  have hhalf : (1 : ℝ) / 2 ≤ 1 - sigma := by linarith
  have hprod : siteRateSq M E * (1 / 2) ≤ siteRateSq M E * (1 - sigma) :=
    mul_le_mul_of_nonneg_left hhalf hS0
  linarith

/-- **Gate 4: the density range.**  The amplitude of `densityThreshold_of_le` at
the manuscript's `a = 3/2`. -/
theorem densityAmplitude_le_sqrt_siteRateSq (M : ABKModel d) {E sigma b : ℝ}
    (hd : 2 ≤ d) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    densityAmplitude d ≤ Real.sqrt (siteRateSq M E) := by
  have hApos : 0 < densityAmplitude d := densityAmplitude_pos hd
  have hbracket : densityAmplitude d ^ 2 ≤ rateBracket d := by
    have h1 : (0 : ℝ) ≤ 32 * (d : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (1 + 2 * (d : ℝ)) := by positivity
    have h4 := densityExponentAmplitude_pos hd
    rw [rateBracket]
    linarith
  have hgate := rate_gate (M := M) (pow_pos hApos 2) hbracket hsigma0 hsigma hb0 hb1
    hE hEb hgamma
  have hsq := Real.sqrt_le_sqrt hgate
  rwa [Real.sqrt_sq hApos.le] at hsq

/-- **Gate 5: the exponent.**  The amplitude of `one_le_densityExponent`. -/
theorem densityExponentAmplitude_le_siteRateSq (M : ABKModel d) {E sigma b : ℝ}
    (hd : 2 ≤ d) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    densityExponentAmplitude d ≤ siteRateSq M E := by
  have hbracket : densityExponentAmplitude d ≤ rateBracket d := by
    have h1 : (0 : ℝ) ≤ 32 * (d : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (1 + 2 * (d : ℝ)) := by positivity
    have h3 : (0 : ℝ) ≤ densityAmplitude d ^ 2 := sq_nonneg _
    rw [rateBracket]
    linarith
  exact rate_gate (M := M) (densityExponentAmplitude_pos hd) hbracket hsigma0 hsigma
    hb0 hb1 hE hEb hgamma

/-- **Gate 6: the entropy-versus-gain gate.** This is the gate that the printed
`b`-free admissibility cannot supply and that the additional requirement `E
>= C b^{-1}` does. -/
theorem entropyGate_of_admissible (M : ABKModel d) {E sigma b : ℝ} (hd : 2 ≤ d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    1 + 2 * (d : ℝ) / b ≤ Real.exp (-(40 / sigma)) * siteRateSq M E / 2 := by
  have hbracket : 2 * (1 + 2 * (d : ℝ)) ≤ rateBracket d := by
    have h1 : (0 : ℝ) ≤ 32 * (d : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ densityAmplitude d ^ 2 := sq_nonneg _
    have h4 := densityExponentAmplitude_pos hd
    rw [rateBracket]
    linarith
  have hx0 : (0 : ℝ) < 2 * (1 + 2 * (d : ℝ)) := by positivity
  have hgate := rate_gate_exp_div (M := M) hx0 hbracket hsigma0 hsigma hb0 hE hEb hgamma
  -- `1 + 2 d / b <= (1 + 2 d) / b`
  have hbinv : (1 : ℝ) ≤ b⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hb0]
    simpa using hb1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hX : 1 + 2 * (d : ℝ) / b ≤ (1 + 2 * (d : ℝ)) / b := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linarith only [hbinv, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd0)
      (by linarith : (0 : ℝ) ≤ b⁻¹ - 1)]
  set u : ℝ := Real.exp (40 / sigma) with hudef
  have hu : (0 : ℝ) < u := Real.exp_pos _
  have hkey : (1 + 2 * (d : ℝ)) / b * (2 * u) ≤ siteRateSq M E := by
    have hid : 2 * (1 + 2 * (d : ℝ)) * u / b = (1 + 2 * (d : ℝ)) / b * (2 * u) := by
      field_simp
    rw [← hid]
    exact hgate
  have hXle : (1 + 2 * (d : ℝ) / b) * (2 * u) ≤ siteRateSq M E := by
    have h2u : (0 : ℝ) ≤ 2 * u := by positivity
    exact le_trans (mul_le_mul_of_nonneg_right hX h2u) hkey
  have hstep : u⁻¹ * ((1 + 2 * (d : ℝ) / b) * (2 * u)) ≤ u⁻¹ * siteRateSq M E :=
    mul_le_mul_of_nonneg_left hXle (by positivity)
  have hid2 : u⁻¹ * ((1 + 2 * (d : ℝ) / b) * (2 * u)) = (1 + 2 * (d : ℝ) / b) * 2 := by
    field_simp
  rw [Real.exp_neg, ← hudef]
  rw [hid2] at hstep
  linarith

end

end Algsuperdiff.Section3.Provider.Percolation
