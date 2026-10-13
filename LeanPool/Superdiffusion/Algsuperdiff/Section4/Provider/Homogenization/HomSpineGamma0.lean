/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMomentTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneArith

/-!
# HomSpineGamma0

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 1: collapsing the `hY` gates to one `γ₀`

## The target

This file closes `hY` (`HomMomentTail.homY_moment_bound`) modulo THREE
displayed gates,

```text
  hratio: 3^{(1-α)2p} e^{-θ} ≤ 1/2,      θ = (1-α)²/(C γ),
  htrunc: 3^{(1-α)2p N₀} ≤ 2^p,
  hsmall: 2 (C e^{(1-α)²/γ}) (3^{(1-α)2p} e^{-θ})^{N₀+1} ≤ 1,
```

with `N₀` a free cut.  This module collapses them to ONE `γ`-threshold plus the
theorem's own `p`-range.  Nothing analytic is added: every step is the
elementary comparison of a logarithm with a power of `γ`.

## The choices, and why they are forced

`htrunc` wants `N₀` SMALL (`N₀ s log 3 ≤ log 2`) while `hsmall` wants `N₀`
LARGE.  The tension is resolved by the shape of the Theorem-C tail
`P{X ≥ N} ≤ C e^{-(1-α)²(N-C)/(Cγ)}`, whose turn-on is at `N ≈ C`: the cut must
be placed just past it and nowhere else.  Hence

```text
  N₀:= ⌈C⌉₊ + 2          (homGateCut),
  C₁:= 16 C (N₀+1) log 3 (homGateRangeConst) — the p-range constant,
```

and then `a:= (1-α)(2p) = s p` obeys `a (N₀+1) log 3 ≤ θ/4` EXACTLY (the
choice of `C₁` makes this an equality of the two majorants), while `N₀+1 ≥ C+3`
makes the `hsmall` exponent `Cθ - θ(N₀+1) ≤ -3θ`.  With `θ ≥ 2(log 2 +
log 2C)` the three gates follow.

## The single threshold

```text
  HomGammaGate C γ:=  γ (log γ)² ≤ κ(C)  ∧  N₀ log 3 ≤ |log γ| log 2,
      κ(C) = (8 C (log 2 + log 2C))⁻¹,
```

and `homGamma0Gate C:= min ((κ/16)², exp(-N₀ log 3 / log 2))` is an EXPLICIT
positive witness: `γ ≤ homGamma0Gate C ⟹ HomGammaGate C γ`
(`homGammaGate_of_le_homGamma0`).  The first clause uses only the
`absLog_le_four_div_quarticRoot`, i.e. `γ(log γ)² ≤ 16√γ`; the second is
monotonicity of `log`.  So the three displayed gates become the single
hypothesis `M.gamma ≤ homGamma0Gate C`.
-/

open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

/-! ## 1. The three gates as logarithmic inequalities -/

/-- `hratio` from one linear inequality between logarithms. -/
theorem gate_ratio_of_log {a theta : ℝ}
    (h : a * Real.log 3 + Real.log 2 ≤ theta) :
    (3 : ℝ) ^ a * Real.exp (-theta) ≤ 1 / 2 := by
  have h3 : (3 : ℝ) ^ a = Real.exp (Real.log 3 * a) :=
    Real.rpow_def_of_pos (by norm_num) a
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub]
  have hstep : Real.log 3 * a + -theta ≤ Real.log (1 / 2 : ℝ) := by
    rw [hlog]
    have hcomm : Real.log 3 * a = a * Real.log 3 := by ring
    rw [hcomm]
    linarith only [h]
  rw [h3, ← Real.exp_add]
  calc Real.exp (Real.log 3 * a + -theta) ≤ Real.exp (Real.log (1 / 2 : ℝ)) :=
        Real.exp_le_exp.mpr hstep
    _ = 1 / 2 := Real.exp_log (by norm_num)

/-- `htrunc` from one linear inequality between logarithms. -/
theorem gate_trunc_of_log {a p : ℝ} (h : a * Real.log 3 ≤ p * Real.log 2) :
    (3 : ℝ) ^ a ≤ (2 : ℝ) ^ p := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr (by linarith only [h])

/-- The geometric ratio to a natural power, in exponential form. -/
private theorem ratio_pow_eq {a theta : ℝ} (N : ℕ) :
    ((3 : ℝ) ^ a * Real.exp (-theta)) ^ N =
      Real.exp (Real.log 3 * a * (N : ℝ)) * Real.exp (-(theta * (N : ℝ))) := by
  rw [mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ a) N,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_nat_mul]
  congr 2
  · ring
  · ring

/-- `hsmall` from one linear inequality between logarithms. -/
theorem gate_small_of_log {Cst a theta : ℝ} {N : ℕ} (hCst : 0 < Cst)
    (h : Real.log (2 * Cst) + Cst * theta + Real.log 3 * a * (N : ℝ) -
      theta * (N : ℝ) ≤ 0) :
    2 * (Cst * Real.exp (Cst * theta) *
      ((3 : ℝ) ^ a * Real.exp (-theta)) ^ N) ≤ 1 := by
  have h2C : (0 : ℝ) < 2 * Cst := by linarith only [hCst]
  have hexp : 2 * Cst = Real.exp (Real.log (2 * Cst)) := (Real.exp_log h2C).symm
  rw [ratio_pow_eq (a := a) (theta := theta) N]
  have hcollect : 2 * (Cst * Real.exp (Cst * theta) *
      (Real.exp (Real.log 3 * a * (N : ℝ)) * Real.exp (-(theta * (N : ℝ))))) =
      (2 * Cst) * Real.exp (Cst * theta + Real.log 3 * a * (N : ℝ) +
        -(theta * (N : ℝ))) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hcollect, hexp, ← Real.exp_add]
  calc Real.exp (Real.log (2 * Cst) +
        (Cst * theta + Real.log 3 * a * (N : ℝ) + -(theta * (N : ℝ))))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith only [h])
    _ = 1 := Real.exp_zero

/-! ## 2. The cut, the range constant, and the threshold -/

/-- **The cut** `N₀:= ⌈C⌉₊ + 2`, placed just past the Theorem-C tail's
turn-on `N ≈ C`.  Any smaller cut breaks `hsmall`, any larger one breaks
`htrunc`. -/
def homGateCut (Cst : ℝ) : ℕ := ⌈Cst⌉₊ + 2

theorem homGateCut_ge (Cst : ℝ) : Cst + 2 ≤ (homGateCut Cst : ℝ) := by
  have h := Nat.le_ceil Cst
  rw [homGateCut]
  push_cast
  linarith only [h]

theorem one_le_homGateCut (Cst : ℝ) : (1 : ℝ) ≤ (homGateCut Cst : ℝ) := by
  rw [homGateCut]
  push_cast
  have h : (0 : ℝ) ≤ (⌈Cst⌉₊ : ℝ) := Nat.cast_nonneg _
  linarith only [h]

/-- **The `p`-range constant** `C₁:= 16 C (N₀+1) log 3`. -/
def homGateRangeConst (Cst : ℝ) : ℝ :=
  16 * Cst * ((homGateCut Cst : ℝ) + 1) * Real.log 3

theorem homGateRangeConst_pos {Cst : ℝ} (hCst : 1 ≤ Cst) :
    0 < homGateRangeConst Cst := by
  have hN : (1 : ℝ) ≤ (homGateCut Cst : ℝ) := one_le_homGateCut Cst
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : (0 : ℝ) < 16 * Cst := by linarith only [hCst]
  have h2 : (0 : ℝ) < (homGateCut Cst : ℝ) + 1 := by linarith only [hN]
  rw [homGateRangeConst]
  exact mul_pos (mul_pos h1 h2) hlog

/-- `κ(C) = (8 C (log 2 + log 2C))⁻¹`, the `γ(log γ)²` budget. -/
def homGateKappa (Cst : ℝ) : ℝ := (8 * Cst * (Real.log 2 + Real.log (2 * Cst)))⁻¹

private theorem log_two_add_log_two_mul_pos {Cst : ℝ} (hCst : 1 ≤ Cst) :
    0 < Real.log 2 + Real.log (2 * Cst) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2C : 0 ≤ Real.log (2 * Cst) := Real.log_nonneg (by linarith only [hCst])
  linarith only [h2, h2C]

theorem homGateKappa_pos {Cst : ℝ} (hCst : 1 ≤ Cst) : 0 < homGateKappa Cst := by
  have hlog := log_two_add_log_two_mul_pos hCst
  have h8 : (0 : ℝ) < 8 * Cst := by linarith only [hCst]
  rw [homGateKappa]
  exact inv_pos.mpr (mul_pos h8 hlog)

/-- **THE SINGLE `γ`-THRESHOLD PREDICATE.**  Both clauses are pure smallness of
`γ`; together with the theorem's own `p`-range they imply all three displayed
gates (`homGates_of_gammaGate`). -/
def HomGammaGate (Cst gamma : ℝ) : Prop :=
  gamma * Real.log gamma ^ (2 : ℕ) ≤ homGateKappa Cst ∧
    (homGateCut Cst : ℝ) * Real.log 3 ≤ |Real.log gamma| * Real.log 2

/-- **The explicit threshold** `γ₀(C)`. -/
def homGamma0Gate (Cst : ℝ) : ℝ :=
  min ((homGateKappa Cst / 16) ^ (2 : ℕ))
    (Real.exp (-((homGateCut Cst : ℝ) * Real.log 3 / Real.log 2)))

theorem homGamma0Gate_pos {Cst : ℝ} (hCst : 1 ≤ Cst) : 0 < homGamma0Gate Cst := by
  have hk := homGateKappa_pos hCst
  have h1 : (0 : ℝ) < (homGateKappa Cst / 16) ^ (2 : ℕ) := by
    have : (0 : ℝ) < homGateKappa Cst / 16 := by linarith only [hk]
    exact pow_pos this 2
  exact lt_min h1 (Real.exp_pos _)

/-- `γ (log γ)² ≤ 16 √γ` for `0 < γ < 1` — the quartic-root comparison, the
only place a logarithm meets a power of `γ`. -/
theorem gamma_mul_sq_log_le {gamma : ℝ} (hg : 0 < gamma) (hg1 : gamma < 1) :
    gamma * Real.log gamma ^ (2 : ℕ) ≤ 16 * Real.sqrt gamma := by
  have ht : 0 < Real.sqrt (Real.sqrt gamma) := quarticRoot_pos hg
  have hbound : |Real.log gamma| ≤ 4 * (Real.sqrt (Real.sqrt gamma))⁻¹ :=
    absLog_le_four_div_quarticRoot hg hg1
  have habs : Real.log gamma ^ (2 : ℕ) = |Real.log gamma| ^ (2 : ℕ) := (sq_abs _).symm
  have hsq : |Real.log gamma| ^ (2 : ℕ) ≤
      (4 * (Real.sqrt (Real.sqrt gamma))⁻¹) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have htsq : Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) = Real.sqrt gamma :=
    quarticRoot_sq gamma
  have hsqrt_pos : 0 < Real.sqrt gamma := Real.sqrt_pos.mpr hg
  have hval : (4 * (Real.sqrt (Real.sqrt gamma))⁻¹) ^ (2 : ℕ) = 16 * (Real.sqrt gamma)⁻¹ := by
    rw [mul_pow, inv_pow, htsq]
    norm_num
  have hcancel : gamma * (Real.sqrt gamma)⁻¹ = Real.sqrt gamma := by
    rw [inv_eq_one_div, mul_one_div, eq_comm, eq_div_iff (ne_of_gt hsqrt_pos),
      Real.mul_self_sqrt (le_of_lt hg)]
  calc gamma * Real.log gamma ^ (2 : ℕ)
      = gamma * |Real.log gamma| ^ (2 : ℕ) := by rw [habs]
    _ ≤ gamma * (16 * (Real.sqrt gamma)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hg)
        rw [← hval]
        exact hsq
    _ = 16 * Real.sqrt gamma := by
        rw [show gamma * (16 * (Real.sqrt gamma)⁻¹) =
            16 * (gamma * (Real.sqrt gamma)⁻¹) by ring, hcancel]

/-- **`γ ≤ γ₀(C)` implies the single gate.** -/
theorem homGammaGate_of_le_homGamma0 {Cst gamma : ℝ} (hCst : 1 ≤ Cst)
    (hg : 0 < gamma) (hle : gamma ≤ homGamma0Gate Cst) : HomGammaGate Cst gamma := by
  have hk : 0 < homGateKappa Cst := homGateKappa_pos hCst
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hN : (1 : ℝ) ≤ (homGateCut Cst : ℝ) := one_le_homGateCut Cst
  have hle1 : gamma ≤ (homGateKappa Cst / 16) ^ (2 : ℕ) := le_trans hle (min_le_left _ _)
  have hle2 : gamma ≤ Real.exp (-((homGateCut Cst : ℝ) * Real.log 3 / Real.log 2)) :=
    le_trans hle (min_le_right _ _)
  have hkq : 0 < homGateKappa Cst / 16 := by linarith only [hk]
  /- the second clau -/
  have hexp : Real.log gamma ≤ -((homGateCut Cst : ℝ) * Real.log 3 / Real.log 2) := by
    have := Real.log_le_log hg hle2
    rwa [Real.log_exp] at this
  have hgamma_lt : gamma < 1 := by
    have hneg : -((homGateCut Cst : ℝ) * Real.log 3 / Real.log 2) < 0 := by
      have hnum : 0 < (homGateCut Cst : ℝ) * Real.log 3 := by
        have h0 : (0 : ℝ) < (homGateCut Cst : ℝ) := by linarith only [hN]
        exact mul_pos h0 hlog3
      have : 0 < (homGateCut Cst : ℝ) * Real.log 3 / Real.log 2 := div_pos hnum hlog2
      linarith only [this]
    have hlt : Real.log gamma < 0 := lt_of_le_of_lt hexp hneg
    by_contra hcon
    push Not at hcon
    exact absurd (Real.log_nonneg hcon) (not_le.mpr hlt)
  have habs : |Real.log gamma| = -Real.log gamma :=
    abs_of_neg (Real.log_neg hg hgamma_lt)
  have hclause2 : (homGateCut Cst : ℝ) * Real.log 3 ≤ |Real.log gamma| * Real.log 2 := by
    rw [habs]
    have hstep : (homGateCut Cst : ℝ) * Real.log 3 / Real.log 2 ≤ -Real.log gamma := by
      linarith only [hexp]
    have := mul_le_mul_of_nonneg_right hstep (le_of_lt hlog2)
    rwa [div_mul_cancel₀ _ (ne_of_gt hlog2)] at this
  /- the first clau -/
  have hsq : Real.sqrt gamma ≤ homGateKappa Cst / 16 := by
    have hpow : Real.sqrt gamma ^ (2 : ℕ) ≤ (homGateKappa Cst / 16) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt (le_of_lt hg)]
      exact hle1
    exact le_of_pow_le_pow_left₀ (by norm_num) (le_of_lt hkq) hpow
  have hclause1 : gamma * Real.log gamma ^ (2 : ℕ) ≤ homGateKappa Cst := by
    refine (gamma_mul_sq_log_le hg hgamma_lt).trans ?_
    have := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 16)
    calc 16 * Real.sqrt gamma ≤ 16 * (homGateKappa Cst / 16) := this
      _ = homGateKappa Cst := by ring
  exact ⟨hclause1, hclause2⟩


/-! ## 3. The three gates at the §4.5 parameter web -/

/-- **THE COLLAPSE.**  At the §4.5 web `1 - α = s/2`, `s = |log γ|⁻¹`, the
single threshold `HomGammaGate C γ` together with the theorem's own `p`-range
`p ≤ C₁⁻¹ γ⁻¹ |log γ|⁻¹` implies all THREE displayed gates of
`homY_moment_bound`, at the cut `N₀ = homGateCut C`. -/
theorem homGates_of_gammaGate {d : ℕ} (M : ABKModel d) {Cst p : ℝ}
    (hCst : 1 ≤ Cst) (hp : 1 ≤ p) (hL : 4 ≤ |Real.log M.gamma|)
    (hgate : HomGammaGate Cst M.gamma)
    (hrange : p ≤ (homGateRangeConst Cst)⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹) :
    ((3 : ℝ) ^ ((1 - homAlpha M) * (2 * p)) *
          Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) / (Cst * M.gamma))) ≤ 1 / 2) ∧
      ((3 : ℝ) ^ ((1 - homAlpha M) * (2 * p) * ((homGateCut Cst : ℕ) : ℝ)) ≤
          (2 : ℝ) ^ p) ∧
      (2 * ((Cst * Real.exp ((1 - homAlpha M) ^ (2 : ℕ) / M.gamma)) *
          ((3 : ℝ) ^ ((1 - homAlpha M) * (2 * p)) *
            Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) / (Cst * M.gamma)))) ^
            (homGateCut Cst + 1)) ≤ 1) := by
  obtain ⟨hk1, hk2⟩ := hgate
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL]
  have hCpos : (0 : ℝ) < Cst := by linarith only [hCst]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hNge : Cst + 2 ≤ (homGateCut Cst : ℝ) := homGateCut_ge Cst
  have hN1 : (1 : ℝ) ≤ (homGateCut Cst : ℝ) := one_le_homGateCut Cst
  have hC1pos : 0 < homGateRangeConst Cst := homGateRangeConst_pos hCst
  set L : ℝ := |Real.log M.gamma| with hLdef
  set c : ℝ := 1 - homAlpha M with hcdef
  have hc : c = L⁻¹ / 2 := by
    rw [hcdef, one_sub_homAlpha, homS, hLdef]
  set W : ℝ := M.gamma⁻¹ * L⁻¹ * L⁻¹ with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]
    exact mul_pos (mul_pos (inv_pos.mpr hgpos) (inv_pos.mpr hLpos)) (inv_pos.mpr hLpos)
  /- theta and a in terms of -/
  have htheta : c ^ (2 : ℕ) / (Cst * M.gamma) = W / (4 * Cst) := by
    rw [hc, hWdef]
    field_simp
    ring
  have ha : c * (2 * p) = p * L⁻¹ := by
    rw [hc]
    field_simp
  set theta : ℝ := W / (4 * Cst) with hthdef
  have hthpos : 0 < theta := by
    rw [hthdef]
    exact div_pos hWpos (by linarith only [hCpos])
  have hapos : 0 ≤ p * L⁻¹ :=
    mul_nonneg (by linarith only [hp]) (le_of_lt (inv_pos.mpr hLpos))
  /- the p-range in the W gau -/
  have haW : p * L⁻¹ ≤ W / homGateRangeConst Cst := by
    have hstep := mul_le_mul_of_nonneg_right hrange (le_of_lt (inv_pos.mpr hLpos))
    refine hstep.trans (le_of_eq ?_)
    rw [hWdef]
    field_simp
  /- the key majorant: a (N+1) log 3 <= theta / -/
  have hkey : (p * L⁻¹) * ((homGateCut Cst : ℝ) + 1) * Real.log 3 ≤ theta / 4 := by
    have hposfac : (0 : ℝ) ≤ ((homGateCut Cst : ℝ) + 1) * Real.log 3 :=
      mul_nonneg (by linarith only [hN1]) (le_of_lt hlog3)
    have hstep := mul_le_mul_of_nonneg_right haW hposfac
    refine (le_of_eq (by ring)).trans (hstep.trans (le_of_eq ?_))
    rw [hthdef, homGateRangeConst]
    field_simp
    ring
  have halog : (p * L⁻¹) * Real.log 3 ≤ theta / 4 := by
    have hmono : (p * L⁻¹) * Real.log 3 ≤ (p * L⁻¹) * ((homGateCut Cst : ℝ) + 1) *
        Real.log 3 := by
      have hfac : (p * L⁻¹) * 1 ≤ (p * L⁻¹) * ((homGateCut Cst : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only [hN1]) hapos
      have := mul_le_mul_of_nonneg_right hfac (le_of_lt hlog3)
      linarith only [this]
    linarith only [hmono, hkey]
  /- the threshold clause, in the theta gau -/
  have hWlow : 8 * Cst * (Real.log 2 + Real.log (2 * Cst)) ≤ W := by
    have hsq : Real.log M.gamma ^ (2 : ℕ) = L * L := by
      rw [hLdef, ← sq_abs]
      ring
    have hprod : M.gamma * (L * L) ≤ homGateKappa Cst := by
      rw [← hsq]
      exact hk1
    have hppos : 0 < M.gamma * (L * L) := mul_pos hgpos (mul_pos hLpos hLpos)
    have hWinv : W = (M.gamma * (L * L))⁻¹ := by
      rw [hWdef]
      field_simp
    have hkinv : (homGateKappa Cst)⁻¹ ≤ (M.gamma * (L * L))⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hppos hprod
    have hkval : (homGateKappa Cst)⁻¹ = 8 * Cst * (Real.log 2 + Real.log (2 * Cst)) := by
      rw [homGateKappa, inv_inv]
    rw [hWinv, ← hkval]
    exact hkinv
  have hth2 : 2 * (Real.log 2 + Real.log (2 * Cst)) ≤ theta := by
    rw [hthdef]
    rw [le_div_iff₀ (by linarith only [hCpos] : (0 : ℝ) < 4 * Cst)]
    linarith only [hWlow]
  have hlog2C : 0 ≤ Real.log (2 * Cst) := Real.log_nonneg (by linarith only [hCst])
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, htheta]
    refine gate_ratio_of_log ?_
    linarith only [halog, hth2, hlog2, hlog2C]
  · rw [ha]
    refine gate_trunc_of_log ?_
    have hstep : (homGateCut Cst : ℝ) * Real.log 3 ≤ L * Real.log 2 := hk2
    have hmul := mul_le_mul_of_nonneg_left hstep hapos
    have hLinv : (p * L⁻¹) * (L * Real.log 2) = p * Real.log 2 := by
      field_simp
    calc p * L⁻¹ * (homGateCut Cst : ℝ) * Real.log 3
        = (p * L⁻¹) * ((homGateCut Cst : ℝ) * Real.log 3) := by ring
      _ ≤ (p * L⁻¹) * (L * Real.log 2) := hmul
      _ = p * Real.log 2 := hLinv
  · have hCth : Cst * theta = c ^ (2 : ℕ) / M.gamma := by
      rw [hthdef, hWdef, hc]
      field_simp
      ring
    rw [ha, htheta, ← hCth]
    refine gate_small_of_log hCpos ?_
    have hNcast : ((homGateCut Cst + 1 : ℕ) : ℝ) = (homGateCut Cst : ℝ) + 1 := by
      push_cast
      ring
    rw [hNcast]
    have hlog3a : Real.log 3 * (p * L⁻¹) * ((homGateCut Cst : ℝ) + 1) ≤ theta / 4 := by
      calc Real.log 3 * (p * L⁻¹) * ((homGateCut Cst : ℝ) + 1)
          = (p * L⁻¹) * ((homGateCut Cst : ℝ) + 1) * Real.log 3 := by ring
        _ ≤ theta / 4 := hkey
    have hbig : theta * ((homGateCut Cst : ℝ) + 1) ≥ theta * (Cst + 3) := by
      refine mul_le_mul_of_nonneg_left (by linarith only [hNge]) (le_of_lt hthpos)
    linarith only [hlog3a, hbig, hth2, hlog2, hthpos]

/-! ## 4. `hY` under the single threshold -/

/-- **`hY`, with the three displayed gates replaced by ONE `γ`-threshold.**

`homY_moment_bound` with `hratio`, `htrunc`, `hsmall` discharged from
`M.gamma ≤ homGamma0Gate Cst` and the theorem's own `p`-range.  `Cst` is the
`C(d,c⋆)` of Theorem C, so `homGamma0Gate Cst` is a `γ₀(d,c⋆)`. -/
theorem homY_moment_bound_of_gamma_le {d : ℕ} (M : ABKModel d)
    {X : Cutoff.CutoffSample d → ℕ∞} (hX : Measurable X) {Cst p : ℝ}
    (hCst : 1 ≤ Cst) (hp : 1 ≤ p) (hL : 4 ≤ |Real.log M.gamma|)
    (hgamma : M.gamma ≤ homGamma0Gate Cst)
    (hrange : p ≤ (homGateRangeConst Cst)⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹)
    (htail : ∀ N : ℕ, (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
      ENNReal.ofReal (Cst *
        Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) / (Cst * M.gamma)))) :
    (∫⁻ omega, homMinimalScaleFactor (1 - homAlpha M) X omega ^ (2 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal 2 ^ (2 * p) := by
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  obtain ⟨h1, h2, h3⟩ := homGates_of_gammaGate M hCst hp hL
    (homGammaGate_of_le_homGamma0 hCst hgpos hgamma) hrange
  have halpha : homAlpha M ≤ 1 := by
    have hs : 0 < homS M := homS_pos (by linarith only [hL])
    rw [homAlpha]
    linarith only [hs]
  exact homY_moment_bound M hX (N0 := homGateCut Cst)
    (lt_of_lt_of_le zero_lt_one hCst) halpha hp htail h1 h2 h3

end

end Algsuperdiff.Section4.Provider.Homogenization
