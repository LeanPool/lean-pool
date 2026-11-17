/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Bridge.Poly
public import LeanPool.AaronsonAmbainis.Bridge.Affine

/-!
# The main theorem and the conjecture as printed

Source.

S. Aaronson and A. Ambainis, *The need for structure in quantum speedups*, arXiv:0911.0996,
Conjecture 6 (Conjecture 1.7 of the journal version, Theory of Computing 10 (2014), 133–166):

  Let `p : R^N → R` be a polynomial of degree `d`. Suppose that `0 ≤ p(X) ≤ 1` for all
  `X ∈ {0,1}^N`, and `E_X[(p(X) − E[p])²] ≥ ε`. Then there exists an `i` such that
  `Inf_i[p] ≥ (ε/d)^{O(1)}`,   where   `Inf_i[p] := E_X[(p(X) − p(X^i))²]`.

The conjecture, and its form on the cube `{1,-1}^n` (`problem_statement.md`), are transcribed
without the definitions of `Defs.lean`: `Ex`, `flipBit`, `ev01`, `evPM` spell out the expectation,
the bit flip and the evaluation of a polynomial on the two cubes. `evPM` sends `true` to `-1`, as
`Defs.lean` does; the statement `ExplicitBoundPM` of `Conjecture.lean` sends `true` to `1`
(`evPMt`, in the last section).

`MainBound C` is a bound of the kind of the main theorem with a constant `C`:
`3 Var(f)^5 ≤ C d^12 Inf_j(f)²`. So `MainTheorem` is `MainBound (50000 π^8)` and
`MainTheoremImproved` is `MainBound (3125 π^8)`. Every such bound is carried over to
polynomials:

* `pm_of_mainBound` — on the cube `{1,-1}^n`, for `|p| ≤ 1`: `3 ε^5 ≤ C d^12 Inf_i(p)²`;
* `zo_of_mainBound` — on the cube `{0,1}^N`, for `0 ≤ p ≤ 1` (the bound is applied to
  `1 − 2p`, whose variance is `4 Var[p]`): `3072 ε^5 ≤ C d^12 Inf_i[p]²`.

The bounds are then put in the form in which the paper prints them, with the power `5/2`
written as `ε² √ε` (`sqrt_form_iff`). From `MainTheorem`:

* `pm_sq_of_mainTheorem`, `pm_sqrt_of_mainTheorem` — `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²`, that is,
  `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6`;
* `zo_sq_of_mainTheorem`, `zo_sqrt_of_mainTheorem` — `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, that
  is, `Inf_i[p] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`;
* `zo_pow_of_mainTheorem` — `Inf_i[p] ≥ (ε/d)^7`, the conjecture as printed (`ratio_pow_le`).

From `MainTheoremImproved`:

* `zo_sq_of_mainTheoremImproved`, `zo_sqrt_of_mainTheoremImproved` —
  `3072 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, that is, `Inf_i[p] ≥ (32 √15 / (125 π^4)) ε^{5/2} / d^6`.

In these theorems `MainTheorem` and `MainTheoremImproved` are hypotheses; `Chain.lean` proves the
first with no hypothesis and the second from the hypothesis `RowBound`.

The last section treats the real power `ε^{5/2}` and the bit encoding of `ExplicitBoundPM`, as
`Conjecture.lean` writes the power and the encoding: `ε ^ ((5 : ℝ) / 2)` equals `ε² √ε`
(`rpow_five_halves`), and `pmt_sq_of_mainTheorem`, `pmt_sqrt_of_mainTheorem` are the bounds on
the cube `{-1,1}^n` with `true ↦ 1` and `false ↦ -1` (`evPMt`), obtained from
`pm_sq_of_mainTheorem` and `pm_sqrt_of_mainTheorem` by negating every bit.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

/-- Uniform expectation over `{0,1}^N`, spelled out. -/
noncomputable def Ex {N : ℕ} (F : (Fin N → Bool) → ℝ) : ℝ := (∑ X, F X) / 2 ^ N

/-- `X` with the `i`-th bit flipped, spelled out (`X^i` in the sources). -/
def flipBit {N : ℕ} (X : Fin N → Bool) (i : Fin N) : Fin N → Bool := Function.update X i (!X i)

/-- The value of the polynomial `p` at the `0/1` point `X ∈ {0,1}^N`. -/
noncomputable def ev01 {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p

/-- The value of the polynomial `p` at the `±1` point attached to `X` (`true ↦ −1`). -/
noncomputable def evPM {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (-1 : ℝ) else 1) p

/-! ### `mean`, `variance`, `inflR`, `flipSet` of `Defs.lean` are the spelled-out notions -/

theorem mean_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) : mean F = Ex F := by
  unfold mean Ex
  rw [Fintype.card_fin]

theorem flipSet_singleton_eq_flipBit {N : ℕ} (X : Cube (Fin N)) (i : Fin N) :
    flipSet X {i} = flipBit X i := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [flipSet_singleton_self]
    simp [flipBit]
  · rw [flipSet_singleton_ne X hk]
    simp [flipBit, Function.update_of_ne hk]

theorem variance_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) :
    variance F = Ex (fun X => (F X - Ex F) ^ 2) := by
  have h : variance F = (∑ x, (F x - mean F) ^ 2) / 2 ^ Fintype.card (Fin N) := rfl
  rw [h, mean_eq_Ex, Fintype.card_fin]
  rfl

theorem inflR_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) (i : Fin N) :
    inflR F i = Ex (fun X => ((F X - F (flipBit X i)) / 2) ^ 2) := by
  have h : inflR F i
      = (∑ x, ((F x - F (flipSet x {i})) / 2) ^ 2) / 2 ^ Fintype.card (Fin N) := rfl
  rw [h, Fintype.card_fin]
  simp only [flipSet_singleton_eq_flipBit]
  rfl

theorem Ex_nonneg {N : ℕ} {F : (Fin N → Bool) → ℝ} (hF : ∀ X, 0 ≤ F X) : 0 ≤ Ex F :=
  div_nonneg (Finset.sum_nonneg fun X _ => hF X) (by positivity)

/-! ### Bounds of the kind of the main theorem, for polynomials -/

/-- A bound of the kind of the main theorem, with the constant `C`: every `f` on the cube with
`|f| ≤ 1`, degree at most `d` and positive variance has a coordinate `j` with
`3 Var(f)^5 ≤ C d^12 Inf_j(f)²`. `MainTheorem` is `MainBound (50000 * π^8)`, and
`MainTheoremImproved` is `MainBound (3125 * π^8)`. -/
def MainBound (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ C * (d : ℝ) ^ 12 * inflR f j ^ 2

theorem mainBound_of_mainTheorem (h : MainTheorem) : MainBound (50000 * Real.pi ^ 8) := h

theorem mainBound_of_mainTheoremImproved (h : MainTheoremImproved) :
    MainBound (3125 * Real.pi ^ 8) := h

/-- A bound of the kind of the main theorem, translated to `[0,1]`-valued functions `P` (apply it
to `1 − 2P`), with the unnormalised L2 influence `E[(P(X) − P(X^i))²]` of Aaronson–Ambainis on
the right: `3072 Var[P]^5 ≤ C d^12 Inf_i[P]²`. -/
theorem zero_one_of_mainBound {C : ℝ} (h : MainBound C) {ι : Type} [Fintype ι]
    [DecidableEq ι] (d : ℕ) (P : Cube ι → ℝ) (hrange : ∀ X, 0 ≤ P X ∧ P X ≤ 1)
    (hdeg : HasDegreeLE P d) (hpos : 0 < variance P) :
    ∃ i, 3072 * variance P ^ 5 ≤ C * (d : ℝ) ^ 12
      * ((∑ X : Cube ι, (P X - P (flipSet X {i})) ^ 2) / 2 ^ Fintype.card ι) ^ 2 := by
  have hdeg' : HasDegreeLE (fun X => 1 + (-2) * P X) d :=
    hasDegreeLE_add (hasDegreeLE_const 1 d) (hasDegreeLE_smul (-2) hdeg)
  have hbd : ∀ X, |1 + (-2) * P X| ≤ 1 := by
    intro X
    obtain ⟨h0, h1⟩ := hrange X
    rw [abs_le]
    constructor <;> linarith
  have hV : variance (fun X => 1 + (-2) * P X) = 4 * variance P := by
    rw [variance_affine]
    norm_num
  have hVpos : 0 < variance (fun X => 1 + (-2) * P X) := by
    rw [hV]
    linarith
  obtain ⟨i, hi⟩ := h ι d (fun X => 1 + (-2) * P X) hbd hdeg' hVpos
  refine ⟨i, ?_⟩
  have hI : inflR (fun X => 1 + (-2) * P X) i
      = (∑ X : Cube ι, (P X - P (flipSet X {i})) ^ 2) / 2 ^ Fintype.card ι := by
    rw [inflR_affine, Level.inflR_eq_quarter]
    ring
  rw [hV, hI] at hi
  have e : 3 * (4 * variance P) ^ 5 = 3072 * variance P ^ 5 := by ring
  rw [e] at hi
  exact hi

/-- A bound of the kind of the main theorem for polynomials on the cube `{0,1}^N` with values in
`[0,1]`: `3072 ε^5 ≤ C d^12 Inf_i[p]²`. -/
theorem zo_of_mainBound {C : ℝ} (h : MainBound C) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ C * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 := by
  have hdeg : HasDegreeLE (ev01 p) d := hasDegreeLE_eval_zo p hp
  have hvar' : ε ≤ variance (ev01 p) := by
    rw [variance_eq_Ex]
    exact hvar
  obtain ⟨i, hi⟩ := zero_one_of_mainBound h d (ev01 p) hrange hdeg (lt_of_lt_of_le hε hvar')
  refine ⟨i, ?_⟩
  have hI : (∑ X : Cube (Fin N), (ev01 p X - ev01 p (flipSet X {i})) ^ 2)
        / 2 ^ Fintype.card (Fin N)
      = Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) := by
    rw [Fintype.card_fin]
    simp only [flipSet_singleton_eq_flipBit]
    rfl
  rw [hI] at hi
  have h5 : ε ^ 5 ≤ variance (ev01 p) ^ 5 := pow_le_pow_left₀ hε.le hvar' 5
  linarith

/-- A bound of the kind of the main theorem for polynomials on the cube `{1,-1}^n` which are
bounded by `1`: `3 ε^5 ≤ C d^12 Inf_i(p)²`. -/
theorem pm_of_mainBound {C : ℝ} (h : MainBound C) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ C * (d : ℝ) ^ 12
      * Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) ^ 2 := by
  have hdeg : HasDegreeLE (evPM p) d := hasDegreeLE_eval_pm p hp
  have hvar' : ε ≤ variance (evPM p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hpos : 0 < variance (evPM p) := lt_of_lt_of_le hε hvar'
  obtain ⟨i, hi⟩ := h (Fin n) d (evPM p) hbd hdeg hpos
  refine ⟨i, ?_⟩
  rw [← inflR_eq_Ex (evPM p) i]
  have h5 : ε ^ 5 ≤ variance (evPM p) ^ 5 := pow_le_pow_left₀ hε.le hvar' 5
  linarith

/-- Under the hypotheses of the statements on the cube `{0,1}^N`: `d ≥ 1` and `ε ≤ 1/4`. -/
theorem zo_hyps_force (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    (1 : ℝ) ≤ (d : ℝ) ∧ ε ≤ 1 / 4 := by
  have hdeg : HasDegreeLE (ev01 p) d := hasDegreeLE_eval_zo p hp
  have hvar' : ε ≤ variance (ev01 p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hd : 1 ≤ d := (aa_hyps_force hdeg (lt_of_lt_of_le hε hvar')).1
  exact ⟨by exact_mod_cast hd, hvar'.trans (variance_le_quarter hrange)⟩

/-- Under the hypotheses of the statement on the cube `{1,-1}^n`, in the encoding of `evPM`:
`d ≥ 1`. -/
theorem pm_hyps_force (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    (1 : ℝ) ≤ (d : ℝ) := by
  have hdeg : HasDegreeLE (evPM p) d := hasDegreeLE_eval_pm p hp
  have hvar' : ε ≤ variance (evPM p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hd : 1 ≤ d := (aa_hyps_force hdeg (lt_of_lt_of_le hε hvar')).1
  exact_mod_cast hd

/-! ### The arithmetic of the printed forms -/

/-- A bound without square roots and its printed form: if `ε, I, c₁ ≥ 0`, `D, c₂, m > 0` and
`15 c₁² m = k c₂²`, then `I ≥ (c₁ √15 / (c₂ π^4)) ε^{5/2} / D^6` if and only if
`k ε^5 ≤ m π^8 D^12 I²`. The power `ε^{5/2}` is written `ε² √ε`. -/
theorem sqrt_form_iff {c₁ c₂ k m ε D I : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂) (hm : 0 < m)
    (hkm : 15 * c₁ ^ 2 * m = k * c₂ ^ 2) (hε : 0 ≤ ε) (hD : 0 < D) (hI : 0 ≤ I) :
    c₁ * Real.sqrt 15 / (c₂ * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / D ^ 6 ≤ I
      ↔ k * ε ^ 5 ≤ m * Real.pi ^ 8 * D ^ 12 * I ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < c₂ * Real.pi ^ 4 * D ^ 6 := by positivity
  have hL : 0 ≤ c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε) := by positivity
  have e : c₁ * Real.sqrt 15 / (c₂ * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / D ^ 6
      = c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε) / (c₂ * Real.pi ^ 4 * D ^ 6) := by
    field_simp
  have e1 : (c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε)) ^ 2 = 15 * c₁ ^ 2 * ε ^ 5 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sq_sqrt hε]
    ring
  have e2 : (I * (c₂ * Real.pi ^ 4 * D ^ 6)) ^ 2
      = c₂ ^ 2 * (Real.pi ^ 8 * D ^ 12 * I ^ 2) := by ring
  have e3 : m * (15 * c₁ ^ 2 * ε ^ 5) = c₂ ^ 2 * (k * ε ^ 5) := by
    linear_combination ε ^ 5 * hkm
  have e4 : m * (c₂ ^ 2 * (Real.pi ^ 8 * D ^ 12 * I ^ 2))
      = c₂ ^ 2 * (m * Real.pi ^ 8 * D ^ 12 * I ^ 2) := by ring
  rw [e, div_le_iff₀ hden]
  constructor
  · intro h
    have h2 := pow_le_pow_left₀ hL h 2
    rw [e1, e2] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hm.le
    rw [e3, e4] at h3
    exact le_of_mul_le_mul_left h3 (pow_pos hc₂ 2)
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hI hden.le)
    rw [e1, e2]
    have h3 := mul_le_mul_of_nonneg_left h (sq_nonneg c₂)
    rw [← e3, ← e4] at h3
    exact le_of_mul_le_mul_left h3 hm

/-- If `192 ε^5 ≤ 3125 π^8 D^12 I²` with `0 < ε ≤ 1/4`, `D ≥ 1` and `I ≥ 0`, then
`(ε/D)^7 ≤ I`: indeed `3125 π^8 ε^9 ≤ 192` for `ε ≤ 1/4`, and `D^12 ≤ D^14`. -/
theorem ratio_pow_le {ε D I : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hD : 1 ≤ D) (hI : 0 ≤ I)
    (h : 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * D ^ 12 * I ^ 2) : (ε / D) ^ 7 ≤ I := by
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD
  apply le_of_pow_le_pow_left₀ two_ne_zero hI
  have h1 : ε ^ 9 ≤ (1 / 4) ^ 9 := pow_le_pow_left₀ hε.le hε4 9
  have hpi : Real.pi ^ 8 ≤ (3.15 : ℝ) ^ 8 :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 8
  have hB : 3125 * Real.pi ^ 8 * ε ^ 9 ≤ 192 := by
    have h4 : 3125 * Real.pi ^ 8 * ε ^ 9 ≤ 3125 * (3.15 : ℝ) ^ 8 * (1 / 4) ^ 9 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpi (by norm_num)) h1 (by positivity)
        (by positivity)
    have h5 : 3125 * (3.15 : ℝ) ^ 8 * (1 / 4) ^ 9 ≤ 192 := by norm_num
    linarith
  have hD12 : D ^ 12 ≤ D ^ 14 := pow_le_pow_right₀ hD (by norm_num)
  have hc : 0 < 3125 * Real.pi ^ 8 := by positivity
  have h6 : (3125 * Real.pi ^ 8) * ε ^ 14 ≤ (3125 * Real.pi ^ 8) * (D ^ 14 * I ^ 2) := by
    calc (3125 * Real.pi ^ 8) * ε ^ 14 = (3125 * Real.pi ^ 8 * ε ^ 9) * ε ^ 5 := by ring
      _ ≤ 192 * ε ^ 5 := mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ 3125 * Real.pi ^ 8 * D ^ 12 * I ^ 2 := h
      _ ≤ 3125 * Real.pi ^ 8 * D ^ 14 * I ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD12 hc.le) (sq_nonneg I)
      _ = (3125 * Real.pi ^ 8) * (D ^ 14 * I ^ 2) := by ring
  have h7 : ε ^ 14 ≤ D ^ 14 * I ^ 2 := le_of_mul_le_mul_left h6 hc
  have e : ((ε / D) ^ 7) ^ 2 = ε ^ 14 / D ^ 14 := by
    rw [← pow_mul, div_pow]
  rw [e, div_le_iff₀ (pow_pos hD0 14)]
  linarith

/-! ### The form on the cube `{1,-1}^n`, from `MainTheorem` -/

/-- `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²`, from `MainTheorem`. -/
theorem pm_sq_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) ^ 2 :=
  pm_of_mainBound (mainBound_of_mainTheorem h) n d p hp hbd ε hε hvar

/-- `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6`, from `MainTheorem`. -/
theorem pm_sqrt_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := pm_sq_of_mainTheorem h n d p hp hbd ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le one_pos (pm_hyps_force n d p hp ε hε hvar)
  have h1 := (sqrt_form_iff (c₁ := 1) (c₂ := 500) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε.le hD (Ex_nonneg fun X => sq_nonneg _)).mpr hi
  rw [one_mul] at h1
  exact ⟨i, h1⟩

/-! ### The conjecture, from `MainTheorem` -/

/-- `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, from `MainTheorem`. -/
theorem zo_sq_of_mainTheorem (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 := by
  obtain ⟨i, hi⟩ := zo_of_mainBound (mainBound_of_mainTheorem h) N d p hp hrange ε hε hvar
  exact ⟨i, by linarith⟩

/-- `Inf_i[p] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`, from `MainTheorem`. -/
theorem zo_sqrt_of_mainTheorem (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2)
      ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheorem h N d p hp hrange ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) :=
    lt_of_lt_of_le one_pos (zo_hyps_force N d p hp hrange ε hε hvar).1
  exact ⟨i, (sqrt_form_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε.le hD
    (Ex_nonneg fun X => sq_nonneg _)).mpr hi⟩

/-- `Inf_i[p] ≥ (ε/d)^7`, from `MainTheorem`. -/
theorem zo_pow_of_mainTheorem (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ≥ (ε / (d : ℝ)) ^ 7 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheorem h N d p hp hrange ε hε hvar
  obtain ⟨hD, hε4⟩ := zo_hyps_force N d p hp hrange ε hε hvar
  exact ⟨i, ratio_pow_le hε hε4 hD (Ex_nonneg fun X => sq_nonneg _) hi⟩

/-! ### The conjecture with the constant of `MainTheoremImproved` -/

/-- `3072 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, from `MainTheoremImproved`. -/
theorem zo_sq_of_mainTheoremImproved (h : MainTheoremImproved) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_of_mainBound (mainBound_of_mainTheoremImproved h) N d p hp hrange ε hε hvar

/-- `Inf_i[p] ≥ (32 √15 / (125 π^4)) ε^{5/2} / d^6`, from `MainTheoremImproved`. -/
theorem zo_sqrt_of_mainTheoremImproved (h : MainTheoremImproved) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2)
      ≥ 32 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheoremImproved h N d p hp hrange ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) :=
    lt_of_lt_of_le one_pos (zo_hyps_force N d p hp hrange ε hε hvar).1
  exact ⟨i, (sqrt_form_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε.le hD
    (Ex_nonneg fun X => sq_nonneg _)).mpr hi⟩

/-! ### The power `5/2` and the encoding of `ExplicitBoundPM`

`Conjecture.lean` writes the power `ε^{5/2}` as the real power `ε ^ ((5 : ℝ) / 2)`, and
`ε ^ ((5 : ℝ) / 2) = ε² √ε` for `ε ≥ 0` (`rpow_five_halves`). The statement `ExplicitBoundPM` of
`Conjecture.lean`, on the cube `{-1,1}^n`, encodes the bit `true` as `1` and the bit `false` as
`-1` (`evPMt`), while `evPM`, like `Defs.lean`, sends `true` to `-1`. Negating every bit
(`negBits`) is a bijection of the cube: `evPMt p X = evPM p (negBits X)`, and `negBits` commutes
with the bit flips, so `evPMt p` and `evPM p` have the same expectation, the same variance and the
same influences. -/

/-- The real power `ε^{5/2}` is `ε² √ε`. -/
theorem rpow_five_halves {ε : ℝ} (hε : 0 ≤ ε) : ε ^ ((5 : ℝ) / 2) = ε ^ 2 * Real.sqrt ε := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add' hε (by norm_num)]
  norm_num

/-- The value of the polynomial `p` at the `±1` point attached to `X` with `true ↦ 1` and
`false ↦ -1`, the encoding of `ExplicitBoundPM`. -/
noncomputable def evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p

/-- Every bit of `X` negated. -/
def negBits {N : ℕ} (X : Fin N → Bool) : Fin N → Bool := fun i => !X i

theorem negBits_negBits {N : ℕ} (X : Fin N → Bool) : negBits (negBits X) = X := by
  funext i
  simp [negBits]

/-- Negating every bit, as a bijection of the cube. -/
def negBitsEquiv (N : ℕ) : (Fin N → Bool) ≃ (Fin N → Bool) :=
  ⟨negBits, negBits, negBits_negBits, negBits_negBits⟩

theorem Ex_comp_negBits {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    Ex (fun X => F (negBits X)) = Ex F := by
  unfold Ex
  congr 1
  exact Equiv.sum_comp (negBitsEquiv N) F

theorem negBits_flipBit {N : ℕ} (X : Fin N → Bool) (i : Fin N) :
    negBits (flipBit X i) = flipBit (negBits X) i := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [negBits, flipBit]
  · simp [negBits, flipBit, Function.update_of_ne hk]

theorem evPMt_eq {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) :
    evPMt p X = evPM p (negBits X) := by
  have hpt : (fun i => if X i then (1 : ℝ) else -1)
      = fun i => if negBits X i then (-1 : ℝ) else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (X i) with h | h <;> simp [negBits, h]
  unfold evPMt evPM
  rw [hpt]

theorem evPMt_bound_iff {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    (∀ X, |evPMt p X| ≤ 1) ↔ ∀ X, |evPM p X| ≤ 1 := by
  constructor
  · intro h X
    have hX := h (negBits X)
    rwa [evPMt_eq, negBits_negBits] at hX
  · intro h X
    rw [evPMt_eq]
    exact h (negBits X)

theorem Ex_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) : Ex (evPMt p) = Ex (evPM p) := by
  have e : evPMt p = fun X => evPM p (negBits X) := funext (evPMt_eq p)
  rw [e]
  exact Ex_comp_negBits (evPM p)

theorem variance_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) = Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) := by
  rw [Ex_evPMt]
  simp only [evPMt_eq]
  exact Ex_comp_negBits (fun X => (evPM p X - Ex (evPM p)) ^ 2)

theorem infl_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (i : Fin N) :
    Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      = Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) := by
  simp only [evPMt_eq, negBits_flipBit]
  exact Ex_comp_negBits (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2)

/-- `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²` on `{-1,1}^n` with `true ↦ 1`, from `MainTheorem`. -/
theorem pmt_sq_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2) ^ 2 := by
  rw [variance_evPMt] at hvar
  obtain ⟨i, hi⟩ :=
    pm_sq_of_mainTheorem h n d p hp ((evPMt_bound_iff p).mp hbd) ε hε hvar
  exact ⟨i, by rwa [infl_evPMt]⟩

/-- `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6` on `{-1,1}^n` with `true ↦ 1`, from
`MainTheorem`, with the power `5/2` written `ε² √ε`. -/
theorem pmt_sqrt_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  rw [variance_evPMt] at hvar
  obtain ⟨i, hi⟩ :=
    pm_sqrt_of_mainTheorem h n d p hp ((evPMt_bound_iff p).mp hbd) ε hε hvar
  exact ⟨i, by rwa [infl_evPMt]⟩

end AaronsonAmbainis.Bridge
