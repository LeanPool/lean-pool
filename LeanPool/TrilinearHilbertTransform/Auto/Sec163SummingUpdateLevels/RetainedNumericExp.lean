/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec163SummingUpdateLevels.NormalizedAbsorptionOfActiveFinal

/-!
# Trilinear Hilbert transform: retained_numeric_exp
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
section
open Filter Real Asymptotics

open scoped Classical in
private def RetainedNumericExpErrorBoundStatement : Prop :=
  ∀ (L₄ : ℝ)
    (α : ℝ)
    (θ₀ : ℝ)
    (Ca : ℝ)
    (b : ℕ)
    (m : ℕ)
    (c₃ : ℕ)
    (_ : ℕ)
    (cc : ℕ)
    (Cl : ℕ)
    (_ : (0 : ℝ) ≤ L₄)
    (_ : (0 : ℝ) < α)
    (_ : (0 : ℝ) < Ca)
    (_ : (1 : ℕ) ≤ m),
  let AL : ℝ :=
    (6000 : ℝ) ^ (30 : ℕ) * (3 : ℝ) ^ (30 : ℕ) + (1 : ℝ)
  let a₁ : ℕ :=
    (30 : ℕ) * b + (cc + (1 : ℕ)) * Cl
  let s : ℕ :=
    max m b
  ∀ (_ : (0 : ℝ) ≤ (↑Cl : ℝ)),
  let D : ℝ :=
    ((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) ^ Cl
  ∀ (k : ℕ)
    (_ : (1 : ℕ) ≤ k),
  let u : ℝ :=
    (↑k : ℝ)
  ∀ (_ : (0 : ℝ) ≤ u)
    (_ : (4 : ℝ) * ((4 : ℝ) * AL * (↑Cl : ℝ) * D * (2 : ℝ) ^ Cl * (9 : ℝ)) * u ^ a₁ * rexp
      (((↑Cl : ℝ) + (4 : ℝ)) * u) ≤ rexp (u ^ c₃))
    (_ : (8 : ℝ) * ((4 : ℝ) * AL * (↑Cl : ℝ) * D * (2 : ℝ) ^ Cl) * u ^ a₁ * rexp (((↑Cl : ℝ)
      + (2 : ℝ)) * u) ≤ rexp (u ^ (cc + (1 : ℕ))))
    (_ : (4 : ℝ) * ((4 : ℝ) * AL * (↑Cl : ℝ)) * u ^ ((30 : ℕ) * b) ≤ rexp ((1 / 2 : ℝ) * u))
    (_ : (4 : ℝ) * ((4 : ℝ) * ((576 : ℝ) * AL * rexp (L₄ + (3 : ℝ)))) * u ^ ((30 : ℕ) * b) *
      rexp ((Ca + (4 : ℝ)) * u ^ s) ≤ rexp (u ^ c₃)),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * u ^ b
  ∀ (_ : Y = L₄ + (2 : ℝ) * u ^ b)
    (_ : (1 : ℝ) ≤ u ^ b)
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) ≤ (4 : ℝ) * AL * u ^ ((30
      : ℕ) * b))
    (_ : u ^ θ₀ ≤ u)
    (_ : (0 : ℝ) ≤ u ^ θ₀),
  let PL : ℝ :=
    rexp ((2 : ℝ) * α * u ^ θ₀)
  ∀ (_ : (1 : ℝ) ≤ PL)
    (_ : PL ≤ rexp u),
  let G : ℝ :=
    rexp (((1 : ℝ) + log ((2 : ℝ) * u)) ^ (2 : ℕ))
  ∀ (_ : G ^ Cl ≤ rexp u),
  let kD : ℝ :=
    ((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * u ^ (cc + (1 : ℕ))
  ∀ (_ : kD = ((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * u ^ (cc + (1 : ℕ)))
    (_ : kD ^ Cl = D * u ^ ((cc + (1 : ℕ)) * Cl))
    (_ : ∀ (x y : ℕ), x ≤ y → u ^ x ≤ u ^ y)
    (_ : u ^ a₁ = u ^ ((30 : ℕ) * b) * u ^ ((cc + (1 : ℕ)) * Cl))
    (_ : ∀ (x y : ℝ), rexp x * rexp y = rexp (x + y)),
  (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * ((↑Cl : ℝ) * kD ^ Cl *
    (PL + (1 : ℝ)) ^ Cl * G ^ Cl * ((PL + (2 : ℝ)) ^ (2 : ℕ) * rexp (-u ^ c₃) + rexp
    ((↑Cl : ℝ) * u ^ cc) * (rexp (-kD / (2 : ℝ)) + rexp (-kD))) + (↑Cl : ℝ) * rexp
    (-u)) + (rexp (Ca * u ^ m) + (1 : ℝ)) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^
    (30 : ℕ) + (1 : ℝ)) * ((9 : ℝ) * (rexp (Y + (3 : ℝ)) + (1 : ℝ)) * rexp (-u ^ c₃) *
    (16 : ℝ))) ≤ rexp ((-2 : ℝ) * u ^ θ₀) ^ min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 :
    ℝ))




private theorem retained_numeric_exp_error_bound : RetainedNumericExpErrorBoundStatement := by
  classical
  intro L₄ α θ₀ Ca b m c₃ c cc Cl hL₄ hα hCa hm1 AL a₁ s hClr D k hk1 u hu0 d21a d21b d21c d21d Y
    hYdef hub1 hF hθu hθ0 PL hPL1 hPLu G hGCl kD hkD hkDCl hupow hua₁ hexpd
  -- the errors
  set! A' : ℝ := 4 * AL * Cl * D * 2 ^ Cl with hA'
  rewrite [← hA'] at d21a d21b
  have hA'0 : 0 ≤ A' := by positivity
  have hPLCl : (PL + 1) ^ Cl ≤ 2 ^ Cl * Real.exp ((Cl : ℝ) * u) := by
    calc (PL + 1) ^ Cl ≤ (2 * Real.exp u) ^ Cl :=
          pow_le_pow_left₀ (by positivity) (by linarith only [hPLu, hPL1]) Cl
      _ = 2 ^ Cl * Real.exp ((Cl : ℝ) * u) := by rw [mul_pow, ← Real.exp_nat_mul]
  have hQ : 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl) ≤
      A' * u ^ a₁ * Real.exp (((Cl : ℝ) + 1) * u) := by
    rw [hkDCl]
    have e : A' * u ^ a₁ * Real.exp (((Cl : ℝ) + 1) * u) = (4 * AL * u ^ (30 * b)) *
        (Cl * (D * u ^ ((cc + 1) * Cl)) * (2 ^ Cl * Real.exp ((Cl : ℝ) * u)) * Real.exp u) := by
      rw [hA', hua₁, show ((Cl : ℝ) + 1) * u = (Cl : ℝ) * u + u by ring, Real.exp_add]
      ring
    rw [e]
    gcongr
  -- the closure term
  have hT1 : 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl) *
      ((PL + 2) ^ 2 * Real.exp (-u ^ c₃)) ≤ Real.exp (-u) / 4 := by
    have h1 : (PL + 2) ^ 2 ≤ 9 * Real.exp (2 * u) := by
      have : PL + 2 ≤ 3 * Real.exp u := by
        have := Real.one_le_exp hu0; linarith only [hPLu, this]
      calc (PL + 2) ^ 2 ≤ (3 * Real.exp u) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
        _ = 9 * Real.exp (2 * u) := by rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    have h2 : 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl) *
        (PL + 2) ^ 2 ≤ (A' * 9) * u ^ a₁ * Real.exp (((Cl : ℝ) + 3) * u) := by
      have := mul_le_mul hQ h1 (by positivity) (by positivity)
      refine this.trans (le_of_eq ?_)
      rw [show ((Cl : ℝ) + 3) * u = ((Cl : ℝ) + 1) * u + 2 * u by ring, ← hexpd]; ring
    have h3 : 4 * ((A' * 9) * u ^ a₁ * Real.exp (((Cl : ℝ) + 3) * u)) * Real.exp u ≤
        Real.exp (u ^ c₃) := by
      refine le_trans (le_of_eq ?_) d21a
      rw [show ((Cl : ℝ) + 4) * u = ((Cl : ℝ) + 3) * u + u by ring, Real.exp_add]
      ring
    have h4 := mul_exp_neg_le h3
    calc _ = (4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl) *
          (PL + 2) ^ 2) * Real.exp (-u ^ c₃) := by ring
      _ ≤ ((A' * 9) * u ^ a₁ * Real.exp (((Cl : ℝ) + 3) * u)) * Real.exp (-u ^ c₃) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ ≤ _ := h4
  -- the mode-error term
  have hT2 : 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl) *
      (Real.exp (Cl * u ^ cc) * (Real.exp (-kD / 2) + Real.exp (-kD))) ≤
      Real.exp (-u) / 4 := by
    have hkD0 : 0 ≤ kD := by positivity
    have h1 : Real.exp (Cl * u ^ cc) * (Real.exp (-kD / 2) + Real.exp (-kD)) ≤
        2 * Real.exp (-u ^ (cc + 1)) := by
      have h5 : Real.exp (-kD) ≤ Real.exp (-kD / 2) :=
        Real.exp_le_exp.mpr (by linarith only [hkD0])
      have h6 : (Cl : ℝ) * u ^ cc + -kD / 2 ≤ -u ^ (cc + 1) := by
        have := hupow cc (cc + 1) (by omega)
        rw [hkD]; nlinarith only [this, hClr]
      calc Real.exp (Cl * u ^ cc) * (Real.exp (-kD / 2) + Real.exp (-kD))
          ≤ Real.exp (Cl * u ^ cc) * (2 * Real.exp (-kD / 2)) := by
            gcongr; linarith only [h5]
        _ = 2 * Real.exp (Cl * u ^ cc + -kD / 2) := by rw [← hexpd]; ring
        _ ≤ 2 * Real.exp (-u ^ (cc + 1)) := by gcongr
    have h3 : 4 * ((A' * 2) * u ^ a₁ * Real.exp (((Cl : ℝ) + 1) * u)) * Real.exp u ≤
        Real.exp (u ^ (cc + 1)) := by
      refine le_trans (le_of_eq ?_) d21b
      rw [show ((Cl : ℝ) + 2) * u = ((Cl : ℝ) + 1) * u + u by ring, Real.exp_add]
      ring
    have h4 := mul_exp_neg_le h3
    calc _ ≤ (A' * u ^ a₁ * Real.exp (((Cl : ℝ) + 1) * u)) * (2 * Real.exp (-u ^ (cc + 1))) :=
          mul_le_mul hQ h1 (by positivity) (by positivity)
      _ = ((A' * 2) * u ^ a₁ * Real.exp (((Cl : ℝ) + 1) * u)) * Real.exp (-u ^ (cc + 1)) := by
          ring
      _ ≤ _ := h4
  -- the remainder term
  have hT3 : 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * Real.exp (-u)) ≤
      Real.exp (-(u / 2)) / 4 := by
    have h3 : 4 * (4 * AL * Cl * u ^ (30 * b)) * Real.exp (u / 2) ≤ Real.exp u := by
      have := mul_le_mul_of_nonneg_right d21c (Real.exp_pos (u / 2)).le
      refine le_trans (le_of_eq (by ring)) (this.trans (le_of_eq ?_))
      rw [hexpd]; ring_nf
    have h4 := mul_exp_neg_le h3
    calc _ ≤ (4 * AL * u ^ (30 * b)) * (Cl * Real.exp (-u)) :=
          mul_le_mul_of_nonneg_right hF (by positivity)
      _ = (4 * AL * Cl * u ^ (30 * b)) * Real.exp (-u) := by ring
      _ ≤ _ := h4
  -- the catalog term
  have hT4 : (Real.exp (Ca * u ^ m) + 1) * (4 * (6000 ^ 30 * Y ^ 30 + 1) *
      (9 * (Real.exp (Y + 3) + 1) * Real.exp (-u ^ c₃) * 16)) ≤ Real.exp (-u) / 4 := by
    have hs1 : 1 ≤ s := le_trans hm1 (le_max_left _ _)
    have hm' : u ^ m ≤ u ^ s := hupow _ _ (le_max_left _ _)
    have hb' : u ^ b ≤ u ^ s := hupow _ _ (le_max_right _ _)
    have hus : u ≤ u ^ s := by
      have := hupow 1 s hs1; rwa [pow_one] at this
    have h1 : Real.exp (Ca * u ^ m) + 1 ≤ 2 * Real.exp (Ca * u ^ m) := by
      have := Real.one_le_exp (show 0 ≤ Ca * u ^ m by positivity); linarith only [this]
    have h2 : Real.exp (Y + 3) + 1 ≤ 2 * (Real.exp (L₄ + 3) * Real.exp (2 * u ^ b)) := by
      have := Real.one_le_exp (show 0 ≤ Y + 3 by positivity)
      rw [hexpd, show L₄ + 3 + 2 * u ^ b = Y + 3 by rw [hYdef]; ring]
      linarith only [this]
    have h3 : 4 * ((4 * (576 * AL * Real.exp (L₄ + 3))) * u ^ (30 * b) *
        Real.exp ((Ca + 3) * u ^ s)) * Real.exp u ≤ Real.exp (u ^ c₃) := by
      refine le_trans ?_ d21d
      have : (Ca + 3) * u ^ s + u ≤ (Ca + 4) * u ^ s := by nlinarith only [hus]
      calc 4 * ((4 * (576 * AL * Real.exp (L₄ + 3))) * u ^ (30 * b) *
            Real.exp ((Ca + 3) * u ^ s)) * Real.exp u
          = 4 * (4 * (576 * AL * Real.exp (L₄ + 3))) * u ^ (30 * b) *
              (Real.exp ((Ca + 3) * u ^ s) * Real.exp u) := by ring
        _ = 4 * (4 * (576 * AL * Real.exp (L₄ + 3))) * u ^ (30 * b) *
              Real.exp ((Ca + 3) * u ^ s + u) := by rw [hexpd]
        _ ≤ 4 * (4 * (576 * AL * Real.exp (L₄ + 3))) * u ^ (30 * b) *
              Real.exp ((Ca + 4) * u ^ s) := by gcongr
    have h4 := mul_exp_neg_le h3
    have h5 : Real.exp (Ca * u ^ m) * Real.exp (2 * u ^ b) ≤ Real.exp ((Ca + 3) * u ^ s) := by
      rw [hexpd]; apply Real.exp_le_exp.mpr; nlinarith only [hm', hb', hCa, hub1]
    calc _ ≤ (2 * Real.exp (Ca * u ^ m)) * ((4 * AL * u ^ (30 * b)) *
          (9 * (2 * (Real.exp (L₄ + 3) * Real.exp (2 * u ^ b))) * Real.exp (-u ^ c₃) * 16)) := by
          gcongr
      _ = (4 * (576 * AL * Real.exp (L₄ + 3)) * u ^ (30 * b) *
          (Real.exp (Ca * u ^ m) * Real.exp (2 * u ^ b))) * Real.exp (-u ^ c₃) := by ring
      _ ≤ (4 * (576 * AL * Real.exp (L₄ + 3)) * u ^ (30 * b) *
          Real.exp ((Ca + 3) * u ^ s)) * Real.exp (-u ^ c₃) := by gcongr
      _ ≤ _ := h4
  -- the sum and `η₀^{c_*}`
  have hsum : Real.exp (-u) / 4 + Real.exp (-u) / 4 + Real.exp (-(u / 2)) / 4 +
      Real.exp (-u) / 4 ≤ Real.exp (-(u / 2)) := by
    have : Real.exp (-u) ≤ Real.exp (-(u / 2)) := Real.exp_le_exp.mpr (by linarith only [hu0])
    linarith only [this]
  have hη : Real.exp (-(u / 2)) ≤
      Real.exp (-2 * u ^ θ₀) ^ min ((1 / 1200 : ℝ) / 2) (α / 4) := by
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hc1 : min ((1 / 1200 : ℝ) / 2) (α / 4) ≤ 1 / 2400 := by
      have := min_le_left ((1 / 1200 : ℝ) / 2) (α / 4); linarith only [this]
    have hc0 : 0 ≤ min ((1 / 1200 : ℝ) / 2) (α / 4) := le_min (by norm_num) (by positivity)
    nlinarith only [hc1, hc0, hθu, hθ0, hu0]
  have e : 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl *
      ((PL + 2) ^ 2 * Real.exp (-u ^ c₃) + Real.exp (Cl * u ^ cc) *
        (Real.exp (-kD / 2) + Real.exp (-kD))) + Cl * Real.exp (-u)) =
      4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl) *
        ((PL + 2) ^ 2 * Real.exp (-u ^ c₃)) +
      4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl * (PL + 1) ^ Cl * G ^ Cl) *
        (Real.exp (Cl * u ^ cc) * (Real.exp (-kD / 2) + Real.exp (-kD))) +
      4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * Real.exp (-u)) := by ring
  rw [e]
  linarith only [hT1, hT2, hT3, hT4, hsum, hη]


/-- The exponential standing bounds of the retained-attempt estimate at accuracy `k` (blueprint
lines 2870-2888: `P = ⌈η₀^{-α}⌉` dominates every fixed power of `k` and of the unit
`G = e^{(1 + log 2k)²}`, and the closure, mode and catalog errors are below `η₀^{c_*}`), with
`Y = L₄ + 2 k^b`, `F = 4 (6000^{30} Y^{30} + 1)`, `k_D = (2 C_l + 2) k^{cc+1}`,
`τ₃ = e^{-k^{c₃}}` and `η₀ = e^{-2 k^{θ₀}}`. -/
theorem retained_numeric_exp {L₄ lW α θ₀ Ca : ℝ} {b m c₃ c cc Cl : ℕ} (hL₄ : 0 ≤ L₄)
    (hlW : 0 ≤ lW) (hα : 0 < α) (hα8 : α ≤ 1 / 9600) (hθ₀ : 0 < θ₀) (hθ₁ : θ₀ ≤ 1)
    (hCa : 0 < Ca) (hb : 1 ≤ b) (hbc : 30 * b < c) (hmc₃ : m < c₃) (hbc₃ : b < c₃)
    (hm1 : 1 ≤ m) (hcc : 1 ≤ cc) :
    ∀ᶠ k : ℕ in atTop,
      (Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1) *
        (20 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1) + 60) + 1 ≤ Real.exp ((k : ℝ) ^ c) ∧
      8 * (lW + (L₄ + 2 * (k : ℝ) ^ b) + 1) ≤ Real.exp ((2 * Cl + 2) * (k : ℝ) ^ (cc + 1)) ∧
      4 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1) * Cl *
          ((2 * Cl + 2) * (k : ℝ) ^ (cc + 1)) ^ Cl *
          Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl ≤ Real.exp (2 * α * (k : ℝ) ^ θ₀) ∧
      Cl * ((2 * Cl + 2) * (k : ℝ) ^ (cc + 1)) ^ Cl + 2 ≤ Real.exp (2 * α * (k : ℝ) ^ θ₀) ∧
      4 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1) * Cl *
          (2 + ((Cl : ℝ) + 1) * (2 * α * (k : ℝ) ^ θ₀ + 1)) ^ 6 *
          Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl ≤ Real.exp (α * (k : ℝ) ^ θ₀ / 4) ∧
      4 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1) *
          (Cl * ((2 * Cl + 2) * (k : ℝ) ^ (cc + 1)) ^ Cl *
            (Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1) ^ Cl *
            Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
            ((Real.exp (2 * α * (k : ℝ) ^ θ₀) + 2) ^ 2 * Real.exp (-(k : ℝ) ^ c₃) +
              Real.exp (Cl * (k : ℝ) ^ cc) *
                (Real.exp (-((2 * Cl + 2) * (k : ℝ) ^ (cc + 1)) / 2) +
                  Real.exp (-((2 * Cl + 2) * (k : ℝ) ^ (cc + 1))))) +
            Cl * Real.exp (-(k : ℝ))) +
        (Real.exp (Ca * (k : ℝ) ^ m) + 1) * (4 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1) *
          (9 * (Real.exp ((L₄ + 2 * (k : ℝ) ^ b) + 3) + 1) * Real.exp (-(k : ℝ) ^ c₃) * 16)) ≤
        Real.exp (-2 * (k : ℝ) ^ θ₀) ^ min ((1 / 1200 : ℝ) / 2) (α / 4) := by
  set! AL : ℝ := 6000 ^ 30 * 3 ^ 30 + 1 with hAL
  have hAL1 : 1 ≤ AL := by rw [hAL]; norm_num
  set! a₁ : ℕ := 30 * b + (cc + 1) * Cl with ha₁
  set! s : ℕ := max m b with hs
  have hsc₃ : s < c₃ := max_lt hmc₃ hbc₃
  have hClr : (0 : ℝ) ≤ Cl := Nat.cast_nonneg _
  set! D : ℝ := (2 * Cl + 2) ^ Cl with hD
  have hD1 : 1 ≤ D := one_le_pow₀ (by linarith only)
  filter_upwards [eventually_nat_add_pow_le L₄ hb, eventually_ge_atTop 1,
    eventually_nat_poly_exp_le_exp (162 * AL) (30 * b : ℕ) 1 (show 1 < c by omega) one_pos,
    eventually_nat_poly_exp_le_exp (8 * (lW + 1 + L₄ + 2)) (b : ℕ) 0
      (show 0 < cc + 1 by omega) one_pos,
    eventually_nat_const_qpoly_le_exp (4 * AL * Cl * D) (a₁ : ℝ) (by positivity) hClr
      (by positivity : 0 < 2 * α) hθ₀,
    eventually_nat_const_qpoly_le_exp (Cl * D + 2) (((cc + 1) * Cl : ℕ) : ℝ) (by positivity)
      le_rfl (by positivity : 0 < 2 * α) hθ₀,
    eventually_nat_const_qpoly_le_exp (4 * AL * Cl * (4 * ((Cl : ℝ) + 1)) ^ 6)
      ((30 * b + 6 : ℕ) : ℝ) (by positivity) hClr (by positivity : 0 < α / 4) hθ₀,
    eventually_nat_qpoly_le_exp 0 hClr one_pos one_pos,
    eventually_nat_poly_exp_le_exp (4 * (4 * AL * Cl * D * 2 ^ Cl * 9)) (a₁ : ℝ) ((Cl : ℝ) + 4)
      (show 1 < c₃ by omega) one_pos,
    eventually_nat_poly_exp_le_exp (8 * (4 * AL * Cl * D * 2 ^ Cl)) (a₁ : ℝ) ((Cl : ℝ) + 2)
      (show 1 < cc + 1 by omega) one_pos,
    eventually_nat_poly_exp_le_exp (4 * (4 * AL * Cl)) ((30 * b : ℕ) : ℝ) 0
      (show 0 < 1 by omega) (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_nat_poly_exp_le_exp (4 * (4 * (576 * AL * Real.exp (L₄ + 3)))) ((30 * b : ℕ) : ℝ)
      (Ca + 4) hsc₃ one_pos]
    with k hY hk1 d3 d10 d18 d19 d20 dG d21a d21b d21c d21d
  have hu1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set u : ℝ := (k : ℝ) with hudef
  have hu0 : 0 ≤ u := by linarith only [hu1]
  have hrp : ∀ n : ℕ, u ^ (n : ℝ) = u ^ n := fun n => Real.rpow_natCast u n
  simp only [hrp, Real.rpow_zero, Real.rpow_one, one_mul, zero_mul, Real.exp_zero, mul_one,
    pow_one, pow_zero] at d3 d10 d18 d19 d20 dG d21a d21b d21c d21d
  set! Y : ℝ := L₄ + 2 * u ^ b with hYdef
  rewrite [← hYdef] at hY ⊢
  have hY0 : 0 ≤ Y := by positivity
  have hub1 : 1 ≤ u ^ b := one_le_pow₀ hu1
  have hY30 : Y ^ 30 ≤ 3 ^ 30 * u ^ (30 * b) := by
    calc Y ^ 30 ≤ (3 * u ^ b) ^ 30 := pow_le_pow_left₀ hY0 hY 30
      _ = 3 ^ 30 * u ^ (30 * b) := by rw [mul_pow, ← pow_mul, mul_comm b]
  have hu30 : 1 ≤ u ^ (30 * b) := one_le_pow₀ hu1
  have hP30 : 6000 ^ 30 * Y ^ 30 + 1 ≤ AL * u ^ (30 * b) := by
    rw [hAL]; nlinarith only [hY30, hu30]
  have hF : 4 * (6000 ^ 30 * Y ^ 30 + 1) ≤ 4 * AL * u ^ (30 * b) := by linarith only [hP30]
  have hF0 : 0 ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) := by positivity
  have hθu : u ^ θ₀ ≤ u := by
    have := Real.rpow_le_rpow_of_exponent_le hu1 hθ₁; rwa [Real.rpow_one] at this
  have hθ0 : 0 ≤ u ^ θ₀ := Real.rpow_nonneg hu0 _
  have h2α : 2 * α * u ^ θ₀ ≤ u := by nlinarith only [hθu, hα8, hα, hθ0, hu0]
  set! PL := Real.exp (2 * α * u ^ θ₀) with hPL
  rewrite [← hPL] at d18 d19 ⊢
  have hPL1 : 1 ≤ PL := Real.one_le_exp (by positivity)
  have hPLu : PL ≤ Real.exp u := Real.exp_le_exp.mpr h2α
  set! G := Real.exp ((1 + Real.log (2 * u)) ^ 2) with hG
  rewrite [← hG] at ⊢
  have hGCl : G ^ Cl ≤ Real.exp u := by rw [hG, ← Real.exp_nat_mul]; exact dG
  have hG0 : 0 ≤ G ^ Cl := by positivity
  set! kD := (2 * (Cl : ℝ) + 2) * u ^ (cc + 1) with hkD
  rewrite [← hkD] at ⊢
  have hkDCl : kD ^ Cl = D * u ^ ((cc + 1) * Cl) := by rw [hkD, mul_pow, ← pow_mul, hD]
  have hupow : ∀ x y : ℕ, x ≤ y → u ^ x ≤ u ^ y := fun x y h => pow_le_pow_right₀ hu1 h
  have hua₁ : u ^ a₁ = u ^ (30 * b) * u ^ ((cc + 1) * Cl) := by rw [ha₁, pow_add]
  have hexpd : ∀ x y : ℝ, Real.exp x * Real.exp y = Real.exp (x + y) := fun x y =>
    (Real.exp_add x y).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `H_max`
    have hX : 20 * (6000 ^ 30 * Y ^ 30 + 1) + 60 + 1 ≤ 81 * AL * u ^ (30 * b) := by
      nlinarith only [hP30, hu30, hAL1]
    have hX0 : 0 ≤ 20 * (6000 ^ 30 * Y ^ 30 + 1) + 60 := by positivity
    calc (PL + 1) * (20 * (6000 ^ 30 * Y ^ 30 + 1) + 60) + 1
        ≤ (2 * PL) * (20 * (6000 ^ 30 * Y ^ 30 + 1) + 60 + 1) := by nlinarith only [hPL1, hX0]
      _ ≤ (2 * Real.exp u) * (81 * AL * u ^ (30 * b)) :=
          mul_le_mul (by linarith only [hPLu]) hX (by positivity) (by positivity)
      _ = 162 * AL * u ^ (30 * b) * Real.exp u := by ring
      _ ≤ _ := d3
  · -- the mode error accuracy
    have h1 : 8 * (lW + Y + 1) ≤ 8 * (lW + 1 + L₄ + 2) * u ^ b := by
      rw [hYdef]; nlinarith only [hub1, hlW, hL₄]
    have h2 : Real.exp (u ^ (cc + 1)) ≤ Real.exp kD := by
      rw [hkD]; apply Real.exp_le_exp.mpr
      have : 0 ≤ u ^ (cc + 1) := by positivity
      nlinarith only [this, hClr]
    linarith only [h1, d10, h2]
  · -- `P` dominates the leaf factor
    rw [hkDCl]
    have e : 4 * AL * u ^ (30 * b) * Cl * (D * u ^ ((cc + 1) * Cl)) * G ^ Cl =
        4 * AL * Cl * D * u ^ a₁ * Real.exp (Cl * (1 + Real.log (2 * u)) ^ 2) := by
      rw [hua₁, hG, ← Real.exp_nat_mul]; ring
    calc 4 * (6000 ^ 30 * Y ^ 30 + 1) * Cl * (D * u ^ ((cc + 1) * Cl)) * G ^ Cl
        ≤ 4 * AL * u ^ (30 * b) * Cl * (D * u ^ ((cc + 1) * Cl)) * G ^ Cl := by gcongr
      _ = _ := e
      _ ≤ _ := d18
  · rw [hkDCl]
    have hu' : 1 ≤ u ^ ((cc + 1) * Cl) := one_le_pow₀ hu1
    have : (Cl : ℝ) * (D * u ^ ((cc + 1) * Cl)) + 2 ≤ (Cl * D + 2) * u ^ ((cc + 1) * Cl) := by
      nlinarith only [hu']
    exact this.trans d19
  · -- the near-band factor
    have h1 : 2 + ((Cl : ℝ) + 1) * (2 * α * u ^ θ₀ + 1) ≤ 4 * ((Cl : ℝ) + 1) * u := by
      nlinarith only [h2α, hu1, hClr]
    have h10 : 0 ≤ 2 + ((Cl : ℝ) + 1) * (2 * α * u ^ θ₀ + 1) := by positivity
    have h6 := pow_le_pow_left₀ h10 h1 6
    rw [mul_pow] at h6
    have e : 4 * AL * u ^ (30 * b) * Cl * ((4 * ((Cl : ℝ) + 1)) ^ 6 * u ^ 6) * G ^ Cl =
        4 * AL * Cl * (4 * ((Cl : ℝ) + 1)) ^ 6 * u ^ (30 * b + 6) *
          Real.exp (Cl * (1 + Real.log (2 * u)) ^ 2) := by
      rw [pow_add, hG, ← Real.exp_nat_mul]; ring
    have e2 : α * u ^ θ₀ / 4 = α / 4 * u ^ θ₀ := by ring
    rw [e2]
    calc 4 * (6000 ^ 30 * Y ^ 30 + 1) * Cl * (2 + ((Cl : ℝ) + 1) * (2 * α * u ^ θ₀ + 1)) ^ 6 *
          G ^ Cl
        ≤ 4 * AL * u ^ (30 * b) * Cl * ((4 * ((Cl : ℝ) + 1)) ^ 6 * u ^ 6) * G ^ Cl := by gcongr
      _ = _ := e
      _ ≤ _ := d20
  · expose_names
    exact @retained_numeric_exp_error_bound L₄ α θ₀ Ca b m c₃ c cc Cl hL₄ hα hCa hm1 hClr k hk1
      hu0 d21a d21b d21c d21d hYdef hub1 hF hθu hθ0 hPL1 hPLu hGCl hkD hkDCl hupow hua₁ hexpd
end

/-- The final absorption on one root (blueprint lines 2851-2888, from `eq:before-absorption` to
`eq:active-final`) for the explicit leaf bound summed over `N_lv` leaves plus a localization error
`E_r |R|`. With `ε = 1/1200`, `C₄ = C_l + 1`, `α = ε/(4(C₄+1))`, `P = ⌈η₀^{-α}⌉` and `η = 4η₀`:
if `P` dominates the leaf count, the powers of `k_D` and the unit `G = e^{(1 + log 2k)²}`
(`h1`-`h3`), and the remaining errors are at most `η₀^{c_*}` (`h4`), the total is at most
`((3 + C_q)(2^{C₄} + 1) + 1) η₀^{c_*} (1 + C_N) |R|` with `c_* = min(ε/2, α/4)`. -/
theorem retained_arith {Cl P k cc : ℕ} {kD η₀ τ₃ δ CN Cq q R Nlv Er : ℝ}
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1) (hCN : 0 ≤ CN) (hCq : 0 ≤ Cq) (hR : 0 ≤ R) (hNlv : 0 ≤ Nlv)
    (hkD : 0 ≤ kD)
    (hP : (P : ℝ) = ⌈η₀ ^ (-((1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1))))⌉₊)
    (hq2 : 2 < q) (hq3 : q < 3) (hq : 2 * ((Cl : ℝ) + 1) * ((q - 2) / (q - 1)) ≤ 1 / 8)
    (h1 : Nlv * Cl * kD ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl ≤ P)
    (h2 : Cl * kD ^ Cl + 2 ≤ P)
    (h3 : Nlv * Cl * (2 + ((Cl : ℝ) + 1) * Real.log P) ^ 6 *
      Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl ≤ (P : ℝ) ^ (1 / 8 : ℝ))
    (h4 : Nlv * (Cl * (kD * P) ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
      (((P : ℝ) + 1) ^ 2 * τ₃ + Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ + Real.exp (-kD))) +
        Cl * Real.exp (-(k : ℝ))) + Er ≤
      η₀ ^ min ((1 / 1200 : ℝ) / 2) ((1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1)) / 4)) :
    Nlv * leafBnd Cl kD P k cc (4 * η₀) η₀ τ₃ δ CN Cq q R + Er * R ≤
      ((3 + Cq) * (2 ^ ((Cl : ℝ) + 1) + 1) + 1) *
        η₀ ^ min ((1 / 1200 : ℝ) / 2) ((1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1)) / 4) *
        (1 + CN) * R := by
  set c := min ((1 / 1200 : ℝ) / 2) ((1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1)) / 4) with hc
  set Gk := Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) with hGk
  have hGk1 : 1 ≤ Gk := Real.one_le_exp (sq_nonneg _)
  have hGk0 : 0 ≤ Gk := by linarith only [hGk1]
  have hP1 : (1 : ℝ) ≤ P := by
    rw [hP]
    have : 1 ≤ η₀ ^ (-((1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1)))) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη0 hη1 (by
        have : (0 : ℝ) ≤ (1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1)) := by positivity
        linarith only [this])
    exact this.trans (Nat.le_ceil _)
  have hP0 : (0 : ℝ) ≤ P := by linarith only [hP1]
  have hCl0 : (0 : ℝ) ≤ Cl := Nat.cast_nonneg _
  -- the polynomial size `K = C_l (k_D P)^{C_l}` and the power `P^{C₄}`
  set K : ℝ := Cl * (kD * P) ^ Cl with hK
  have hK0 : 0 ≤ K := mul_nonneg hCl0 (pow_nonneg (mul_nonneg hkD hP0) _)
  have hC₄ : ((P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ)) = (P : ℝ) ^ (Cl + 1) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have hKP : K + 2 ≤ 1 * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ) := by
    rw [one_mul, hC₄, hK, mul_pow, pow_succ]
    have hPCl : (1 : ℝ) ≤ (P : ℝ) ^ Cl := one_le_pow₀ hP1
    have e : (Cl : ℝ) * (kD ^ Cl * (P : ℝ) ^ Cl) = (Cl * kD ^ Cl) * (P : ℝ) ^ Cl := by ring
    rw [e]
    have h0 : 0 ≤ (Cl : ℝ) * kD ^ Cl := mul_nonneg hCl0 (pow_nonneg hkD _)
    nlinarith only [h2, hPCl, h0]
  have hlogK : Real.log (K + 2) ≤ ((Cl : ℝ) + 1) * Real.log P := by
    have h := Real.log_le_log (by linarith only [hK0]) (hKP.trans_eq (by rw [one_mul, hC₄]))
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hlogK0 : 0 ≤ Real.log (K + 2) := Real.log_nonneg (by linarith only [hK0])
  -- the near-band factor `G₀ ≤ P^{1/8}`
  set! G₀ : ℝ := Nlv * Cl * (2 + Real.log (K + 2)) ^ 6 * Gk ^ Cl with hG₀
  have hG₀P : G₀ ≤ (P : ℝ) ^ (1 / 8 : ℝ) := by
    refine le_trans ?_ h3
    rw [hG₀]
    have h6 : (2 + Real.log (K + 2)) ^ 6 ≤ (2 + ((Cl : ℝ) + 1) * Real.log P) ^ 6 :=
      pow_le_pow_left₀ (by linarith only [hlogK0]) (by linarith only [hlogK]) 6
    have h0 : 0 ≤ Nlv * Cl := mul_nonneg hNlv hCl0
    have hG : 0 ≤ Gk ^ Cl := pow_nonneg hGk0 _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 h0) hG
  -- the main term: `N_lv C_l (k_D P)^{C_l} G^{C_l} (η^{ε} + η₀) ≤ 3 η₀^ε P^{C₄}`
  have hmainP : Nlv * (Cl * (kD * P) ^ Cl * Gk ^ Cl) ≤ (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ) := by
    rw [hC₄, pow_succ]
    have e : Nlv * (Cl * (kD * P) ^ Cl * Gk ^ Cl) =
        (Nlv * Cl * kD ^ Cl * Gk ^ Cl) * (P : ℝ) ^ Cl := by rw [mul_pow]; ring
    rw [e, mul_comm ((P : ℝ) ^ Cl)]
    exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hP0 _)
  have hη4 : (4 * η₀) ^ (1 / 1200 : ℝ) + η₀ ≤ 3 * η₀ ^ (1 / 1200 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hη0.le]
    have h4 : (4 : ℝ) ^ (1 / 1200 : ℝ) ≤ 2 := by
      have e : (2 : ℝ) = 4 ^ (1 / 2 : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hη' : η₀ ≤ η₀ ^ (1 / 1200 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hη0 hη1 (show (1 / 1200 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have h0 : 0 ≤ η₀ ^ (1 / 1200 : ℝ) := Real.rpow_nonneg hη0.le _
    nlinarith only [h4, hη', h0]
  have hA1 : Nlv * (Cl * (kD * P) ^ Cl * Gk ^ Cl) * ((4 * η₀) ^ (1 / 1200 : ℝ) + η₀) * R ≤
      3 * (η₀ ^ (1 / 1200 : ℝ) * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ)) * R := by
    have h0 : 0 ≤ (4 * η₀) ^ (1 / 1200 : ℝ) + η₀ := by
      have := Real.rpow_nonneg (by linarith only [hη0] : (0 : ℝ) ≤ 4 * η₀) (1 / 1200 : ℝ)
      linarith only [this, hη0]
    have h5 := mul_le_mul hmainP hη4 h0 (Real.rpow_nonneg hP0 _)
    have h6 := mul_le_mul_of_nonneg_right h5 hR
    calc _ ≤ (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ) * (3 * η₀ ^ (1 / 1200 : ℝ)) * R := h6
      _ = _ := by ring
  -- the near-band term
  have hsqP : (Real.sqrt P)⁻¹ = (P : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hP0]
  -- the expansion of the summed leaf bound
  have hexp : Nlv * leafBnd Cl kD P k cc (4 * η₀) η₀ τ₃ δ CN Cq q R + Er * R =
      Nlv * (Cl * (kD * P) ^ Cl * Gk ^ Cl) * ((4 * η₀) ^ (1 / 1200 : ℝ) + η₀) * R +
      (Nlv * (K * Gk ^ Cl * (((P : ℝ) + 1) ^ 2 * τ₃ +
        Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ + Real.exp (-kD))) +
          Cl * Real.exp (-(k : ℝ))) + Er) * R +
      Cq * ((1 + CN) * ((P : ℝ) ^ (-(1 / 2) : ℝ) * G₀ * (K + 2) ^ (2 * (q - 2) / (q - 1)))) *
        R := by
    unfold leafBnd
    rw [div_eq_mul_inv _ (Real.sqrt _), hsqP, hG₀, hK]
    ring
  have hA2 := mul_le_mul_of_nonneg_right h4 hR
  have hc0 : 0 ≤ η₀ ^ c := Real.rpow_nonneg hη0.le _
  have hnear0 : 0 ≤ (1 + CN) * ((P : ℝ) ^ (-(1 / 2) : ℝ) * G₀ *
      (K + 2) ^ (2 * (q - 2) / (q - 1))) := by
    have hG0 : 0 ≤ G₀ := mul_nonneg (mul_nonneg (mul_nonneg hNlv hCl0)
      (pow_nonneg (by linarith only [hlogK0]) _)) (pow_nonneg hGk0 _)
    have h1' := Real.rpow_nonneg hP0 (-(1 / 2) : ℝ)
    have h2' := Real.rpow_nonneg (by linarith only [hK0] : (0 : ℝ) ≤ K + 2) (2 * (q - 2) / (q - 1))
    exact mul_nonneg (by linarith only [hCN]) (mul_nonneg (mul_nonneg h1' hG0) h2')
  have hmn0 : 0 ≤ η₀ ^ (1 / 1200 : ℝ) * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hη0.le _) (Real.rpow_nonneg hP0 _)
  have hX : Nlv * leafBnd Cl kD P k cc (4 * η₀) η₀ τ₃ δ CN Cq q R + Er * R ≤
      (3 + Cq) * (η₀ ^ (1 / 1200 : ℝ) * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ) +
        (1 + CN) * ((P : ℝ) ^ (-(1 / 2) : ℝ) * G₀ * (K + 2) ^ (2 * (q - 2) / (q - 1)))) * R +
        η₀ ^ c * R := by
    rw [hexp]
    have e1 : (3 + Cq) * (η₀ ^ (1 / 1200 : ℝ) * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ) +
        (1 + CN) * ((P : ℝ) ^ (-(1 / 2) : ℝ) * G₀ * (K + 2) ^ (2 * (q - 2) / (q - 1)))) * R =
        3 * (η₀ ^ (1 / 1200 : ℝ) * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ)) * R +
        Cq * (η₀ ^ (1 / 1200 : ℝ) * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ)) * R +
        3 * ((1 + CN) * ((P : ℝ) ^ (-(1 / 2) : ℝ) * G₀ * (K + 2) ^ (2 * (q - 2) / (q - 1)))) * R +
        Cq * ((1 + CN) * ((P : ℝ) ^ (-(1 / 2) : ℝ) * G₀ *
          (K + 2) ^ (2 * (q - 2) / (q - 1)))) * R := by ring
    rw [e1]
    have h5 : 0 ≤ Cq * (η₀ ^ (1 / 1200 : ℝ) * (P : ℝ) ^ (((Cl : ℝ) + 1) : ℝ)) * R :=
      mul_nonneg (mul_nonneg hCq hmn0) hR
    have h6 : 0 ≤ 3 * ((1 + CN) * ((P : ℝ) ^ (-(1 / 2) : ℝ) * G₀ *
        (K + 2) ^ (2 * (q - 2) / (q - 1)))) * R := mul_nonneg (mul_nonneg (by norm_num) hnear0) hR
    linarith only [hA1, hA2, h5, h6]
  rw [hP] at hG₀P hKP hX
  have hfin := active_final_arith (ε := 1 / 1200) (C₄ := (Cl : ℝ) + 1) (C₅ := (Cl : ℝ) + 1)
    (by norm_num) (by positivity) hη0 hη1 (by linarith only [hCq] : (0 : ℝ) ≤ 3 + Cq) hCN hR
    hG₀P hK0 hKP le_rfl hq2 hq3 hq hX
  have hR' : η₀ ^ c * R ≤ η₀ ^ c * (1 + CN) * R := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + CN by linarith only [hCN]) hc0
    nlinarith only [this, hR]
  rw [← hc] at hfin
  calc _ ≤ _ := hfin
    _ ≤ (3 + Cq) * (2 ^ ((Cl : ℝ) + 1) + 1) * η₀ ^ c * (1 + CN) * R +
        η₀ ^ c * (1 + CN) * R := by linarith only [hR']
    _ = _ := by ring

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ}

open Classical in
/-- Blueprint lines 2839-2841 on one root ("choose their thresholds so the union of exceptional
roots has length at most `|R|/4`"), assembled with the localization to the search leaves and the
leaf bounds: the failure roots (length at most `|R|/8`) and the six cut families of each of the
`N_l` leaves (lengths at most `2ρ|R|`, `12 N_l ρ ≤ 1/8`) have maximal union cells `X` of length
at most `|R|/4`, and the active minima of the pattern below no cell of `X` are at most
`N_l` times the leaf bound plus the localization error `M_p |R| W`. -/
theorem root_assembly (A : ActiveSetup κ c₀) (p : Fin 3) {δa : ℝ} (Tc FR : Finset (ℤ × ℤ))
    (hTc : Tc = A.cells.filter (A.active δa)) (Nl : ℕ) (Fl : ℕ → Fin 6 → Finset (ℤ × ℤ))
    (Lf : ℕ → ℤ × ℤ → ℝ) {ρ Bnd Mp W : ℝ}
    (hFRsub : ∀ c ∈ FR, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (hFR : ∑ c ∈ FR, dyadicGridLength A.G c.1 ≤ 1 / 8 * dyadicGridLength A.G A.R.1)
    (hFlsub : ∀ s < Nl, ∀ i, ∀ c ∈ Fl s i,
      dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (hFl : ∀ s < Nl, ∀ i, dyadicRootLength A.G (Fl s i) ≤ 2 * ρ * dyadicGridLength A.G A.R.1)
    (hNlρ : (Nl : ℝ) * (6 * (2 * ρ)) ≤ 1 / 8)
    (hloc : ∀ cs ⊆ Tc, (∀ I ∈ cs, ¬ ∃ e ∈ FR,
        dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) →
      ∑ I ∈ cs, dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ ≤
        ∑ s ∈ Finset.range Nl, ∑ I ∈ cs, dyadicGridLength A.G I.1 * Lf s I +
          (∑ I ∈ cs, dyadicGridLength A.G I.1) * W)
    (hleaf : ∀ s < Nl, ∀ cs ⊆ Tc, (∀ I ∈ cs, ¬ ∃ e ∈ FR,
        dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) →
      (∀ I ∈ cs, ∀ i, ∀ e ∈ Fl s i, ¬ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) →
      ∑ I ∈ cs, dyadicGridLength A.G I.1 * Lf s I ≤ Bnd)
    (hMp : ∀ y : ℝ, ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧
      A.active δa I).card : ℝ) ≤ Mp)
    (hW : 0 ≤ W) :
    ∃ X : Finset (ℤ × ℤ),
      (∀ c ∈ X, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧
      (∀ c ∈ X, ∀ c' ∈ X, c ≠ c' →
        Disjoint (dyadicGridCell A.G c.1 c.2) (dyadicGridCell A.G c'.1 c'.2)) ∧
      ∑ c ∈ X, dyadicGridLength A.G c.1 ≤ 1 / 4 * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ (A.cells.filter (fun I => ¬ ∃ c ∈ X,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G c.1 c.2)).filter (A.active δa),
        dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ ≤
      Nl * Bnd + Mp * dyadicGridLength A.G A.R.1 * W := by
  have hR := (dyadicGridLength_pos A.G A.R.1).le
  -- the cut families: the failure roots and the leaf cuts
  set! T : Finset (Option (ℕ × Fin 6)) :=
    insert none ((Finset.range Nl ×ˢ Finset.univ).image some) with hT
  set! F : Option (ℕ × Fin 6) → Finset (ℤ × ℤ) := fun o => o.elim FR (fun si => Fl si.1 si.2)
    with hF
  set! ρs : Option (ℕ × Fin 6) → ℝ := fun o => o.elim (1 / 8) (fun _ => 2 * ρ) with hρs
  have hnone : none ∉ (Finset.range Nl ×ˢ (Finset.univ : Finset (Fin 6))).image some := by
    simp
  have hsome : ∀ o ∈ T, o ≠ none → ∃ s < Nl, ∃ i, o = some (s, i) := by
    intro o ho hne
    rw [hT, Finset.mem_insert] at ho
    rcases ho with h | h
    · exact absurd h hne
    · obtain ⟨⟨s, i⟩, hsi, rfl⟩ := Finset.mem_image.mp h
      exact ⟨s, Finset.mem_range.mp (Finset.mem_product.mp hsi).1, i, rfl⟩
  have hFR' : ∀ o ∈ T, ∀ c ∈ F o, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 := by
    intro o ho c hc
    by_cases hn : o = none
    · subst hn; exact hFRsub c hc
    · obtain ⟨s, hs, i, rfl⟩ := hsome o ho hn
      exact hFlsub s hs i c hc
  have hFlen : ∀ o ∈ T, dyadicRootLength A.G (F o) ≤ ρs o * dyadicGridLength A.G A.R.1 := by
    intro o ho
    by_cases hn : o = none
    · subst hn; exact hFR
    · obtain ⟨s, hs, i, rfl⟩ := hsome o ho hn
      exact hFl s hs i
  have hρsum : ∑ o ∈ T, ρs o ≤ 1 / 4 := by
    rw [hT, Finset.sum_insert hnone, Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h)]
    simp only [hρs, Option.elim]
    rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    linarith only [hNlρ]
  obtain ⟨X, hXR, hXd, hXl, hXc⟩ := exceptional_union A.G T F ρs A.R hFR' hFlen hρsum
  refine ⟨X, hXR, hXd, hXl, ?_⟩
  -- the retained cells
  set cs := (A.cells.filter (fun I => ¬ ∃ c ∈ X,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G c.1 c.2)).filter (A.active δa) with hcs
  have hcsT : cs ⊆ Tc := by
    intro I hI
    rw [hTc]
    obtain ⟨hI1, hI2⟩ := Finset.mem_filter.mp hI
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hI1).1, hI2⟩
  have hnoX : ∀ I ∈ cs, ¬ ∃ c ∈ X, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G c.1 c.2 :=
    fun I hI => (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
  have hnoFR : ∀ I ∈ cs, ¬ ∃ e ∈ FR, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2 := by
    rintro I hI ⟨e, he, hIe⟩
    obtain ⟨d, hd, hed⟩ := hXc none (Finset.mem_insert_self _ _) e he
    exact hnoX I hI ⟨d, hd, hIe.trans hed⟩
  have hnoFl : ∀ s < Nl, ∀ I ∈ cs, ∀ i, ∀ e ∈ Fl s i,
      ¬ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2 := by
    intro s hs I hI i e he hIe
    have hmem : some (s, i) ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨(s, i), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hs, Finset.mem_univ _⟩, rfl⟩)
    obtain ⟨d, hd, hed⟩ := hXc (some (s, i)) hmem e he
    exact hnoX I hI ⟨d, hd, hIe.trans hed⟩
  -- the localization and the leaf bounds
  have h1 := hloc cs hcsT hnoFR
  have h2 : ∑ s ∈ Finset.range Nl, ∑ I ∈ cs, dyadicGridLength A.G I.1 * Lf s I ≤ Nl * Bnd := by
    calc ∑ s ∈ Finset.range Nl, ∑ I ∈ cs, dyadicGridLength A.G I.1 * Lf s I
        ≤ ∑ _s ∈ Finset.range Nl, Bnd := Finset.sum_le_sum fun s hs =>
          hleaf s (Finset.mem_range.mp hs) cs hcsT hnoFR (hnoFl s (Finset.mem_range.mp hs))
      _ = Nl * Bnd := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the localization error
  have h3 : ∑ I ∈ cs, dyadicGridLength A.G I.1 ≤ Mp * dyadicGridLength A.G A.R.1 := by
    have hcsA : ∀ I ∈ cs, I ∈ A.cells ∧ A.active δa I := by
      intro I hI
      obtain ⟨hI1, hI2⟩ := Finset.mem_filter.mp hI
      exact ⟨(Finset.mem_filter.mp hI1).1, hI2⟩
    have := integrated_cap_le A.G cs (fun _ => 1) A.R (fun I hI => A.sub I (hcsA I hI).1)
      (C := Mp) (fun x => by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hMp x)
        intro I hI
        obtain ⟨hIcs, hx⟩ := Finset.mem_filter.mp hI
        exact Finset.mem_filter.mpr ⟨(hcsA I hIcs).1, hx, (hcsA I hIcs).2⟩)
    simpa using this
  have h4 := mul_le_mul_of_nonneg_right h3 hW
  linarith only [h1, h2, h4]

end ActiveSetup

/-- A basic projection without columns vanishes almost everywhere: its current projection lies in
the span of no columns. -/
theorem BasicProjection.val_ae_zero_of_isEmpty {G : RealDyadicGrid} {R : ℤ × ℤ} {CF : ℝ}
    (P : BasicProjection G R CF) (hV : IsEmpty P.V) (I : ℤ × ℤ) :
    P.val I =ᵐ[MeasureTheory.volume] 0 := by
  unfold BasicProjection.val ColumnDepthFamily.currentZ
  split_ifs with h
  · have hr : cellColumnRange P.Ψ.D P.Ψ.A h = ⊥ := by
      have : IsEmpty {v // v ∈ P.Ψ.A.labels (P.Ψ.anc I)} := ⟨fun v => hV.elim v.1⟩
      rw [cellColumnRange, Set.range_eq_empty, Submodule.span_empty]
    have hmem := cellColumnProjection_mem P.Ψ.D P.Ψ.A h P.Z
    rw [hr, Submodule.mem_bot] at hmem
    rw [hmem]
    filter_upwards [MeasureTheory.Lp.coeFn_zero (ColumnHilbert P.V) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)] with y hy
    rw [hy]
    rfl
  · exact Filter.EventuallyEq.rfl

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ}

/-- Without vertices of the basic families (no basic columns) all pattern forms vanish on the cells
of the setup: every pattern has a basic slot, and the basic arguments vanish there. -/
theorem Hf_z_eq_zero_of_isEmpty_vtx (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
    (hV : ¬ Nonempty bf.Vtx) (p : Fin 3) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    A.Hf I (A.z (Fin.castSucc p) I) = 0 := by
  have hcell : Nonempty (AdmCell A.G A.R A.treeDepth) :=
    ⟨⟨A.R, dyadicFiniteTree_root_mem A.G A.R A.treeDepth⟩⟩
  have hLab : IsEmpty bf.Lab := ⟨fun x => hV ⟨(x, hcell.some)⟩⟩
  have hPV : ∀ l j, IsEmpty (bf.P l j).V := fun l j => ⟨fun v => hLab.elim ⟨l, ⟨j, v⟩⟩⟩
  -- a basic slot of the pattern
  set l₀ : Fin 4 := (A.mslot p).succAbove 0 with hl₀
  have hl₀ne : l₀ ≠ A.mslot p := Fin.succAbove_ne _ _
  have hB0 : ∀ᵐ y ∂MeasureTheory.volume, y ∈ dyadicGridCell A.G I.1 I.2 → A.B l₀ I y = 0 := by
    filter_upwards [bf.rep l₀ I hI, (bf.P l₀ 0).val_ae_zero_of_isEmpty (hPV l₀ 0) I,
      (bf.P l₀ 1).val_ae_zero_of_isEmpty (hPV l₀ 1) I] with y hy h0 h1 hyI
    rw [hy hyI, h0, h1]; simp
  have hcongr := localProgressionForm_congr_cell (A.adm I hI)
    (f := A.z (Fin.castSucc p) I) (g := Function.update (A.z (Fin.castSucc p) I) l₀ 0)
    (fun j => by
      by_cases hj : j = l₀
      · subst hj
        filter_upwards [hB0] with y hy hyI
        rw [Function.update_self, A.z_slot_basic p I hl₀ne, hy hyI]; rfl
      · exact Filter.Eventually.of_forall fun y _ => by rw [Function.update_of_ne hj])
  change localProgressionForm (dyadicGridLength A.G I.1) (A.w I) (A.z (Fin.castSucc p) I) = 0
  rw [hcongr]
  unfold localProgressionForm
  have : ∀ z : ℝ × ℝ, A.w I z * ∏ j, Function.update (A.z (Fin.castSucc p) I) l₀ 0 j
      (realProgressionCoordinate j z) = 0 := fun z => by
    rw [Finset.prod_eq_zero (Finset.mem_univ l₀) (by rw [Function.update_self]; rfl), mul_zero]
  simp only [this, MeasureTheory.integral_zero, mul_zero]

end ActiveSetup



end TrilinearHT.Auto
end
