/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Combining time-pairing moduli

The compactness lemma `lem:compactness` of the CKN manuscript asks for one modulus of the form
A * |t - s| + B * |t - s| ^ θ for all indices of a sequence. In the
blow-up limit (`prop:blowup-limit`) such moduli come with different exponents
for finitely many indices and for a tail. On a bounded time interval these
moduli combine into one of the same form.
-/

public section


open Set

noncomputable section

namespace ESS

/-- On [0, L], a higher Hölder power is dominated by a lower one up to a
constant factor. -/
theorem blowupLimitAssembly_rpow_le_max_mul_rpow
    {d L θ θ' : ℝ} (hd : 0 ≤ d) (hdL : d ≤ L) (hθ : 0 < θ)
    (hθθ' : θ ≤ θ') :
    d ^ θ' ≤ (max 1 L) ^ θ' * d ^ θ := by
  have hθ' : 0 < θ' := lt_of_lt_of_le hθ hθθ'
  have hmax : 1 ≤ max 1 L := le_max_left 1 L
  have hmaxpow : 1 ≤ (max 1 L) ^ θ' := Real.one_le_rpow hmax hθ'.le
  rcases le_total d 1 with hd1 | hd1
  · rcases hd.eq_or_lt with hd0 | hdpos
    · rw [← hd0, Real.zero_rpow hθ'.ne', Real.zero_rpow hθ.ne', mul_zero]
    · have hle : d ^ θ' ≤ d ^ θ :=
        Real.rpow_le_rpow_of_exponent_ge hdpos hd1 hθθ'
      have hnonneg : 0 ≤ d ^ θ := Real.rpow_nonneg hd θ
      calc
        d ^ θ' ≤ d ^ θ := hle
        _ = 1 * d ^ θ := (one_mul _).symm
        _ ≤ (max 1 L) ^ θ' * d ^ θ :=
          mul_le_mul_of_nonneg_right hmaxpow hnonneg
  · have hle : d ^ θ' ≤ (max 1 L) ^ θ' :=
      Real.rpow_le_rpow hd (hdL.trans (le_max_right 1 L)) hθ'.le
    have hone : 1 ≤ d ^ θ := Real.one_le_rpow hd1 hθ.le
    have hnonneg : 0 ≤ (max 1 L) ^ θ' := le_trans zero_le_one hmaxpow
    calc
      d ^ θ' ≤ (max 1 L) ^ θ' := hle
      _ = (max 1 L) ^ θ' * 1 := (mul_one _).symm
      _ ≤ (max 1 L) ^ θ' * d ^ θ :=
        mul_le_mul_of_nonneg_left hone hnonneg

/-- Two moduli of the form A * d + B * d ^ θ, each valid on a subset of
indices of a family of functions on a bounded interval, combine into one
modulus of the same form valid on the union. -/
theorem blowupLimitAssembly_modulus_or
    (g : ℕ → ℝ → ℝ) (a b : ℝ) (P Q : ℕ → Prop)
    (hP : ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, P n → s ∈ Icc a b → t ∈ Icc a b →
        |g n t - g n s| ≤ A * dist t s + B * (dist t s) ^ θ)
    (hQ : ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, Q n → s ∈ Icc a b → t ∈ Icc a b →
        |g n t - g n s| ≤ A * dist t s + B * (dist t s) ^ θ) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, (P n ∨ Q n) → s ∈ Icc a b → t ∈ Icc a b →
        |g n t - g n s| ≤ A * dist t s + B * (dist t s) ^ θ := by
  obtain ⟨A₁, B₁, θ₁, hA₁, hB₁, hθ₁, h₁⟩ := hP
  obtain ⟨A₂, B₂, θ₂, hA₂, hB₂, hθ₂, h₂⟩ := hQ
  let L : ℝ := b - a
  let θ : ℝ := min θ₁ θ₂
  have hθ : 0 < θ := lt_min hθ₁ hθ₂
  have hmax₁ : 0 ≤ (max 1 L) ^ θ₁ :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left 1 L)) θ₁
  have hmax₂ : 0 ≤ (max 1 L) ^ θ₂ :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left 1 L)) θ₂
  refine ⟨A₁ + A₂, B₁ * (max 1 L) ^ θ₁ + B₂ * (max 1 L) ^ θ₂, θ,
    add_nonneg hA₁ hA₂,
    add_nonneg (mul_nonneg hB₁ hmax₁) (mul_nonneg hB₂ hmax₂), hθ, ?_⟩
  intro n s t hn hs ht
  have hd : 0 ≤ dist t s := dist_nonneg
  have hdL : dist t s ≤ L := by
    rw [Real.dist_eq, abs_le]
    constructor
    · linarith only [hs.2, ht.1]
    · linarith only [hs.1, ht.2]
  have hpow₁ : (dist t s) ^ θ₁ ≤ (max 1 L) ^ θ₁ * (dist t s) ^ θ :=
    blowupLimitAssembly_rpow_le_max_mul_rpow hd hdL hθ (min_le_left θ₁ θ₂)
  have hpow₂ : (dist t s) ^ θ₂ ≤ (max 1 L) ^ θ₂ * (dist t s) ^ θ :=
    blowupLimitAssembly_rpow_le_max_mul_rpow hd hdL hθ (min_le_right θ₁ θ₂)
  have hθpow : 0 ≤ (dist t s) ^ θ := Real.rpow_nonneg hd θ
  have hA₁d : 0 ≤ A₁ * dist t s := mul_nonneg hA₁ hd
  have hA₂d : 0 ≤ A₂ * dist t s := mul_nonneg hA₂ hd
  have hB₁d : 0 ≤ B₁ * (max 1 L) ^ θ₁ * (dist t s) ^ θ :=
    mul_nonneg (mul_nonneg hB₁ hmax₁) hθpow
  have hB₂d : 0 ≤ B₂ * (max 1 L) ^ θ₂ * (dist t s) ^ θ :=
    mul_nonneg (mul_nonneg hB₂ hmax₂) hθpow
  rcases hn with hn | hn
  · have hbound := h₁ n s t hn hs ht
    have hB : B₁ * (dist t s) ^ θ₁ ≤
        B₁ * (max 1 L) ^ θ₁ * (dist t s) ^ θ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hpow₁ hB₁
    have hsum : A₁ * dist t s + B₁ * (dist t s) ^ θ₁ ≤
        (A₁ + A₂) * dist t s +
          (B₁ * (max 1 L) ^ θ₁ + B₂ * (max 1 L) ^ θ₂) * (dist t s) ^ θ := by
      rw [add_mul, add_mul]
      linarith only [hB, hA₂d, hB₂d]
    exact hbound.trans hsum
  · have hbound := h₂ n s t hn hs ht
    have hB : B₂ * (dist t s) ^ θ₂ ≤
        B₂ * (max 1 L) ^ θ₂ * (dist t s) ^ θ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hpow₂ hB₂
    have hsum : A₂ * dist t s + B₂ * (dist t s) ^ θ₂ ≤
        (A₁ + A₂) * dist t s +
          (B₁ * (max 1 L) ^ θ₁ + B₂ * (max 1 L) ^ θ₂) * (dist t s) ^ θ := by
      rw [add_mul, add_mul]
      linarith only [hB, hA₁d, hB₁d]
    exact hbound.trans hsum

/-- Finitely many individual moduli of the form A * d + B * d ^ θ on a
bounded interval combine into one. -/
theorem blowupLimitAssembly_modulus_le
    (g : ℕ → ℝ → ℝ) (a b : ℝ)
    (hone : ∀ n : ℕ, ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
        |g n t - g n s| ≤ A * dist t s + B * (dist t s) ^ θ)
    (j : ℕ) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, n ≤ j → s ∈ Icc a b → t ∈ Icc a b →
        |g n t - g n s| ≤ A * dist t s + B * (dist t s) ^ θ := by
  induction j with
  | zero =>
      obtain ⟨A, B, θ, hA, hB, hθ, h⟩ := hone 0
      refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
      intro n s t hn hs ht
      have hn0 : n = 0 := Nat.le_zero.mp hn
      subst hn0
      exact h s t hs ht
  | succ j ih =>
      have hsingle : ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
          ∀ n s t, n = j + 1 → s ∈ Icc a b → t ∈ Icc a b →
            |g n t - g n s| ≤ A * dist t s + B * (dist t s) ^ θ := by
        obtain ⟨A, B, θ, hA, hB, hθ, h⟩ := hone (j + 1)
        refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
        intro n s t hn hs ht
        subst hn
        exact h s t hs ht
      obtain ⟨A, B, θ, hA, hB, hθ, h⟩ :=
        blowupLimitAssembly_modulus_or g a b (fun n => n ≤ j)
          (fun n => n = j + 1) ih hsingle
      refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
      intro n s t hn hs ht
      apply h n s t _ hs ht
      rcases Nat.lt_or_ge n (j + 1) with hlt | hge
      · exact Or.inl (Nat.lt_succ_iff.mp hlt)
      · exact Or.inr (le_antisymm hn hge)

end ESS

end
