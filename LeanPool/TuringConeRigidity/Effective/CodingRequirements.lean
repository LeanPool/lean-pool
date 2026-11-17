/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingExtraction

/-!
# Coding Requirements
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingRequirements
open CodingForcing CodingAgreement CodingLocations CodingExtraction

def Good (A : ℕ → Oracle) (Y : Oracle) (e₀ e₁ : OracleCode) (p : Condition) : Prop :=
  Disagreement Y e₀ e₁ p ∨
    (∃ n, ∀ q, Extends A p q → ∀ v, v ∉ CommonIdeal.run Y e₀ q.left n) ∨
    (∃ n, ∀ q, Extends A p q → ∀ v, v ∉ CommonIdeal.run Y e₁ q.right n) ∨
    UniqueValues A Y e₀ p ∨ ∃ k, Reduces (A k) Y

theorem good_dense (A : ℕ → Oracle)
    (hIntro : ∀ k Z, (∀ a, Z a = true → A k a = true) →
      {a | Z a = true}.Infinite → Reduces (A k) Z)
    (Y : Oracle) (e₀ e₁ : OracleCode) (p : Condition) :
    ∃ q, Extends A p q ∧ Good A Y e₀ e₁ q := by
  obtain ⟨q, hpq, hd | hn⟩ := disagreement_decision_dense A Y e₀ e₁ p
  · exact ⟨q, hpq, Or.inl hd⟩
  · by_cases hl : ∃ r, Extends A q r ∧ ∃ n, ∀ s, Extends A r s → ∀ v, v ∉ CommonIdeal.run Y e₀
      s.left n
    · obtain ⟨r, hqr, hdiv⟩ := hl
      exact ⟨r, extends_trans hpq hqr, Or.inr (Or.inl hdiv)⟩
    · by_cases hr : ∃ r, Extends A q r ∧ ∃ n, ∀ s, Extends A r s → ∀ v, v ∉ CommonIdeal.run Y e₁
        s.right n
      · obtain ⟨r, hqr, hdiv⟩ := hr
        exact ⟨r, extends_trans hpq hqr, Or.inr (Or.inr (Or.inl hdiv))⟩
      · by_cases hu : ∃ r, Extends A q r ∧ UniqueValues A Y e₀ r
        · obtain ⟨r, hqr, hu⟩ := hu
          exact ⟨r, extends_trans hpq hqr, Or.inr (Or.inr (Or.inr (Or.inl hu)))⟩
        · have hL : DenseLeft A Y e₀ q := by
            intro r hqr n
            by_contra h
            push Not at h
            exact hl ⟨r, hqr, n, fun s hrs v => h s v hrs⟩
          have hR : DenseRight A Y e₁ q := by
            intro r hqr n
            by_contra h
            push Not at h
            exact hr ⟨r, hqr, n, fun s hrs v => h s v hrs⟩
          have hU : ∀ r, Extends A q r → ¬ UniqueValues A Y e₀ r :=
            fun r hqr huni => hu ⟨r, hqr, huni⟩
          obtain ⟨k, _, hk⟩ := case2_computes_member hIntro hn hL hR hU
          exact ⟨q, hpq, Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk⟩)))⟩

theorem arbitrary_right_extension (A : ℕ → Oracle) (p : Condition)
    (s : List Bool) (hs : p.right <+: s) : ∃ q, Extends A p q ∧ q.right = s := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨append p u, append_extends A p u, rfl⟩

theorem good_common_output {A : ℕ → Oracle} {Y G₀ G₁ Z : Oracle}
    {e₀ e₁ : OracleCode} {p : Condition}
    (h₀ : CommonIdeal.Extends G₀ p.left) (h₁ : CommonIdeal.Extends G₁ p.right)
    (he₀ : OracleCode.eval (oracleFunction (join Y G₀)) e₀ = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y G₁)) e₁ = oracleFunction Z)
    (h : Good A Y e₀ e₁ p) : Reduces Z Y ∨ ∃ k, Reduces (A k) Y := by
  rcases h with hd | hl | hr | hu | ha
  · obtain ⟨n, a, b, hab, hva, hvb⟩ := hd
    have hta := CommonIdeal.run_total h₀ n a hva
    have htb := CommonIdeal.run_total h₁ n b hvb
    rw [he₀] at hta
    rw [he₁] at htb
    exact False.elim (hab (Part.mem_unique hta htb))
  · obtain ⟨n, hn⟩ := hl
    obtain ⟨s, hs, hv⟩ := CommonIdeal.run_finite_extension h₀ n (CommonIdeal.bit (Z n)) (by
      rw [he₀]; exact Part.mem_some _)
    obtain ⟨q, hpq, hq⟩ := arbitrary_left_extension A p s hs
    exact False.elim (hn q hpq _ (hq ▸ hv))
  · obtain ⟨n, hn⟩ := hr
    obtain ⟨s, hs, hv⟩ := CommonIdeal.run_finite_extension h₁ n (CommonIdeal.bit (Z n)) (by
      rw [he₁]; exact Part.mem_some _)
    obtain ⟨q, hpq, hq⟩ := arbitrary_right_extension A p s hs
    exact False.elim (hn q hpq _ (hq ▸ hv))
  · exact Or.inl (case1_reduces hu h₀ he₀)
  · exact Or.inr ha

def GoodForCode (A : ℕ → Oracle) (B : Oracle) (c e₀ e₁ : OracleCode) (p : Condition) : Prop :=
  ∀ Y : Oracle, OracleCode.eval (oracleFunction B) c = oracleFunction Y → Good A Y e₀ e₁ p

theorem goodForCode_dense (A : ℕ → Oracle)
    (hIntro : ∀ k Z, (∀ a, Z a = true → A k a = true) →
      {a | Z a = true}.Infinite → Reduces (A k) Z)
    (B : Oracle) (c e₀ e₁ : OracleCode) (p : Condition) :
    ∃ q, Extends A p q ∧ GoodForCode A B c e₀ e₁ q := by
  by_cases h : ∃ Y : Oracle, OracleCode.eval (oracleFunction B) c = oracleFunction Y
  · obtain ⟨Y, hY⟩ := h
    obtain ⟨q, hpq, hg⟩ := good_dense A hIntro Y e₀ e₁ p
    refine ⟨q, hpq, ?_⟩
    intro Z hZ
    have he : Y = Z := oracleFunction_injective (hY.symm.trans hZ)
    exact he ▸ hg
  · exact ⟨p, extends_refl A p, fun Y hY => False.elim (h ⟨Y, hY⟩)⟩

end TuringRigidity.CodingRequirements

end OAI
