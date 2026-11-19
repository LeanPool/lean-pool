/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingAgreement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingForcing
public import LeanPool.TuringConeRigidity.Representation.CommonIdealSearch

/-!
# Coding Agreement
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingAgreement
open CodingForcing

/-- The two finite oracle computations return different values on some common input. -/
def Disagreement (Y : Oracle) (e₀ e₁ : OracleCode) (p : Condition) : Prop :=
  ∃ n a b, a ≠ b ∧ a ∈ CommonIdeal.run Y e₀ p.left n ∧ b ∈ CommonIdeal.run Y e₁ p.right n

/-- No permitted extension of the condition produces a disagreement between the two
computations. -/
def NoDisagreement (A : ℕ → Oracle) (Y : Oracle) (e₀ e₁ : OracleCode) (p : Condition) : Prop :=
  ∀ q, Extends A p q → ¬ Disagreement Y e₀ e₁ q

theorem disagreement_mono {A : ℕ → Oracle} {Y : Oracle} {e₀ e₁ : OracleCode}
    {p q : Condition} (h : Extends A p q) (hd : Disagreement Y e₀ e₁ p) :
    Disagreement Y e₀ e₁ q := by
  obtain ⟨n, a, b, hab, ha, hb⟩ := hd
  exact ⟨n, a, b, hab, CommonIdeal.run_mono h.1 n a ha, CommonIdeal.run_mono h.2.1 n b hb⟩

theorem disagreement_decision_dense (A : ℕ → Oracle) (Y : Oracle) (e₀ e₁ : OracleCode)
    (p : Condition) :
    ∃ q, Extends A p q ∧ (Disagreement Y e₀ e₁ q ∨ NoDisagreement A Y e₀ e₁ q) := by
  by_cases h : ∃ q, Extends A p q ∧ Disagreement Y e₀ e₁ q
  · obtain ⟨q, hpq, hd⟩ := h
    exact ⟨q, hpq, Or.inl hd⟩
  · exact ⟨p, extends_refl A p, Or.inr (fun q hpq hd => h ⟨q, hpq, hd⟩)⟩

theorem noDisagreement_of_common_output {A : ℕ → Oracle} {Y G₀ G₁ Z : Oracle}
    {e₀ e₁ : OracleCode} {p : Condition}
    (h₀ : CommonIdeal.Extends G₀ p.left) (h₁ : CommonIdeal.Extends G₁ p.right)
    (he₀ : OracleCode.eval (oracleFunction (join Y G₀)) e₀ = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y G₁)) e₁ = oracleFunction Z)
    (h : Disagreement Y e₀ e₁ p ∨ NoDisagreement A Y e₀ e₁ p) :
    NoDisagreement A Y e₀ e₁ p := by
  rcases h with hd | hn
  · obtain ⟨n, a, b, hab, ha, hb⟩ := hd
    have hta := CommonIdeal.run_total h₀ n a ha
    have htb := CommonIdeal.run_total h₁ n b hb
    rw [he₀] at hta
    rw [he₁] at htb
    exact False.elim (hab (Part.mem_unique hta htb))
  · exact hn

/-- Whenever the left computation converges on a fixed input along two permitted extensions,
its outputs agree. -/
def UniqueValues (A : ℕ → Oracle) (Y : Oracle) (e : OracleCode) (p : Condition) : Prop :=
  ∀ q r, Extends A p q → Extends A p r → ∀ n a b,
    a ∈ CommonIdeal.run Y e q.left n → b ∈ CommonIdeal.run Y e r.left n → a = b

theorem unique_search_sound {A : ℕ → Oracle} {Y G Z : Oracle} {e : OracleCode}
    {p : Condition} (hu : UniqueValues A Y e p) (hG : CommonIdeal.Extends G p.left)
    (he : OracleCode.eval (oracleFunction (join Y G)) e = oracleFunction Z)
    (w : List Bool) (n a : ℕ) (ha : a ∈ CommonIdeal.run Y e (p.left ++ w) n) :
    a = CommonIdeal.bit (Z n) := by
  obtain ⟨q, hpq, hq⟩ := arbitrary_left_extension A p (p.left ++ w) (List.prefix_append _ _)
  obtain ⟨s, hs, hb⟩ := CommonIdeal.run_finite_extension hG n (CommonIdeal.bit (Z n)) (by
    rw [he]
    exact Part.mem_some _)
  obtain ⟨r, hpr, hr⟩ := arbitrary_left_extension A p s hs
  exact hu q r hpq hpr n a (CommonIdeal.bit (Z n)) (hq ▸ ha) (hr ▸ hb)

theorem case1_reduces {A : ℕ → Oracle} {Y G Z : Oracle} {e : OracleCode} {p : Condition}
    (hu : UniqueValues A Y e p) (hG : CommonIdeal.Extends G p.left)
    (he : OracleCode.eval (oracleFunction (join Y G)) e = oracleFunction Z) : Reduces Z Y := by
  obtain ⟨d, hd⟩ := CommonIdeal.finiteRun_code e p.left
  apply RecursiveIn.iff_nat.mpr
  apply UniformOracle.total_search (CommonIdeal.searchTrial_recursive Y d) (fun n =>
    CommonIdeal.bit (Z n))
  · intro n z a ha
    have hf := Nat.Partrec.Code.evaln_sound ha
    rw [hd] at hf
    have hr := (CommonIdeal.finiteRun_approximates Y e p.left
      (Nat.unpair (Nat.unpair z).2).1 n).1 (Nat.unpair z).1 a hf
    exact unique_search_sound hu hG he _ n a hr
  · intro n
    obtain ⟨w, a, ha⟩ := CommonIdeal.agreeing_search_complete hG he n
    obtain ⟨wcode, hw⟩ := BorelGeneric.word_surjective w
    rw [← hw] at ha
    obtain ⟨m, hm⟩ := (CommonIdeal.finiteRun_approximates Y e p.left wcode n).2 a ha
    have hf := hm m le_rfl
    dsimp only at hf
    rw [← hd] at hf
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hf
    exact ⟨Nat.pair m (Nat.pair wcode t), a, by simpa [CommonIdeal.searchTrial] using ht⟩

end TuringRigidity.CodingAgreement

end OAI
