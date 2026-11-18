/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingLocations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingSplitting
public import LeanPool.TuringConeRigidity.Effective.CodingOnePoint

/-!
# Coding Locations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingLocations
open CodingForcing CodingAgreement CodingOnePoint CodingSplitting

/-- Below each permitted extension, every input has a further extension on which the left
computation halts. -/
def DenseLeft (A : ℕ → Oracle) (Y : Oracle) (e : OracleCode) (p : Condition) : Prop :=
  ∀ q, Extends A p q → ∀ n, ∃ r v, Extends A q r ∧ v ∈ CommonIdeal.run Y e r.left n

/-- Below each permitted extension, every input has a further extension on which the right
computation halts. -/
def DenseRight (A : ℕ → Oracle) (Y : Oracle) (e : OracleCode) (p : Condition) : Prop :=
  ∀ q, Extends A p q → ∀ n, ∃ r v, Extends A q r ∧ v ∈ CommonIdeal.run Y e r.right n

/-- Changing one bit in an extended word changes a computed output. -/
def SplittingLocation (Y : Oracle) (e : OracleCode) (base : List Bool) (m : ℕ) : Prop :=
  ∃ s b n v w, base <+: s ∧ base.length ≤ m ∧ m < s.length ∧ v ≠ w ∧
    v ∈ CommonIdeal.run Y e s n ∧ w ∈ CommonIdeal.run Y e (s.set m b) n

theorem splittingLocation_sound {A : ℕ → Oracle} {Y : Oracle} {e₀ e₁ : OracleCode}
    {p : Condition} (hn : NoDisagreement A Y e₀ e₁ p) (hR : DenseRight A Y e₁ p)
    {m : ℕ} (hm : SplittingLocation Y e₀ p.left m) : CodingLocation A p m := by
  obtain ⟨s, b, n, v, w, hs, hmp, hms, hvw, hv, hw⟩ := hm
  obtain ⟨r, hpr, hr⟩ := arbitrary_left_extension A p s hs
  have hms' : m < r.left.length := by simpa only [hr] using hms
  rcases split_coding_or_divergence hn hpr m hmp hms' b n v w hvw
      (hr ▸ hv) (hr ▸ hw) with hc | hd
  · exact hc
  · obtain ⟨q, c, hrq, hc⟩ := hR r hpr n
    exact False.elim (hd q hrq c hc)

theorem splittingLocation_unbounded {A : ℕ → Oracle} {Y : Oracle} {e : OracleCode}
    {p : Condition} (hL : DenseLeft A Y e p)
    (hU : ∀ q, Extends A p q → ¬ UniqueValues A Y e q) (N : ℕ) :
    ∃ m, N ≤ m ∧ SplittingLocation Y e p.left m := by
  obtain ⟨q, hpq, hNq⟩ := length_dense A p N
  have hu := hU q hpq
  simp only [UniqueValues] at hu
  push Not at hu
  obtain ⟨r, s, hqr, hqs, n, a, b, ha, hb, hab⟩ := hu
  rcases split_or_divergent_word hqr.1 hqs.1 n a b ha hb hab with hsplit | hdiv
  · obtain ⟨w, m, c, v, z, hqw, hqm, hmw, hvz, hv, hz⟩ := hsplit
    exact ⟨m, hNq.trans hqm, w, c, n, v, z, hpq.1.trans hqw,
      hpq.1.length_le.trans hqm, hmw, hvz, hv, hz⟩
  · obtain ⟨w, hqw, hd⟩ := hdiv
    obtain ⟨t, hqt, ht⟩ := arbitrary_left_extension A q w hqw
    obtain ⟨u, v, htu, hv⟩ := hL t (extends_trans hpq hqt) n
    have hwu : w <+: u.left := by simpa only [ht] using htu.1
    obtain ⟨extra, hleft⟩ := hwu
    exact False.elim (hd extra v (hleft ▸ hv))

theorem splittingLocations_infinite {A : ℕ → Oracle} {Y : Oracle} {e : OracleCode}
    {p : Condition} (hL : DenseLeft A Y e p)
    (hU : ∀ q, Extends A p q → ¬ UniqueValues A Y e q) :
    {m | SplittingLocation Y e p.left m}.Infinite := by
  intro hf
  have hb := hf.bddAbove
  obtain ⟨b, hb⟩ := hb
  obtain ⟨m, hm, hs⟩ := splittingLocation_unbounded hL hU (b+1)
  have hmb := hb hs
  omega

end TuringRigidity.CodingLocations

end OAI
