/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.WitnessedArithmetic
import Mathlib.Tactic

/-! Untrusted exclusion hints with kernel-checked local arithmetic.
The producer chooses a method, fan, or split; soundness does not trust the search. -/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

namespace ConwaySoifer.Certificates

/-- A proposed exclusion proof; a split supplies its exact common denominator. -/
inductive ExclusionHint where
  | ordinary
  | diameter
  | pair (i j : Nat)
  | witnessedFan (witness : FanWitness)
  | fan (nodes : List IPoint)
  | split (a mid b den : Int) (left right : ExclusionHint)

/-- Verify a supplied hint without searching for fan directions or split points. -/
def ExclusionHint.check (Ps : List IPoint) (den : Int) (caps : List Cap)
    (ord : Option (Fin 6)) (fuel : Nat) : ExclusionHint → Int → Int → Int → Bool
  | .ordinary, a, b, d => ordinaryCheck Ps den ord a b d fuel
  | .diameter, a, b, d => diamCheck Ps den a b d fuel
  | .pair i j, a, b, d => pairCheck Ps den i j a b d fuel
  | .witnessedFan witness, a, b, d => witness.check Ps den caps a b d fuel eastP
  | .fan nodes, a, b, d => nodesOK Ps den caps (maxLen Ps) a b d fuel eastP nodes
  | .split aa mid bb dd left right, a, b, d =>
      decide (0 < dd) && decide (a * dd = aa * d) && decide (b * dd = bb * d) &&
        left.check Ps den caps ord fuel aa mid dd &&
        right.check Ps den caps ord fuel mid bb dd

/-- Every accepted hint excludes every geometric context on the whole input interval. -/
theorem ExclusionHint.sound (hint : ExclusionHint) {Ps : List IPoint} {den : Int}
    {caps : List Cap} {ord : Option (Fin 6)} {fuel : Nat} (hden : 0 < den) :
    ∀ (a b d : Int), 0 < d → hint.check Ps den caps ord fuel a b d = true →
      ∀ (U : EquilateralTriangle) (x : ℝ), 0 < x → (a : ℝ) / d ≤ x → x ≤ (b : ℝ) / d →
        Ctx U (den : ℝ) x Ps caps ord → False := by
  induction hint with
  | ordinary =>
    intro a b d hd h U x hx hlo hhi C
    exact ordinaryCheck_sound C rfl hden hd h hx hlo hhi
  | diameter =>
    intro a b d hd h U x hx hlo hhi C
    exact diamCheck_sound C rfl hden hd h hlo hhi
  | pair i j =>
    intro a b d hd h U x hx hlo hhi C
    exact pairCheck_sound C rfl hden hd h hlo hhi
  | witnessedFan witness =>
    intro a b d hd h U x hx hlo hhi C
    exact witness.rejects C rfl hden hd h hx hlo hhi
  | fan nodes =>
    intro a b d hd h U x hx hlo hhi C
    obtain ⟨O, hO1, hO2⟩ := U.exists_orientation_in_arc C.side_pos
    refine nodesOK_sound C rfl hden hd hx hlo hhi O ⟨hO1, hO2⟩ nodes eastP h ?_ ?_ ?_ hO2
    · rw [evalF_eastP]; simp [InArc, cross, eastDir, rot]
    · rw [evalF_eastP]; simp [eastDir]
    · rw [evalF_eastP]; exact hO1
  | split aa mid bb dd left right ihl ihr =>
    intro a b d hd h U x hx hlo hhi C
    simp only [ExclusionHint.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hdd, ha⟩, hb⟩, hl⟩, hr⟩ := h
    have hdR : (d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hd)
    have hddR : (dd : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hdd)
    have ea : (a : ℝ) / d = (aa : ℝ) / dd :=
      (div_eq_div_iff hdR hddR).mpr (by exact_mod_cast ha)
    have eb : (b : ℝ) / d = (bb : ℝ) / dd :=
      (div_eq_div_iff hdR hddR).mpr (by exact_mod_cast hb)
    rw [ea] at hlo
    rw [eb] at hhi
    by_cases hm : x ≤ (mid : ℝ) / dd
    · exact ihl aa mid dd hdd hl U x hx hlo hm C
    · exact ihr mid bb dd hdd hr U x hx (le_of_lt (lt_of_not_ge hm)) hhi C

end ConwaySoifer.Certificates
