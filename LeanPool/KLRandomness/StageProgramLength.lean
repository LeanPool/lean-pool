/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineProgramLength

/-!
# Short descriptions for the complete fixed-stage program

The variable input is the nested pair of a trial rank, a candidate index
below `r^24`, and bounded horizon advice. The bound on the horizon advice
is fixed before the trial rank. Its binary size therefore contributes only
to the constant term, while the candidate index contributes a multiple of
the rank's binary size.
-/

@[expose] public section

namespace Klr.StageProgramLength

open Filter AffineDescription AffineProgramLength

/-- Exact encoding-size estimate for the three variable stage parameters. -/
theorem size_input_le (B r q b : ℕ) (hq : q < r ^ 24) (hb : b ≤ B) :
    Nat.size (Nat.pair r (Nat.pair q b)) ≤
      96 * Nat.size r + 4 * Nat.size B + 4 := by
  have hqsize := (Nat.size_le_size hq.le).trans (size_pow_le r 24)
  have hbsize := Nat.size_le_size hb
  have hinner := size_pair_le q b
  have hmax : max (Nat.size q) (Nat.size b) ≤
      24 * Nat.size r + Nat.size B + 1 := max_le (by omega) (by omega)
  have hinner' : Nat.size (Nat.pair q b) ≤
      48 * Nat.size r + 2 * Nat.size B + 2 := by omega
  have houter := size_pair_le r (Nat.pair q b)
  have hmax' : max (Nat.size r) (Nat.size (Nat.pair q b)) ≤
      48 * Nat.size r + 2 * Nat.size B + 2 := max_le (by omega) hinner'
  omega

/-- One fixed reconstruction program eventually has enough rank to pay
for every possible candidate index and every bounded horizon advice value. -/
theorem eventually_programFor_stage_budget (e : Nat.Partrec.Code) (B level : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ q b : ℕ, q < r ^ 24 → b ≤ B →
      2 * (programFor e (Nat.pair r (Nat.pair q b))).length + level + 1 ≤ r := by
  filter_upwards [eventually_programFor_length_budget e 96 (4 * Nat.size B + 4) level]
    with r hr
  intro q b hq hb
  exact hr _ (by simpa [Nat.add_assoc] using size_input_le B r q b hq hb)

end Klr.StageProgramLength
