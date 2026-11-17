/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/TriplePrefix.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericSourceTransfer

/-!
# Triple Prefix
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.TriplePrefix
open FiniteShuffle ShuffleRequirements PairGenericSelection

theorem join_agree {n : ℕ} {A A' B B' : Oracle}
    (ha : Agree n A A') (hb : Agree n B B') : Agree n (join A B) (join A' B') := by
  intro i hi
  simp only [join]
  split
  · exact hb (i / 2) (by omega)
  · exact ha (i / 2) (by omega)

theorem join_columns (H : Oracle) : join (column false H) (column true H) = H := by
  funext i
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have he : i = 2 * (i / 2) := by omega
    rw [he,join_even]
    rfl
  · have he : i = 2 * (i / 2) + 1 := by omega
    rw [he,join_odd]
    rfl

def prefixes (s : List Bool) : List Bool × List Bool × List Bool :=
  let H : Oracle := fun i => s.getD i false
  (initial (column false H) s.length,
    initial (column false (column true H)) s.length,
    initial (column true (column true H)) s.length)

theorem realizes_join {s : List Bool} {Y L R : Oracle}
    (hY : Realizes (prefixes s).1 Y)
    (hL : Realizes (prefixes s).2.1 L)
    (hR : Realizes (prefixes s).2.2 R) : Realizes s (join Y (join L R)) := by
  let H : Oracle := fun i => s.getD i false
  have hYa : Agree s.length (column false H) Y := (realizes_initial _ _ _).mp hY
  have hLa : Agree s.length (column false (column true H)) L := (realizes_initial _ _ _).mp hL
  have hRa : Agree s.length (column true (column true H)) R := (realizes_initial _ _ _).mp hR
  have h := join_agree hYa (join_agree hLa hRa)
  rw [join_columns,join_columns] at h
  exact h

end TuringRigidity.TriplePrefix

end OAI
