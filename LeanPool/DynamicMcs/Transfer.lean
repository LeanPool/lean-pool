/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

import Mathlib.Tactic.SplitIfs
public import LeanPool.DynamicMcs.Definitions
public import LeanPool.DynamicMcs.GreedySearch
public import LeanPool.DynamicMcs.EdgeUpdate
public import LeanPool.DynamicMcs.Exec
public import LeanPool.DynamicMcs.ExecFlip
public import LeanPool.DynamicMcs.BridgeAssembly

/-!
# Transport between the executable, specification, and proof models
development

`McsLean.ChallengeDefs` holds the definitions `DynamicMcs.lean` states its
theorems about.  The proofs live in the `Greedy` development, whose
definitions have identical bodies but are distinct constants.  This file
connects the two families with `_eq` / `_toDyn` lemmas.

The recursive greedy definitions (`mcsLoop`, `mcsRemainder`, `greedySuffix`)
are related by induction; `greedyPick` values agree definitionally because
both namespaces use the same explicit `mcsPick` construction.  The bounded
insertion probe `DynamicMcs.UGraph.firstBreakWindow` (which stops at the window
end) is related to the project's filtered full-suffix scan by
`firstBreakWindow_eq_scan`.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs

namespace UGraph

variable {n : ℕ}

/-- The scan's reported position is at least its starting position. -/
lemma firstBreakAux_ge (H : UGraph n) (order : List (Vert n)) :
    ∀ (k j : ℕ) (xs : List (Vert n)), firstBreakAux H order k xs = some j → k ≤ j := by
  intro k j xs
  induction xs generalizing k with
  | nil => simp [firstBreakAux]
  | cons x xs ih =>
      intro h
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · rw [firstBreakAux, ite_eq_left hx] at h
        have := ih (k + 1) h
        omega
      · rw [firstBreakAux, ite_eq_right hx] at h
        exact le_of_eq (Option.some.inj h)

/-- Scanning only the first `m` elements reports the same first break as the
full scan, provided that break lies among those `m` positions. -/
lemma firstBreakAux_take (H : UGraph n) (order : List (Vert n)) :
    ∀ (k m : ℕ) (xs : List (Vert n)),
      firstBreakAux H order k (xs.take m) =
        (firstBreakAux H order k xs).filter (fun j => decide (j < k + m)) := by
  intro k m xs
  induction xs generalizing k m with
  | nil => simp [firstBreakAux]
  | cons x xs ih =>
      cases m with
      | zero =>
          cases h : firstBreakAux H order k (x :: xs) with
          | none => simp [firstBreakAux]
          | some j =>
              have hkj := firstBreakAux_ge H order k j (x :: xs) h
              have hnot : ¬ j < k := by omega
              simp [firstBreakAux, Option.filter, hnot]
      | succ m =>
          by_cases hx : IsMCSNext H (order.take k).toFinset x
          · simp only [List.take_succ_cons, firstBreakAux, hx, ↓reduceIte]
            rw [ih, show k + (m + 1) = k + 1 + m by omega]
          · simp [List.take_succ_cons, firstBreakAux, Option.filter, hx]

/-- The bounded window probe equals the full-suffix scan filtered to the
window: stopping the scan at `k1` loses nothing. -/
theorem firstBreakWindow_eq_scan (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) :
    firstBreakWindow H order k0 k1 =
      (firstBreak H order k0).filter (fun j => decide (j ≤ k1)) := by
  unfold firstBreakWindow firstBreak
  rw [firstBreakAux_take]
  cases h : firstBreakAux H order k0 (order.drop k0) with
  | none => rfl
  | some j =>
      have := firstBreakAux_ge H order k0 j _ h
      simp only [Option.filter, decide_eq_true_eq]
      split_ifs <;> first | rfl | (exfalso; omega)

end UGraph

namespace Transport

open UGraph

/-- The greedy proof layer uses the same graph type as the specification. -/
def toDyn {n : ℕ} (G : UGraph n) : DynamicMcs.UGraph n :=
  G

/-- `greedyPick` values are definitionally equal across the namespaces. -/
lemma greedyPick_val {n} (G : UGraph n) (chosen : Finset (Vert n))
    (h h' : chosen ≠ (Finset.univ : Finset (Vert n))) :
    (greedyPick G chosen h).1 = (DynamicMcs.UGraph.greedyPick (toDyn G) chosen h').1 := by
  rfl

/-- `mcsLoop` computes the same continuation through either namespace. -/
lemma mcsLoop_eq (n : ℕ) (G : UGraph n) (chosen : Finset (Vert n)) (k : ℕ)
    (hk : chosen.card + k = n) (hk' : chosen.card + k = n) :
    UGraph.mcsLoop G chosen k hk = DynamicMcs.UGraph.mcsLoop (toDyn G) chosen k hk' := rfl

/-- `mcsRemainder` computes equal lists across the namespaces. -/
lemma mcsRemainder_eq (n : ℕ) (G : UGraph n) (chosen : Finset (Vert n)) :
    UGraph.mcsRemainder G chosen = DynamicMcs.UGraph.mcsRemainder (toDyn G) chosen := rfl

/-- `greedySuffix` computes equal lists across the namespaces. -/
lemma greedySuffix_eq {n : ℕ} (G : UGraph n) (pref : List (Vert n)) :
    UGraph.greedySuffix G pref = DynamicMcs.UGraph.greedySuffix (toDyn G) pref := rfl

/-- `IsMCSNext` is invariant under the structure transport `toDyn`. -/
lemma IsMCSNext_toDyn {n} (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) :
    IsMCSNext G chosen w ↔ DynamicMcs.UGraph.IsMCSNext (toDyn G) chosen w := Iff.rfl

/-- `IsMCSOrdering` is invariant under `toDyn`. -/
lemma IsMCSOrdering_toDyn {n} (G : UGraph n) (order : List (Vert n)) :
    IsMCSOrdering G order ↔ DynamicMcs.UGraph.IsMCSOrdering (toDyn G) order := Iff.rfl

/-- `FlipOf` is invariant under `toDyn`. -/
lemma FlipOf_toDyn {n} (G G' : UGraph n) (u v : Vert n) :
    FlipOf G G' u v ↔ DynamicMcs.UGraph.FlipOf (toDyn G) (toDyn G') u v := Iff.rfl

/-- `laterPos` is invariant. -/
lemma laterPos_eq (order : List (Vert n)) (u v : Vert n) :
    laterPos order u v = Greedy.Update.laterPos order u v := by
  unfold laterPos Greedy.Update.laterPos
  rfl

/-- `laterVert` is invariant. -/
lemma laterVert_eq (order : List (Vert n)) (u v : Vert n) :
    laterVert order u v = Greedy.Update.laterVert order u v := by
  unfold laterVert Greedy.Update.laterVert
  rfl

/-- `firstBreakAux` computes equal options across the namespaces. -/
lemma firstBreakAux_eq (H : UGraph n) (order : List (Vert n)) :
    ∀ (k : ℕ) (xs : List (Vert n)),
      firstBreakAux H order k xs = Greedy.Update.firstBreakAux (toDyn H) order k xs := by
  intro k xs
  induction xs generalizing k with
  | nil =>
      rw [firstBreakAux, Greedy.Update.firstBreakAux]
  | cons x xs ih =>
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · have hxD : DynamicMcs.UGraph.IsMCSNext (toDyn H) (order.take k).toFinset x :=
          (IsMCSNext_toDyn H (order.take k).toFinset x).mpr hx
        rw [firstBreakAux, Greedy.Update.firstBreakAux, ite_eq_left hx, ite_eq_left hxD]
        exact ih (k + 1)
      · have hxD : ¬ DynamicMcs.UGraph.IsMCSNext (toDyn H) (order.take k).toFinset x := by
          intro h
          exact hx ((IsMCSNext_toDyn H (order.take k).toFinset x).mp h)
        rw [firstBreakAux, Greedy.Update.firstBreakAux, ite_eq_right hx, ite_eq_right hxD]

/-- `firstBreak` computes equal options across the namespaces. -/
lemma firstBreak_eq (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) :
    firstBreak H order k0 = Greedy.Update.firstBreak (toDyn H) order k0 := by
  unfold firstBreak Greedy.Update.firstBreak
  exact firstBreakAux_eq H order k0 (order.drop k0)

/-- The deletion probe computes equal booleans across the namespaces. -/
lemma deletionBreaks_eq (H : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    deletionBreaks H order u v = Greedy.Update.deletionBreaks (toDyn H) order u v := by
  unfold deletionBreaks Greedy.Update.deletionBreaks UGraph.isFalse Greedy.Update.isFalse
  rw [← laterPos_eq, ← laterVert_eq]
  by_cases h : IsMCSNext H (order.take (laterPos order u v)).toFinset (laterVert order u v)
  · rw [ite_eq_left h, ite_eq_left ((IsMCSNext_toDyn _ _ _).1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((IsMCSNext_toDyn _ _ _).2 h'))]

/-- The bounded window probe transports to the project's filtered scan. -/
lemma firstBreakWindow_eq (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) :
    firstBreakWindow H order k0 k1 =
      Greedy.Update.firstBreakWindow (toDyn H) order k0 k1 := by
  rw [firstBreakWindow_eq_scan, firstBreak_eq]
  unfold Greedy.Update.firstBreakWindow
  cases Greedy.Update.firstBreak (toDyn H) order k0 with
  | none => rfl
  | some j =>
      by_cases hj : j ≤ k1 <;> simp [Option.filter, hj]

/-- `initOrder` computes equal lists across the namespaces. -/
lemma initOrder_eq (G : UGraph n) :
    initOrder G = Greedy.Update.initOrder (toDyn G) := by
  unfold initOrder Greedy.Update.initOrder
  exact greedySuffix_eq G []

end Transport
end DynamicMcs
