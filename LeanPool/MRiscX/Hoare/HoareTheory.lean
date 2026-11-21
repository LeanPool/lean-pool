/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
module

public import LeanPool.MRiscX.Hoare.HoareCore
public import Mathlib.Data.Nat.Notation
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide.Normalize.Prop

/-!
This file contains some minor lemmas to ease the prove in the "main" file "HoareRules".
Also, those lemmas can be used to deepen the understanding of the weak function.
-/

@[expose] public section

theorem weak_with_less_BL_weakens : ∀ (s s' : MState) (L_w L_b L : Set UInt64) (c : Code),
  weak s s' L_w L_b c →
  weak s s' L_w (L_b \ L) c
  := by
  intros s s' L_w L_b L c
  unfold weak
  intro H HCode
  specialize H HCode
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.mem_union, = Set.mem_sdiff]


theorem weak_L_w_with_L_from_L_b : ∀ (s s' : MState) (L_w L_b L : Set UInt64) (c : Code),
  L ⊆ L_b →
  weak s s' L_w L_b c →
  weak s s' (L_w ∪ L) (L_b \ L) c
  := by
  intros s s' L_w L_b L c T
  unfold weak
  intro H HCode
  specialize H HCode
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.subset_def, = Set.mem_union, = Set.mem_sdiff]
