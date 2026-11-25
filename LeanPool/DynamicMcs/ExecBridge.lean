/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec
public import LeanPool.DynamicMcs.GreedySearch

/-!
# Executable `bestPick` selection helper

Defines the `better` selection relation used inside `Exec.bestPick` and proves
it is definitionally the `bestPick` foldl lambda. The executable/abstract
equivalence `mcsOrder_eq_greedySuffix` (the bridge this file originally planned)
is now proved in `McsLean/BridgeAssembly.lean`, assembled from
`CardBridge.lean` and `BridgeParts{A,B,C}.lean`; the helper lemmas below the
`PLANNED` block were completed there. This file is `sorry`/`axiom`-free.
-/

@[expose] public section

open DynamicMcs.Greedy

namespace DynamicMcs

namespace ExecBridge

/-- The `bestPick` selection: better of `a0` and `v` under the lex order
(cardC desc, then id asc). Mirrors the lambda inside `Exec.bestPick`. -/
def better (a : Adj n) (chosen : List ℕ) (a0 v : ℕ) : ℕ :=
  if Exec.cardC a chosen v > Exec.cardC a chosen a0
    ∨ (Exec.cardC a chosen v = Exec.cardC a chosen a0 ∧ v < a0)
  then v else a0

/-- `better` is definitionally the same as `Exec.bestPick`'s foldl lambda. -/
lemma better_eq_bestPick_lambda (a : Adj n) (chosen : List ℕ) (best v : ℕ) :
    (fun b v =>
      let cb := Exec.cardC a chosen b
      let cv := Exec.cardC a chosen v
      if cv > cb ∨ (cv = cb ∧ v < b) then v else b) best v
    = better a chosen best v := by
  rfl

-- PLANNED THEOREMS (documented; proofs to be completed):
--
--   lemma better_lex_two (a : Adj n) (chosen acc v : ℕ) :
--       let acc' := better a chosen acc v
--       Exec.cardC a chosen acc' ≥ Exec.cardC a chosen acc ∧
--       Exec.cardC a chosen acc' ≥ Exec.cardC a chosen v ∧
--       (Exec.cardC a chosen v = Exec.cardC a chosen acc' → acc' ≤ acc) ∧
--       (Exec.cardC a chosen acc = Exec.cardC a chosen acc' → acc' ≤ v)
--
--   lemma bestPick_foldl_lex (a : Adj n) (chosen : List ℕ) :
--       ∀ (l : List ℕ) (acc : ℕ),
--         (∀ x ∈ l, Exec.cardC a chosen x ≤ Exec.cardC a chosen acc) →
--         (∀ x ∈ l, Exec.cardC a chosen x = Exec.cardC a chosen acc → acc ≤ x) →
--         let acc' := l.foldl (fun b v =>
--           let cb := Exec.cardC a chosen b
--           let cv := Exec.cardC a chosen v
--           if cv > cb ∨ (cv = cb ∧ v < b) then v else b) acc
--         (∀ x ∈ l, Exec.cardC a chosen x ≤ Exec.cardC a chosen acc') ∧
--         (∀ x ∈ l, Exec.cardC a chosen x = Exec.cardC a chosen acc' → acc' ≤ x)
--
--   lemma bestPick_lex (a : Adj n) (chosen rem : List ℕ) (hrem_ne : rem ≠ []) :
--       let w := Exec.bestPick a chosen rem
--       w ∈ rem ∧
--       (∀ x ∈ rem, Exec.cardC a chosen x ≤ Exec.cardC a chosen w) ∧
--       (∀ x ∈ rem, Exec.cardC a chosen x = Exec.cardC a chosen w → w ≤ x)
--
--   lemma cardC_eq_neigh (a : Adj n) (hsymm : ∀ u v : ℕ, Exec.getAdj a u v = Exec.getAdj a v u)
--       (chosen : List ℕ) (w : ℕ) (hw : w < a.length) :
--       let G := Exec.toUGraph a hsymm (fun u => …)
--       Greedy.UGraph.neigh G (chosen.map ⟨·, …⟩).toFinset ⟨w, hw⟩
--       = Exec.cardC a chosen w
--
--   lemma mcsStep_preserves_legal (…) : each `mcsStep` pick satisfies
--       `Greedy.UGraph.IsMCSNext` at the corresponding prefix.
--
--   theorem mcsOrder_eq_greedySuffix
--       (a : Adj n)
--       (hsymm : ∀ u v : ℕ, Exec.getAdj a u v = Exec.getAdj a v u)
--       (hloop : ∀ u : ℕ, Exec.getAdj a u u = false) :
--       let G := Exec.toUGraph a hsymm hloop
--       ∃ (ord : List (Greedy.Vert n)),
--         Greedy.UGraph.IsMCSOrdering G ord ∧
--         ord.map (fun v => v.val) = Exec.mcsOrder a

end ExecBridge
end DynamicMcs
