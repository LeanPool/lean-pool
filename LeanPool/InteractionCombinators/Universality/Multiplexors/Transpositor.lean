/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Multiplexors.AutoMux
public import Mathlib.Tactic.TypeStar

/-!
# Lafont, "Interaction Combinators" (1997): the transpositor `T_{p,q}`

Page 83 (PDF page 15). For `p, q ∈ ℕ`, the transpositor `T_{p,q}` is a principal net of arity
`2p + q` such that two copies plugged by their roots reduce to the wiring `ι_{p,q}`, the involutive
permutation of `{1, …, 2p + q}` that exchanges 1 with 2, 3 with 4, …, `2p - 1` with `2p`, and fixes
the last `q` ports. The figure implements it as the autodual multiplexor `T_{p+q}` whose first `p`
auxiliary ports each carry a `con` cell with two free auxiliary ports, the last `q` ports being
free. The rules used are `dup`–`dup` and `era`–`era` (inside `T_{p+q}`) and `con`–`con`, which
exchanges the auxiliary ports: this exchange is the transposition (`dup` would not do, since
`dup`–`dup` does not exchange).

Contents, in the order of the file:

1. Definitions: `pairCon`, which groups the first `2p` trees in pairs under a `con` each;
   `transpositor`, the net `T_{p,q}`; `swapPairs`, the permutation `ι_{p,q}` on lists.
2. Auxiliary lemmas: `length_pairCon_eq`, `swapPairs_swapPairs` (`ι_{p,q}` is an involution),
   `vars_transpositor` (the names of `T_{p,q}`), and `pairCon_red`, the `con`–`con` steps that
   turn facing pairs of `con` cells into `ι_{p,q}`.
3. Main result: `transpositor_transpositor`, the property of page 83.
4. Examples: `transpositor_one_one`, the net `T_{1,1}`, and the picture of page 83 for
   `p = q = 1`.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- Group the first `2p` trees in pairs under a `con` each (the `γ` cells on the first `p`
auxiliary ports of `T_{p+q}` in the figure of page 83): the trees on ports `2i - 1` and `2i` become
the left and right auxiliary ports of the `i`-th `con`. If fewer than `2p` trees are given, the
last odd tree is left alone. -/
def pairCon :
    -- the number `p` of pairs
    ℕ →
    -- the trees, in order
    List (Term sig ℕ) →
    List (Term sig ℕ)
  | 0, ts => ts
  | p + 1, t :: t' :: ts => mkCon t t' :: pairCon p ts
  | _ + 1, ts => ts

/-- The transpositor `T_{p,q}` (Lafont, page 83), applied to the trees plugged into its `2p + q`
ports, numbered from left to right: the autodual multiplexor `T_{p+q}` (`autoMux`) whose first `p`
auxiliary ports carry a `con` cell each, ports `2i - 1` and `2i` of `T_{p,q}` being the left and
right auxiliary ports of the `i`-th `con`, and whose last `q` auxiliary ports are ports
`2p + 1, …, 2p + q` of `T_{p,q}`. -/
def transpositor
    -- the number `p` of pairs
    (p : ℕ)
    -- the trees plugged into the `2p + q` ports, in order
    (ts : List (Term sig ℕ)) :
    Term sig ℕ :=
  autoMux (pairCon p ts)

/-- `ι_{p,q}` (Lafont, page 83): exchange the elements 1 and 2, 3 and 4, …, `2p - 1` and `2p`
of a list, and leave the rest in place. -/
def swapPairs
    {α : Type*} :
    -- the number `p` of pairs
    ℕ →
    -- the list, in order
    List α →
    List α
  | 0, ts => ts
  | p + 1, t :: t' :: ts => t' :: t :: swapPairs p ts
  | _ + 1, ts => ts

-- ============================================================================================
-- 2. Auxiliary lemmas
-- ============================================================================================

/-- `pairCon` maps lists of the same length to lists of the same length. -/
theorem length_pairCon_eq :
    -- the number of pairs, and two lists of trees
    ∀ (p : ℕ) (ts us : List (Term sig ℕ)),
    -- of the same length
    ts.length = us.length →
    -- are grouped into lists of the same length
    (pairCon p ts).length = (pairCon p us).length
  | 0, _, _, h => h
  | p + 1, _ :: _ :: ts, _ :: _ :: us, h => by
    simp only [pairCon, List.length_cons, Nat.add_right_cancel_iff] at h ⊢
    exact length_pairCon_eq p ts us h
  | _ + 1, [], [], _ => rfl
  | _ + 1, [_], [_], _ => rfl
  | _ + 1, [], _ :: _, h => by simp at h
  | _ + 1, _ :: _, [], h => by simp at h
  | _ + 1, [_], _ :: _ :: _, h => by simp at h
  | _ + 1, _ :: _ :: _, [_], h => by simp at h

/-- `ι_{p,q}` is an involution (page 83). -/
theorem swapPairs_swapPairs
    {α : Type*} :
    -- for every number of pairs and every list, `ι_{p,q}` applied twice is the identity
    ∀ (p : ℕ) (l : List α),
    swapPairs p (swapPairs p l) = l
  | 0, _ => rfl
  | p + 1, t :: t' :: l => by simp [swapPairs, swapPairs_swapPairs p l]
  | _ + 1, [] => rfl
  | _ + 1, [_] => rfl

/-- The names of `T_{p,q}` (page 83) are those of the trees plugged into its ports: its cells
carry no name. -/
theorem vars_transpositor
    -- the number of pairs
    (p : ℕ)
    -- the trees plugged into the ports
    (ts : List (Term sig ℕ)) :
    -- the names of `T_{p,q}` are the names of the trees, together
    (transpositor p ts).vars = (ts.map Term.vars).sum := by
  rw [transpositor, vars_autoMux]
  induction p generalizing ts with
  | zero => rfl
  | succ p ih =>
    match ts with
    | [] => rfl
    | [_] => rfl
    | t :: t' :: ts => simp [pairCon, ih, add_assoc]

/-- The `con` cells of two copies of `T_{p,q}`, once the multiplexors have met, face each other in
pairs; one `γγ` step per pair (page 83) exchanges the auxiliary ports, which gives `ι_{p,q}`. -/
theorem pairCon_red :
    -- the number of pairs, the trees `ts` of one copy and `us` of the other
    ∀ (p : ℕ) (ts us : List (Term sig ℕ))
    -- the rest of the net
      (Δ : CNet),
    -- both copies have the same number of ports
    ts.length = us.length →
    -- then the facing pairs of `con` cells reduce to the equations between `ts` and the `us`
    -- permuted by `ι_{p,q}`, and `Δ`
    Red ((List.zipWith (fun t u => s(t, u)) (pairCon p ts) (pairCon p us) : CNet) + Δ)
      ((List.zipWith (fun t u => s(t, u)) ts (swapPairs p us) : CNet) + Δ)
  | 0, _, _, _, _ => Relation.ReflTransGen.refl
  | p + 1, t :: t' :: ts, u :: u' :: us, Δ, h => by
    have hlen : ts.length = us.length := by simpa using h
    simp only [pairCon, swapPairs, List.zipWith_cons_cons, ← Multiset.cons_coe,
      Multiset.cons_add]
    refine Relation.ReflTransGen.head (step_con_con t t' u u' _) ?_
    have ih := pairCon_red p ts us (s(t, u') ::ₘ s(t', u) ::ₘ Δ) hlen
    refine ih.cast ?_ ?_ <;> ms
  | _ + 1, [], [], _, _ => Relation.ReflTransGen.refl
  | _ + 1, [_], [_], _, _ => Relation.ReflTransGen.refl
  | _ + 1, [], _ :: _, _, h => by simp at h
  | _ + 1, _ :: _, [], _, h => by simp at h
  | _ + 1, [_], _ :: _ :: _, _, h => by simp at h
  | _ + 1, _ :: _ :: _, [_], _, h => by simp at h

-- ============================================================================================
-- 3. Main result: the property of the transpositor
-- ============================================================================================

/-- The property of the transpositor (Lafont, page 83): two copies of `T_{p,q}` plugged by their
roots reduce to the wiring `ι_{p,q}`, here the equations joining port `i` of one copy to port
`ι_{p,q}(i)` of the other. The multiplexors `T_{p+q}` meet first (`δδ`, `εε`), then each pair of
`con` cells interacts by `γγ`, which exchanges the auxiliary ports. No hypothesis `2p ≤ length` is
needed: with fewer ports, both `pairCon` and `swapPairs` leave the unpaired port alone. -/
theorem transpositor_transpositor
    -- the number of pairs, the trees `ts` of one copy and `us` of the other
    (p : ℕ)
    (ts us : List (Term sig ℕ))
    -- the rest of the net
    (Δ : CNet)
    -- both copies have the same number of ports
    (hlen : ts.length = us.length) :
    -- `T_{p,q}` against `T_{p,q}` reduces to the equations between `ts` and the `us` permuted by
    -- `ι_{p,q}`, and `Δ`
    Red (s(transpositor p ts, transpositor p us) ::ₘ Δ)
      ((List.zipWith (fun t u => s(t, u)) ts (swapPairs p us) : CNet) + Δ) :=
  (autoMux_autoMux (pairCon p ts) (pairCon p us) Δ (length_pairCon_eq p ts us hlen)).trans
    (pairCon_red p ts us Δ hlen)

-- ============================================================================================
-- 4. Examples
-- ============================================================================================

/-- `T_{1,1}` of page 83 on ports `0, 1, 2`: a `dup` whose left auxiliary port carries a `con`
on ports `0, 1`, and whose right auxiliary port is port `2`. -/
theorem transpositor_one_one :
    -- `T_{1,1}` is a `dup` on a `con` and a free port
    transpositor 1 [var 0, var 1, var 2] = mkDup (mkCon (var 0) (var 1)) (var 2 : Term sig ℕ) :=
  rfl

/-- The picture of page 83 for `p = q = 1`: `T_{1,1}` on ports `0, 1, 2` against `T_{1,1}` on
ports `3, 4, 5` reduces to the wiring `ι_{1,1}`: `0–4`, `1–3`, `2–5`. -/
example :
    Red {s(transpositor 1 [var 0, var 1, var 2], transpositor 1 [var 3, var 4, var 5])}
      (s(var 0, var 4) ::ₘ s(var 1, var 3) ::ₘ {s(var 2, var 5)}) := by
  have h := transpositor_transpositor 1 [var 0, var 1, var 2] [var 3, var 4, var 5] 0 rfl
  refine h.cast rfl ?_
  simp only [swapPairs, List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil, add_zero]
  rfl

end INet.Comb
