/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Combinators

/-!
# Lafont, "Interaction Combinators" (1997): erasing and multiplexors

Page 85, Lemma 2 (i): an `era` plugged into the root of a tree of combinators leaves an `era` on
each leaf. Pages 82–83, Section 2.2 and Fig. 4: the multiplexor `M_n`, a right-nested tree of
`con` cells, and its dual `M_n*`; `M_n` against `M_n*` reduces to `n` wires.

Contents, in the order of the file:

1. Definitions: `mux`, the multiplexor `M_n`, and `muxStar`, its dual `M_n*`.
2. Erasing a tree: `erase_tree`, Lemma 2 (i).
3. Main result: `mux_muxStar`, the multiplexor property, `M_n` against `M_n*` reduces to `n`
   wires.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definitions: the multiplexor and its dual
-- ============================================================================================

/-- The multiplexor `M_n`, applied to the trees plugged into its `n` auxiliary ports. -/
def mux :
    -- the trees plugged into the auxiliary ports, in order
    List (Term sig ℕ) →
    Term sig ℕ
  | [] => mkEra
  | [t] => t
  | t :: t' :: ts => mkCon t (mux (t' :: ts))

/-- The dual multiplexor `M_n*`. -/
def muxStar :
    -- the trees plugged into the auxiliary ports, in order
    List (Term sig ℕ) →
    Term sig ℕ
  | [] => mkEra
  | [u] => u
  | u :: u' :: us => mkCon (muxStar (u' :: us)) u

-- ============================================================================================
-- 2. Erasing a tree (Lemma 2 (i))
-- ============================================================================================

/-- Lafont's Lemma 2 (i). -/
theorem erase_tree
    -- the tree, with an `era` on its root
    (τ : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet) :
    -- the net reduces to an `era` on each leaf of `τ`, and `Δ`
    Red (s(mkEra, τ) ::ₘ Δ)
      (τ.vars.map (fun x => s(mkEra, var x)) + Δ) := by
  induction τ using Comb.induction generalizing Δ with
  | var x => simpa using Relation.ReflTransGen.refl
  | era => simpa using Steps.single (step_era_era Δ)
  | con a b iha ihb =>
    refine Relation.ReflTransGen.head (step_era_con a b Δ) ?_
    have h1 : Red _ _ := iha (s(mkEra, b) ::ₘ Δ)
    have h2 : Red _ _ := ihb (a.vars.map (fun x => s(mkEra, var x)) + Δ)
    refine h1.trans (Steps.cast h2 ?_ ?_)
    · ms
    · simp only [vars_mkCon, Multiset.map_add]
      ms
  | dup a b iha ihb =>
    refine Relation.ReflTransGen.head (step_era_dup a b Δ) ?_
    have h1 : Red _ _ := iha (s(mkEra, b) ::ₘ Δ)
    have h2 : Red _ _ := ihb (a.vars.map (fun x => s(mkEra, var x)) + Δ)
    refine h1.trans (Steps.cast h2 ?_ ?_)
    · ms
    · simp only [vars_mkDup, Multiset.map_add]
      ms

-- ============================================================================================
-- 3. Main result: the multiplexor property
-- ============================================================================================

/-- Lafont's multiplexor property: `M_n` against `M_n*` reduces to `n` wires, here the equations
between the trees plugged into matching auxiliary ports. -/
theorem mux_muxStar :
    -- the trees `ts` on the auxiliary ports of `M_n`, `us` on those of `M_n*`
    ∀ (ts us : List (Term sig ℕ))
    -- the rest of the net
      (Δ : CNet),
    -- both multiplexors have the same arity `n`
    ts.length = us.length →
    -- then `M_n` against `M_n*` reduces to the `n` equations between matching trees, and `Δ`
    Red (s(mux ts, muxStar us) ::ₘ Δ)
      ((List.zipWith (fun t u => s(t, u)) ts us : CNet) + Δ)
  | [], [], Δ, _ => by simpa [mux, muxStar] using Steps.single (step_era_era Δ)
  | [t], [u], Δ, _ => by simpa [mux, muxStar] using Relation.ReflTransGen.refl
  | t :: t' :: ts, u :: u' :: us, Δ, h => by
    have hlen : (t' :: ts).length = (u' :: us).length := by simpa using h
    refine Relation.ReflTransGen.head
      (step_con_con t (mux (t' :: ts)) (muxStar (u' :: us)) u Δ) ?_
    have ih := mux_muxStar (t' :: ts) (u' :: us) (s(t, u) ::ₘ Δ) hlen
    refine ih.cast (Multiset.cons_swap _ _ _) ?_
    simp only [List.zipWith_cons_cons, ← Multiset.cons_coe]
    ms
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h

end INet.Comb
