/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Multiplexors.Multiplexor

/-!
# Lafont, "Interaction Combinators" (1997): the autodual multiplexor

Page 83, Fig. 5: the autodual multiplexor `T_n`, a right-nested tree of `dup` cells, plugged by
its root into a second copy of itself, reduces to `n` wires. The names of the three multiplexors
`M_n`, `M_n*` and `T_n` are those of the trees plugged into their auxiliary ports.

Contents, in the order of the file:

1. Definition: `autoMux`, the autodual multiplexor `T_n` of Fig. 5, built with `dup`.
2. Auxiliary lemmas: `vars_mux`, `vars_muxStar`, `vars_autoMux`. The names of the three
   multiplexors are the names of the trees plugged into their auxiliary ports.
3. Main result: `autoMux_autoMux`, the property of `T_n` (page 83): two copies of `T_n` plugged
   by their roots reduce to `n` wires, joining port `i` of one to port `i` of the other.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definition: the autodual multiplexor
-- ============================================================================================

/-- The autodual multiplexor `T_n` (Lafont, Fig. 5, page 83), applied to the trees plugged into
its `n` auxiliary ports. `T_0` is `era`, `T_1` is a wire, and `T_{n+2}` is a `dup` whose right
auxiliary port carries `T_{n+1}`, as `M_n` is nested in Fig. 4. -/
def autoMux :
    -- the trees plugged into the auxiliary ports, in order
    List (Term sig ℕ) →
    Term sig ℕ
  | [] => mkEra
  | [t] => t
  | t :: t' :: ts => mkDup t (autoMux (t' :: ts))

-- ============================================================================================
-- 2. Auxiliary lemmas: the names of the multiplexors
-- ============================================================================================

/-- The names of the multiplexor `M_n` (Lafont, Fig. 4, page 83) are those of the trees plugged
into its auxiliary ports: the cells of `M_n` carry no name. -/
theorem vars_mux :
    -- for the trees `ts` on the auxiliary ports, the names of `M_n` are the names of the `ts`
    ∀ (ts : List (Term sig ℕ)),
    (mux ts).vars = (ts.map Term.vars).sum
  | [] => by simp [mux]
  | [t] => by simp [mux]
  | t :: t' :: ts => by
    rw [mux, vars_mkCon, vars_mux (t' :: ts)]
    simp

/-- The names of the dual multiplexor `M_n*` (Lafont, Fig. 4, page 83) are those of the trees
plugged into its auxiliary ports. -/
theorem vars_muxStar :
    -- for the trees `ts` on the auxiliary ports, the names of `M_n*` are the names of the `ts`
    ∀ (ts : List (Term sig ℕ)),
    (muxStar ts).vars = (ts.map Term.vars).sum
  | [] => by simp [muxStar]
  | [t] => by simp [muxStar]
  | t :: t' :: ts => by
    rw [muxStar, vars_mkCon, vars_muxStar (t' :: ts)]
    simp [add_comm]

/-- The names of the autodual multiplexor `T_n` (Lafont, Fig. 5, page 83) are those of the trees
plugged into its auxiliary ports. -/
theorem vars_autoMux :
    -- for the trees `ts` on the auxiliary ports, the names of `T_n` are the names of the `ts`
    ∀ (ts : List (Term sig ℕ)),
    (autoMux ts).vars = (ts.map Term.vars).sum
  | [] => by simp [autoMux]
  | [t] => by simp [autoMux]
  | t :: t' :: ts => by
    rw [autoMux, vars_mkDup, vars_autoMux (t' :: ts)]
    simp

-- ============================================================================================
-- 3. Main result: the property of the autodual multiplexor
-- ============================================================================================

/-- The property of the autodual multiplexor (Lafont, page 83, picture above Fig. 5): two copies
of `T_n` plugged by their roots reduce to `n` wires, here the equations between the trees plugged
into matching auxiliary ports. Only the rules `δδ` and `εε` are used. -/
theorem autoMux_autoMux :
    -- the trees `ts` on the auxiliary ports of one `T_n`, `us` on those of the other
    ∀ (ts us : List (Term sig ℕ))
    -- the rest of the net
      (Δ : CNet),
    -- both multiplexors have the same arity `n`
    ts.length = us.length →
    -- then the two copies of `T_n` reduce to the `n` equations between matching trees, and `Δ`
    Red (s(autoMux ts, autoMux us) ::ₘ Δ)
      ((List.zipWith (fun t u => s(t, u)) ts us : CNet) + Δ)
  | [], [], Δ, _ => by simpa [autoMux] using Steps.single (step_era_era Δ)
  | [t], [u], Δ, _ => by simpa [autoMux] using Relation.ReflTransGen.refl
  | t :: t' :: ts, u :: u' :: us, Δ, h => by
    have hlen : (t' :: ts).length = (u' :: us).length := by simpa using h
    refine Relation.ReflTransGen.head
      (step_dup_dup t (autoMux (t' :: ts)) u (autoMux (u' :: us)) Δ) ?_
    have ih := autoMux_autoMux (t' :: ts) (u' :: us) (s(t, u) ::ₘ Δ) hlen
    refine ih.cast (Multiset.cons_swap _ _ _) ?_
    simp only [List.zipWith_cons_cons, ← Multiset.cons_coe]
    ms
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h

end INet.Comb
