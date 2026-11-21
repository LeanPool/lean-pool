/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Combinators

/-!
# Lafont, "Interaction Combinators" (1997): duplicating a wiring

Page 87, Lemma 3 (ii): a wiring with a `dup` cell on each of its free ports reduces to two copies
of the wiring. Each wire of the wiring carries a `dup` at both ends; the two `dup` cells are
joined by the wire, so after a wire substitution they form an active pair, and the rule
`dup`–`dup` annihilates them without exchanging the auxiliary ports.

Contents, in the order of the file:

1. Auxiliary lemma: `stepE_dup_wire`, two `dup` cells joined by a wire annihilate, after a wire
   substitution.
2. Main result: `dup_wiring`, Lemma 3 (ii) (page 87).
3. An example showing that the hypotheses of `dup_wiring` can hold.
-/

@[expose] public section

namespace INet

namespace Comb

open Term

-- ============================================================================================
-- 1. Auxiliary lemma: one wire between two dup cells
-- ============================================================================================

/-- Two duplicators whose principal ports are joined by the wire `x` annihilate: a wire
substitution makes them an active pair, and the rule `δδ` joins the left auxiliary ports together
and the right ones together, without exchange (page 87, one wire of Lemma 3 (ii)). -/
theorem stepE_dup_wire
    -- the wire joining the principal ports of the two `dup` cells
    (x : ℕ)
    -- the auxiliary ports of the two `dup` cells: `a`, `b` of the first, `c`, `d` of the second
    (a b c d : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear
    (hlin : Net.Linear (s(mkDup a b, var x) ::ₘ s(mkDup c d, var x) ::ₘ Δ)) :
    -- after a wire substitution, one interaction joins `a` to `c` and `b` to `d`
    StepE system (s(mkDup a b, var x) ::ₘ s(mkDup c d, var x) ::ₘ Δ)
      (s(a, c) ::ₘ s(b, d) ::ₘ Δ) := by
  have e : (s(mkDup a b, var x) ::ₘ s(mkDup c d, var x) ::ₘ Δ : CNet) =
      s(var x, mkDup c d) ::ₘ s(mkDup a b, var x) ::ₘ Δ := by
    rw [Multiset.cons_swap, Sym2.eq_swap (a := mkDup c d)]
  have hx : x ∉ (mkDup a b : Term sig ℕ).vars := by
    intro hm
    have h := hlin x
    simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at h
    have := Multiset.count_pos.2 hm
    omega
  have hw := Wire.mk x (mkDup c d) (mkDup a b) (var x) Δ (hlin.cast e) (by simp)
  rw [subst_var_self, subst_of_notMem hx] at hw
  exact ⟨_, (hw.cast e.symm rfl).equiv, step_dup_dup a b c d Δ⟩

-- ============================================================================================
-- 2. Main result: Lemma 3 (ii)
-- ============================================================================================

/-- Lafont's Lemma 3 (ii), page 87: a wiring `D` with a duplicator on every free port reduces to two
copies of `D`. Each wire `x` of `D` carries `dup (a x) (b x)` at one end and `dup (c x) (d x)` at
the other; the first copy of the wire joins `a x` to `c x`, the second joins `b x` to `d x`. The
two duplicators of a wire are joined by it, so they interact after a wire substitution, hence
`StepsE`. -/
theorem dup_wiring
    -- the wires of the wiring
    (D : Multiset ℕ)
    -- the auxiliary ports of the `dup` cells on each wire `x`: `a x`, `b x` at one end,
    -- `c x`, `d x` at the other
    (a b c d : ℕ → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: a `dup` at both ends of every wire, and `Δ`
    (hlin : Net.Linear (D.map (fun x => s(mkDup (a x) (b x), var x))
                          + D.map (fun x => s(mkDup (c x) (d x), var x))
                          + Δ)) :
    -- the net reduces, up to wires, to the two copies of the wiring, `a x`—`c x` and
    -- `b x`—`d x` for each wire `x`, and `Δ`
    StepsE system
      (D.map (fun x => s(mkDup (a x) (b x), var x))
        + D.map (fun x => s(mkDup (c x) (d x), var x))
        + Δ)
      (D.map (fun x => s(a x, c x))
        + D.map (fun x => s(b x, d x))
        + Δ) := by
  induction D using Multiset.induction_on generalizing Δ with
  | empty => simpa using Relation.ReflTransGen.refl
  | cons x D ih =>
    have e : ((x ::ₘ D).map (fun x => s(mkDup (a x) (b x), var x)) +
        (x ::ₘ D).map (fun x => s(mkDup (c x) (d x), var x)) + Δ : CNet) =
        s(mkDup (a x) (b x), var x) ::ₘ s(mkDup (c x) (d x), var x) ::ₘ
          (D.map (fun x => s(mkDup (a x) (b x), var x)) +
            D.map (fun x => s(mkDup (c x) (d x), var x)) + Δ) := by
      simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]
      exact Multiset.cons_swap _ _ _
    have e' : (D.map (fun x => s(a x, c x)) + D.map (fun x => s(b x, d x)) +
        (s(a x, c x) ::ₘ s(b x, d x) ::ₘ Δ) : CNet) =
        (x ::ₘ D).map (fun x => s(a x, c x)) + (x ::ₘ D).map (fun x => s(b x, d x)) + Δ := by
      simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]
      exact Multiset.cons_swap _ _ _
    rw [e] at hlin ⊢
    rw [← e']
    have h1 := stepE_dup_wire x (a x) (b x) (c x) (d x) _ hlin
    have h1lin := h1.linear system_wellFormed.linear hlin
    have e'' : (s(a x, c x) ::ₘ s(b x, d x) ::ₘ
        (D.map (fun x => s(mkDup (a x) (b x), var x)) +
          D.map (fun x => s(mkDup (c x) (d x), var x)) + Δ) : CNet) =
        D.map (fun x => s(mkDup (a x) (b x), var x)) +
          D.map (fun x => s(mkDup (c x) (d x), var x)) + (s(a x, c x) ::ₘ s(b x, d x) ::ₘ Δ) := by
      simp only [Multiset.add_cons]
    rw [e''] at h1 h1lin
    exact Relation.ReflTransGen.head h1 (ih _ h1lin)

-- ============================================================================================
-- 3. The hypotheses can hold
-- ============================================================================================

/-- The hypotheses of `dup_wiring` hold: one wire `0` with a duplicator at each end, whose
auxiliary ports are the free ports `1, 2, 3, 4`, reduces to the two copies `1—3` and `2—4`. -/
example :
    -- a `dup` on each end of the wire `0` reduces, up to wires, to `1`—`3` and `2`—`4`
    StepsE system
      ({s(mkDup (var 1) (var 2), var 0), s(mkDup (var 3) (var 4), var 0)} : CNet)
      {s(var 1, var 3), s(var 2, var 4)} := by
  have h := dup_wiring {0} (fun _ => var 1) (fun _ => var 2) (fun _ => var 3) (fun _ => var 4) 0
    (by
      intro y
      simp only [Multiset.map_singleton, Multiset.singleton_add, add_zero, Net.vars_cons,
        Net.vars_singleton, eqVars_mk, vars_mkDup, vars_var, Multiset.count_add,
        Multiset.count_singleton, Multiset.count_cons]
      split_ifs <;> omega)
  simpa [Multiset.insert_eq_cons] using h

end Comb

end INet
