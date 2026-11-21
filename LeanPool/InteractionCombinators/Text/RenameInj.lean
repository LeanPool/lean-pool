/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.NetLemmas

/-!
# Renaming all names by an injective function

A net is a text, and its names are an artefact of the text (Lafont 1997, Section 1.1, pages 70 to
72: nets are graphs). Renaming *every* name of a net by an injective function `f` therefore
changes nothing: the renamed net is written `N.bind fun y => Term.var (f y)`, with no new
definition.

Contents, in the order of the file:

1. Auxiliary lemmas: `Term.bind_var_subst` (renaming commutes with plugging a tree into a name),
   `Net.count_vars_bind_var` (the names are renamed one for one), `Net.Linear.bind_var`
   (linearity is kept).
2. Main results: `Wire.bind_var` (a wire substitution stays a wire substitution) and
   `Equiv.bind_var` (equivalent nets stay equivalent).
-/

@[expose] public section

namespace INet

variable {S : Signature} {ν μ : Type} [DecidableEq ν] [DecidableEq μ]

-- ============================================================================================
-- 1. Auxiliary lemmas
-- ============================================================================================

/-- Renaming by an injective function commutes with substitution: renaming `r` with `t` plugged
into `x` is the renamed `r` with the renamed `t` plugged into `f x`. Names do not matter in a
graph (Lafont 1997, Section 1.1, pages 70 to 72). -/
theorem Term.bind_var_subst
    -- the renaming, which is injective
    (f : ν → μ)
    (hf : Function.Injective f)
    -- the tree `r`, the name `x` and the tree `t` plugged into it
    (r : Term S ν)
    (x : ν)
    (t : Term S ν) :
    -- renaming after plugging is plugging the renamed `t` into `f x` after renaming
    (r.subst x t).bind (fun y => Term.var (f y)) =
      (r.bind fun y => Term.var (f y)).subst (f x) (t.bind fun y => Term.var (f y)) := by
  induction r with
  | var z =>
    by_cases hz : z = x
    · subst hz; simp [Term.subst]
    · have hfz : f z ≠ f x := fun h => hz (hf h)
      simp [Term.subst, hz, hfz]
  | app α ts ih =>
    simp only [Term.subst, Term.bind_app] at ih ⊢
    congr 1
    funext i
    exact ih i

/-- Renaming by an injective function keeps the number of occurrences of every name: `f x` occurs
in the renamed net as often as `x` in the net (Lafont 1997, Section 1.1, pages 70 to 72). -/
theorem Net.count_vars_bind_var
    -- the renaming, which is injective
    (f : ν → μ)
    (hf : Function.Injective f)
    -- the net and the name whose occurrences are counted
    (N : Net S ν)
    (x : ν) :
    -- `f x` occurs in the renamed net as often as `x` in `N`
    (N.bind fun y => Term.var (f y)).vars.count (f x) = N.vars.count x := by
  rw [Net.vars_bind_var]
  exact Multiset.count_map_eq_count' f _ hf x

/-- Renaming by an injective function keeps a net linear: internal wires stay internal wires and
free ports stay free ports (Lafont 1997, Section 1.1, pages 70 to 72). -/
theorem Net.Linear.bind_var
    -- the renaming, which is injective
    (f : ν → μ)
    (hf : Function.Injective f)
    -- the net, which is linear
    {N : Net S ν}
    (h : N.Linear) :
    -- the renamed net is linear
    (N.bind fun y => Term.var (f y)).Linear := by
  intro y
  by_cases hy : y ∈ (N.bind fun y => Term.var (f y)).vars
  · rw [Net.vars_bind_var] at hy
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hy
    rw [Net.count_vars_bind_var f hf]
    exact h x
  · rw [Multiset.count_eq_zero_of_notMem hy]
    omega

-- ============================================================================================
-- 2. Main results: wire substitutions and equivalence are kept
-- ============================================================================================

/-- A wire substitution, renamed by an injective function, is the wire substitution of the renamed
wire in the renamed net (Lafont 1997, Section 1.1, pages 70 to 72). -/
theorem Wire.bind_var
    -- the renaming, which is injective
    (f : ν → μ)
    (hf : Function.Injective f)
    -- the two nets, related by a wire substitution
    {N M : Net S ν}
    (h : Wire N M) :
    -- the renamed nets are related by a wire substitution
    Wire (N.bind fun y => Term.var (f y)) (M.bind fun y => Term.var (f y)) := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hlin' := hlin.bind_var f hf
  have hx' : f x ∈ (a.bind fun y => Term.var (f y)).vars +
      (b.bind fun y => Term.var (f y)).vars := by
    have := Multiset.mem_map_of_mem f hx
    simpa [Term.vars_bind, Multiset.bind_singleton] using this
  have e : (Net.bind (fun y => Term.var (f y)) (s(Term.var x, t) ::ₘ s(a, b) ::ₘ Δ) : Net S μ) =
      s(Term.var (f x), t.bind fun y => Term.var (f y)) ::ₘ
        s(a.bind fun y => Term.var (f y), b.bind fun y => Term.var (f y)) ::ₘ
          Δ.bind fun y => Term.var (f y) := by
    simp [Net.bind]
  have e' : (Net.bind (fun y => Term.var (f y)) (s(a.subst x t, b.subst x t) ::ₘ Δ) : Net S μ) =
      s((a.bind fun y => Term.var (f y)).subst (f x) (t.bind fun y => Term.var (f y)),
        (b.bind fun y => Term.var (f y)).subst (f x) (t.bind fun y => Term.var (f y))) ::ₘ
          Δ.bind fun y => Term.var (f y) := by
    simp [Net.bind, Term.bind_var_subst f hf]
  rw [e, e']
  exact Wire.mk (f x) _ _ _ _ (hlin'.cast e) hx'

/-- Equivalent nets stay equivalent when all their names are renamed by an injective function:
the equivalence is a property of the graph, not of the names (Lafont 1997, Section 1.1, pages 70
to 72). -/
theorem Equiv.bind_var
    -- the renaming, which is injective
    (f : ν → μ)
    (hf : Function.Injective f)
    -- the two nets, which are equivalent
    {N M : Net S ν}
    (h : Equiv N M) :
    -- the renamed nets are equivalent
    Equiv (N.bind fun y => Term.var (f y)) (M.bind fun y => Term.var (f y)) := by
  induction h with
  | rel _ _ h => exact (h.bind_var f hf).equiv
  | refl _ => exact Equiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end INet
