/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.SymmPerm

/-!
# Proposition 1: strong confluence (Lafont 1997, page 73)

The statement and its proof, kept apart from `RuleInstances.lean`, which has the lemmas
about instances of a rule. The proof uses the symmetry of a rule of a symbol with itself
(`System.WellFormed.symm`), which is symmetry up to a permutation of the internal wires
(`Rule.SymmPerm`, `InteractionCombinators/Universality/RecursionFree/SymmPerm.lean`); that file is
built on `RuleInstances.lean`, hence the separate file.

Contents, in the order of the file:

1. Auxiliary lemma: `Rule.equiv_inst_swap`. An active pair of a symbol with itself, fired with
   either cell first, gives the same graph.
2. Main result: `Step.strong_confluence`, Proposition 1 (page 73).
3. An example showing that the hypotheses of `Rule.equiv_inst_swap` can hold.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemma: an active pair read the other way
-- ============================================================================================

namespace Rule

variable {a b k : ℕ}

/-- **The same active pair, read the other way** (Lafont 1997, Proposition 1, page 73, implicit;
and page 73: the rule of a symbol with itself is symmetric). In a well-formed system with a rule
`r` for `α`, `α`, the equation `α(as) = α(bs)` can be fired with `as` on the first cell or with
`bs` on the first cell. In a linear net, with fresh injective names `f`, `f'` for the new wires,
the two results are the same graph. -/
theorem equiv_inst_swap
    -- a well-formed interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a symbol `α` and the rule `r` of `α` with itself
    {α : S.Sym}
    {r : Rule S (S.arity α) (S.arity α)}
    (hr : I.rule α α = some r)
    -- the trees on the auxiliary ports of the two cells
    (as bs : Fin (S.arity α) → Term S ℕ)
    -- the rest of the net
    (Δ : Net S ℕ)
    -- the net we start from is linear: the active pair `α(as) = α(bs)`, and `Δ`
    (hN : Net.Linear (s(Term.app α as, Term.app α bs) ::ₘ Δ))
    -- two injective namings `f`, `f'` of the internal wires of `r`
    (f f' : Fin r.internal → ℕ)
    (hf : Function.Injective f)
    (hf' : Function.Injective f')
    -- both are fresh for the net
    (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α as, Term.app α bs) ::ₘ Δ))
    (hfresh' : ∀ i, f' i ∉ Net.vars (s(Term.app α as, Term.app α bs) ::ₘ Δ)) :
    -- firing with `as` on the first cell, named by `f`, and with `bs` on the first cell, named
    -- by `f'`, give the same graph
    Equiv (r.inst as bs f + Δ) (r.inst bs as f' + Δ) := by
  have hrl := hI.linear _ _ _ hr
  have E := r.equiv_inst_same hrl as bs Δ hN f f' hf hf' hfresh hfresh'
  have L' := r.linear_inst_add hrl (hα := rfl) (hβ := rfl) hf' hN hfresh'
  exact E.trans (r.equiv_inst_comm_of_symmPerm hrl (hI.symm _ _ hr) as bs f' Δ L')

end Rule

-- ============================================================================================
-- 2. Main result: strong confluence
-- ============================================================================================

/-- **Proposition 1: strong confluence** (Lafont 1997, page 73). If a linear net `N` reduces in
one interaction to `M₁` and to `M₂`, then either `M₁` and `M₂` are the same graph, or each reduces
in one interaction to a net, and the two nets are the same graph. -/
theorem Step.strong_confluence
    -- a well-formed interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a net `N` and two nets `M₁`, `M₂`
    {N M₁ M₂ : Net S ℕ}
    -- `N` is linear
    (hN : N.Linear)
    -- `N` reduces in one interaction to `M₁`, and in one interaction to `M₂`
    (h₁ : Step I N M₁)
    (h₂ : Step I N M₂) :
    -- either `M₁` and `M₂` are the same graph,
    Equiv M₁ M₂ ∨
      -- or there are nets `P₁`, `P₂` such that
      ∃ P₁ P₂,
        -- `M₁` reduces in one interaction to `P₁`,
        Step I M₁ P₁ ∧
        -- `M₂` reduces in one interaction to `P₂`,
        Step I M₂ P₂ ∧
        -- and `P₁` and `P₂` are the same graph
        Equiv P₁ P₂ := by
  obtain ⟨α, β, r₁, hr₁, as, bs, Δ₁, f, hf, hffresh⟩ := h₁
  generalize hNe : (s(Term.app α as, Term.app β bs) ::ₘ Δ₁ : Net S ℕ) = N' at h₂
  obtain ⟨γ, δ, r₂, hr₂, cs, ds, Δ₂, g, hg, hgfresh⟩ := h₂
  rcases Multiset.cons_eq_cons.1 hNe with ⟨he, hΔ⟩ | ⟨-, C, hC₁, hC₂⟩
  · -- the same active pair
    subst hΔ
    rcases Sym2.eq_iff.1 he with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · -- read the same way
      simp only [Term.app.injEq] at hac hbd
      obtain ⟨rfl, hac⟩ := hac
      obtain ⟨rfl, hbd⟩ := hbd
      cases eq_of_heq hac
      cases eq_of_heq hbd
      rw [hr₁] at hr₂
      cases Option.some.inj hr₂
      left
      exact Rule.equiv_inst_same _ (hI.linear _ _ _ hr₁) _ _ _ hN f g hf hg hffresh hgfresh
    · -- read the other way
      simp only [Term.app.injEq] at had hbc
      obtain ⟨rfl, had⟩ := had
      obtain ⟨rfl, hbc⟩ := hbc
      cases eq_of_heq had
      cases eq_of_heq hbc
      by_cases hαβ : α = β
      · subst hαβ
        rw [hr₁] at hr₂
        cases Option.some.inj hr₂
        left
        exact Rule.equiv_inst_swap hI hr₁ _ _ _ hN f g hf hg hffresh
          (fun i => by rw [Sym2.eq_swap]; exact hgfresh i)
      · have := hI.unique α β hαβ (by simp [hr₁])
        rw [this] at hr₂
        cases hr₂
  · -- two different active pairs
    subst hC₁ hC₂
    right
    exact Step.commute hI.linear hr₁ hr₂ as bs cs ds C hN f hf hffresh g hg hgfresh

-- ============================================================================================
-- 3. The hypotheses can hold
-- ============================================================================================

section Example

open Comb

/-- Non-vacuity of `Rule.equiv_inst_swap`: in the combinators, the `con`–`con` pair
`con(0, 1) = con(2, 3)` fired with `0, 1` on the first cell and with `2, 3` on the first cell
gives the same graph. The first gives `0 = 3, 1 = 2`, the second `2 = 1, 3 = 0`. -/
example :
    -- firing `con(0, 1) = con(2, 3)` either way gives the same graph
    Equiv (ruleConCon.inst ![var 0, var 1] ![var 2, var 3] Fin.elim0 + 0)
      (ruleConCon.inst ![var 2, var 3] ![var 0, var 1] Fin.elim0 + 0) := by
  refine Rule.equiv_inst_swap (I := system) (α := con) system_wellFormed rfl _ _ 0 ?_
    Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0)
  intro y
  change Multiset.count y (Net.vars (s(mkCon (var 0) (var 1), mkCon (var 2) (var 3)) ::ₘ 0)) ≤ 2
  simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkCon, vars_var,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

end Example

end INet
