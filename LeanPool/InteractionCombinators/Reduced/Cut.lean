/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.NetTrWire

/-!
# Cuts, and a strict translation keeps them (Proposition 3, page 80)

Lafont 1997, page 77: "a cut" is a pair of cells joined by their principal ports. Page 79: a net
is reduced when it has no cut and no vicious circle. Proposition 3 (page 80) says that a
translation reflects reduced nets, and keeps them when it is strict. Its proof checks four points;
this file and `InteractionCombinators/Reduced/CutChain.lean` do the first two, about cuts.

A net is text, so a cut is a cut of the graph: two principal ports joined *up to wires*. The text
`x = α(…), x = β(…)` is a cut, and so is a chain `α(…) = x₁, x₁ = x₂, x₂ = β(…)`.

Contents, in the order of the file:

1. Definition: `Net.HasCut`, some net equivalent to `N` has an equation `α(…) = β(…)`.
2. Auxiliary lemmas: `Net.hasCut_of_mem`, `Net.HasCut.of_equiv`, `Net.hasCut_iff_of_equiv` (the
   definition does not depend on the spelling of the net); `Net.stepE_of_cut_mem` (a cut that
   has a rule fires); `Net.HasCut.stepE` (in a system with a rule for every pair of symbols, in
   one order or the other, a net with a cut can be reduced); `PNet.Strict.inst_eq_app` (an
   instance of a strict principal net is a cell).
3. Main result: `Translation.NetTr.hasCut_of_strict`, the second point of the proof of
   Proposition 3: if `Φ` is strict and `N` has a cut, so does `Φ(N)`.
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

namespace Net

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- A net has a cut (Lafont 1997, page 77): two cells are joined by their principal ports, up to
wires. Some net that is the same graph as `N` has an equation whose two sides are cells. -/
def HasCut
    -- the net
    (N : Net S ℕ) :
    Prop :=
  -- there is a net `N'`, the same graph as `N`,
  ∃ N', Equiv N N' ∧
    -- with an equation between a cell `α(ts)` and a cell `β(us)`
    ∃ (α β : S.Sym) (ts : Fin (S.arity α) → Term S ℕ)
      (us : Fin (S.arity β) → Term S ℕ), s(Term.app α ts, Term.app β us) ∈ N'

-- ============================================================================================
-- 2. Auxiliary lemmas: cuts up to wires, and reducing a cut
-- ============================================================================================

/-- An equation between two cells is a cut (Lafont 1997, page 77). -/
theorem hasCut_of_mem
    -- the net
    {N : Net S ℕ}
    -- the two cells `α(ts)` and `β(us)`
    {α β : S.Sym}
    {ts : Fin (S.arity α) → Term S ℕ}
    {us : Fin (S.arity β) → Term S ℕ}
    -- the equation between them is in `N`
    (h : s(Term.app α ts, Term.app β us) ∈ N) :
    N.HasCut :=
  ⟨N, Equiv.refl N, α, β, ts, us, h⟩

/-- Having a cut is a property of the graph (Lafont 1997, page 77): it does not change under
wire substitution. -/
theorem HasCut.of_equiv
    -- two nets, the first with a cut
    {N M : Net S ℕ}
    (h : N.HasCut)
    -- they are the same graph
    (e : Equiv N M) :
    M.HasCut := by
  obtain ⟨N', hE, rest⟩ := h
  exact ⟨N', e.symm.trans hE, rest⟩

/-- Equivalent nets have a cut together (Lafont 1997, page 77). -/
theorem hasCut_iff_of_equiv
    -- two nets that are the same graph
    {N M : Net S ℕ}
    (e : Equiv N M) :
    N.HasCut ↔ M.HasCut :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

/-- **A cut with a rule fires** (Lafont 1997, page 73: interaction; page 77: cuts). If `N` is the
same graph as `α(…) = β(…), Δ` and the system has a rule for `α`–`β`, then `N` reduces in one
interaction up to wires. No linearity is needed: the names given to the new wires are taken above
every name of the net. -/
theorem stepE_of_cut_mem
    -- the system, with a rule `r` for the pair `α`–`β`
    {I : System S}
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (hr : I.rule α β = some r)
    -- the net, and the two cells `α(ts)` and `β(us)`
    {N : Net S ℕ}
    {ts : Fin (S.arity α) → Term S ℕ}
    {us : Fin (S.arity β) → Term S ℕ}
    -- the rest of the net
    (Δ : Net S ℕ)
    -- `N` is the same graph as the cut `α(ts) = β(us)` and `Δ`
    (hE : Equiv N (s(Term.app α ts, Term.app β us) ::ₘ Δ)) :
    -- `N` reduces in one interaction, up to wires
    ∃ M, StepE I N M := by
  let k : ℕ := (Net.vars (s(Term.app α ts, Term.app β us) ::ₘ Δ)).sup + 1
  refine ⟨_, _, hE, Step.mk α β r hr ts us Δ (fun w => k + w)
    (fun a b hab => Fin.ext (by simpa using hab)) (fun w hw => ?_)⟩
  have := Multiset.le_sup hw
  omega

/-- **A cut can be reduced** (Lafont 1997, page 79: a net is reduced when it has no cut and no
vicious circle). In a system with a rule for every pair of symbols, in one order or the other, a
net with a cut reduces in one interaction up to wires. The combinators are such a system
(`Comb.system_complete`). No linearity is needed. -/
theorem HasCut.stepE
    -- the system: every pair of symbols has a rule, in one order or the other
    {I : System S}
    (hI : ∀ α β, (I.rule α β).isSome ∨ (I.rule β α).isSome)
    -- the net, with a cut
    {N : Net S ℕ}
    (h : N.HasCut) :
    -- `N` reduces in one interaction, up to wires
    ∃ M, StepE I N M := by
  obtain ⟨N', hE, α, β, ts, us, hm⟩ := h
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem hm
  rcases hI α β with h | h
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
    exact stepE_of_cut_mem hr Δ hE
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
    rw [Sym2.eq_swap] at hE
    exact stepE_of_cut_mem hr Δ hE

end Net

/-- An instance of a strict principal net is a cell: its root is the principal port of a cell
(Lafont 1997, page 80). -/
theorem PNet.Strict.inst_eq_app
    -- a strict principal net of arity `n`
    {n : ℕ}
    {p : PNet S' n}
    (hp : p.Strict)
    -- the trees plugged into its auxiliary ports, and the names of its internal wires
    (args : Fin n → Term S' ℕ)
    (f : Fin p.internal → ℕ) :
    -- the instance is a cell `γ(us)`
    ∃ γ us, p.inst args f = Term.app γ us := by
  unfold PNet.inst
  cases h : p.tree with
  | var x => exact absurd h (hp x)
  | app γ ts => exact ⟨γ, _, rfl⟩

-- ============================================================================================
-- 3. Main result: a strict translation keeps cuts
-- ============================================================================================

/-- **A strict translation keeps cuts** (Lafont 1997, Proposition 3, second point of the proof,
page 80): if `Φ` is strict, `N'` translates `N` and `N` has a cut, then `N'` has a cut. The cut of
`N` is an equation `α(…) = β(…)` of a net equivalent to `N`; a translation of that net is
equivalent to `N'` (`NetTr.of_equiv`), and strictness makes both sides of the translated equation
cells. -/
theorem Translation.NetTr.hasCut_of_strict
    -- a strict translation
    {Φ : Translation S S'}
    (hΦ : Φ.Strict)
    -- a net and its translation
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- the net has a cut
    (hc : N.HasCut) :
    N'.HasCut := by
  obtain ⟨N₁, hE, α, β, ts, us, hm⟩ := hc
  obtain ⟨N₁', h₁, hE'⟩ := h.of_equiv hE
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem hm
  obtain ⟨e', Δ', he, -, rfl⟩ := Multiset.rel_cons_left.1 h₁.rel
  obtain ⟨a', b', rfl, ha, hb⟩ := Translation.EqTr.mk he
  cases ha with
  | app _ _ ts' f _ =>
  cases hb with
  | app _ _ us' g _ =>
  obtain ⟨γ, vs, hγ⟩ := (hΦ α).inst_eq_app ts' f
  obtain ⟨δ, ws, hδ⟩ := (hΦ β).inst_eq_app us' g
  refine ⟨_, hE', γ, δ, vs, ws, ?_⟩
  rw [hγ, hδ]
  exact Multiset.mem_cons_self _ _

end INet
