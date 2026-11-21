/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.SimulationStrict
public import LeanPool.InteractionCombinators.Translations.TranslationInvertible

/-!
# An invertible translation simulates every interaction in one step (page 81)

Lafont 1997, page 81, after Proposition 4: "if `Φ` is strict, the left member is not reduced, and
the reduction cannot be of length 0. Similarly, if `Φ` is invertible, the reduction must be of
length 1. … `L > 0` if `Φ` is strict, and `L = M = 1` if `Φ` is invertible."

The paper's argument: `Φ(α)` and `Φ(β)` are single cells `α'`, `β'` (page 81, top;
`Translation.Invertible.net_eq`), so their pair is one cut. The reduction is not empty (as for
`L > 0`), and after the interaction of `α'` with `β'` the net is an instance of a reduced net,
which has no cut, so nothing follows.

In Lean the reduction is `StepsE`: a wire substitution may come before each interaction. That
the net reached after one interaction up to wires from the pair `α'(u) = β'(v)` has no cut is a
statement about every net that is the same graph as the pair. Here it is a hypothesis, `hpair`,
about the target system alone; it is proved for every well-formed system in
`Translations/PairStepE.lean` (`System.WellFormed.stepE_pair_not_hasCut`), which also gives the
theorem without it (`Translation.Invertible.compatibleWithin_one_of_wellFormed`).

Contents, in the order of the file:

1. Auxiliary lemmas, counted reductions that stop after one interaction: `StepE.hasCut` (a net
   that reduces has a cut), `StepsEN.cases_head` (a counted reduction is empty, or starts with
   one interaction), `StepsEN.eq_one_of_not_hasCut` (a non-empty reduction whose first
   interaction leaves no cut has length `1`).
2. Auxiliary lemmas, from distinct names to all names: `Translation.CompatibleWithin.of_distinct`
   (`CompatibleWithin` for distinct names on the ports gives it for all names, the proof of
   `CompatibleWithin.pos` for any `L`, `M`), `Translation.CompatibleWithin.one_of_pair` (a strict
   compatible translation whose pairs leave no cut after one interaction has `L = M = 1`).
3. Auxiliary lemmas, invertible translations: `Translation.Invertible.inst_eq` (an instance of
   `Φ(α)` with names on its ports is one cell with the names permuted),
   `Translation.Invertible.strict`.
4. Main result: `Translation.Invertible.compatibleWithin_one`, `L = M = 1` for an invertible
   translation, given `hpair` for the target system.
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: counted reductions that stop after one interaction
-- ============================================================================================

/-- **A net that reduces has a cut** (Lafont 1997, page 73: an interaction rewrites a cut; page 77:
the definition of a cut). If `N` reduces in one interaction up to wires, a net that is the same
graph as `N` has an equation between two cells. -/
theorem StepE.hasCut
    -- the interaction system
    {I : System S}
    -- a net `N` that reduces in one interaction, up to wires, to `M`
    {N M : Net S ℕ}
    (h : StepE I N M) :
    N.HasCut := by
  obtain ⟨K, hE, hs⟩ := h
  cases hs with
  | mk α β r hr as bs Δ f hf hfresh => exact ⟨_, hE, α, β, as, bs, Multiset.mem_cons_self _ _⟩

/-- **A counted reduction is empty or starts with one interaction** (Lafont 1997, page 81, the
length of a reduction). -/
theorem StepsEN.cases_head
    -- the interaction system
    {I : System S}
    -- a reduction of `N` to `M` in `m` interactions, up to wires
    {m : ℕ}
    {N M : Net S ℕ}
    (h : StepsEN I m N M) :
    -- either it is empty: `m = 0` and `M` is `N`,
    (m = 0 ∧ N = M)
      -- or `m = n + 1`, and `N` reduces in one interaction to `K`, then in `n` to `M`
      ∨ ∃ K n, m = n + 1 ∧ StepE I N K ∧ StepsEN I n K M := by
  induction h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | tail _ hs ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨K, n, rfl, h1, h2⟩
    · exact Or.inr ⟨_, 0, rfl, hs, .refl _⟩
    · exact Or.inr ⟨K, n + 1, rfl, h1, h2.tail hs⟩

/-- **A reduction that cannot go on after one interaction has length `1`** (Lafont 1997, page 81:
"the reduction must be of length 1"). If `N` reduces in `n ≠ 0` interactions up to wires to `M`,
and every net reached from `N` in one interaction up to wires has no cut, then `n = 1`, and `N`
reduces to `M` in one interaction up to wires: a second interaction would need a cut
(`StepE.hasCut`). -/
theorem StepsEN.eq_one_of_not_hasCut
    -- the interaction system
    {I : System S}
    -- a reduction of `N` to `M` in `n` interactions, up to wires, and `n` is not `0`
    {n : ℕ}
    {N M : Net S ℕ}
    (h : StepsEN I n N M)
    (hn : n ≠ 0)
    -- every net reached from `N` in one interaction, up to wires, has no cut
    (hK : ∀ K, StepE I N K → ¬ K.HasCut) :
    -- the reduction has one interaction,
    n = 1
      -- and `N` reduces to `M` in one interaction, up to wires
      ∧ StepE I N M := by
  rcases h.cases_head with ⟨rfl, -⟩ | ⟨K, m, rfl, h1, h2⟩
  · exact absurd rfl hn
  · rcases h2.cases_head with ⟨rfl, rfl⟩ | ⟨K', m', rfl, h3, -⟩
    · exact ⟨rfl, h1⟩
    · exact absurd h3.hasCut (hK K h1)

-- ============================================================================================
-- 2. Auxiliary lemmas: from distinct names to all names
-- ============================================================================================

namespace Translation

variable {Φ : Translation S S'}

/-- **Compatibility within `L` and `M` for distinct names gives it for all names** (Lafont 1997,
page 81, the lengths `L`, `M`; page 73, the two cells of a rule have distinct ports). If the
translations of the two cells of every rule, with pairwise distinct names on their ports, reduce up
to wires in `k` interactions, `L ≤ k ≤ M`, to a translation of the right member, then so do they
for any names. The rules of `I` are those of a well-formed system and the rules of `I'` are linear,
as in Proposition 4. For equal names, the pair `α(xs) = β(ys)` interacts in `I`, and its
simulation (`CompatibleByDistinct.step`, the proof of Proposition 4) only uses the rule with fresh
distinct names. This is the argument of `CompatibleWithin.pos`, for any bounds. -/
theorem CompatibleWithin.of_distinct
    -- the source system, well-formed, and the target system, with linear rules
    {I : System S}
    {I' : System S'}
    -- the bounds on the lengths of the simulations
    {L M : ℕ}
    (hI : I.WellFormed)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- for distinct names on the ports, every rule is simulated in `k` interactions,
    -- `L ≤ k ≤ M`, up to wires
    (h : Φ.CompatibleByDistinct I fun N K => ∃ k, L ≤ k ∧ k ≤ M ∧ StepsEN I' k N K) :
    -- then it is for all names
    Φ.CompatibleWithin I I' L M := by
  intro α β r hr xs ys f g hlin
  let A : Sym2 (Term S ℕ) := s(.app α fun i => .var (xs i), .app β fun j => .var (ys j))
  let k : ℕ := (Net.vars ({A} : Net S ℕ)).sup + 1
  have hstep : Step I (A ::ₘ 0)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w) + 0) :=
    Step.mk α β r hr _ _ 0 (fun w => k + w)
      (fun a b hab => Fin.ext (by simpa using hab))
      (fun w hw => by
        have hle : k + w ≤ (Net.vars ({A} : Net S ℕ)).sup :=
          Multiset.le_sup (show k + (w : ℕ) ∈ Net.vars ({A} : Net S ℕ) from hw)
        omega)
  have hT : Φ.NetTr (A ::ₘ 0) (s((Φ.net α).inst (fun i => .var (xs i)) f,
      (Φ.net β).inst (fun j => .var (ys j)) g) ::ₘ 0) :=
    ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl,
      TermTr.app α _ _ f fun i => TermTr.var _, TermTr.app β _ _ g fun j => TermTr.var _⟩
      Multiset.Rel.zero, hlin⟩
  obtain ⟨M₁, M', hR, hE, hT'⟩ := CompatibleByDistinct.step
    (R := fun N K => ∃ k, L ≤ k ∧ k ≤ M ∧ StepsEN I' k N K) hI.linear hI'
    (fun Γ ⟨k, hL, hM, hk⟩ hl => by
      obtain ⟨M', h1, h2, h3⟩ := hk.add_right hI' Γ hl
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2, h3⟩)
    (fun hE ⟨k, hL, hM, hk⟩ => by
      obtain ⟨M', h1, h2⟩ := hk.of_equiv hE
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2⟩)
    (fun ⟨_, _, _, hk⟩ => hk.stepsE) h hstep hT
  rw [add_zero] at hT'
  exact ⟨M₁, M', fun w => k + w, hR, hE, hT'⟩

/-- **A strict compatible translation whose pairs stop after one interaction has `L = M = 1`**
(Lafont 1997, page 81: "if `Φ` is invertible, the reduction must be of length 1"). Let `Φ` be
strict and compatible, `I` well-formed and the rules of `I'` linear. Suppose that, for every rule
of `I` and distinct names on the ports, every net reached in one interaction up to wires from the
translations of the two cells, plugged by their roots, has no cut (`hpair`). Then `Φ` simulates
every rule in exactly one interaction. The reduction given by `Compatible` is not empty
(`not_equiv_pair_of_strict`), and it cannot go on after its first interaction
(`StepsEN.eq_one_of_not_hasCut`). -/
theorem CompatibleWithin.one_of_pair
    -- the source system and the target system
    {I : System S}
    {I' : System S'}
    -- `Φ` is strict, `I` is well-formed, and the rules of `I'` are linear
    (hΦ : Φ.Strict)
    (hI : I.WellFormed)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- for every rule of `I` and pairwise distinct names `xs`, `ys` on the ports, the
    -- translations of the two cells, plugged by their roots, leave no cut after one
    -- interaction up to wires
    (hpair : ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
      ∀ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
        (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
        Function.Injective xs → Function.Injective ys → (∀ i j, xs i ≠ ys j) →
        ∀ K, StepE I' {s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} K → ¬ K.HasCut)
    -- `Φ` is compatible with the two systems
    (h : Φ.Compatible I I') :
    -- every rule of `I` is simulated in exactly one interaction, up to wires
    Φ.CompatibleWithin I I' 1 1 := by
  refine CompatibleWithin.of_distinct hI hI' ?_
  intro α β r hr xs ys f g hx hy hxy hl
  obtain ⟨M₁, N', h', hS, hE, hT⟩ := h α β r hr xs ys f g hl
  obtain ⟨n, hn⟩ := hS.exists_stepsEN
  have hn0 : n ≠ 0 := by
    rintro rfl
    rcases hn.cases_head with ⟨-, he⟩ | ⟨K, m, hm, -⟩
    · rw [← he] at hE
      exact not_equiv_pair_of_strict hΦ hI hr hx hy hxy f g hT hE
    · omega
  obtain ⟨-, h1⟩ := hn.eq_one_of_not_hasCut hn0 (hpair α β r hr xs ys f g hx hy hxy)
  exact ⟨M₁, N', h', ⟨1, le_rfl, le_rfl, StepsEN.single h1⟩, hE, hT⟩

-- ============================================================================================
-- 3. Auxiliary lemmas: invertible translations
-- ============================================================================================

/-- **An instance of `Φ(α)` is one cell** (Lafont 1997, page 81, top), when `Φ` is invertible:
there are a symbol `α'` and a bijection `ρ` such that the instance of `Φ(α)` with the names `xs`
on its ports is the cell `α'` with the name `xs (ρ j)` on its auxiliary port `j`. -/
theorem Invertible.inst_eq
    -- `Φ` is invertible, and `α` is a symbol
    (h : Φ.Invertible)
    (α : S.Sym) :
    -- there are a symbol `α'` of `S'` and a bijection `ρ` of the auxiliary ports
    ∃ (α' : S'.Sym) (ρ : Fin (S'.arity α') ≃ Fin (S.arity α)),
      -- such that, for all names `xs` on the ports and `f` on the internal wires, the instance
      -- of `Φ(α)` is the cell `α'` with the name `xs (ρ j)` on its port `j`
      ∀ (xs : Fin (S.arity α) → ℕ) (f : Fin (Φ.net α).internal → ℕ),
        (Φ.net α).inst (fun i => .var (xs i)) f = .app α' fun j => .var (xs (ρ j)) := by
  obtain ⟨α', ρ, hρ⟩ := h.net_eq α
  refine ⟨α', ρ, fun xs f => ?_⟩
  rw [PNet.inst, hρ]
  simp [Term.bind]

/-- An invertible translation is strict (Lafont 1997, page 81): each `Φ(α)` is a cell. -/
theorem Invertible.strict (h : Φ.Invertible) : Φ.Strict := fun α x hx => by
  obtain ⟨α', ρ, hρ⟩ := h.net_eq α
  rw [hρ] at hx
  cases hx

-- ============================================================================================
-- 4. Main result: an invertible translation simulates every rule in one interaction
-- ============================================================================================

/-- **`L = M = 1` if `Φ` is invertible** (Lafont 1997, page 81: "if `Φ` is invertible, the
reduction must be of length 1 … `L = M = 1` if `Φ` is invertible"). Let `Φ` be invertible and
compatible, `I` well-formed and the rules of `I'` linear. Suppose that in `I'`, a pair of two
cells `γ(u) = δ(v)` with pairwise distinct names on its auxiliary ports leaves no cut after one
interaction up to wires (`hpair`; for a literal interaction this is `Rule.not_hasCut_inst`, since
a rule of a well-formed system has a reduced right member). Then every rule of `I` is simulated
in exactly one interaction.

The hypothesis `hpair` is about `I'` alone and is what the paper uses ("its right member, an
instance of a reduced net, has no cut"). It holds when `I'` is well-formed
(`System.WellFormed.stepE_pair_not_hasCut`, in `Translations/PairStepE.lean`). -/
theorem Invertible.compatibleWithin_one
    -- the source system and the target system
    {I : System S}
    {I' : System S'}
    -- `Φ` is invertible, `I` is well-formed, and the rules of `I'` are linear
    (hΦ : Φ.Invertible)
    (hI : I.WellFormed)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- in `I'`, a pair of two cells `γ(u) = δ(v)` with pairwise distinct names on the auxiliary
    -- ports leaves no cut after one interaction up to wires
    (hpair : ∀ (γ δ : S'.Sym) (u : Fin (S'.arity γ) → ℕ) (v : Fin (S'.arity δ) → ℕ),
      Function.Injective u → Function.Injective v → (∀ i j, u i ≠ v j) →
      ∀ K, StepE I' {s(.app γ fun i => .var (u i), .app δ fun j => .var (v j))} K →
        ¬ K.HasCut)
    -- `Φ` is compatible with the two systems
    (h : Φ.Compatible I I') :
    -- every rule of `I` is simulated in exactly one interaction, up to wires
    Φ.CompatibleWithin I I' 1 1 := by
  refine CompatibleWithin.one_of_pair hΦ.strict hI hI' ?_ h
  intro α β r hr xs ys f g hx hy hxy K hK
  obtain ⟨α', ρ, hρ⟩ := hΦ.inst_eq α
  obtain ⟨β', σ, hσ⟩ := hΦ.inst_eq β
  rw [hρ, hσ] at hK
  exact hpair α' β' (fun j => xs (ρ j)) (fun j => ys (σ j)) (hx.comp ρ.injective)
    (hy.comp σ.injective) (fun i j => hxy _ _) K hK

end Translation

end INet
