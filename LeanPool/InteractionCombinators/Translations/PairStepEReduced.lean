/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.PairStepE
public import LeanPool.InteractionCombinators.Translations.TranslationComp
public import LeanPool.InteractionCombinators.Core.Combinators

/-!
# `L = M = 1` for an invertible translation, from linear and reduced rules (page 81)

Lafont 1997, page 81: "if `Φ` is invertible, the reduction must be of length 1 … `L = M = 1` if
`Φ` is invertible", because the right member of a rule of the target, "an instance of a reduced
net, has no cut". The argument uses only that the rules of the target `I'` are linear and that
their right members are reduced.

* `Translation.Invertible.compatibleWithin_one_of_reduced` — the statement with `I.WellFormed`
  and the rules of `I'` linear and reduced, without `I'.WellFormed`.
* `Translation.Invertible.compatibleWithin_one_of_linear_reduced` — the same with only the
  linearity and the reducedness of the rules of `I` too. Of `I.WellFormed`, the proof of
  `Invertible.compatibleWithin_one` uses only these two fields: `linear` in
  `CompatibleWithin.of_distinct` (Proposition 4), `linear` and `reduced` in
  `not_equiv_pair_of_strict` (`L > 0`). The fields `unique` and `symm` are not used.
* `Comb.sysCE` — a check: Lafont's combinators with one more rule `con`–`era`. Its rules are
  linear and reduced, it is not well formed (`sysCE_not_wellFormed`, `unique` fails), and the
  identity translation of the combinators into it has `L = M = 1`
  (`id_compatibleWithin_sysCE`), which `compatibleWithin_one_of_wellFormed` cannot give.

Contents, in the order of the file:

1. Auxiliary lemmas, with only linear or reduced rules:
   `Translation.CompatibleWithin.of_distinct_of_linear` (compatibility for distinct names gives
   it for all names), `Translation.not_equiv_pair_of_strict_of_reduced` (a strict translation
   never simulates an interaction by an empty reduction), `Translation.id_compatible_of_rule`
   (the identity translation into a system with more rules is compatible).
2. Main results: `Translation.Invertible.compatibleWithin_one_of_linear_reduced` (`L = M = 1`
   from linear and reduced rules on both sides) and
   `Translation.Invertible.compatibleWithin_one_of_reduced` (`L = M = 1` with `I` well formed,
   without `I'.WellFormed`), page 81.
3. A check, a system that is not well formed: `Comb.ruleConEraLoop`, `Comb.sysCE`, its rules
   linear and reduced (`sysCE_linear`, `sysCE_reduced`), `sysCE_not_wellFormed`, and
   `Comb.id_compatibleWithin_sysCE`.
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

namespace Translation

variable {Φ : Translation S S'}

-- ============================================================================================
-- 1. Auxiliary lemmas: with only linear or reduced rules
-- ============================================================================================

/-- **Compatibility within `L` and `M` for distinct names gives it for all names**, with only the
rules of `I` linear (Lafont 1997, page 81, the lengths `L`, `M`; page 80). This is
`CompatibleWithin.of_distinct`, whose proof uses only the linearity of the rules of `I`. -/
theorem CompatibleWithin.of_distinct_of_linear
    -- the two systems, and the bounds `L ≤ M` on the length of a simulation
    {I : System S}
    {I' : System S'}
    {L M : ℕ}
    -- the rules of `I` and of `I'` are linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- `Φ` simulates every rule of `I` in `k` interactions of `I'`, `L ≤ k ≤ M`, for distinct
    -- names on the ports
    (h : Φ.CompatibleByDistinct I fun N K => ∃ k, L ≤ k ∧ k ≤ M ∧ StepsEN I' k N K) :
    -- then it does so for all names
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
    (R := fun N K => ∃ k, L ≤ k ∧ k ≤ M ∧ StepsEN I' k N K) hI hI'
    (fun Γ ⟨k, hL, hM, hk⟩ hl => by
      obtain ⟨M', h1, h2, h3⟩ := hk.add_right hI' Γ hl
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2, h3⟩)
    (fun hE ⟨k, hL, hM, hk⟩ => by
      obtain ⟨M', h1, h2⟩ := hk.of_equiv hE
      exact ⟨M', ⟨k, hL, hM, h1⟩, h2⟩)
    (fun ⟨_, _, _, hk⟩ => hk.stepsE) h hstep hT
  rw [add_zero] at hT'
  exact ⟨M₁, M', fun w => k + w, hR, hE, hT'⟩

/-- **A strict translation never simulates an interaction by an empty reduction**, with only the
rule `r` linear and reduced (Lafont 1997, page 81: "`L > 0` if `Φ` is strict"). This is
`not_equiv_pair_of_strict`, whose proof uses only these two properties of the rule. -/
theorem not_equiv_pair_of_strict_of_reduced
    -- the translation is strict
    (hΦ : Φ.Strict)
    -- a linear and reduced rule for two symbols `α`, `β`
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (hrl : r.Linear)
    (hrr : r.Reduced)
    -- distinct names on the ports of the two cells
    {xs : Fin (S.arity α) → ℕ}
    {ys : Fin (S.arity β) → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires of the translations of `α` and `β`
    (f : Fin (Φ.net α).internal → ℕ)
    (g : Fin (Φ.net β).internal → ℕ)
    -- an instance of the rule, and a translation `N'` of it
    {h : Fin r.internal → ℕ}
    {N' : Net S' ℕ}
    (hT : Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    -- the translations of the two cells, plugged by their roots, are not the same graph as `N'`
    ¬ Equiv ({s((Φ.net α).inst (fun i => .var (xs i)) f,
      (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) N' := fun e =>
  Rule.not_hasCut_inst hrl hrr hx hy hxy hT.linear_source
    (hT.hasCut_reflect ((hasCut_pair hΦ α β xs ys f g).of_equiv e))

/-- The identity translation of `I` into a system `I'` that has every rule of `I` is compatible,
when the rules of `I'` are linear. One interaction of `I'` with the same rule simulates each
interaction of `I`. -/
theorem id_compatible_of_rule
    -- two systems on the same signature, every rule of `I` a rule of `I'`
    {I I' : System S}
    (hsub : ∀ α β r, I.rule α β = some r → I'.rule α β = some r)
    -- the rules of `I'` are linear
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear) :
    -- the identity translation is compatible
    (Translation.id S).Compatible I I' := by
  intro α β r hr xs ys f g hlin
  let L : Sym2 (Term S ℕ) := s(.app α fun i => .var (xs i), .app β fun j => .var (ys j))
  let k : ℕ := (Net.vars ({L} : Net S ℕ)).sup + 1
  have hstep : Step I' (L ::ₘ 0)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w) + 0) :=
    Step.mk α β r (hsub _ _ _ hr) _ _ 0 (fun w => k + w)
      (fun a b hab => Fin.ext (by simpa using hab))
      (fun w hw => by
        have hle : k + w ≤ (Net.vars ({L} : Net S ℕ)).sup :=
          Multiset.le_sup (show k + (w : ℕ) ∈ Net.vars ({L} : Net S ℕ) from hw)
        omega)
  have hstep' : Step I' ({L} : Net S ℕ)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w)) := by
    simpa using hstep
  refine ⟨_, _, fun w => k + w, (Steps.single hstep').stepsE, Equiv.refl _, ?_, ?_⟩
  · exact Multiset.rel_refl_of_refl_on fun e _ => eqTr_id e
  · exact hstep'.linear hI' hlin

-- ============================================================================================
-- 2. Main results: `L = M = 1` for an invertible translation
-- ============================================================================================

/-- **`L = M = 1` if `Φ` is invertible, from linear and reduced rules on both sides** (Lafont
1997, page 81: "if `Φ` is invertible, the reduction must be of length 1 … `L = M = 1` if `Φ` is
invertible"; "its right member, an instance of a reduced net, has no cut"). Let `Φ` be invertible
and compatible, and the rules of `I` and of `I'` linear and reduced. Then every rule of `I` is
simulated in exactly one interaction up to wires. Neither system is asked to be well formed: the
fields `unique` and `symm` of `System.WellFormed` are not used. The proof is that of
`CompatibleWithin.one_of_pair` and `Invertible.compatibleWithin_one`, with the pairs of `I'`
handled by `PairStepE.stepE_pair_not_hasCut_of`. -/
theorem Invertible.compatibleWithin_one_of_linear_reduced
    -- the two systems
    {I : System S}
    {I' : System S'}
    -- the translation is invertible
    (hΦ : Φ.Invertible)
    -- the rules of `I` are linear and reduced
    (hIl : ∀ α β r, I.rule α β = some r → r.Linear)
    (hIr : ∀ α β r, I.rule α β = some r → r.Reduced)
    -- the rules of `I'` are linear and reduced
    (hlin : ∀ α β r, I'.rule α β = some r → r.Linear)
    (hred : ∀ α β r, I'.rule α β = some r → r.Reduced)
    -- the translation is compatible
    (h : Φ.Compatible I I') :
    -- it simulates every rule of `I` in exactly one interaction of `I'`
    Φ.CompatibleWithin I I' 1 1 := by
  refine CompatibleWithin.of_distinct_of_linear hIl hlin ?_
  intro α β r hr xs ys f g hx hy hxy hl
  obtain ⟨M₁, N', h', hS, hE, hT⟩ := h α β r hr xs ys f g hl
  obtain ⟨n, hn⟩ := hS.exists_stepsEN
  have hn0 : n ≠ 0 := by
    rintro rfl
    rcases hn.cases_head with ⟨-, he⟩ | ⟨K, m, hm, -⟩
    · rw [← he] at hE
      exact not_equiv_pair_of_strict_of_reduced hΦ.strict (hIl _ _ _ hr) (hIr _ _ _ hr)
        hx hy hxy f g hT hE
    · omega
  have hpair : ∀ K, StepE I' (s((Φ.net α).inst (fun i => .var (xs i)) f,
      (Φ.net β).inst (fun j => .var (ys j)) g) ::ₘ 0) K → ¬ K.HasCut := by
    intro K hK
    obtain ⟨α', ρ, hρ⟩ := hΦ.inst_eq α
    obtain ⟨β', σ, hσ⟩ := hΦ.inst_eq β
    rw [hρ, hσ] at hK
    exact PairStepE.stepE_pair_not_hasCut_of hlin hred (hx.comp ρ.injective)
      (hy.comp σ.injective) (fun i j => hxy _ _) hK
  obtain ⟨-, h1⟩ := hn.eq_one_of_not_hasCut hn0 hpair
  exact ⟨M₁, N', h', ⟨1, le_rfl, le_rfl, StepsEN.single h1⟩, hE, hT⟩

/-- **`L = M = 1` if `Φ` is invertible, without `I'.WellFormed`** (Lafont 1997, page 81: "if `Φ`
is invertible, the reduction must be of length 1 … `L = M = 1` if `Φ` is invertible"; "its right
member, an instance of a reduced net, has no cut"). Let `Φ` be invertible and compatible, `I`
well-formed, and the rules of `I'` linear and reduced. Then `Φ` simulates every rule of `I` in
exactly one interaction up to wires. This is `Invertible.compatibleWithin_one`, with its
hypothesis on the pairs of `I'` given by `PairStepE.stepE_pair_not_hasCut_of`. Of
`I.WellFormed`, only `linear` and `reduced` are used
(`Invertible.compatibleWithin_one_of_linear_reduced`). -/
theorem Invertible.compatibleWithin_one_of_reduced
    -- the two systems
    {I : System S}
    {I' : System S'}
    -- the translation is invertible, and `I` is well formed
    (hΦ : Φ.Invertible)
    (hI : I.WellFormed)
    -- the rules of `I'` are linear and reduced
    (hlin : ∀ α β r, I'.rule α β = some r → r.Linear)
    (hred : ∀ α β r, I'.rule α β = some r → r.Reduced)
    -- the translation is compatible
    (h : Φ.Compatible I I') :
    -- it simulates every rule of `I` in exactly one interaction of `I'`
    Φ.CompatibleWithin I I' 1 1 :=
  hΦ.compatibleWithin_one hI hlin
    (fun _ _ _ _ hu hv huv _ hK => PairStepE.stepE_pair_not_hasCut_of hlin hred hu hv huv hK) h

end Translation

-- ============================================================================================
-- 3. A check: a system that is not well formed
-- ============================================================================================

namespace Comb

/-- A rule `con`–`era` that joins the two auxiliary ports of the `con` cell. -/
def ruleConEraLoop : Rule sig 2 0 := ⟨0, {s(.var (.inl 0), .var (.inl 1))}⟩

/-- Lafont's combinators with one more rule, `con`–`era` (`ruleConEraLoop`). Since `era`–`con` is
already a rule, this system is not well formed (page 73: "no other rule is given for `α_j`,
`α_i`"), but each of its rules is linear and reduced. -/
def sysCE : System sig where
  rule
    | .con, .era => some ruleConEraLoop
    | α, β => system.rule α β

-- the rule `con`–`era` is linear and reduced
theorem ruleConEraLoop_linear : ruleConEraLoop.Linear :=
  ⟨by decide, by decide, by decide⟩

theorem ruleConEraLoop_reduced : ruleConEraLoop.Reduced := by
  intro e he
  rw [show e = s(.var (.inl 0), .var (.inl 1)) from Multiset.mem_singleton.1 he]
  exact ⟨_, _, rfl, fun w => by simp⟩

-- every rule of the combinators is a rule of `sysCE`
theorem sysCE_rule_of_system :
    ∀ α β r, system.rule α β = some r → sysCE.rule α β = some r := by
  intro α β r h
  cases α <;> cases β <;> first | exact h | cases h

-- the rules of `sysCE` are linear and reduced
theorem sysCE_linear : ∀ α β r, sysCE.rule α β = some r → r.Linear := by
  intro α β r h
  cases α <;> cases β
  case con.era => cases h; exact ruleConEraLoop_linear
  all_goals exact system_wellFormed.linear _ _ _ h

theorem sysCE_reduced : ∀ α β r, sysCE.rule α β = some r → r.Reduced := by
  intro α β r h
  cases α <;> cases β
  case con.era => cases h; exact ruleConEraLoop_reduced
  all_goals exact system_wellFormed.reduced _ _ _ h

/-- `sysCE` is not well formed: it has both a rule `era`–`con` and a rule `con`–`era`, so
`unique` fails (page 73). -/
theorem sysCE_not_wellFormed : ¬ sysCE.WellFormed := fun h =>
  absurd (h.unique Comb.era Comb.con (fun e => by cases e) rfl) (by simp [sysCE])

/-- **`L = M = 1` into a system that is not well formed** (Lafont 1997, page 81). The identity
translation of Lafont's combinators into `sysCE` is invertible and compatible, and
`Translation.Invertible.compatibleWithin_one_of_reduced` gives that it simulates every rule in
exactly one interaction up to wires. Since `sysCE` is not well formed (`sysCE_not_wellFormed`),
`Invertible.compatibleWithin_one_of_wellFormed` does not apply here. -/
theorem id_compatibleWithin_sysCE :
    -- the identity simulates each rule of the combinators in one interaction of `sysCE`,
    (Translation.id sig).CompatibleWithin system sysCE 1 1 ∧
    -- and `sysCE` is not well formed
    ¬ sysCE.WellFormed :=
  ⟨(Translation.invertible_id sig).compatibleWithin_one_of_reduced system_wellFormed
    sysCE_linear sysCE_reduced
    (Translation.id_compatible_of_rule sysCE_rule_of_system sysCE_linear),
    sysCE_not_wellFormed⟩

end Comb

end INet
