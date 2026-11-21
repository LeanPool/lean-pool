/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.RenameMany
public import LeanPool.InteractionCombinators.Text.RenameStep
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
import LeanPool.InteractionCombinators.Core.Combinators

/-!
# Two interactions on disjoint active pairs commute

Proposition 1 (Lafont 1997, page 73): reduction in an interaction system is strongly confluent.
Its proof has two cases. If the two interactions fire two different active pairs, the pairs are
disjoint and the interactions commute. This file is that case (`Step.commute`); the case where the
same active pair is fired is not treated here.

Contents, in the order of the file:

1. Auxiliary lemmas on the instances of a rule, and a bound on names: `Rule.mem_vars_inst`;
   `Rule.facts_of_linear`, in a linear net the internal wires of an instance of a linear rule
   have distinct names, used nowhere else; `Rule.equiv_inst`, the names of these wires do not
   matter; `Net.exists_below`.
2. Main result: `Step.commute`, after firing one of two active pairs, the other can still be
   fired, and both orders give the same net up to wires.
3. Examples showing that the hypotheses of `Step.commute` can hold, in the combinators.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: the instances of a rule, and a bound on names
-- ============================================================================================

namespace Rule

variable {a b : ℕ}

/-- A name of an instance of a rule is a name of a tree plugged into a port, or one of the wires
created by the rule. -/
theorem mem_vars_inst
    -- the rule and its instance: the trees on the ports, the names of the new wires
    {r : Rule S a b}
    {as : Fin a → Term S ℕ}
    {bs : Fin b → Term S ℕ}
    {f : Fin r.internal → ℕ}
    -- a name of the instance
    {x : ℕ}
    (hx : x ∈ (r.inst as bs f).vars) :
    -- it is a name of a tree on a port of the first cell,
    (∃ i, x ∈ (as i).vars)
      -- or of a tree on a port of the second cell,
      ∨ (∃ j, x ∈ (bs j).vars)
      -- or the name of a new wire
      ∨ ∃ w, x = f w := by
  rw [inst, Net.vars_bind, Multiset.mem_bind] at hx
  obtain ⟨p, -, hp⟩ := hx
  rcases p with i | j | w
  · exact Or.inl ⟨i, hp⟩
  · exact Or.inr (Or.inl ⟨j, hp⟩)
  · exact Or.inr (Or.inr ⟨w, by simpa using hp⟩)

/-- In a linear net, the internal wires of an instance of a linear rule have pairwise distinct
names, which occur in no tree plugged into the ports and nowhere in the rest of the net
(Lafont 1997, page 72: the wires created by an interaction are new). -/
theorem facts_of_linear
    -- a linear rule
    (r : Rule S a b)
    (hr : r.Linear)
    -- its instance: the trees on the ports, the names of the new wires
    {as : Fin a → Term S ℕ}
    {bs : Fin b → Term S ℕ}
    {f : Fin r.internal → ℕ}
    -- the rest of the net
    {Γ : Net S ℕ}
    -- the net is linear
    (hlin : (r.inst as bs f + Γ).Linear) :
    -- the new wires have distinct names,
    Function.Injective f
      -- and for each new wire `w`:
      ∧ ∀ w,
        -- its name is in no tree on a port of the first cell,
        (∀ i, f w ∉ (as i).vars)
        -- nor of the second cell,
        ∧ (∀ j, f w ∉ (bs j).vars)
        -- nor in the rest of the net,
        ∧ f w ∉ Γ.vars
        -- and it occurs exactly twice in the net
        ∧ (r.inst as bs f + Γ).vars.count (f w) = 2 := by
  have key : ∀ w, ∑ i, (as i).vars.count (f w) + ∑ j, (bs j).vars.count (f w) +
      2 * (∑ w', if f w = f w' then 1 else 0) + Γ.vars.count (f w) ≤ 2 := by
    intro w
    have := hlin (f w)
    simpa only [Net.vars_add, Multiset.count_add, count_vars_inst r hr] using this
  have one : ∀ w, 1 ≤ ∑ w', if f w = f w' then 1 else 0 := fun w =>
    calc 1 = if f w = f w then 1 else 0 := (ite_eq_left rfl).symm
      _ ≤ ∑ w', if f w = f w' then 1 else 0 :=
        Finset.single_le_sum (f := fun w' => if f w = f w' then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  have hinj : Function.Injective f := by
    intro w₀ w₁ heq
    by_contra hne
    have h2 : ∑ w' ∈ ({w₀, w₁} : Finset _), (if f w₀ = f w' then 1 else 0) ≤
        ∑ w', if f w₀ = f w' then 1 else 0 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne] at h2
    simp only [heq, ite_true] at h2
    have := key w₀
    simp only [heq] at this
    omega
  have hsum : ∀ w, (∑ w', if f w = f w' then 1 else 0) = 1 := by
    intro w
    rw [Finset.sum_eq_single w]
    · simp
    · intro w' _ hw'
      exact ite_eq_right fun h => hw' (hinj h).symm
    · simp
  refine ⟨hinj, fun w => ⟨fun i => ?_, fun j => ?_, ?_, ?_⟩⟩
  · refine Multiset.count_eq_zero.1 ?_
    have hle : (as i).vars.count (f w) ≤ ∑ i, (as i).vars.count (f w) :=
      Finset.single_le_sum (f := fun i => (as i).vars.count (f w))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := key w; have := one w; omega
  · refine Multiset.count_eq_zero.1 ?_
    have hle : (bs j).vars.count (f w) ≤ ∑ j, (bs j).vars.count (f w) :=
      Finset.single_le_sum (f := fun j => (bs j).vars.count (f w))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have := key w; have := one w; omega
  · exact Multiset.count_eq_zero.1 (by have := key w; have := one w; omega)
  · have := key w
    rw [hsum w] at this
    rw [Net.vars_add, Multiset.count_add, count_vars_inst r hr, hsum w]
    omega

/-- **The names of the internal wires of an instance do not matter.** In a linear net, renaming
the wires created by an instance of a linear rule to distinct unused names gives the same graph
(Lafont 1997, pages 70 to 72: a net is a graph, and the right-hand side of a rule is a net whose
internal wires are new). -/
theorem equiv_inst
    -- a linear rule
    (r : Rule S a b)
    (hr : r.Linear)
    -- the trees on the ports of the instance
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- the old and the new names of the new wires
    (f f' : Fin r.internal → ℕ)
    -- the rest of the net
    (Γ : Net S ℕ)
    -- the net with the old names is linear
    (hlin : (r.inst as bs f + Γ).Linear)
    -- the new names are distinct, and unused in that net
    (hf' : Function.Injective f')
    (hfresh : ∀ w, f' w ∉ (r.inst as bs f + Γ).vars) :
    -- the two nets are the same graph
    Equiv (r.inst as bs f + Γ) (r.inst as bs f' + Γ) := by
  obtain ⟨hf, hff⟩ := r.facts_of_linear hr hlin
  classical
  let φ : ℕ → ℕ := fun x => if h : ∃ w, f w = x then f' h.choose else x
  have hφf : ∀ w, φ (f w) = f' w := by
    intro w
    have h : ∃ w', f w' = f w := ⟨w, rfl⟩
    simp only [φ, dite_eq_left h]
    rw [hf h.choose_spec]
  have hφx : ∀ x, (∀ w, f w ≠ x) → φ x = x := by
    intro x hx
    simp only [φ, dite_eq_right (not_exists.2 hx)]
  have E := Net.equiv_bind_var hlin φ
    (by
      intro x hx y hy hxy
      have hx : x ∈ (r.inst as bs f + Γ).vars := hx
      have hy : y ∈ (r.inst as bs f + Γ).vars := hy
      by_cases hxr : ∃ w, f w = x <;> by_cases hyr : ∃ w, f w = y
      · obtain ⟨w, rfl⟩ := hxr
        obtain ⟨w', rfl⟩ := hyr
        rw [hφf, hφf] at hxy
        rw [hf' hxy]
      · obtain ⟨w, rfl⟩ := hxr
        rw [hφf, hφx y (not_exists.1 hyr)] at hxy
        exact absurd (hxy ▸ hy) (hfresh w)
      · obtain ⟨w', rfl⟩ := hyr
        rw [hφf, hφx x (not_exists.1 hxr)] at hxy
        exact absurd (hxy ▸ hx) (hfresh w')
      · rwa [hφx x (not_exists.1 hxr), hφx y (not_exists.1 hyr)] at hxy)
    (by
      intro x hx
      refine hφx x fun w hw => ?_
      have := (hff w).2.2.2
      rw [hw, hx] at this
      omega)
  refine E.trans (Equiv.of_eq ?_)
  rw [Net.bind_add, Rule.inst_bind_var]
  have hΓ : Γ.bind (fun y => Term.var (φ y)) = Γ := by
    conv_rhs => rw [← Net.bind_var_self Γ]
    refine Net.bind_congr fun x hx => ?_
    rw [hφx x fun w hw => (hff w).2.2.1 (hw ▸ hx)]
  have has : ∀ i, (as i).bind (fun y => Term.var (φ y)) = as i := by
    intro i
    conv_rhs => rw [← Term.bind_var_self (as i)]
    refine Term.bind_congr fun x hx => ?_
    rw [hφx x fun w hw => (hff w).1 i (hw ▸ hx)]
  have hbs : ∀ j, (bs j).bind (fun y => Term.var (φ y)) = bs j := by
    intro j
    conv_rhs => rw [← Term.bind_var_self (bs j)]
    refine Term.bind_congr fun x hx => ?_
    rw [hφx x fun w hw => (hff w).2.1 j (hw ▸ hx)]
  simp only [has, hbs, hφf, hΓ]

end Rule

/-- Every net has a bound on its names: the names from some `K` on are unused. -/
theorem Net.exists_below
    (N : Net S ℕ) :
    ∃ K, N.Below K :=
  ⟨N.vars.sup + 1, fun _ hx => Nat.lt_succ_of_le (Multiset.le_sup hx)⟩

-- ============================================================================================
-- 2. Main result: two interactions on disjoint active pairs commute
-- ============================================================================================

/-- **Two interactions on disjoint active pairs commute** (Lafont 1997, Proposition 1, page 73,
the case of two different active pairs). In a linear net with two active pairs
`α(as) = β(bs)` and `γ(cs) = δ(ds)`, fire the first one (its new wires named by `f`) or the second
one (its new wires named by `g`). Each result can then fire the other pair, by one literal
interaction, and the two final nets are the same graph. -/
theorem Step.commute
    -- an interaction system whose rules are linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- the symbols of the two active pairs, `α`–`β` and `γ`–`δ`, and their rules
    {α β γ δ : S.Sym}
    {r₁ : Rule S (S.arity α) (S.arity β)}
    {r₂ : Rule S (S.arity γ) (S.arity δ)}
    (hr₁ : I.rule α β = some r₁)
    (hr₂ : I.rule γ δ = some r₂)
    -- the trees on the auxiliary ports of the four cells
    (as : Fin (S.arity α) → Term S ℕ)
    (bs : Fin (S.arity β) → Term S ℕ)
    (cs : Fin (S.arity γ) → Term S ℕ)
    (ds : Fin (S.arity δ) → Term S ℕ)
    -- the rest of the net
    (Δ : Net S ℕ)
    -- the net with the two active pairs is linear
    (hN : Net.Linear
      (s(Term.app α as, Term.app β bs) ::ₘ s(Term.app γ cs, Term.app δ ds) ::ₘ Δ))
    -- the names `f` of the wires created by the first interaction: distinct and unused
    (f : Fin r₁.internal → ℕ)
    (hf : Function.Injective f)
    (hffresh : ∀ i, f i ∉
      Net.vars (s(Term.app α as, Term.app β bs) ::ₘ s(Term.app γ cs, Term.app δ ds) ::ₘ Δ))
    -- the names `g` of the wires created by the second interaction: distinct and unused
    (g : Fin r₂.internal → ℕ)
    (hg : Function.Injective g)
    (hgfresh : ∀ i, g i ∉
      Net.vars (s(Term.app γ cs, Term.app δ ds) ::ₘ s(Term.app α as, Term.app β bs) ::ₘ Δ)) :
    -- there are two nets `P₁` and `P₂` such that
    ∃ P₁ P₂,
      -- the net where the first pair has fired reduces, by firing the second, to `P₁`,
      Step I (r₁.inst as bs f + (s(Term.app γ cs, Term.app δ ds) ::ₘ Δ)) P₁
      -- the net where the second pair has fired reduces, by firing the first, to `P₂`,
      ∧ Step I (r₂.inst cs ds g + (s(Term.app α as, Term.app β bs) ::ₘ Δ)) P₂
      -- and `P₁` and `P₂` are the same graph
      ∧ Equiv P₁ P₂ := by
  have hgN := fun w => hgfresh w
  simp only [Net.vars_cons, eqVars_mk, vars_app, Multiset.mem_add, Multiset.mem_sum,
    Finset.mem_univ, true_and, not_or, not_exists] at hgN
  set e₁ : Sym2 (Term S ℕ) := s(Term.app α as, Term.app β bs)
  set e₂ : Sym2 (Term S ℕ) := s(Term.app γ cs, Term.app δ ds)
  set N : Net S ℕ := e₁ ::ₘ e₂ ::ₘ Δ
  have hN' : (e₂ ::ₘ e₁ ::ₘ Δ) = N := Multiset.cons_swap _ _ _
  have h₁ : Step I N (r₁.inst as bs f + (e₂ ::ₘ Δ)) :=
    Step.mk α β r₁ hr₁ as bs (e₂ ::ₘ Δ) f hf hffresh
  have h₂ : Step I N (r₂.inst cs ds g + (e₁ ::ₘ Δ)) := by
    rw [← hN']
    exact Step.mk γ δ r₂ hr₂ cs ds (e₁ ::ₘ Δ) g hg hgfresh
  set M₁ := r₁.inst as bs f + (e₂ ::ₘ Δ)
  set M₂ := r₂.inst cs ds g + (e₁ ::ₘ Δ)
  have L₁ : M₁.Linear := h₁.linear hI hN
  have L₂ : M₂.Linear := h₂.linear hI hN
  -- a block of names above every name of `M₁` and `M₂`
  obtain ⟨K, hK⟩ := Net.exists_below (M₁ + M₂)
  have hK₁ : ∀ x ∈ M₁.vars, x < K := fun x hx => hK x (by simp [hx])
  have hK₂ : ∀ x ∈ M₂.vars, x < K := fun x hx => hK x (by simp [hx])
  let n₂ := r₂.internal
  let g' : Fin r₂.internal → ℕ := fun w => K + w
  let f' : Fin r₁.internal → ℕ := fun w => K + n₂ + w
  have hg' : Function.Injective g' := fun w w' h => Fin.ext (by simpa [g'] using h)
  have hf' : Function.Injective f' := fun w w' h => Fin.ext (by simpa [f'] using h)
  -- names of the trees of the two active pairs
  have hcs₁ : ∀ i, ∀ x ∈ (cs i).vars, x ∈ M₁.vars := fun i x hx => by
    simp only [M₁, e₂, Net.vars_add, Net.vars_cons, eqVars_mk, vars_app, Multiset.mem_add,
      Multiset.mem_sum, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl (Or.inl ⟨i, hx⟩))
  have hds₁ : ∀ j, ∀ x ∈ (ds j).vars, x ∈ M₁.vars := fun j x hx => by
    simp only [M₁, e₂, Net.vars_add, Net.vars_cons, eqVars_mk, vars_app, Multiset.mem_add,
      Multiset.mem_sum, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl (Or.inr ⟨j, hx⟩))
  have hgM₂ : ∀ w, g w ∈ M₂.vars := fun w =>
    Multiset.one_le_count_iff_mem.1
      (by rw [show M₂.vars.count (g w) = 2 from
            ((r₂.facts_of_linear (hI _ _ _ hr₂) L₂).2 w).2.2.2]; omega)
  -- the second pair fires after the first
  have s₁ : Step I M₁ (r₂.inst cs ds g' + (r₁.inst as bs f + Δ)) := by
    have := Step.mk γ δ r₂ hr₂ cs ds (r₁.inst as bs f + Δ) g' hg' (fun w hw => by
      have hw' : g' w ∈ M₁.vars := by
        simp only [M₁, Net.vars_add, Net.vars_cons, Multiset.mem_add] at hw ⊢
        tauto
      have := hK₁ _ hw'
      simp [g'] at this)
    have e : (s(Term.app γ cs, Term.app δ ds) ::ₘ (r₁.inst as bs f + Δ)) = M₁ := by
      simp only [M₁, e₂, Multiset.add_cons]
    rwa [e] at this
  -- the first pair fires after the second
  have s₂ : Step I M₂ (r₁.inst as bs f' + (r₂.inst cs ds g + Δ)) := by
    have := Step.mk α β r₁ hr₁ as bs (r₂.inst cs ds g + Δ) f' hf' (fun w hw => by
      have hw' : f' w ∈ M₂.vars := by
        simp only [M₂, Net.vars_add, Net.vars_cons, Multiset.mem_add] at hw ⊢
        tauto
      have := hK₂ _ hw'
      simp [f'] at this
      omega)
    have e : (s(Term.app α as, Term.app β bs) ::ₘ (r₂.inst cs ds g + Δ)) = M₂ := by
      simp only [M₂, e₁, Multiset.add_cons]
    rwa [e] at this
  refine ⟨_, _, s₁, s₂, ?_⟩
  -- rename the wires `f` to `f'`, then the wires `g'` to `g`
  have LP₁ := s₁.linear hI L₁
  have e₃ : r₂.inst cs ds g' + (r₁.inst as bs f + Δ) =
      r₁.inst as bs f + (r₂.inst cs ds g' + Δ) := add_left_comm _ _ _
  rw [e₃] at LP₁ ⊢
  have E₁ := r₁.equiv_inst (hI _ _ _ hr₁) as bs f f' _ LP₁ hf' (fun w hw => by
    rw [Net.vars_add, Multiset.mem_add, Net.vars_add, Multiset.mem_add] at hw
    rcases hw with hw | hw | hw
    · have hM : f' w ∈ M₁.vars := by simp [M₁, hw]
      have := hK₁ _ hM
      simp [f'] at this
      omega
    · rcases Rule.mem_vars_inst hw with ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨w', hw'⟩
      · have := hK₁ _ (hcs₁ i _ hi); simp [f'] at this; omega
      · have := hK₁ _ (hds₁ j _ hj); simp [f'] at this; omega
      · simp only [f', g'] at hw'; omega
    · have hM : f' w ∈ M₁.vars := by simp [M₁, hw]
      have := hK₁ _ hM
      simp [f'] at this
      omega)
  have LQ := E₁.linear LP₁
  have e₄ : r₁.inst as bs f' + (r₂.inst cs ds g' + Δ) =
      r₂.inst cs ds g' + (r₁.inst as bs f' + Δ) := add_left_comm _ _ _
  rw [e₄] at LQ E₁
  have E₂ := r₂.equiv_inst (hI _ _ _ hr₂) cs ds g' g _ LQ hg (fun w hw => by
    have hgK := hK₂ _ (hgM₂ w)
    rw [Net.vars_add, Multiset.mem_add, Net.vars_add, Multiset.mem_add] at hw
    rcases hw with hw | hw | hw
    · rcases Rule.mem_vars_inst hw with ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨w', hw'⟩
      · exact (hgN w).1.1 i hi
      · exact (hgN w).1.2 j hj
      · simp only [g'] at hw'; omega
    · rcases Rule.mem_vars_inst hw with ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨w', hw'⟩
      · exact (hgN w).2.1.1 i hi
      · exact (hgN w).2.1.2 j hj
      · simp only [f'] at hw'; omega
    · exact (hgN w).2.2 hw)
  refine E₁.trans (E₂.trans (Equiv.of_eq (add_left_comm _ _ _)))

-- ============================================================================================
-- 3. The hypotheses can hold
-- ============================================================================================

section Example

open Comb

/-- Non-vacuity, in the combinators: a `con`–`con` pair and an `era`–`era` pair. Both orders of
reduction meet. -/
example :
    ∃ P₁ P₂,
      -- after the `con`–`con` interaction, the `era`–`era` one fires
      Step system
        (ruleConCon.inst ![var 0, var 1] ![var 2, var 3] Fin.elim0
          + (s(mkEra, mkEra) ::ₘ 0)) P₁
      -- after the `era`–`era` interaction, the `con`–`con` one fires
      ∧ Step system
        (ruleEraEra.inst ![] ![] Fin.elim0
          + (s(mkCon (var 0) (var 1), mkCon (var 2) (var 3)) ::ₘ 0)) P₂
      -- and both orders meet
      ∧ Equiv P₁ P₂ := by
  refine Step.commute (I := system) (α := con) (β := con) (γ := era) (δ := era)
    system_wellFormed.linear rfl rfl ![var 0, var 1] ![var 2, var 3] ![] ![] 0 ?_
    Fin.elim0 (fun i => i.elim0) (fun i => i.elim0) Fin.elim0 (fun i => i.elim0)
    (fun i => i.elim0)
  have distinct : (Net.vars (s(mkCon (var 0) (var 1), mkCon (var 2) (var 3)) ::ₘ
      s(mkEra, mkEra) ::ₘ 0)).Nodup := by decide
  exact fun y => (Multiset.nodup_iff_count_le_one.mp distinct y).trans (by decide)

/-- Non-vacuity where the new wires clash: two `con`–`dup` pairs, each creating four wires, both
named `10, 11, 12, 13`. After one interaction these names are in use, and the other interaction
has to pick new ones. Both orders of reduction still meet. -/
example :
    ∃ P₁ P₂,
      -- after the first `con`–`dup` interaction, the second one fires
      Step system
        (ruleConDup.inst ![var 0, var 1] ![var 2, var 3] ![10, 11, 12, 13]
          + (s(mkCon (var 4) (var 5), mkDup (var 6) (var 7)) ::ₘ 0)) P₁
      -- after the second `con`–`dup` interaction, the first one fires
      ∧ Step system
        (ruleConDup.inst ![var 4, var 5] ![var 6, var 7] ![10, 11, 12, 13]
          + (s(mkCon (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ 0)) P₂
      -- and both orders meet
      ∧ Equiv P₁ P₂ := by
  have hinj : Function.Injective (![10, 11, 12, 13] : Fin 4 → ℕ) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  refine Step.commute (I := system) (α := con) (β := dup) (γ := con) (δ := dup)
    system_wellFormed.linear rfl rfl ![var 0, var 1] ![var 2, var 3] ![var 4, var 5]
    ![var 6, var 7] 0 ?_ ![10, 11, 12, 13] hinj ?_ ![10, 11, 12, 13] hinj ?_
  · have distinct : (Net.vars (s(mkCon (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ
        s(mkCon (var 4) (var 5), mkDup (var 6) (var 7)) ::ₘ 0)).Nodup := by decide
    exact fun y => (Multiset.nodup_iff_count_le_one.mp distinct y).trans (by decide)
  · intro i
    change _ ∉ Net.vars (s(mkCon (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ
      s(mkCon (var 4) (var 5), mkDup (var 6) (var 7)) ::ₘ 0)
    fin_cases i <;>
      simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkCon, vars_mkDup, vars_var] <;>
      decide
  · intro i
    change _ ∉ Net.vars (s(mkCon (var 4) (var 5), mkDup (var 6) (var 7)) ::ₘ
      s(mkCon (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ 0)
    fin_cases i <;>
      simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkCon, vars_mkDup, vars_var] <;>
      decide

end Example

end INet
