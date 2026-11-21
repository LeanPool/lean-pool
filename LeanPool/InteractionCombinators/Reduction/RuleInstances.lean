/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduction.Commute

/-!
# Instances of a rule: the same active pair fired twice

Lafont 1997, Proposition 1, page 73: "If a net N reduces in one step to P and to P′, with P ≠ P′,
then P and P′ reduce in one step to a common Q."

`InteractionCombinators/Reduction/Commute.lean` treats two interactions on different active pairs
(`Step.commute`). This file gives the lemmas about instances of a rule needed for the same active
pair fired twice; the proposition itself is assembled in
`InteractionCombinators/Reduction/StrongConfluence.lean` (`Step.strong_confluence`).

The same active pair can be fired in two ways that differ in the text:
* the new wires may get different names (`Rule.equiv_inst_same`);
* the equation `α(as) = α(bs)` is unordered, so a rule `r` of `α` with itself can be read with
  `as` and `bs` exchanged. The two results are the same graph because `r` is symmetric
  (`System.WellFormed.symm`, page 73: "the rule for α, α must be symmetric"). The symmetry is up
  to a permutation of the internal wires; it is treated in
  `Universality/RecursionFree/SymmPerm.lean` (`Rule.equiv_inst_comm_of_symmPerm`), which
  `Rule.equiv_inst_swap` in `StrongConfluence.lean` uses.

The tool for the second point is `Rule.equiv_bind_args`: plugging trees into the auxiliary ports
of two equivalent right-hand sides gives equivalent nets.

Contents, in the order of the file:

1. Definitions: `Rule.args`, the trees plugged into the names of a right-hand side;
   `Rule.PortShape`, the shape of a right-hand side up to wires.
2. Auxiliary lemmas: `Rule.inst_eq_bind`; `Term.bind_subst` and `Wire.bind_add` (a wire
   substitution survives plugging trees into the names); `Rule.PortShape.of_equiv`,
   `Rule.count_vars_bind_args_le`, `Rule.equiv_bind_args` (equivalent right-hand sides give
   equivalent instances), `Rule.portShape_net`; `Rule.linear_inst_add`,
   `Rule.equiv_inst_of_linear` (the names of the new wires do not matter), `Rule.swap_inst`.
3. Main result: `Rule.equiv_inst_same` (the same active pair fired twice, the same way).
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace Rule

variable {a b k : ℕ}

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- The trees plugged into the names of a right-hand side: `as` into the ports of the first cell,
`bs` into the ports of the second, and the name `f w` into the internal wire `w`. -/
def args
    -- the trees on the ports of the first cell, and on those of the second
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- the names of the internal wires
    (f : Fin k → ℕ) :
    Fin a ⊕ Fin b ⊕ Fin k → Term S ℕ :=
  Sum.elim as (Sum.elim bs fun w => var (f w))

/-- The shape of a right-hand side up to wires: linear, with each auxiliary port of the two cells
occurring once. Internal wires occur twice or not at all. -/
def PortShape
    -- a net over the ports of the two cells and `k` internal wires
    (K : Net S (Fin a ⊕ Fin b ⊕ Fin k)) :
    Prop :=
  K.Linear ∧ (∀ i, K.vars.count (.inl i) = 1) ∧ (∀ j, K.vars.count (.inr (.inl j)) = 1)

-- ============================================================================================
-- 2. Auxiliary lemmas
-- ============================================================================================

/-- An instance of a rule is its right-hand side with the trees `args as bs f` plugged into its
names. -/
theorem inst_eq_bind
    -- the rule
    (r : Rule S a b)
    -- the trees on the ports and the names of the new wires
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    (f : Fin r.internal → ℕ) :
    r.inst as bs f = r.net.bind (args as bs f) := rfl

end Rule

/-- Plugging trees into the names of a tree commutes with plugging `t` into `x`, when `x` is sent
to a name `n` that occurs in the image of no other name of the tree. -/
theorem Term.bind_subst
    -- the trees plugged into the names, `x` being sent to the name `n`
    {ν : Type}
    [DecidableEq ν]
    (σ : ν → Term S ℕ)
    {x : ν}
    {n : ℕ}
    (hn : σ x = var n)
    -- the tree plugged into `x`
    (t : Term S ν) :
    -- for every tree `r` in which `n` comes from no name other than `x`,
    ∀ r : Term S ν, (∀ y ∈ r.vars, y ≠ x → n ∉ (σ y).vars) →
      -- substituting `t` for `x`, then plugging, is plugging, then substituting for `n`
      (r.subst x t).bind σ = (r.bind σ).subst n (t.bind σ)
  | var y, h => by
    by_cases hy : y = x
    · subst hy
      simp [Term.subst, hn]
    · have := h y (by simp) hy
      simp only [Term.subst, bind_var, ite_eq_right hy]
      exact (subst_of_notMem this).symm
  | app α ts, h => by
    simp only [Term.subst, bind_app] at *
    congr 1
    funext i
    exact Term.bind_subst σ hn t (ts i) fun y hy => h y
      (by simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨i, hy⟩)

/-- A wire substitution stays a wire substitution after plugging trees into the names and adding a
context, provided every internal wire is sent to a name and the result is linear. -/
theorem Wire.bind_add
    -- a wire substitution from `N` to `M`
    {ν : Type}
    [DecidableEq ν]
    {N M : Net S ν}
    (h : Wire N M)
    -- the trees plugged into the names
    (σ : ν → Term S ℕ)
    -- the rest of the net
    (Δ : Net S ℕ)
    -- every internal wire of `N` is sent to a name
    (hσ : ∀ x, N.vars.count x = 2 → ∃ n, σ x = var n)
    -- the net obtained from `N` is linear
    (hlin : (N.bind σ + Δ).Linear) :
    Wire (N.bind σ + Δ) (M.bind σ + Δ) := by
  obtain ⟨x, t, a, b, Δ₀, hlinN, hx⟩ := h
  set N : Net S ν := s(var x, t) ::ₘ s(a, b) ::ₘ Δ₀ with hNdef
  have hc : N.vars.count x = 2 := by
    have h2 := hlinN x
    have h1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
    simp only [N, Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at h2 h1 ⊢
    omega
  obtain ⟨n, hn⟩ := hσ x hc
  -- `n` occurs in the image of no other name
  have hfr : ∀ y ∈ N.vars, y ≠ x → n ∉ (σ y).vars := by
    intro y hy hyx hny
    have hle : x ::ₘ x ::ₘ {y} ≤ N.vars := by
      rw [Multiset.le_iff_count]
      intro z
      by_cases hzx : z = x
      · subst hzx
        rw [Multiset.count_cons_self, Multiset.count_cons_self,
          Multiset.count_singleton, ite_eq_right (Ne.symm hyx), hc]
      · rw [Multiset.count_cons_of_ne hzx, Multiset.count_cons_of_ne hzx,
          Multiset.count_singleton]
        split_ifs with hzy
        · subst hzy; exact Multiset.one_le_count_iff_mem.2 hy
        · exact Nat.zero_le _
    obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.1 hle
    have h2 := hlin n
    rw [Net.vars_add, Net.vars_bind, hR, Multiset.add_bind] at h2
    simp only [Multiset.cons_bind, Multiset.singleton_bind, hn, vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at h2
    have := Multiset.one_le_count_iff_mem.2 hny
    omega
  have hmem : ∀ y ∈ a.vars + b.vars, y ∈ N.vars := fun y hy => by
    simp only [N, Net.vars_cons, eqVars_mk, Multiset.mem_add] at hy ⊢
    tauto
  have ha := Term.bind_subst σ hn t a fun y hy => hfr y (hmem y (by simp [hy]))
  have hb := Term.bind_subst σ hn t b fun y hy => hfr y (hmem y (by simp [hy]))
  have hx' : n ∈ (a.bind σ).vars + (b.bind σ).vars := by
    rw [vars_bind, vars_bind, ← Multiset.add_bind, Multiset.mem_bind]
    exact ⟨x, hx, by simp [hn]⟩
  have e : N.bind σ + Δ = s(var n, t.bind σ) ::ₘ s(a.bind σ, b.bind σ) ::ₘ (Δ₀.bind σ + Δ) := by
    simp [N, Net.bind, hn]
  have e' : Net.bind σ (s(a.subst x t, b.subst x t) ::ₘ Δ₀) + Δ =
      s((a.bind σ).subst n (t.bind σ), (b.bind σ).subst n (t.bind σ)) ::ₘ (Δ₀.bind σ + Δ) := by
    simp [Net.bind, ha, hb]
  rw [e, e']
  exact Wire.mk n _ _ _ _ (hlin.cast e) hx'

namespace Rule

variable {a b k : ℕ}

/-- The shape of a right-hand side is kept by `Equiv`. -/
theorem PortShape.of_equiv
    -- two nets over the same ports and internal wires, the same graph
    {K L : Net S (Fin a ⊕ Fin b ⊕ Fin k)}
    (h : Equiv K L)
    -- the first has the shape of a right-hand side
    (hK : PortShape K) :
    PortShape L :=
  ⟨h.linear hK.1, fun i => (h.free_iff _).1 (hK.2.1 i), fun j => (h.free_iff _).1 (hK.2.2 j)⟩

/-- The names of an instance of a net of the shape of a right-hand side are bounded by those of
the trees plugged into the ports and two ends for each internal wire. -/
theorem count_vars_bind_args_le
    -- a net of the shape of a right-hand side
    {K : Net S (Fin a ⊕ Fin b ⊕ Fin k)}
    (hK : PortShape K)
    -- the trees on the ports and the names of the internal wires
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    (f : Fin k → ℕ)
    -- a name
    (y : ℕ) :
    -- `y` occurs at most as often as in the trees, plus twice for each internal wire named `y`
    (K.bind (args as bs f)).vars.count y
      ≤ ∑ i, (as i).vars.count y + ∑ j, (bs j).vars.count y
        + 2 * ∑ w, if y = f w then 1 else 0 := by
  rw [Net.vars_bind, Multiset.count_bind_fintype, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [hK.2.1, hK.2.2, one_mul, args, Sum.elim_inl, Sum.elim_inr, vars_var,
    Multiset.count_singleton, Finset.mul_sum]
  have : ∑ w, K.vars.count (.inr (.inr w)) * (if y = f w then 1 else 0) ≤
      ∑ w, 2 * (if y = f w then 1 else 0) :=
    Finset.sum_le_sum fun w _ => Nat.mul_le_mul_right _ (hK.1 _)
  omega

/-- **Equivalent right-hand sides give equivalent instances.** If two nets over the ports and
internal wires of a rule are the same graph, plugging the same trees into their ports and the same
names into their internal wires, beside a context `Δ`, gives the same graph, provided the instance
is linear. (Lafont 1997, pages 70 to 72: a net is a graph, and the right-hand side of a rule is
plugged into the net by its ports.) -/
theorem equiv_bind_args
    -- two nets over the same ports and internal wires, the same graph, the first of the shape of
    -- a right-hand side
    {K L : Net S (Fin a ⊕ Fin b ⊕ Fin k)}
    (h : Equiv K L)
    (hK : PortShape K)
    -- the trees on the ports and the names of the internal wires
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    (f : Fin k → ℕ)
    -- the rest of the net
    (Δ : Net S ℕ)
    -- every name occurs at most twice in the trees, the internal wires and `Δ` together
    (hL : ∀ y, ∑ i, (as i).vars.count y + ∑ j, (bs j).vars.count y
        + 2 * (∑ w, if y = f w then 1 else 0) + Δ.vars.count y ≤ 2) :
    Equiv (K.bind (args as bs f) + Δ) (L.bind (args as bs f) + Δ) := by
  revert hK
  induction h with
  | rel K L h =>
    intro hK
    refine (Wire.bind_add h _ Δ ?_ ?_).equiv
    · intro x hx
      rcases x with i | j | w
      · rw [hK.2.1 i] at hx; omega
      · rw [hK.2.2 j] at hx; omega
      · exact ⟨f w, rfl⟩
    · intro y
      rw [Net.vars_add, Multiset.count_add]
      have := count_vars_bind_args_le hK as bs f y
      have := hL y
      omega
  | refl _ => exact fun _ => Equiv.refl _
  | symm K L h ih => exact fun hL' => (ih (PortShape.of_equiv (Equiv.symm h) hL')).symm
  | trans K M L h₁ _ ih₁ ih₂ =>
    exact fun hK => (ih₁ hK).trans (ih₂ (PortShape.of_equiv h₁ hK))

/-- The right-hand side of a linear rule has the shape of a right-hand side. -/
theorem portShape_net
    -- a linear rule
    (r : Rule S a b)
    (hr : r.Linear) :
    PortShape r.net := by
  refine ⟨fun p => ?_, hr.left, hr.right⟩
  rcases p with i | j | w
  · rw [hr.left]; omega
  · rw [hr.right]; omega
  · rw [hr.internal]

/-- An instance of a linear rule in a linear net, with fresh injective names for the new wires,
is linear. -/
theorem linear_inst_add
    -- a linear rule
    (r : Rule S a b)
    (hr : r.Linear)
    -- the trees on the ports, and the rest of the net
    {as : Fin a → Term S ℕ}
    {bs : Fin b → Term S ℕ}
    {Δ : Net S ℕ}
    -- injective names for the new wires
    {f : Fin r.internal → ℕ}
    (hf : Function.Injective f)
    -- the two cells of the active pair
    {α β : S.Sym}
    {hα : S.arity α = a}
    {hβ : S.arity β = b}
    -- the net with the active pair is linear
    (hN : Net.Linear (s(Term.app α (hα ▸ as), Term.app β (hβ ▸ bs)) ::ₘ Δ))
    -- the names of the new wires are fresh
    (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α (hα ▸ as), Term.app β (hβ ▸ bs)) ::ₘ Δ)) :
    (r.inst as bs f + Δ).Linear := by
  subst hα hβ
  intro y
  have hy := hN y
  simp only [Net.vars_cons, Net.vars_add, eqVars_mk, Term.vars_app, Multiset.count_add,
    Multiset.count_sum'] at hy ⊢
  rw [Rule.count_vars_inst r hr]
  by_cases hex : ∃ w, y = f w
  · obtain ⟨w0, rfl⟩ := hex
    have hsum : ∑ w, (if f w0 = f w then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single w0]
      · simp
      · intro w _ hw
        exact ite_eq_right fun h => hw (hf h).symm
      · simp
    have h0 := Multiset.count_eq_zero_of_notMem (hfresh w0)
    simp only [Net.vars_cons, eqVars_mk, Term.vars_app, Multiset.count_add,
      Multiset.count_sum'] at h0
    omega
  · have hsum : ∑ w, (if y = f w then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun w _ => ite_eq_right fun h => hex ⟨w, h⟩
    omega

/-- Two instances of a linear rule that differ only in the names of the new wires are the same
graph, when both are linear. -/
theorem equiv_inst_of_linear
    -- a linear rule
    (r : Rule S a b)
    (hr : r.Linear)
    -- the trees on the ports
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- two choices of names for the new wires
    (f f' : Fin r.internal → ℕ)
    -- the rest of the net
    (Δ : Net S ℕ)
    -- both instances are linear
    (L : (r.inst as bs f + Δ).Linear)
    (L' : (r.inst as bs f' + Δ).Linear) :
    Equiv (r.inst as bs f + Δ) (r.inst as bs f' + Δ) := by
  obtain ⟨K, hK⟩ := Net.exists_below ((r.inst as bs f + Δ) + (r.inst as bs f' + Δ))
  let g : Fin r.internal → ℕ := fun w => K + w
  have hg : Function.Injective g := fun w w' h => Fin.ext (by simpa [g] using h)
  have E := r.equiv_inst hr as bs f g Δ L hg fun w hw => by
    have := hK _ (by rw [Net.vars_add, Multiset.mem_add]; exact Or.inl hw)
    simp [g] at this
  have E' := r.equiv_inst hr as bs f' g Δ L' hg fun w hw => by
    have := hK _ (by rw [Net.vars_add, Multiset.mem_add]; exact Or.inr hw)
    simp [g] at this
  exact E.trans E'.symm

/-- Reading a rule from the other cell and exchanging the trees gives the same instance. -/
theorem swap_inst
    -- the rule
    (r : Rule S a b)
    -- the trees on the ports and the names of the new wires
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    (f : Fin r.internal → ℕ) :
    r.swap.inst bs as f = r.inst as bs f := by
  simp only [Rule.inst, Rule.swap]
  rw [Net.bind_bind]
  congr 1
  funext p
  rcases p with i | j | w <;> rfl

-- ============================================================================================
-- 3. Main result
-- ============================================================================================

/-- **The same active pair, read the same way** (Lafont 1997, Proposition 1, page 73, implicit:
firing the same active pair twice gives the same graph). For a linear rule `r` and a linear net
`α(as) = β(bs), Δ`, two interactions with fresh injective names `f`, `f'` for the new wires give
the same graph. -/
theorem equiv_inst_same
    -- a linear rule for the pair `α`, `β`
    {α β : S.Sym}
    (r : Rule S (S.arity α) (S.arity β))
    (hr : r.Linear)
    -- the trees on the ports of the two cells, and the rest of the net
    (as : Fin (S.arity α) → Term S ℕ)
    (bs : Fin (S.arity β) → Term S ℕ)
    (Δ : Net S ℕ)
    -- the net with the active pair `α(as) = β(bs)` is linear
    (hN : Net.Linear (s(Term.app α as, Term.app β bs) ::ₘ Δ))
    -- two choices of injective names for the new wires, both fresh
    (f f' : Fin r.internal → ℕ)
    (hf : Function.Injective f)
    (hf' : Function.Injective f')
    (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α as, Term.app β bs) ::ₘ Δ))
    (hfresh' : ∀ i, f' i ∉ Net.vars (s(Term.app α as, Term.app β bs) ::ₘ Δ)) :
    -- the two interactions give the same graph
    Equiv (r.inst as bs f + Δ) (r.inst as bs f' + Δ) :=
  r.equiv_inst_of_linear hr as bs f f' Δ
    (r.linear_inst_add hr (hα := rfl) (hβ := rfl) hf hN hfresh)
    (r.linear_inst_add hr (hα := rfl) (hβ := rfl) hf' hN hfresh')

end Rule

end INet
