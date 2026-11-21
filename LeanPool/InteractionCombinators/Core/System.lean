/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Net
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Interaction systems and reduction

* `Rule S a b` — the right-hand side of an interaction between a cell with `a` auxiliary ports and
  a cell with `b`: a net whose names are the auxiliary ports of the two cells and some internal
  wires.
* `System S` — at most one rule for each pair of symbols.
* `Step`, `Steps` — reduction. Only interactions are steps; wire substitution is not.

Contents, in the order of the file:

1. Rules: `Rule`, `Rule.inst`, `Rule.Linear`, `Rule.Reduced`, `Rule.swap`,
   `Rule.count_vars_inst`.
2. Systems and one interaction: `System`, `Step`, `Rule.symm_of_equiv`, `System.WellFormed`.
3. One interaction and linearity: `Step.linear`, `Step.add_right`.
4. Reduction: `Steps`, `Steps.single`, `Steps.cast`, `Steps.linear`.
5. Reduction up to wires: `StepE`, `StepsE`, `Step.stepE`, `Steps.stepsE`, `StepE.linear`,
   `StepsE.linear`.
6. The tactic `ms`, which reorders a sum of multisets.
-/

@[expose] public section

namespace INet

-- the signature, for the whole file
variable {S : Signature}

-- ============================================================================================
-- 1. Rules
-- ============================================================================================

/-- The right-hand side of an interaction rule. Its names are the `a` auxiliary ports of the first
cell, the `b` auxiliary ports of the second, and `internal` new wires. -/
structure Rule (S : Signature) (a b : ℕ) where
  /-- The number of wires created by the rule. -/
  internal : ℕ
  /-- The net that replaces the two cells. -/
  net : Net S (Fin a ⊕ Fin b ⊕ Fin internal)

/-- The right-hand side of a rule, with trees plugged into the auxiliary ports and the internal
wires named by `f`. -/
def Rule.inst
    -- the rule, between a cell with `a` auxiliary ports and a cell with `b`
    {a b : ℕ}
    (r : Rule S a b)
    -- the trees plugged into the auxiliary ports of the first cell
    (as : Fin a → Term S ℕ)
    -- the trees plugged into the auxiliary ports of the second cell
    (bs : Fin b → Term S ℕ)
    -- the names given to the wires created by the rule
    (f : Fin r.internal → ℕ) :
    Net S ℕ :=
  r.net.bind (Sum.elim as (Sum.elim bs fun i => Term.var (f i)))

namespace Rule

-- the numbers of auxiliary ports of the two cells
variable {a b : ℕ}

/-- In the right-hand side of a rule, every auxiliary port of the two cells occurs exactly once and
every internal wire exactly twice. -/
structure Linear (r : Rule S a b) : Prop where
  -- every auxiliary port of the first cell occurs exactly once
  left : ∀ i, r.net.vars.count (.inl i) = 1
  -- every auxiliary port of the second cell occurs exactly once
  right : ∀ j, r.net.vars.count (.inr (.inl j)) = 1
  -- every wire created by the rule has exactly two ends
  internal : ∀ w, r.net.vars.count (.inr (.inr w)) = 2

/-- The right-hand side is a reduced net, written as trees rooted at the auxiliary ports: every
equation has an auxiliary port on one side. Together with linearity this excludes pairs of cells
plugged by their principal ports, vicious circles and cyclic wires. -/
def Reduced
    (r : Rule S a b) :
    Prop :=
  -- for every equation `e` of the right-hand side,
  ∀ e ∈ r.net,
    -- there are a name `p` and a tree `t` such that
    ∃ p t,
      -- the equation is `p = t`,
      e = s(Term.var p, t) ∧
      -- and `p` is an auxiliary port of one of the two cells, not a wire created by the rule
      ∀ w, p ≠ .inr (.inr w)

/-- The same rule read from the other cell: the two groups of auxiliary ports are exchanged. -/
def swap
    (r : Rule S a b) :
    Rule S b a where
  -- the same number of wires is created
  internal := r.internal
  -- the ports of the first cell become those of the second and conversely; the wires are kept
  net := r.net.bind fun p =>
    Term.var (Sum.elim (fun i => .inr (.inl i)) (Sum.elim .inl fun w => .inr (.inr w)) p)

/-- The count of an element in a `Multiset.bind` over a finite type, as a sum over the type. -/
theorem _root_.Multiset.count_bind_fintype
    {P ν : Type}
    [Fintype P]
    [DecidableEq P]
    [DecidableEq ν]
    -- the multiset, and the function applied to every element
    (m : Multiset P)
    (g : P → Multiset ν)
    -- the element that is counted
    (y : ν) :
    (m.bind g).count y = ∑ p, m.count p * (g p).count y := by
  rw [Multiset.count_bind, Finset.sum_multiset_map_count]
  simp only [smul_eq_mul]
  refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hp), zero_mul]

/-- The names of an instance of a linear rule: those of the trees plugged into the ports, and both
ends of each internal wire. -/
theorem count_vars_inst
    -- the rule, which is linear
    (r : Rule S a b)
    (hr : r.Linear)
    -- the trees plugged into the auxiliary ports of the two cells
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- the names given to the wires created by the rule
    (f : Fin r.internal → ℕ)
    -- the name that is counted
    (y : ℕ) :
    (r.inst as bs f).vars.count y =
      -- its occurrences in the trees plugged into the first cell and into the second,
      ∑ i, (as i).vars.count y + ∑ j, (bs j).vars.count y +
        -- and two for each created wire that bears this name
        2 * ∑ w, if y = f w then 1 else 0 := by
  rw [inst, Net.vars_bind, Multiset.count_bind_fintype, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp only [hr.left, hr.right, hr.internal, one_mul, Sum.elim_inl, Sum.elim_inr, Term.vars_var,
    Multiset.count_singleton, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  ring

end Rule

-- ============================================================================================
-- 2. Systems and one interaction
-- ============================================================================================

/-- An interaction system: at most one rule for each pair of symbols. An equation is unordered, so
a rule given for `α`, `β` also applies to `β`, `α`. -/
structure System (S : Signature) where
  /-- The rule for a pair of symbols, if any. -/
  rule : (α β : S.Sym) → Option (Rule S (S.arity α) (S.arity β))

/-- One interaction: two cells plugged by their principal ports are replaced by the right-hand
side of their rule. The wires the rule creates get names not used in the net. -/
inductive Step (I : System S) : Net S ℕ → Net S ℕ → Prop
  | mk
      -- the symbols of the two cells, and the rule of the system for them
      (α β : S.Sym)
      (r : Rule S (S.arity α) (S.arity β))
      (hr : I.rule α β = some r)
      -- the trees on the auxiliary ports of the first cell
      (as : Fin (S.arity α) → Term S ℕ)
      -- the trees on the auxiliary ports of the second cell
      (bs : Fin (S.arity β) → Term S ℕ)
      -- the rest of the net
      (Δ : Net S ℕ)
      -- the names given to the wires created by the rule: pairwise distinct,
      (f : Fin r.internal → ℕ)
      (hf : Function.Injective f)
      -- and not used in the net one starts from
      (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α as, Term.app β bs) ::ₘ Δ)) :
      -- the equation between the two cells is replaced by the right-hand side of the rule
      Step I (s(Term.app α as, Term.app β bs) ::ₘ Δ) (r.inst as bs f + Δ)

/-- A rule that is the same net as its swap up to wires is symmetric in the sense of
`System.WellFormed.symm`, with the identity permutation. -/
theorem Rule.symm_of_equiv
    -- a rule between two cells with the same number of auxiliary ports
    {a : ℕ}
    {r : Rule S a a}
    -- read from the other cell, it is the same net up to wires
    (h : Equiv r.swap.net r.net) :
    -- there is a permutation `π` of the wires created by the rule such that
    ∃ π : _root_.Equiv.Perm (Fin r.internal),
      -- the rule read from the other cell is, up to wires, the rule with its wires permuted
      Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x)) := by
  refine ⟨1, ?_⟩
  have hb : ∀ t : Term S (Fin a ⊕ Fin a ⊕ Fin r.internal), t.bind (fun x => Term.var
      (Sum.map id (Sum.map id (1 : _root_.Equiv.Perm (Fin r.internal))) x)) = t := by
    intro t
    induction t with
    | var x => rcases x with i | j | w <;> rfl
    | app α ts ih =>
      change Term.app α _ = Term.app α _
      congr 1
      funext i
      exact ih i
  have e : (r.net.bind fun x =>
      Term.var (Sum.map id (Sum.map id (1 : _root_.Equiv.Perm (Fin r.internal))) x)) = r.net := by
    unfold Net.bind
    conv_rhs => rw [← Multiset.map_id r.net]
    refine Multiset.map_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ x y => exact congrArg₂ (fun u v => s(u, v)) (hb x) (hb y)
  exact h.trans (Equiv.of_eq e.symm)

/-- An interaction system in the sense of Lafont: rules are linear and reduced, and can be applied
without ambiguity. -/
structure System.WellFormed (I : System S) : Prop where
  /-- Every rule is linear. -/
  linear : ∀ α β r, I.rule α β = some r → r.Linear
  /-- Every right-hand side is a reduced net. -/
  reduced : ∀ α β r, I.rule α β = some r → r.Reduced
  /-- A rule given for `α`, `β` excludes another rule for `β`, `α`. -/
  unique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none
  /-- A rule of a symbol with itself is symmetric: read from the other cell it is the same graph
  (Lafont 1997, page 73), that is, the same net up to wires and up to a permutation of its
  internal wires. The permutation is needed because the internal wires of a rule are named by
  `Fin r.internal`, which leaves no spare name through which `Equiv` could exchange two of them. -/
  symm :
    -- for every rule `r` of a symbol `α` with itself,
    ∀ α r, I.rule α α = some r →
      -- there is a permutation `π` of the wires created by the rule such that
      ∃ π : _root_.Equiv.Perm (Fin r.internal),
        -- the rule read from the other cell is, up to wires, the rule with its wires permuted
        Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x))

-- ============================================================================================
-- 3. One interaction and linearity
-- ============================================================================================

/-- An interaction of a linear rule keeps the net linear. -/
theorem Step.linear
    -- the system: every rule is linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- one interaction, from `N` to `N'`
    {N N' : Net S ℕ}
    (h : Step I N N')
    -- the net one starts from is linear
    (hN : N.Linear) :
    N'.Linear := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := h
  intro y
  have hy := hN y
  simp only [Net.vars_cons, Net.vars_add, eqVars_mk, Term.vars_app, Multiset.count_add,
    Multiset.count_sum'] at hy ⊢
  rw [Rule.count_vars_inst r (hI _ _ _ hr)]
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

/-- An interaction can be done inside a larger net, as long as the result is linear: the names
given to the wires created by the rule are then unused in the rest of the net. -/
theorem Step.add_right
    -- the system: every rule is linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- one interaction, from `N` to `M`
    {N M : Net S ℕ}
    (h : Step I N M)
    -- the rest of the net
    (Γ : Net S ℕ)
    -- the larger net one arrives at is linear
    (hlin : (M + Γ).Linear) :
    Step I (N + Γ) (M + Γ) := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := h
  have hΓ : ∀ w, f w ∉ Γ.vars := by
    intro w
    refine Multiset.count_eq_zero.1 ?_
    have h2 := hlin (f w)
    simp only [Net.vars_add, Multiset.count_add, Rule.count_vars_inst r (hI _ _ _ hr)] at h2
    have h1 : (1 : ℕ) ≤ ∑ w', if f w = f w' then 1 else 0 :=
      calc 1 = if f w = f w then 1 else 0 := (ite_eq_left rfl).symm
        _ ≤ _ := Finset.single_le_sum (f := fun w' => if f w = f w' then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    omega
  have e : (s(Term.app α as, Term.app β bs) ::ₘ Δ) + Γ =
      s(Term.app α as, Term.app β bs) ::ₘ (Δ + Γ) := Multiset.cons_add _ _ _
  have := Step.mk α β r hr as bs (Δ + Γ) f hf (fun w hw => by
    rw [← e, Net.vars_add, Multiset.mem_add] at hw
    exact hw.elim (hfresh w) (hΓ w))
  rw [e, add_assoc]
  exact this

-- ============================================================================================
-- 4. Reduction
-- ============================================================================================

/-- Reduction in any number of interactions. -/
abbrev Steps
    (I : System S) :
    Net S ℕ → Net S ℕ → Prop :=
  Relation.ReflTransGen (Step I)

namespace Steps

-- a system and four nets
variable {I : System S} {N N' M M' : Net S ℕ}

/-- One interaction is a reduction. -/
theorem single
    (h : Step I N N') :
    Steps I N N' :=
  Relation.ReflTransGen.single h

/-- A reduction carried along equalities of nets. -/
theorem cast
    (h : Steps I N N')
    -- a net equal to the one started from, and a net equal to the one arrived at
    (hN : N = M)
    (hN' : N' = M') :
    Steps I M M' :=
  hN ▸ hN' ▸ h

/-- Reduction by linear rules keeps the net linear. -/
theorem linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (h : Steps I N N')
    (hN : N.Linear) :
    N'.Linear := by
  induction h with
  | refl => exact hN
  | tail _ hstep ih => exact hstep.linear hI ih

end Steps

-- ============================================================================================
-- 5. Reduction up to wires
-- ============================================================================================

/-- One interaction up to wires: the net is first rewritten into an equivalent one, then two
cells interact. This lets two cells interact when their principal ports are joined by a named
wire, as in `x = α(…)`, `x = β(…)`, which is an active pair of the graph. -/
def StepE
    -- the system
    (I : System S)
    -- the net one starts from, and the net one arrives at
    (N M : Net S ℕ) :
    Prop :=
  -- there is a net `N'` such that
  ∃ N',
    -- `N'` is the same graph as `N`,
    Equiv N N' ∧
    -- and one interaction leads from `N'` to `M`
    Step I N' M

/-- Reduction up to wires, in any number of interactions. -/
abbrev StepsE
    (I : System S) :
    Net S ℕ → Net S ℕ → Prop :=
  Relation.ReflTransGen (StepE I)

/-- One interaction is one interaction up to wires. -/
theorem Step.stepE
    {I : System S}
    {N M : Net S ℕ}
    (h : Step I N M) :
    StepE I N M :=
  ⟨N, Equiv.refl N, h⟩

/-- A reduction is a reduction up to wires. -/
theorem Steps.stepsE
    {I : System S}
    {N M : Net S ℕ}
    (h : Steps I N M) :
    StepsE I N M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.stepE

/-- An interaction up to wires, by a linear rule, keeps the net linear. -/
theorem StepE.linear
    -- the system: every rule is linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- one interaction up to wires, from `N` to `M`
    {N M : Net S ℕ}
    (h : StepE I N M)
    -- the net one starts from is linear
    (hN : N.Linear) :
    M.Linear := by
  obtain ⟨N', he, hs⟩ := h
  exact hs.linear hI (he.linear hN)

/-- Reduction up to wires, by linear rules, keeps the net linear. -/
theorem StepsE.linear
    -- the system: every rule is linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- a reduction up to wires, from `N` to `M`
    {N M : Net S ℕ}
    (h : StepsE I N M)
    -- the net one starts from is linear
    (hN : N.Linear) :
    M.Linear := by
  induction h with
  | refl => exact hN
  | tail _ hstep ih => exact hstep.linear hI ih

-- ============================================================================================
-- 6. The tactic `ms`
-- ============================================================================================

/-- Reorder a sum of multisets. -/
macro "ms" : tactic =>
  `(tactic| first | rfl | (simp only [← Multiset.singleton_add, add_zero, zero_add]; abel) | abel)

end INet
