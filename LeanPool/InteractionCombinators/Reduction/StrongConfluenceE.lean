/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduction.StrongConfluence
public import LeanPool.InteractionCombinators.Translations.PairStepE

/-!
# Proposition 1 for reduction of graphs (Lafont 1997, page 73)

`Step.strong_confluence` is Proposition 1 for literal interactions. The reduction of graphs is
`StepE`: an interaction may first rewrite the net into another text of the same graph. Two `StepE`
from one net `N` fire in two texts `N₁`, `N₂` of `N`, and an active pair of `N₂` need not be an
equation of `N₁`: in `x = α(…), x = β(…)` it is behind the wire `x`.

**The transport lemma.** An active pair of a text is followed through every other text of the
same graph as a *written chain* (`Cut.chain`, `InteractionCombinators/Reduced/CutChain.lean`)

  `α(as) = x₁, x₁ = x₂, …, xₖ = β(bs)`, plus the rest `D` of the net,

together with the net its interaction gives: `r.inst as bs f + D`, up to `Equiv`
(`StrongConfluenceE.ChainPair`). The form chosen is this one, rather than "the same pair in a
rewritten text", because cells have no identity in a text: the pair is identified by the graph it
gives when fired, which is a statement about one text only. A wire substitution, in either
direction, keeps such a chain (`ChainPair.wire`, `ChainPair.wire_symm`), so equivalent nets have
the same chains (`ChainPair.of_equiv`): this is the transport. A chain is then contracted by wire
substitutions (`ChainPair.contract`), which keep a chain of length `0`, that is, an equation
`α(as) = β(bs)`, of length `0`.

**Proposition 1 up to wires** (`StepE.strong_confluence`). The two active pairs fired from `N₁` and
`N₂` are chains of `N₁`. Contract the second one: in the net `K` reached, both are equations, and
`Step.strong_confluence` applies to `K`.

Contents, in the order of the file:

1. Definition: `ChainPair`, an active pair written as a chain, with its interaction.
2. Auxiliary lemmas, instances of a rule and wire substitution: `subst_app`, `sub_inst`,
   `mem_vars_inst_left`, `mem_vars_inst_right`, `mem_vars_app`.
3. Auxiliary lemmas, a chain with its interaction: `count_vars_short`, `linear_short`,
   `notMem_short` (the equation between the two ends of a chain), `ChainPair.of_step`,
   `ChainPair.step`, `linear_inst_chain`, `ChainPair.refresh`, `mem_ends_of_mem_chain`,
   `ChainPair.wire`, `chain_replace_cell`, `ChainPair.unsub`, `ChainPair.wire_symm`, and the
   transport lemma `ChainPair.of_equiv`.
4. Auxiliary lemmas, contracting a chain: `equiv_of_wires`, `wires_chain`, `ChainPair.contract`,
   `ChainPair.wires`.
5. Main result: `StepE.strong_confluence`, Proposition 1 for reduction of graphs (page 73).
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term Cut

namespace StrongConfluenceE

-- ============================================================================================
-- 1. Definition: an active pair written as a chain
-- ============================================================================================

/-- **An active pair written as a chain, with its interaction** (Lafont 1997, page 73). The net
`N` is a chain `α(as) = x₁, …, xₖ = β(bs)` of at most `n` names, plus a rest `D`; the rule of
`α`, `β` is `r`, and firing the pair, with fresh injective names `f` for the new wires, gives a
net that is the same graph as `M`. -/
def ChainPair
    -- the interaction system
    (I : System S)
    -- the net, the net its interaction gives up to wires, a bound on the length of the chain
    (N M : Net S ℕ)
    (n : ℕ) :
    Prop :=
  -- two symbols with a rule `r`, the trees on their auxiliary ports, the links of the chain,
  -- the rest of the net and the names of the new wires, such that
  ∃ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)) (_ : I.rule α β = some r)
    (as : Fin (S.arity α) → Term S ℕ) (bs : Fin (S.arity β) → Term S ℕ) (xs : List ℕ)
    (D : Net S ℕ) (f : Fin r.internal → ℕ),
    -- the chain has at most `n` links,
    xs.length ≤ n ∧
    -- the names of the new wires are distinct
    Function.Injective f ∧
    -- and fresh for the net,
    (∀ i, f i ∉ N.vars) ∧
    -- the net is the chain `α(as) = x₁, …, xₖ = β(bs)` and the rest `D`,
    N = chain (Term.app α as) xs (Term.app β bs) + D ∧
    -- and firing the pair gives the same graph as `M`
    Equiv (r.inst as bs f + D) M

-- ============================================================================================
-- 2. Auxiliary lemmas: instances of a rule and wire substitution
-- ============================================================================================


/-- Plugging `t` into a name `x` of a cell plugs it into the trees on its ports. -/
theorem subst_app
    -- the cell `α(ts)`
    (α : S.Sym)
    (ts : Fin (S.arity α) → Term S ℕ)
    -- the name `x` and the tree `t` plugged into it
    (x : ℕ)
    (t : Term S ℕ) :
    (Term.app α ts).subst x t = Term.app α fun i => (ts i).subst x t := rfl

/-- Plugging `t` into a name `x` of an instance of a rule plugs it into the trees on the ports,
when `x` is not one of the new wires. -/
theorem sub_inst
    -- the rule
    {a b : ℕ}
    (r : Rule S a b)
    -- the trees on the auxiliary ports of the two cells
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- the names of the internal wires of the rule
    (f : Fin r.internal → ℕ)
    -- the name `x` and the tree `t` plugged into it; `x` is not a name of an internal wire
    (x : ℕ)
    (t : Term S ℕ)
    (hf : ∀ w, f w ≠ x) :
    sub (r.inst as bs f) x t =
      r.inst (fun i => (as i).subst x t) (fun j => (bs j).subst x t) f := by
  have e : sub (r.inst as bs f) x t =
      Net.bind (fun y => if y = x then t else var y) (r.inst as bs f) := rfl
  rw [e, Rule.inst, Rule.inst, Net.bind_bind]
  congr 1
  funext p
  rcases p with i | j | w
  · rfl
  · rfl
  · simp [hf w]

/-- A name of a tree plugged into a port of the first cell is a name of the instance. -/
theorem mem_vars_inst_left
    -- a linear rule
    {a b : ℕ}
    {r : Rule S a b}
    (hr : r.Linear)
    -- the trees on the auxiliary ports of the two cells, and the names of the internal wires
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    (f : Fin r.internal → ℕ)
    -- a name `x` of the tree on the port `i` of the first cell
    {x : ℕ}
    {i : Fin a}
    (hx : x ∈ (as i).vars) :
    x ∈ (r.inst as bs f).vars := by
  rw [← Multiset.one_le_count_iff_mem, Rule.count_vars_inst r hr]
  have h1 := Multiset.one_le_count_iff_mem.2 hx
  have : (as i).vars.count x ≤ ∑ i, (as i).vars.count x :=
    Finset.single_le_sum (f := fun i => (as i).vars.count x) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  omega

/-- A name of a tree plugged into a port of the second cell is a name of the instance. -/
theorem mem_vars_inst_right
    -- a linear rule
    {a b : ℕ}
    {r : Rule S a b}
    (hr : r.Linear)
    -- the trees on the auxiliary ports of the two cells, and the names of the internal wires
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    (f : Fin r.internal → ℕ)
    -- a name `x` of the tree on the port `j` of the second cell
    {x : ℕ}
    {j : Fin b}
    (hx : x ∈ (bs j).vars) :
    x ∈ (r.inst as bs f).vars := by
  rw [← Multiset.one_le_count_iff_mem, Rule.count_vars_inst r hr]
  have h1 := Multiset.one_le_count_iff_mem.2 hx
  have : (bs j).vars.count x ≤ ∑ j, (bs j).vars.count x :=
    Finset.single_le_sum (f := fun j => (bs j).vars.count x) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

/-- A name of a cell is the name of one of the trees on its ports. -/
theorem mem_vars_app
    -- the cell `α(ts)` and a name `x` of it
    {α : S.Sym}
    {ts : Fin (S.arity α) → Term S ℕ}
    {x : ℕ}
    (hx : x ∈ (Term.app α ts).vars) :
    -- `x` is a name of the tree on some port `i`
    ∃ i, x ∈ (ts i).vars := by
  simpa only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and] using hx

-- ============================================================================================
-- 3. Auxiliary lemmas: a chain with its interaction
-- ============================================================================================

/-- The equation `a = b` between the two ends of a chain has fewer names than the chain. -/
theorem count_vars_short
    -- the two ends, the links of the chain, the rest of the net
    (a b : Term S ℕ)
    (xs : List ℕ)
    (D : Net S ℕ)
    -- a name
    (y : ℕ) :
    (Net.vars (s(a, b) ::ₘ D)).count y ≤ (chain a xs b + D).vars.count y := by
  rw [Net.vars_add, Multiset.count_add, count_vars_chain, Net.vars_cons, Multiset.count_add,
    eqVars_mk, Multiset.count_add]
  omega

/-- Replacing a chain by the equation between its two ends keeps linearity. -/
theorem linear_short
    -- the two ends, the links of the chain, the rest of the net
    {a b : Term S ℕ}
    {xs : List ℕ}
    {D : Net S ℕ}
    -- the net with the chain is linear
    (h : (chain a xs b + D).Linear) :
    Net.Linear (s(a, b) ::ₘ D) :=
  fun y => (count_vars_short a b xs D y).trans (h y)

/-- A name that is not in a net with a chain is not in it with the equation between the two
ends of the chain. -/
theorem notMem_short
    -- the two ends, the links of the chain, the rest of the net
    {a b : Term S ℕ}
    {xs : List ℕ}
    {D : Net S ℕ}
    -- a name that is not a name of the net with the chain
    {y : ℕ}
    (h : y ∉ (chain a xs b + D).vars) :
    y ∉ Net.vars (s(a, b) ::ₘ D) := by
  rw [← Multiset.count_eq_zero] at h ⊢
  have := count_vars_short a b xs D y
  omega

variable {I : System S}

/-- One interaction is a chain of length `0`. -/
theorem ChainPair.of_step
    -- one literal interaction from `N` to `M`
    {N M : Net S ℕ}
    (h : Step I N M) :
    ChainPair I N M 0 := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := h
  exact ⟨α, β, r, hr, as, bs, [], Δ, f, le_rfl, hf, hfresh, by simp, Equiv.refl _⟩

/-- A chain of length `0` is an equation between two cells: it can be fired. -/
theorem ChainPair.step
    -- a chain pair of length `0` of `N`, with interaction `M`
    {N M : Net S ℕ}
    (h : ChainPair I N M 0) :
    -- `N` reduces in one literal interaction to a net that is the same graph as `M`
    ∃ M', Step I N M' ∧ Equiv M' M := by
  obtain ⟨α, β, r, hr, as, bs, xs, D, f, hlen, hf, hfresh, rfl, hE⟩ := h
  have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hxs
  have e : chain (Term.app α as) [] (Term.app β bs) + D =
      s(Term.app α as, Term.app β bs) ::ₘ D := by
    simp
  rw [e] at hfresh ⊢
  exact ⟨_, Step.mk α β r hr as bs D f hf hfresh, hE⟩

/-- The instance of a chain is linear when the chain is, with fresh injective names. -/
theorem linear_inst_chain
    -- every rule of the system is linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- two symbols and their rule
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (hr : I.rule α β = some r)
    -- the trees on the auxiliary ports, the links of the chain, the rest of the net
    {as : Fin (S.arity α) → Term S ℕ}
    {bs : Fin (S.arity β) → Term S ℕ}
    {xs : List ℕ}
    {D : Net S ℕ}
    -- injective names for the new wires
    {f : Fin r.internal → ℕ}
    (hf : Function.Injective f)
    -- the net with the chain is linear
    (hN : (chain (Term.app α as) xs (Term.app β bs) + D).Linear)
    -- the names of the new wires are fresh for it
    (hfresh : ∀ i, f i ∉ (chain (Term.app α as) xs (Term.app β bs) + D).vars) :
    (r.inst as bs f + D).Linear :=
  r.linear_inst_add (hI _ _ _ hr) (hα := rfl) (hβ := rfl) hf (linear_short hN)
    fun i => notMem_short (hfresh i)

/-- **New names for the new wires.** In a chain pair of a linear net `N`, the names `f` can be
replaced by any injective names that are fresh for a net `N'` containing the names of `N`. -/
theorem ChainPair.refresh
    -- every rule of the system is linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- a chain pair of a linear net `N`, and a net `N'` containing the names of `N`
    {N N' M : Net S ℕ}
    {n : ℕ}
    (h : ChainPair I N M n)
    (hN : N.Linear)
    (hsub : ∀ y ∈ N.vars, y ∈ N'.vars) :
    -- the same data as in `ChainPair I N M n`, such that
    ∃ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)) (_ : I.rule α β = some r)
      (as : Fin (S.arity α) → Term S ℕ) (bs : Fin (S.arity β) → Term S ℕ) (xs : List ℕ)
      (D : Net S ℕ) (f : Fin r.internal → ℕ),
      -- the chain has at most `n` links,
      xs.length ≤ n ∧
      -- the names of the new wires are distinct
      Function.Injective f ∧
      -- and fresh for `N'`,
      (∀ i, f i ∉ N'.vars) ∧
      -- `N` is the chain and the rest `D`,
      N = chain (Term.app α as) xs (Term.app β bs) + D ∧
      -- and firing the pair gives the same graph as `M`
      Equiv (r.inst as bs f + D) M := by
  obtain ⟨α, β, r, hr, as, bs, xs, D, f, hlen, hf, hfresh, rfl, hE⟩ := h
  obtain ⟨K, hK⟩ := Net.exists_below N'
  let g : Fin r.internal → ℕ := fun w => K + w
  have hg : Function.Injective g := fun w w' e => Fin.ext (by simpa [g] using e)
  have hgN' : ∀ i, g i ∉ N'.vars := fun i hm => by
    have := hK _ hm
    simp [g] at this
  have hgN : ∀ i, g i ∉ (chain (Term.app α as) xs (Term.app β bs) + D).vars :=
    fun i hm => hgN' i (hsub _ hm)
  refine ⟨α, β, r, hr, as, bs, xs, D, g, hlen, hg, hgN', rfl, ?_⟩
  have L := linear_inst_chain hI hr hf hN hfresh
  have L' := linear_inst_chain hI hr hg hN hgN
  exact (r.equiv_inst_of_linear (hI _ _ _ hr) as bs g f D L' L).trans hE

/-- A name of a chain that is not one of its links is a name of one of its two ends. -/
theorem mem_ends_of_mem_chain
    -- the two ends and the links of the chain
    {a b : Term S ℕ}
    {xs : List ℕ}
    -- a name of the chain that is not a link
    {x : ℕ}
    (hxs : x ∉ xs)
    (hx : x ∈ (chain a xs b).vars) :
    -- it is a name of one of the two ends
    x ∈ a.vars ∨ x ∈ b.vars := by
  rw [← Multiset.one_le_count_iff_mem, count_vars_chain, List.count_eq_zero.2 hxs] at hx
  by_cases ha : x ∈ a.vars
  · exact Or.inl ha
  · right
    rw [← Multiset.one_le_count_iff_mem]
    rw [Multiset.count_eq_zero.2 ha] at hx
    omega

/-- **A wire substitution keeps a chain pair** (Lafont 1997, page 73). If the wire `x = t` is a link
of the chain, the chain gets shorter and its interaction does not change; otherwise `t` is plugged
into the rest of the net, the chain keeps its links, and the interaction is changed by the same
wire substitution. The chain does not get longer. -/
theorem ChainPair.wire
    -- every rule of the system is linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- a wire substitution from `N` to `N'`
    {N N' M : Net S ℕ}
    {n : ℕ}
    (h : Wire N N')
    -- a chain pair of `N` of length at most `n`, with interaction `M`
    (hc : ChainPair I N M n) :
    -- is a chain pair of `N'`, with the same bound and the same interaction
    ChainPair I N' M n := by
  have hsub : ∀ y ∈ N'.vars, y ∈ N.vars := fun y hy => h.mem_vars hy
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hcx := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcx
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have ht : x ∉ t.vars := Multiset.count_eq_zero.1 (by omega)
  have hΔ : x ∉ Net.vars Δ := Multiset.count_eq_zero.1 (by omega)
  have hM : s(a.subst x t, b.subst x t) ::ₘ Δ = sub (s(a, b) ::ₘ Δ) x t := by
    rw [sub_cons, sub_of_notMem t hΔ]
  obtain ⟨α, β, r, hr, as, bs, xs, D, f, hlen, hf, hfresh, hN, hE⟩ := hc
  have hxN : x ∈ Net.vars (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) := by simp
  have hfx : ∀ w, f w ≠ x := fun w e => hfresh w (e ▸ hxN)
  have hlin' := hlin x
  rw [hN, Net.vars_add, Multiset.count_add, count_vars_chain] at hlin'
  have hW : s(var x, t) ∈ chain (Term.app α as) xs (Term.app β bs) + D :=
    hN ▸ Multiset.mem_cons_self _ _
  have hfresh' : ∀ i, f i ∉ Net.vars (s(a.subst x t, b.subst x t) ::ₘ Δ) :=
    fun i hm => hfresh i (hsub _ hm)
  rw [hM] at hfresh' ⊢
  rcases Multiset.mem_add.1 hW with hWc | hWD
  · -- the wire is a link of the chain
    obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem hWc
    rw [hC, Multiset.cons_add] at hN
    rw [(Multiset.cons_inj_right _).1 hN] at hfresh' ⊢
    have hxs : x ∈ xs := mem_chain_var ⟨β, bs, rfl⟩ (Term.app α as) xs
      (fun e => not_isCell_var x (e ▸ (⟨α, as, rfl⟩ : (Term.app α as).IsCell))) hWc
    have h1 := List.count_pos_iff.2 hxs
    have hD : x ∉ Net.vars D := Multiset.count_eq_zero.1 (by omega)
    have hAx : x ∉ (Term.app α as).vars := Multiset.count_eq_zero.1 (by omega)
    have hBx : x ∉ (Term.app β bs).vars := Multiset.count_eq_zero.1 (by omega)
    rw [Cut.sub_add, sub_of_notMem t hD, sub_contract hBx _ xs C hAx (by omega) hC] at hfresh' ⊢
    exact ⟨α, β, r, hr, as, bs, xs.erase x, D, f, List.length_erase_le.trans hlen, hf,
      hfresh', rfl, hE⟩
  · -- the wire is in the rest of the net
    obtain ⟨D₁, rfl⟩ := Multiset.exists_cons_of_mem hWD
    rw [Multiset.add_cons] at hN
    rw [(Multiset.cons_inj_right _).1 hN] at hfresh' ⊢
    have hD1 : 1 ≤ (Net.vars (s(var x, t) ::ₘ D₁)).count x := by
      rw [Net.vars_cons, eqVars_mk, Multiset.count_add, Term.vars_var, Multiset.count_add,
        Multiset.count_singleton_self]
      omega
    have hxs : x ∉ xs := fun hm => by
      have := List.count_pos_iff.2 hm
      omega
    rw [Cut.sub_add, sub_chain _ _ xs hxs, subst_app, subst_app] at hfresh' ⊢
    refine ⟨α, β, r, hr, _, _, xs, sub D₁ x t, f, hlen, hf, hfresh', rfl, ?_⟩
    -- the interaction, before and after the wire substitution
    have hNlin : (chain (Term.app α as) xs (Term.app β bs) + s(var x, t) ::ₘ D₁).Linear := by
      rw [Multiset.add_cons, ← hN]; exact hlin
    have hNfresh : ∀ i, f i ∉ (chain (Term.app α as) xs (Term.app β bs) + s(var x, t) ::ₘ D₁).vars
        := by
      rw [Multiset.add_cons, ← hN]; exact hfresh
    have L := linear_inst_chain hI hr hf hNlin hNfresh
    rw [Multiset.add_cons] at L
    have hxR : x ∈ (r.inst as bs f + D₁).vars := by
      have hxc : x ∈ (chain (Term.app α as) xs (Term.app β bs) + D₁).vars := by
        have : x ∈ Net.vars (s(a, b) ::ₘ Δ) := by
          rw [Net.vars_cons, Multiset.mem_add]; exact Or.inl hx
        rwa [(Multiset.cons_inj_right _).1 hN] at this
      rw [Net.vars_add, Multiset.mem_add] at hxc ⊢
      rcases hxc with hxc | hxc
      · left
        rcases mem_ends_of_mem_chain hxs hxc with hA | hB
        · obtain ⟨i, hi⟩ := mem_vars_app hA
          exact mem_vars_inst_left (hI _ _ _ hr) as bs f hi
        · obtain ⟨j, hj⟩ := mem_vars_app hB
          exact mem_vars_inst_right (hI _ _ _ hr) as bs f hj
      · exact Or.inr hxc
    have Wr := PairStepE.wire_sub L hxR
    rw [Cut.sub_add, sub_inst r as bs f x t hfx, ← Multiset.add_cons] at Wr
    exact Wr.equiv.symm.trans hE

/-- **Changing a cell at an end of a chain**, keeping track of the end. If an equation `c = b₀` of
a chain has a cell `c` on one side, `c` is the first or the last end of the chain, and it can be
replaced there by any tree `a'`. -/
theorem chain_replace_cell
    -- an equation `c = b₀` with a cell `c`, and a tree `a'` to put in place of `c`
    {c a' b₀ : Term S ℕ}
    (hc : c.IsCell) :
    -- for every chain `A = x₁, …, xₖ = B` that is `c = b₀` and some equations `C`,
    ∀ (A B : Term S ℕ) (xs : List ℕ) (C : Net S ℕ), chain A xs B = s(c, b₀) ::ₘ C →
      -- either `c` is the first end `A`, and `a' = b₀, C` is the chain from `a'` to `B`,
      (c = A ∧ s(a', b₀) ::ₘ C = chain a' xs B) ∨
      -- or `c` is the last end `B`, and `a' = b₀, C` is the chain from `A` to `a'`
      (c = B ∧ s(a', b₀) ::ₘ C = chain A xs a')
  | A, B, [], C, h => by
    rw [chain_nil, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, rfl⟩ := h
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, by simp⟩
    · exact Or.inr ⟨rfl, by simp [Sym2.eq_swap]⟩
  | A, B, y :: ys, C, h => by
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h1, rfl⟩ | ⟨-, cs, h2, rfl⟩
    · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd hc (not_isCell_var y)
    · rcases chain_replace_cell hc (var y) B ys cs h2 with ⟨rfl, -⟩ | ⟨rfl, e⟩
      · exact absurd hc (not_isCell_var y)
      · refine Or.inr ⟨rfl, ?_⟩
        rw [Multiset.cons_swap, e, chain_cons]

/-- A wire substitution undone keeps a chain pair, when `x` occurs in the left side `a` of the
equation it was plugged into: the chain gets a new link `x`, or one of its two cells is the cell
into which `t` was plugged, or the wire is in the rest of the net. -/
theorem ChainPair.unsub
    -- every rule of the system is linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- the wire `x = t`, the equation `a = b` with `x` in `a`, and the rest `Δ` of the net
    {x : ℕ}
    {t a b : Term S ℕ}
    {Δ M : Net S ℕ}
    {n : ℕ}
    (hxa : x ∈ a.vars)
    -- the net `x = t, a = b, Δ` is linear
    (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ))
    -- the net with `t` plugged into `x` has a chain pair with interaction `M`
    (hc : ChainPair I (s(a.subst x t, b) ::ₘ Δ) M n) :
    -- then so has the net before the substitution, with a chain of some length
    ∃ n', ChainPair I (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) M n' := by
  have hcx := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcx
  have hxa1 := Multiset.one_le_count_iff_mem.2 hxa
  have hxb : x ∉ b.vars := Multiset.count_eq_zero.1 (by omega)
  have hxt : x ∉ t.vars := Multiset.count_eq_zero.1 (by omega)
  have hW : Wire (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) (s(a.subst x t, b) ::ₘ Δ) := by
    have := Wire.mk x t a b Δ hlin (Multiset.mem_add.2 (Or.inl hxa))
    rwa [Term.subst_of_notMem hxb] at this
  obtain ⟨α, β, r, hr, as, bs, xs, D, f, hlen, hf, hfresh, hN, hE⟩ :=
    hc.refresh hI hW.linear_right fun y hy => hW.mem_vars hy
  have hxN : x ∈ Net.vars (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) := by simp
  have hfx : ∀ w, f w ≠ x := fun w e => hfresh w (e ▸ hxN)
  have hrl := hI _ _ _ hr
  have hT : s(a.subst x t, b) ∈ chain (Term.app α as) xs (Term.app β bs) + D :=
    hN ▸ Multiset.mem_cons_self _ _
  rcases Multiset.mem_add.1 hT with hTc | hTD
  · -- the equation is a link of the chain
    obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem hTc
    rw [hC, Multiset.cons_add] at hN
    have hΔ := (Multiset.cons_inj_right _).1 hN
    subst hΔ
    cases a with
    | var y =>
      have hy : y = x := by simpa [eq_comm] using hxa
      subst hy
      rw [subst_var_self] at hC
      obtain ⟨xs', e⟩ := chain_insert (x := y) _ _ xs C hC
      refine ⟨xs'.length, α, β, r, hr, as, bs, xs', D, f, le_rfl, hf, hfresh, ?_, hE⟩
      rw [← Multiset.cons_add, ← Multiset.cons_add, e]
    | app γ ts =>
      have hcell : ((Term.app γ ts).subst x t).IsCell := isCell_subst ⟨γ, ts, rfl⟩ x t
      obtain ⟨i₀, hi₀⟩ := mem_vars_app hxa
      rcases chain_replace_cell (a' := Term.app γ ts) hcell _ _ xs C hC with ⟨hA, e⟩ | ⟨hB, e⟩
      · -- the cell `α(as)` is `γ(ts)` with `t` plugged into `x`
        rw [subst_app, Term.app.injEq] at hA
        obtain ⟨rfl, hts⟩ := hA
        have hts' := eq_of_heq hts
        have hN' : s(var x, t) ::ₘ s(Term.app γ ts, b) ::ₘ (C + D) =
            chain (Term.app γ ts) xs (Term.app β bs) + s(var x, t) ::ₘ D := by
          rw [← Multiset.cons_add, e, Multiset.add_cons]
        rw [hN'] at hlin hfresh ⊢
        refine ⟨xs.length, γ, β, r, hr, ts, bs, xs, _, f, le_rfl, hf, hfresh, rfl, ?_⟩
        have hl := hlin x
        rw [Net.vars_add, Multiset.count_add, count_vars_chain] at hl
        simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at hl
        have hBx : x ∉ (Term.app β bs).vars := Multiset.count_eq_zero.1 (by omega)
        have hDx : x ∉ Net.vars D := Multiset.count_eq_zero.1 (by omega)
        have L := linear_inst_chain hI hr hf hlin hfresh
        rw [Multiset.add_cons] at L
        have Wr := PairStepE.wire_sub L (by
          rw [Net.vars_add]
          exact Multiset.mem_add.2 (Or.inl (mem_vars_inst_left hrl ts bs f hi₀)))
        have hbs : (fun j => (bs j).subst x t) = bs := funext fun j =>
          Term.subst_of_notMem fun hm => hBx (by
            simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨j, hm⟩)
        rw [Cut.sub_add, sub_inst r ts bs f x t hfx, sub_of_notMem t hDx, hbs, hts',
          ← Multiset.add_cons] at Wr
        exact Wr.equiv.trans hE
      · -- the cell `β(bs)` is `γ(ts)` with `t` plugged into `x`
        rw [subst_app, Term.app.injEq] at hB
        obtain ⟨rfl, hts⟩ := hB
        have hts' := eq_of_heq hts
        have hN' : s(var x, t) ::ₘ s(Term.app γ ts, b) ::ₘ (C + D) =
            chain (Term.app α as) xs (Term.app γ ts) + s(var x, t) ::ₘ D := by
          rw [← Multiset.cons_add, e, Multiset.add_cons]
        rw [hN'] at hlin hfresh ⊢
        refine ⟨xs.length, α, γ, r, hr, as, ts, xs, _, f, le_rfl, hf, hfresh, rfl, ?_⟩
        have hl := hlin x
        rw [Net.vars_add, Multiset.count_add, count_vars_chain] at hl
        simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at hl
        have hAx : x ∉ (Term.app α as).vars := Multiset.count_eq_zero.1 (by omega)
        have hDx : x ∉ Net.vars D := Multiset.count_eq_zero.1 (by omega)
        have L := linear_inst_chain hI hr hf hlin hfresh
        rw [Multiset.add_cons] at L
        have Wr := PairStepE.wire_sub L (by
          rw [Net.vars_add]
          exact Multiset.mem_add.2 (Or.inl (mem_vars_inst_right hrl as ts f hi₀)))
        have has : (fun i => (as i).subst x t) = as := funext fun i =>
          Term.subst_of_notMem fun hm => hAx (by
            simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨i, hm⟩)
        rw [Cut.sub_add, sub_inst r as ts f x t hfx, sub_of_notMem t hDx, has, hts',
          ← Multiset.add_cons] at Wr
        exact Wr.equiv.trans hE
  · -- the equation is in the rest of the net
    obtain ⟨D₁, rfl⟩ := Multiset.exists_cons_of_mem hTD
    rw [Multiset.add_cons] at hN
    have hΔ := (Multiset.cons_inj_right _).1 hN
    subst hΔ
    have hN' : s(var x, t) ::ₘ s(a, b) ::ₘ (chain (Term.app α as) xs (Term.app β bs) + D₁) =
        chain (Term.app α as) xs (Term.app β bs) + s(var x, t) ::ₘ s(a, b) ::ₘ D₁ := by
      rw [Multiset.add_cons, Multiset.add_cons]
    rw [hN'] at hlin hfresh ⊢
    refine ⟨xs.length, α, β, r, hr, as, bs, xs, _, f, le_rfl, hf, hfresh, rfl, ?_⟩
    have L := linear_inst_chain hI hr hf hlin hfresh
    rw [Multiset.add_cons, Multiset.add_cons] at L
    have Wr := Wire.mk x t a b _ L (Multiset.mem_add.2 (Or.inl hxa))
    rw [Term.subst_of_notMem hxb] at Wr
    rw [Multiset.add_cons] at hE
    have e : r.inst as bs f + s(var x, t) ::ₘ s(a, b) ::ₘ D₁ =
        s(var x, t) ::ₘ s(a, b) ::ₘ (r.inst as bs f + D₁) := by
      rw [Multiset.add_cons, Multiset.add_cons]
    rw [e]
    exact Wr.equiv.trans hE

/-- **A wire substitution undone keeps a chain pair** (Lafont 1997, page 73). If `N'` is `N` with
the wire `x = t` contracted and `N'` has a chain pair, so has `N`, with the same interaction up to
wires. -/
theorem ChainPair.wire_symm
    -- every rule of the system is linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- a wire substitution from `N` to `N'`
    {N N' M : Net S ℕ}
    {n : ℕ}
    (h : Wire N N')
    -- a chain pair of `N'` with interaction `M`
    (hc : ChainPair I N' M n) :
    -- `N` has a chain pair, of some length, with the same interaction
    ∃ n', ChainPair I N M n' := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hcx := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcx
  rcases Multiset.mem_add.1 hx with hxa | hxb
  · have hb : x ∉ b.vars := by
      have := Multiset.one_le_count_iff_mem.2 hxa
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem hb] at hc
    exact ChainPair.unsub hI hxa hlin hc
  · have ha : x ∉ a.vars := by
      have := Multiset.one_le_count_iff_mem.2 hxb
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem ha, Sym2.eq_swap] at hc
    rw [Sym2.eq_swap (a := a)] at hlin ⊢
    exact ChainPair.unsub hI hxb hlin hc

/-- **The transport lemma** (Lafont 1997, page 73: reduction is defined on graphs). Two texts of
the same graph have the same chain pairs, with the same interactions up to wires. -/
theorem ChainPair.of_equiv
    -- every rule of the system is linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- two texts of the same graph
    {N N' : Net S ℕ}
    (h : Equiv N N')
    -- the interaction
    (M : Net S ℕ) :
    -- `N` has a chain pair with interaction `M` if and only if `N'` has one
    (∃ n, ChainPair I N M n) ↔ ∃ n, ChainPair I N' M n := by
  induction h with
  | rel _ _ h =>
    exact ⟨fun ⟨n, hc⟩ => ⟨n, hc.wire hI h⟩, fun ⟨_, hc⟩ => hc.wire_symm hI h⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

-- ============================================================================================
-- 4. Auxiliary lemmas: contracting a chain
-- ============================================================================================

/-- Wire substitutions, in any number, give the same graph. -/
theorem equiv_of_wires
    -- wire substitutions done forward from `N` to `K`
    {N K : Net S ℕ}
    (h : Relation.ReflTransGen Wire N K) :
    Equiv N K := by
  induction h with
  | refl => exact Equiv.refl _
  | tail _ w ih => exact ih.trans w.equiv

/-- A chain of a linear net is contracted, link after link, into the equation between its two
ends, by wire substitutions done forward. -/
theorem wires_chain
    -- the last end of the chain and the rest of the net
    (B : Term S ℕ)
    (D : Net S ℕ) :
    -- for every first end `A` and links `xs` such that the net with the chain is linear,
    ∀ (A : Term S ℕ) (xs : List ℕ), (chain A xs B + D).Linear →
      -- wire substitutions done forward lead to the net `A = B, D`
      Relation.ReflTransGen Wire (chain A xs B + D) (s(A, B) ::ₘ D)
  | A, [], _ => by
    rw [chain_nil, Multiset.singleton_add]
  | A, y :: ys, hlin => by
    have e : chain A (y :: ys) B + D = s(var y, A) ::ₘ (chain (var y) ys B + D) := by
      rw [chain_cons, Multiset.cons_add, Sym2.eq_swap]
    rw [e] at hlin ⊢
    have hc := hlin y
    rw [Net.vars_cons, Multiset.count_add, Net.vars_add, Multiset.count_add, count_vars_chain]
      at hc
    simp only [eqVars_mk, Term.vars_var, Multiset.count_add, Multiset.count_singleton_self] at hc
    have hys : y ∉ ys := fun hm => by
      have := List.count_pos_iff.2 hm
      omega
    have hB : y ∉ B.vars := Multiset.count_eq_zero.1 (by omega)
    have hD : y ∉ Net.vars D := Multiset.count_eq_zero.1 (by omega)
    have W := PairStepE.wire_sub hlin (by
      rw [Net.vars_add, Multiset.mem_add, ← Multiset.one_le_count_iff_mem, count_vars_chain]
      left
      simp only [Term.vars_var, Multiset.count_singleton_self]
      omega)
    rw [Cut.sub_add, sub_chain B (var y) ys hys, subst_var_self, Term.subst_of_notMem hB,
      sub_of_notMem A hD] at W
    exact Relation.ReflTransGen.head W (wires_chain B D A ys W.linear_right)

/-- **Contracting a chain pair** (Lafont 1997, page 71: a chain of wires is one wire). A chain
pair of a linear net becomes, by wire substitutions done forward, a chain of length `0`: an
equation between the two cells. -/
theorem ChainPair.contract
    -- a chain pair of a linear net `N`, with interaction `M`
    {N M : Net S ℕ}
    {n : ℕ}
    (h : ChainPair I N M n)
    (hN : N.Linear) :
    -- wire substitutions done forward lead from `N` to a net `K` with a chain of length `0`
    ∃ K, Relation.ReflTransGen Wire N K ∧ ChainPair I K M 0 := by
  obtain ⟨α, β, r, hr, as, bs, xs, D, f, -, hf, hfresh, rfl, hE⟩ := h
  refine ⟨_, wires_chain _ D _ xs hN, α, β, r, hr, as, bs, [], D, f, le_rfl, hf,
    fun i => ?_, by simp, hE⟩
  exact notMem_short (hfresh i)

/-- Wire substitutions done forward keep a chain pair, and do not make the chain longer. -/
theorem ChainPair.wires
    -- every rule of the system is linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- wire substitutions done forward from `N` to `K`
    {N K M : Net S ℕ}
    {n : ℕ}
    (h : Relation.ReflTransGen Wire N K)
    -- a chain pair of `N` of length at most `n`, with interaction `M`
    (hc : ChainPair I N M n) :
    ChainPair I K M n := by
  induction h with
  | refl => exact hc
  | tail _ w ih => exact ih.wire hI w

end StrongConfluenceE

-- ============================================================================================
-- 5. Main result: Proposition 1 for reduction of graphs
-- ============================================================================================

open StrongConfluenceE

/-- **Proposition 1 for reduction of graphs** (Lafont 1997, Proposition 1, page 73: "If a net `N`
reduces in one step to `P` and to `P'`, with `P ≠ P'`, then `P` and `P'` reduce in one step to a
common `Q`"). Nets are graphs, so equality of nets is `Equiv` and one step is `StepE`, an
interaction that may first rewrite the net into another text of the same graph. If a linear net
`N` reduces by one `StepE` to `M₁` and to `M₂`, then either `M₁` and `M₂` are the same graph, or
each reduces by one `StepE` to a net, and the two nets are the same graph.

The two interactions fire in two texts `N₁`, `N₂` of `N`. The active pair fired in `N₂` is a
chain of wires in `N₁` (`ChainPair.of_equiv`); contracting it gives a text `K` in which both active
pairs are equations (`ChainPair.contract`, `ChainPair.wires`), and Proposition 1 for literal steps
(`Step.strong_confluence`) applies to `K`. -/
theorem StepE.strong_confluence
    -- a well-formed interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a linear net `N`
    {N M₁ M₂ : Net S ℕ}
    (hN : N.Linear)
    -- two reductions of graphs, in one step, from `N` to `M₁` and to `M₂`
    (h₁ : StepE I N M₁)
    (h₂ : StepE I N M₂) :
    -- either `M₁` and `M₂` are the same graph,
    Equiv M₁ M₂ ∨
    -- or each reduces in one step to a net, and the two nets are the same graph
    ∃ P₁ P₂, StepE I M₁ P₁ ∧ StepE I M₂ P₂ ∧ Equiv P₁ P₂ := by
  obtain ⟨N₁, e₁, s₁⟩ := h₁
  obtain ⟨N₂, e₂, s₂⟩ := h₂
  have hl := hI.linear
  have hN₁ := e₁.linear hN
  obtain ⟨n, c₂⟩ :=
    (ChainPair.of_equiv hl (e₂.symm.trans e₁) M₂).1 ⟨0, ChainPair.of_step s₂⟩
  obtain ⟨K, hK, c₂'⟩ := c₂.contract hN₁
  have c₁ := (ChainPair.of_step s₁).wires hl hK
  have hKl : K.Linear := (equiv_of_wires hK).linear hN₁
  obtain ⟨M₁', t₁, E₁⟩ := c₁.step
  obtain ⟨M₂', t₂, E₂⟩ := c₂'.step
  rcases Step.strong_confluence hI hKl t₁ t₂ with E | ⟨P₁, P₂, u₁, u₂, EP⟩
  · exact Or.inl (E₁.symm.trans (E.trans E₂))
  · exact Or.inr ⟨P₁, P₂, ⟨M₁', E₁.symm, u₁⟩, ⟨M₂', E₂.symm, u₂⟩, EP⟩

end INet
