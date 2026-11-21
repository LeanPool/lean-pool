/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.StepsEAdd
public import LeanPool.InteractionCombinators.Text.NetTrWire
public import LeanPool.InteractionCombinators.Reduction.Commute

/-!
# Proposition 4: a translation of interaction systems simulates reduction

Lafont 1997, Proposition 4, page 81: "If N reduces in n steps to M, then Φ(N) reduces in n′ steps
to Φ(M)". The paper says "Obviously"; the work is in the names.

`Translation.Compatible` speaks of the two cells of a rule with plain names `xs`, `ys` on their
auxiliary ports and nothing around them. Inside a net the auxiliary ports carry trees `as`, `bs`
and there is a context `Δ`. The proof does not substitute trees into a reduction. It expands the
active pair instead: with fresh names `xs`, `ys`,

  `α(as) = β(bs), Δ`  is the same graph as  `α(xs) = β(ys), Δ, xs = as, ys = bs`

(`Simulation.equiv_expand`). The translation follows the equivalence (`NetTr.of_equiv`), the
compatibility applies to the first equation, the reduction is done beside the rest
(`StepsE.add_right`), and the wires `xs = as`, `ys = bs` are contracted again on the right-hand
side (`Simulation.equiv_contract_inst`).

Contents, in the order of the file:

1. Definitions: `Simulation.wires` (the wires `p = σ p`), `Simulation.ports` (the fresh names on
   the auxiliary ports of an active pair), `Simulation.arg` (the tree plugged into a fresh name),
   `Simulation.pairVar` (the active pair with the fresh names), `Translation.CompatibleBy`
   (compatibility for any reduction `R` of the target), `Translation.CompatibleByDistinct` (the
   same, for distinct names on the ports).
2. Auxiliary lemmas, contracting wires: `Simulation.equiv_wire_net` (one wire),
   `Simulation.equiv_contract_list` (several wires), `Simulation.bind_ofFn`,
   `Simulation.sum_singleton_ofFn`.
3. Auxiliary lemmas, the fresh names: `Simulation.arg_left`, `Simulation.arg_right`,
   `Simulation.mem_ports`, `Simulation.nodup_ports`, `Simulation.fresh_arg`,
   `Simulation.bind_arg_below`, `Simulation.vars_wires_ports`.
4. Auxiliary lemmas, expanding the active pair and contracting the right member:
   `Simulation.equiv_expand`, `Simulation.equiv_contract_inst`.
5. Auxiliary lemmas, reduction up to wires and translations: `StepE.free_iff`,
   `StepsE.free_iff` (the free ports are kept), `StepsE.of_equiv`, `Translation.TermTr.var_inv`,
   `Translation.TermTr.app_var_inv`, `Translation.compatible_iff_compatibleBy`,
   `Translation.CompatibleBy.distinct`.
6. Main results, Proposition 4 (page 81): `Translation.CompatibleByDistinct.step`,
   `Translation.CompatibleBy.step`, `Translation.Compatible.step` (one interaction is
   simulated), `Translation.Compatible.steps` (any number of interactions are simulated).
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

namespace Simulation

/-- The wires `p = σ p`, for the names `p` of a list. -/
abbrev wires
    -- the tree on the other end of each name
    (σ : ℕ → Term S ℕ)
    -- the names
    (l : List ℕ) :
    Net S ℕ :=
  (l : Multiset ℕ).map fun p => s(var p, σ p)

/-- The fresh names put on the auxiliary ports of an active pair, from the bound `B` on: `B + i`
for the `i`-th port of the first cell, `B + a + j` for the `j`-th port of the second. -/
def ports
    -- the bound, and the arities of the two cells
    (B a b : ℕ) :
    List ℕ :=
  List.ofFn (fun i : Fin a => B + i) ++ List.ofFn (fun j : Fin b => B + a + j)

/-- The tree plugged into a fresh name: `as i` into `B + i`, `bs j` into `B + a + j`. -/
def arg
    -- the arities of the two cells, and the bound
    {a b : ℕ}
    (B : ℕ)
    -- the trees on the auxiliary ports of the two cells
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- the name
    (z : ℕ) :
    Term S ℕ :=
  if h : B ≤ z ∧ z < B + a then as ⟨z - B, by omega⟩
  else if h' : B + a ≤ z ∧ z < B + a + b then bs ⟨z - B - a, by omega⟩ else var z

/-- The active pair `α(xs) = β(ys)` with the fresh names `xs i = B + i`, `ys j = B + a + j`. -/
abbrev pairVar
    -- the bound, and the symbols of the two cells
    (B : ℕ)
    (α β : S.Sym) :
    Sym2 (Term S ℕ) :=
  s(.app α fun i => var (B + i), .app β fun j => var (B + S.arity α + j))

end Simulation

/-- `Translation.Compatible`, with the reduction of each rule taken in a relation `R` on the nets
of the target instead of `StepsE I'`. `Compatible` is the case `R = StepsE I'`
(`Translation.compatible_iff_compatibleBy`); a reduction counted and bounded is another case
(Lafont 1997, page 81, the lengths `L` and `M`). -/
def Translation.CompatibleBy
    -- the translation, and the interaction system of the source
    (Φ : Translation S S')
    (I : System S)
    -- the reduction of the target
    (R : Net S' ℕ → Net S' ℕ → Prop) :
    Prop :=
  -- for every rule `r` of `I` between `α` and `β`,
  ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
    -- all names `xs`, `ys` on the ports and `f`, `g` on the internal wires of the translations,
    ∀ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
      (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
      -- if the translations of the two cells, plugged by their roots, form a linear net,
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
      -- then this net reduces by `R` to a net `M`
      ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
        R {s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
        -- which is the same graph as `N'`
        Equiv M N' ∧
        -- a translation of the right member, with the same names on the ports
        Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'

/-- `Translation.CompatibleBy`, for distinct names only: the rule is simulated when the names
`xs` on the ports of the first cell are pairwise distinct, those `ys` of the second too, and no
`xs i` is a `ys j`, as for the two cells of a rule in the paper (Lafont 1997, page 81). The
proof of Proposition 4 only uses this case (`Translation.CompatibleByDistinct.step`). -/
def Translation.CompatibleByDistinct
    -- the translation, and the interaction system of the source
    (Φ : Translation S S')
    (I : System S)
    -- the reduction of the target
    (R : Net S' ℕ → Net S' ℕ → Prop) :
    Prop :=
  -- for every rule `r` of `I` between `α` and `β`,
  ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
    -- all names `xs`, `ys` on the ports and `f`, `g` on the internal wires of the translations,
    ∀ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
      (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
      -- if the names on the ports are pairwise distinct,
      Function.Injective xs → Function.Injective ys → (∀ i j, xs i ≠ ys j) →
      -- and the translations of the two cells, plugged by their roots, form a linear net,
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
      -- then this net reduces by `R` to a net `M`
      ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
        R {s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
        -- which is the same graph as `N'`
        Equiv M N' ∧
        -- a translation of the right member, with the same names on the ports
        Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'

namespace Simulation

-- ============================================================================================
-- 2. Auxiliary lemmas: contracting wires
-- ============================================================================================

/-- **One wire, anywhere in a net.** An equation `x = t` whose name `x` has its other end in `K`
is the same graph as `K` with `t` plugged into `x` (Lafont 1997, Section 1.1, page 71). -/
theorem equiv_wire_net
    -- the wire `x = t`, and the rest of the net
    {x : ℕ}
    {t : Term S ℕ}
    {K : Net S ℕ}
    -- the net is linear, and the other end of `x` is in `K`
    (hlin : Net.Linear (s(var x, t) ::ₘ K))
    (hx : x ∈ K.vars) :
    -- the net is the same graph as `K` with `t` plugged into `x`
    Equiv (s(var x, t) ::ₘ K) (K.bind fun z => if z = x then t else var z) := by
  obtain ⟨e, he, hxe⟩ : ∃ e ∈ K, x ∈ eqVars e := by
    simpa [Net.vars, Multiset.mem_bind] using hx
  obtain ⟨K', rfl⟩ := Multiset.exists_cons_of_mem he
  induction e using Sym2.ind with
  | _ a b =>
    have W := Wire.mk x t a b K' hlin hxe
    refine W.equiv.trans (Equiv.of_eq ?_)
    have hc := hlin x
    simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at hc
    have h1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hxe
    rw [Multiset.count_add] at h1
    have hK' : x ∉ Net.vars K' := Multiset.count_eq_zero.1 (by omega)
    rw [Net.bind_cons]
    congr 1
    conv_lhs => rw [← Net.bind_var_self K']
    exact Net.bind_congr fun z hz => by simp [show z ≠ x from fun h => hK' (h ▸ hz)]

/-- A name of the wires `p = σ p` is a name `q` of the list or a name of its tree `σ q`. -/
theorem mem_vars_wires
    -- the wires
    {σ : ℕ → Term S ℕ}
    {l : List ℕ}
    -- a name of the wires
    {z : ℕ}
    (hz : z ∈ (wires σ l).vars) :
    -- it is a name `q` of the list, or a name of `σ q`
    ∃ q ∈ l, z = q ∨ z ∈ (σ q).vars := by
  simp only [wires, Net.vars, Multiset.mem_bind, Multiset.mem_map, Multiset.mem_coe] at hz
  obtain ⟨e, ⟨q, hq, rfl⟩, hz⟩ := hz
  simp only [eqVars_mk, vars_var, Multiset.mem_add, Multiset.mem_singleton] at hz
  exact ⟨q, hq, hz⟩

/-- **Several wires, contracted.** If the names `p` of a list each have one end in `K` and the
other in an equation `p = σ p`, and no `σ q` uses a name of the list, the net `K, (p = σ p)ₚ` is
the same graph as `K` with `σ p` plugged into each `p` (Lafont 1997, Section 1.1, page 71). -/
theorem equiv_contract_list
    -- the tree on the other end of each name
    (σ : ℕ → Term S ℕ) :
    -- for a list `l` of names and a net `K`:
    ∀ (l : List ℕ) (K : Net S ℕ),
      -- if the names of the list are distinct,
      l.Nodup →
      -- no tree `σ q` uses a name of the list,
      (∀ p ∈ l, ∀ q ∈ l, p ∉ (σ q).vars) →
      -- every name of the list occurs in `K`,
      (∀ p ∈ l, p ∈ K.vars) →
      -- and `K` with the wires is linear,
      (K + wires σ l).Linear →
      -- then `K` with the wires is the same graph as `K` with `σ p` plugged into each `p`
      Equiv (K + wires σ l) (K.bind fun z => if z ∈ l then σ z else var z)
  | [], K, _, _, _, _ => by
    simpa [wires] using Equiv.of_eq (Net.bind_var_self K).symm
  | p :: l, K, hnd, hσ, hK, hlin => by
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have e0 : K + wires σ (p :: l) = s(var p, σ p) ::ₘ (K + wires σ l) := by
      rw [wires, ← Multiset.cons_coe, Multiset.map_cons, Multiset.add_cons]
    rw [e0] at hlin ⊢
    have hpK : p ∈ Net.vars (K + wires σ l) := by
      rw [Net.vars_add]; exact Multiset.mem_add.2 (Or.inl (hK p (by simp)))
    have E1 := equiv_wire_net hlin hpK
    -- the wires of `l` do not see `p`
    have hW : (wires σ l).bind (fun z => if z = p then σ p else var z) = wires σ l := by
      conv_rhs => rw [← Net.bind_var_self (wires σ l)]
      refine Net.bind_congr fun z hz => ?_
      obtain ⟨q, hq, hz⟩ := mem_vars_wires hz
      have hzp : z ≠ p := by
        rintro rfl
        rcases hz with rfl | hz
        · exact hpl hq
        · exact hσ z (by simp) q (by simp [hq]) hz
      simp [hzp]
    rw [Net.bind_add, hW] at E1
    set K₁ := K.bind fun z => if z = p then σ p else var z with hK₁
    have hK₁l : ∀ q ∈ l, q ∈ K₁.vars := by
      intro q hq
      have hqp : q ≠ p := fun h => hpl (h ▸ hq)
      rw [hK₁, Net.vars_bind, Multiset.mem_bind]
      exact ⟨q, hK q (by simp [hq]), by simp [hqp]⟩
    have IH := equiv_contract_list σ l K₁ (List.nodup_cons.1 hnd).2
      (fun p' hp' q hq => hσ p' (by simp [hp']) q (by simp [hq])) hK₁l (E1.linear hlin)
    refine E1.trans (IH.trans (Equiv.of_eq ?_))
    rw [hK₁, Net.bind_bind]
    refine Net.bind_congr fun z _ => ?_
    by_cases hzp : z = p
    · subst hzp
      simp only [ite_true, List.mem_cons, true_or]
      conv_rhs => rw [← Term.bind_var_self (σ z)]
      refine Term.bind_congr fun y hy => ?_
      have hyl : y ∉ l := fun h => hσ y (by simp [h]) z (by simp) hy
      simp [hyl]
    · simp [hzp]

/-- A multiset of names given as a list of values, bound: the sum over the indices. -/
theorem bind_ofFn
    -- the values, and the multiset of each value
    {n : ℕ}
    (f : Fin n → ℕ)
    (g : ℕ → Multiset ℕ) :
    ((List.ofFn f : List ℕ) : Multiset ℕ).bind g = ∑ i, g (f i) := by
  rw [← Fin.univ_val_map, Multiset.bind_map]
  rfl

/-- The sum of the singletons of the values of `f` is the list of its values. -/
theorem sum_singleton_ofFn
    -- the values
    {n : ℕ}
    (f : Fin n → ℕ) :
    ∑ i, ({f i} : Multiset ℕ) = ((List.ofFn f : List ℕ) : Multiset ℕ) := by
  rw [← Fin.univ_val_map]
  have := Multiset.sum_map_singleton (Finset.univ.val.map f)
  rw [Multiset.map_map] at this
  exact this

-- ============================================================================================
-- 3. Auxiliary lemmas: the fresh names of the expansion
-- ============================================================================================

variable {a b : ℕ}

/-- The tree plugged into the fresh name `B + i` is `as i`. -/
theorem arg_left
    -- the bound, and the trees on the auxiliary ports of the two cells
    (B : ℕ)
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- a port of the first cell
    (i : Fin a) :
    arg B as bs (B + i) = as i := by
  unfold arg
  split_ifs with h1
  · congr 1
    exact Fin.ext (by simp)
  all_goals omega

/-- The tree plugged into the fresh name `B + a + j` is `bs j`. -/
theorem arg_right
    -- the bound, and the trees on the auxiliary ports of the two cells
    (B : ℕ)
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- a port of the second cell
    (j : Fin b) :
    arg B as bs (B + a + j) = bs j := by
  unfold arg
  split_ifs with h1 h2
  · omega
  · congr 1
    exact Fin.ext (by simp; omega)
  · omega

/-- The fresh names are the numbers from `B` to `B + a + b`, excluded. -/
theorem mem_ports {B z : ℕ} : z ∈ ports B a b ↔ B ≤ z ∧ z < B + a + b := by
  simp only [ports, List.mem_append, List.mem_ofFn]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩) <;> omega
  · rintro ⟨h1, h2⟩
    by_cases h : z < B + a
    · exact Or.inl ⟨⟨z - B, by omega⟩, by simp; omega⟩
    · exact Or.inr ⟨⟨z - B - a, by omega⟩, by simp; omega⟩

/-- The name `B + i` of the `i`-th port of the first cell is a fresh name. -/
theorem left_mem_ports (B : ℕ) (i : Fin a) : B + (i : ℕ) ∈ ports B a b :=
  List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- The name `B + a + j` of the `j`-th port of the second cell is a fresh name. -/
theorem right_mem_ports (B : ℕ) (j : Fin b) : B + a + (j : ℕ) ∈ ports B a b :=
  List.mem_append_right _ (List.mem_ofFn.2 ⟨j, rfl⟩)

/-- The fresh names are distinct. -/
theorem nodup_ports (B a b : ℕ) : (ports B a b).Nodup := by
  rw [ports, List.nodup_append]
  refine ⟨List.nodup_ofFn.2 fun i j h => Fin.ext (by simpa using h),
    List.nodup_ofFn.2 fun i j h => Fin.ext (by simpa using h), ?_⟩
  intro x hx y hy
  simp only [List.mem_ofFn] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  omega

/-- Nothing is plugged into a name below `B`. -/
theorem arg_below
    -- a name below the bound
    {B z : ℕ}
    (hz : z < B)
    -- the trees on the auxiliary ports of the two cells
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ) :
    arg B as bs z = var z := by
  unfold arg
  split_ifs <;> first | rfl | omega

/-- The names of the trees plugged into the fresh names are below `B`. -/
theorem below_arg
    -- the bound, and the trees on the auxiliary ports, whose names are below it
    {B : ℕ}
    {as : Fin a → Term S ℕ}
    {bs : Fin b → Term S ℕ}
    (has : ∀ i, (as i).Below B)
    (hbs : ∀ j, (bs j).Below B)
    -- a fresh name
    {p : ℕ}
    (hp : p ∈ ports B a b) :
    (arg B as bs p).Below B := by
  simp only [ports, List.mem_append, List.mem_ofFn] at hp
  rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [arg_left]; exact has i
  · rw [arg_right]; exact hbs j

/-- No tree plugged into a fresh name uses a fresh name. -/
theorem fresh_arg
    -- the bound, and the trees on the auxiliary ports, whose names are below it
    {B : ℕ}
    {as : Fin a → Term S ℕ}
    {bs : Fin b → Term S ℕ}
    (has : ∀ i, (as i).Below B)
    (hbs : ∀ j, (bs j).Below B) :
    ∀ p ∈ ports B a b, ∀ q ∈ ports B a b, p ∉ (arg B as bs q).vars := by
  intro p hp q hq hm
  have := below_arg has hbs hq p hm
  have := (mem_ports.1 hp).1
  omega

/-- Plugging the trees into the fresh names leaves a net below `B` unchanged. -/
theorem bind_arg_below
    -- the bound, and the trees on the auxiliary ports of the two cells
    {B : ℕ}
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- a net whose names are below the bound
    {Δ : Net S ℕ}
    (hΔ : Δ.Below B) :
    Δ.bind (fun z => if z ∈ ports B a b then arg B as bs z else var z) = Δ := by
  conv_rhs => rw [← Net.bind_var_self Δ]
  refine Net.bind_congr fun z hz => ?_
  have : z ∉ ports B a b := fun h => by have := hΔ z hz; have := (mem_ports.1 h).1; omega
  simp [this]

/-- The names of the wires `p = σ p` are the names of the list and the names of the trees. -/
theorem vars_wires
    -- the wires
    (σ : ℕ → Term S ℕ)
    (l : List ℕ) :
    (wires σ l).vars = (l : Multiset ℕ) + (l : Multiset ℕ).bind fun p => (σ p).vars := by
  simp only [wires, Net.vars, Multiset.bind_map, eqVars_mk, vars_var]
  rw [Multiset.bind_add, Multiset.bind_singleton, Multiset.map_id']

/-- The names of the wires `xs = as`, `ys = bs` are the fresh names and the names of the trees. -/
theorem vars_wires_ports
    -- the bound, and the trees on the auxiliary ports of the two cells
    (B : ℕ)
    (as : Fin (a) → Term S ℕ)
    (bs : Fin b → Term S ℕ) :
    (wires (arg B as bs) (ports B a b)).vars
      = (ports B a b : Multiset ℕ) + ((∑ i, (as i).vars) + ∑ j, (bs j).vars) := by
  rw [vars_wires]
  congr 1
  rw [ports, ← Multiset.coe_add, Multiset.add_bind, bind_ofFn, bind_ofFn]
  simp only [arg_left, arg_right]

-- ============================================================================================
-- 4. Auxiliary lemmas: expanding the active pair, contracting the right member
-- ============================================================================================

/-- The fresh names occur in the active pair `α(xs) = β(ys)`. -/
theorem mem_vars_pairVar
    -- the bound, and the symbols of the two cells
    {B : ℕ}
    {α β : S.Sym}
    -- a fresh name
    {p : ℕ}
    (hp : p ∈ ports B (S.arity α) (S.arity β)) :
    p ∈ eqVars (pairVar B α β) := by
  simp only [ports, List.mem_append, List.mem_ofFn] at hp
  simp only [eqVars_mk, vars_app, vars_var, Multiset.mem_add, Multiset.mem_sum, Finset.mem_univ,
    true_and, Multiset.mem_singleton]
  rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

/-- **The active pair, expanded** (Lafont 1997, Section 1.2, page 73). With the names from `B` on
unused, `α(as) = β(bs), Δ` is the same graph as `α(xs) = β(ys), Δ, xs = as, ys = bs`, and the
expanded net is linear. -/
theorem equiv_expand
    -- the bound, and the active pair `α(as) = β(bs)`
    {B : ℕ}
    {α β : S.Sym}
    {as : Fin (S.arity α) → Term S ℕ}
    {bs : Fin (S.arity β) → Term S ℕ}
    -- the rest of the net
    {Δ : Net S ℕ}
    -- the net is linear, and its names are below `B`
    (hN : Net.Linear (s(.app α as, .app β bs) ::ₘ Δ))
    (hB : Net.Below B (s(.app α as, .app β bs) ::ₘ Δ)) :
    -- the expanded net `α(xs) = β(ys), Δ, xs = as, ys = bs` is linear,
    Net.Linear ((pairVar B α β ::ₘ Δ) + wires (arg B as bs) (ports B (S.arity α) (S.arity β))) ∧
      -- and the net is the same graph as the expanded net
      Equiv (s(.app α as, .app β bs) ::ₘ Δ)
        ((pairVar B α β ::ₘ Δ) + wires (arg B as bs) (ports B (S.arity α) (S.arity β))) := by
  obtain ⟨hA, hBb, hΔ⟩ := Net.below_cons.1 hB
  have has : ∀ i, (as i).Below B := fun i x hx => hA x (by
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨i, hx⟩)
  have hbs : ∀ j, (bs j).Below B := fun j x hx => hBb x (by
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨j, hx⟩)
  have hlin : Net.Linear
      ((pairVar B α β ::ₘ Δ) + wires (arg B as bs) (ports B (S.arity α) (S.arity β))) := by
    refine Net.Linear.add_fresh hN (ports B (S.arity α) (S.arity β) : Multiset ℕ)
      (Multiset.coe_nodup.2 (nodup_ports _ _ _))
      (fun x hx hm => by have := hB x hm; have := (mem_ports.1 hx).1; omega) ?_
    rw [Net.vars_add, vars_wires_ports, Net.vars_cons, Net.vars_cons]
    simp only [eqVars_mk, vars_app, vars_var, sum_singleton_ofFn, ports, ← Multiset.coe_add]
    abel
  refine ⟨hlin, ((equiv_contract_list _ _ _ (nodup_ports _ _ _) (fresh_arg has hbs)
    (fun p hp => by
      rw [Net.vars_cons]; exact Multiset.mem_add.2 (Or.inl (mem_vars_pairVar hp))) hlin).trans
    (Equiv.of_eq ?_)).symm⟩
  rw [Net.bind_cons, bind_arg_below as bs hΔ]
  congr 2
  · simp only [bind_app, bind_var]
    congr 1
    funext i
    rw [ite_eq_left_of_eq_true _ _ (eq_true (left_mem_ports B i)), arg_left]
  · simp only [bind_app, bind_var]
    congr 1
    funext j
    rw [ite_eq_left_of_eq_true _ _ (eq_true (right_mem_ports B j)), arg_right]

/-- **The right-hand side, contracted** (Lafont 1997, Section 1.2, page 73). An instance of a
linear rule with the fresh names `xs`, `ys` on the ports, beside `Δ` and the wires `xs = as`,
`ys = bs`, is the same graph as the instance with `as`, `bs` on the ports, beside `Δ`. -/
theorem equiv_contract_inst
    -- the bound, the symbols of the two cells, and a linear rule between them
    {B : ℕ}
    {α β : S.Sym}
    (r : Rule S (S.arity α) (S.arity β))
    (hr : r.Linear)
    -- the trees on the auxiliary ports, the rest of the net, and the names of the internal wires
    {as : Fin (S.arity α) → Term S ℕ}
    {bs : Fin (S.arity β) → Term S ℕ}
    {Δ : Net S ℕ}
    (h₂ : Fin r.internal → ℕ)
    -- the names of the trees and of the rest are below `B`
    (has : ∀ i, (as i).Below B)
    (hbs : ∀ j, (bs j).Below B)
    (hΔ : Δ.Below B)
    -- the instance with the fresh names, beside `Δ` and the wires `xs = as`, `ys = bs`, is linear
    (hlin : Net.Linear ((r.inst (fun i => var (B + i)) (fun j => var (B + S.arity α + j)) h₂ + Δ)
      + wires (arg B as bs) (ports B (S.arity α) (S.arity β)))) :
    -- it is the same graph as the instance with `as`, `bs` on the ports, beside `Δ`
    Equiv ((r.inst (fun i => var (B + i)) (fun j => var (B + S.arity α + j)) h₂ + Δ)
      + wires (arg B as bs) (ports B (S.arity α) (S.arity β))) (r.inst as bs h₂ + Δ) := by
  refine (equiv_contract_list _ _ _ (nodup_ports _ _ _) (fresh_arg has hbs) ?_ hlin).trans
    (Equiv.of_eq ?_)
  · intro p hp
    rw [Net.vars_add]
    refine Multiset.mem_add.2 (Or.inl ?_)
    rw [Rule.inst, Net.vars_bind, Multiset.mem_bind]
    simp only [ports, List.mem_append, List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨.inl i, Multiset.one_le_count_iff_mem.1 (by rw [hr.left]), by simp⟩
    · exact ⟨.inr (.inl j), Multiset.one_le_count_iff_mem.1 (by rw [hr.right]), by simp⟩
  · have hf := (r.facts_of_linear hr
      (Γ := Δ + wires (arg B as bs) (ports B (S.arity α) (S.arity β)))
      (hlin.cast (add_assoc _ _ _))).2
    rw [Net.bind_add, bind_arg_below as bs hΔ, Rule.inst, Rule.inst, Net.bind_bind]
    congr 1
    refine Net.bind_congr fun p _ => ?_
    rcases p with i | j | w
    · simp only [Sum.elim_inl, bind_var]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (left_mem_ports B i)), arg_left]
    · simp only [Sum.elim_inr, Sum.elim_inl, bind_var]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (right_mem_ports B j)), arg_right]
    · have hw : h₂ w ∉ ports B (S.arity α) (S.arity β) := fun hm => (hf w).2.2.1 (by
        rw [Net.vars_add, vars_wires]
        exact Multiset.mem_add.2 (Or.inr (Multiset.mem_add.2 (Or.inl (Multiset.mem_coe.2 hm)))))
      simp [hw]

end Simulation

-- ============================================================================================
-- 5. Auxiliary lemmas: reduction up to wires, translations of cells
-- ============================================================================================

/-- One interaction up to wires keeps the free ports (Lafont 1997, Section 1.2, page 73). -/
theorem StepE.free_iff
    -- an interaction system with linear rules
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- one interaction up to wires from `N` to `M`
    {N M : Net S ℕ}
    (h : StepE I N M)
    -- a name
    (y : ℕ) :
    -- it is a free port of `M` exactly when it is a free port of `N`
    M.vars.count y = 1 ↔ N.vars.count y = 1 := by
  obtain ⟨K, hE, hS⟩ := h
  exact (hS.free_iff hI y).trans (hE.free_iff y).symm

/-- Reduction up to wires keeps the free ports (Lafont 1997, Section 1.2, page 73). -/
theorem StepsE.free_iff
    -- an interaction system with linear rules
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- a reduction up to wires from `N` to `M`
    {N M : Net S ℕ}
    (h : StepsE I N M)
    -- a name
    (y : ℕ) :
    -- it is a free port of `M` exactly when it is a free port of `N`
    M.vars.count y = 1 ↔ N.vars.count y = 1 := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hs ih => exact (hs.free_iff hI y).trans ih

/-- **An equivalence followed by a reduction up to wires.** If `N` is the same graph as `K` and `K`
reduces to `M`, then `N` reduces to a net that is the same graph as `M` (Lafont 1997, Section 1.2,
page 73: reduction is defined on graphs). -/
theorem StepsE.of_equiv
    -- an interaction system
    {I : System S}
    -- `N` is the same graph as `K`, and `K` reduces up to wires to `M`
    {N K M : Net S ℕ}
    (hE : Equiv N K)
    (h : StepsE I K M) :
    -- `N` reduces up to wires to a net `M'` that is the same graph as `M`
    ∃ M',
      StepsE I N M' ∧
      Equiv M' M := by
  induction h with
  | refl => exact ⟨N, Relation.ReflTransGen.refl, hE⟩
  | tail _ hs ih =>
    obtain ⟨M', h1, h2⟩ := ih
    exact ⟨_, h1.tail (StepE.of_equiv h2 hs), Equiv.refl _⟩

namespace Translation

variable {Φ : Translation S S'}

/-- The only translation of a name is the name. -/
theorem TermTr.var_inv
    -- a translation `t'` of the name `x`
    {x : ℕ}
    {t' : Term S' ℕ}
    (h : Φ.TermTr (.var x) t') :
    t' = .var x := by
  cases h
  rfl

/-- The translations of a cell with names on its auxiliary ports are the instances of its
principal net with the same names on the ports (Lafont 1997, Section 1.7, page 80). -/
theorem TermTr.app_var_inv
    -- a cell `α` with the names `xs` on its auxiliary ports, and a translation `t'` of it
    {α : S.Sym}
    {xs : Fin (S.arity α) → ℕ}
    {t' : Term S' ℕ}
    (h : Φ.TermTr (.app α fun i => .var (xs i)) t') :
    -- `t'` is the principal net of `α` with `xs` on its ports and some names `f` inside
    ∃ f, t' = (Φ.net α).inst (fun i => .var (xs i)) f := by
  cases h with
  | app _ _ ts' f hh =>
    refine ⟨f, ?_⟩
    congr 1
    funext i
    exact (hh i).var_inv

end Translation

/-- A translation of interaction systems (Lafont 1997, Section 1.7, page 81) is one compatible by
the reduction up to wires of the target. -/
theorem Translation.compatible_iff_compatibleBy
    -- a translation, and the interaction systems of the source and of the target
    {Φ : Translation S S'}
    {I : System S}
    {I' : System S'} :
    Φ.Compatible I I' ↔ Φ.CompatibleBy I (StepsE I') := Iff.rfl

/-- A translation compatible for all names is compatible for distinct names. -/
theorem Translation.CompatibleBy.distinct
    -- a translation, the interaction system of the source, and a reduction of the target
    {Φ : Translation S S'}
    {I : System S}
    {R : Net S' ℕ → Net S' ℕ → Prop}
    -- `Φ` is compatible by `R` for all names
    (h : Φ.CompatibleBy I R) :
    Φ.CompatibleByDistinct I R :=
  fun α β r hr xs ys f g _ _ _ hl => h α β r hr xs ys f g hl

-- ============================================================================================
-- 6. Main results: Proposition 4
-- ============================================================================================

/-- **One interaction is simulated, for any reduction of the target** (Lafont 1997,
Proposition 4, page 81, the case of one step). `R` is a reduction of the target nets that can be
done beside a context (`hadd`), that can start from an equivalent net (`heq`), and that is a
reduction up to wires (`hR`). If the translations of the two cells of every rule, with distinct
names on their ports, reduce by `R` to a translation of its right-hand side, `N` reduces to `M` by
one interaction, and `N'` is a translation of `N`, then `N'` reduces by `R` to a net that is the
same graph as a translation of `M`. The rules of `I` and of `I'` are linear, as Lafont's rules are
(page 73). -/
theorem Translation.CompatibleByDistinct.step
    -- the interaction systems of the source and of the target, and a reduction of the target
    {I : System S}
    {I' : System S'}
    {R : Net S' ℕ → Net S' ℕ → Prop}
    -- the rules of both systems are linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- `R` can be done beside a context `Γ`
    (hadd : ∀ {N M : Net S' ℕ} (Γ : Net S' ℕ), R N M → (N + Γ).Linear →
      ∃ M', R (N + Γ) (M' + Γ) ∧ Equiv M' M ∧ (M' + Γ).Linear)
    -- `R` can start from the same graph
    (heq : ∀ {N K M : Net S' ℕ}, Equiv N K → R K M → ∃ M', R N M' ∧ Equiv M' M)
    -- `R` is a reduction up to wires
    (hR : ∀ {N M : Net S' ℕ}, R N M → StepsE I' N M)
    -- the translation, compatible by `R` for distinct names
    {Φ : Translation S S'}
    (hΦ : Φ.CompatibleByDistinct I R)
    -- one interaction from `N` to `M`, and a translation `N'` of `N`
    {N M : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Step I N M)
    (hT : Φ.NetTr N N') :
    -- there are nets `M₁` and `M'` such that
    ∃ M₁ M',
      -- `N'` reduces by `R` to `M₁`,
      R N' M₁ ∧
      -- `M₁` is the same graph as `M'`,
      Equiv M₁ M' ∧
      -- and `M'` is a translation of `M`
      Φ.NetTr M M' := by
  obtain ⟨α, β, r, hr, as, bs, Δ, hh, hhinj, hhfresh⟩ := h
  have hN := hT.linear_source
  have hrl := hI _ _ _ hr
  -- the expanded source net
  obtain ⟨B, hB⟩ := Net.exists_below (s(.app α as, .app β bs) ::ₘ Δ)
  obtain ⟨hlin₀, E₀⟩ := Simulation.equiv_expand hN hB
  obtain ⟨hA, hBb, hΔ⟩ := Net.below_cons.1 hB
  have has : ∀ i, (as i).Below B := fun i x hx => hA x (by
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨i, hx⟩)
  have hbs : ∀ j, (bs j).Below B := fun j x hx => hBb x (by
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨j, hx⟩)
  set W := Simulation.wires (Simulation.arg B as bs) (Simulation.ports B (S.arity α) (S.arity β))
    with hW
  -- its translation, taken apart
  obtain ⟨N₀', hT₀, E₀'⟩ := hT.of_equiv E₀
  have hrel := hT₀.rel
  rw [Multiset.cons_add] at hrel
  obtain ⟨e', Γ', he', hΓ', hN₀'⟩ := Multiset.rel_cons_left.1 hrel
  obtain ⟨a', b', rfl, ha', hb'⟩ := EqTr.mk he'
  obtain ⟨f, rfl⟩ := ha'.app_var_inv
  obtain ⟨g, rfl⟩ := hb'.app_var_inv
  set P : Sym2 (Term S' ℕ) := s((Φ.net α).inst (fun i => var (B + i)) f,
    (Φ.net β).inst (fun j => var (B + S.arity α + j)) g) with hP
  have hlin' : Net.Linear (P ::ₘ Γ') := hN₀' ▸ hT₀.linear
  have hPl : Net.Linear ({P} : Net S' ℕ) := fun y => by
    have := hlin' y
    rw [Net.vars_cons, Multiset.count_add] at this
    rw [Net.vars_singleton]
    omega
  have hΓl : Net.Linear Γ' := fun y => by
    have := hlin' y
    rw [Net.vars_cons, Multiset.count_add] at this
    omega
  have hTΓ : Φ.NetTr (Δ + W) Γ' := ⟨hΓ', hΓl⟩
  -- the compatibility, then the reduction beside `Γ'`
  obtain ⟨M₁, R', h₁, hS₁, E₁, hR'⟩ :=
    hΦ α β r hr (fun i => B + i) (fun j => B + S.arity α + j) f g
      (fun i i' e => Fin.ext (by simpa using e)) (fun j j' e => Fin.ext (by simpa using e))
      (fun i j e => by have := i.isLt; omega) hPl
  have hPΓ : ({P} : Net S' ℕ) + Γ' = P ::ₘ Γ' := Multiset.singleton_add _ _
  obtain ⟨M₂, hS₂, E₂, hl₂⟩ := hadd Γ' hS₁ (hPΓ ▸ hlin')
  -- the fresh names are free ports of the active pair, hence of `R'` and of `M₂`
  have hfreeP : ∀ p ∈ Simulation.ports B (S.arity α) (S.arity β),
      (Net.vars ({P} : Net S' ℕ)).count p = 1 := by
    intro p hp
    have c1 : 1 ≤ (eqVars (Simulation.pairVar B α β)).count p :=
      Multiset.one_le_count_iff_mem.2 (Simulation.mem_vars_pairVar hp)
    have c2 := ha'.count_le p
    have c3 := hb'.count_le p
    have c4 : 1 ≤ (Net.vars (Δ + W)).count p := by
      refine Multiset.one_le_count_iff_mem.2 ?_
      rw [Net.vars_add, hW, Simulation.vars_wires]
      exact Multiset.mem_add.2 (Or.inr (Multiset.mem_add.2 (Or.inl (Multiset.mem_coe.2 hp))))
    have c5 := hTΓ.count_le p
    have c6 := hlin' p
    rw [Net.vars_cons, Multiset.count_add, hP, eqVars_mk, Multiset.count_add] at c6
    simp only [eqVars_mk, Multiset.count_add] at c1
    rw [Net.vars_singleton, hP, eqVars_mk, Multiset.count_add]
    omega
  have hfreeMR : ∀ y, R'.vars.count y = 1 ↔ M₂.vars.count y = 1 := fun y =>
    ((E₂.trans E₁).free_iff y).symm
  have hfreeR : ∀ p ∈ Simulation.ports B (S.arity α) (S.arity β), R'.vars.count p = 1 :=
    fun p hp => (E₁.free_iff p).1 ((StepsE.free_iff hI' (hR hS₁) p).2 (hfreeP p hp))
  -- rename the internal wires of `R'` away from `Γ'`, fixing the names of `M₂`
  set C := (M₂.vars + Net.vars Γ').sup + 1 with hC
  have hltM : ∀ x ∈ M₂.vars, x < C := fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sup (Multiset.mem_add.2 (Or.inl hx)))
  have hltΓ : ∀ x ∈ Net.vars Γ', x < C := fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sup (Multiset.mem_add.2 (Or.inr hx)))
  let ι : ℕ → ℕ := fun x => if x ∈ M₂.vars then x else x + C
  have hfix : ∀ x ∈ M₂.vars, ι x = x := fun x hx => by simp [ι, hx]
  have hshift : ∀ x, x ∉ M₂.vars → ι x = x + C := fun x hx => by simp [ι, hx]
  have hι : Function.Injective ι := by
    intro x y hxy
    by_cases hx : x ∈ M₂.vars <;> by_cases hy : y ∈ M₂.vars
    · rwa [hfix x hx, hfix y hy] at hxy
    · rw [hfix x hx, hshift y hy] at hxy
      have := hltM x hx
      omega
    · rw [hshift x hx, hfix y hy] at hxy
      have := hltM y hy
      omega
    · rw [hshift x hx, hshift y hy] at hxy
      omega
  have hout : ∀ x, x ∉ M₂.vars → ι x ∉ Net.vars Γ' := fun x hx hm => by
    have := hltΓ _ hm
    rw [hshift x hx] at this
    omega
  have hmemM : ∀ y, R'.vars.count y = 1 → y ∈ M₂.vars := fun y hy =>
    Multiset.one_le_count_iff_mem.1 (by rw [(hfreeMR y).1 hy])
  have hTl : ((R'.bind fun y => var (ι y)) + Γ').Linear :=
    Net.Linear.bind_var_add_right ι hι hl₂ hfix hout hR'.linear hfreeMR
  have ER : Equiv R' (R'.bind fun y => var (ι y)) :=
    Net.equiv_bind_var hR'.linear ι hι.injOn fun x hx => hfix x (hmemM x hx)
  have hTR := hR'.bind_var ι hι
  rw [Rule.inst_bind_var] at hTR
  have hιp : ∀ p ∈ Simulation.ports B (S.arity α) (S.arity β), ι p = p := fun p hp =>
    hfix p (hmemM p (hfreeR p hp))
  have ex : (fun i : Fin (S.arity α) => (var (B + i) : Term S ℕ).bind fun y => var (ι y)) =
      fun i : Fin (S.arity α) => (var (B + i) : Term S ℕ) := funext fun i => by
    rw [bind_var, hιp _ (Simulation.left_mem_ports B i)]
  have ey : (fun j : Fin (S.arity β) =>
      (var (B + S.arity α + j) : Term S ℕ).bind fun y => var (ι y)) =
      fun j : Fin (S.arity β) => (var (B + S.arity α + j) : Term S ℕ) := funext fun j => by
    rw [bind_var, hιp _ (Simulation.right_mem_ports B j)]
  rw [ex, ey] at hTR
  -- the translation of the expanded right-hand side
  set h₂ : Fin r.internal → ℕ := fun w => ι (h₁ w)
  have hT₂ : Φ.NetTr ((r.inst (fun i => var (B + i)) (fun j => var (B + S.arity α + j)) h₂ + Δ)
      + W) ((R'.bind fun y => var (ι y)) + Γ') :=
    ⟨by rw [add_assoc]; exact Multiset.Rel.add hTR.rel hΓ', hTl⟩
  have E₃ := Simulation.equiv_contract_inst r hrl h₂ has hbs hΔ hT₂.linear_source
  -- the new wires: from `h₂` to `hh`, through names `h₃` above both
  have hMl : (r.inst as bs hh + Δ).Linear :=
    (Step.mk α β r hr as bs Δ hh hhinj hhfresh).linear hI hN
  set D := ((r.inst as bs h₂ + Δ).vars + (r.inst as bs hh + Δ).vars).sup + 1 with hD
  have h₃inj : Function.Injective fun w : Fin r.internal => D + w :=
    fun w w' e => Fin.ext (by simpa using e)
  have E₄ := Rule.equiv_inst r hrl as bs h₂ (fun w => D + w) Δ (E₃.linear hT₂.linear_source)
    h₃inj fun w hw => by
      have := Multiset.le_sup (Multiset.mem_add.2 (Or.inl hw) :
        D + (w : ℕ) ∈ (r.inst as bs h₂ + Δ).vars + (r.inst as bs hh + Δ).vars)
      omega
  have E₅ := Rule.equiv_inst r hrl as bs hh (fun w => D + w) Δ hMl h₃inj fun w hw => by
      have := Multiset.le_sup (Multiset.mem_add.2 (Or.inr hw) :
        D + (w : ℕ) ∈ (r.inst as bs h₂ + Δ).vars + (r.inst as bs hh + Δ).vars)
      omega
  obtain ⟨M'', hM'', E₆⟩ := hT₂.of_equiv (E₃.trans (E₄.trans E₅.symm))
  -- the reduction of `N'`
  have hS₃ : R N₀' (M₂ + Γ') := by
    rw [hN₀', ← hPΓ]
    exact hS₂
  obtain ⟨X, hX, EX⟩ := heq E₀' hS₃
  have E₇ : Equiv (M₂ + Γ') ((R'.bind fun y => var (ι y)) + Γ') :=
    Equiv.add_right Γ' ((E₂.trans E₁).trans ER) hl₂ hTl
  exact ⟨X, M'', hX, EX.trans (E₇.trans E₆), hM''⟩

/-- **One interaction is simulated, for any reduction of the target** (Lafont 1997,
Proposition 4, page 81, the case of one step): `Translation.CompatibleByDistinct.step` for a
translation compatible for all names. -/
theorem Translation.CompatibleBy.step
    -- the interaction systems of the source and of the target, and a reduction of the target
    {I : System S}
    {I' : System S'}
    {R : Net S' ℕ → Net S' ℕ → Prop}
    -- the rules of both systems are linear
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- `R` can be done beside a context `Γ`
    (hadd : ∀ {N M : Net S' ℕ} (Γ : Net S' ℕ), R N M → (N + Γ).Linear →
      ∃ M', R (N + Γ) (M' + Γ) ∧ Equiv M' M ∧ (M' + Γ).Linear)
    -- `R` can start from the same graph
    (heq : ∀ {N K M : Net S' ℕ}, Equiv N K → R K M → ∃ M', R N M' ∧ Equiv M' M)
    -- `R` is a reduction up to wires
    (hR : ∀ {N M : Net S' ℕ}, R N M → StepsE I' N M)
    -- the translation, compatible by `R` for all names
    {Φ : Translation S S'}
    (hΦ : Φ.CompatibleBy I R)
    -- one interaction from `N` to `M`, and a translation `N'` of `N`
    {N M : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Step I N M)
    (hT : Φ.NetTr N N') :
    -- there are nets `M₁` and `M'` such that
    ∃ M₁ M',
      -- `N'` reduces by `R` to `M₁`,
      R N' M₁ ∧
      -- `M₁` is the same graph as `M'`,
      Equiv M₁ M' ∧
      -- and `M'` is a translation of `M`
      Φ.NetTr M M' :=
  hΦ.distinct.step hI hI' hadd heq hR h hT

/-- **One interaction is simulated** (Lafont 1997, Proposition 4, page 81, the case of one step).
If `Φ` is a translation of interaction systems from `I` to `I'`, `N` reduces to `M` by one
interaction, and `N'` is a translation of `N`, then `N'` reduces up to wires to a net that is the
same graph as a translation of `M`. The rules of `I` and of `I'` are linear, as Lafont's rules are
(page 73). -/
theorem Translation.Compatible.step
    -- the interaction systems of the source and of the target, whose rules are linear
    {I : System S}
    {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- a translation of interaction systems
    {Φ : Translation S S'}
    (hΦ : Φ.Compatible I I')
    -- one interaction from `N` to `M`, and a translation `N'` of `N`
    {N M : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Step I N M)
    (hT : Φ.NetTr N N') :
    -- there are nets `M₁` and `M'` such that
    ∃ M₁ M',
      -- `N'` reduces up to wires to `M₁`,
      StepsE I' N' M₁ ∧
      -- `M₁` is the same graph as `M'`,
      Equiv M₁ M' ∧
      -- and `M'` is a translation of `M`
      Φ.NetTr M M' :=
  Translation.CompatibleBy.step hI hI' (fun Γ h hl => StepsE.add_right hI' Γ h hl)
    (fun hE h => StepsE.of_equiv hE h) id hΦ h hT

/-- **Any number of interactions are simulated** (Lafont 1997, Proposition 4, page 81: "If N
reduces in n steps to M, then Φ(N) reduces in n′ steps to Φ(M)"). If `Φ` is a translation of
interaction systems from `I` to `I'`, `N` reduces to `M`, and `N'` is a translation of `N`, then
`N'` reduces up to wires to a net that is the same graph as a translation of `M`. -/
theorem Translation.Compatible.steps
    -- the interaction systems of the source and of the target, whose rules are linear
    {I : System S}
    {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- a translation of interaction systems
    {Φ : Translation S S'}
    (hΦ : Φ.Compatible I I')
    -- a reduction from `N` to `M`, and a translation `N'` of `N`
    {N M : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Steps I N M)
    (hT : Φ.NetTr N N') :
    -- there are nets `M₁` and `M'` such that
    ∃ M₁ M',
      -- `N'` reduces up to wires to `M₁`,
      StepsE I' N' M₁ ∧
      -- `M₁` is the same graph as `M'`,
      Equiv M₁ M' ∧
      -- and `M'` is a translation of `M`
      Φ.NetTr M M' := by
  induction h with
  | refl => exact ⟨N', N', Relation.ReflTransGen.refl, Equiv.refl _, hT⟩
  | tail _ hs ih =>
    obtain ⟨M₁, M', h1, e1, t1⟩ := ih
    obtain ⟨M₂, M'', h2, e2, t2⟩ := hΦ.step hI hI' hs t1
    obtain ⟨X, hX, eX⟩ := StepsE.of_equiv e1 h2
    exact ⟨X, M'', h1.trans hX, eX.trans e2, t2⟩

end INet
