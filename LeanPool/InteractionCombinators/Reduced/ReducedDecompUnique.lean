/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduced.ReducedDecomp
public import LeanPool.InteractionCombinators.Universality.RecursionFree.DecompositionLemmas

/-!
# Trees on a wiring are unique up to renaming of the wiring (Proposition 2, page 79)

Lafont 1997, Proposition 2, page 79: "Any reduced net with `n` free ports can be uniquely
decomposed as follows", the picture showing trees `τ₁, …, τₙ` whose roots are the free ports and
whose leaves are joined by a wiring `ω`. The existence is `Net.IsReduced.exists_treesOnWiring`
(`InteractionCombinators/Reduced/ReducedDecomp.lean`). This file proves the uniqueness.

## The normal form

The form `Net.IsTreesOnWiring` (every equation is `x = t` with `x` a free port) is not unique up
to renaming: `0 = 7, 2 = con(7, 3)` and `2 = con(0, 3)` are both in it, one wire substitution
apart (`Checks/Reduced/ReducedDecompReview.lean`, `pendant_merged`). The extra freedom is an
equation `x = y` with `y` internal: in the picture, a tree with no cell joined by `ω` to a leaf of
another tree, and the text may as well plug `x` into that leaf. `Net.IsTreesOnWiringN` forbids it:
an equation between two names joins two free ports. Then every equation is either `x = t` with `t` a
tree with a cell, or `x = y` with both free (a wire of `ω` between two trees with no cell); every
other free port is a leaf of a tree, and every internal name joins two leaves.

## The proof

There are no graphs in it. It uses the invariant `Equiv.sol_iff`: equivalent nets have the same
solutions on their free ports. For a net `N` in normal form, `Net.rootTree N x` is the tree hung
from the free port `x` (`var x` if there is none; for a wire `x = y` between free ports, the tree
is hung from the larger name). It is a solution of `N`, and every solution `s` of `N` factors
through it: `s z = (rootTree N z).bind s`. Given `Equiv N M`, the solution `rootTree N` of `N`
extends to a solution `s₁` of `M`, and `rootTree M` to a solution `s₂` of `N`. On the free ports,
`rootTree N p = ((rootTree N p).bind s₂).bind s₁`, so `s₂` sends every leaf of the trees of `N` to
a name, and `s₁` sends it back. This name is the renaming `ρ`.

Contents, in the order of the file:

1. Definitions: `Term.nameOr`, the name of a tree that is a name; `Net.IsTreesOnWiringN`, the
   normal form; `Net.RootTree`, a tree hung from a free port; `Net.rootTree`, the tree hung from
   a name.
2. Auxiliary lemmas on terms: `Term.var_of_bind_eq_self`, `Term.exists_var_of_bind_eq_var`,
   `Term.nameOr_var`.
3. Auxiliary lemmas on counts and root trees: `Net.count_eqVars_le`, `Net.eq_of_count_one`,
   `Net.RootTree.unique`, `Net.rootTree_eq`, `Net.IsTreesOnWiringN.exists_rootTree`,
   `Net.IsTreesOnWiringN.solves_rootTree`, `Net.solves_rootTree_factor`,
   `Net.rootTree_var_transfer`, `Net.IsTreesOnWiringN.nodup`.
4. Auxiliary lemmas for the existence: `Net.IsTreesOnWiring.wire`,
   `Net.exists_treesOnWiringN_card`, the induction on the number of equations.
5. Main results: `Net.IsReduced.exists_treesOnWiringN`, **Proposition 2, existence**, in normal
   form; `Net.IsTreesOnWiringN.unique`, **Proposition 2, uniqueness**: two equivalent nets in
   normal form differ by a renaming of the internal names.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- The name of a tree that is a name, or `d`. -/
def Term.nameOr
    -- the default name
    {ν : Type}
    (d : ν) :
    Term S ν → ν
  | var w => w
  | app _ _ => d

namespace Net

/-- **Trees on a wiring, normal form** (Lafont 1997, Proposition 2, page 79): the form
`Net.IsTreesOnWiring`, and an equation between two names joins two free ports. So no tree with no
cell hangs from a free port into an internal name; such a free port is written as the leaf it is
plugged into. -/
def IsTreesOnWiringN
    -- the net
    (N : Net S ℕ) :
    Prop :=
  -- every equation is `x = t` with `x` a free port,
  N.IsTreesOnWiring ∧
  -- and in an equation `x = y` between two names, `y` is a free port too
  ∀ x y, s(var x, var y) ∈ N → N.vars.count y = 1

/-- `t` is the tree hung from the free port `x` of `N` (Lafont 1997, page 79): the equation
`x = t` is in `N`, and if `t` is a name `y`, then `y < x`, so that a wire between two free ports
is hung from one of its ends only. -/
def RootTree
    -- the net, the port and the tree
    (N : Net S ℕ)
    (x : ℕ)
    (t : Term S ℕ) :
    Prop :=
  -- the equation `x = t` is in `N`,
  s(var x, t) ∈ N ∧
  -- `x` is a free port,
  N.vars.count x = 1 ∧
  -- and if `t` is a name, it is smaller than `x`
  ∀ y, t = var y → y < x

open Classical in
/-- The tree hung from the name `x` of `N`, or `var x` if there is none. -/
noncomputable def rootTree
    -- the net and the name
    (N : Net S ℕ)
    (x : ℕ) :
    Term S ℕ :=
  if h : ∃ t, N.RootTree x t then h.choose else var x

end Net

-- ============================================================================================
-- 2. Auxiliary lemmas on terms
-- ============================================================================================

/-- A tree that plugging does not change: every leaf is plugged into itself. -/
theorem Term.var_of_bind_eq_self
    -- the plugging and the tree
    {ν : Type}
    {f : ν → Term S ν}
    {t : Term S ν}
    -- plugging `f` into `t` gives `t` back
    (h : t.bind f = t) :
    -- every leaf `v` of `t` is plugged into itself
    ∀ v ∈ t.vars, f v = var v := by
  induction t with
  | var x =>
    intro v hv
    rw [vars_var, Multiset.mem_singleton] at hv
    subst hv
    exact h
  | app α ts ih =>
    intro v hv
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    rw [bind_app] at h
    have h2 := eq_of_heq (Term.app.inj h).2
    exact ih i (congrFun h2 i) v hi

/-- A plugged tree that is a name was a name. -/
theorem Term.exists_var_of_bind_eq_var
    -- the plugging, the tree and the name
    {ν μ : Type}
    {f : ν → Term S μ}
    {t : Term S ν}
    {v : μ}
    -- plugging `f` into `t` gives the name `v`
    (h : t.bind f = var v) :
    -- there is a name `w` such that
    ∃ w,
      -- `t` is the name `w`,
      t = var w ∧
      -- and `f` plugs `v` into `w`
      f w = var v := by
  cases t with
  | var w => exact ⟨w, rfl, h⟩
  | app α ts => simp at h

/-- The name of the tree `var w` is `w`. -/
@[simp] theorem Term.nameOr_var
    -- the default name and the name
    {ν : Type}
    (d w : ν) :
    (var w : Term S ν).nameOr d = w := rfl

namespace Net

-- ============================================================================================
-- 3. Auxiliary lemmas on counts and root trees
-- ============================================================================================

/-- The names of an equation of a net are names of the net. -/
theorem count_eqVars_le
    -- an equation of the net
    {N : Net S ℕ}
    {e : Sym2 (Term S ℕ)}
    (he : e ∈ N)
    -- a name
    (x : ℕ) :
    -- occurs in `e` at most as often as in `N`
    (eqVars e).count x ≤ N.vars.count x := by
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem he
  simp only [Net.vars_cons, Multiset.count_add]
  omega

/-- A free port occurs in one equation only. -/
theorem eq_of_count_one
    -- a free port of the net
    {N : Net S ℕ}
    {x : ℕ}
    (h : N.vars.count x = 1)
    -- two equations of the net, both containing `x`
    {e e' : Sym2 (Term S ℕ)}
    (he : e ∈ N)
    (he' : e' ∈ N)
    (hx : x ∈ eqVars e)
    (hx' : x ∈ eqVars e') :
    -- are the same equation
    e = e' := by
  by_contra hne
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem he
  have hR : e' ∈ R := (Multiset.mem_cons.1 he').resolve_left (Ne.symm hne)
  obtain ⟨Q, rfl⟩ := Multiset.exists_cons_of_mem hR
  have h1 := Multiset.one_le_count_iff_mem.2 hx
  have h2 := Multiset.one_le_count_iff_mem.2 hx'
  simp only [Net.vars_cons, Multiset.count_add] at h
  omega

/-- The tree hung from a free port is unique. -/
theorem RootTree.unique
    -- two trees hung from the same port `x` of `N`
    {N : Net S ℕ}
    {x : ℕ}
    {t t' : Term S ℕ}
    (h : N.RootTree x t)
    (h' : N.RootTree x t') :
    -- are equal
    t = t' := by
  have := eq_of_count_one h.2.1 h.1 h'.1 (by simp) (by simp)
  rcases Sym2.eq_iff.1 this with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · exact h2.trans h1

/-- The tree hung from `x` is not `x`. -/
theorem RootTree.ne_var
    -- a tree hung from the port `x` of `N`
    {N : Net S ℕ}
    {x : ℕ}
    {t : Term S ℕ}
    (h : N.RootTree x t) :
    t ≠ var x :=
  fun e => lt_irrefl _ (h.2.2 x e)

/-- An equation is hung from one name only. -/
theorem RootTree.root_eq
    -- a tree `t` hung from `x` in `N`, and a tree `u` hung from `y` in `M`
    {N M : Net S ℕ}
    {x y : ℕ}
    {t u : Term S ℕ}
    (hx : N.RootTree x t)
    (hy : M.RootTree y u)
    -- the two equations are the same
    (he : s(var x, t) = s(var y, u)) :
    -- then the two roots are the same
    x = y := by
  rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, h2⟩
  · injection h1
  · have a := hx.2.2 y h2
    have b := hy.2.2 x h1.symm
    omega

/-- `rootTree N x` is the tree hung from `x`, when there is one. -/
theorem rootTree_eq
    -- a tree hung from the port `x` of `N`
    {N : Net S ℕ}
    {x : ℕ}
    {t : Term S ℕ}
    (h : N.RootTree x t) :
    rootTree N x = t := by
  unfold rootTree
  split_ifs with h'
  · exact h'.choose_spec.unique h
  · exact absurd ⟨t, h⟩ h'

/-- If `rootTree N x` is not `var x`, it is hung from `x`. -/
theorem rootTree_of_ne
    -- a name `x` whose `rootTree` is not `var x`
    {N : Net S ℕ}
    {x : ℕ}
    (h : rootTree N x ≠ var x) :
    N.RootTree x (rootTree N x) := by
  unfold rootTree at h ⊢
  split_ifs at h ⊢ with h'
  · exact h'.choose_spec
  · exact absurd rfl h

/-- Nothing is hung from a name that is not a free port. -/
theorem rootTree_of_not_free
    -- a name `x` that does not occur exactly once in `N`
    {N : Net S ℕ}
    {x : ℕ}
    (hx : N.vars.count x ≠ 1) :
    rootTree N x = var x := by
  by_contra h
  exact hx (rootTree_of_ne h).2.1

/-- In normal form, every equation is hung from a free port. -/
theorem IsTreesOnWiringN.exists_rootTree
    -- a net in normal form
    {N : Net S ℕ}
    (h : N.IsTreesOnWiringN)
    -- an equation of the net
    {e : Sym2 (Term S ℕ)}
    (he : e ∈ N) :
    -- there are a port `x` and a tree `t` such that
    ∃ x t,
      -- `t` is hung from `x`,
      N.RootTree x t ∧
      -- and the equation is `x = t`
      e = s(var x, t) := by
  obtain ⟨x, t, rfl, hx⟩ := h.1 e he
  by_cases hv : ∃ y, t = var y
  · obtain ⟨y, rfl⟩ := hv
    have hy : N.vars.count y = 1 := h.2 x y he
    have hxy : x ≠ y := by
      rintro rfl
      have := count_eqVars_le he x
      simp only [eqVars_mk, vars_var, Multiset.count_add, Multiset.count_singleton_self] at this
      omega
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨y, var x, ⟨by rw [Sym2.eq_swap]; exact he, hy, fun z hz => ?_⟩, Sym2.eq_swap⟩
      injection hz with hz
      omega
    · refine ⟨x, var y, ⟨he, hx, fun z hz => ?_⟩, rfl⟩
      injection hz with hz
      omega
  · exact ⟨x, t, ⟨he, hx, fun y hy => absurd ⟨y, hy⟩ hv⟩, rfl⟩

/-- In normal form, the leaves of a tree are not roots. -/
theorem RootTree.rootTree_leaf
    -- a tree hung from the port `x` of `N`
    {N : Net S ℕ}
    {x : ℕ}
    {t : Term S ℕ}
    (hr : N.RootTree x t)
    -- a leaf of the tree
    {v : ℕ}
    (hv : v ∈ t.vars) :
    -- nothing is hung from it
    rootTree N v = var v := by
  by_contra hne
  have hv' := rootTree_of_ne hne
  have heq := eq_of_count_one hv'.2.1 hv'.1 hr.1 (by simp) (by simp [hv])
  rcases Sym2.eq_iff.1 heq with ⟨h1, -⟩ | ⟨h1, h2⟩
  · have hvx : v = x := by injection h1
    rw [hvx] at hv
    have h3 := count_eqVars_le hr.1 x
    rw [eqVars_mk, Multiset.count_add, vars_var, Multiset.count_singleton_self, hr.2.1] at h3
    have h4 := Multiset.one_le_count_iff_mem.2 hv
    omega
  · have a := hr.2.2 v h1.symm
    have b := hv'.2.2 x h2
    omega

/-- In normal form, the trees hung from the free ports are a solution of the net. -/
theorem IsTreesOnWiringN.solves_rootTree
    -- a net in normal form
    {N : Net S ℕ}
    (h : N.IsTreesOnWiringN) :
    N.Solves (rootTree N) := by
  intro e he
  obtain ⟨x, t, hr, rfl⟩ := h.exists_rootTree he
  simp only [Sym2.lift_mk, bind_var]
  rw [rootTree_eq hr]
  symm
  calc t.bind (rootTree N) = t.bind var := Term.bind_congr fun v hv => hr.rootTree_leaf hv
    _ = t := Term.bind_var_self t

/-- Every solution of a net factors through the trees hung from its free ports. -/
theorem solves_rootTree_factor
    -- a solution `s` of the net
    {N : Net S ℕ}
    {μ : Type}
    {s : ℕ → Term S μ}
    (hs : N.Solves s)
    -- a name
    (z : ℕ) :
    -- `s z` is `s` plugged into the tree hung from `z`
    s z = (rootTree N z).bind s := by
  by_cases h : rootTree N z = var z
  · rw [h, bind_var]
  · simpa using hs _ (rootTree_of_ne h).1

/-- The step of the uniqueness: a free port that is a leaf on one side is a leaf on the other. -/
theorem rootTree_var_transfer
    -- two nets, `M` in normal form, and a substitution `s₁`
    {N M : Net S ℕ}
    {s₁ : ℕ → Term S ℕ}
    (hm : M.IsTreesOnWiringN)
    -- on the free ports of `N`, the tree of `N` is the tree of `M` plugged with `s₁`
    (A : ∀ p, N.vars.count p = 1 → rootTree N p = (rootTree M p).bind s₁)
    -- on the free ports of `M`, `s₁` is the tree of `N`
    (hp₁ : ∀ p, M.vars.count p = 1 → s₁ p = rootTree N p)
    -- a free port `p` of `N` from which nothing is hung in `N`
    (p : ℕ)
    (hp : N.vars.count p = 1)
    (hNp : rootTree N p = var p) :
    -- nothing is hung from `p` in `M` either
    rootTree M p = var p := by
  by_contra hne
  have hr := rootTree_of_ne hne
  have e1 := A p hp
  rw [hNp] at e1
  obtain ⟨w, hw, hw1⟩ := Term.exists_var_of_bind_eq_var e1.symm
  rw [hw] at hr
  have hwp : w < p := hr.2.2 w rfl
  have hwM : M.vars.count w = 1 := hm.2 p w hr.1
  have hσw : rootTree N w = var p := (hp₁ w hwM).symm.trans hw1
  have hne' : rootTree N w ≠ var w := by
    rw [hσw]
    intro e
    injection e with e
    omega
  have hr' := rootTree_of_ne hne'
  rw [hσw] at hr'
  have := hr'.2.2 p rfl
  omega

/-- In normal form, no equation occurs twice. -/
theorem IsTreesOnWiringN.nodup
    -- a net in normal form
    {N : Net S ℕ}
    (h : N.IsTreesOnWiringN) :
    N.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro e
  by_contra hc
  have he : e ∈ N := Multiset.count_pos.1 (by omega)
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem he
  have hR : e ∈ R := Multiset.count_pos.1 (by rw [Multiset.count_cons_self] at hc; omega)
  obtain ⟨Q, rfl⟩ := Multiset.exists_cons_of_mem hR
  obtain ⟨x, t, hr, rfl⟩ := h.exists_rootTree he
  have := hr.2.1
  simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at this
  omega

-- ============================================================================================
-- 4. Auxiliary lemmas for the existence: the induction on the number of equations
-- ============================================================================================

/-- A wire substitution keeps the form `Net.IsTreesOnWiring` (Lafont 1997, page 79). -/
theorem IsTreesOnWiring.wire
    -- `M` is `N` after a wire substitution
    {N M : Net S ℕ}
    (hW : Wire N M)
    -- `N` is in the form
    (h : N.IsTreesOnWiring) :
    -- then `M` is in the form
    M.IsTreesOnWiring := by
  have hfree := hW.free_iff
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := hW
  have hx2 : 2 ≤ (Net.vars (s(var x, t) ::ₘ s(a, b) ::ₘ Δ)).count x := by
    have := Multiset.one_le_count_iff_mem.2 hx
    simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at this ⊢
    omega
  intro e he
  rcases Multiset.mem_cons.1 he with rfl | he
  · obtain ⟨z, u, hzu, hz⟩ := h _ (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
    have hzx : z ≠ x := by
      rintro rfl
      omega
    refine ⟨z, u.subst x t, ?_, (hfree z).1 hz⟩
    rcases Sym2.eq_iff.1 hzu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Cut.subst_var_ne hzx]
    · rw [Cut.subst_var_ne hzx, Sym2.eq_swap]
  · obtain ⟨z, u, hzu, hz⟩ := h e (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem he))
    exact ⟨z, u, hzu, (hfree z).1 hz⟩

/-- The induction on the number of equations behind `Net.IsReduced.exists_treesOnWiringN`: an
equation `x = y` with `y` internal is contracted by one wire substitution. -/
theorem exists_treesOnWiringN_card :
    -- for every number `n` and every net `N` with `n` equations,
    ∀ (n : ℕ) (N : Net S ℕ), Multiset.card N = n →
      -- if `N` is linear and in the form,
      N.Linear → N.IsTreesOnWiring →
      -- then `N` is the same graph as a net `M` in normal form
      ∃ M, Equiv N M ∧ M.IsTreesOnWiringN := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hN hF
  by_cases hG : ∀ x y, s(var x, var y) ∈ N → N.vars.count y = 1
  · exact ⟨N, Equiv.refl N, hF, hG⟩
  push Not at hG
  obtain ⟨x, y, hm, hy⟩ := hG
  have hxy : y ∉ (var x : Term S ℕ).vars := by
    intro hyx
    rw [vars_var, Multiset.mem_singleton] at hyx
    subst hyx
    obtain ⟨z, u, he, hz⟩ := hF _ hm
    rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨-, h1⟩ <;>
    · injection h1 with h1
      exact hy (h1 ▸ hz)
  have hm' : s(var y, var x) ∈ N := by rw [Sym2.eq_swap]; exact hm
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem hm'
  obtain ⟨M, hW, hc⟩ := exists_wire_of_not_free hN hy hxy
  obtain ⟨M', hE, hM'⟩ := ih _ (hn ▸ hc) M rfl hW.linear_right (hF.wire hW)
  exact ⟨M', hW.equiv.trans hE, hM'⟩

-- ============================================================================================
-- 5. Main results: Proposition 2, existence in normal form and uniqueness
-- ============================================================================================

/-- **Proposition 2, existence, in normal form** (Lafont 1997, page 79): a linear reduced net is
the same graph as a net in the normal form `Net.IsTreesOnWiringN`, trees hung from the free ports
with no tree that is an internal name. -/
theorem IsReduced.exists_treesOnWiringN
    -- a linear reduced net
    {N : Net S ℕ}
    (hN : N.Linear)
    (hR : N.IsReduced) :
    -- there is a net `M` such that
    ∃ M,
      -- `N` is the same graph as `M`,
      Equiv N M ∧
      -- and `M` is in normal form
      M.IsTreesOnWiringN := by
  obtain ⟨M, hE, hM⟩ := hR.exists_treesOnWiring hN
  obtain ⟨M', hE', hM'⟩ := exists_treesOnWiringN_card _ M rfl (hE.linear hN) hM
  exact ⟨M', hE.trans hE', hM'⟩

/-- **Proposition 2, uniqueness** (Lafont 1997, page 79: "Any reduced net with `n` free ports can
be uniquely decomposed as follows"). Two equivalent nets in the normal form
`Net.IsTreesOnWiringN` differ only by a renaming `ρ` of their internal names, the wires of the
wiring: `ρ` fixes the free ports and is injective on the names of `N`. Linearity is not assumed. -/
theorem IsTreesOnWiringN.unique
    -- two nets, both in normal form
    {N M : Net S ℕ}
    (hn : N.IsTreesOnWiringN)
    (hm : M.IsTreesOnWiringN)
    -- that are the same graph
    (h : Equiv N M) :
    -- there is a renaming `ρ` of names such that
    ∃ ρ : ℕ → ℕ,
      -- `ρ` fixes the free ports of `N`,
      (∀ x, N.vars.count x = 1 → ρ x = x) ∧
      -- `ρ` is injective on the names of `N`,
      Set.InjOn ρ {x | x ∈ N.vars} ∧
      -- and renaming the names of `N` by `ρ` gives exactly `M`
      M = N.bind (fun x => var (ρ x)) := by
  classical
  have hfree := h.free_iff
  obtain ⟨s₁, hs₁, hp₁⟩ :=
    (h.sol_iff (rootTree N)).1 ⟨rootTree N, hn.solves_rootTree, fun _ _ => rfl⟩
  obtain ⟨s₂, hs₂, hp₂⟩ :=
    (h.sol_iff (rootTree M)).2 ⟨rootTree M, hm.solves_rootTree, fun _ _ => rfl⟩
  have A₁ : ∀ p, N.vars.count p = 1 → rootTree N p = (rootTree M p).bind s₁ := fun p hp =>
    (hp₁ p ((hfree p).1 hp)).symm.trans (solves_rootTree_factor hs₁ p)
  have A₂ : ∀ p, M.vars.count p = 1 → rootTree M p = (rootTree N p).bind s₂ := fun p hp =>
    (hp₂ p ((hfree p).2 hp)).symm.trans (solves_rootTree_factor hs₂ p)
  have TN := rootTree_var_transfer hm A₁ hp₁
  have TM := rootTree_var_transfer hn A₂ hp₂
  -- `s₂` sends the leaves of the trees of `N` to names, and `s₁` sends them back
  have K : ∀ p, N.vars.count p = 1 → ∀ v ∈ (rootTree N p).vars, (s₂ v).bind s₁ = var v := by
    intro p hp v hv
    have e := A₁ p hp
    rw [A₂ p ((hfree p).1 hp), Term.bind_bind] at e
    exact Term.var_of_bind_eq_self e.symm v hv
  -- an internal name of `N` is sent to an internal name of `M`
  have S₂ : ∀ v ∈ N.vars, N.vars.count v ≠ 1 →
      ∃ w, s₂ v = var w ∧ s₁ w = var v ∧ M.vars.count w ≠ 1 := by
    intro v hvN hv
    obtain ⟨e, he, hve⟩ := Multiset.mem_bind.1 hvN
    obtain ⟨x, t, hr, rfl⟩ := hn.exists_rootTree he
    have hvt : v ∈ t.vars := by
      rw [eqVars_mk, Multiset.mem_add, vars_var, Multiset.mem_singleton] at hve
      rcases hve with rfl | hvt
      · exact absurd hr.2.1 hv
      · exact hvt
    have hk := K x hr.2.1 v (by rw [rootTree_eq hr]; exact hvt)
    obtain ⟨w, hw, hw1⟩ := Term.exists_var_of_bind_eq_var hk
    refine ⟨w, hw, hw1, fun hwM => ?_⟩
    have hσw : rootTree N w = var v := (hp₁ w hwM).symm.trans hw1
    have hvw : v ≠ w := fun e => hv (e ▸ (hfree w).2 hwM)
    have hne : rootTree N w ≠ var w := by
      rw [hσw]
      intro e
      injection e with e
      exact hvw e
    have hr' := rootTree_of_ne hne
    rw [hσw] at hr'
    exact hv (hn.2 w v hr'.1)
  -- a free port that is a leaf of `N` is fixed by `s₂`
  have S₁ : ∀ v, N.vars.count v = 1 → rootTree N v = var v → s₂ v = var v := fun v hv hσ =>
    (hp₂ v hv).trans (TN v hv hσ)
  let ρ : ℕ → ℕ := fun v => if N.vars.count v = 1 then v else (s₂ v).nameOr v
  have hρf : ∀ v, N.vars.count v = 1 → ρ v = v := fun v hv => by simp [ρ, hv]
  have hρi : ∀ v ∈ N.vars, N.vars.count v ≠ 1 →
      ∃ w, ρ v = w ∧ s₂ v = var w ∧ s₁ w = var v ∧ M.vars.count w ≠ 1 := by
    intro v hvN hv
    obtain ⟨w, hw, hw1, hw2⟩ := S₂ v hvN hv
    exact ⟨w, by simp [ρ, hv, hw], hw, hw1, hw2⟩
  -- the tree hung from a root of `N`, renamed, is the tree hung from it in `M`
  have T : ∀ x t, N.RootTree x t →
      t.bind (fun v => var (ρ v)) = rootTree M x ∧ M.RootTree x (rootTree M x) := by
    intro x t hr
    have hx := hr.2.1
    refine ⟨?_, rootTree_of_ne fun e => ?_⟩
    · rw [A₂ x ((hfree x).1 hx), rootTree_eq hr]
      refine Term.bind_congr fun v hv => ?_
      have hvN : v ∈ N.vars := Multiset.one_le_count_iff_mem.1
        ((Multiset.one_le_count_iff_mem.2 (by simp [hv] : v ∈ eqVars s(var x, t))).trans
          (count_eqVars_le hr.1 v))
      by_cases hvf : N.vars.count v = 1
      · rw [hρf v hvf, S₁ v hvf (hr.rootTree_leaf hv)]
      · obtain ⟨w, hρ, hw, -⟩ := hρi v hvN hvf
        rw [hρ, hw]
    · have := TM x ((hfree x).1 hx) e
      rw [rootTree_eq hr] at this
      exact hr.ne_var this
  refine ⟨ρ, hρf, ?_, ?_⟩
  · intro v₁ hv₁ v₂ hv₂ he
    simp only [Set.mem_ofPred_eq] at hv₁ hv₂
    by_cases h₁ : N.vars.count v₁ = 1 <;> by_cases h₂ : N.vars.count v₂ = 1
    · rwa [hρf v₁ h₁, hρf v₂ h₂] at he
    · obtain ⟨w, hρ, -, -, hw⟩ := hρi v₂ hv₂ h₂
      rw [hρf v₁ h₁, hρ] at he
      exact absurd ((hfree v₁).1 h₁) (he ▸ hw)
    · obtain ⟨w, hρ, -, -, hw⟩ := hρi v₁ hv₁ h₁
      rw [hρf v₂ h₂, hρ] at he
      exact absurd ((hfree v₂).1 h₂) (he ▸ hw)
    · obtain ⟨w₁, hρ₁, -, hw₁, -⟩ := hρi v₁ hv₁ h₁
      obtain ⟨w₂, hρ₂, -, hw₂, -⟩ := hρi v₂ hv₂ h₂
      rw [hρ₁, hρ₂] at he
      subst he
      rw [hw₁] at hw₂
      injection hw₂
  · -- the image of an equation of `N`
    have hg : ∀ x t, N.RootTree x t →
        Sym2.map (Term.bind fun v => var (ρ v)) s(var x, t) = s(var x, rootTree M x) := by
      intro x t hr
      rw [Sym2.map_mk, bind_var, hρf x hr.2.1, (T x t hr).1]
    refine Multiset.Nodup.ext hm.nodup (Multiset.Nodup.map_on ?_ hn.nodup) |>.2 ?_
    · intro e₁ he₁ e₂ he₂ he
      obtain ⟨x₁, t₁, hr₁, rfl⟩ := hn.exists_rootTree he₁
      obtain ⟨x₂, t₂, hr₂, rfl⟩ := hn.exists_rootTree he₂
      rw [hg x₁ t₁ hr₁, hg x₂ t₂ hr₂] at he
      have hx : x₁ = x₂ := RootTree.root_eq (T x₁ t₁ hr₁).2 (T x₂ t₂ hr₂).2 he
      subst hx
      rw [hr₁.unique hr₂]
    · intro e
      constructor
      · intro he
        obtain ⟨x, u, hr, rfl⟩ := hm.exists_rootTree he
        have hx := hr.2.1
        have hσ : rootTree N x ≠ var x := fun e' =>
          hr.ne_var ((rootTree_eq hr).symm.trans (TN x ((hfree x).2 hx) e'))
        have hrN := rootTree_of_ne hσ
        refine Multiset.mem_map.2 ⟨_, hrN.1, ?_⟩
        rw [hg x _ hrN, rootTree_eq hr]
      · intro he
        obtain ⟨e', he', rfl⟩ := Multiset.mem_map.1 he
        obtain ⟨x, t, hr, rfl⟩ := hn.exists_rootTree he'
        rw [show Sym2.map (Term.bind fun v => var (ρ v)) s(var x, t) = _ from hg x t hr]
        exact (T x t hr).2.1

end Net

end INet
