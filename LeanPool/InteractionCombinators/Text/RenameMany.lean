/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.Instance
public import LeanPool.InteractionCombinators.Text.NetLemmas

/-!
# Renaming several internal wires at once

The names of the internal wires of a net are an artefact of the text (Lafont 1997, Section 1.1,
pages 70 to 72: a net is a graph). `Net.equiv_rename` renames one internal wire to an unused name.
Here the internal wires are renamed all at once, by any function that keeps the names of the net
distinct and keeps the free ports (`Net.equiv_bind_var`). The targets need not be unused: the
function may permute the internal wires.

The proof renames the internal wires one at a time to a block of unused names
(`Net.equiv_bind_var_fresh`), and from the block to their targets, which are unused by then.

Contents, in the order of the file:

1. Auxiliary lemmas: `Term.bind_congr` and `Net.bind_congr` (plugging depends only on the names
   that occur), `Term.bind_var_self` and `Net.bind_var_self` (plugging every name into itself
   changes nothing), `Net.rename_eq_bind` (renaming one name is a `bind`),
   `Net.equiv_bind_var_fresh` (renaming the internal wires to unused names).
2. Main result: `Net.equiv_bind_var`, renaming the internal wires by any function that keeps the
   names distinct and the free ports in place.
3. Examples: the hypotheses of `Net.equiv_bind_var` hold for a renaming that moves a wire, and for
   one that exchanges two wires.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas
-- ============================================================================================

/-- Plugging trees into the leaves depends only on the trees plugged into the names that occur. -/
theorem Term.bind_congr
    -- the two families of trees plugged into the names, and the tree they are plugged into
    {ν μ : Type}
    {f g : ν → Term S μ}
    {t : Term S ν}
    -- the two families agree on the names of `t`
    (h : ∀ x ∈ t.vars, f x = g x) :
    -- so plugging them into `t` gives the same tree
    t.bind f = t.bind g := by
  induction t with
  | var x => exact h x (by simp)
  | app α ts ih =>
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and] at h
    change app α _ = app α _
    congr 1
    funext i
    exact ih i fun x hx => h x ⟨i, hx⟩

/-- Plugging a name into itself changes nothing. -/
theorem Term.bind_var_self
    -- a tree
    {ν : Type}
    (t : Term S ν) :
    t.bind var = t := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    change app α _ = app α ts
    congr 1
    funext i
    exact ih i

namespace Net

/-- Plugging trees into the names of a net depends only on the trees plugged into the names that
occur. -/
theorem bind_congr
    -- the two families of trees plugged into the names, and the net they are plugged into
    {ν μ : Type}
    {f g : ν → Term S μ}
    {N : Net S ν}
    -- the two families agree on the names of `N`
    (h : ∀ x ∈ N.vars, f x = g x) :
    -- so plugging them into `N` gives the same net
    N.bind f = N.bind g := by
  refine Multiset.map_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : ∀ x ∈ a.vars + b.vars, f x = g x := fun x hx =>
      h x (Multiset.mem_bind.2 ⟨s(a, b), he, by simpa using hx⟩)
    have ha : a.bind f = a.bind g :=
      Term.bind_congr fun x hx => hab x (Multiset.mem_add.2 (Or.inl hx))
    have hb : b.bind f = b.bind g :=
      Term.bind_congr fun x hx => hab x (Multiset.mem_add.2 (Or.inr hx))
    change s(a.bind f, b.bind f) = s(a.bind g, b.bind g)
    rw [ha, hb]

/-- Plugging every name into itself changes nothing. -/
theorem bind_var_self
    -- a net
    {ν : Type}
    (N : Net S ν) :
    N.bind var = N := by
  unfold Net.bind
  conv_rhs => rw [← Multiset.map_id N]
  refine Multiset.map_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => simp [Term.bind_var_self]

/-- Renaming one name (`Net.rename`, by `Term.subst`) is a renaming of all names by a function
that moves that name only. -/
theorem rename_eq_bind
    -- the net, the name `x` that is renamed and its new name `y`
    (N : Net S ℕ)
    (x y : ℕ) :
    -- renaming `x` to `y` is plugging into every name `z` the name `z`, or `y` when `z = x`
    N.rename x y = N.bind fun z => var (if z = x then y else z) := by
  have h : (fun r : Term S ℕ => r.subst x (var y)) =
      Term.bind fun z => var (if z = x then y else z) := by
    funext r
    change r.bind _ = r.bind _
    congr 1
    funext z
    split_ifs <;> rfl
  unfold Net.rename Net.bind
  rw [h]

/-- Renaming the internal wires of a linear net to unused names, one wire at a time. The names of
the net stay distinct, the free ports are kept, and the new name of every internal wire is unused
in the net. -/
theorem equiv_bind_var_fresh
    -- the net, which is linear
    {N : Net S ℕ}
    (hlin : N.Linear)
    -- the renaming: injective on the names of the net, an internal wire goes to an unused name,
    -- a free port is kept
    (g : ℕ → ℕ)
    (hinj : Set.InjOn g {x | x ∈ N.vars})
    (hfresh : ∀ x, N.vars.count x = 2 → g x ∉ N.vars)
    (hfree : ∀ x, N.vars.count x = 1 → g x = x) :
    -- the renamed net is the same graph
    Equiv N (N.bind fun x => var (g x)) := by
  -- after the wires of `s` have been renamed
  have main : ∀ s : Finset ℕ, (∀ x ∈ s, N.vars.count x = 2) →
      Equiv N (N.bind fun x => var (if x ∈ s then g x else x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, ite_false]
      exact Equiv.of_eq (Net.bind_var_self N).symm
    | insert a s ha ih =>
      intro hs
      have hs' : ∀ x ∈ s, N.vars.count x = 2 := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have E := ih hs'
      have ha2 : N.vars.count a = 2 := hs a (Finset.mem_insert_self a s)
      have ham : a ∈ N.vars := Multiset.one_le_count_iff_mem.1 (by omega)
      have hgs : Set.InjOn (fun x => if x ∈ s then g x else x) {x | x ∈ N.vars} := by
        intro x hx x' hx' heq
        simp only at heq
        split_ifs at heq with h1 h2 h2
        · exact hinj hx hx' heq
        · exact absurd (heq ▸ hx') (hfresh x (hs' x h1))
        · exact absurd (heq ▸ hx) (hfresh x' (hs' x' h2))
        · exact heq
      have hMv := Net.vars_bind_var (S := S) (fun x => if x ∈ s then g x else x) N
      have hx : (Net.vars (N.bind fun x => (var (if x ∈ s then g x else x) : Term S ℕ))).count a
          = 2 := by
        rw [hMv]
        have := Multiset.count_map_eq_count _ N.vars hgs a ham
        simp only [ite_eq_right ha] at this
        rw [this, ha2]
      have hy : g a ∉ Net.vars (N.bind fun x => (var (if x ∈ s then g x else x) : Term S ℕ)) := by
        rw [hMv]
        intro hm
        obtain ⟨x, hxm, hxe⟩ := Multiset.mem_map.1 hm
        by_cases hxs : x ∈ s
        · rw [ite_eq_left hxs] at hxe
          exact ha (hinj hxm ham hxe ▸ hxs)
        · rw [ite_eq_right hxs] at hxe
          exact hfresh a ha2 (hxe ▸ hxm)
      have R := Net.equiv_rename (E.linear hlin) hx hy
      rw [Net.rename_eq_bind, Net.bind_bind] at R
      refine E.trans (R.trans (Equiv.of_eq (Net.bind_congr fun x hxm => ?_)))
      change var _ = var _
      congr 1
      by_cases hxa : x = a
      · subst hxa
        simp [ha]
      · by_cases hxs : x ∈ s
        · have hne : g x ≠ a := fun h => hfresh x (hs' x hxs) (h ▸ ham)
          simp [hxs, hne]
        · simp [hxs, hxa]
  have E := main (N.vars.toFinset.filter fun x => N.vars.count x = 2) (by simp)
  refine E.trans (Equiv.of_eq (Net.bind_congr fun x hxm => ?_))
  have h1 := Multiset.one_le_count_iff_mem.2 hxm
  have h2 := hlin x
  by_cases hc : N.vars.count x = 2
  · simp [hxm, hc]
  · have hc1 : N.vars.count x = 1 := by omega
    simp [hc, hfree x hc1]

-- ============================================================================================
-- 2. Main result: renaming the internal wires
-- ============================================================================================

/-- **Renaming the internal wires of a net.** In a linear net, renaming the names by a function
that keeps the names of the net distinct and keeps the free ports gives the same graph. The new
names need not be unused: the function may permute the internal wires. (Lafont 1997, Section 1.1,
pages 70 to 72: a net is a graph, and the names of its internal wires do not matter.) -/
theorem equiv_bind_var
    -- the net, which is linear
    {N : Net S ℕ}
    (hlin : N.Linear)
    -- the renaming: injective on the names of the net, and a free port is kept
    (f : ℕ → ℕ)
    (hinj : Set.InjOn f {x | x ∈ N.vars})
    (hfree : ∀ x, N.vars.count x = 1 → f x = x) :
    -- the renamed net is the same graph
    Equiv N (N.bind fun x => Term.var (f x)) := by
  -- a block of names above every name of the net and every target
  let K : ℕ := max N.vars.sup (N.vars.map f).sup + 1
  have hK : ∀ x ∈ N.vars, x < K ∧ f x < K := by
    intro x hx
    have h1 := Multiset.le_sup hx
    have h2 := Multiset.le_sup (Multiset.mem_map_of_mem f hx)
    simp only [K]
    omega
  have hcount : ∀ x ∈ N.vars, N.vars.count x = 1 ∨ N.vars.count x = 2 := by
    intro x hx
    have h1 := Multiset.one_le_count_iff_mem.2 hx
    have h2 := hlin x
    omega
  -- first to the block
  let g : ℕ → ℕ := fun x => if N.vars.count x = 2 then K + x else x
  have hg2 : ∀ x, N.vars.count x = 2 → g x = K + x := fun x hx => ite_eq_left hx
  have hg1 : ∀ x, N.vars.count x = 1 → g x = x := fun x hx => ite_eq_right (by omega)
  have hginj : Set.InjOn g {x | x ∈ N.vars} := by
    intro x hx x' hx' heq
    have hx : x ∈ N.vars := hx
    have hx' : x' ∈ N.vars := hx'
    have b := (hK x hx).1
    have b' := (hK x' hx').1
    rcases hcount x hx with h | h <;> rcases hcount x' hx' with h' | h'
    · rw [hg1 x h, hg1 x' h'] at heq; exact heq
    · rw [hg1 x h, hg2 x' h'] at heq; omega
    · rw [hg2 x h, hg1 x' h'] at heq; omega
    · rw [hg2 x h, hg2 x' h'] at heq; omega
  have E1 : Equiv N (N.bind fun x => var (g x)) :=
    Net.equiv_bind_var_fresh hlin g hginj
      (fun x hx hm => by
        have := (hK _ hm).1
        rw [hg2 x hx] at this
        omega)
      hg1
  have hMv := Net.vars_bind_var (S := S) g N
  have hML := E1.linear hlin
  have hMc : ∀ x ∈ N.vars,
      (Net.vars (N.bind fun x => (var (g x) : Term S ℕ))).count (g x) = N.vars.count x := by
    intro x hx
    rw [hMv]
    exact Multiset.count_map_eq_count _ N.vars hginj x hx
  -- then from the block to the targets
  let h : ℕ → ℕ := fun y => if K ≤ y then f (y - K) else y
  have hhg : ∀ x ∈ N.vars, h (g x) = f x := by
    intro x hx
    rcases hcount x hx with h1 | h2
    · have : ¬ K ≤ x := by have := (hK x hx).1; omega
      rw [hg1 x h1]
      simp only [h, ite_eq_right this]
      exact (hfree x h1).symm
    · rw [hg2 x h2]
      simp [h]
  have E2 : Equiv (N.bind fun x => (var (g x) : Term S ℕ))
      ((N.bind fun x => (var (g x) : Term S ℕ)).bind fun y => var (h y)) := by
    refine Net.equiv_bind_var_fresh hML h ?_ ?_ ?_
    · intro y hy y' hy' heq
      have hy : y ∈ Net.vars (N.bind fun x => (var (g x) : Term S ℕ)) := hy
      have hy' : y' ∈ Net.vars (N.bind fun x => (var (g x) : Term S ℕ)) := hy'
      rw [hMv] at hy hy'
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.1 hy'
      rw [hhg x hx, hhg x' hx'] at heq
      rw [hinj hx hx' heq]
    · intro y hy hm
      have hym : y ∈ Net.vars (N.bind fun x => (var (g x) : Term S ℕ)) :=
        Multiset.one_le_count_iff_mem.1 (by omega)
      rw [hMv] at hym hm
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hym
      rw [hMc x hx] at hy
      rw [hhg x hx] at hm
      obtain ⟨x', hx', hxe⟩ := Multiset.mem_map.1 hm
      have b := (hK x hx).2
      rcases hcount x' hx' with h1 | h2
      · rw [hg1 x' h1] at hxe
        have : x' = x := hinj hx' hx ((hfree x' h1).trans hxe)
        subst this
        omega
      · rw [hg2 x' h2] at hxe
        omega
    · intro y hy
      have hym : y ∈ Net.vars (N.bind fun x => (var (g x) : Term S ℕ)) :=
        Multiset.one_le_count_iff_mem.1 (by omega)
      rw [hMv] at hym
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hym
      rw [hMc x hx] at hy
      rw [hhg x hx, hg1 x hy]
      exact hfree x hy
  rw [Net.bind_bind] at E2
  refine E1.trans (E2.trans (Equiv.of_eq (Net.bind_congr fun x hx => ?_)))
  change var _ = var _
  rw [hhg x hx]

end Net

-- ============================================================================================
-- 3. Examples
-- ============================================================================================

/-- The hypotheses of `Net.equiv_bind_var` hold for a renaming that moves a wire. In the net
`0 = 1`, `1 = 2` the name `1` is an internal wire and `0`, `2` are free ports; the wire is renamed
to `5`. -/
example : Equiv ({s(var 0, var 1), s(var 1, var 2)} : Net S ℕ)
    {s(var 0, var 5), s(var 5, var 2)} := by
  have hlin : Net.Linear ({s(var 0, var 1), s(var 1, var 2)} : Net S ℕ) := by
    intro x
    simp only [Multiset.insert_eq_cons, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var,
      Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  have E := Net.equiv_bind_var hlin (fun x => if x = 1 then 5 else x)
    (by
      intro x hx y hy hxy
      simp only [Multiset.insert_eq_cons, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var,
        Set.mem_ofPred_eq,Multiset.mem_add, Multiset.mem_singleton] at hx hy
      simp only at hxy
      split_ifs at hxy <;> omega)
    (by
      intro x hx
      have : x ≠ 1 := by
        rintro rfl
        simp [Net.vars] at hx
      simp [this])
  simpa [Net.bind] using E

/-- `Net.equiv_bind_var` with targets that are in use: the two internal wires `0` and `1` of the
net `0 = 1`, `1 = 0` are exchanged. -/
example : Equiv ({s(var 0, var 1), s(var 1, var 0)} : Net S ℕ)
    (Net.bind (fun x => var (if x = 0 then 1 else if x = 1 then 0 else x))
      ({s(var 0, var 1), s(var 1, var 0)} : Net S ℕ)) := by
  refine Net.equiv_bind_var ?_ (fun x => if x = 0 then 1 else if x = 1 then 0 else x) ?_ ?_
  · intro x
    simp only [Multiset.insert_eq_cons, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var,
      Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  · intro x _ y _ hxy
    simp only at hxy
    split_ifs at hxy <;> omega
  · intro x hx
    simp only [Multiset.insert_eq_cons, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var,
      Multiset.count_add, Multiset.count_singleton] at hx
    split_ifs at hx <;> omega

end INet
