/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Net
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Order.Lattice.Nat

/-!
# Renaming an internal wire

The name of an internal wire does not matter: a linear net and the same net with one internal wire
renamed to an unused name are the same graph (`Net.equiv_rename`).

The proof introduces the new name next to one end of the wire by a wire substitution read
backwards, then removes the old name by a wire substitution read forwards. When both ends of the
wire are in the same tree, one of the subtrees is first pulled out into its own equation.

Contents, in the order of the file:

1. Definition: `Net.rename`, the net with one name replaced by another everywhere, with
   `Net.rename_cons` and `Net.rename_of_notMem`.
2. Auxiliary lemmas on trees: `Term.subst_subst_back`, `Term.count_rename`,
   `Term.subst_var_of_ne`, `Term.subst_update`, `Term.count_vars_update`. Renaming in a tree, and
   pulling a subtree out of a tree.
3. Auxiliary lemmas: the cases of the renaming. `equiv_rename_two` (the two ends of the wire in
   two equations), `equiv_rename_sides` (on the two sides of one equation), `Net.exists_fresh`,
   `equiv_rename_tree` (both in one tree).
4. Main result: `Net.equiv_rename`, renaming an internal wire gives the same graph.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- Rename the name `x` to `y` everywhere in the net. -/
def Net.rename
    -- the net
    (N : Net S ℕ)
    -- the old name and the new name
    (x y : ℕ) :
    Net S ℕ :=
  N.map (Sym2.map fun r => r.subst x (var y))

/-- Renaming in a net renames in each of its equations. -/
@[simp] theorem Net.rename_cons
    -- the first equation `a = b`
    (a b : Term S ℕ)
    -- the rest of the net
    (N : Net S ℕ)
    -- the old name and the new name
    (x y : ℕ) :
    Net.rename (s(a, b) ::ₘ N) x y =
      s(a.subst x (var y), b.subst x (var y)) ::ₘ N.rename x y := by
  simp [Net.rename]

/-- Renaming a name that does not occur in the net leaves the net unchanged. -/
theorem Net.rename_of_notMem
    -- the net, and the old name, which does not occur in it
    {N : Net S ℕ}
    {x : ℕ}
    -- the new name
    (y : ℕ)
    (h : x ∉ N.vars) :
    N.rename x y = N := by
  unfold Net.rename
  conv_rhs => rw [← Multiset.map_id N]
  refine Multiset.map_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : x ∉ a.vars + b.vars := fun hm =>
      h (Multiset.mem_bind.2 ⟨s(a, b), he, by simpa using hm⟩)
    simp only [Multiset.mem_add, not_or] at hab
    simp [subst_of_notMem hab.1, subst_of_notMem hab.2]

-- ============================================================================================
-- 2. Auxiliary lemmas on trees
-- ============================================================================================

namespace Term

/-- Renaming `x` to the unused name `y` and back is the identity. -/
theorem subst_subst_back
    -- the old name `x` and the new name `y`
    {x y : ℕ} :
    -- for every tree `r` in which `y` does not occur,
    ∀ {r : Term S ℕ},
      y ∉ r.vars →
      -- renaming `x` to `y` and then `y` to `x` gives `r` back
      (r.subst x (var y)).subst y (var x) = r
  | var z, h => by
    have hzy : z ≠ y := by simpa [eq_comm] using h
    by_cases hzx : z = x
    · subst hzx; simp [subst]
    · simp [subst, hzx, hzy]
  | app α ts, h => by
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and, not_exists] at h
    change app α _ = app α ts
    congr 1
    funext i
    exact subst_subst_back (h i)

/-- The names of a tree after renaming `x` to the unused name `y`. -/
theorem count_rename
    -- the tree
    (r : Term S ℕ)
    -- the old name `x` and the new name `y`, which is different and does not occur in `r`
    {x y : ℕ}
    (hxy : x ≠ y)
    (hy : y ∉ r.vars)
    -- the name whose occurrences are counted
    (z : ℕ) :
    -- `y` occurs as often as `x` did, `x` no longer occurs, and the other names are unchanged
    (r.subst x (var y)).vars.count z =
      if z = y then r.vars.count x else if z = x then 0 else r.vars.count z := by
  rw [count_vars_subst, vars_var, Multiset.count_singleton]
  have h0 := Multiset.count_eq_zero_of_notMem hy
  by_cases hzy : z = y
  · subst hzy
    have : ¬ z = x := fun h => hxy h.symm
    simp [this, h0]
  · by_cases hzx : z = x
    · simp [hzx]
    · simp [hzy, hzx]

/-- Substituting for `x` leaves a leaf named by another name `z` unchanged. -/
theorem subst_var_of_ne
    -- the two different names
    {z x : ℕ}
    -- the tree substituted for `x`
    (t : Term S ℕ)
    (h : z ≠ x) :
    (var z : Term S ℕ).subst x t = var z := by simp [subst, h]

/-- Plugging a subtree back into the place it was pulled out of. -/
theorem subst_update
    -- the tree `α ts` and the place `i` of the subtree
    {α : S.Sym}
    (ts : Fin (S.arity α) → Term S ℕ)
    (i : Fin (S.arity α))
    -- the name `w` put in place of the subtree, which does not occur in the tree
    {w : ℕ}
    (hw : w ∉ (app α ts).vars) :
    -- substituting the subtree for `w` gives the tree back
    (app α (Function.update ts i (var w))).subst w (ts i) = app α ts := by
  simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and, not_exists] at hw
  change app α _ = app α ts
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self]
  · rw [Function.update_of_ne hj]
    exact subst_of_notMem (hw j)

/-- The names of a tree with a subtree pulled out and replaced by the name `w`. -/
theorem count_vars_update
    -- the tree `α ts` and the place `i` of the subtree
    {α : S.Sym}
    (ts : Fin (S.arity α) → Term S ℕ)
    (i : Fin (S.arity α))
    -- the name `w` put in place of the subtree, and the name whose occurrences are counted
    (w z : ℕ) :
    -- the tree with `w` in place of the subtree, together with the subtree, has the names of
    -- the tree and one more `w`
    (app α (Function.update ts i (var w))).vars.count z + (ts i).vars.count z =
      (app α ts).vars.count z + if z = w then 1 else 0 := by
  simp only [vars_app, Multiset.count_sum']
  have h1 : (fun j => (Function.update ts i (var w) j).vars.count z) =
      Function.update (fun j => (ts j).vars.count z) i (if z = w then 1 else 0) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_self, Multiset.count_singleton]
    · simp [Function.update_of_ne hj]
  rw [show (∑ j, (Function.update ts i (var w) j).vars.count z) =
      ∑ j, Function.update (fun j => (ts j).vars.count z) i (if z = w then 1 else 0) j from
        Finset.sum_congr rfl fun j _ => congrFun h1 j]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h2 := Finset.sum_erase_add (s := Finset.univ) (f := fun j => (ts j).vars.count z)
    (Finset.mem_univ i)
  have h3 : (Finset.univ \ {i} : Finset (Fin (S.arity α))) = Finset.univ.erase i := by
    ext j; simp
  rw [h3]
  omega

end Term

-- ============================================================================================
-- 3. Auxiliary lemmas: the cases of the renaming
-- ============================================================================================

section Cases

variable {a b c d r : Term S ℕ} {Δ : Net S ℕ} {x y : ℕ}

/-- Renaming a wire whose two ends are in different equations. -/
theorem equiv_rename_two
    -- the net `a = b, c = d, Δ` is linear
    (hlin : Net.Linear (s(a, b) ::ₘ s(c, d) ::ₘ Δ))
    -- the name `x` occurs in `a = b` and in `c = d`
    (hx1 : x ∈ a.vars + b.vars)
    (hx2 : x ∈ c.vars + d.vars)
    -- the new name `y` does not occur in the net
    (hy : y ∉ Net.vars (s(a, b) ::ₘ s(c, d) ::ₘ Δ)) :
    -- renaming `x` to `y` in the two equations gives the same graph
    Equiv (s(a, b) ::ₘ s(c, d) ::ₘ Δ)
      (s(a.subst x (var y), b.subst x (var y)) ::ₘ
        s(c.subst x (var y), d.subst x (var y)) ::ₘ Δ) := by
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at hxl
  have h1 := Multiset.one_le_count_iff_mem.2 hx1
  have h2 := Multiset.one_le_count_iff_mem.2 hx2
  rw [Multiset.count_add] at h1 h2
  simp only [Net.vars_cons, eqVars_mk, Multiset.mem_add, not_or] at hy
  obtain ⟨⟨hya, hyb⟩, ⟨hyc, hyd⟩, hyΔ⟩ := hy
  have hxy : x ≠ y := by
    rintro rfl
    rcases Multiset.mem_add.1 hx1 with h | h
    · exact hya h
    · exact hyb h
  have ya := Multiset.count_eq_zero_of_notMem hya
  have yb := Multiset.count_eq_zero_of_notMem hyb
  have yc := Multiset.count_eq_zero_of_notMem hyc
  have yd := Multiset.count_eq_zero_of_notMem hyd
  have yΔ := Multiset.count_eq_zero_of_notMem hyΔ
  -- the net with the new name `y` on the end of the wire that is in `a = b`
  have L0 : Net.Linear (s(var y, var x) ::ₘ s(a.subst x (var y), b.subst x (var y)) ::ₘ
      (s(c, d) ::ₘ Δ)) := by
    intro z
    have hz := hlin z
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, vars_var, Multiset.count_singleton,
      count_rename a hxy hya, count_rename b hxy hyb] at hz ⊢
    by_cases hzy : z = y
    · subst hzy
      have : ¬ z = x := fun h => hxy h.symm
      simp only [this, ite_true, ite_false]
      omega
    · by_cases hzx : z = x
      · subst hzx
        simp only [hzy, ite_true, ite_false]
        omega
      · simp only [hzy, hzx, ite_false]
        omega
  have hmem : y ∈ (a.subst x (var y)).vars + (b.subst x (var y)).vars := by
    refine Multiset.one_le_count_iff_mem.1 ?_
    rw [Multiset.count_add, count_rename a hxy hya, count_rename b hxy hyb]
    simp only [ite_true]
    omega
  have W1 := Wire.mk y (var x) (a.subst x (var y)) (b.subst x (var y)) (s(c, d) ::ₘ Δ) L0 hmem
  rw [subst_subst_back hya, subst_subst_back hyb] at W1
  have e : (s(var y, var x) ::ₘ s(a.subst x (var y), b.subst x (var y)) ::ₘ (s(c, d) ::ₘ Δ) :
      Net S ℕ) = s(var x, var y) ::ₘ s(c, d) ::ₘ
        (s(a.subst x (var y), b.subst x (var y)) ::ₘ Δ) := by
    rw [Sym2.eq_swap (a := var y) (b := var x)]
    simp only [← Multiset.singleton_add]
    abel
  have W2 := Wire.mk x (var y) c d (s(a.subst x (var y), b.subst x (var y)) ::ₘ Δ)
    (L0.cast e) hx2
  refine W1.equiv.symm.trans ((Equiv.of_eq e).trans (W2.equiv.trans (Equiv.of_eq ?_)))
  exact Multiset.cons_swap _ _ _

/-- Renaming a wire whose two ends are on the two sides of one equation. -/
theorem equiv_rename_sides
    -- the net `a = b, Δ` is linear
    (hlin : Net.Linear (s(a, b) ::ₘ Δ))
    -- the name `x` occurs once in `a` and once in `b`
    (hxa : a.vars.count x = 1)
    (hxb : b.vars.count x = 1)
    -- the new name `y` does not occur in the net
    (hy : y ∉ Net.vars (s(a, b) ::ₘ Δ)) :
    -- renaming `x` to `y` in the equation gives the same graph
    Equiv (s(a, b) ::ₘ Δ) (s(a.subst x (var y), b.subst x (var y)) ::ₘ Δ) := by
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at hxl
  simp only [Net.vars_cons, eqVars_mk, Multiset.mem_add, not_or] at hy
  obtain ⟨⟨hya, hyb⟩, hyΔ⟩ := hy
  have hxy : x ≠ y := by
    rintro rfl
    exact hya (Multiset.one_le_count_iff_mem.1 (by omega))
  have ya := Multiset.count_eq_zero_of_notMem hya
  have yb := Multiset.count_eq_zero_of_notMem hyb
  have yΔ := Multiset.count_eq_zero_of_notMem hyΔ
  have L0 : Net.Linear (s(var y, var x) ::ₘ s(a.subst x (var y), b) ::ₘ Δ) := by
    intro z
    have hz := hlin z
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, vars_var, Multiset.count_singleton,
      count_rename a hxy hya] at hz ⊢
    by_cases hzy : z = y
    · subst hzy
      have : ¬ z = x := fun h => hxy h.symm
      simp only [this, ite_true, ite_false]
      omega
    · by_cases hzx : z = x
      · subst hzx
        simp only [hzy, ite_true, ite_false]
        omega
      · simp only [hzy, hzx, ite_false]
        omega
  have hmem : y ∈ (a.subst x (var y)).vars + b.vars := by
    refine Multiset.one_le_count_iff_mem.1 ?_
    rw [Multiset.count_add, count_rename a hxy hya]
    simp only [ite_true]
    omega
  have W1 := Wire.mk y (var x) (a.subst x (var y)) b Δ L0 hmem
  rw [subst_subst_back hya, subst_of_notMem hyb] at W1
  have e : (s(var y, var x) ::ₘ s(a.subst x (var y), b) ::ₘ Δ : Net S ℕ) =
      s(var x, var y) ::ₘ s(a.subst x (var y), b) ::ₘ Δ := by
    rw [Sym2.eq_swap (a := var y) (b := var x)]
  have hxb' : x ∈ (a.subst x (var y)).vars + b.vars :=
    Multiset.mem_add.2 (Or.inr (Multiset.one_le_count_iff_mem.1 (by omega)))
  have W2 := Wire.mk x (var y) (a.subst x (var y)) b Δ (L0.cast e) hxb'
  have hxa' : x ∉ (a.subst x (var y)).vars := by
    refine Multiset.count_eq_zero.1 ?_
    rw [count_rename a hxy hya]
    simp [hxy]
  rw [subst_of_notMem hxa'] at W2
  exact W1.equiv.symm.trans ((Equiv.of_eq e).trans W2.equiv)

end Cases

/-- A name that is not used in the net and is different from `y`. -/
theorem Net.exists_fresh
    -- the net
    (N : Net S ℕ)
    -- the name to avoid besides those of the net
    (y : ℕ) :
    ∃ w, w ∉ N.vars ∧ w ≠ y :=
  ⟨max N.vars.sup y + 1, fun h => by have := Multiset.le_sup h; omega, by omega⟩

/-- Renaming a wire whose two ends are in the same tree. One of the subtrees holding an end is
pulled out into its own equation, named by a new wire `w`; the wire is renamed there; and the
subtree is plugged back. -/
theorem equiv_rename_tree
    -- the tree that holds both ends of the wire
    (a : Term S ℕ) :
    -- for every other side `r`, rest of the net `Δ`, old name `x` and new name `y`,
    ∀ (r : Term S ℕ) (Δ : Net S ℕ) (x y : ℕ),
      -- if the net `r = a, Δ` is linear,
      Net.Linear (s(r, a) ::ₘ Δ) →
      -- `x` occurs twice in `a`,
      a.vars.count x = 2 →
      -- and `y` does not occur in the net,
      y ∉ Net.vars (s(r, a) ::ₘ Δ) →
      -- then renaming `x` to `y` in `a` gives the same graph
      Equiv (s(r, a) ::ₘ Δ) (s(r, a.subst x (var y)) ::ₘ Δ) := by
  induction a with
  | var z =>
    intro r Δ x y _ hx
    rw [vars_var, Multiset.count_singleton] at hx
    split_ifs at hx; omega
  | app α ts ih =>
    intro r Δ x y hlin hx hy
    have hxl := hlin x
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at hxl
    simp only [Net.vars_cons, eqVars_mk, Multiset.mem_add, not_or] at hy
    obtain ⟨⟨hyr, hya⟩, hyΔ⟩ := hy
    have hxa : x ∈ (app α ts).vars := Multiset.one_le_count_iff_mem.1 (by omega)
    have hxy : x ≠ y := by rintro rfl; exact hya hxa
    have hxr : x ∉ r.vars := Multiset.count_eq_zero.1 (by omega)
    -- a subtree holding an end of the wire
    obtain ⟨i, hi⟩ : ∃ i, (ts i).vars.count x ≠ 0 := by
      have hsum : ∑ i, (ts i).vars.count x ≠ 0 := by
        rw [← Multiset.count_sum', ← vars_app]; omega
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      exact ⟨i, hi⟩
    -- a new name for the root of that subtree
    obtain ⟨w, hwN, hwy⟩ := Net.exists_fresh (s(r, app α ts) ::ₘ Δ) y
    simp only [Net.vars_cons, eqVars_mk, Multiset.mem_add, not_or] at hwN
    obtain ⟨⟨hwr, hwa⟩, hwΔ⟩ := hwN
    have hwx : w ≠ x := by rintro rfl; exact hwa hxa
    have hwi : w ∉ (ts i).vars := by
      simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and, not_exists] at hwa
      exact hwa i
    have hyi : y ∉ (ts i).vars := by
      simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and, not_exists] at hya
      exact hya i
    have hU := count_vars_update ts i w
    have wr := Multiset.count_eq_zero_of_notMem hwr
    have wa := Multiset.count_eq_zero_of_notMem hwa
    have wΔ := Multiset.count_eq_zero_of_notMem hwΔ
    have wi := Multiset.count_eq_zero_of_notMem hwi
    have ya := Multiset.count_eq_zero_of_notMem hya
    have yi := Multiset.count_eq_zero_of_notMem hyi
    have hUw : (app α (Function.update ts i (var w))).vars.count w = 1 := by
      have := hU w; simp only [ite_true] at this; omega
    have hUy : y ∉ (app α (Function.update ts i (var w))).vars := by
      refine Multiset.count_eq_zero.1 ?_
      have := hU y
      have hyw : ¬ y = w := fun h => hwy h.symm
      simp only [hyw, ite_false] at this
      omega
    have hUx := hU x
    have hxw : ¬ x = w := fun h => hwx h.symm
    simp only [hxw, ite_false] at hUx
    -- pull the subtree out
    have L1 : Net.Linear
        (s(var w, ts i) ::ₘ s(r, app α (Function.update ts i (var w))) ::ₘ Δ) := by
      intro z
      have hz := hlin z
      have hUz := hU z
      simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, vars_var,
        Multiset.count_singleton] at hz ⊢
      by_cases hzw : z = w
      · subst hzw
        simp only [ite_true] at hUz ⊢
        omega
      · simp only [hzw, ite_false] at hUz ⊢
        omega
    have P1 := Wire.mk w (ts i) r (app α (Function.update ts i (var w))) Δ L1
      (Multiset.mem_add.2 (Or.inr (Multiset.one_le_count_iff_mem.1 (by omega))))
    rw [subst_of_notMem hwr, subst_update ts i hwa] at P1
    -- rename the wire in the net with the subtree pulled out
    have E12 : Equiv (s(var w, ts i) ::ₘ s(r, app α (Function.update ts i (var w))) ::ₘ Δ)
        (s(var w, (ts i).subst x (var y)) ::ₘ
          s(r, (app α (Function.update ts i (var w))).subst x (var y)) ::ₘ Δ) := by
      have hyN1 : y ∉ Net.vars (s(var w, ts i) ::ₘ
          s(r, app α (Function.update ts i (var w))) ::ₘ Δ) := by
        simp only [Net.vars_cons, eqVars_mk, Multiset.mem_add, not_or, vars_var,
          Multiset.mem_singleton]
        exact ⟨⟨fun h => hwy h.symm, hyi⟩, ⟨hyr, hUy⟩, hyΔ⟩
      by_cases h2 : (ts i).vars.count x = 2
      · -- both ends are in the subtree: induction
        have hxU : x ∉ (app α (Function.update ts i (var w))).vars :=
          Multiset.count_eq_zero.1 (by omega)
        rw [subst_of_notMem hxU]
        exact ih i (var w) _ x y L1 h2 hyN1
      · -- one end in the subtree, the other in the rest of the tree
        have h1 : (ts i).vars.count x = 1 := by omega
        have := equiv_rename_two (a := var w) (b := ts i) (c := r)
          (d := app α (Function.update ts i (var w))) (Δ := Δ) (x := x) (y := y) L1
          (Multiset.mem_add.2 (Or.inr (Multiset.one_le_count_iff_mem.1 (by omega))))
          (Multiset.mem_add.2 (Or.inr (Multiset.one_le_count_iff_mem.1 (by omega)))) hyN1
        rwa [subst_var_of_ne _ hwx, subst_of_notMem hxr] at this
    -- plug the renamed subtree back
    have L2 := E12.linear L1
    have hUw' : w ∈ r.vars +
        ((app α (Function.update ts i (var w))).subst x (var y)).vars := by
      refine Multiset.mem_add.2 (Or.inr (Multiset.one_le_count_iff_mem.1 ?_))
      rw [count_rename _ hxy hUy]
      simp only [hwy, hwx, ite_false]
      omega
    have W3 := Wire.mk w ((ts i).subst x (var y)) r
      ((app α (Function.update ts i (var w))).subst x (var y)) Δ L2 hUw'
    have hshape : (app α (Function.update ts i (var w))).subst x (var y) =
        app α (Function.update (fun j => (ts j).subst x (var y)) i (var w)) := by
      change app α _ = app α _
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact subst_var_of_ne _ hwx
      · simp only [Function.update_of_ne hj]
        rfl
    have hw' : w ∉ (app α fun j => (ts j).subst x (var y)).vars := by
      refine Multiset.count_eq_zero.1 ?_
      have := count_rename (app α ts) hxy hya w
      simp only [hwy, hwx, ite_false] at this
      exact this.trans wa
    have hres : ((app α (Function.update ts i (var w))).subst x (var y)).subst w
        ((ts i).subst x (var y)) = (app α ts).subst x (var y) := by
      rw [hshape]
      exact subst_update (fun j => (ts j).subst x (var y)) i hw'
    rw [subst_of_notMem hwr, hres] at W3
    exact P1.equiv.symm.trans (E12.trans W3.equiv)

-- ============================================================================================
-- 4. Main result: renaming an internal wire
-- ============================================================================================

/-- **Renaming an internal wire.** In a linear net, renaming a name that occurs twice to a name
that does not occur gives the same graph. -/
theorem Net.equiv_rename
    -- the linear net
    {N : Net S ℕ}
    (hlin : N.Linear)
    -- the old name `x`, which occurs twice in the net: an internal wire
    {x y : ℕ}
    (hx : N.vars.count x = 2)
    -- the new name `y`, which does not occur in the net
    (hy : y ∉ N.vars) :
    -- the net with `x` renamed to `y` is the same graph
    Equiv N (N.rename x y) := by
  have hxm : x ∈ Multiset.bind N eqVars := Multiset.one_le_count_iff_mem.1 (by
    change 1 ≤ N.vars.count x; omega)
  obtain ⟨e, he, hxe⟩ := Multiset.mem_bind.1 hxm
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem he
    rw [eqVars_mk] at hxe
    have hab := Multiset.one_le_count_iff_mem.2 hxe
    rw [Multiset.count_add] at hab
    have hx' := hx
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at hx'
    rw [Net.rename_cons]
    by_cases hΔ : x ∈ Net.vars (Δ : Net S ℕ)
    · -- the other end is in another equation
      obtain ⟨e₂, he₂, hxe₂⟩ := Multiset.mem_bind.1 (show x ∈ Multiset.bind Δ eqVars from hΔ)
      induction e₂ using Sym2.ind with
      | _ c d =>
        obtain ⟨Δ', rfl⟩ := Multiset.exists_cons_of_mem he₂
        rw [eqVars_mk] at hxe₂
        have hcd := Multiset.one_le_count_iff_mem.2 hxe₂
        rw [Multiset.count_add] at hcd
        simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at hx'
        have hΔ' : x ∉ Net.vars (Δ' : Net S ℕ) := Multiset.count_eq_zero.1 (by omega)
        rw [Net.rename_cons, Net.rename_of_notMem y hΔ']
        exact equiv_rename_two hlin hxe hxe₂ hy
    · rw [Net.rename_of_notMem y hΔ]
      have hΔ0 := Multiset.count_eq_zero_of_notMem hΔ
      by_cases ha : a.vars.count x = 1
      · exact equiv_rename_sides hlin ha (by omega) hy
      · by_cases ha0 : a.vars.count x = 0
        · -- both ends in `b`
          rw [subst_of_notMem (Multiset.count_eq_zero.1 ha0)]
          exact equiv_rename_tree b a Δ x y hlin (by omega) hy
        · -- both ends in `a`
          have hb0 : b.vars.count x = 0 := by omega
          rw [subst_of_notMem (Multiset.count_eq_zero.1 hb0)]
          have e₁ : (s(a, b) ::ₘ Δ : Net S ℕ) = s(b, a) ::ₘ Δ := by rw [Sym2.eq_swap]
          have e₂ : (s(a.subst x (var y), b) ::ₘ Δ : Net S ℕ) =
              s(b, a.subst x (var y)) ::ₘ Δ := by rw [Sym2.eq_swap]
          rw [e₁, e₂]
          exact equiv_rename_tree a b Δ x y (hlin.cast e₁) (by omega) (e₁ ▸ hy)

end INet
