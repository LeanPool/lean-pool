/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Multiplexors.AutoMux
public import LeanPool.InteractionCombinators.Universality.Duplication.DupPackage
public import LeanPool.InteractionCombinators.Universality.Menus.Package

/-!
# Lafont, "Interaction Combinators" (1997): the copier `C_n`

Page 88, first picture of Section 2.6: a copier `C_n` is a principal net of arity `n` such that a
package plugged into its root reduces to `n` copies of the package, one on each auxiliary port.
Lafont observes that when the package is built without `δ` (here `dup`), Lemma 3 gives "an obvious
implementation of the `C_n` (in fact, the same as for the `T_n`)". So `C_n` is the autodual
multiplexor `T_n` of Fig. 5.

Contents, in the order of the file:

1. Definition: `copier`, the net `C_n`, which is `autoMux`.
2. Auxiliary lemmas: `vars_bind_var`, `IsPackage.bind_var`, `DupFree.bind_var`,
   `injOn_comp_bind_var`. A package without `dup`, renamed injectively on its names, is again a
   package without `dup`.
3. Main result: `copier_package`, the property of `C_n` (page 88), for every package without
   `dup`.
4. An example showing that the hypotheses of `copier_package` can hold.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- The copier `C_n` (Lafont, page 88, first picture of Section 2.6), applied to the trees plugged
into its `n` auxiliary ports. For packages built without `dup`, the paper takes `C_n` to be the
autodual multiplexor `T_n` (Fig. 5, page 83): `era` for `n = 0`, a wire for `n = 1`, and a
right-nested tree of `dup` cells for `n ≥ 2`. -/
abbrev copier
    -- the trees plugged into the auxiliary ports, in order
    (us : List (Term sig ℕ)) :
    Term sig ℕ :=
  autoMux us

-- ============================================================================================
-- 2. Auxiliary lemmas: renaming a package
-- ============================================================================================

/-- The names of a tree renamed by `f` are the images by `f` of its names. -/
theorem vars_bind_var
    -- the renaming
    (f : ℕ → ℕ)
    -- the tree
    (t : Term sig ℕ) :
    (t.bind fun x => var (f x)).vars = t.vars.map f := by
  rw [Term.vars_bind]
  simp [Multiset.bind_singleton]

/-- A package renamed by a function injective on its names is a package (page 80: the names of
the wires of a package are arbitrary). -/
theorem IsPackage.bind_var
    -- the package
    {π : Term sig ℕ}
    (hπ : π.IsPackage)
    -- the renaming, injective on the names of the package
    (f : ℕ → ℕ)
    (hf : Set.InjOn f {x | x ∈ π.vars}) :
    (π.bind fun x => var (f x)).IsPackage := by
  intro y hy
  rw [vars_bind_var] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
  rw [Multiset.count_map_eq_count f _ hf x hx]
  exact hπ x hx

/-- Renaming the leaves of a tree adds no `dup` cell. -/
theorem DupFree.bind_var
    -- a tree without `dup`
    {π : Term sig ℕ}
    (hd : DupFree π)
    -- the renaming
    (f : ℕ → ℕ) :
    DupFree (π.bind fun x => var (f x)) := by
  induction π using Comb.induction with
  | var x => trivial
  | era => rw [bind_mkEra]; trivial
  | con a b iha ihb =>
    rw [bind_mkCon, dupFree_mkCon]
    obtain ⟨ha, hb⟩ := dupFree_mkCon.1 hd
    exact ⟨iha ha, ihb hb⟩
  | dup a b => exact absurd hd dupFree_mkDup

/-- Two successive injective renamings of a package form one injective renaming. -/
theorem injOn_comp_bind_var
    -- the package and the two renamings, `g` applied first
    {π : Term sig ℕ}
    {f g : ℕ → ℕ}
    -- `g` is injective on the names of the package
    (hg : Set.InjOn g {x | x ∈ π.vars})
    -- `f` is injective on the names of the renamed package
    (hf : Set.InjOn f {x | x ∈ (π.bind fun x => var (g x)).vars}) :
    Set.InjOn (fun x => f (g x)) {x | x ∈ π.vars} := by
  intro x hx x' hx' h
  rw [vars_bind_var] at hf
  exact hg hx hx' (hf (Multiset.mem_map_of_mem g hx) (Multiset.mem_map_of_mem g hx') h)

-- ============================================================================================
-- 3. Main result: the property of the copier
-- ============================================================================================

/-- The property of the copier (Lafont, page 88, first picture of Section 2.6): a package `π`
without `dup`, plugged into the root of `C_n`, reduces to `n` copies of `π`, one on each auxiliary
port. Each copy is `π` with its internal wires renamed by a function injective on the names of
`π`, hence the same graph as `π`. For `n = 0` the package is erased (corollary of Lemma 2,
page 84); for `n ≥ 2` each `dup` of `C_n` duplicates it (corollary of Lemma 3, page 87). -/
theorem copier_package
    -- the package: every name occurs twice, and there is no `dup` cell
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    (hd : DupFree π)
    -- the trees plugged into the `n` auxiliary ports of the copier
    (us : List (Term sig ℕ))
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the package on the root of the copier, and `Δ`
    (hlin : Net.Linear (s(copier us, π) ::ₘ Δ)) :
    -- there are `n` renamings `fs` and a net `N` such that
    ∃ (fs : List (ℕ → ℕ)) (N : CNet),
      -- one renaming for each auxiliary port,
      fs.length = us.length ∧
      -- each injective on the names of the package,
      (∀ f ∈ fs, Set.InjOn f {x | x ∈ π.vars}) ∧
      -- the net reduces, up to wires, to `N`,
      StepsE system (s(copier us, π) ::ₘ Δ) N ∧
      -- and `N` is the same graph as: on each port `u`, the copy of `π` renamed by `f`; and `Δ`
      Equiv N
        ((List.zipWith (fun u f => s(u, π.bind (fun x => var (f x)))) us fs : CNet) + Δ) := by
  induction us using autoMux.induct generalizing π Δ with
  | case1 =>
    refine ⟨[], Δ, rfl, by simp, erase_package π hπ Δ hlin, ?_⟩
    simpa using Equiv.refl Δ
  | case2 u =>
    refine ⟨[id], _, rfl, by simp [Set.injOn_id], Relation.ReflTransGen.refl, Equiv.of_eq ?_⟩
    simp [copier, autoMux, Term.bind_var_self]
  | case3 t t' ts ih =>
    obtain ⟨f, g, N, hf, hg, hS, hE⟩ := dup_package π hπ hd t (autoMux (t' :: ts)) Δ hlin
    set πg := π.bind (fun x => var (g x)) with hπg
    have hK : Net.Linear (s(copier (t' :: ts), πg) ::ₘ
        s(t, π.bind (fun x => var (f x))) ::ₘ Δ) :=
      (hE.linear (hS.linear system_wellFormed.linear hlin)).cast (Multiset.cons_swap _ _ _)
    obtain ⟨fs, N', hlen, hfs, hS', hE'⟩ :=
      ih πg (IsPackage.bind_var hπ g hg) (hd.bind_var g) _ hK
    obtain ⟨M, hSM, hEM⟩ :=
      stepsE_of_equiv (hE.trans (Equiv.of_eq (Multiset.cons_swap _ _ _))) hS'
    refine ⟨f :: fs.map (fun f' x => f' (g x)), M, by simpa using hlen, ?_, hS.trans hSM,
      hEM.trans (hE'.trans (Equiv.of_eq ?_))⟩
    · intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · exact hf
      · obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hh
        exact injOn_comp_bind_var hg (hfs f' hf')
    · have e : ∀ f' : ℕ → ℕ, πg.bind (fun x => var (f' x)) =
          π.bind (fun x => var (f' (g x))) := fun f' => by
        rw [hπg, Term.bind_bind]
        rfl
      have hz : ∀ (vs : List (Term sig ℕ)) (gs : List (ℕ → ℕ)),
          List.zipWith (fun u f' => s(u, πg.bind (fun x => var (f' x)))) vs gs =
            List.zipWith (fun u f' => s(u, π.bind (fun x => var (f' x)))) vs
              (gs.map (fun f' x => f' (g x))) := by
        intro vs gs
        simp only [List.zipWith_map_right, e]
      rw [hz, List.zipWith_cons_cons, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]

-- ============================================================================================
-- 4. The hypotheses can hold
-- ============================================================================================

/-- The hypotheses of `copier_package` hold: a `con` whose auxiliary ports are joined by the wire
`0`, plugged into `C_3` with free auxiliary ports `1`, `2`, `3`, reduces to three copies. -/
example :
    ∃ (fs : List (ℕ → ℕ)) (N : CNet),
      fs.length = 3 ∧
      StepsE system ({s(copier [var 1, var 2, var 3], mkCon (var 0) (var 0))} : CNet) N ∧
      Equiv N
        ((List.zipWith (fun u f => s(u, mkCon (var (f 0)) (var (f 0)))) [var 1, var 2, var 3]
          fs : CNet)) := by
  obtain ⟨fs, N, hlen, -, hS, hE⟩ := copier_package (mkCon (var 0) (var 0))
    (isPackage_mkCon_var 0) (dupFree_mkCon.2 ⟨trivial, trivial⟩) [var 1, var 2, var 3] 0 (by
      intro y
      simp only [copier, autoMux, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkDup, vars_mkCon,
        vars_var, add_zero, Multiset.count_add, Multiset.count_singleton]
      split_ifs <;> omega)
  refine ⟨fs, N, hlen, by simpa [Multiset.insert_eq_cons] using hS, ?_⟩
  simpa using hE

end INet.Comb
