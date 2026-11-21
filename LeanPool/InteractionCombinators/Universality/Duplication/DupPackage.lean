/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Duplication.DupWiring
public import LeanPool.InteractionCombinators.Universality.Duplication.Duplication
public import LeanPool.InteractionCombinators.Text.RenameMany
public import LeanPool.InteractionCombinators.Universality.Menus.Package

/-!
# Lafont, "Interaction Combinators" (1997): duplicating a package

The corollary of Lemma 3 on page 87: a package `π` without `dup`, plugged into the principal port
of a `dup`, reduces to two copies of `π`.

The proof follows the paper. Lemma 3 (i) (`dup_tree_nested`) copies the tree and leaves one `dup`
on each leaf. In a package every leaf is one end of a wire, so these `dup` cells sit in pairs on
the wires of the package; Lemma 3 (ii) (`dup_wiring`) makes each pair annihilate, which leaves two
wires between names. Plugging these wires (`equiv_wires_var`) gives the two copies.

Contents, in the order of the file:

1. Auxiliary lemmas, equations between names: `subst_var_eq_bind`, `equiv_wire_var`,
   `equiv_wires_var`. An equation between two names is a wire, and can be removed by renaming.
2. Auxiliary lemma, the copies of a tree: `nested_spec`, the copies built by `nested`, leaf by
   leaf.
3. Auxiliary lemma, reduction after an equivalence: `stepsE_of_equiv`.
4. Main result: `dup_package`, the corollary of Lemma 3 (page 87).
5. An example showing that the hypotheses of `dup_package` can hold.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: equations between names
-- ============================================================================================

/-- Plugging a name into one name is a renaming of that name. -/
theorem subst_var_eq_bind
    -- the tree, and the name `a` plugged into the name `b`
    (c : Term sig ℕ)
    (a b : ℕ) :
    c.subst b (var a) = c.bind fun y => var (if y = b then a else y) := by
  unfold Term.subst
  congr 1
  funext y
  split_ifs <;> rfl

/-- An equation `a = b` between two names is a wire (page 70: a net is a graph, and a wire may
be cut by a name): if `b` occurs in the rest of the net, the equation can be removed by renaming
`b` to `a` there. -/
theorem equiv_wire_var
    -- the two names of the equation
    (a b : ℕ)
    -- the rest of the net, linear together with the equation
    (M : CNet)
    (hlin : Net.Linear (s(var a, var b) ::ₘ M))
    -- `b` occurs in the rest of the net
    (hb : b ∈ M.vars) :
    -- the equation is removed by renaming `b` to `a` in the rest of the net
    Equiv (s(var a, var b) ::ₘ M) (M.bind fun y => var (if y = b then a else y)) := by
  obtain ⟨e, he, hbe⟩ := Multiset.mem_bind.1 hb
  obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem he
  induction e using Sym2.ind with
  | _ c d =>
  have hb' : b ∈ c.vars + d.vars := by simpa using hbe
  have e1 : (s(var a, var b) ::ₘ s(c, d) ::ₘ M' : CNet) = s(var b, var a) ::ₘ s(c, d) ::ₘ M' := by
    rw [Sym2.eq_swap]
  have W := Wire.mk b (var a) c d M' (hlin.cast e1) hb'
  have hbM' : b ∉ Net.vars M' := by
    intro hm
    have h := hlin b
    simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at h
    have h1 := Multiset.count_pos.2 hb'
    have h2 := Multiset.count_pos.2 hm
    rw [Multiset.count_add] at h1
    omega
  refine (Equiv.of_eq e1).trans (W.equiv.trans (Equiv.of_eq ?_))
  have hM' : Net.bind (fun y => var (if y = b then a else y)) M' = M' := by
    rw [Net.bind_congr (g := var) fun y hy => by
      rw [ite_eq_right (fun (h : y = b) => absurd (h ▸ hy) hbM')]]
    exact Net.bind_var_self M'
  simp only [Net.bind, Multiset.map_cons, Sym2.map_mk] at hM' ⊢
  rw [hM', subst_var_eq_bind, subst_var_eq_bind]

/-- Several equations between names are removed at once. Each name `y` of `Q` is joined to
`ρ y` by an equation, and occurs once more in `M`; the targets `ρ y` are not in `Q`. Removing
the equations renames each `y` of `Q` to `ρ y` in `M`. -/
theorem equiv_wires_var
    -- the names `y` joined by an equation to `ρ y`
    (Q : Multiset ℕ)
    (ρ : ℕ → ℕ)
    -- the rest of the net, linear together with the equations
    (M : CNet)
    (hlin : Net.Linear (Q.map (fun y => s(var (ρ y), var y)) + M))
    -- each name of `Q` occurs in the rest of the net
    (hq : ∀ y ∈ Q, y ∈ M.vars)
    -- the targets `ρ y` are not in `Q`
    (hρ : ∀ y ∈ Q, ρ y ∉ Q) :
    -- the equations are removed by renaming each `y` of `Q` to `ρ y` in the rest of the net
    Equiv (Q.map (fun y => s(var (ρ y), var y)) + M)
      (M.bind fun y => var (if y ∈ Q then ρ y else y)) := by
  induction Q using Multiset.induction_on generalizing M with
  | empty =>
    simp only [Multiset.map_zero, zero_add, Multiset.notMem_zero, ite_false]
    exact Equiv.of_eq (Net.bind_var_self M).symm
  | cons y₀ Q ih =>
    set f₀ : ℕ → ℕ := fun y => if y = y₀ then ρ y₀ else y with hf₀
    have e0 : ((y₀ ::ₘ Q).map (fun y => s(var (ρ y), var y)) + M : CNet) =
        s(var (ρ y₀), var y₀) ::ₘ (Q.map (fun y => s(var (ρ y), var y)) + M) := by
      simp
    rw [e0] at hlin ⊢
    have hy₀M : y₀ ∈ M.vars := hq y₀ (Multiset.mem_cons_self _ _)
    -- `y₀` occurs neither in the other equations
    have hcount := hlin y₀
    have hQ : ∀ y ∈ Q, y ≠ y₀ ∧ ρ y ≠ y₀ := by
      intro y hy
      refine ⟨?_, fun h => hρ y (Multiset.mem_cons_of_mem hy) (h ▸ Multiset.mem_cons_self _ _)⟩
      rintro rfl
      obtain ⟨Q', rfl⟩ := Multiset.exists_cons_of_mem hy
      have := Multiset.count_pos.2 hy₀M
      simp only [Multiset.map_cons, Multiset.cons_add, Net.vars_cons, Net.vars_add, eqVars_mk,
        vars_var, Multiset.count_add, Multiset.count_singleton_self] at hcount
      omega
    have W := equiv_wire_var (ρ y₀) y₀ _ hlin
      (by rw [Net.vars_add]; exact Multiset.mem_add.2 (Or.inr hy₀M))
    have e1 : Net.bind (fun y => var (f₀ y)) (Q.map (fun y => s(var (ρ y), var y)) + M) =
        Q.map (fun y => s(var (ρ y), var y)) + M.bind (fun y => var (f₀ y)) := by
      unfold Net.bind
      rw [Multiset.map_add, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun y hy => ?_
      obtain ⟨h1, h2⟩ := hQ y hy
      simp [hf₀, h1, h2]
    have W' := W.trans (Equiv.of_eq e1)
    have L := W'.linear hlin
    have IH := ih (M.bind fun y => var (f₀ y)) L
      (by
        intro y hy
        rw [Net.vars_bind_var]
        refine Multiset.mem_map.2 ⟨y, hq y (Multiset.mem_cons_of_mem hy), ?_⟩
        simp [hf₀, (hQ y hy).1])
      (fun y hy h => hρ y (Multiset.mem_cons_of_mem hy) (Multiset.mem_cons_of_mem h))
    refine W'.trans (IH.trans (Equiv.of_eq ?_))
    rw [Net.bind_bind]
    refine Net.bind_congr fun z _ => ?_
    change var _ = var _
    congr 1
    by_cases hz : z = y₀
    · subst hz
      have : ρ z ∉ Q := fun h => hρ z (Multiset.mem_cons_self _ _) (Multiset.mem_cons_of_mem h)
      simp [hf₀, this]
    · simp [hf₀, hz, Multiset.mem_cons]

-- ============================================================================================
-- 2. Auxiliary lemma: the copies of a tree, leaf by leaf
-- ============================================================================================

/-- The copies built by `nested` (Lafont's picture for Lemma 3 (i), page 87), leaf by leaf. The
first copy `l` is `τ` with each leaf occurrence given its own new name `y`, and `σ y` is the
original leaf; the second copy `r` is `l` with each name `y` changed to `y + 1`; and `E` puts one
`dup` on each original leaf, `σ y = dup(y, y + 1)`. The new names lie in `[k, (nested k τ).k)`
and are pairwise distinct. -/
theorem nested_spec
    -- the tree, without `dup` cell
    (τ : Term sig ℕ)
    (hτ : DupFree τ)
    -- the first new name
    (k : ℕ) :
    -- there is a map `σ` from the new names to the original leaves such that
    ∃ σ : ℕ → ℕ,
      -- the tree is the first copy with each new name `y` changed back to `σ y`,
      τ = (nested k τ).l.bind (fun y => var (σ y)) ∧
      -- the second copy is the first with each name `y` changed to `y + 1`,
      (nested k τ).r = (nested k τ).l.bind (fun y => var (y + 1)) ∧
      -- the equations put `dup(y, y + 1)` on the original leaf `σ y`,
      (nested k τ).E = (nested k τ).l.vars.map
        (fun y => s(var (σ y), mkDup (var y) (var (y + 1)))) ∧
      -- the next free name is at least `k`,
      k ≤ (nested k τ).k ∧
      -- the new names `y` and `y + 1` lie in `[k, (nested k τ).k)`,
      (∀ y ∈ (nested k τ).l.vars, k ≤ y ∧ y + 2 ≤ (nested k τ).k) ∧
      -- and they are pairwise distinct
      ((nested k τ).l.vars + (nested k τ).l.vars.map (· + 1)).Nodup := by
  induction τ using Comb.induction generalizing k with
  | var x =>
    refine ⟨fun _ => x, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [nested_var]
  | era =>
    refine ⟨id, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [nested_mkEra]
  | dup a b => exact absurd hτ dupFree_mkDup
  | con a b iha ihb =>
    obtain ⟨hda, hdb⟩ := dupFree_mkCon.1 hτ
    obtain ⟨σb, hb1, hb2, hb3, hb4, hb5, hb6⟩ := ihb hdb k
    obtain ⟨σa, ha1, ha2, ha3, ha4, ha5, ha6⟩ := iha hda (nested k b).k
    rw [nested_mkCon]
    set Rb := nested k b with hRb
    set Ra := nested Rb.k a with hRa
    have hsa : ∀ y ∈ Ra.l.vars, (if y < Rb.k then σb y else σa y) = σa y := fun y hy =>
      ite_eq_right (fun h => by have := (ha5 y hy).1; omega)
    have hsb : ∀ y ∈ Rb.l.vars, (if y < Rb.k then σb y else σa y) = σb y := fun y hy =>
      ite_eq_left (by have := (hb5 y hy).2; omega)
    refine ⟨fun y => if y < Rb.k then σb y else σa y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change mkCon a b = (mkCon Ra.l Rb.l).bind _
      rw [bind_mkCon]
      congr 1
      · exact ha1.trans (Term.bind_congr fun y hy => by simp only [hsa y hy])
      · exact hb1.trans (Term.bind_congr fun y hy => by simp only [hsb y hy])
    · change mkCon Ra.r Rb.r = (mkCon Ra.l Rb.l).bind _
      rw [bind_mkCon, ha2, hb2]
    · change Ra.E + Rb.E = (mkCon Ra.l Rb.l).vars.map _
      rw [vars_mkCon, Multiset.map_add, ha3, hb3]
      congr 1
      · exact Multiset.map_congr rfl fun y hy => by simp only [hsa y hy]
      · exact Multiset.map_congr rfl fun y hy => by simp only [hsb y hy]
    · change k ≤ Ra.k
      omega
    · change ∀ y ∈ (mkCon Ra.l Rb.l).vars, k ≤ y ∧ y + 2 ≤ Ra.k
      intro y hy
      rw [vars_mkCon, Multiset.mem_add] at hy
      rcases hy with hy | hy
      · have := ha5 y hy; omega
      · have := hb5 y hy; omega
    · change ((mkCon Ra.l Rb.l).vars + (mkCon Ra.l Rb.l).vars.map (· + 1)).Nodup
      have e : ((mkCon Ra.l Rb.l).vars + (mkCon Ra.l Rb.l).vars.map (· + 1)) =
          (Ra.l.vars + Ra.l.vars.map (· + 1)) + (Rb.l.vars + Rb.l.vars.map (· + 1)) := by
        rw [vars_mkCon, Multiset.map_add]
        abel
      rw [e, Multiset.nodup_add]
      refine ⟨ha6, hb6, Multiset.disjoint_left.2 fun {z} hz hz' => ?_⟩
      have h1 : Rb.k ≤ z := by
        rcases Multiset.mem_add.1 hz with h | h
        · exact (ha5 z h).1
        · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 h
          have := (ha5 y hy).1; omega
      have h2 : z < Rb.k := by
        rcases Multiset.mem_add.1 hz' with h | h
        · have := (hb5 z h).2; omega
        · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 h
          have := (hb5 y hy).2; omega
      omega

-- ============================================================================================
-- 3. Auxiliary lemma: reduction after an equivalence
-- ============================================================================================

/-- An equivalence followed by a reduction up to wires is a reduction up to wires, to a net
equivalent to the end. -/
theorem stepsE_of_equiv
    -- three nets
    {N K M : CNet}
    -- `N` is the same graph as `K`, which reduces up to wires to `M`
    (hE : Equiv N K)
    (h : StepsE system K M) :
    -- `N` reduces up to wires to a net `M'` that is the same graph as `M`
    ∃ M',
      StepsE system N M' ∧
      Equiv M' M := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨K', ⟨K'', hK, hS⟩, hrest⟩
  · exact ⟨N, Relation.ReflTransGen.refl, hE⟩
  · exact ⟨M, Relation.ReflTransGen.head ⟨K'', hE.trans hK, hS⟩ hrest, Equiv.refl M⟩

-- ============================================================================================
-- 4. Main result: duplicating a package
-- ============================================================================================

/-- The corollary of Lemma 3, page 87: a package `π` without `dup`, plugged into the principal
port of a `dup` with auxiliary trees `u` and `v`, reduces to two copies of `π`, plugged into `u`
and `v`. The copies are `π` with its internal wires renamed injectively, by `f` and `g`: they are
the same graph as `π`.

Lemma 3 (i) leaves a `dup` on each leaf of the two copies; the two leaves of each wire `x` of `π`
give two `dup` cells joined by `x`, and Lemma 3 (ii) makes them annihilate. -/
theorem dup_package
    -- the package: every name occurs twice, and there is no `dup` cell
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    (hd : DupFree π)
    -- the trees plugged into the two auxiliary ports of the `dup`
    (u v : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the package on the principal port of the `dup`, and `Δ`
    (hlin : Net.Linear (s(mkDup u v, π) ::ₘ Δ)) :
    -- there are two renamings `f`, `g` and a net `N` such that
    ∃ (f g : ℕ → ℕ) (N : CNet),
      -- `f` is injective on the names of the package,
      Set.InjOn f {x | x ∈ π.vars} ∧
      -- so is `g`,
      Set.InjOn g {x | x ∈ π.vars} ∧
      -- the net reduces, up to wires, to `N`,
      StepsE system (s(mkDup u v, π) ::ₘ Δ) N ∧
      -- and `N` is the same graph as: the copy renamed by `f` on `u`, by `g` on `v`; and `Δ`
      Equiv N
        (s(u, π.bind (fun x => var (f x))) ::ₘ
          s(v, π.bind (fun x => var (g x))) ::ₘ Δ) := by
  classical
  -- Lemma 3 (i), with new names from a bound `n` on the names of the net
  obtain ⟨n, hn⟩ : ∃ n, Net.Below n (s(mkDup u v, π) ::ₘ Δ) :=
    ⟨(Net.vars (s(mkDup u v, π) ::ₘ Δ)).sup + 1, fun x hx => by
      have := Multiset.le_sup hx; omega⟩
  obtain ⟨hred, hnK, hbelK⟩ := dup_tree π hd n u v Δ hn
  have hN1lin := Steps.linear system_wellFormed.linear hred hlin
  obtain ⟨E1, -, -⟩ := flat_equiv_nested π hd n (dupNet n u v π).2 u v Δ hN1lin hbelK
  set K := (dupNet n u v π).2 with hK
  set C := nested K π with hC
  obtain ⟨σ, h1, h2, h3, -, h5, h6⟩ := nested_spec π hd K
  rw [← hC] at h1 h2 h3 h5 h6
  set L := C.l.vars with hL
  have hLnd : L.Nodup := (Multiset.nodup_add.1 h6).1
  have hdisj := (Multiset.nodup_add.1 h6).2.2
  have hnotS : ∀ y ∈ L, ∀ z ∈ L, y ≠ z + 1 := fun y hy z hz h =>
    Multiset.disjoint_left.1 hdisj hy (h ▸ Multiset.mem_map_of_mem (· + 1) hz)
  have hπv : π.vars = L.map σ := by
    rw [congrArg Term.vars h1, Term.vars_bind]
    simp [hL, Multiset.bind_singleton]
  have hrv : C.r.vars = L.map (· + 1) := by
    rw [h2, Term.vars_bind]
    simp [hL, Multiset.bind_singleton]
  -- the two leaves of each wire of `π`
  set D := π.vars.dedup with hD
  have hcard : ∀ x ∈ D, (L.filter (fun y => x = σ y)).card = 2 := by
    intro x hx
    rw [← Multiset.count_map, ← hπv]
    exact hπ x (Multiset.mem_dedup.1 hx)
  have hpair : ∀ x, ∃ a b, x ∈ D → L.filter (fun y => x = σ y) = {a, b} := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 (hcard x hx)
      exact ⟨a, b, fun _ => hab⟩
    · exact ⟨0, 0, fun h => absurd h hx⟩
  choose p q hpq using hpair
  have hmem : ∀ x ∈ D, ∀ y, (y ∈ L ∧ x = σ y) ↔ (y = p x ∨ y = q x) := by
    intro x hx y
    have h := (Multiset.mem_filter (p := fun y => x = σ y) (s := L) (a := y)).symm
    rw [hpq x hx] at h
    refine h.trans ?_
    simp
  have hpL : ∀ x ∈ D, p x ∈ L ∧ σ (p x) = x := fun x hx => by
    have := (hmem x hx (p x)).2 (Or.inl rfl)
    exact ⟨this.1, this.2.symm⟩
  have hqL : ∀ x ∈ D, q x ∈ L ∧ σ (q x) = x := fun x hx => by
    have := (hmem x hx (q x)).2 (Or.inr rfl)
    exact ⟨this.1, this.2.symm⟩
  have hpq_ne : ∀ x ∈ D, p x ≠ q x := by
    intro x hx h
    have hnd : (L.filter (fun y => x = σ y)).Nodup := hLnd.filter _
    rw [hpq x hx, h] at hnd
    simp at hnd
  have hpq' : ∀ x ∈ D, ∀ x' ∈ D, p x ≠ q x' := by
    intro x hx x' hx' h
    have : x' = x := by rw [← (hqL x' hx').2, ← h, (hpL x hx).2]
    subst this
    exact hpq_ne x' hx h
  have hσD : ∀ y ∈ L, σ y ∈ D := fun y hy =>
    Multiset.mem_dedup.2 (by rw [hπv]; exact Multiset.mem_map_of_mem σ hy)
  have hLeq : L = D.map p + D.map q := by
    refine (Multiset.Nodup.ext hLnd ?_).2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · rw [Multiset.nodup_add]
      refine ⟨(Multiset.nodup_dedup _).map_on ?_, (Multiset.nodup_dedup _).map_on ?_,
        Multiset.disjoint_left.2 fun {z} hz hz' => ?_⟩
      · intro x hx x' hx' h
        rw [← (hpL x hx).2, ← (hpL x' hx').2, h]
      · intro x hx x' hx' h
        rw [← (hqL x hx).2, ← (hqL x' hx').2, h]
      · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
        obtain ⟨x', hx', h⟩ := Multiset.mem_map.1 hz'
        exact hpq' x hx x' hx' h.symm
    · rcases (hmem (σ y) (hσD y hy) y).1 ⟨hy, rfl⟩ with h | h
      · exact Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨σ y, hσD y hy, h.symm⟩))
      · exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨σ y, hσD y hy, h.symm⟩))
    · rcases Multiset.mem_add.1 hy with h | h <;> obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 h
      · exact (hpL x hx).1
      · exact (hqL x hx).1
  -- the `dup` cells left by Lemma 3 (i) sit in pairs on the wires of `π`
  have hE : C.E = D.map (fun x => s(mkDup (var (p x)) (var (p x + 1)), var x)) +
      D.map (fun x => s(mkDup (var (q x)) (var (q x + 1)), var x)) := by
    rw [h3, hLeq, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 1
    · refine Multiset.map_congr rfl fun x hx => ?_
      simp only [Function.comp, (hpL x hx).2]
      exact Sym2.eq_swap
    · refine Multiset.map_congr rfl fun x hx => ?_
      simp only [Function.comp, (hqL x hx).2]
      exact Sym2.eq_swap
  set M : CNet := s(u, C.l) ::ₘ s(v, C.r) ::ₘ Δ with hM
  have eX : (s(u, C.l) ::ₘ s(v, C.r) ::ₘ (C.E + Δ) : CNet) =
      D.map (fun x => s(mkDup (var (p x)) (var (p x + 1)), var x)) +
        D.map (fun x => s(mkDup (var (q x)) (var (q x + 1)), var x)) + M := by
    rw [hE, hM]
    ms
  have hXlin := E1.linear hN1lin
  -- Lemma 3 (ii)
  have hW := dup_wiring D (fun x => var (p x)) (fun x => var (p x + 1)) (fun x => var (q x))
    (fun x => var (q x + 1)) M (hXlin.cast eX)
  have hYlin := hW.linear system_wellFormed.linear (hXlin.cast eX)
  -- the wires left between names
  set Q := D.map q + D.map (fun x => q x + 1) with hQ
  set ρ : ℕ → ℕ := fun z => if z ∈ D.map q then p (σ z) else p (σ (z - 1)) + 1 with hρ
  have hq1 : ∀ x ∈ D, q x + 1 ∉ D.map q := by
    intro x hx h
    obtain ⟨x', hx', h'⟩ := Multiset.mem_map.1 h
    exact hnotS _ (hqL x' hx').1 _ (hqL x hx).1 h'
  have hρq : ∀ x ∈ D, ρ (q x) = p x := fun x hx => by
    simp only [hρ, Multiset.mem_map_of_mem q hx, ite_true, (hqL x hx).2]
  have hρq1 : ∀ x ∈ D, ρ (q x + 1) = p x + 1 := fun x hx => by
    simp only [hρ, hq1 x hx, ite_false, Nat.add_sub_cancel, (hqL x hx).2]
  have eY : D.map (fun x => s(var (p x), var (q x))) +
      D.map (fun x => s(var (p x + 1), var (q x + 1))) + M =
      Q.map (fun y => s(var (ρ y), var y)) + M := by
    rw [hQ, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 2
    · exact Multiset.map_congr rfl fun x hx => by simp only [Function.comp, hρq x hx]
    · exact Multiset.map_congr rfl fun x hx => by simp only [Function.comp, hρq1 x hx]
  have hpQ : ∀ x ∈ D, p x ∉ Q ∧ p x + 1 ∉ Q := by
    intro x hx
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      rcases Multiset.mem_add.1 h with h | h <;> obtain ⟨x', hx', h'⟩ := Multiset.mem_map.1 h
    · exact hpq' x hx x' hx' h'.symm
    · exact hnotS _ (hpL x hx).1 _ (hqL x' hx').1 h'.symm
    · exact hnotS _ (hqL x' hx').1 _ (hpL x hx).1 h'
    · exact hpq' x hx x' hx' (by omega)
  have hQK : ∀ y ∈ Q, K ≤ y := by
    intro y hy
    rcases Multiset.mem_add.1 hy with h | h <;> obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 h
    · exact (h5 _ (hqL x hx).1).1
    · have := (h5 _ (hqL x hx).1).1; omega
  have EW := equiv_wires_var Q ρ M (hYlin.cast eY)
    (by
      intro y hy
      rw [hM]
      simp only [Net.vars_cons, eqVars_mk, Multiset.mem_add]
      rcases Multiset.mem_add.1 hy with h | h <;> obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 h
      · exact Or.inl (Or.inr (hqL x hx).1)
      · rw [hrv]
        exact Or.inr (Or.inl (Or.inr (Multiset.mem_map_of_mem _ (hqL x hx).1))))
    (by
      intro y hy
      rcases Multiset.mem_add.1 hy with h | h <;> obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 h
      · rw [hρq x hx]; exact (hpQ x hx).1
      · rw [hρq1 x hx]; exact (hpQ x hx).2)
  -- the renamed net is the two copies of `π`
  set G : ℕ → ℕ := fun y => if y ∈ Q then ρ y else y with hG
  have hGold : ∀ y, y < n → G y = y := fun y hy =>
    ite_eq_right (fun h => by have := hQK y h; omega)
  simp only [Net.below_cons, below_mkDup] at hn
  obtain ⟨⟨hu, hv⟩, -, hΔ⟩ := hn
  have hGl : C.l.bind (fun y => var (G y)) = π.bind (fun x => var (p x)) := by
    conv_rhs => rw [h1]
    rw [Term.bind_bind]
    refine Term.bind_congr fun z hz => ?_
    change var (G z) = var (p (σ z))
    congr 1
    rcases (hmem (σ z) (hσD z hz) z).1 ⟨hz, rfl⟩ with h | h
    · rw [h, (hpL _ (hσD z hz)).2]
      exact ite_eq_right (hpQ _ (hσD z hz)).1
    · have hzq : z ∈ D.map q := h ▸ Multiset.mem_map_of_mem q (hσD z hz)
      have hzQ : z ∈ Q := Multiset.mem_add.2 (Or.inl hzq)
      simp only [hG, hzQ, ite_true, hρ, hzq]
  have hGr : C.r.bind (fun y => var (G y)) = π.bind (fun x => var (p x + 1)) := by
    conv_rhs => rw [h1]
    rw [h2, Term.bind_bind, Term.bind_bind]
    refine Term.bind_congr fun z hz => ?_
    change var (G (z + 1)) = var (p (σ z) + 1)
    congr 1
    rcases (hmem (σ z) (hσD z hz) z).1 ⟨hz, rfl⟩ with h | h
    · rw [h, (hpL _ (hσD z hz)).2]
      exact ite_eq_right (hpQ _ (hσD z hz)).2
    · have hx := hσD z hz
      have hzQ : z + 1 ∈ Q :=
        Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨σ z, hx, by rw [← h]⟩))
      simp only [hG, hzQ, ite_true]
      calc ρ (z + 1) = ρ (q (σ z) + 1) := by rw [← h]
        _ = p (σ z) + 1 := hρq1 _ hx
  have hGu : u.bind (fun y => var (G y)) = u := by
    rw [Term.bind_congr (g := var) fun y hy => by rw [hGold y (hu y hy)]]
    exact Term.bind_var_self u
  have hGv : v.bind (fun y => var (G y)) = v := by
    rw [Term.bind_congr (g := var) fun y hy => by rw [hGold y (hv y hy)]]
    exact Term.bind_var_self v
  have hGΔ : Net.bind (fun y => var (G y)) Δ = Δ := by
    rw [Net.bind_congr (g := var) fun y hy => by rw [hGold y (hΔ y hy)]]
    exact Net.bind_var_self Δ
  have eZ : Net.bind (fun y => var (G y)) M =
      s(u, π.bind (fun x => var (p x))) ::ₘ s(v, π.bind (fun x => var (p x + 1))) ::ₘ Δ := by
    rw [hM, ← hGl, ← hGr]
    conv_rhs => rw [← hGu, ← hGv, ← hGΔ]
    simp only [Net.bind, Multiset.map_cons, Sym2.map_mk]
  -- assemble
  obtain ⟨N, hS, hEN⟩ := stepsE_of_equiv (E1.trans (Equiv.of_eq eX)) hW
  have hinj : Set.InjOn p {x | x ∈ π.vars} := by
    intro x hx x' hx' h
    have hx : x ∈ D := Multiset.mem_dedup.2 hx
    have hx' : x' ∈ D := Multiset.mem_dedup.2 hx'
    rw [← (hpL x hx).2, ← (hpL x' hx').2, h]
  refine ⟨p, fun x => p x + 1, N, hinj, fun x hx x' hx' h => hinj hx hx' (by simpa using h),
    hred.stepsE.trans hS, ?_⟩
  exact hEN.trans ((Equiv.of_eq eY).trans (EW.trans (Equiv.of_eq eZ)))

-- ============================================================================================
-- 5. The hypotheses can hold
-- ============================================================================================

/-- The hypotheses of `dup_package` hold: a `con` whose auxiliary ports are joined by the wire
`0`, plugged into a `dup` with free auxiliary ports `1` and `2`, reduces to two copies of the
package, one on `1` and one on `2`, each with its own wire. -/
example :
    ∃ (f g : ℕ → ℕ) (N : CNet),
      StepsE system ({s(mkDup (var 1) (var 2), mkCon (var 0) (var 0))} : CNet) N ∧
      Equiv N
        {s(var 1, mkCon (var (f 0)) (var (f 0))), s(var 2, mkCon (var (g 0)) (var (g 0)))} := by
  obtain ⟨f, g, N, -, -, hS, hE⟩ := dup_package (mkCon (var 0) (var 0)) (isPackage_mkCon_var 0)
    (dupFree_mkCon.2 ⟨trivial, trivial⟩) (var 1) (var 2) 0 (by
      intro y
      simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkDup, vars_mkCon, vars_var,
        add_zero, Multiset.count_add, Multiset.count_singleton]
      split_ifs <;> omega)
  refine ⟨f, g, N, hS, ?_⟩
  simpa [Multiset.insert_eq_cons] using hE

end INet.Comb
