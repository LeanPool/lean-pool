/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.RenameMany

/-!
# Tools for the decomposition of a rule (page 85)

Three generic tools used by `RecursionFree/Decomposition.lean` and the files around it.

* `Term.renameOpt`, `Net.renameOpt` — rename the names of a tree or a net by a *partial* function
  `ν → Option μ`. The result exists when every name that occurs is renamed
  (`Term.renameOpt_spec`, `Net.renameOpt_spec`); it has the renamed names, the same cells, and
  plugging into it is plugging into the original. A partial function is needed because the
  target type may be empty while the source is not.
* `rankIn` — the position of an element of a finite set, for an injective key into `ℕ`. It
  numbers the set from `0` to its cardinality minus one (`rankIn_lt`, `rankIn_injOn`,
  `rankIn_surj`).
* `Net.equiv_absorb` — equations `p = c p` between a free port `p` and a wire `c p` of the net
  are absorbed by wire substitution: the result is the net with `p` in place of `c p`.

Contents, in the order of the file:

1. Definitions: renaming by a partial function, `Term.renameOpt`, `renameOptEq`,
   `Net.renameOpt`.
2. Auxiliary lemma: `Multiset.filterMap_finset_sum`.
3. Results: what renaming by a partial function gives, `Term.renameOpt_spec`,
   `renameOptEq_spec`, `Net.renameOpt_spec`, `Net.mem_renameOpt`.
4. Ranks: the definition `rankIn` and `rankIn_lt`, `rankIn_lt_rank`, `rankIn_injOn`,
   `rankIn_surj`.
5. Absorbing equations between a port and a wire: the auxiliary lemmas `Net.bind_var_of_fix`,
   `Net.wire_var`, and the main result `Net.equiv_absorb`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

section RenameOpt

-- the names before and after the renaming
variable {ν μ : Type}

-- ============================================================================================
-- 1. Definitions: renaming by a partial function
-- ============================================================================================

/-- Rename the leaves of a tree by a partial function; `none` if some leaf is not renamed. -/
def Term.renameOpt
    -- the partial renaming
    (g : ν → Option μ) :
    Term S ν → Option (Term S μ)
  | var x => (g x).map var
  | app α ts =>
    if h : ∀ i, (Term.renameOpt g (ts i)).isSome then
      some (app α fun i => (Term.renameOpt g (ts i)).get (h i))
    else none

/-- Rename the names of an equation by a partial function. -/
def renameOptEq
    -- the partial renaming
    (g : ν → Option μ) :
    Sym2 (Term S ν) → Option (Sym2 (Term S μ)) :=
  Sym2.lift ⟨fun u v => (u.renameOpt g).bind fun u' => (v.renameOpt g).map fun v' => s(u', v'),
    fun u v => by
      cases hu : u.renameOpt g <;> cases hv : v.renameOpt g <;> simp [hu, hv, Sym2.eq_swap]⟩

/-- Rename the names of a net by a partial function; equations that cannot be renamed are
dropped (there is none when every name is renamed, `Net.renameOpt_spec`). -/
def Net.renameOpt
    -- the partial renaming
    (g : ν → Option μ)
    -- the net
    (N : Net S ν) :
    Net S μ :=
  N.filterMap (renameOptEq g)

-- ============================================================================================
-- 2. Auxiliary lemma: `filterMap` of a finite sum
-- ============================================================================================

/-- `filterMap` distributes over a finite sum of multisets. -/
theorem _root_.Multiset.filterMap_finset_sum
    -- the index set and the family of multisets
    {ι α β : Type}
    (s : Finset ι)
    (f : ι → Multiset α)
    -- the partial function
    (g : α → Option β) :
    (∑ i ∈ s, f i).filterMap g = ∑ i ∈ s, (f i).filterMap g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Multiset.filterMap_add, ih]

-- ============================================================================================
-- 3. Results: what renaming by a partial function gives
-- ============================================================================================

/-- When every leaf of `t` is renamed by `g`, the renamed tree exists; its leaves are the renamed
leaves, its cells are those of `t`, and plugging `F` into it is plugging `G` into `t` as soon as
`F` and `G` agree through `g`. -/
theorem Term.renameOpt_spec
    -- the partial renaming
    (g : ν → Option μ) :
    -- for every tree `t` whose leaves are all renamed by `g`,
    ∀ t : Term S ν, (∀ x ∈ t.vars, (g x).isSome) →
      -- there is a tree `t'` such that
      ∃ t',
        -- `t'` is the renamed tree,
        t.renameOpt g = some t' ∧
        -- its leaves are the renamed leaves of `t`,
        t'.vars = t.vars.filterMap g ∧
        -- its cells are those of `t`,
        t'.cells = t.cells ∧
        -- and plugging `F` into `t'` is plugging `G` into `t` when `F` and `G` agree through `g`
        ∀ {κ : Type} (F : μ → Term S κ) (G : ν → Term S κ),
          (∀ x ∈ t.vars, ∀ y, g x = some y → F y = G x) → t'.bind F = t.bind G
  | var x, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    refine ⟨var y, by simp [Term.renameOpt, hy], ?_, rfl, fun F G hFG => ?_⟩
    · change ({y} : Multiset μ) = Multiset.filterMap g ({x} : Multiset ν)
      rw [← Multiset.cons_zero, ← Multiset.cons_zero, Multiset.filterMap_cons_some _ _ _ hy,
        Multiset.filterMap_zero]
    simpa using hFG x (by simp) y hy
  | app α ts, h => by
    have hmem : ∀ i, ∀ x ∈ (ts i).vars, x ∈ (app α ts).vars := fun i x hx => by
      simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨i, hx⟩
    have ih := fun i => Term.renameOpt_spec g (ts i) fun x hx => h x (hmem i x hx)
    choose t' ht' hv hc hb using ih
    have hs : ∀ i, (Term.renameOpt g (ts i)).isSome := fun i => by simp [ht' i]
    refine ⟨app α t', ?_, ?_, ?_, ?_⟩
    · rw [Term.renameOpt]
      split_ifs
      congr 2
      funext i
      simp [ht' i]
    · simp [hv, Multiset.filterMap_finset_sum]
    · simp [hc]
    · intro κ F G hFG
      simp only [bind_app]
      congr 1
      funext i
      exact hb i F G fun x hx => hFG x (hmem i x hx)

/-- When every name of an equation `e` is renamed by `g`, the renamed equation exists; its names
are the renamed names, its cells are those of `e`, and plugging `F` into it is plugging `G` into
`e` as soon as `F` and `G` agree through `g`. -/
theorem renameOptEq_spec
    -- the partial renaming
    (g : ν → Option μ)
    -- the equation, all of whose names are renamed
    (e : Sym2 (Term S ν))
    (h : ∀ x ∈ eqVars e, (g x).isSome) :
    -- there is an equation `e'` such that
    ∃ e',
      -- `e'` is the renamed equation,
      renameOptEq g e = some e' ∧
      -- its names are the renamed names of `e`,
      eqVars e' = (eqVars e).filterMap g ∧
      -- its cells are those of `e`,
      eqCells e' = eqCells e ∧
      -- and plugging `F` into `e'` is plugging `G` into `e` when `F` and `G` agree through `g`
      ∀ {κ : Type} (F : μ → Term S κ) (G : ν → Term S κ),
        (∀ x ∈ eqVars e, ∀ y, g x = some y → F y = G x) →
          e'.map (Term.bind F) = e.map (Term.bind G) := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [eqVars_mk, Multiset.mem_add] at h
    obtain ⟨u', hu, hvu, hcu, hbu⟩ := Term.renameOpt_spec g u fun x hx => h x (Or.inl hx)
    obtain ⟨v', hv, hvv, hcv, hbv⟩ := Term.renameOpt_spec g v fun x hx => h x (Or.inr hx)
    refine ⟨s(u', v'), by simp [renameOptEq, hu, hv], by simp [hvu, hvv, Multiset.filterMap_add],
      by simp [hcu, hcv], fun F G hFG => ?_⟩
    simp only [eqVars_mk, Multiset.mem_add] at hFG
    simp only [Sym2.map_mk]
    rw [hbu F G fun x hx => hFG x (Or.inl hx), hbv F G fun x hx => hFG x (Or.inr hx)]

/-- When every name of `N` is renamed by `g`, the renamed net has the renamed names and the same
cells, and plugging `F` into it is plugging `G` into `N` as soon as `F` and `G` agree through
`g`. -/
theorem Net.renameOpt_spec
    -- the partial renaming
    (g : ν → Option μ)
    -- the net, all of whose names are renamed
    (N : Net S ν)
    (h : ∀ x ∈ N.vars, (g x).isSome) :
    -- the names of the renamed net are the renamed names of `N`,
    (Net.renameOpt g N).vars = N.vars.filterMap g ∧
    -- its cells are those of `N`,
    (Net.renameOpt g N).cells = N.cells ∧
    -- and plugging `F` into it is plugging `G` into `N` when `F` and `G` agree through `g`
    ∀ {κ : Type} (F : μ → Term S κ) (G : ν → Term S κ),
      (∀ x ∈ N.vars, ∀ y, g x = some y → F y = G x) →
        (Net.renameOpt g N).bind F = N.bind G := by
  induction N using Multiset.induction_on with
  | empty => simp [Net.renameOpt, Net.bind, Net.cells]
  | cons e N ih =>
    simp only [Net.vars_cons, Multiset.mem_add] at h
    obtain ⟨e', he, hv, hc, hb⟩ := renameOptEq_spec g e fun x hx => h x (Or.inl hx)
    obtain ⟨ihv, ihc, ihb⟩ := ih fun x hx => h x (Or.inr hx)
    have hcons : Net.renameOpt g (e ::ₘ N) = e' ::ₘ Net.renameOpt g N := by
      exact Multiset.filterMap_cons_some _ _ _ he
    refine ⟨?_, ?_, fun F G hFG => ?_⟩
    · rw [hcons, Net.vars_cons, Net.vars_cons, Multiset.filterMap_add, hv, ihv]
    · rw [hcons, Net.cells_cons, Net.cells_cons, hc, ihc]
    · simp only [Net.vars_cons, Multiset.mem_add] at hFG
      rw [hcons]
      simp only [Net.bind, Multiset.map_cons]
      rw [hb F G fun x hx => hFG x (Or.inl hx)]
      congr 1
      exact ihb F G fun x hx => hFG x (Or.inr hx)

/-- Every equation of the renamed net is the renaming of an equation of `N`. -/
theorem Net.mem_renameOpt
    -- the partial renaming, the net, and an equation of the renamed names
    {g : ν → Option μ}
    {N : Net S ν}
    {e' : Sym2 (Term S μ)} :
    -- `e'` is in the renamed net if and only if it is the renaming of an equation of `N`
    e' ∈ Net.renameOpt g N ↔ ∃ e ∈ N, renameOptEq g e = some e' :=
  Multiset.mem_filterMap _ _

end RenameOpt

-- ============================================================================================
-- 4. Ranks
-- ============================================================================================

section Rank

-- the elements that are ranked
variable {V : Type}

/-- The position of `x` in the finite set `M`, ordered by the key `κ`: the number of elements of
`M` with a smaller key. -/
def rankIn
    -- the finite set and the key that orders it
    (M : Finset V)
    (κ : V → ℕ)
    -- the element
    (x : V) :
    ℕ :=
  (M.filter fun y => κ y < κ x).card

-- the finite set and the key that orders it
variable {M : Finset V} {κ : V → ℕ}

/-- The rank of an element of `M` is less than the cardinality of `M`. -/
theorem rankIn_lt
    -- an element of `M`
    {x : V}
    (hx : x ∈ M) :
    rankIn M κ x < M.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨x, hx, lt_irrefl _⟩)

/-- An element of `M` with a smaller key has a smaller rank. -/
theorem rankIn_lt_rank
    -- an element `x` of `M`, and an element `y` with a larger key
    {x y : V}
    (hx : x ∈ M)
    (h : κ x < κ y) :
    rankIn M κ x < rankIn M κ y := by
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun z hz => ?_, fun he => ?_⟩)
  · simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans h⟩
  · have : x ∈ M.filter fun z => κ z < κ y := Finset.mem_filter.2 ⟨hx, h⟩
    rw [← he] at this
    exact lt_irrefl _ (Finset.mem_filter.1 this).2

/-- For an injective key, two elements of `M` with the same rank are equal. -/
theorem rankIn_injOn
    -- the key is injective
    (hκ : Function.Injective κ) :
    Set.InjOn (rankIn M κ) M := by
  intro x hx y hy h
  rcases lt_trichotomy (κ x) (κ y) with hl | he | hl
  · exact absurd h (rankIn_lt_rank hx hl).ne
  · exact hκ he
  · exact absurd h (rankIn_lt_rank hy hl).ne'

/-- For an injective key, every number below the cardinality of `M` is the rank of an element
of `M`. -/
theorem rankIn_surj
    -- the key is injective
    (hκ : Function.Injective κ)
    -- a number below the cardinality of `M`
    {l : ℕ}
    (hl : l < M.card) :
    -- it is the rank of an element of `M`
    ∃ x ∈ M, rankIn M κ x = l := by
  have hsub : M.image (rankIn M κ) ⊆ Finset.range M.card := fun n hn => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hn
    exact Finset.mem_range.2 (rankIn_lt hx)
  have hcard : (Finset.range M.card).card ≤ (M.image (rankIn M κ)).card := by
    rw [Finset.card_range, Finset.card_image_of_injOn (rankIn_injOn hκ)]
  have := Finset.eq_of_subset_of_card_le hsub hcard
  have hl' : l ∈ M.image (rankIn M κ) := this ▸ Finset.mem_range.2 hl
  simpa using hl'

end Rank

-- ============================================================================================
-- 5. Absorbing equations between a port and a wire
-- ============================================================================================

section Absorb

-- the names, with decidable equality
variable {ν : Type} [DecidableEq ν]

omit [DecidableEq ν] in
/-- Renaming the names of a net that occur by themselves changes nothing. -/
theorem Net.bind_var_of_fix
    -- the net, and a renaming that fixes every name of it
    {N : Net S ν}
    {f : ν → ν}
    (h : ∀ y ∈ N.vars, f y = y) :
    N.bind (fun y => var (f y)) = N := by
  rw [Net.bind_congr (g := var) fun y hy => by rw [h y hy]]
  exact Net.bind_var_self N

/-- A wire substitution of the name `c` by the name `p`, where `c` occurs once in `N`. -/
theorem Net.wire_var
    -- the rest of the net, and the names of the equation `c = p`
    {N : Net S ν}
    {c p : ν}
    -- the net with the equation `c = p` is linear
    (hlin : Net.Linear (s(var c, var p) ::ₘ N))
    -- `c` occurs in `N`
    (hc : c ∈ N.vars) :
    -- the equation `c = p` is absorbed: `N` with `p` in place of `c`
    Wire (s(var c, var p) ::ₘ N) (N.bind fun y => if y = c then var p else var y) := by
  obtain ⟨e, he, hce⟩ := Multiset.mem_bind.1 hc
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem he
  induction e using Sym2.ind with
  | _ u v =>
    have hcount := hlin c
    simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at hcount
    have hcuv : 1 ≤ (u.vars + v.vars).count c := Multiset.one_le_count_iff_mem.2 hce
    rw [Multiset.count_add] at hcuv
    have hΔ : c ∉ Net.vars Δ := by
      intro hm
      have := Multiset.one_le_count_iff_mem.2 hm
      omega
    have hΔ' : Net.bind (fun y => if y = c then var p else var y) Δ = Δ := by
      rw [Net.bind_congr (g := var) fun y hy => by
        have : y ≠ c := fun h => hΔ (h ▸ hy)
        simp [this]]
      exact Net.bind_var_self Δ
    have e : Net.bind (fun y => if y = c then var p else var y) (s(u, v) ::ₘ Δ) =
        s(u.subst c (var p), v.subst c (var p)) ::ₘ Δ := by
      simp only [Net.bind, Multiset.map_cons, Sym2.map_mk]
      exact congrArg₂ _ rfl hΔ'
    rw [e]
    exact Wire.mk c (var p) u v Δ hlin hce

/-- Equations `p = c p` between a name `p ∈ T` and a name `c p` that occurs in `N` are absorbed
by wire substitution: the result is `N` renamed by any `f` that sends `c p` to `p` and fixes `p`
and every other name of `N`. -/
theorem Net.equiv_absorb
    -- `c p` is the wire of `N` joined to the port `p`
    (c : ν → ν)
    -- the renaming that undoes the equations
    (f : ν → ν) :
    -- for every finite set `T` of ports and every net `N`,
    ∀ (T : Finset ν) (N : Net S ν),
      -- if `N` with the equations `c p = p` for `p ∈ T` is linear,
      Net.Linear (N + T.val.map (fun p => s(var (c p), var p))) →
      -- `c` is injective on `T`,
      Set.InjOn c T →
      -- each `c p` occurs in `N`,
      (∀ p ∈ T, c p ∈ N.vars) →
      -- no `c p` is a port of `T`,
      (∀ p ∈ T, ∀ q ∈ T, c p ≠ q) →
      -- `f` sends `c p` to `p`,
      (∀ p ∈ T, f (c p) = p) →
      -- `f` fixes every port of `T`,
      (∀ p ∈ T, f p = p) →
      -- and `f` fixes every other name of `N`,
      (∀ y ∈ N.vars, (∀ p ∈ T, y ≠ c p) → f y = y) →
      -- then the net with the equations is the same graph as `N` renamed by `f`
      Equiv (N + T.val.map (fun p => s(var (c p), var p))) (N.bind fun y => var (f y)) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro N _ _ _ _ _ _ hfix
    simp only [Finset.empty_val, Multiset.map_zero, add_zero]
    rw [Net.bind_var_of_fix fun y hy => hfix y hy fun p hp => absurd hp (Finset.notMem_empty p)]
    exact Equiv.refl N
  | insert p T hpT ih =>
    intro N hlin hinj hcN hcp hfc hfp hfix
    have hT : ∀ q ∈ T, q ∈ insert p T := fun q hq => Finset.mem_insert_of_mem hq
    have hpp : p ∈ insert p T := Finset.mem_insert_self p T
    set E := T.val.map (fun p => s(var (c p), var p)) with hE
    have hsplit : N + (insert p T).val.map (fun p => s(var (c p), var p)) =
        s(var (c p), var p) ::ₘ (N + E) := by
      rw [Finset.insert_val_of_notMem hpT, Multiset.map_cons, Multiset.add_cons]
    -- `c p` does not occur in the other equations
    have hcE : c p ∉ Net.vars E := by
      intro hm
      simp only [hE, Net.vars, Multiset.mem_bind, Multiset.mem_map] at hm
      obtain ⟨_, ⟨q, hq, rfl⟩, hm⟩ := hm
      simp only [eqVars_mk, Term.vars_var, Multiset.mem_add, Multiset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hpT (hinj hpp (hT q hq) hm ▸ hq)
      · exact hcp p hpp q (hT q hq) hm
    have hlin' : Net.Linear (s(var (c p), var p) ::ₘ (N + E)) := hlin.cast hsplit
    have hcNE : c p ∈ Net.vars (N + E) := by
      rw [Net.vars_add]; exact Multiset.mem_add.2 (Or.inl (hcN p hpp))
    have hw := Net.wire_var hlin' hcNE
    set g : ν → Term S ν := fun y => if y = c p then var p else var y with hg
    have hEfix : Net.bind g E = E := by
      rw [Net.bind_congr (g := var) fun y hy => by
        have : y ≠ c p := fun h => hcE (h ▸ hy)
        simp [hg, this]]
      exact Net.bind_var_self E
    have hNE : Net.bind g (N + E) = Net.bind g N + E := by
      simp only [Net.bind, Multiset.map_add] at hEfix ⊢
      rw [hEfix]
    rw [hNE] at hw
    have hvars : ∀ y ∈ (N.bind g).vars, y = p ∨ (y ∈ N.vars ∧ y ≠ c p) := by
      intro y hy
      rw [Net.vars_bind] at hy
      obtain ⟨z, hz, hy⟩ := Multiset.mem_bind.1 hy
      by_cases hzc : z = c p
      · simp only [hg, hzc, ite_true, Term.vars_var, Multiset.mem_singleton] at hy
        exact Or.inl hy
      · simp only [hg, hzc, ite_false, Term.vars_var, Multiset.mem_singleton] at hy
        subst hy
        exact Or.inr ⟨hz, hzc⟩
    have ih' := ih (N.bind g) (hw.linear_right) (hinj.mono fun q hq => hT q hq)
      (fun q hq => by
        rw [Net.vars_bind]
        refine Multiset.mem_bind.2 ⟨c q, hcN q (hT q hq), ?_⟩
        have hne : c q ≠ c p := fun h => hpT (hinj (hT q hq) hpp h ▸ hq)
        simp [hg, hne])
      (fun q hq q' hq' => hcp q (hT q hq) q' (hT q' hq'))
      (fun q hq => hfc q (hT q hq)) (fun q hq => hfp q (hT q hq))
      (fun y hy hyT => by
        rcases hvars y hy with rfl | ⟨hyN, hyc⟩
        · exact hfp y hpp
        · refine hfix y hyN fun q hq => ?_
          rcases Finset.mem_insert.1 hq with rfl | hq
          · exact hyc
          · exact hyT q hq)
    have hfin : (N.bind g).bind (fun y => var (f y)) = N.bind fun y => var (f y) := by
      rw [Net.bind_bind]
      refine Net.bind_congr fun y _ => ?_
      by_cases hy : y = c p
      · simp [hg, hy, hfp p hpp, hfc p hpp]
      · simp [hg, hy]
    rw [hsplit, ← hfin]
    exact hw.equiv.trans ih'

end Absorb

end INet
