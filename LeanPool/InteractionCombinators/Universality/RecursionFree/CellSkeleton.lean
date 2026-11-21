/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Menus.Menu
public import LeanPool.InteractionCombinators.Universality.Multiplexors.Transpositor
public import LeanPool.InteractionCombinators.Universality.Duplication.DupPackage
public import LeanPool.InteractionCombinators.Reduction.Commute

/-!
# Lafont, "Interaction Combinators" (1997): the cell `[αᵢ]` of Fig. 6, first stages of Fig. 7

Page 86 (PDF page 18), Section 2.4, restricted case.

Fig. 6 (left) translates a cell `αᵢ` of arity `nᵢ` into the transpositor `T_{1,1}` whose three
ports carry, from left to right, the menu `Γᵢ`, the selector `Sⁱ_m`, and a wire `ℓ`. The free
port of `Sⁱ_m` is the root of the multiplexor `M_{nᵢ+1}`, whose auxiliary ports are the `nᵢ`
auxiliary ports of the cell and then the same wire `ℓ` (the loop on the right of the figure).
Here the menu `Γ` is an arbitrary tree, and the trees `ts` are plugged into the auxiliary ports
of the cell.

The first two rows of Fig. 7: two such cells plugged by their roots. `T_{1,1}` against `T_{1,1}`
exchanges the first two ports, so `Γⱼ` meets `Sⁱ_m` and `Γᵢ` meets `Sʲ_m`, and the two loops are
joined. Each selector then extracts one package of the other menu.

Indices are counted from 0, as in `selector`.

Contents, in the order of the file:

1. Definitions: `cellSel`, the selector `Sⁱ_m` with a tree on its free port, and
   `selector_eq_cellSel`; `cellSkel`, the tree of Fig. 6, left.
2. Auxiliary lemmas on substitution: `subst_muxStar`, `subst_mux`, `subst_selector`,
   `vars_cellSel`, `map_subst_of_notMem`.
3. Auxiliary lemmas on wires: `equiv_cellSel` (a new wire on the free port of a selector),
   `equiv_contract` (two wires in a row are one wire), `equiv_loop` (joining two loops).
4. Main result: `cellSkel_cellSkel`, the first stages of Fig. 7.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- The selector `Sⁱ_m` of page 84 with the tree `t` plugged into its free port (Fig. 6, page 86,
where `t` is the multiplexor `M_{nᵢ+1}`). -/
def cellSel
    -- the length of the menu and the index of the package to select
    (m i : ℕ)
    -- the tree on the free port
    (t : Term sig ℕ) :
    Term sig ℕ :=
  muxStar (List.replicate i mkEra ++ t :: List.replicate (m - i - 1) mkEra)

/-- The selector `Sⁱ_m` with free port `x` is `cellSel` on the wire `x` (page 86). -/
theorem selector_eq_cellSel
    -- the length of the menu, the index, and the free port
    (m i x : ℕ) :
    (selector m i x : Term sig ℕ) = cellSel m i (var x) :=
  rfl

/-- The cell `[αᵢ]` of Fig. 6 (left, page 86), with the trees `ts` plugged into its auxiliary
ports: the transpositor `T_{1,1}` carrying, from left to right, the menu `Γ`, the selector `Sⁱ_m`
whose free port is the root of `M_{nᵢ+1}`, and the wire `ℓ`. The auxiliary ports of `M_{nᵢ+1}` are
`ts` and then the same wire `ℓ`, so `ℓ` is the internal loop of the cell. -/
def cellSkel
    -- the menu
    (Γ : Term sig ℕ)
    -- the length of the menu and the index of the cell
    (m i : ℕ)
    -- the trees plugged into the auxiliary ports of the cell
    (ts : List (Term sig ℕ))
    -- the name of the internal loop
    (ℓ : ℕ) :
    Term sig ℕ :=
  transpositor 1 [Γ, cellSel m i (mux (ts ++ [var ℓ])), var ℓ]

-- ============================================================================================
-- 2. Auxiliary lemmas: substitution
-- ============================================================================================

/-- Substitution goes through the dual multiplexor `M_n*`. -/
theorem subst_muxStar
    -- plugging the tree `t` into the name `x`
    (x : ℕ)
    (t : Term sig ℕ) :
    -- for every list of trees on the auxiliary ports
    ∀ (us : List (Term sig ℕ)),
      (muxStar us).subst x t = muxStar (us.map (·.subst x t))
  | [] => by apply subst_of_notMem; simp [muxStar]
  | [_] => rfl
  | u :: u' :: us => by
    rw [muxStar, subst_mkCon, subst_muxStar x t (u' :: us)]
    rfl

/-- Substitution goes through the multiplexor `M_n`. -/
theorem subst_mux
    -- plugging the tree `t` into the name `x`
    (x : ℕ)
    (t : Term sig ℕ) :
    -- for every list of trees on the auxiliary ports
    ∀ (us : List (Term sig ℕ)),
      (mux us).subst x t = mux (us.map (·.subst x t))
  | [] => by apply subst_of_notMem; simp [mux]
  | [_] => rfl
  | u :: u' :: us => by
    rw [mux, subst_mkCon, subst_mux x t (u' :: us)]
    rfl

/-- Plugging `t` into the free port `x` of `Sⁱ_m` gives `cellSel m i t` (page 86). -/
theorem subst_selector
    -- the selector `Sⁱ_m` with free port `x`
    (m i x : ℕ)
    -- the tree plugged into `x`
    (t : Term sig ℕ) :
    (selector m i x).subst x t = cellSel m i t := by
  rw [selector, subst_muxStar, cellSel]
  congr 1
  have he : (mkEra : Term sig ℕ).subst x t = mkEra := subst_of_notMem (by simp [vars_mkEra])
  simp [List.map_replicate, he, subst_var_self]

/-- The names of `cellSel m i t` are those of `t`: the other ports of the selector carry erasers. -/
theorem vars_cellSel
    -- the selector `Sⁱ_m` with the tree `t` on its free port
    (m i : ℕ)
    (t : Term sig ℕ) :
    (cellSel m i t).vars = t.vars := by
  simp [cellSel, vars_muxStar, vars_mkEra, List.map_replicate]

/-- A list of trees none of which contains `x` is unchanged by plugging a tree into `x`. -/
theorem map_subst_of_notMem
    -- plugging the tree `t` into the name `x`
    (x : ℕ)
    (t : Term sig ℕ) :
    -- for every list of trees in which `x` does not occur
    ∀ (us : List (Term sig ℕ)),
      x ∉ (us.map Term.vars).sum →
      -- the substitution leaves the list unchanged
      us.map (·.subst x t) = us
  | [], _ => rfl
  | u :: us, h => by
    simp only [List.map_cons, List.sum_cons, Multiset.mem_add, not_or] at h
    rw [List.map_cons, subst_of_notMem h.1, map_subst_of_notMem x t us h.2]

-- ============================================================================================
-- 3. Auxiliary lemmas: wires
-- ============================================================================================

/-- Expanding the free port of a selector into a new wire `x` (page 86): `Γ` against `Sⁱ_m` with
the tree `t` on its free port is the same graph as `Γ` against `Sⁱ_m` with free port `x`, plus the
equation `x = t`, when `x` is unused. -/
theorem equiv_cellSel
    -- the tree `G` against the selector `Sⁱ_m` with the tree `t` on its free port
    (G t : Term sig ℕ)
    (m i : ℕ)
    -- the new wire
    (x : ℕ)
    -- the rest of the net
    (R : CNet)
    -- the net is linear, and `x` does not occur in it
    (hlin : Net.Linear (s(G, cellSel m i t) ::ₘ R))
    (hx : x ∉ Net.vars (s(G, cellSel m i t) ::ₘ R)) :
    -- the same graph as `G` against `Sⁱ_m` with free port `x`, and the equation `x = t`
    Equiv (s(G, cellSel m i t) ::ₘ R) (s(G, selector m i x) ::ₘ s(var x, t) ::ₘ R) := by
  have hxG : x ∉ G.vars := fun h => hx (by simp [h])
  have L : Net.Linear (s(var x, t) ::ₘ s(G, selector m i x) ::ₘ R) := by
    refine hlin.add_fresh {x} (Multiset.nodup_singleton x) (by simpa using hx) ?_
    simp only [Net.vars_cons, eqVars_mk, vars_var, selector_eq_cellSel, vars_cellSel]
    ms
  have W := Wire.mk x t G (selector m i x) R L (by simp [selector_eq_cellSel, vars_cellSel])
  rw [subst_of_notMem hxG, subst_selector] at W
  exact W.equiv.symm.trans (Equiv.of_eq (Multiset.cons_swap _ _ _))

/-- An equation `P = x` followed by `x = t` is the equation `P = t` (a wire, page 70). -/
theorem equiv_contract
    -- the two equations `P = x` and `x = t`
    (P t : Term sig ℕ)
    (x : ℕ)
    -- the rest of the net
    (R : CNet)
    -- the net is linear
    (hlin : Net.Linear (s(P, var x) ::ₘ s(var x, t) ::ₘ R)) :
    -- the same graph as the equation `P = t`
    Equiv (s(P, var x) ::ₘ s(var x, t) ::ₘ R) (s(P, t) ::ₘ R) := by
  have hc := hlin x
  simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hc
  have ht : x ∉ t.vars := Multiset.count_eq_zero.1 (by omega)
  have L : Net.Linear (s(var x, P) ::ₘ s(var x, t) ::ₘ R) :=
    hlin.cast (by rw [Sym2.eq_swap (a := P)])
  have W := Wire.mk x P (var x) t R L (by simp)
  rw [subst_var_self, subst_of_notMem ht] at W
  exact (Equiv.of_eq (by rw [Sym2.eq_swap (a := P)])).trans W.equiv

/-- Joining two loops (Fig. 7, page 86): the equation `ℓ = ℓ'` with `ℓ'` the last auxiliary port
of `M_{n+1}` is `M_{n+1}` with `ℓ` on that port. -/
theorem equiv_loop
    -- the multiplexor `M_{n+1}` with leaves `us` and `ℓ'`, against the tree `Q`
    (us : List (Term sig ℕ))
    (Q : Term sig ℕ)
    -- the two loops
    (ℓ ℓ' : ℕ)
    -- the rest of the net
    (R : CNet)
    -- the net with the equation `ℓ = ℓ'` is linear
    (hlin : Net.Linear (s(var ℓ, var ℓ') ::ₘ s(mux (us ++ [var ℓ']), Q) ::ₘ R)) :
    -- the same graph as `M_{n+1}` with `ℓ` on its last auxiliary port
    Equiv (s(var ℓ, var ℓ') ::ₘ s(mux (us ++ [var ℓ']), Q) ::ₘ R)
      (s(mux (us ++ [var ℓ]), Q) ::ₘ R) := by
  have hc := hlin ℓ'
  simp only [Net.vars_cons, eqVars_mk, vars_var, vars_mux, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Multiset.count_add,
    Multiset.count_singleton_self] at hc
  have hus : ℓ' ∉ (us.map Term.vars).sum := Multiset.count_eq_zero.1 (by omega)
  have hQ : ℓ' ∉ Q.vars := Multiset.count_eq_zero.1 (by omega)
  have L : Net.Linear (s(var ℓ', var ℓ) ::ₘ s(mux (us ++ [var ℓ']), Q) ::ₘ R) :=
    hlin.cast (by rw [Sym2.eq_swap (a := var ℓ)])
  have W := Wire.mk ℓ' (var ℓ) (mux (us ++ [var ℓ'])) Q R L
    (by simp [vars_mux])
  rw [subst_of_notMem hQ, subst_mux, List.map_append, map_subst_of_notMem _ _ us hus,
    List.map_cons, List.map_nil, subst_var_self] at W
  exact (Equiv.of_eq (by rw [Sym2.eq_swap (a := var ℓ)])).trans W.equiv

-- ============================================================================================
-- 4. Main result: the first stages of Fig. 7
-- ============================================================================================

/-- The first two rows of Fig. 7 (page 86). Two cells `[αᵢ]` and `[αⱼ]` of Fig. 6, with menus of
packages `Gi`, `Gj` of length `m`, indices `i, j < m`, trees `ts`, `us` on their auxiliary ports and
loops `ℓ`, `ℓ'`, plugged by their roots in a context `Δ`, reduce up to wires to `M_{nᵢ+1}` (leaves
`ts`, `ℓ`) against the package `Gj[i]` and `M_{nⱼ+1}` (leaves `us`, `ℓ`) against `Gi[j]`: the two
loops are joined into the single wire `ℓ`.

The transpositors meet first (`transpositor_transpositor`, `p = 1`): `Γⱼ` meets `Sⁱ_m` and `Γᵢ`
meets `Sʲ_m`. Each selector, its free port joined to the multiplexor by a new wire, then extracts
one package of the other menu (`menu_selector`). The new wires are taken above every name of the
net, so no freshness hypothesis is needed. -/
theorem cellSkel_cellSkel
    -- the two menus, both of length `m`, and the indices `i, j < m` of the two cells
    (Gi Gj : List (Term sig ℕ))
    (m : ℕ)
    (i j : ℕ)
    (hGi : Gi.length = m)
    (hGj : Gj.length = m)
    (hi : i < m)
    (hj : j < m)
    -- the menus are made of packages
    (hpi : ∀ π ∈ Gi, π.IsPackage)
    (hpj : ∀ π ∈ Gj, π.IsPackage)
    -- the trees on the auxiliary ports of the two cells, and their loops
    (ts us : List (Term sig ℕ))
    (ℓ ℓ' : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the two cells plugged by their roots, and `Δ`
    (hlin : Net.Linear (s(cellSkel (menu Gi) m i ts ℓ, cellSkel (menu Gj) m j us ℓ') ::ₘ Δ)) :
    -- there is a net `M` such that
    ∃ M,
      -- the two cells reduce, up to wires, to `M`,
      StepsE system (s(cellSkel (menu Gi) m i ts ℓ, cellSkel (menu Gj) m j us ℓ') ::ₘ Δ) M ∧
      -- and `M` is the same graph as: `M_{nᵢ+1}` (leaves `ts`, `ℓ`) against `Gj[i]`,
      -- `M_{nⱼ+1}` (leaves `us`, `ℓ`) against `Gi[j]`, and `Δ`
      Equiv M
        (s(mux (ts ++ [var ℓ]), Gj[i]'(hGj ▸ hi))
          ::ₘ s(mux (us ++ [var ℓ]), Gi[j]'(hGi ▸ hj))
          ::ₘ Δ) := by
  subst hGi
  set T := mux (ts ++ [var ℓ]) with hT
  set U := mux (us ++ [var ℓ']) with hU
  -- the transpositors meet (page 83)
  have h1 := transpositor_transpositor 1 [menu Gi, cellSel Gi.length i T, var ℓ]
    [menu Gj, cellSel Gi.length j U, var ℓ'] Δ rfl
  set N1 : CNet := s(menu Gj, cellSel Gi.length i T) ::ₘ
    (s(menu Gi, cellSel Gi.length j U) ::ₘ s(var ℓ, var ℓ') ::ₘ Δ) with hN1
  have h1' : Red (s(cellSkel (menu Gi) Gi.length i ts ℓ, cellSkel (menu Gj) Gi.length j us ℓ')
      ::ₘ Δ) N1 := by
    refine h1.cast rfl ?_
    simp only [swapPairs, List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_add, zero_add, hN1]
    rw [Sym2.eq_swap (a := cellSel _ i T), Multiset.cons_swap]
  have L1 : N1.Linear := h1'.linear system_wellFormed.linear hlin
  -- two new wires above every name
  obtain ⟨K, hK⟩ := Net.exists_below N1
  have hKN1 : K ∉ N1.vars := hK.notMem le_rfl
  -- expand the free port of `Sⁱ_m` into the wire `K`
  have E1 := equiv_cellSel (menu Gj) T Gi.length i K _ L1 hKN1
  set N1a : CNet := s(menu Gi, cellSel Gi.length j U) ::ₘ
    (s(menu Gj, selector Gi.length i K) ::ₘ s(var K, T) ::ₘ s(var ℓ, var ℓ') ::ₘ Δ) with hN1a
  have E1' : Equiv N1 N1a := E1.trans (Equiv.of_eq (by rw [hN1a]; ms))
  have L1a : N1a.Linear := E1'.linear L1
  have hb1a : N1a.Below (K + 1) := by
    rw [hN1] at hK
    simp only [Net.below_cons] at hK
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hK
    have hT' : T.Below K := fun x hx => h2 x (by rw [vars_cellSel]; exact hx)
    simp only [hN1a, Net.below_cons, below_var]
    simp only [below_var] at h5 h6
    refine ⟨h3.mono (by omega), h4.mono (by omega), h1.mono (by omega), ?_, by omega,
      hT'.mono (by omega), by omega, by omega, h7.mono (by omega)⟩
    intro x hx
    rw [selector_eq_cellSel, vars_cellSel, vars_var, Multiset.mem_singleton] at hx
    omega
  -- expand the free port of `Sʲ_m` into the wire `K + 1`
  have E2 := equiv_cellSel (menu Gi) U Gi.length j (K + 1) _ L1a (hb1a.notMem le_rfl)
  set N1b : CNet := s(menu Gi, selector Gi.length j (K + 1)) ::ₘ s(var (K + 1), U) ::ₘ
    (s(menu Gj, selector Gi.length i K) ::ₘ s(var K, T) ::ₘ s(var ℓ, var ℓ') ::ₘ Δ) with hN1b
  have L1b : N1b.Linear := E2.linear L1a
  -- the selector `Sʲ_m` takes the package `Gi[j]`
  have S1 := menu_selector Gi j hj (K + 1) hpi _ L1b
  set N2 : CNet := s(menu Gj, selector Gj.length i K) ::ₘ
    (s(Gi[j], var (K + 1)) ::ₘ s(var (K + 1), U) ::ₘ s(var K, T) ::ₘ s(var ℓ, var ℓ') ::ₘ Δ)
    with hN2
  have S1' : StepsE system N1b N2 := by
    convert S1 using 1
    rw [hN2, hGj]
    ms
  have L2 : N2.Linear := S1'.linear system_wellFormed.linear L1b
  -- the selector `Sⁱ_m` takes the package `Gj[i]`
  have S2 := menu_selector Gj i (hGj ▸ hi) K hpj _ L2
  set N3 : CNet := s(Gj[i]'(hGj ▸ hi), var K) ::ₘ s(var K, T) ::ₘ
    (s(Gi[j], var (K + 1)) ::ₘ s(var (K + 1), U) ::ₘ s(var ℓ, var ℓ') ::ₘ Δ) with hN3
  have S2' : StepsE system N2 N3 := by
    convert S2 using 1
    rw [hN3]
    ms
  have L3 : N3.Linear := S2'.linear system_wellFormed.linear L2
  -- remove the two new wires and join the loops
  have E3 := equiv_contract (Gj[i]'(hGj ▸ hi)) T K _ L3
  set N4 : CNet := s(Gi[j], var (K + 1)) ::ₘ s(var (K + 1), U) ::ₘ
    (s(Gj[i]'(hGj ▸ hi), T) ::ₘ s(var ℓ, var ℓ') ::ₘ Δ) with hN4
  have E3' : Equiv N3 N4 := E3.trans (Equiv.of_eq (by rw [hN4]; ms))
  have L4 : N4.Linear := E3'.linear L3
  have E4 := equiv_contract (Gi[j]) U (K + 1) _ L4
  set N5 : CNet := s(var ℓ, var ℓ') ::ₘ s(U, Gi[j]) ::ₘ (s(Gj[i]'(hGj ▸ hi), T) ::ₘ Δ) with hN5
  have E4' : Equiv N4 N5 := E4.trans (Equiv.of_eq (by rw [hN5, Sym2.eq_swap (a := Gi[j])]; ms))
  have L5 : N5.Linear := E4'.linear L4
  have E5 := equiv_loop us (Gi[j]) ℓ ℓ' _ L5
  obtain ⟨M, hS, hE⟩ := stepsE_of_equiv (E1'.trans E2) (S1'.trans S2')
  refine ⟨M, h1'.stepsE.trans hS, hE.trans (E3'.trans (E4'.trans (E5.trans
    (Equiv.of_eq ?_))))⟩
  rw [Sym2.eq_swap (a := Gj[i]'(hGj ▸ hi))]
  ms

end INet.Comb
