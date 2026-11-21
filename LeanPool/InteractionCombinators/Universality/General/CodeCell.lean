/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Codes.DecodeCopyChain
public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFreeFig7

/-!
# The cell `⟨α_k⟩` of Fig. 10 and the extraction of page 90

Lafont 1997, Section 2.7, Fig. 10 (journal page 89, PDF page 21) and the text of page 90.

**`[αᵢ]` needs no new definition.** The cell `[αᵢ]` of Fig. 10 (top left) is the cell of Fig. 6
with one more leaf on its multiplexor: `T_{1,1}` carries the menu `Γᵢ`, the selector `Sⁱ_m` on the
root of `M_{nᵢ+2}`, and the loop `ℓ`; the leaves of `M_{nᵢ+2}` are the code `!Γ`, the `nᵢ` auxiliary
ports and the loop. This is `cellSkel Γᵢ m i (code K Γ :: ts) ℓ` (`CellSkeleton.lean`).

**`⟨α_k⟩`** (Fig. 10, bottom left) has one more port than `α_k`, at its top left: the root of a
copier `C_2`. The left auxiliary port of `C_2` goes into the decoder `D`, whose free port is plugged
into the root of a selector `S^k_m`; the free port of that selector is the first port of `T_{1,1}`.
The right auxiliary port of `C_2` is the first leaf of `M_{n_k+2}`. The rest is as in `[α_k]`.

The figure joins two auxiliary ports twice (the free port of the left `S^k_m` to the first port of
`T_{1,1}`, and the right auxiliary port of `C_2` to the first leaf of `M_{n_k+2}`), so `⟨α_k⟩`
is a net of three equations (`codeCell`). Internal wires `y` and `u` make these two connections.
The remaining internal wire `w` connects `D` to `S^k_m`.

Contents, in the order of the file:

1. Definition: `codeCell`, the cell `⟨α_k⟩`, with trees `P` on its principal port and `x` on its
   extra port.
2. Auxiliary lemmas: `subst_cellSkel` (plugging a tree into a wire of `[αᵢ]`), `vars_cellSkel`
   (the names of `[αᵢ]`), `vars_le_sum_of_mem`.
3. Main result: `codeCell_code`, page 90: a copy of `!Γ` on the extra port of `⟨α_k⟩` reduces to
   `[α_k]`.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- **The cell `⟨α_k⟩` of Fig. 10** (bottom left, page 89), with the tree `P` on its principal port
(the root of `T_{1,1}`), the tree `x` on its extra port (the root of `C_2`), and the trees `ts` on
its `n_k` auxiliary ports. It is the net of three equations

* `x = C_2(D, u)`: the copier `C_2` whose left auxiliary port carries the decoder `D` (free port
  `w`, loop `k₀, k₀ + 1`) and whose right auxiliary port is the wire `u`;
* `w = S^k_m(y)`: the free port of `D` against the root of the selector `S^k_m`, whose free port is
  the wire `y`;
* `P = T_{1,1}(y, S^k_m(M_{n_k+2}(u, ts, ℓ)), ℓ)`: the cell `[α_k]` with the wire `y` in place of
  the menu and the wire `u` in place of the code, `cellSkel (var y) m k (var u :: ts) ℓ`.

The internal wires are `u`, `w`, `y`, the loop `ℓ`, and the loop `k₀, k₀ + 1` of the decoder. -/
def codeCell
    -- the number `m` of symbols and the index `k` of the symbol `α_k`
    (m k : ℕ)
    -- the trees on the principal port and on the extra port
    (P x : Term sig ℕ)
    -- the trees on the `n_k` auxiliary ports
    (ts : List (Term sig ℕ))
    -- the internal wires: the loop `ℓ`, the wires `u`, `w`, `y`, and the loop `k₀, k₀ + 1` of `D`
    (ℓ u w y k₀ : ℕ) :
    CNet :=
  s(x, copier [decoder w k₀, var u]) ::ₘ s(var w, selector m k y) ::ₘ
    s(P, cellSkel (var y) m k (var u :: ts) ℓ) ::ₘ 0

-- ============================================================================================
-- 2. Auxiliary lemmas: names and substitution in the cell `[αᵢ]`
-- ============================================================================================

/-- Plugging the tree `t` into a wire `x` of the cell `[αᵢ]` of Fig. 6 (page 86) other than its
loop plugs it into the menu and the trees of the auxiliary ports. -/
theorem subst_cellSkel
    -- the cell `[αᵢ]`: menu `Γ`, `m` symbols, index `i`, auxiliary trees `ts`, loop `ℓ`
    (Γ : Term sig ℕ)
    (m i : ℕ)
    (ts : List (Term sig ℕ))
    (ℓ : ℕ)
    -- the wire `x`, other than the loop, and the tree `t` plugged into it
    (x : ℕ)
    (t : Term sig ℕ)
    (hx : x ≠ ℓ) :
    (cellSkel Γ m i ts ℓ).subst x t =
      cellSkel (Γ.subst x t) m i (ts.map (·.subst x t)) ℓ := by
  have hℓ : (var ℓ : Term sig ℕ).subst x t = var ℓ := subst_of_notMem (by simp [hx])
  simp only [Term.subst] at hℓ ⊢
  simp [cellSkel, bind_transpositor, bind_cellSel, bind_mux, hℓ]

/-- The names of the cell `[αᵢ]` of Fig. 6 (page 86): those of the menu, of the trees on the
auxiliary ports, and the loop `ℓ` twice. -/
theorem vars_cellSkel
    -- the cell `[αᵢ]`: menu `Γ`, `m` symbols, index `i`, auxiliary trees `ts`, loop `ℓ`
    (Γ : Term sig ℕ)
    (m i : ℕ)
    (ts : List (Term sig ℕ))
    (ℓ : ℕ) :
    (cellSkel Γ m i ts ℓ).vars = Γ.vars + (ts.map Term.vars).sum + {ℓ} + {ℓ} := by
  simp only [cellSkel, vars_transpositor, vars_cellSel, vars_mux, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, List.map_append, List.sum_append, vars_var]
  abel

/-- The names of a tree of a list are among the names of the list. -/
theorem vars_le_sum_of_mem
    -- the tree
    {ρ : Term sig ℕ} :
    -- if `ρ` belongs to the list `ts`, its names are among those of `ts`
    ∀ {ts : List (Term sig ℕ)}, ρ ∈ ts → ρ.vars ≤ (ts.map Term.vars).sum
  | t :: ts, h => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Multiset.le_add_right _ _
    · exact (vars_le_sum_of_mem h).trans (Multiset.le_add_left _ _)

-- ============================================================================================
-- 3. Main result: the extraction of page 90
-- ============================================================================================

/-- **The extraction of page 90.** Let `Γ = Γ₁ & ⋯ & Γ_m` be a menu of packages that is itself a
package, with names below `K`, and `k < m`. A copy of the code `!Γ` (renamed by `f`, injective on
the names of the code, as `copier_code` leaves it) plugged into the extra port of `⟨α_k⟩` (Fig. 10,
page 89), in any context `Δ`, reduces to a net that is `Equiv` to the cell `[α_k]` of Fig. 10:
`cellSkel Γ_k m k (!Γ :: ts) ℓ`, where the menu entry `Γ_k` and the code `!Γ` are copies, renamed
by some `g` and `g'` injective on the names of the code.

`C_2` and `D` act first (`copier_decoder_copy`): `Γ` renamed by `g` comes out of `D`, and a copy of
`!Γ` renamed by `g'` comes out of the right port of `C_2`. Then `S^k_m` extracts `Γ_k` from the
decoded menu (`menu_selector`), and the two wires `y` and `u` are plugged into `T_{1,1}` and
`M_{n_k+2}`. -/
theorem codeCell_code
    -- the menu `Γ = Γ₁ & ⋯ & Γ_m`: its entries are packages, and so is the menu
    (Γs : List (Term sig ℕ))
    (hp : ∀ π ∈ Γs, π.IsPackage)
    (hΓ : (menu Γs).IsPackage)
    -- a bound `K` on the names of the menu
    (K : ℕ)
    (hb : (menu Γs).Below K)
    -- the index `k` of the symbol
    (k : ℕ)
    (hk : k < Γs.length)
    -- the renaming of the copy of `!Γ`, injective on the names of the code
    (f : ℕ → ℕ)
    (hf : Set.InjOn f {x | x ∈ (code K (menu Γs)).vars})
    -- the tree on the principal port and the trees on the auxiliary ports of `⟨α_k⟩`
    (P : Term sig ℕ)
    (ts : List (Term sig ℕ))
    -- the internal wires of `⟨α_k⟩`
    (ℓ u w y k₀ : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: `⟨α_k⟩` with the copy of `!Γ` on its extra port, and `Δ`
    (hlin : Net.Linear (codeCell Γs.length k P ((code K (menu Γs)).bind fun x => var (f x)) ts
      ℓ u w y k₀ + Δ)) :
    -- there are two renamings `g`, `g'` and a net `M` such that
    ∃ (g g' : ℕ → ℕ) (M : CNet),
      -- `g` is injective on the names of the code,
      Set.InjOn g {x | x ∈ (code K (menu Γs)).vars} ∧
      -- `g'` is injective on the names of the code,
      Set.InjOn g' {x | x ∈ (code K (menu Γs)).vars} ∧
      -- the net reduces, up to wires, to `M`,
      StepsE system (codeCell Γs.length k P ((code K (menu Γs)).bind fun x => var (f x)) ts
        ℓ u w y k₀ + Δ) M ∧
      -- and `M` is the same graph as `[α_k]` with menu `Γ_k` renamed by `g` and code `!Γ`
      -- renamed by `g'` on its first leaf, `P` on its principal port; and `Δ`
      Equiv M (s(P, cellSkel (Γs[k].bind fun x => var (g x)) Γs.length k
        (((code K (menu Γs)).bind fun x => var (g' x)) :: ts) ℓ) ::ₘ Δ) := by
  set C := code K (menu Γs) with hC
  set S := (selector Γs.length k y : Term sig ℕ) with hSdef
  set Q := cellSkel (var y) Γs.length k (var u :: ts) ℓ with hQ
  have e0 : codeCell Γs.length k P (C.bind fun x => var (f x)) ts ℓ u w y k₀ + Δ =
      s(copier [decoder w k₀, var u], C.bind fun x => var (f x)) ::ₘ
        (s(var w, S) ::ₘ s(P, Q) ::ₘ Δ) := by
    rw [codeCell, Sym2.eq_swap (a := C.bind _)]
    simp only [Multiset.cons_add, zero_add]
    rfl
  rw [e0] at hlin ⊢
  obtain ⟨g, g', M, hg, hg', hS, hE⟩ :=
    copier_decoder_copy (menu Γs) hΓ K hb f hf w k₀ (var u) _ hlin
  refine ⟨g, g', ?_⟩
  have L1 := hE.linear (hS.linear system_wellFormed.linear hlin)
  set A := (menu Γs).bind fun x => var (g x) with hA
  set B := C.bind fun x => var (g' x) with hB
  -- the wire `w` from `D` to `S^k_m`
  set R : CNet := s(var u, B) ::ₘ s(P, Q) ::ₘ Δ with hR
  have e1 : s(var w, A) ::ₘ s(var u, B) ::ₘ s(var w, S) ::ₘ s(P, Q) ::ₘ Δ =
      s(S, var w) ::ₘ s(var w, A) ::ₘ R := by
    rw [hR, Sym2.eq_swap (a := S)]
    ms
  have E1 := equiv_contract S A w R (L1.cast e1)
  -- the selector `S^k_m` extracts the package `Γ_k`
  set Gs := Γs.map fun π => π.bind fun x => var (g x) with hGs
  have hlen : Gs.length = Γs.length := List.length_map _
  have e2 : s(S, A) ::ₘ R = s(menu Gs, selector Gs.length k y) ::ₘ R := by
    rw [hlen, hA, menu, bind_var_mux, ← menu, Sym2.eq_swap]
  have L2 : Net.Linear (s(menu Gs, selector Gs.length k y) ::ₘ R) :=
    (E1.linear (L1.cast e1)).cast e2
  have hpG : ∀ π ∈ Gs, π.IsPackage := by
    intro π hπ
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hπ
    refine IsPackage.bind_var (hp ρ hρ) g (hg.mono fun x hx => ?_)
    change x ∈ (code K (menu Γs)).vars
    rw [vars_code]
    refine Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl ?_)))
    rw [menu, vars_mux]
    exact Multiset.mem_of_le (vars_le_sum_of_mem hρ) hx
  have S2 := menu_selector Gs k (hlen ▸ hk) y hpG R L2
  have hGk : ∀ h, Gs[k]'h = Γs[k].bind fun x => var (g x) := fun h => List.getElem_map _
  rw [hGk] at S2
  set Ak := Γs[k].bind fun x => var (g x) with hAk
  set N3 : CNet := s(var y, Ak) ::ₘ s(P, Q) ::ₘ s(var u, B) ::ₘ Δ with hN3
  have e3 : s(Ak, var y) ::ₘ R = N3 := by
    rw [hR, hN3, Sym2.eq_swap (a := Ak)]
    ms
  rw [e3] at S2
  have L3 : N3.Linear := S2.linear system_wellFormed.linear L2
  -- the wire `y` into the first port of `T_{1,1}`
  have hcy := L3 y
  simp only [hN3, hQ, Net.vars_cons, eqVars_mk, vars_var, vars_cellSkel, List.map_cons,
    List.sum_cons, Multiset.count_add, Multiset.count_singleton_self,
    Multiset.count_singleton] at hcy
  have hyAk : y ∉ Ak.vars := Multiset.count_eq_zero.1 (by omega)
  have hyP : y ∉ P.vars := Multiset.count_eq_zero.1 (by omega)
  have hyts : y ∉ (ts.map Term.vars).sum := Multiset.count_eq_zero.1 (by omega)
  have hyu : y ≠ u := by intro h; subst h; simp at hcy; omega
  have hyℓ : y ≠ ℓ := by intro h; subst h; simp at hcy; omega
  have W3 := Wire.mk y Ak P Q (s(var u, B) ::ₘ Δ) L3
    (Multiset.mem_add.2 (Or.inr (by rw [hQ, vars_cellSkel]; simp)))
  set Q4 := cellSkel Ak Γs.length k (var u :: ts) ℓ with hQ4
  have hsQ : Q.subst y Ak = Q4 := by
    rw [hQ, subst_cellSkel _ _ _ _ _ _ _ hyℓ, subst_var_self, List.map_cons,
      map_subst_of_notMem _ _ ts hyts, subst_of_notMem (r := var u) (by simp [hyu])]
  rw [subst_of_notMem hyP, hsQ] at W3
  have L4 := W3.linear_right
  -- the wire `u` into the first leaf of `M_{n_k+2}`
  set N4 : CNet := s(var u, B) ::ₘ s(P, Q4) ::ₘ Δ with hN4
  have e4 : s(P, Q4) ::ₘ s(var u, B) ::ₘ Δ = N4 := by rw [hN4]; ms
  rw [e4] at L4
  have hcu := L4 u
  simp only [hN4, hQ4, Net.vars_cons, eqVars_mk, vars_var, vars_cellSkel, List.map_cons,
    List.sum_cons, Multiset.count_add, Multiset.count_singleton_self,
    Multiset.count_singleton] at hcu
  have huAk : u ∉ Ak.vars := Multiset.count_eq_zero.1 (by omega)
  have huP : u ∉ P.vars := Multiset.count_eq_zero.1 (by omega)
  have huts : u ∉ (ts.map Term.vars).sum := Multiset.count_eq_zero.1 (by omega)
  have huℓ : u ≠ ℓ := by intro h; subst h; simp at hcu; omega
  have W4 := Wire.mk u B P Q4 Δ L4
    (Multiset.mem_add.2 (Or.inr (by rw [hQ4, vars_cellSkel]; simp)))
  rw [subst_of_notMem huP, hQ4, subst_cellSkel _ _ _ _ _ _ _ huℓ, subst_of_notMem huAk,
    List.map_cons, subst_var_self, map_subst_of_notMem _ _ ts huts] at W4
  -- put the pieces together
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv (hE.trans ((Equiv.of_eq e1).trans
    (E1.trans (Equiv.of_eq e2)))) S2
  exact ⟨M', hg, hg', hS.trans hS', hE'.trans (W3.equiv.trans ((Equiv.of_eq e4).trans W4.equiv))⟩

end INet.Comb
