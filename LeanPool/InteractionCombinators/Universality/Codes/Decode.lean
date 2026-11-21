/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Codes.Code

/-!
# Lafont, "Interaction Combinators" (1997): the decoder extracts `π` from `!π`

Page 89, Fig. 9: "`!π` is a code for `π`, which can be extracted with the decoder `D`". The code
`!π` against the decoder reduces to `π` on the free port of the decoder.

The first stage (`code_decoder`, `Code.lean`) leaves `M_n` against a `dup` cell whose auxiliary
ports `a` (port 0), `b` (port 1) are joined to `M_n*` of the trees `l_i` and `M_n*` of the trees
`r_i`. The rest of
Fig. 9 is done here by induction on the list of cells (`decode_cells`), one cell at a time: the
`con` at the top of `M_n` meets the `dup`, the two `con` cells it leaves meet the tops of the two
`M_n*`, and what is left is the cell `x₀ = dup(l₀, r₀)` and the same configuration on the remaining
`n - 1` cells. This is Lemma 3 (i) on `M_n` (a `dup` copies `M_n`, leaving `x_i = dup(x_i', x_i'')`)
followed by `mux_muxStar` on each copy, with the interactions taken in a different order. For
`n = 0` the eraser `M_0` erases the `dup`, and the two erasers left meet the two `M_0*`.

Contents, in the order of the file:

1. Definition: `decodeNet`, the net left by the first stage of Fig. 9.
2. Auxiliary lemmas: `muxStar_cons_cons`, `mux_cons_cons` (`M_n*` and `M_n` unfolded once),
   `vars_decodeNet` (the names of `decodeNet`).
3. The rest of Fig. 9: `decode_cells`, by induction on the cells.
4. Main results: `code_decoder_tree`, Fig. 9 for any tree, with new names above the names of the
   net; `code_decoder_package`, Fig. 9 for a package.
-/

@[expose] public section

namespace INet.Comb

open Term Decomp

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- The net left by the first stage of Fig. 9 (page 89), on a list of cells
`cs = [(x_i, l_i, r_i)]`: `M_n` on the names `x_i` against a `dup` cell with auxiliary ports `a`,
`b`; `M_n*` of the trees `l_i` (auxiliary port 0 of the cells) on `a`; `M_n*` of the trees `r_i`
(auxiliary port 1) on `b`; and the rest `Δ`. -/
def decodeNet
    -- the cells `x_i = dup(l_i, r_i)`, as triples `(x_i, l_i, r_i)`
    (cs : List (ℕ × Term sig ℕ × Term sig ℕ))
    -- the names on the auxiliary ports 0 and 1 of the `dup` cell
    (a b : ℕ)
    -- the rest of the net
    (Δ : CNet) :
    CNet :=
  s(mux (cs.map fun c => var c.1), mkDup (var a) (var b)) ::ₘ
    s(muxStar (cs.map fun c => c.2.1), var a) ::ₘ
    s(muxStar (cs.map fun c => c.2.2), var b) ::ₘ Δ

-- ============================================================================================
-- 2. Auxiliary lemmas: unfolding the multiplexors, the names of `decodeNet`
-- ============================================================================================

/-- `M_n*` of a list with at least two elements, unfolded once. -/
theorem muxStar_cons_cons
    -- the first two trees and the others
    (u u' : Term sig ℕ)
    (us : List (Term sig ℕ)) :
    muxStar (u :: u' :: us) = mkCon (muxStar (u' :: us)) u := rfl

/-- `M_n` of a list with at least two elements, unfolded once. -/
theorem mux_cons_cons
    -- the first two trees and the others
    (t t' : Term sig ℕ)
    (ts : List (Term sig ℕ)) :
    mux (t :: t' :: ts) = mkCon t (mux (t' :: ts)) := rfl

/-- The names of the net left by the first stage of Fig. 9: the cut names (on `M_n`), the names of
the trees `l_i`, `r_i` (on the two `M_n*`), the two ends of `a` and of `b`, and the rest. -/
theorem vars_decodeNet
    -- the cells, and any tree `τ` (`ports` and `auxVars` do not depend on it)
    (cs : List (ℕ × Term sig ℕ × Term sig ℕ))
    (τ : Term sig ℕ)
    -- the names on the auxiliary ports of the `dup` cell
    (a b : ℕ)
    -- the rest of the net
    (Δ : CNet) :
    -- the cut names, the names of the trees of the cells, `a` and `b` twice each, and those of `Δ`
    Net.vars (decodeNet cs a b Δ)
      = (Decomp.mk τ cs 0).ports + (Decomp.mk τ cs 0).auxVars
        + ({a, a, b, b} : Multiset ℕ) + Net.vars Δ := by
  simp only [decodeNet, Net.vars_cons, eqVars_mk, vars_mkDup, vars_var, vars_mux, vars_muxStar,
    ports, auxVars, List.map_map]
  induction cs with
  | nil =>
    simp only [List.map_nil, List.sum_nil, Multiset.coe_nil, Multiset.insert_eq_cons,
      ← Multiset.singleton_add]
    ms
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp, vars_var, ← Multiset.cons_coe] at ih ⊢
    rw [← Multiset.singleton_add]
    have h := congrArg (({c.1} + c.2.1.vars + c.2.2.vars) + ·) ih
    refine Eq.trans ?_ (h.trans ?_) <;> abel

-- ============================================================================================
-- 3. The rest of Fig. 9, by induction on the cells
-- ============================================================================================

/-- The rest of Fig. 9 (page 89), by induction on the cells: `M_n` on the names `x_i`, against a
`dup` cell whose auxiliary port 0, `a`, is joined to `M_n*` of the trees `l_i` and whose auxiliary
port 1, `b`, to `M_n*` of the trees `r_i`, reduces to the `n` cells
`x_i = dup(l_i, r_i)`. The net must be linear and its names below `j`, the first new name. -/
theorem decode_cells :
    -- for the cells `(x_i, l_i, r_i)`, the names `a`, `b` of the `dup` cell, the first new name
    -- `j` and the rest of the net `Δ`,
    ∀ (cs : List (ℕ × Term sig ℕ × Term sig ℕ)) (a b j : ℕ) (Δ : CNet),
      -- if the net is linear
      Net.Linear (decodeNet cs a b Δ) →
      -- and its names are below `j`,
      Net.Below j (decodeNet cs a b Δ) →
      -- then it reduces, up to wires, to a net `M`
      ∃ M, StepsE system (decodeNet cs a b Δ) M ∧
        -- that is the same graph as the cells `x_i = dup(l_i, r_i)` and `Δ`
        Equiv M ((cs.map cellEq : List _) + Δ)
  | [], a, b, j, Δ, hlin, hb => by
    -- `M_0 = ε` erases the `dup`; the two erasers meet the two `M_0* = ε`
    simp only [decodeNet, List.map_nil, mux, muxStar] at hlin hb ⊢
    have h1 := step_era_dup (var a) (var b) (s(mkEra, var a) ::ₘ s(mkEra, var b) ::ₘ Δ)
    have L1 := h1.linear system_wellFormed.linear hlin
    have e1 : (s(mkEra, var a) ::ₘ s(mkEra, var b) ::ₘ s(mkEra, var a) ::ₘ s(mkEra, var b) ::ₘ Δ
        : CNet) = s(var a, mkEra) ::ₘ s(mkEra, var a) ::ₘ
          (s(mkEra, var b) ::ₘ s(mkEra, var b) ::ₘ Δ) := by
      rw [Sym2.eq_swap (a := mkEra) (b := var a)]; ms
    have E2 := equiv_cut_var a mkEra mkEra _ (L1.cast e1)
    have h2 : StepE system _ _ := ⟨_, (Equiv.of_eq e1).trans E2, step_era_era _⟩
    have L2 := h2.linear system_wellFormed.linear L1
    have e2 : (s(mkEra, var b) ::ₘ s(mkEra, var b) ::ₘ Δ : CNet) =
        s(var b, mkEra) ::ₘ s(mkEra, var b) ::ₘ Δ := by
      rw [Sym2.eq_swap (a := mkEra) (b := var b)]
    have E3 := equiv_cut_var b mkEra mkEra _ (L2.cast e2)
    have h3 : StepE system _ _ := ⟨_, (Equiv.of_eq e2).trans E3, step_era_era _⟩
    exact ⟨Δ, ((Relation.ReflTransGen.single h1.stepE).tail h2).tail h3,
      Equiv.of_eq (by simp)⟩
  | [c], a, b, j, Δ, hlin, hb => by
    -- `M_1` and `M_1*` are wires: two wire substitutions give the cell
    obtain ⟨x, l, r⟩ := c
    simp only [decodeNet, List.map_cons, List.map_nil, mux, muxStar] at hlin hb ⊢
    have e : (s(var x, mkDup (var a) (var b)) ::ₘ s(l, var a) ::ₘ s(r, var b) ::ₘ Δ : CNet) =
        s(var a, l) ::ₘ s(var b, r) ::ₘ s(var x, mkDup (var a) (var b)) ::ₘ Δ := by
      rw [Sym2.eq_swap (a := r), Sym2.eq_swap (a := l)]; ms
    have E := equiv_cut_bin mkDup vars_mkDup subst_mkDup a b l r (var x) Δ (hlin.cast e)
    refine ⟨_, Relation.ReflTransGen.refl, (Equiv.of_eq e).trans (E.trans (Equiv.of_eq ?_))⟩
    simp [cellEq]
  | c :: c' :: cs, a, b, j, Δ, hlin, hb => by
    obtain ⟨x, l, r⟩ := c
    set T := mux ((c' :: cs).map fun c => var c.1) with hT
    set R := muxStar ((c' :: cs).map fun c => c.2.2) with hR
    set L := muxStar ((c' :: cs).map fun c => c.2.1) with hL
    have e0 : decodeNet ((x, l, r) :: c' :: cs) a b Δ =
        s(mkCon (var x) T, mkDup (var a) (var b)) ::ₘ s(mkCon L l, var a) ::ₘ
          s(mkCon R r, var b) ::ₘ Δ := by
      simp only [decodeNet, List.map_cons, mux_cons_cons, muxStar_cons_cons, hT, hR, hL]
    rw [e0] at hlin hb ⊢
    have hb' := hb
    simp only [Net.below_cons, below_mkCon, below_mkDup, Term.below_var] at hb'
    obtain ⟨⟨hx, hTb⟩, ⟨ha, hbb⟩, ⟨hLb, hl⟩, -, ⟨hRb, hr⟩, -, hΔ⟩ := hb'
    -- `con` at the top of `M_n` against the `dup`, new wires `j, j + 1, j + 2, j + 3`
    have h1 := step_con_dup (var x) T (var a) (var b)
      (s(mkCon L l, var a) ::ₘ s(mkCon R r, var b) ::ₘ Δ) j (j + 1) (j + 2) (j + 3) (by simp)
      (fun v hv => hb.notMem (by simp at hv; omega))
    have L1 := h1.linear system_wellFormed.linear hlin
    -- the copy on `a` (port 0) meets `M_n*` of the trees `l_i`
    have e1 : (s(var x, mkDup (var j) (var (j + 1))) ::ₘ s(T, mkDup (var (j + 2)) (var (j + 3))) ::ₘ
        s(var a, mkCon (var j) (var (j + 2))) ::ₘ s(var b, mkCon (var (j + 1)) (var (j + 3))) ::ₘ
        s(mkCon L l, var a) ::ₘ s(mkCon R r, var b) ::ₘ Δ : CNet) =
        s(var a, mkCon (var j) (var (j + 2))) ::ₘ s(mkCon L l, var a) ::ₘ
          (s(var x, mkDup (var j) (var (j + 1))) ::ₘ s(T, mkDup (var (j + 2)) (var (j + 3))) ::ₘ
            s(var b, mkCon (var (j + 1)) (var (j + 3))) ::ₘ s(mkCon R r, var b) ::ₘ Δ) := by ms
    have E2 := equiv_cut_var a (mkCon (var j) (var (j + 2))) (mkCon L l) _ (L1.cast e1)
    have h2 : StepE system _ _ := ⟨_, (Equiv.of_eq e1).trans E2,
      step_con_con L l (var j) (var (j + 2)) _⟩
    have L2 := h2.linear system_wellFormed.linear L1
    -- the copy on `b` (port 1) meets `M_n*` of the trees `r_i`
    have e2 : (s(L, var (j + 2)) ::ₘ s(l, var j) ::ₘ
          (s(var x, mkDup (var j) (var (j + 1))) ::ₘ s(T, mkDup (var (j + 2)) (var (j + 3))) ::ₘ
            s(var b, mkCon (var (j + 1)) (var (j + 3))) ::ₘ s(mkCon R r, var b) ::ₘ Δ) : CNet) =
        s(var b, mkCon (var (j + 1)) (var (j + 3))) ::ₘ s(mkCon R r, var b) ::ₘ
          (s(L, var (j + 2)) ::ₘ s(l, var j) ::ₘ s(var x, mkDup (var j) (var (j + 1))) ::ₘ
            s(T, mkDup (var (j + 2)) (var (j + 3))) ::ₘ Δ) := by ms
    have E3 := equiv_cut_var b (mkCon (var (j + 1)) (var (j + 3))) (mkCon R r) _ (L2.cast e2)
    have h3 : StepE system _ _ := ⟨_, (Equiv.of_eq e2).trans E3,
      step_con_con R r (var (j + 1)) (var (j + 3)) _⟩
    have L3 := h3.linear system_wellFormed.linear L2
    -- the left tree and the right tree plugged into the copy of the `dup` cell on `x`
    have e3 : (s(R, var (j + 3)) ::ₘ s(r, var (j + 1)) ::ₘ
          (s(L, var (j + 2)) ::ₘ s(l, var j) ::ₘ s(var x, mkDup (var j) (var (j + 1))) ::ₘ
            s(T, mkDup (var (j + 2)) (var (j + 3))) ::ₘ Δ) : CNet) =
        s(var j, l) ::ₘ s(var (j + 1), r) ::ₘ s(var x, mkDup (var j) (var (j + 1))) ::ₘ
          (s(T, mkDup (var (j + 2)) (var (j + 3))) ::ₘ s(R, var (j + 3)) ::ₘ
            s(L, var (j + 2)) ::ₘ Δ) := by
      rw [Sym2.eq_swap (a := l), Sym2.eq_swap (a := r)]; ms
    have E4 := equiv_cut_bin mkDup vars_mkDup subst_mkDup j (j + 1) l r (var x) _ (L3.cast e3)
    have e4 : (s(var x, mkDup l r) ::ₘ (s(T, mkDup (var (j + 2)) (var (j + 3))) ::ₘ
          s(R, var (j + 3)) ::ₘ s(L, var (j + 2)) ::ₘ Δ) : CNet) =
        decodeNet (c' :: cs) (j + 2) (j + 3) (cellEq (x, l, r) ::ₘ Δ) := by
      simp only [decodeNet, hT, hR, hL, cellEq]; ms
    have E5 := ((Equiv.of_eq e3).trans E4).trans (Equiv.of_eq e4)
    have L5 := E5.linear L3
    -- the remaining `n - 1` cells
    have hb5 : Net.Below (j + 4)
        (decodeNet (c' :: cs) (j + 2) (j + 3) (cellEq (x, l, r) ::ₘ Δ)) := by
      rw [← e4]
      simp only [Net.below_cons, below_mkDup, Term.below_var]
      exact ⟨by omega, ⟨hl.mono (by omega), hr.mono (by omega)⟩, hTb.mono (by omega),
        ⟨by omega, by omega⟩, hRb.mono (by omega), by omega, hLb.mono (by omega), by omega,
        hΔ.mono (by omega)⟩
    obtain ⟨M, hS, hE⟩ := decode_cells (c' :: cs) (j + 2) (j + 3) (j + 4) _ L5 hb5
    obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv E5 hS
    refine ⟨M', (((Relation.ReflTransGen.single h1.stepE).tail h2).tail h3).trans hS',
      hE'.trans (hE.trans (Equiv.of_eq ?_))⟩
    simp only [List.map_cons, ← Multiset.cons_coe]
    ms

-- ============================================================================================
-- 4. Main results: the decoder extracts the tree from its code
-- ============================================================================================

/-- Fig. 9 (page 89) for any tree `t`: the code `code k t` against the decoder `decoder w k₀`
reduces to a net that is `Equiv` to `t` on the free port `w` of the decoder. The new names of the
code start at `k`, above every name of the net `s(var w, t) ::ₘ Δ`; the loop `k₀, k₀ + 1` of the
decoder and the new wires of the reduction start at or above the next unused name of the code. -/
theorem code_decoder_tree
    -- the tree, the first new name `k` of its code, the free port `w` of the decoder, and the
    -- first name `k₀` of the loop of the decoder
    (t : Term sig ℕ)
    (k w k₀ : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net `t` on `w`, with `Δ`, is linear and its names are below `k`
    (hlin : Net.Linear (s(var w, t) ::ₘ Δ))
    (hb : Net.Below k (s(var w, t) ::ₘ Δ))
    -- the loop of the decoder is at or above the names of the code
    (hk₀ : (decomp k t).k ≤ k₀) :
    -- the code against the decoder reduces, up to wires, to a net `M`
    ∃ M, StepsE system (s(code k t, decoder w k₀) ::ₘ Δ) M ∧
      -- that is the same graph as `t` on `w`, with `Δ`
      Equiv M (s(var w, t) ::ₘ Δ) := by
  set D := decomp k t with hD
  -- the first stage: `M_4` against `M_4*`
  have h1 : Red (s(code k t, decoder w k₀) ::ₘ Δ)
      (decodeNet D.cells k₀ (k₀ + 1) (s(D.τ, var w) ::ₘ Δ)) := code_decoder k t w k₀ Δ
  -- its names: those of `s(var w, t) ::ₘ Δ`, and both ends of the cut names and of the loop
  obtain ⟨hnd, hr, hkk⟩ := decomp_ports t k
  have hDk : D.k = (decomp k t).k := rfl
  have hvt := decomp_vars t k
  simp only [vars'] at hvt
  have hv : Net.vars (decodeNet D.cells k₀ (k₀ + 1) (s(D.τ, var w) ::ₘ Δ)) =
      Net.vars (s(var w, t) ::ₘ Δ) +
        ((k₀ ::ₘ (k₀ + 1) ::ₘ D.ports) + (k₀ ::ₘ (k₀ + 1) ::ₘ D.ports)) := by
    rw [vars_decodeNet D.cells D.τ, Net.vars_cons, Net.vars_cons, eqVars_mk, eqVars_mk]
    change D.ports + D.auxVars + _ + (D.τ.vars + _ + _) = _
    have h := congrArg (fun m => D.ports + ({k₀, k₀, k₀ + 1, k₀ + 1} : Multiset ℕ) +
      (var w : Term sig ℕ).vars + Net.vars Δ + m) hvt
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add] at h ⊢
    refine Eq.trans ?_ (h.trans ?_) <;> abel
  have hF : (k₀ ::ₘ (k₀ + 1) ::ₘ D.ports).Nodup := by
    refine Multiset.nodup_cons.2 ⟨?_, Multiset.nodup_cons.2 ⟨fun h => ?_, hnd⟩⟩
    · rw [Multiset.mem_cons]
      rintro (h | h)
      · omega
      · have := (hr _ h).2; omega
    · have := (hr _ h).2; omega
  have hfresh : ∀ x ∈ k₀ ::ₘ (k₀ + 1) ::ₘ D.ports, x ∉ Net.vars (s(var w, t) ::ₘ Δ) := by
    intro x hx
    refine hb.notMem ?_
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · omega
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · omega
    · exact (hr x hx).1
  have L1 := hlin.add_fresh _ hF hfresh hv
  have B1 : Net.Below (k₀ + 2) (decodeNet D.cells k₀ (k₀ + 1) (s(D.τ, var w) ::ₘ Δ)) := by
    intro x hx
    rw [hv] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · have := hb x hx; omega
    · have hx' : x ∈ k₀ ::ₘ (k₀ + 1) ::ₘ D.ports := by
        rcases Multiset.mem_add.1 hx with h | h <;> exact h
      rcases Multiset.mem_cons.1 hx' with rfl | hx'
      · omega
      rcases Multiset.mem_cons.1 hx' with rfl | hx'
      · omega
      · have := (hr x hx').2; omega
  -- the rest of Fig. 9
  obtain ⟨M, hS, hE⟩ := decode_cells D.cells k₀ (k₀ + 1) (k₀ + 2) _ L1 B1
  -- the cells `x_i = dup(l_i, r_i)` and `τ` on `w` are `t` on `w` (page 88)
  have E := decomp_equiv t k (var w) Δ hlin hb
  refine ⟨M, h1.stepsE.trans hS, hE.trans ((Equiv.of_eq ?_).trans E.symm)⟩
  rw [← hD, Decomp.net, Sym2.eq_swap (a := D.τ)]
  ms

/-- Fig. 9 (page 89): "`!π` is a code for `π`, which can be extracted with the decoder `D`". For a
package `π` plugged into the name `w`, with any context `Δ`, the code `!π` (new names from `k`,
above every name of the net) plugged into the decoder with free port `w` and loop `k₀, k₀ + 1`
reduces, by interactions up to wires, to a net that is `Equiv` to `π` on `w`. The loop and the new
wires of the reduction are taken at or above `(decomp k π).k`, the next name unused by the code.

The hypothesis that `π` is a package is not needed: see `code_decoder_tree`. -/
theorem code_decoder_package
    -- the package (the hypothesis is not used)
    (π : Term sig ℕ)
    (_hπ : π.IsPackage)
    -- the first new name `k` of the code, the free port `w` of the decoder, and the first name
    -- `k₀` of the loop of the decoder
    (k w k₀ : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net `π` on `w`, with `Δ`, is linear and its names are below `k`
    (hlin : Net.Linear (s(var w, π) ::ₘ Δ))
    (hb : Net.Below k (s(var w, π) ::ₘ Δ))
    -- the loop of the decoder is at or above the names of the code
    (hk₀ : (decomp k π).k ≤ k₀) :
    -- the code `!π` against the decoder reduces, up to wires, to a net `M`
    ∃ M, StepsE system (s(code k π, decoder w k₀) ::ₘ Δ) M ∧
      -- that is the same graph as `π` on `w`, with `Δ`
      Equiv M (s(var w, π) ::ₘ Δ) :=
  code_decoder_tree π k w k₀ Δ hlin hb hk₀

end INet.Comb
