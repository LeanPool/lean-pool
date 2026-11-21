/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeShift
public import LeanPool.InteractionCombinators.Translations.Simulation

/-!
# `⟨t⟩` with a copy of `!Γ` on each extra port reduces to `[t]` (Fig. 10, page 90)

Lafont 1997, Fig. 10 (journal page 89, PDF page 21) and the text of page 90: after the copier
`C_{p_{i,j}}` has made one copy of `!Γ` per cell of `⟨φ_{i,j}⟩`, each cell `⟨α_k⟩` uses its copy to
become `[α_k]`, "and we get the translation of `φ_{i,j}`".

The statement is for one tree `t` of a side: the net `P = ⟨t⟩` (`codeTerm`) with an equation
`e = (!Γ)_f` for each tree `e` on an extra port of `⟨t⟩` (`codeExtras`), each copy of `!Γ` renamed
injectively, in any context `Δ`, reduces to a net that is `Equiv` to `P = t'`, where `t'` is a
translation of `t` by `codeTranslation side`.

The proof is by induction on `t`. At a cell `β` whose subtrees are `t_1, …, t_n`:

1. the subtrees `⟨t_i⟩` are cut off the cell along fresh wires `z_i` (`cellSkel_cut`);
2. the cell `⟨β⟩` takes its copy of `!Γ` and becomes `[β]` (`codeCell_code_codeMenus`);
3. each subtree, with its own copies, reduces by induction, beside the others
   (`stepsE_jobs`);
4. the wires `z_i` are contracted again (`cellSkel_uncut`), and the cell is an instance of the
   principal net `[β]` (`codeNet_inst_eq`).

Contents, in the order of the file:

1. Definitions: `codeCopies`, the equations `e = (!Γ)_f`, one per tree `e` on an extra port;
   `wiresOf`, the wires `Z + j = t j`.
2. Auxiliary lemmas: splitting the copies along the subtrees. `codeCopies_cons`,
   `codeCopies_flatten_ofFn`.
3. Auxiliary lemmas: cutting the subtrees of a cell off along fresh wires. `vars_wiresOf`,
   `sum_vars_ofFn_var'`, `sum_vars_ofFn`, `wiresOf_eq`, `cut_free`, `cellSkel_uncut`,
   `cellSkel_cut`.
4. Auxiliary lemma: the cell `⟨β⟩` beside the rest is linear. `codeCell_add_linear`.
5. Auxiliary lemmas: the subtrees, side by side. `stepsE_jobs`, `sum_map_cons_univ`.
6. Main results: `codeTerm_extractE`, the statement for any numbering of the symbols, and
   `codeTerm_extract`, the statement for the enumeration `symEnum S`.
-/

@[expose] public section

namespace INet.Comb

open Term Translation Simulation

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- The equations `e = C_f` for the trees `es` on the extra ports and the renamings `fs`: the copy
of `C` renamed by `f` on the extra port `e` (the form in which `copier_code` leaves its copies). -/
def codeCopies
    -- the tree that is copied
    (C : Term sig ℕ)
    -- the trees on the extra ports, and one renaming for each
    (es : List (Term sig ℕ))
    (fs : List (ℕ → ℕ)) :
    CNet :=
  (List.zipWith (fun e f => s(e, C.bind fun x => var (f x))) es fs : CNet)

/-- The wires `Z + j = t j`. -/
def wiresOf
    -- the number `n` of wires, and the first fresh name
    {n : ℕ}
    (Z : ℕ)
    -- the trees at the other ends of the wires
    (t : Fin n → Term sig ℕ) :
    CNet :=
  Finset.univ.val.map fun j : Fin n => s(var (Z + (j : ℕ)), t j)

-- ============================================================================================
-- 2. Auxiliary lemmas: splitting the copies along the subtrees
-- ============================================================================================

/-- The copies on a list `e :: es` are the copy on `e` and the copies on `es`. -/
theorem codeCopies_cons
    -- the tree that is copied
    (C : Term sig ℕ)
    -- the first extra port and the others
    (e : Term sig ℕ)
    (es : List (Term sig ℕ))
    -- the first renaming and the others
    (f : ℕ → ℕ)
    (fs : List (ℕ → ℕ)) :
    codeCopies C (e :: es) (f :: fs)
      = s(e, C.bind fun x => var (f x)) ::ₘ codeCopies C es fs := by
  simp [codeCopies]

/-- **Splitting the copies along the subtrees.** The copies on a flattened list of extra ports are
the sum of the copies on each list, for some split of the renamings. -/
theorem codeCopies_flatten_ofFn
    -- the tree that is copied
    (C : Term sig ℕ) :
    -- for `n` lists `E i` of extra ports, and as many renamings `fs` as ports in all,
    ∀ {n : ℕ} (E : Fin n → List (Term sig ℕ)) (fs : List (ℕ → ℕ)),
      fs.length = ∑ i, (E i).length →
      -- there are lists of renamings `fss i` such that
      ∃ fss : Fin n → List (ℕ → ℕ),
        -- `fss i` has one renaming for each port of `E i`,
        (∀ i, (fss i).length = (E i).length) ∧
        -- every renaming of `fss i` is one of `fs`,
        (∀ i, ∀ f ∈ fss i, f ∈ fs) ∧
        -- and the copies on the flattened list are the sum of the copies on each `E i`
        codeCopies C (List.ofFn E).flatten fs = ∑ i, codeCopies C (E i) (fss i)
  | 0, E, fs, h => by
    have : fs = [] := List.length_eq_zero_iff.1 (by simpa using h)
    subst this
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [codeCopies]⟩
  | n + 1, E, fs, h => by
    rw [Fin.sum_univ_succ] at h
    obtain ⟨fss, h1, h2, h3⟩ := codeCopies_flatten_ofFn C (fun i => E i.succ)
      (fs.drop (E 0).length) (by rw [List.length_drop]; omega)
    refine ⟨Fin.cons (fs.take (E 0).length) fss, fun i => ?_, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, List.length_take]; omega
      · simpa using h1 j
    · refine Fin.cases (fun f hf => List.mem_of_mem_take hf) (fun j f hf => ?_) i
      exact List.mem_of_mem_drop (h2 j f (by simpa using hf))
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [← h3, List.ofFn_succ, List.flatten_cons]
      conv_lhs => rw [← List.take_append_drop (E 0).length fs]
      rw [codeCopies, List.zipWith_append (by rw [List.length_take]; omega), ← Multiset.coe_add]
      rfl

-- ============================================================================================
-- 3. Auxiliary lemmas: cutting the subtrees of a cell off along fresh wires
-- ============================================================================================

/-- The names of the wires `Z + j = t j` are each `Z + j` and the names of each `t j`. -/
theorem vars_wiresOf
    -- the first fresh name, and the trees at the other ends of the wires
    {n : ℕ}
    (Z : ℕ)
    (t : Fin n → Term sig ℕ) :
    (wiresOf Z t).vars = ∑ j : Fin n, ({Z + (j : ℕ)} + (t j).vars) := by
  simp only [wiresOf, Net.vars, Multiset.bind, Multiset.join, Multiset.map_map]
  rw [Finset.sum_eq_multiset_sum]
  rfl

/-- The names of the leaves `Z + j` are the names `Z + j`. -/
theorem sum_vars_ofFn_var'
    -- the first fresh name
    {n : ℕ}
    (Z : ℕ) :
    ((List.ofFn fun j : Fin n => (var (Z + j) : Term sig ℕ)).map Term.vars).sum
      = ∑ j : Fin n, ({Z + (j : ℕ)} : Multiset ℕ) := by
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- The names of the trees of a list `List.ofFn t` are the sum of the names of each `t j`. -/
theorem sum_vars_ofFn
    -- the trees
    {n : ℕ}
    (t : Fin n → Term sig ℕ) :
    ((List.ofFn t).map Term.vars).sum = ∑ j, (t j).vars := by
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- `wiresOf` as the `wires` of `Simulation`. -/
theorem wiresOf_eq
    -- the first fresh name, and the trees at the other ends of the wires
    {n : ℕ}
    (Z : ℕ)
    (t : Fin n → Term sig ℕ) :
    wiresOf Z t
      = wires (fun x => if h : Z ≤ x ∧ x - Z < n then t ⟨x - Z, h.2⟩ else var x)
          (List.ofFn fun j : Fin n => Z + (j : ℕ)) := by
  rw [wires, ← Fin.univ_val_map, Multiset.map_map, wiresOf]
  refine Multiset.map_congr rfl fun j _ => ?_
  simp

/-- The names `Z + i` of the leaves of a cut cell, with the wires `Z + j = t j`, beside `P` and
`Δ`: by linearity, `Z + i` occurs nowhere else. -/
theorem cut_free
    -- the cell: the tree `Γ` in place of the menu, `u` in place of the code, the number `m` of
    -- symbols, the symbol `k`, the name `ℓ` of its principal port, and the tree `P` facing it
    {n : ℕ}
    (Γ u P : Term sig ℕ)
    (m k ℓ : ℕ)
    -- the first fresh name, and the subtrees cut off along the wires `Z + j`
    (Z : ℕ)
    (t : Fin n → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the cut net is linear
    (hlin : Net.Linear (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ)
      ::ₘ Δ + wiresOf Z t))
    -- the leaf `Z + i`
    (i : Fin n) :
    -- `Z + i` occurs in none of `P`, `Γ`, `u`,
    P.vars.count (Z + i) = 0 ∧ Γ.vars.count (Z + i) = 0 ∧ u.vars.count (Z + i) = 0 ∧
      -- it is not `ℓ`,
      ℓ ≠ Z + i ∧
      -- it occurs neither in `Δ` nor in any subtree `t j`
      (Net.vars Δ).count (Z + i) = 0 ∧ ∀ j, (t j).vars.count (Z + i) = 0 := by
  have hc := hlin (Z + i)
  simp only [Net.vars_add, Net.vars_cons, eqVars_mk, vars_cellSkel, List.map_cons, List.sum_cons,
    sum_vars_ofFn_var', vars_wiresOf, Multiset.count_add, Multiset.count_sum',
    Finset.sum_add_distrib] at hc
  have h1 : 1 ≤ ∑ j : Fin n, Multiset.count (Z + i) ({Z + (j : ℕ)} : Multiset ℕ) :=
    le_trans (by simp) (Finset.single_le_sum (f := fun j : Fin n =>
      Multiset.count (Z + i) ({Z + (j : ℕ)} : Multiset ℕ)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))
  have h2 : ∀ j, (t j).vars.count (Z + i) ≤ ∑ j, (t j).vars.count (Z + i) := fun j =>
    Finset.single_le_sum (f := fun j => (t j).vars.count (Z + i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  refine ⟨by omega, by omega, by omega, fun h => ?_, by omega, fun j => by have := h2 j; omega⟩
  rw [h, Multiset.count_singleton_self] at hc
  omega

/-- **Contracting the wires of a cut cell** (page 71): the cell `[αᵢ]` whose auxiliary ports carry
the names `Z + j`, with the wires `Z + j = t j`, beside `P` and `Δ`, is the same graph as the cell
with the trees `t j` on its auxiliary ports. -/
theorem cellSkel_uncut
    -- the cell: the tree `Γ` in place of the menu, `u` in place of the code, the number `m` of
    -- symbols, the symbol `k`, the name `ℓ` of its principal port, and the tree `P` facing it
    {n : ℕ}
    (Γ u P : Term sig ℕ)
    (m k ℓ : ℕ)
    -- the first fresh name, and the subtrees cut off along the wires `Z + j`
    (Z : ℕ)
    (t : Fin n → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the cut net is linear
    (hlin : Net.Linear (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ)
      ::ₘ Δ + wiresOf Z t)) :
    -- the cut net is the same graph as the cell with the subtrees on its auxiliary ports
    Equiv
      (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ) ::ₘ Δ
        + wiresOf Z t)
      (s(P, cellSkel Γ m k (u :: List.ofFn t) ℓ) ::ₘ Δ) := by
  have hf := cut_free Γ u P m k ℓ Z t Δ hlin
  set σ : ℕ → Term sig ℕ := fun x => if h : Z ≤ x ∧ x - Z < n then t ⟨x - Z, h.2⟩ else var x
  set zl := List.ofFn fun j : Fin n => Z + (j : ℕ)
  have hzl : ∀ x, x ∈ zl ↔ ∃ i : Fin n, x = Z + i := fun x => by
    simp only [zl, List.mem_ofFn]
    exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  have hσ : ∀ i : Fin n, σ (Z + i) = t i := fun i => by simp [σ]
  have hnd : zl.Nodup := List.nodup_ofFn.2 fun i j h => Fin.ext (by simpa using h)
  rw [wiresOf_eq] at hlin ⊢
  refine (equiv_contract_list σ zl _ hnd ?_ ?_ hlin).trans (Equiv.of_eq ?_)
  · intro p hp q hq
    obtain ⟨i, rfl⟩ := (hzl p).1 hp
    obtain ⟨j, rfl⟩ := (hzl q).1 hq
    rw [hσ]
    exact Multiset.count_eq_zero.1 ((hf i).2.2.2.2.2 j)
  · intro p hp
    obtain ⟨i, rfl⟩ := (hzl p).1 hp
    have hm : Z + (i : ℕ) ∈ ∑ j : Fin n, ({Z + (j : ℕ)} : Multiset ℕ) :=
      Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Multiset.mem_singleton_self _⟩
    rw [Net.vars_cons, eqVars_mk, vars_cellSkel, List.map_cons, List.sum_cons,
      sum_vars_ofFn_var']
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr (Multiset.mem_add.2 (Or.inl
      (Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr (Multiset.mem_add.2
        (Or.inr hm)))))))))))
  · have hid : ∀ r : Term sig ℕ, (∀ i : Fin n, r.vars.count (Z + i) = 0) →
        r.bind (fun z => if z ∈ zl then σ z else var z) = r := fun r hr => by
      conv_rhs => rw [← Term.bind_var_self r]
      refine Term.bind_congr fun x hx => ?_
      have : x ∉ zl := fun h => by
        obtain ⟨i, rfl⟩ := (hzl x).1 h
        exact Multiset.count_eq_zero.1 (hr i) hx
      simp [this]
    have hΔ : Net.bind (fun z => if z ∈ zl then σ z else var z) Δ = Δ := by
      conv_rhs => rw [← Net.bind_var_self Δ]
      refine Net.bind_congr fun x hx => ?_
      have : x ∉ zl := fun h => by
        obtain ⟨i, rfl⟩ := (hzl x).1 h
        exact Multiset.count_eq_zero.1 (hf i).2.2.2.2.1 hx
      simp [this]
    have hℓ : ℓ ∉ zl := fun h => by
      obtain ⟨i, hi⟩ := (hzl ℓ).1 h
      exact (hf i).2.2.2.1 hi
    rw [Net.bind_cons, hΔ, hid P fun i => (hf i).1,
      bind_cellSkel_of _ _ _ _ _ _ ℓ (by simp [hℓ]), hid Γ fun i => (hf i).2.1, List.map_cons,
      hid u fun i => (hf i).2.2.1, List.map_ofFn]
    congr 4
    refine List.ofFn_inj.2 (funext fun j => ?_)
    have : Z + (j : ℕ) ∈ zl := (hzl _).2 ⟨j, rfl⟩
    simp [this, hσ]

/-- **Cutting the subtrees of a cell** (page 71): with the names from `Z` unused, the cell `[αᵢ]`
with the trees `c j` on its auxiliary ports, beside `P` and `Δ`, is the same graph as the cell
with the fresh names `Z + j` on its auxiliary ports and the wires `Z + j = c j`; and that net is
linear. -/
theorem cellSkel_cut
    -- the cell: the tree `Γ` in place of the menu, `u` in place of the code, the number `m` of
    -- symbols, the symbol `k`, the name `ℓ` of its principal port, and the tree `P` facing it
    {n : ℕ}
    (Γ u P : Term sig ℕ)
    (m k ℓ : ℕ)
    -- the first fresh name, and the subtrees on the auxiliary ports of the cell
    (Z : ℕ)
    (c : Fin n → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear, and its names are below `Z`
    (hlin : Net.Linear (s(P, cellSkel Γ m k (u :: List.ofFn c) ℓ) ::ₘ Δ))
    (hZ : Net.Below Z (s(P, cellSkel Γ m k (u :: List.ofFn c) ℓ) ::ₘ Δ)) :
    -- the cut net, with the names `Z + j` on the auxiliary ports and the wires `Z + j = c j`,
    -- is linear,
    Net.Linear (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ) ::ₘ Δ
      + wiresOf Z c) ∧
    -- the net we start from is the same graph as the cut net,
    Equiv (s(P, cellSkel Γ m k (u :: List.ofFn c) ℓ) ::ₘ Δ)
      (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ) ::ₘ Δ
        + wiresOf Z c) ∧
    -- and the names of the cut net are those of the net we start from, and each `Z + j` twice
    Net.vars (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ) ::ₘ Δ
        + wiresOf Z c)
      = Net.vars (s(P, cellSkel Γ m k (u :: List.ofFn c) ℓ) ::ₘ Δ)
        + (∑ j : Fin n, ({Z + (j : ℕ)} : Multiset ℕ)
          + ∑ j : Fin n, ({Z + (j : ℕ)} : Multiset ℕ)) := by
  set F : Multiset ℕ := ∑ j : Fin n, ({Z + (j : ℕ)} : Multiset ℕ)
  have hF : F = Finset.univ.val.map fun j : Fin n => Z + (j : ℕ) := by
    simp only [F, Finset.sum_eq_multiset_sum]
    exact Multiset.sum_map_singleton _ |>.symm.trans (by rw [Multiset.map_map]; rfl) |>.symm
  have hv : Net.vars (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ) ::ₘ
      Δ + wiresOf Z c) = Net.vars (s(P, cellSkel Γ m k (u :: List.ofFn c) ℓ) ::ₘ Δ) + (F + F) := by
    simp only [Net.vars_add, Net.vars_cons, eqVars_mk, vars_cellSkel, List.map_cons,
      List.sum_cons, sum_vars_ofFn_var', vars_wiresOf, Finset.sum_add_distrib, F]
    rw [sum_vars_ofFn]
    abel
  have hlin' : Net.Linear (s(P, cellSkel Γ m k (u :: List.ofFn fun j : Fin n => var (Z + j)) ℓ) ::ₘ
      Δ + wiresOf Z c) := by
    refine Net.Linear.add_fresh hlin F ?_ ?_ hv
    · rw [hF]
      exact (Multiset.nodup_map_iff_of_injective (fun i j h => Fin.ext (by simpa using h))).2
        Finset.univ.nodup
    · intro x hx hm
      rw [hF] at hx
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hx
      exact absurd (hZ _ hm) (by omega)
  exact ⟨hlin', (cellSkel_uncut Γ u P m k ℓ Z c Δ hlin').symm, hv⟩

-- ============================================================================================
-- 4. Auxiliary lemma: the cell `⟨β⟩`
-- ============================================================================================

/-- The net `⟨α_k⟩` (`codeCell`) beside `R` is linear when its tree on the extra port, its cell
and `R` are, and its internal wire `w` (from `D` to `S^k_m`) is a new name (page 89). -/
theorem codeCell_add_linear
    -- the number `m` of symbols and the symbol `k`
    (m k : ℕ)
    -- the tree `P` facing the cell, the tree `x` on the extra port, the trees `ts` on the
    -- auxiliary ports
    (P x : Term sig ℕ)
    (ts : List (Term sig ℕ))
    -- the internal wires of `⟨α_k⟩`
    (ℓ u w y k₀ : ℕ)
    -- the rest of the net
    (R : CNet)
    -- the tree on the extra port, the cell and `R` form a linear net
    (hlin : Net.Linear (s(codeExtra m k y u k₀, x)
      ::ₘ s(P, cellSkel (var y) m k (var u :: ts) ℓ) ::ₘ R))
    -- the wire `w` is a new name
    (hw : w ∉ Net.vars (s(codeExtra m k y u k₀, x)
      ::ₘ s(P, cellSkel (var y) m k (var u :: ts) ℓ) ::ₘ R)) :
    Net.Linear (codeCell m k P x ts ℓ u w y k₀ + R) := by
  refine Net.Linear.add_fresh hlin {w} (Multiset.nodup_singleton w)
    (fun z hz => by rw [Multiset.mem_singleton.1 hz]; exact hw) ?_
  simp only [codeCell, Multiset.cons_add, zero_add, Net.vars_cons, eqVars_mk, vars_codeExtra,
    copier, vars_autoMux, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    vars_decoder, vars_var, selector_eq_cellSel, vars_cellSel]
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  abel

-- ============================================================================================
-- 5. Auxiliary lemmas: the subtrees, side by side
-- ============================================================================================

/-- **Reducing several parts of a net one after the other.** If each part `J i`, in any context,
reduces to a net `Equiv` to one equation `z i = t` (with `R i t`), then the sum of the parts does,
to the equations `z i = t i`. -/
theorem stepsE_jobs
    -- the parts, the name `z i` left by each, and the property `R i` of the tree it leaves
    {n : ℕ}
    (J : Fin n → CNet)
    (z : Fin n → ℕ)
    (R : Fin n → Term sig ℕ → Prop)
    -- each part, beside any `Δ` with which it is linear, reduces to `z i = t` with `R i t`
    (hJ : ∀ (i : Fin n) (Δ : CNet), Net.Linear (J i + Δ) →
      ∃ M t, StepsE system (J i + Δ) M ∧ Equiv M (s(var (z i), t) ::ₘ Δ) ∧ R i t) :
    -- for a multiset `L` of distinct parts and any `Δ` with which their sum is linear,
    ∀ (L : Multiset (Fin n)), L.Nodup → ∀ Δ : CNet, Net.Linear ((L.map J).sum + Δ) →
      -- there are a net `M` and trees `t i` such that
      ∃ (M : CNet) (t : Fin n → Term sig ℕ),
        -- the sum of the parts, beside `Δ`, reduces, up to wires, to `M`,
        StepsE system ((L.map J).sum + Δ) M ∧
        -- `M` is the same graph as the equations `z i = t i` beside `Δ`,
        Equiv M (L.map (fun i => s(var (z i), t i)) + Δ) ∧
        -- and each `t i` has the property `R i`
        ∀ i ∈ L, R i (t i) := by
  intro L
  induction L using Multiset.induction_on with
  | empty =>
    intro _ Δ _
    exact ⟨_, fun _ => var 0, .refl, by simpa using Equiv.refl Δ, by simp⟩
  | cons i L ih =>
    intro hnd Δ hlin
    have hi : i ∉ L := (Multiset.nodup_cons.1 hnd).1
    rw [Multiset.map_cons, Multiset.sum_cons, add_assoc] at hlin ⊢
    obtain ⟨M₁, t₁, hS₁, hE₁, hR₁⟩ := hJ i _ hlin
    have L₁ := hE₁.linear (hS₁.linear system_wellFormed.linear hlin)
    have e : s(var (z i), t₁) ::ₘ ((L.map J).sum + Δ) =
        (L.map J).sum + (s(var (z i), t₁) ::ₘ Δ) := by rw [Multiset.add_cons]
    rw [e] at L₁ hE₁
    obtain ⟨M₂, t₂, hS₂, hE₂, hR₂⟩ := ih (Multiset.nodup_cons.1 hnd).2 _ L₁
    obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv hE₁ hS₂
    have hup : ∀ j ∈ L, Function.update t₂ i t₁ j = t₂ j := fun j hj =>
      Function.update_of_ne (fun h : j = i => hi (h ▸ hj)) _ _
    have hm : L.map (fun j => s(var (z j), Function.update t₂ i t₁ j)) =
        L.map (fun j => s(var (z j), t₂ j)) := Multiset.map_congr rfl fun j hj => by rw [hup j hj]
    refine ⟨M', Function.update t₂ i t₁, hS₁.trans hS', hE'.trans (hE₂.trans (Equiv.of_eq ?_)), ?_⟩
    · rw [Multiset.map_cons, Function.update_self, hm, Multiset.add_cons, Multiset.cons_add]
    · intro j hj
      rcases Multiset.mem_cons.1 hj with rfl | hj
      · simpa using hR₁
      · rw [hup j hj]
        exact hR₂ j hj

/-- The parts `z i = c i, copies_i`, summed, are the wires `z i = c i` and all the copies. -/
theorem sum_map_cons_univ
    -- the equation `e i` and the rest `A i` of each part
    {n : ℕ}
    (e : Fin n → Sym2 (Term sig ℕ))
    (A : Fin n → CNet) :
    (Finset.univ.val.map fun i => e i ::ₘ A i).sum = Finset.univ.val.map e + ∑ i, A i := by
  have h : (fun i => e i ::ₘ A i) = fun i => {e i} + A i :=
    funext fun i => (Multiset.singleton_add _ _).symm
  rw [h, Multiset.sum_map_add, Finset.sum_eq_multiset_sum]
  congr 1
  rw [show (fun i => ({e i} : CNet)) = (fun a => {a}) ∘ e from rfl, ← Multiset.map_map,
    Multiset.sum_map_singleton]

-- ============================================================================================
-- 6. Main results: `⟨t⟩` with its copies of `!Γ` reduces to `[t]`
-- ============================================================================================

section Enum

-- the numbering `e` of the `n` symbols, and the expanded sides of the rules
variable {S : Signature} {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **`⟨t⟩` with a copy of `!Γ` on each extra port reduces to `[t]`, for any numbering `e` of the
symbols** (Lafont 1997, Fig. 10, pages 89–90; page 90: no order on the symbols is needed). This is
`codeTerm_extract` with the `n` symbols numbered by any `e : S.Sym ≃ Fin n`:
`Γ = codeMenusE e side k₀`, `!Γ = code K Γ` with `K` above the names of `Γ`, the cells `⟨α⟩` of
`codeTerm` selecting the menu `e α` among `n`, and `t'` a translation of `t` by
`codeTranslationE e side`. -/
theorem codeTerm_extractE
    -- the first name `k₀` of `Γ`, and the bound `K` on its names
    (k₀ K : ℕ)
    (hK : k₀ + ∑ i, codeMenuSizesE e side i ≤ K)
    -- the tree of the side
    (t : Term S ℕ) :
    -- for new names from `b`, the tree `P` facing `⟨t⟩`, the renamings `fs` and the rest `Δ`,
    ∀ (b : ℕ) (P : Term sig ℕ) (fs : List (ℕ → ℕ)) (Δ : CNet),
      -- if there is one renaming for each extra port of `⟨t⟩`,
      fs.length = (codeExtras n (fun α => (e α : ℕ)) b t).length →
      -- each injective on the names of `!Γ`,
      (∀ f ∈ fs, Set.InjOn f {x | x ∈ (code K (menu (codeMenusE e side k₀))).vars}) →
      -- and the net `P = ⟨t⟩`, with the copies of `!Γ` on the extra ports and `Δ`, is linear,
      Net.Linear (s(P, codeTerm n (fun α => (e α : ℕ)) b t)
        ::ₘ (codeCopies (code K (menu (codeMenusE e side k₀)))
          (codeExtras n (fun α => (e α : ℕ)) b t) fs + Δ)) →
      -- then there are a net `M` and a tree `t'` such that
      ∃ M t',
        -- the net reduces, up to wires, to `M`,
        StepsE system (s(P, codeTerm n (fun α => (e α : ℕ)) b t)
          ::ₘ (codeCopies (code K (menu (codeMenusE e side k₀)))
            (codeExtras n (fun α => (e α : ℕ)) b t) fs + Δ)) M ∧
        -- `M` is the same graph as `P = t'` beside `Δ`,
        Equiv M (s(P, t') ::ₘ Δ) ∧
        -- and `t'` is a translation of `t`
        (codeTranslationE e side).TermTr t t' := by
  set C := code K (menu (codeMenusE e side k₀)) with hC
  have hm : (codeMenusE e side k₀).length = n := length_codeMenusE e side k₀
  induction t with
  | var x =>
    intro b P fs Δ hlen _ _
    have : fs = [] := List.length_eq_zero_iff.1 (by simpa [codeExtras] using hlen)
    subst this
    refine ⟨_, var x, .refl, Equiv.of_eq ?_, .var x⟩
    simp [codeTerm, codeExtras, codeCopies]
  | app β ts ih =>
    intro b P fs Δ hlen hinj hlin
    set idx : S.Sym → ℕ := fun α => (e α : ℕ)
    set c : Fin (S.arity β) → Term sig ℕ :=
      fun i => codeTerm n idx (b + 5 + off (fun j => codeSize (ts j)) i) (ts i) with hc
    set E : Fin (S.arity β) → List (Term sig ℕ) :=
      fun i => codeExtras n idx (b + 5 + off (fun j => codeSize (ts j)) i) (ts i) with hE
    have eT : codeTerm n idx b (.app β ts) =
        cellSkel (var (b + 2)) n (idx β) (var (b + 1) :: List.ofFn c) b := rfl
    have eX : codeExtras n idx b (.app β ts) =
        codeExtra n (idx β) (b + 2) (b + 1) (b + 3) :: (List.ofFn E).flatten := rfl
    rw [eT, eX] at hlin ⊢
    rw [eX] at hlen
    obtain ⟨f₀, fs', rfl⟩ : ∃ f₀ fs', fs = f₀ :: fs' := by
      cases fs with
      | nil => simp at hlen
      | cons f fs => exact ⟨f, fs, rfl⟩
    have hlen' : fs'.length = ∑ i, (E i).length := by
      simp only [List.length_cons, List.length_flatten, List.map_ofFn, List.sum_ofFn,
        Function.comp_def, add_left_inj] at hlen
      exact hlen
    obtain ⟨fss, hfl, hfm, hsplit⟩ := codeCopies_flatten_ofFn C E fs' hlen'
    rw [codeCopies_cons, hsplit] at hlin ⊢
    set e₀ := codeExtra n (idx β) (b + 2) (b + 1) (b + 3) with he₀
    set X : CNet := ∑ i, codeCopies C (E i) (fss i) with hX
    set C₀ := C.bind fun x => var (f₀ x) with hC₀
    -- 1. cut the subtrees off the cell, along the fresh wires `Z + 1 + j`
    obtain ⟨Z, hZ⟩ := Net.exists_below (s(P, cellSkel (var (b + 2)) n (idx β)
      (var (b + 1) :: List.ofFn c) b) ::ₘ (s(e₀, C₀) ::ₘ X + Δ))
    obtain ⟨hlin₁, hE₁, hv₁⟩ := cellSkel_cut (var (b + 2)) (var (b + 1)) P n (idx β) b (Z + 1) c _
      hlin (hZ.mono (Nat.le_succ Z))
    set Q₀ := cellSkel (var (b + 2)) n (idx β)
      (var (b + 1) :: List.ofFn fun j : Fin (S.arity β) => var (Z + 1 + j)) b with hQ₀
    set R : CNet := X + Δ + wiresOf (Z + 1) c with hR
    have e1 : s(P, Q₀) ::ₘ (s(e₀, C₀) ::ₘ X + Δ) + wiresOf (Z + 1) c =
        s(e₀, C₀) ::ₘ s(P, Q₀) ::ₘ R := by
      rw [hR, Multiset.cons_add, Multiset.cons_add, Multiset.cons_add, Multiset.cons_swap]
    rw [e1] at hlin₁ hE₁ hv₁
    -- 2. the cell `⟨β⟩` takes its copy of `!Γ` and becomes `[β]`
    have hw : Z ∉ Net.vars (s(e₀, C₀) ::ₘ s(P, Q₀) ::ₘ R) := by
      rw [hv₁]
      intro hm'
      rcases Multiset.mem_add.1 hm' with h | h
      · exact absurd (hZ _ h) (lt_irrefl _)
      · have : Z ∈ ∑ j : Fin (S.arity β), ({Z + 1 + (j : ℕ)} : Multiset ℕ) := by
          rcases Multiset.mem_add.1 h with h | h <;> exact h
        obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 this
        rw [Multiset.mem_singleton] at hj
        omega
    have hlin₂ := codeCell_add_linear n (idx β) P C₀ _ b (b + 1) Z (b + 2) (b + 3) R hlin₁ hw
    have E₂ := codeCell_equiv n (idx β) P C₀ _ b (b + 1) Z (b + 2) (b + 3) R hlin₂
    rw [Sym2.eq_swap] at E₂
    have key := codeCell_code_codeMenusE e side k₀ K hK β f₀ (hinj f₀ List.mem_cons_self) P
      (List.ofFn fun j : Fin (S.arity β) => var (Z + 1 + j)) b (b + 1) Z (b + 2) (b + 3) R
    rw [hm] at key
    obtain ⟨g, g', M₀, -, -, hS₀, hE₀⟩ := key hlin₂
    obtain ⟨M₀', hS₀', hE₀'⟩ := stepsE_of_equiv (hE₁.trans E₂.symm) hS₀
    have hlin₃ := (hE₀'.trans hE₀).linear (hS₀'.linear system_wellFormed.linear hlin)
    -- 3. the subtrees, with their copies, reduce one after the other
    set Q₁ := cellSkel
      ((menu (codeCellMenuE e side β (k₀ + off (codeMenuSizesE e side) (e β)))).bind
        fun x => var (g x)) n (e β) ((C.bind fun x => var (g' x)) ::
          List.ofFn fun j : Fin (S.arity β) => var (Z + 1 + j)) b with hQ₁
    set J : Fin (S.arity β) → CNet :=
      fun i => s(var (Z + 1 + i), c i) ::ₘ codeCopies C (E i) (fss i) with hJ
    have e3 : s(P, Q₁) ::ₘ R = (Finset.univ.val.map J).sum + s(P, Q₁) ::ₘ Δ := by
      rw [hJ, sum_map_cons_univ, hR, hX, wiresOf]
      rw [Multiset.add_cons]
      congr 1
      abel
    have hE₀'' := hE₀'.trans hE₀
    rw [e3] at hlin₃ hE₀''
    obtain ⟨M₁, t'', hS₁, hE₁', hR₁⟩ := stepsE_jobs J (fun i => Z + 1 + i)
      (fun i t' => (codeTranslationE e side).TermTr (ts i) t')
      (fun i Δ' hl => by
        have e : J i + Δ' = s(var (Z + 1 + i), c i) ::ₘ (codeCopies C (E i) (fss i) + Δ') :=
          Multiset.cons_add _ _ _
        rw [e] at hl ⊢
        exact ih i _ _ (fss i) Δ' (hfl i)
          (fun f hf => hinj f (List.mem_cons_of_mem _ (hfm i f hf))) hl)
      Finset.univ.val Finset.univ.nodup _ hlin₃
    obtain ⟨M₁', hS₁', hE₁''⟩ := stepsE_of_equiv hE₀'' hS₁
    have hlin₄ := (hE₁''.trans hE₁').linear (hS₁'.linear system_wellFormed.linear
      (hS₀'.linear system_wellFormed.linear hlin))
    -- 4. the wires are contracted, and the cell is an instance of `[β]`
    have e4 : (Finset.univ.val.map fun i : Fin (S.arity β) => s(var (Z + 1 + (i : ℕ)), t'' i))
          + s(P, Q₁) ::ₘ Δ =
        s(P, Q₁) ::ₘ Δ + wiresOf (Z + 1) t'' := add_comm _ _
    rw [e4] at hlin₄ hE₁'
    have E₄ := cellSkel_uncut _ _ P n (e β) b (Z + 1) t'' Δ hlin₄
    obtain ⟨F, hF⟩ := codeNetE_inst_eq e side β (k₀ + off (codeMenuSizesE e side) (e β)) k₀ K
      g g' b t''
    have hTr : (codeTranslationE e side).TermTr (.app β ts) ((codeNetE e side β).inst t'' F) :=
      TermTr.app (Φ := codeTranslationE e side) β ts t'' F fun i => hR₁ i (Finset.mem_univ i)
    refine ⟨M₁', (codeNetE e side β).inst t'' F, hS₀'.trans hS₁',
      hE₁''.trans (hE₁'.trans (E₄.trans (Equiv.of_eq (by rw [hF])))),
      hTr⟩

end Enum

-- finitely many symbols, and the expanded sides of the rules
variable {S : Signature} [Finite S.Sym]
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **`⟨t⟩` with a copy of `!Γ` on each extra port reduces to `[t]`** (Lafont 1997, Fig. 10,
pages 89–90: "and we get the translation of `φ_{i,j}`", here for one tree of the side). Let
`Γ = codeMenus side k₀` (the menu `Γ_0 & ⋯ & Γ_{m-1}` of Fig. 10, for any choice `side` of expanded
sides) and `!Γ = code K Γ` with `K` above the names of `Γ`. The net made of `P = ⟨t⟩` (`codeTerm`,
new names from `b`), one equation `e = (!Γ)_f` for each tree `e` on an extra port of `⟨t⟩`
(`codeExtras`, in order, with the renamings `fs`, each injective on the names of `!Γ`) and any
context `Δ`, if linear, reduces to a net that is `Equiv` to `P = t'` beside `Δ`, where `t'` is a
translation of `t` by the translation `[α]` of Fig. 10 (`codeTranslation side`). -/
theorem codeTerm_extract
    -- the first name `k₀` of `Γ`, and the bound `K` on its names
    (k₀ K : ℕ)
    (hK : k₀ + ∑ i, codeMenuSizes side i ≤ K)
    -- the tree of the side
    (t : Term S ℕ) :
    -- for new names from `b`, the tree `P` facing `⟨t⟩`, the renamings `fs` and the rest `Δ`,
    ∀ (b : ℕ) (P : Term sig ℕ) (fs : List (ℕ → ℕ)) (Δ : CNet),
      -- if there is one renaming for each extra port of `⟨t⟩`,
      fs.length = (codeExtras (Nat.card S.Sym) (fun α => symEnum S α) b t).length →
      -- each injective on the names of `!Γ`,
      (∀ f ∈ fs, Set.InjOn f {x | x ∈ (code K (menu (codeMenus side k₀))).vars}) →
      -- and the net `P = ⟨t⟩`, with the copies of `!Γ` on the extra ports and `Δ`, is linear,
      Net.Linear (s(P, codeTerm (Nat.card S.Sym) (fun α => symEnum S α) b t)
        ::ₘ (codeCopies (code K (menu (codeMenus side k₀)))
          (codeExtras (Nat.card S.Sym) (fun α => symEnum S α) b t) fs + Δ)) →
      -- then there are a net `M` and a tree `t'` such that
      ∃ M t',
        -- the net reduces, up to wires, to `M`,
        StepsE system (s(P, codeTerm (Nat.card S.Sym) (fun α => symEnum S α) b t)
          ::ₘ (codeCopies (code K (menu (codeMenus side k₀)))
            (codeExtras (Nat.card S.Sym) (fun α => symEnum S α) b t) fs + Δ)) M ∧
        -- `M` is the same graph as `P = t'` beside `Δ`,
        Equiv M (s(P, t') ::ₘ Δ) ∧
        -- and `t'` is a translation of `t`
        (codeTranslation side).TermTr t t' :=
  codeTerm_extractE (symEnum S) side k₀ K hK t

end INet.Comb
