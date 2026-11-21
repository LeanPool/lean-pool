/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.TranslationExists
public import LeanPool.InteractionCombinators.Text.RenameMany

/-!
# Composition of translations and invertible translations (pages 80–81)

Lafont 1997, Section 1.7, journal page 80, last paragraph, and page 81, top: "Composition of
translations is defined in the obvious way. One says that `Φ` is invertible if there is a
translation `Φ⁻¹` of `Σ'` into `Σ` such that `Φ⁻¹ ∘ Φ = id_Σ` and `Φ ∘ Φ⁻¹ = id_Σ'`."

* `Term.toFin` — a tree over `ℕ` whose names are below `B`, as a tree over `Fin B`.
* `PNet.ofNat` — a tree over `ℕ` whose names `0, …, n - 1` occur once and whose names
  `n, …, n + m - 1` occur twice, and no other, as a principal net with `m` internal wires.
* `PNet.natTree` — the tree of a principal net over `ℕ`: the port `i` is named `i`, the internal
  wire `w` is named `n + w`.
* `Translation.trPNet` — the translation `Ψ(p)` of a principal net: `Ψ` applied to its tree, with
  fresh internal wires numbered after those of `p`.
* `Translation.comp` — `Ψ ∘ Φ`: the principal net of `α` is `Ψ(Φ(α))`.
* `PNet.Iso` — equality of principal nets up to the names of their internal wires. Principal nets
  are graphs, so the names of internal wires do not matter.
* `Translation.Invertible` — `Φ⁻¹ ∘ Φ = id` and `Φ ∘ Φ⁻¹ = id`, read as `Iso` at every symbol.
* `Translation.comp_id`, `Translation.id_comp`, `Translation.invertible_id`.

Contents, in the order of the file:

1. Auxiliary lemmas, renaming the leaves of a tree: `Term.vars_bind_var_map`.
2. A tree with names below `B` as a tree over `Fin B`: `Term.mem_vars_app`, the definition
   `Term.toFin`, and `Term.bind_toFin`, `Term.toFin_bind_val`, `Term.toFin_eq`,
   `Term.count_toFin`.
3. Definition: a tree over `ℕ` as a principal net, `PNet.ofNat`.
4. Principal nets equal up to the names of internal wires: the definition `PNet.Iso`; it is an
   equivalence (`PNet.Iso.refl`, `PNet.Iso.symm`, `PNet.Iso.trans`), keeps the root cell
   (`PNet.Iso.root`), and `PNet.iso_ofNat` (`ofNat` of a renamed principal net).
5. The tree of a principal net over `ℕ`: the definitions `PNet.enc`, `PNet.natTree`, and their
   names (`PNet.enc_injective`, `PNet.vars_natTree`, `PNet.natTree_lt`,
   `PNet.count_natTree_enc`).
6. Definitions: the translation of a principal net (`Translation.trPNet_hyps`,
   `Translation.trPNet`), composition (`Translation.comp`), and invertible translations
   (`Translation.Invertible`).
7. Main results: the identity is neutral, `Translation.comp_id`, `Translation.id_comp`, and
   invertible, `Translation.invertible_id`.
-/

@[expose] public section

namespace INet

variable {S S' S'' : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: renaming the leaves of a tree
-- ============================================================================================

/-- The names of a tree renamed by `g`: those of the tree, renamed. -/
theorem Term.vars_bind_var_map
    -- the renaming
    {ν μ : Type}
    (g : ν → μ)
    -- the tree
    (t : Term S ν) :
    (t.bind fun x => var (g x)).vars = t.vars.map g := by
  rw [vars_bind]
  exact Multiset.bind_singleton _ _

-- ============================================================================================
-- 2. A tree with names below `B` as a tree over `Fin B`
-- ============================================================================================

/-- A name of a subtree is a name of the tree. -/
theorem Term.mem_vars_app
    -- the tree `app α ts` and the index of one of its subtrees
    {ν : Type}
    {α : S.Sym}
    {ts : Fin (S.arity α) → Term S ν}
    (i : Fin _)
    -- a name of the subtree `ts i`
    {x : ν}
    (hx : x ∈ (ts i).vars) :
    x ∈ (app α ts).vars := by
  simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]
  exact ⟨i, hx⟩

/-- A tree over `ℕ` whose names are below `B`, as a tree over `Fin B`. -/
def Term.toFin
    -- the bound on the names
    {B : ℕ} :
    -- a tree over `ℕ`, whose names are below `B`, gives a tree over `Fin B`
    (t : Term S ℕ) →
    (∀ x ∈ t.vars, x < B) →
    Term S (Fin B)
  | .var x, h => .var ⟨x, h x (by simp)⟩
  | .app α ts, h => .app α fun i => Term.toFin (ts i) fun x hx => h x (Term.mem_vars_app i hx)

/-- Forgetting the bound of `toFin` gives the tree back. -/
theorem Term.bind_toFin
    -- a tree whose names are below `B`
    {B : ℕ}
    (t : Term S ℕ)
    (h : ∀ x ∈ t.vars, x < B) :
    (t.toFin h).bind (fun x => var x.val) = t := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    change app α _ = app α ts
    congr 1
    funext i
    exact ih i _

/-- `toFin` of a tree over `Fin B` seen over `ℕ` is the tree. -/
theorem Term.toFin_bind_val
    -- a tree over `Fin B`
    {B : ℕ}
    (u : Term S (Fin B))
    -- the bound on the names of the same tree seen over `ℕ`
    (h : ∀ x ∈ (u.bind fun x => var x.val).vars, x < B) :
    (u.bind fun x => var x.val).toFin h = u := by
  induction u with
  | var x => rfl
  | app α ts ih =>
    change app α _ = app α ts
    congr 1
    funext i
    exact ih i _

/-- `toFin` of a tree that is a tree over `Fin B` seen over `ℕ`. -/
theorem Term.toFin_eq
    -- a tree over `ℕ`, whose names are below `B`
    {B : ℕ}
    {t : Term S ℕ}
    -- a tree over `Fin B` that is `t` seen over `ℕ`
    {u : Term S (Fin B)}
    (h : ∀ x ∈ t.vars, x < B)
    (htu : t = u.bind fun x => var x.val) :
    t.toFin h = u := by
  subst htu
  exact Term.toFin_bind_val u h

/-- The names of `toFin`: those of the tree, with their multiplicity. -/
theorem Term.count_toFin
    -- a tree whose names are below `B`
    {B : ℕ}
    (t : Term S ℕ)
    (h : ∀ x ∈ t.vars, x < B)
    -- a name below `B`
    (y : Fin B) :
    (t.toFin h).vars.count y = t.vars.count y.val := by
  have e := congrArg Term.vars (Term.bind_toFin t h)
  rw [Term.vars_bind_var_map] at e
  rw [← e, Multiset.count_map_eq_count' _ _ Fin.val_injective]

namespace PNet

variable {n : ℕ}

-- ============================================================================================
-- 3. Definition: a tree over `ℕ` as a principal net
-- ============================================================================================

/-- **A tree as a principal net** (principal nets, pages 79–80). A tree `t` whose names are below
`n + m`, whose names `0, …, n - 1` occur once and whose names `n, …, n + m - 1` occur twice is a
principal net with `n` auxiliary ports and `m` internal wires: the name `i < n` is the port `i`,
the name `n + w` the internal wire `w`. -/
def ofNat
    -- the number of ports and of internal wires
    (n m : ℕ)
    -- the tree: its names are below `n + m`, a port occurs once, an internal wire twice
    (t : Term S ℕ)
    (hb : ∀ x ∈ t.vars, x < n + m)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ w < m, t.vars.count (n + w) = 2) :
    PNet S n where
  internal := m
  tree := (t.toFin hb).bind fun x => var (finSumFinEquiv.symm x)
  port_count i := by
    rw [Term.vars_bind_var_map, ← finSumFinEquiv_symm_apply_castAdd,
      Multiset.count_map_eq_count' _ _ finSumFinEquiv.symm.injective, Term.count_toFin]
    exact hp i i.isLt
  internal_count w := by
    rw [Term.vars_bind_var_map, ← finSumFinEquiv_symm_apply_natAdd,
      Multiset.count_map_eq_count' _ _ finSumFinEquiv.symm.injective, Term.count_toFin]
    exact hw w w.isLt

-- ============================================================================================
-- 4. Principal nets equal up to the names of internal wires
-- ============================================================================================

/-- **Equality of principal nets** (principal nets, pages 79–80). Two principal nets are the same
graph when one tree is the other with its internal wires renamed by a bijection; the ports keep
their names. This is the equality of the paper's `Φ⁻¹ ∘ Φ = id_Σ` (pages 80–81). -/
def Iso
    -- two principal nets of the same arity
    (p q : PNet S n) :
    Prop :=
  -- a bijection of the internal wires that renames the tree of `p` into that of `q`
  ∃ e : Fin p.internal ≃ Fin q.internal,
    p.tree.bind (fun x => var (Sum.map id e x)) = q.tree

/-- Renaming the internal wires by `e`, then by `e.symm`, changes nothing. -/
theorem bind_sumMap_symm
    -- the renaming of the internal wires
    {m k : ℕ}
    (e : Fin m ≃ Fin k)
    -- the tree
    (t : Term S (Fin n ⊕ Fin m)) :
    (t.bind fun x => var (Sum.map id e x)).bind (fun x => var (Sum.map id e.symm x)) = t := by
  rw [Term.bind_bind]
  conv_rhs => rw [← Term.bind_var_self t]
  exact Term.bind_congr fun x _ => by cases x <;> simp

/-- `Iso` is reflexive. -/
theorem Iso.refl
    (p : PNet S n) :
    p.Iso p :=
  ⟨_root_.Equiv.refl (Fin p.internal), by
    conv_rhs => rw [← Term.bind_var_self p.tree]
    exact Term.bind_congr fun x _ => by cases x <;> rfl⟩

/-- `Iso` is symmetric. -/
theorem Iso.symm
    {p q : PNet S n}
    (h : p.Iso q) :
    q.Iso p := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by rw [← he]; exact bind_sumMap_symm e p.tree⟩

/-- `Iso` is transitive. -/
theorem Iso.trans
    -- three principal nets, the first two and the last two `Iso`
    {p q r : PNet S n}
    (h : p.Iso q)
    (h' : q.Iso r) :
    p.Iso r := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨e.trans e', ?_⟩
  rw [← he', ← he, Term.bind_bind]
  exact Term.bind_congr fun x _ => by cases x <;> rfl

/-- Principal nets that are `Iso` have the same root cell. -/
theorem Iso.root
    -- two principal nets that are `Iso`
    {p q : PNet S n}
    (h : p.Iso q)
    -- the tree of `p` has the cell `α` at its root
    {α : S.Sym}
    {ts : Fin (S.arity α) → Term S (Fin n ⊕ Fin p.internal)}
    (hp : p.tree = app α ts) :
    -- so has the tree of `q`
    ∃ ts', q.tree = app α ts' := by
  obtain ⟨e, he⟩ := h
  rw [← he, hp, bind_app]
  exact ⟨_, rfl⟩

/-- **`ofNat` of a renamed principal net** (pages 79–80): if `t` is the tree of `q` with the port
`i` named `i` and the internal wire `w` named `n + e w`, then `ofNat t` is `q` up to the names of
internal wires. -/
theorem iso_ofNat
    -- the principal net, and a numbering `e` of its internal wires
    (q : PNet S n)
    {m : ℕ}
    (e : Fin q.internal ≃ Fin m)
    -- a tree satisfying the hypotheses of `ofNat`
    {t : Term S ℕ}
    (hb : ∀ x ∈ t.vars, x < n + m)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ w < m, t.vars.count (n + w) = 2)
    -- the tree is that of `q`, the port `i` named `i`, the internal wire `w` named `n + e w`
    (ht : t = q.tree.bind fun x =>
      var (Sum.elim (fun i : Fin n => (i : ℕ)) (fun w => n + (e w : ℕ)) x)) :
    (ofNat n m t hb hp hw).Iso q := by
  have key : t = (q.tree.bind fun x => var (finSumFinEquiv (Sum.map id e x))).bind
      (fun x => var x.val) := by
    rw [ht, Term.bind_bind]
    exact Term.bind_congr fun x _ => by cases x <;> simp
  refine ⟨e.symm, ?_⟩
  change (((t.toFin hb).bind fun x => var (finSumFinEquiv.symm x)).bind
    fun x => var (Sum.map id e.symm x)) = q.tree
  rw [Term.toFin_eq hb key, Term.bind_bind, Term.bind_bind]
  conv_rhs => rw [← Term.bind_var_self q.tree]
  exact Term.bind_congr fun x _ => by cases x <;> simp

-- ============================================================================================
-- 5. The tree of a principal net over `ℕ`
-- ============================================================================================

/-- The names of the ports and internal wires of a principal net in `ℕ`: the port `i` is `i`, the
internal wire `w` is `n + w`. -/
def enc
    (p : PNet S n) :
    Fin n ⊕ Fin p.internal → ℕ :=
  Sum.elim (fun i => (i : ℕ)) (fun w => n + (w : ℕ))

/-- Distinct ports and internal wires get distinct names. -/
theorem enc_injective
    (p : PNet S n) :
    Function.Injective p.enc := by
  rintro (i | w) (j | v) h
  · exact congrArg Sum.inl (Fin.ext h)
  · change (i : ℕ) = n + (v : ℕ) at h
    omega
  · change n + (w : ℕ) = (j : ℕ) at h
    omega
  · exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel h))

/-- The names of the ports and internal wires are below `n + p.internal`. -/
theorem enc_lt
    -- a port or internal wire of `p`
    (p : PNet S n)
    (x : Fin n ⊕ Fin p.internal) :
    p.enc x < n + p.internal := by
  cases x with
  | inl i => simp only [enc, Sum.elim_inl]; omega
  | inr w => simp only [enc, Sum.elim_inr]; omega

/-- The tree of a principal net over `ℕ`, its port `i` named `i`, its internal wire `w` named
`n + w`. -/
def natTree
    (p : PNet S n) :
    Term S ℕ :=
  p.tree.bind fun x => var (p.enc x)

/-- The names of `natTree`: the ports and internal wires, named by `enc`. -/
theorem vars_natTree
    (p : PNet S n) :
    p.natTree.vars = p.tree.vars.map p.enc :=
  Term.vars_bind_var_map _ _

/-- The names of `natTree` are below `n + p.internal`. -/
theorem natTree_lt
    (p : PNet S n) :
    ∀ x ∈ p.natTree.vars, x < n + p.internal := by
  intro x hx
  rw [vars_natTree, Multiset.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact p.enc_lt y

/-- In `natTree`, the name of a port occurs once and that of an internal wire twice, as in the
principal net. -/
theorem count_natTree_enc
    -- a port or internal wire of `p`
    (p : PNet S n)
    (x : Fin n ⊕ Fin p.internal) :
    p.natTree.vars.count (p.enc x) = p.tree.vars.count x := by
  rw [vars_natTree, Multiset.count_map_eq_count' _ _ p.enc_injective]

end PNet

namespace Translation

open PNet

-- ============================================================================================
-- 6. Definitions: the translation of a principal net, composition, invertibility
-- ============================================================================================

variable {n : ℕ}

/-- The hypotheses of `ofNat` for the translation of `natTree` (page 80): its names are below
`n + p.internal + Ψ.size`, the ports occur once, and the internal wires of `p` and of the new
instances twice. -/
theorem trPNet_hyps
    -- the translation and the principal net
    (Ψ : Translation S' S'')
    (p : PNet S' n) :
    -- the names of the translated tree are below `n + (p.internal + Ψ.size)`,
    (∀ x ∈ (Ψ.trTerm (n + p.internal) p.natTree).vars,
        x < n + (p.internal + Ψ.size p.natTree)) ∧
      -- a port occurs once,
      (∀ i < n, (Ψ.trTerm (n + p.internal) p.natTree).vars.count i = 1) ∧
      -- and an internal wire, of `p` or of a new instance, twice
      (∀ w < p.internal + Ψ.size p.natTree,
        (Ψ.trTerm (n + p.internal) p.natTree).vars.count (n + w) = 2) := by
  have hv := Ψ.vars_trTerm (n + p.internal) p.natTree
  refine ⟨fun x hx => ?_, fun i hi => ?_, fun w hw => ?_⟩
  · rw [hv, two_nsmul, Multiset.mem_add, Multiset.mem_add, or_self] at hx
    rcases hx with hx | hx
    · have := p.natTree_lt x hx; omega
    · have := (Multiset.mem_Ico.1 hx).2; omega
  · rw [hv, Multiset.count_add, Multiset.count_nsmul, count_Ico]
    split_ifs with hc
    · omega
    have e : i = p.enc (.inl ⟨i, hi⟩) := rfl
    rw [e, p.count_natTree_enc, p.port_count]
  · rw [hv, Multiset.count_add, Multiset.count_nsmul, count_Ico]
    split_ifs with hc
    · rw [Multiset.count_eq_zero_of_notMem (fun hm => by have := p.natTree_lt _ hm; omega)]
    · have hw' : w < p.internal := by omega
      have e : n + w = p.enc (.inr ⟨w, hw'⟩) := rfl
      rw [e, p.count_natTree_enc, p.internal_count]

/-- **The translation `Ψ(p)` of a principal net** (page 80): `Ψ` applied to the tree of `p`, the
port `i` of `p` named `i`, its internal wire `w` named `n + w`, and the internal wires of the new
instances numbered from `n + p.internal`. It has `p.internal + Ψ.size` internal wires: those of
`p`, then those of the instances. -/
def trPNet
    -- the translation and the principal net
    (Ψ : Translation S' S'')
    (p : PNet S' n) :
    PNet S'' n :=
  PNet.ofNat n (p.internal + Ψ.size p.natTree) (Ψ.trTerm (n + p.internal) p.natTree)
    (Ψ.trPNet_hyps p).1 (Ψ.trPNet_hyps p).2.1 (Ψ.trPNet_hyps p).2.2

/-- **Composition of translations** (page 80, "composition of translations is defined in the
obvious way"): `Ψ ∘ Φ` translates the symbol `α` to `Ψ(Φ(α))`, the translation by `Ψ` of the
principal net `Φ(α)`. -/
def comp
    -- `Φ` is applied first, then `Ψ`
    (Ψ : Translation S' S'')
    (Φ : Translation S S') :
    Translation S S'' :=
  ⟨fun α => Ψ.trPNet (Φ.net α)⟩

/-- **Invertible translation** (pages 80–81): there is a translation `Φ⁻¹` of `S'` into `S` with
`Φ⁻¹ ∘ Φ = id_S` and `Φ ∘ Φ⁻¹ = id_S'`. The principal nets are graphs, so these equations are read
as equality up to the names of internal wires (`PNet.Iso`) at every symbol. -/
def Invertible
    (Φ : Translation S S') :
    Prop :=
  -- there is a translation `Ψ` back
  ∃ Ψ : Translation S' S,
    -- such that `Ψ ∘ Φ = id_S`, symbol by symbol,
    (∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α)) ∧
    -- and `Φ ∘ Ψ = id_S'`, symbol by symbol
    ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α')

-- ============================================================================================
-- 7. Main results: the identity is neutral and invertible
-- ============================================================================================

/-- The identity translation uses no new internal wire (page 80). -/
theorem id_size
    (t : Term S ℕ) :
    (Translation.id S).size t = 0 := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    change 0 + ∑ i, (Translation.id S).size (ts i) = 0
    simp [ih]

/-- The identity translation of a tree is the tree (page 80). -/
theorem id_trTerm
    -- the first name of the new wires, and the tree
    (k : ℕ)
    (t : Term S ℕ) :
    (Translation.id S).trTerm k t = t := by
  induction t generalizing k with
  | var x => rfl
  | app α ts ih =>
    change app α _ = app α ts
    congr 1
    funext i
    exact ih i _

/-- **`Φ ∘ id = Φ`** (page 80): the translation by `Φ` of the single cell `α` is `Φ(α)`, up to the
names of internal wires. -/
theorem comp_id
    -- the translation and a symbol
    (Φ : Translation S S')
    (α : S.Sym) :
    ((Φ.comp (Translation.id S)).net α).Iso (Φ.net α) := by
  have hm : (Φ.net α).internal =
      0 + ((Φ.net α).internal + ∑ i : Fin (S.arity α), Φ.size (var (i : ℕ))) := by
    simp [size]
  have hy := Φ.trPNet_hyps ((Translation.id S).net α)
  refine iso_ofNat (Φ.net α) (finCongr hm) hy.1 hy.2.1 hy.2.2 ?_
  change (Φ.net α).tree.bind _ = _
  exact Term.bind_congr fun x _ => by cases x <;> simp [enc] <;> rfl

/-- **`id ∘ Φ = Φ`** (page 80): the translation of `Φ(α)` by the identity is `Φ(α)`, up to the
names of internal wires. -/
theorem id_comp
    -- the translation and a symbol
    (Φ : Translation S S')
    (α : S.Sym) :
    (((Translation.id S').comp Φ).net α).Iso (Φ.net α) := by
  have hm : (Φ.net α).internal =
      (Φ.net α).internal + (Translation.id S').size (Φ.net α).natTree := by
    rw [id_size, Nat.add_zero]
  have hy := (Translation.id S').trPNet_hyps (Φ.net α)
  refine iso_ofNat (Φ.net α) (finCongr hm) hy.1 hy.2.1 hy.2.2 ?_
  rw [id_trTerm]
  exact Term.bind_congr fun x _ => by cases x <;> simp [enc]

/-- **The identity is invertible** (pages 80–81), its own inverse: `id ∘ id = id`. -/
theorem invertible_id
    (S : Signature) :
    (Translation.id S).Invertible :=
  ⟨Translation.id S, fun α => comp_id _ α, fun α => comp_id _ α⟩

end Translation

end INet
