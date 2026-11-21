/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphContract

/-!
# The order of erasing names does not matter

Lafont 1997, Section 1.1, page 71: a name is a wire. Reading a text as a graph, a name that
occurs twice ends two wires, and it is erased by joining them (`Graph.Contract`). This file shows
that when every name ends at most two wires, as in the raw graph of a linear text, the graph
obtained by erasing names does not depend on the order in which they are erased.

The hypothesis "at most two ends" is needed: `Checks/Core/GraphReview.lean`, `threeText`.

Contents, in the order of the file:

1. Definition: `Graph.EraseName x A B d`, erasing the name `x` from the multiset of wires `A`
   gives `B`, and `d` new cyclic wires (`0` or `1`).
2. A contraction is the erasure of one name: `ext_fields`, `contract_iff`.
3. Counting ends: `bind_join`, `bind_loop`, `EraseName.two_le` (an erased name ends two wires),
   `exists_wire_of_mem'`, `exists_eraseName` (a name that ends two wires can be erased),
   `EraseName.cons`.
4. Erasing one name has one result: `pair_wires`, `EraseName.shape`, `EraseName.unique` (if `x`
   ends at most two wires, the two wires at `x` are determined).
5. Erasures at two names commute: `comm_shared`, `EraseName.comm`. The cases are the wire
   `s(x, y)` shared by the two names, and the two wires `s(x, y), s(x, y)` forming a cycle.
6. The local diamond: `Contract.count_name_le_two` (contraction keeps "every name ends at most
   two wires"), `Contract.diamond`, `not_contract`.
7. Main results: `Graph.contracts_unique`, two sequences of contractions that end where every
   name ends at most one wire end at the same graph (equality, not only `Iso`: contraction
   renumbers nothing); `Net.Linear.contracts_unique`, the same for the raw graph of a text of a
   linear net.
-/

@[expose] public section

namespace INet

variable {S : Signature} {ν : Type}

namespace Graph

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- Erasing the name `x` from the wires `A` gives the wires `B` and `d` new cyclic wires
(Lafont 1997, page 71): either two wires `s(x, p)`, `s(x, q)` are joined into `s(p, q)`, or the
wire `s(x, x)` becomes a cyclic wire. -/
inductive EraseName (x : ν) : Multiset (Sym2 (End ν)) → Multiset (Sym2 (End ν)) → ℕ → Prop
  -- the two wires `s(x, p)` and `s(x, q)` become the wire `s(p, q)`, and no cyclic wire
  | join (p q : End ν) (W : Multiset (Sym2 (End ν))) :
      EraseName x (s(.name x, p) ::ₘ s(.name x, q) ::ₘ W) (s(p, q) ::ₘ W) 0
  -- the wire `s(x, x)` becomes one cyclic wire
  | loop (W : Multiset (Sym2 (End ν))) : EraseName x (s(.name x, .name x) ::ₘ W) W 1

-- ============================================================================================
-- 2. A contraction is the erasure of one name
-- ============================================================================================

/-- Two graphs with the same fields are equal. -/
private theorem ext_fields
    -- two graphs
    {G H : Graph S ν}
    -- with the same cells, the same wires and the same number of cyclic wires
    (hc : G.cells = H.cells)
    (hw : G.wires = H.wires)
    (hl : G.loops = H.loops) :
    G = H := by
  obtain ⟨C, W, n⟩ := G
  obtain ⟨C', W', n'⟩ := H
  simp only at hc hw hl
  subst hc hw hl
  rfl

/-- **A contraction is the erasure of one name** (Lafont 1997, page 71): it keeps the cells, and
erases a name `x` from the wires, adding the cyclic wires that the erasure creates. -/
theorem contract_iff
    -- two graphs
    {G H : Graph S ν} :
    -- `H` is a contraction of `G` if and only if
    Contract G H ↔
      -- the cells are the same,
      H.cells = G.cells ∧
      -- and for some name `x`, erasing `x` from the wires of `G` gives those of `H` and `d`
      -- cyclic wires, which `H` has in addition to those of `G`
      ∃ x d, EraseName x G.wires H.wires d ∧ H.loops = G.loops + d := by
  constructor
  · intro h
    cases h with
    | join x p q C W n => exact ⟨rfl, x, 0, .join p q W, rfl⟩
    | loop x C W n => exact ⟨rfl, x, 1, .loop W, rfl⟩
  · obtain ⟨C, WG, n⟩ := G
    obtain ⟨C', WH, n'⟩ := H
    rintro ⟨hc, x, d, h, hl⟩
    simp only at hc h hl
    subst hc hl
    cases h with
    | join p q W => exact .join x p q _ _ _
    | loop W => exact .loop x _ _ _

-- ============================================================================================
-- 3. Counting ends
-- ============================================================================================

/-- The ends of two wires at `x`, and of the others. -/
private theorem bind_join
    -- the name, the other ends of its two wires, and the other wires
    (x : ν)
    (p q : End ν)
    (W : Multiset (Sym2 (End ν))) :
    (s(.name x, p) ::ₘ s(.name x, q) ::ₘ W).bind wireEnds
      = .name x ::ₘ .name x ::ₘ p ::ₘ q ::ₘ W.bind wireEnds := by
  simp only [Multiset.cons_bind, wireEnds_mk, Multiset.insert_eq_cons, Multiset.cons_add,
    Multiset.singleton_add]
  exact congrArg (End.name x ::ₘ ·) (Multiset.cons_swap _ _ _)

/-- The ends of a wire from `x` to itself, and of the others. -/
private theorem bind_loop
    -- the name and the other wires
    (x : ν)
    (W : Multiset (Sym2 (End ν))) :
    (s(.name x, .name x) ::ₘ W).bind wireEnds = .name x ::ₘ .name x ::ₘ W.bind wireEnds := by
  simp only [Multiset.cons_bind, wireEnds_mk, Multiset.insert_eq_cons, Multiset.cons_add,
    Multiset.singleton_add]

/-- A name that is erased ends at least two wires (Lafont 1997, page 71). -/
theorem EraseName.two_le
    [DecidableEq ν]
    -- an erasure of the name `x` from the wires `A`
    {x : ν}
    {A B : Multiset (Sym2 (End ν))}
    {d : ℕ}
    (h : EraseName x A B d) :
    -- `x` occurs at least twice among the ends of the wires of `A`
    2 ≤ (A.bind wireEnds).count (.name x) := by
  cases h with
  | join p q W =>
    rw [bind_join, Multiset.count_cons_self, Multiset.count_cons_self]
    omega
  | loop W =>
    rw [bind_loop, Multiset.count_cons_self, Multiset.count_cons_self]
    omega

/-- A name that is an end of one of the wires: the wires are that wire and the others. -/
private theorem exists_wire_of_mem'
    -- the wires, and a name among their ends
    {W : Multiset (Sym2 (End ν))}
    {x : ν}
    (h : End.name x ∈ W.bind wireEnds) :
    -- there is a wire `s(x, p)` among them, and the others `W'`
    ∃ p W', W = s(.name x, p) ::ₘ W' := by
  obtain ⟨w, hw, hxw⟩ := Multiset.mem_bind.1 h
  obtain ⟨W', rfl⟩ := Multiset.exists_cons_of_mem hw
  induction w using Sym2.ind with
  | _ a b =>
    simp only [wireEnds_mk, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hxw
    rcases hxw with rfl | rfl
    · exact ⟨b, W', rfl⟩
    · exact ⟨a, W', by rw [Sym2.eq_swap]⟩

/-- **A name that ends two wires can be erased** (Lafont 1997, page 71). -/
theorem exists_eraseName
    [DecidableEq ν]
    -- the name `x`, which occurs at least twice among the ends of the wires `A`
    {x : ν}
    {A : Multiset (Sym2 (End ν))}
    (hx : 2 ≤ (A.bind wireEnds).count (.name x)) :
    -- erasing `x` from `A` gives some wires `B` and `d` cyclic wires
    ∃ B d, EraseName x A B d := by
  have h1 : 0 < (A.bind wireEnds).count (.name x) := by omega
  obtain ⟨p, W', rfl⟩ := exists_wire_of_mem' (Multiset.count_pos.1 h1)
  by_cases hp : p = .name x
  · subst hp
    exact ⟨_, _, .loop W'⟩
  · rw [Multiset.cons_bind, Multiset.count_add, wireEnds_mk, Multiset.insert_eq_cons,
      Multiset.count_cons_self, Multiset.count_singleton] at hx
    simp only [Ne.symm hp, ite_false] at hx
    have h2 : 0 < (W'.bind wireEnds).count (.name x) := by omega
    obtain ⟨q, W'', rfl⟩ := exists_wire_of_mem' (Multiset.count_pos.1 h2)
    exact ⟨_, _, .join p q W''⟩

/-- Erasing a name commutes with adding a wire elsewhere. -/
theorem EraseName.cons
    -- an erasure of the name `x` from the wires `A`
    {x : ν}
    {A B : Multiset (Sym2 (End ν))}
    {d : ℕ}
    (h : EraseName x A B d)
    -- one more wire
    (w : Sym2 (End ν)) :
    -- the erasure is still possible with `w` added on both sides
    EraseName x (w ::ₘ A) (w ::ₘ B) d := by
  cases h with
  | join p q W =>
    rw [Multiset.cons_swap w s(.name x, p), Multiset.cons_swap w s(.name x, q),
      Multiset.cons_swap w s(p, q)]
    exact .join p q _
  | loop W =>
    rw [Multiset.cons_swap w s(.name x, .name x)]
    exact .loop _

-- ============================================================================================
-- 4. Erasing one name has one result
-- ============================================================================================

/-- Two pairs of wires at `x` that are equal have the same other ends, up to order. -/
private theorem pair_wires
    -- the name and the other ends of the two pairs of wires
    {x : ν}
    {p q p' q' : End ν}
    -- the two pairs are the same multiset
    (h : s(End.name x, p) ::ₘ {s(.name x, q)} = s(.name x, p') ::ₘ {s(.name x, q')}) :
    s(p, q) = s(p', q') := by
  rcases Multiset.cons_eq_cons.1 h with ⟨h1, h2⟩ | ⟨_, cs, h1, h2⟩
  · rw [Multiset.singleton_inj] at h2
    rw [Sym2.congr_right.1 h1, Sym2.congr_right.1 h2]
  · rw [Multiset.singleton_eq_cons_iff] at h1 h2
    rw [Sym2.congr_right.1 h1.1, ← Sym2.congr_right.1 h2.1, Sym2.eq_swap]

/-- The wires at `x` and the other wires, when `x` ends exactly the wires of an erasure. -/
private theorem EraseName.shape
    [DecidableEq ν]
    -- the name `x`, which occurs at most twice among the ends of the wires `A`
    {x : ν}
    {A B : Multiset (Sym2 (End ν))}
    {d : ℕ}
    (hx : (A.bind wireEnds).count (.name x) ≤ 2)
    -- an erasure of `x` from `A`
    (h : EraseName x A B d) :
    -- either no cyclic wire is made, the wires at `x` are `s(x, p)`, `s(x, q)`, and `B` is
    -- `s(p, q)` and the other wires,
    (d = 0 ∧ ∃ p q, A.filter (fun w => End.name x ∈ wireEnds w) =
        s(.name x, p) ::ₘ {s(.name x, q)} ∧
      B = s(p, q) ::ₘ A.filter (fun w => End.name x ∉ wireEnds w)) ∨
    -- or one cyclic wire is made, the only wire at `x` is `s(x, x)`, and `B` is the other wires
    (d = 1 ∧ A.filter (fun w => End.name x ∈ wireEnds w) = {s(.name x, .name x)} ∧
      B = A.filter (fun w => End.name x ∉ wireEnds w)) := by
  have none : ∀ W : Multiset (Sym2 (End ν)), (W.bind wireEnds).count (.name x) = 0 →
      W.filter (fun w => End.name x ∈ wireEnds w) = 0 ∧
        W.filter (fun w => End.name x ∉ wireEnds w) = W := by
    intro W hW
    have hm : ∀ w ∈ W, End.name x ∉ wireEnds w := fun w hw hxw =>
      Multiset.count_eq_zero.1 hW (Multiset.mem_bind.2 ⟨w, hw, hxw⟩)
    exact ⟨Multiset.filter_eq_nil.2 hm, Multiset.filter_eq_self.2 hm⟩
  set P : Sym2 (End ν) → Prop := fun w => End.name x ∈ wireEnds w with hP
  set Q : Sym2 (End ν) → Prop := fun w => End.name x ∉ wireEnds w with hQ
  have mem : ∀ p : End ν, End.name x ∈ wireEnds s(.name x, p) := fun p => by simp
  cases h with
  | join p q W =>
    rw [bind_join, Multiset.count_cons_self, Multiset.count_cons_self] at hx
    have h0 : (p ::ₘ q ::ₘ W.bind wireEnds).count (.name x) = 0 := by omega
    have hp : End.name x ≠ p := fun e => by rw [← e, Multiset.count_cons_self] at h0; omega
    have hq : End.name x ≠ q := fun e => by
      rw [← e, Multiset.count_cons_of_ne hp, Multiset.count_cons_self] at h0; omega
    rw [Multiset.count_cons_of_ne hp, Multiset.count_cons_of_ne hq] at h0
    obtain ⟨f1, f2⟩ := none W h0
    refine .inl ⟨rfl, p, q, ?_, ?_⟩
    · rw [Multiset.filter_cons_of_pos (p := P) _ (mem p),
        Multiset.filter_cons_of_pos (p := P) _ (mem q), f1]
      rfl
    · rw [Multiset.filter_cons_of_neg (p := Q) _ (not_not.2 (mem p)),
        Multiset.filter_cons_of_neg (p := Q) _ (not_not.2 (mem q)), f2]
  | loop W =>
    rw [bind_loop, Multiset.count_cons_self, Multiset.count_cons_self] at hx
    obtain ⟨f1, f2⟩ := none B (by omega)
    refine .inr ⟨rfl, ?_, ?_⟩
    · rw [Multiset.filter_cons_of_pos (p := P) _ (mem _), f1]
      rfl
    · rw [Multiset.filter_cons_of_neg (p := Q) _ (not_not.2 (mem _)), f2]

/-- **Erasing a name that ends at most two wires has one result** (Lafont 1997, page 71): the
wires at the name are determined, and so is what they become. -/
theorem EraseName.unique
    [DecidableEq ν]
    -- the name `x`, which occurs at most twice among the ends of the wires `A`
    {x : ν}
    {A B B' : Multiset (Sym2 (End ν))}
    {d d' : ℕ}
    (hx : (A.bind wireEnds).count (.name x) ≤ 2)
    -- two erasures of `x` from `A`
    (h : EraseName x A B d)
    (h' : EraseName x A B' d') :
    -- they give the same wires and the same number of cyclic wires
    B = B' ∧ d = d' := by
  rcases h.shape hx with ⟨rfl, p, q, f, rfl⟩ | ⟨rfl, f, rfl⟩ <;>
    rcases h'.shape hx with ⟨rfl, p', q', f', rfl⟩ | ⟨rfl, f', rfl⟩
  · exact ⟨by rw [pair_wires (f.symm.trans f')], rfl⟩
  · have := congrArg Multiset.card (f.symm.trans f')
    simp at this
  · have := congrArg Multiset.card (f.symm.trans f')
    simp at this
  · exact ⟨rfl, rfl⟩

-- ============================================================================================
-- 5. Erasures at two names commute
-- ============================================================================================

/-- Two names `x ≠ y` that share the wire `s(x, y)`: erasing `x`, then `y`, or `y`, then `x`,
gives the same wires. -/
private theorem comm_shared
    [DecidableEq ν]
    -- two different names
    {x y : ν}
    (hxy : x ≠ y)
    -- the other end `q ≠ y` of the second wire at `x`, and the other wires
    (q : End ν)
    (W : Multiset (Sym2 (End ν)))
    (hq : q ≠ .name y)
    -- `y` ends at least two of the wires `s(x, y)`, `s(x, q)` and `W`
    (hy : 2 ≤ ((s(.name x, .name y) ::ₘ s(.name x, q) ::ₘ W).bind wireEnds).count (.name y)) :
    -- there are wires `B₂`, `K` and numbers of cyclic wires `d₂`, `e₁`, `e₂` such that
    ∃ B₂ d₂ K e₁ e₂,
      -- erasing `y` first gives `B₂` and `d₂` cyclic wires,
      EraseName y (s(.name x, .name y) ::ₘ s(.name x, q) ::ₘ W) B₂ d₂ ∧
      -- erasing `y` after `x` gives `K` and `e₁` cyclic wires,
      EraseName y (s(.name y, q) ::ₘ W) K e₁ ∧
      -- erasing `x` after `y` gives `K` too, and `e₂` cyclic wires,
      EraseName x B₂ K e₂ ∧
      -- and both orders make as many cyclic wires
      0 + e₁ = d₂ + e₂ := by
  have hyx : End.name y ≠ (End.name x : End ν) := fun e => hxy (End.name.inj e).symm
  rw [bind_join, Multiset.count_cons_of_ne hyx, Multiset.count_cons_of_ne hyx,
    Multiset.count_cons_self, Multiset.count_cons_of_ne (Ne.symm hq)] at hy
  obtain ⟨t, W₀, rfl⟩ := exists_wire_of_mem' (Multiset.count_pos.1 (by omega : 0 <
    (W.bind wireEnds).count (.name y)))
  refine ⟨s(.name x, t) ::ₘ s(.name x, q) ::ₘ W₀, 0, s(q, t) ::ₘ W₀, 0, 0, ?_, .join q t W₀, ?_,
    rfl⟩
  · have e : s(.name x, .name y) ::ₘ s(.name x, q) ::ₘ s(.name y, t) ::ₘ W₀ =
        s(.name y, .name x) ::ₘ s(.name y, t) ::ₘ s(.name x, q) ::ₘ W₀ := by
      rw [Sym2.eq_swap (a := End.name x) (b := End.name y),
        Multiset.cons_swap s(.name x, q) s(.name y, t)]
    rw [e]
    exact .join (.name x) t _
  · rw [Sym2.eq_swap (a := q)]
    exact .join t q W₀

/-- **Erasures at two different names commute** (Lafont 1997, page 71): if `x ≠ y`, `x` is
erased from `A`, and `y` ends two wires of `A`, then `y` can be erased from `A` and from the
result, `x` from the result of erasing `y`, and both orders give the same wires and the same
number of cyclic wires. -/
theorem EraseName.comm
    [DecidableEq ν]
    -- two different names
    {x y : ν}
    (hxy : x ≠ y)
    -- an erasure of `x` from the wires `A`, giving `B` and `d` cyclic wires
    {A B : Multiset (Sym2 (End ν))}
    {d : ℕ}
    (h : EraseName x A B d)
    -- `y` occurs at least twice among the ends of the wires of `A`
    (hy : 2 ≤ (A.bind wireEnds).count (.name y)) :
    -- there are wires `B₂`, `K` and numbers of cyclic wires `d₂`, `e₁`, `e₂` such that
    ∃ B₂ d₂ K e₁ e₂,
      -- erasing `y` from `A` gives `B₂` and `d₂` cyclic wires,
      EraseName y A B₂ d₂ ∧
      -- erasing `y` from `B` gives `K` and `e₁` cyclic wires,
      EraseName y B K e₁ ∧
      -- erasing `x` from `B₂` gives `K` too, and `e₂` cyclic wires,
      EraseName x B₂ K e₂ ∧
      -- and both orders make as many cyclic wires
      d + e₁ = d₂ + e₂ := by
  have hyx : End.name y ≠ (End.name x : End ν) := fun e => hxy (End.name.inj e).symm
  cases h with
  | loop W =>
    rw [bind_loop, Multiset.count_cons_of_ne hyx, Multiset.count_cons_of_ne hyx] at hy
    obtain ⟨W', e, hW⟩ := exists_eraseName hy
    exact ⟨_, e, W', e, 1, hW.cons _, hW, .loop W', by omega⟩
  | join p q W =>
    by_cases hp : p = .name y <;> by_cases hq : q = .name y
    · subst hp hq
      refine ⟨s(.name x, .name x) ::ₘ W, 0, W, 1, 1, ?_, .loop W, .loop W, rfl⟩
      have := EraseName.join (x := y) (.name x) (.name x) W
      rwa [Sym2.eq_swap (a := End.name y) (b := End.name x)] at this
    · subst hp
      exact comm_shared hxy q W hq hy
    · subst hq
      rw [Multiset.cons_swap, Sym2.eq_swap (a := p)]
      rw [Multiset.cons_swap] at hy
      exact comm_shared hxy p W hp hy
    · rw [bind_join, Multiset.count_cons_of_ne hyx, Multiset.count_cons_of_ne hyx,
        Multiset.count_cons_of_ne (Ne.symm hp), Multiset.count_cons_of_ne (Ne.symm hq)] at hy
      obtain ⟨W', e, hW⟩ := exists_eraseName hy
      exact ⟨_, e, s(p, q) ::ₘ W', e, 0, (hW.cons _).cons _, hW.cons _, .join p q W', by omega⟩

-- ============================================================================================
-- 6. The local diamond
-- ============================================================================================

/-- **Contraction keeps "every name ends at most two wires"** (Lafont 1997, page 71). -/
theorem Contract.count_name_le_two
    [DecidableEq ν]
    -- a contraction from `G` to `H`
    {G H : Graph S ν}
    (h : Contract G H)
    -- every name ends at most two wires of `G`
    (h2 : ∀ x, G.ends.count (.name x) ≤ 2)
    -- a name
    (x : ν) :
    -- it ends at most two wires of `H`
    H.ends.count (.name x) ≤ 2 :=
  (Multiset.count_le_of_le _ h.ends_le).trans (h2 x)

/-- **The local diamond** (Lafont 1997, page 71): if every name of `G` ends at most two wires,
two contractions of `G` give the same graph, or can be closed by one contraction each. -/
theorem Contract.diamond
    [DecidableEq ν]
    -- a graph `G` where every name ends at most two wires, and two graphs
    {G H₁ H₂ : Graph S ν}
    (h2 : ∀ x, G.ends.count (.name x) ≤ 2)
    -- two contractions of `G`
    (h₁ : Contract G H₁)
    (h₂ : Contract G H₂) :
    -- either they give the same graph,
    H₁ = H₂ ∨
    -- or one more contraction of each gives the same graph `K`
    ∃ K, Contract H₁ K ∧ Contract H₂ K := by
  obtain ⟨c₁, x, d, e₁, l₁⟩ := contract_iff.1 h₁
  obtain ⟨c₂, y, d', e₂, l₂⟩ := contract_iff.1 h₂
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨hw, hd⟩ := e₁.unique (h2 x) e₂
    exact .inl (ext_fields (c₁.trans c₂.symm) hw (by omega))
  · obtain ⟨B₂, d₂, K, f₁, f₂, g₂, k₁, k₂, hd⟩ := e₁.comm hxy e₂.two_le
    obtain ⟨rfl, rfl⟩ := g₂.unique (h2 y) e₂
    refine .inr ⟨⟨G.cells, K, G.loops + d + f₁⟩, contract_iff.2 ⟨c₁.symm, y, f₁, k₁, ?_⟩,
      contract_iff.2 ⟨c₂.symm, x, f₂, k₂, ?_⟩⟩
    · change G.loops + d + f₁ = H₁.loops + f₁
      omega
    · change G.loops + d + f₁ = H₂.loops + f₂
      omega

/-- A graph in which every name ends at most one wire has no contraction (Lafont 1997,
page 71). -/
theorem not_contract
    [DecidableEq ν]
    -- a graph `G` where every name ends at most one wire, and a graph `H`
    {G H : Graph S ν}
    (hG : ∀ x, G.ends.count (.name x) ≤ 1) :
    -- `H` is not a contraction of `G`
    ¬ Contract G H := fun h => by
  obtain ⟨x, hx⟩ := h.ends_eq
  have := hG x
  rw [hx, Multiset.count_cons_self, Multiset.count_cons_self] at this
  omega

-- ============================================================================================
-- 7. Main results: the order of contraction does not matter
-- ============================================================================================

/-- **Contraction has a unique result** (Lafont 1997, page 71; the order of erasing names): if
every name of `G` ends at most two wires, two sequences of contractions from `G` that both reach
a graph in which every name ends at most one wire reach the same graph. -/
theorem contracts_unique
    [DecidableEq ν]
    -- a graph `G` where every name ends at most two wires, and two graphs
    {G H₁ H₂ : Graph S ν}
    (h2 : ∀ x, G.ends.count (.name x) ≤ 2)
    -- two sequences of contractions from `G`
    (h₁ : Relation.ReflTransGen Contract G H₁)
    (h₂ : Relation.ReflTransGen Contract G H₂)
    -- each ending where every name ends at most one wire
    (n₁ : ∀ x, H₁.ends.count (.name x) ≤ 1)
    (n₂ : ∀ x, H₂.ends.count (.name x) ≤ 1) :
    -- they end at the same graph
    H₁ = H₂ := by
  suffices ∀ m, ∀ G : Graph S ν, Multiset.card G.ends = m → (∀ x, G.ends.count (.name x) ≤ 2) →
      ∀ H₁ H₂, Relation.ReflTransGen Contract G H₁ → Relation.ReflTransGen Contract G H₂ →
        (∀ x, H₁.ends.count (.name x) ≤ 1) → (∀ x, H₂.ends.count (.name x) ≤ 1) → H₁ = H₂ from
    this _ G rfl h2 H₁ H₂ h₁ h₂ n₁ n₂
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro G hG h2 H₁ H₂ h₁ h₂ n₁ n₂
    rcases Relation.ReflTransGen.cases_head h₁ with rfl | ⟨G₁, s₁, r₁⟩
    · rcases Relation.ReflTransGen.cases_head h₂ with rfl | ⟨G₂, s₂, -⟩
      · rfl
      · exact absurd s₂ (not_contract n₁)
    · rcases Relation.ReflTransGen.cases_head h₂ with rfl | ⟨G₂, s₂, r₂⟩
      · exact absurd s₁ (not_contract n₂)
      · have lt₁ : Multiset.card G₁.ends < m := by have := s₁.card_ends; omega
        have lt₂ : Multiset.card G₂.ends < m := by have := s₂.card_ends; omega
        rcases Contract.diamond h2 s₁ s₂ with rfl | ⟨K, k₁, k₂⟩
        · exact ih _ lt₁ G₁ rfl (s₁.count_name_le_two h2) H₁ H₂ r₁ r₂ n₁ n₂
        · obtain ⟨N, hN, nN⟩ := exists_contracts K
          rw [ih _ lt₁ G₁ rfl (s₁.count_name_le_two h2) H₁ N r₁ (.head k₁ hN) n₁ nN,
            ih _ lt₂ G₂ rfl (s₂.count_name_le_two h2) H₂ N r₂ (.head k₂ hN) n₂ nN]

end Graph

/-- **The graph of a text of a linear net does not depend on the order of contraction**
(Lafont 1997, page 71; the order of erasing names): if `N` is linear and `N = Net.ofList L`, two
graphs reached from the raw graph of `L` by contractions, in which every name ends at most one
wire, are equal. -/
theorem Net.Linear.contracts_unique
    [DecidableEq ν]
    -- a linear net `N`
    {N : Net S ν}
    (hN : N.Linear)
    -- a text `L` of `N`
    {L : List (Term S ν × Term S ν)}
    (hL : N = Net.ofList L)
    -- the number of the first cell of the raw graph of `L`, and two graphs
    (k : ℕ)
    {G G' : Graph S ν}
    -- two sequences of contractions from the raw graph of `L`
    (h : Relation.ReflTransGen Graph.Contract (Graph.raw k L) G)
    (h' : Relation.ReflTransGen Graph.Contract (Graph.raw k L) G')
    -- each ending where every name ends at most one wire
    (n : ∀ x, G.ends.count (.name x) ≤ 1)
    (n' : ∀ x, G'.ends.count (.name x) ≤ 1) :
    -- they end at the same graph
    G = G' :=
  Graph.contracts_unique (Graph.raw_count_name_le_two k L (hL ▸ hN)) h h' n n'

end INet
