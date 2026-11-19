/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# A packed checker for Farkas certificates

A Farkas certificate for a system of real linear inequalities `rᵢ(v) ≤ bᵢ` in a box
`lo k ≤ v k ≤ hi k` is a family of natural multipliers `zᵢ` such that the combined row
`∑ zᵢ rᵢ = ∑ₖ cₖ v k` satisfies `∑ₖ min(cₖ lo k, cₖ hi k) > ∑ zᵢ bᵢ`. Then no `v` in the box
satisfies every row.

This file gives a checker `check` for such certificates and its soundness theorem
`check_sound`. The checker is meant to be run by the kernel (`decide +kernel`) on certificates
with thousands of rows and variables, so it is written for kernel evaluation:

* The rows are tags `t : T` at the leaves of a balanced tree `WTree T` together with their
  multipliers; a caller-supplied builder `build : T → Option Row` turns a tag into a row.
* The coefficient vector `∑ zᵢ rᵢ` is kept as two natural numbers per chunk of variables
  (positive and negative parts), with the coefficient of variable `k` in a fixed-width slot of
  `W` bits. The chunks sit at the leaves of a sparse binary trie of depth `D` (`PackTrie`), so
  that no single natural number covers all variables. Rows and trees are summed over balanced
  trees, because the kernel evaluates lazily and a linear fold nests deeply.
* All kernel-evaluated functions are defined directly by recursors (in scratch measurements,
  structural recursion through `brecOn` took about 1.6 times as long to reduce) and are therefore
  `noncomputable`; they are evaluated only by the kernel.
* One pass computes `∑ zᵢ · (sum of the row's coefficients)` plus a penalty `2 ^ W` for every
  missing row and every variable index `≥ nv`. If this total is `< 2 ^ W`, every row builds,
  every index is in range and no slot sum overflows its `W` bits.
* The box sum is accumulated as an unnormalized fraction (`Frac`) by divide and conquer over the
  slots.

`checkWith W D` takes the trie depth `D` as a parameter (`2 ^ D` chunks of `nv / 2 ^ D + 1`
slots each); `check W` is `checkWith W 4`, and `checkWith_sound` holds for every `D`.

The soundness proof is geometry-free: `hrow` gives the rows, `hbox` the box, and
`check_sound` derives `False`.
-/

@[expose] public section

namespace Esgk.FarkasPackedCheck

open Finset

/-! ### Rows, weighted trees and boxes -/

/-- The row `∑_{(k,c) ∈ pos} c * v k - ∑_{(k,c) ∈ neg} c * v k ≤ rhs`. -/
structure Row where
  /-- entries `(k, c)` with coefficient `+c` on variable `k` -/
  pos : List (Nat × Nat)
  /-- entries `(k, c)` with coefficient `-c` on variable `k` -/
  neg : List (Nat × Nat)
  /-- the right-hand side -/
  rhs : Int

/-- `∑_{(k,c) ∈ E} c * v k`. -/
noncomputable def entrySum (E : List (Nat × Nat)) (v : Nat → ℝ) : ℝ :=
  (E.map fun e ↦ (e.2 : ℝ) * v e.1).sum

/-- The left-hand side `∑_{(k,c) ∈ pos} c * v k - ∑_{(k,c) ∈ neg} c * v k` of a row. -/
noncomputable def Row.lhs (r : Row) (v : Nat → ℝ) : ℝ := entrySum r.pos v - entrySum r.neg v

/-- The point `v` satisfies the row `r`. -/
def Row.Holds (r : Row) (v : Nat → ℝ) : Prop := r.lhs v ≤ r.rhs

/-- Weighted rows (multiplier `z`, row tag `t`), as a balanced tree. -/
inductive WTree (T : Type) where
  | leaf (z : Nat) (t : T)
  | node (l r : WTree T)

/-- Rational bounds for the variables `0, …, nv - 1`. -/
structure Box where
  /-- the number of variables -/
  nv : Nat
  /-- the lower bounds -/
  lo : Nat → Rat
  /-- the upper bounds -/
  hi : Nat → Rat

/-! ### Kernel-evaluated functions -/

/-- A sparse binary trie of natural numbers: `zero` stands for a subtree of zeros. A trie of
depth `d` holds the chunks `0, …, 2 ^ d - 1` (see `PackTrie.get`). -/
inductive PackTrie where
  | zero
  | leaf (x : Nat)
  | node (l r : PackTrie)

namespace PackTrie

/-- Add `x` to every leaf of `t` (a `zero` subtree becomes the leaf `x`). -/
noncomputable def addLeaf (x : Nat) (t : PackTrie) : PackTrie :=
  PackTrie.rec (motive := fun _ ↦ PackTrie) (leaf x) (fun y ↦ leaf (x + y))
    (fun _ _ il ir ↦ node il ir) t

/-- Leafwise sum of two tries. -/
noncomputable def add (s : PackTrie) : PackTrie → PackTrie :=
  PackTrie.rec (motive := fun _ ↦ PackTrie → PackTrie) (fun t ↦ t) (fun x t ↦ addLeaf x t)
    (fun a b iha ihb t ↦ PackTrie.rec (motive := fun _ ↦ PackTrie) (node a b)
      (fun y ↦ addLeaf y (node a b)) (fun c e _ _ ↦ node (iha c) (ihb e)) t) s

/-- The trie of depth `D` with value `x` at chunk `q` and zeros elsewhere. -/
noncomputable def single (D q x : Nat) : PackTrie :=
  Nat.rec (motive := fun _ ↦ Nat → PackTrie) (fun _ ↦ leaf x)
    (fun d ih q ↦ bif Nat.blt q (2 ^ d) then node (ih q) zero else node zero (ih (q - 2 ^ d)))
    D q

/-- The left subtree (a `zero` or a leaf is its own subtree). -/
noncomputable def left (t : PackTrie) : PackTrie :=
  PackTrie.rec (motive := fun _ ↦ PackTrie) zero leaf (fun l _ _ _ ↦ l) t

/-- The right subtree (a `zero` or a leaf is its own subtree). -/
noncomputable def right (t : PackTrie) : PackTrie :=
  PackTrie.rec (motive := fun _ ↦ PackTrie) zero leaf (fun _ r _ _ ↦ r) t

/-- The value of the leftmost leaf. -/
noncomputable def val (t : PackTrie) : Nat :=
  PackTrie.rec (motive := fun _ ↦ Nat) 0 (fun x ↦ x) (fun _ _ il _ ↦ il) t

/-- Whether the trie is `zero`. -/
noncomputable def isZero (t : PackTrie) : Bool :=
  PackTrie.rec (motive := fun _ ↦ Bool) true (fun _ ↦ false) (fun _ _ _ _ ↦ false) t

/-- The chunk `q` of a trie of depth `d` (proof-side semantics; a leaf above depth `0` is the
same value on all its chunks). -/
def get : Nat → PackTrie → Nat → Nat
  | _, zero, _ => 0
  | _, leaf x, _ => x
  | 0, node l _, q => get 0 l q
  | d + 1, node l r, q => if q < 2 ^ d then get d l q else get d r (q - 2 ^ d)

end PackTrie

/-- Combine adjacent elements with `f`; `p` is a pending element. -/
noncomputable def pairUp {α : Type} (f : α → α → α) (l : List α) : Option α → List α :=
  List.rec (motive := fun _ ↦ Option α → List α)
    (fun p ↦ Option.rec (motive := fun _ ↦ List α) [] (fun a ↦ [a]) p)
    (fun x _ ih p ↦
      Option.rec (motive := fun _ ↦ List α) (ih (some x)) (fun a ↦ f a x :: ih none) p)
    l

/-- Fold a list with `f` over a balanced tree (`d` rounds of `pairUp`, then a linear fold). -/
noncomputable def balFold {α : Type} (f : α → α → α) (e : α) (d : Nat) : List α → α :=
  Nat.rec (motive := fun _ ↦ List α → α) (fun l ↦ l.foldr f e)
    (fun _ ih l ↦ List.rec (motive := fun _ ↦ α) e
      (fun x xs _ ↦ List.rec (motive := fun _ ↦ α) x (fun _ _ _ ↦ ih (pairUp f l none)) xs) l) d

/-- `List.map`, by the recursor. -/
noncomputable def listMap {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ ↦ List β) [] (fun a _ ih ↦ f a :: ih) l

/-- The packed trie of `z` times the entries `E`: entry `(k, c)` adds `z * c` to slot `k % L` of
chunk `k / L`, slot `i` sitting at bit `W * i`. -/
noncomputable def packEntries (W L D z : Nat) (E : List (Nat × Nat)) : PackTrie :=
  balFold PackTrie.add .zero 64
    (listMap (fun e ↦ PackTrie.single D (e.1 / L) ((z * e.2) <<< (W * (e.1 % L)))) E)

/-- `∑_{(k,c) ∈ E} (z * c + [k ≥ nv] * 2 ^ W)`. -/
noncomputable def costEntries (W nv z : Nat) (E : List (Nat × Nat)) : Nat :=
  balFold Nat.add 0 64 (listMap (fun e ↦ z * e.2 + bif Nat.blt e.1 nv then 0 else 2 ^ W) E)

section Trees

variable {T : Type}

/-- Sum of tries over the leaves of a weighted tree. -/
noncomputable def WTree.sumTrie (f : Nat → T → PackTrie) (w : WTree T) : PackTrie :=
  WTree.rec (motive := fun _ ↦ PackTrie) f (fun _ _ il ir ↦ PackTrie.add il ir) w

/-- Sum of natural numbers over the leaves of a weighted tree. -/
noncomputable def WTree.sumNat (f : Nat → T → Nat) (w : WTree T) : Nat :=
  WTree.rec (motive := fun _ ↦ Nat) f (fun _ _ il ir ↦ Nat.add il ir) w

/-- Sum of integers over the leaves of a weighted tree. -/
noncomputable def WTree.sumInt (f : Nat → T → Int) (w : WTree T) : Int :=
  WTree.rec (motive := fun _ ↦ Int) f (fun _ _ il ir ↦ Int.add il ir) w

/-- The cost of a leaf: `∑ z * c` over its entries, plus `2 ^ W` for a missing row and for
every variable index `≥ nv`. -/
noncomputable def leafCost (W nv : Nat) (build : T → Option Row) (z : Nat) (t : T) : Nat :=
  Option.rec (motive := fun _ ↦ Nat) (2 ^ W)
    (fun r ↦ costEntries W nv z r.pos + costEntries W nv z r.neg) (build t)

/-- The packed trie of a leaf (`sel` picks the positive or the negative entries). -/
noncomputable def leafPack (W L D : Nat) (build : T → Option Row) (sel : Row → List (Nat × Nat))
    (z : Nat) (t : T) : PackTrie :=
  Option.rec (motive := fun _ ↦ PackTrie) .zero (fun r ↦ packEntries W L D z (sel r)) (build t)

/-- The weighted right-hand side `z * rhs` of a leaf. -/
noncomputable def leafRhs (build : T → Option Row) (z : Nat) (t : T) : Int :=
  Option.rec (motive := fun _ ↦ Int) 0 (fun r ↦ (z : Int) * r.rhs) (build t)

end Trees

/-- An unnormalized fraction `num / den`. -/
structure Frac where
  /-- the numerator -/
  num : Int
  /-- the denominator -/
  den : Nat

/-- Sum of fractions; the denominators are multiplied only when they differ. -/
def Frac.add (a b : Frac) : Frac :=
  bif Nat.beq a.den b.den then ⟨a.num + b.num, a.den⟩
  else ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

/-- The box minimum of `(p - n) * v k`: `(p - n) * lo k` if `p > n`, `(p - n) * hi k` if
`p < n`, and `0` if `p = n`. -/
def slotTerm (B : Box) (k p n : Nat) : Frac :=
  bif Nat.beq p n then ⟨0, 1⟩
  else bif Nat.blt n p then ⟨((p - n : Nat) : Int) * (B.lo k).num, (B.lo k).den⟩
  else ⟨-(((n - p : Nat) : Int) * (B.hi k).num), (B.hi k).den⟩

/-- Box sum over the slots `k, …, k + c - 1` of the packed pair `(p, n)`, linearly. -/
noncomputable def linSum (W : Nat) (B : Box) (c : Nat) : Nat → Nat → Nat → Frac :=
  Nat.rec (motive := fun _ ↦ Nat → Nat → Nat → Frac) (fun _ _ _ ↦ ⟨0, 1⟩)
    (fun _ ih k p n ↦
      Frac.add (slotTerm B k (p % 2 ^ W) (n % 2 ^ W)) (ih (k + 1) (p >>> W) (n >>> W))) c

/-- Box sum over the slots `k, …, k + cnt - 1` of the packed pair `(p, n)`, by divide and
conquer (`d` is fuel; `linSum` takes over when it runs out). -/
noncomputable def boxSum (W : Nat) (B : Box) (d : Nat) : Nat → Nat → Nat → Nat → Frac :=
  Nat.rec (motive := fun _ ↦ Nat → Nat → Nat → Nat → Frac) (fun cnt k p n ↦ linSum W B cnt k p n)
    (fun _ ih cnt k p n ↦
      bif Nat.ble cnt 1 then linSum W B cnt k p n
      else Frac.add (ih (cnt / 2) k (p % 2 ^ (W * (cnt / 2))) (n % 2 ^ (W * (cnt / 2))))
        (ih (cnt - cnt / 2) (k + cnt / 2) (p >>> (W * (cnt / 2))) (n >>> (W * (cnt / 2))))) d

/-- Box sum over the chunks `q, …, q + 2 ^ d - 1` of a pair of tries of depth `d`, with `L`
slots per chunk. -/
noncomputable def decodeTrie (W L : Nat) (B : Box) (d : Nat) : Nat → PackTrie → PackTrie → Frac :=
  Nat.rec (motive := fun _ ↦ Nat → PackTrie → PackTrie → Frac)
    (fun q tp tn ↦ boxSum W B 64 L (q * L) tp.val tn.val)
    (fun d ih q tp tn ↦ bif tp.isZero && tn.isZero then ⟨0, 1⟩
      else Frac.add (ih q tp.left tn.left) (ih (q + 2 ^ d) tp.right tn.right)) d

/-- The number of slots per chunk for `nv` variables in `2 ^ D` chunks. -/
def chunkLen (nv D : Nat) : Nat := nv / 2 ^ D + 1

/-- `β < num / den` (for `den > 0`). -/
def fracGt (β : Int) (F : Frac) : Bool := decide (β * (F.den : Int) < F.num)

/-- The checker with trie depth `D`: the leaf costs sum to less than `2 ^ W`, and the box sum
of the combined row exceeds `β = ∑ z * rhs`. -/
noncomputable def checkWith {T : Type} (W D : Nat) (B : Box) (build : T → Option Row)
    (w : WTree T) : Bool :=
  Nat.blt (w.sumNat (leafCost W B.nv build)) (2 ^ W) &&
  fracGt (w.sumInt (leafRhs build))
    (decodeTrie W (chunkLen B.nv D) B D 0
      (w.sumTrie (leafPack W (chunkLen B.nv D) D build Row.pos))
      (w.sumTrie (leafPack W (chunkLen B.nv D) D build Row.neg)))

/-- The checker with slot width `W` bits and trie depth `4`. -/
noncomputable def check {T : Type} (W : Nat) (B : Box) (build : T → Option Row) (w : WTree T) :
    Bool :=
  checkWith W 4 B build w

/-! ### Soundness: tries -/

namespace PackTrie

private theorem addLeaf_node (x : Nat) (l r : PackTrie) :
    addLeaf x (node l r) = node (addLeaf x l) (addLeaf x r) := rfl

private theorem get_zero (d q : Nat) : get d zero q = 0 := by cases d <;> rfl

private theorem get_leaf (d x q : Nat) : get d (leaf x) q = x := by cases d <;> rfl

private theorem get_node_zero (l r : PackTrie) (q : Nat) : get 0 (node l r) q = get 0 l q := rfl

private theorem get_node_succ (d : Nat) (l r : PackTrie) (q : Nat) :
    get (d + 1) (node l r) q = if q < 2 ^ d then get d l q else get d r (q - 2 ^ d) := rfl

private theorem get_addLeaf (x : Nat) (t : PackTrie) (d q : Nat) :
    get d (addLeaf x t) q = x + get d t q := by
  induction t generalizing d q with
  | zero => change get d (leaf x) q = x + get d zero q; rw [get_leaf, get_zero, Nat.add_zero]
  | leaf y => change get d (leaf (x + y)) q = x + get d (leaf y) q; rw [get_leaf, get_leaf]
  | node l r ihl ihr =>
    rw [addLeaf_node]
    cases d with
    | zero => rw [get_node_zero, get_node_zero, ihl]
    | succ d => rw [get_node_succ, get_node_succ]; split_ifs <;> simp [ihl, ihr]

private theorem get_add (s t : PackTrie) (d q : Nat) :
    get d (add s t) q = get d s q + get d t q := by
  induction s generalizing t d q with
  | zero => change get d t q = get d zero q + get d t q; rw [get_zero, Nat.zero_add]
  | leaf x => change get d (addLeaf x t) q = _; rw [get_addLeaf, get_leaf]
  | node a b iha ihb =>
    cases t with
    | zero => change get d (node a b) q = _; rw [get_zero, Nat.add_zero]
    | leaf y => change get d (addLeaf y (node a b)) q = _; rw [get_addLeaf, get_leaf, Nat.add_comm]
    | node c e =>
      change get d (node (add a c) (add b e)) q = _
      cases d with
      | zero => rw [get_node_zero, get_node_zero, get_node_zero, iha]
      | succ d =>
        rw [get_node_succ, get_node_succ, get_node_succ]; split_ifs <;> simp [iha, ihb]

private theorem le_of_blt_false {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  have h' : ¬ (Nat.blt a b = true) := by simp [h]
  rw [Nat.blt_eq] at h'; omega

private theorem lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

private theorem get_single (D : Nat) :
    ∀ q q' x : Nat, q < 2 ^ D → q' < 2 ^ D → get D (single D q' x) q = if q = q' then x else 0 := by
  induction D with
  | zero =>
    intro q q' x hq hq'
    have h1 : q = 0 := by simpa using hq
    have h2 : q' = 0 := by simpa using hq'
    subst h1; subst h2
    change get 0 (leaf x) 0 = _; simp [get_leaf]
  | succ D ih =>
    intro q q' x hq hq'
    have hp : 2 ^ (D + 1) = 2 ^ D + 2 ^ D := by rw [Nat.pow_succ]; omega
    change get (D + 1) (bif Nat.blt q' (2 ^ D) then node (single D q' x) zero
      else node zero (single D (q' - 2 ^ D) x)) q = _
    cases h : Nat.blt q' (2 ^ D) with
    | true =>
      have h' : q' < 2 ^ D := lt_of_blt_true h
      rw [Bool.cond_true, get_node_succ]
      split_ifs with h1 h2 h2
      · exact (ih q q' x h1 h').trans (ite_eq_left h2)
      · exact (ih q q' x h1 h').trans (ite_eq_right h2)
      · omega
      · exact get_zero _ _
    | false =>
      have h' : ¬ q' < 2 ^ D := Nat.not_lt.2 (le_of_blt_false h)
      rw [Bool.cond_false, get_node_succ]
      split_ifs with h1 h2 h2
      · omega
      · exact get_zero _ _
      · rw [ih (q - 2 ^ D) (q' - 2 ^ D) x (by omega) (by omega), ite_eq_left (by omega)]
      · rw [ih (q - 2 ^ D) (q' - 2 ^ D) x (by omega) (by omega), ite_eq_right (by omega)]

private theorem get_succ_eq (d : Nat) (t : PackTrie) (q : Nat) :
    get (d + 1) t q = if q < 2 ^ d then get d t.left q else get d t.right (q - 2 ^ d) := by
  cases t with
  | zero => change 0 = _; split_ifs <;> exact (get_zero _ _).symm
  | leaf x => change x = _; split_ifs <;> exact (get_leaf _ _ _).symm
  | node l r => rfl

private theorem get_zero_depth (t : PackTrie) (q : Nat) : get 0 t q = t.val := by
  induction t with
  | zero => rfl
  | leaf x => rfl
  | node l r ihl _ => exact ihl

private theorem eq_zero_of_isZero {t : PackTrie} (h : t.isZero = true) : t = zero := by
  cases t with
  | zero => rfl
  | leaf x => exact (Bool.false_ne_true h).elim
  | node l r => exact (Bool.false_ne_true h).elim

end PackTrie

/-! ### Soundness: balanced folds -/

private theorem sum_pairUp {α : Type} {M : Type*} [AddCommMonoid M] (f : α → α → α) (φ : α → M)
    (hf : ∀ a b, φ (f a b) = φ a + φ b) (l : List α) (p : Option α) :
    ((pairUp f l p).map φ).sum = (l.map φ).sum + p.elim 0 φ := by
  induction l generalizing p with
  | nil => cases p <;> simp [pairUp]
  | cons x xs ih =>
    cases p with
    | none =>
      change ((pairUp f xs (some x)).map φ).sum = _
      rw [ih]; simp [add_comm]
    | some a =>
      change ((f a x :: pairUp f xs none).map φ).sum = _
      rw [List.map_cons, List.sum_cons, ih, hf]; simp only [Option.elim, List.map_cons,
        List.sum_cons, add_zero]; abel

private theorem balFold_sum {α : Type} {M : Type*} [AddCommMonoid M] (f : α → α → α) (e : α)
    (φ : α → M) (hf : ∀ a b, φ (f a b) = φ a + φ b) (he : φ e = 0) (d : Nat) (l : List α) :
    φ (balFold f e d l) = (l.map φ).sum := by
  induction d generalizing l with
  | zero =>
    change φ (l.foldr f e) = _
    induction l with
    | nil => simpa using he
    | cons x xs ih => rw [List.foldr_cons, hf, ih, List.map_cons, List.sum_cons]
  | succ d ih =>
    rcases l with _ | ⟨x, _ | ⟨y, ys⟩⟩
    · change φ e = _; simpa using he
    · change φ x = _; simp
    · change φ (balFold f e d (pairUp f (x :: y :: ys) none)) = _
      rw [ih, sum_pairUp f φ hf]; simp

private theorem listMap_eq {α β : Type} (f : α → β) (l : List α) : listMap f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => change f a :: listMap f l = _; rw [ih, List.map_cons]

/-! ### Soundness: entry lists -/

/-- The coefficient of variable `k` in the entries `E` (proof-side). -/
def coeff (E : List (Nat × Nat)) (k : Nat) : Nat := (E.map fun e ↦ if e.1 = k then e.2 else 0).sum

private theorem coeff_nil (k : Nat) : coeff [] k = 0 := rfl

private theorem coeff_cons (e : Nat × Nat) (E : List (Nat × Nat)) (k : Nat) :
    coeff (e :: E) k = (if e.1 = k then e.2 else 0) + coeff E k := by
  simp [coeff]

private theorem coeff_le (E : List (Nat × Nat)) (k : Nat) : coeff E k ≤ (E.map (·.2)).sum := by
  induction E with
  | nil => simp [coeff_nil]
  | cons e E ih => rw [coeff_cons, List.map_cons, List.sum_cons]; split_ifs <;> omega

private theorem coeff_eq_zero {E : List (Nat × Nat)} {nv k : Nat} (hE : ∀ e ∈ E, e.1 < nv)
    (hk : nv ≤ k) : coeff E k = 0 := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rw [coeff_cons, ite_eq_right (by have := hE e (by simp); omega),
      ih (fun e' he' ↦ hE e' (by simp [he'])), Nat.add_zero]

private theorem entrySum_eq {E : List (Nat × Nat)} {nv : Nat} (hE : ∀ e ∈ E, e.1 < nv)
    (v : Nat → ℝ) : entrySum E v = ∑ k ∈ range nv, (coeff E k : ℝ) * v k := by
  induction E with
  | nil => simp [entrySum, coeff_nil]
  | cons e E ih =>
    have he : e.1 < nv := hE e (by simp)
    have ih' := ih (fun e' he' ↦ hE e' (by simp [he']))
    have h1 : ∑ k ∈ range nv, ((if e.1 = k then e.2 else 0 : Nat) : ℝ) * v k = e.2 * v e.1 := by
      rw [Finset.sum_eq_single_of_mem e.1 (mem_range.2 he)]
      · simp
      · intro b _ hb; rw [ite_eq_right (Ne.symm hb)]; simp
    simp only [entrySum, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    simp only [coeff_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib, h1]

private theorem shiftLeft_eq_pow (a W i : Nat) : a <<< (W * i) = a * (2 ^ W) ^ i := by
  rw [Nat.shiftLeft_eq, pow_mul]

/-- Chunk `q` of the single-entry trie, as a slot sum. -/
private theorem chunk_indicator {W L D z : Nat} {e : Nat × Nat} (he : e.1 < L * 2 ^ D) {q : Nat}
    (hq : q < 2 ^ D) :
    (PackTrie.single D (e.1 / L) ((z * e.2) <<< (W * (e.1 % L)))).get D q =
      ∑ i ∈ range L, z * (if e.1 = q * L + i then e.2 else 0) * (2 ^ W) ^ i := by
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.zero_mul] at he; omega
    · exact h
  have hdiv : e.1 / L < 2 ^ D := (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; exact he)
  rw [PackTrie.get_single D q (e.1 / L) _ hq hdiv, shiftLeft_eq_pow]
  by_cases h : q = e.1 / L
  · rw [ite_eq_left h, Finset.sum_eq_single_of_mem (e.1 % L) (mem_range.2 (Nat.mod_lt _ hL))]
    · rw [ite_eq_left (by rw [h]; exact (Nat.div_add_mod' e.1 L).symm)]
    · intro b hb hne
      rw [ite_eq_right]; · simp
      intro hb'
      apply hne
      have h2 := Nat.div_add_mod' e.1 L
      rw [← h] at h2
      omega
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [ite_eq_right]; · simp
    intro hi'
    apply h
    rw [hi', Nat.add_comm, Nat.add_mul_div_right _ _ hL,
      Nat.div_eq_of_lt (mem_range.1 hi), Nat.zero_add]

private theorem get_packEntries {W L D z : Nat} {E : List (Nat × Nat)}
    (hE : ∀ e ∈ E, e.1 < L * 2 ^ D) {q : Nat} (hq : q < 2 ^ D) :
    (packEntries W L D z E).get D q = ∑ i ∈ range L, z * coeff E (q * L + i) * (2 ^ W) ^ i := by
  unfold packEntries
  rw [balFold_sum PackTrie.add .zero (fun t ↦ t.get D q) (fun a b ↦ PackTrie.get_add a b D q)
    (PackTrie.get_zero D q), listMap_eq, List.map_map]
  induction E with
  | nil => simp [coeff_nil]
  | cons e E ih =>
    rw [List.map_cons, List.sum_cons, ih (fun e' he' ↦ hE e' (by simp [he']))]
    simp only [Function.comp, coeff_cons, Nat.mul_add, Nat.add_mul, Finset.sum_add_distrib]
    rw [chunk_indicator (hE e (by simp)) hq]

private theorem costEntries_eq (W nv z : Nat) (E : List (Nat × Nat)) :
    costEntries W nv z E = (E.map fun e ↦ z * e.2 + bif Nat.blt e.1 nv then 0 else 2 ^ W).sum := by
  unfold costEntries
  rw [listMap_eq]
  exact (balFold_sum Nat.add (0 : Nat) (id : Nat → Nat) (fun _ _ ↦ rfl) rfl 64 _).trans
    (by rw [List.map_id])

private theorem tot_le_costEntries (W nv z : Nat) (E : List (Nat × Nat)) :
    z * (E.map (·.2)).sum ≤ costEntries W nv z E := by
  rw [costEntries_eq]
  induction E with
  | nil => simp
  | cons e E ih => simp only [List.map_cons, List.sum_cons, Nat.mul_add]; omega

private theorem valid_of_costEntries_lt {W nv z : Nat} {E : List (Nat × Nat)}
    (h : costEntries W nv z E < 2 ^ W) : ∀ e ∈ E, e.1 < nv := by
  rw [costEntries_eq] at h
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [List.map_cons, List.sum_cons] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · cases hb : Nat.blt e'.1 nv with
      | true => exact PackTrie.lt_of_blt_true hb
      | false => rw [hb, Bool.cond_false] at h; omega
    · exact ih (by omega) e' he'

/-! ### Soundness: fractions and the slot decode -/

/-- The real value `num / den` of a fraction. -/
noncomputable def Frac.val (F : Frac) : ℝ := (F.num : ℝ) / (F.den : ℝ)

private theorem Frac.add_spec {a b : Frac} (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (a.add b).den ∧ (a.add b).val = a.val + b.val := by
  unfold Frac.add
  cases h : Nat.beq a.den b.den with
  | true =>
    have hab : a.den = b.den := Nat.eq_of_beq_eq_true h
    rw [Bool.cond_true]
    refine ⟨ha, ?_⟩
    change ((a.num + b.num : Int) : ℝ) / (a.den : ℝ) = (a.num : ℝ) / a.den + (b.num : ℝ) / b.den
    rw [← hab]; push_cast; rw [add_div]
  | false =>
    rw [Bool.cond_false]
    refine ⟨Nat.mul_pos ha hb, ?_⟩
    have ha' : (a.den : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b.den : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    change ((a.num * b.den + b.num * a.den : Int) : ℝ) / ((a.den * b.den : Nat) : ℝ) =
      (a.num : ℝ) / a.den + (b.num : ℝ) / b.den
    push_cast
    field_simp

private theorem slotTerm_den (B : Box) (k p n : Nat) : 0 < (slotTerm B k p n).den := by
  unfold slotTerm
  cases Nat.beq p n <;> cases Nat.blt n p <;> simp [Rat.den_pos]

private theorem slotTerm_self (B : Box) (k p : Nat) : (slotTerm B k p p).val = 0 := by
  unfold slotTerm
  rw [show Nat.beq p p = true from Nat.beq_refl p, Bool.cond_true]
  simp [Frac.val]

private theorem slotTerm_le (B : Box) (k p n : Nat) {x : ℝ} (hlo : (B.lo k : ℝ) ≤ x)
    (hhi : x ≤ (B.hi k : ℝ)) : (slotTerm B k p n).val ≤ ((p : ℝ) - n) * x := by
  cases h1 : Nat.beq p n with
  | true =>
    have : p = n := Nat.eq_of_beq_eq_true h1
    subst this
    rw [slotTerm_self]; simp
  | false =>
    unfold slotTerm
    rw [h1, Bool.cond_false]
    cases h2 : Nat.blt n p with
    | true =>
      have hnp : n < p := PackTrie.lt_of_blt_true h2
      rw [Bool.cond_true]
      change ((((p - n : Nat) : Int) * (B.lo k).num : Int) : ℝ) / ((B.lo k).den : ℝ) ≤ _
      have hc : ((B.lo k).num : ℝ) / (B.lo k).den = (B.lo k : ℝ) := (Rat.cast_def _).symm
      push_cast [Nat.cast_sub hnp.le]
      rw [mul_div_assoc, hc]
      have h0 : (0 : ℝ) ≤ (p : ℝ) - n := by
        have : (n : ℝ) < p := by exact_mod_cast hnp
        linarith
      exact mul_le_mul_of_nonneg_left hlo h0
    | false =>
      have hpn : p ≤ n := PackTrie.le_of_blt_false h2
      rw [Bool.cond_false]
      change ((-(((n - p : Nat) : Int) * (B.hi k).num) : Int) : ℝ) / ((B.hi k).den : ℝ) ≤ _
      have hc : ((B.hi k).num : ℝ) / (B.hi k).den = (B.hi k : ℝ) := (Rat.cast_def _).symm
      push_cast [Nat.cast_sub hpn]
      rw [neg_div, mul_div_assoc, hc]
      have h0 : (0 : ℝ) ≤ (n : ℝ) - p := by
        have : (p : ℝ) ≤ n := by exact_mod_cast hpn
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hhi h0]

private theorem linSum_spec (W : Nat) (B : Box) (c : Nat) : ∀ k p n : Nat,
    0 < (linSum W B c k p n).den ∧ (linSum W B c k p n).val =
      ∑ i ∈ range c,
        (slotTerm B (k + i) (p / (2 ^ W) ^ i % 2 ^ W) (n / (2 ^ W) ^ i % 2 ^ W)).val := by
  induction c with
  | zero =>
    intro k p n
    rw [show linSum W B 0 k p n = ⟨0, 1⟩ from rfl]
    exact ⟨Nat.one_pos, by simp [Frac.val]⟩
  | succ c ih =>
    intro k p n
    have hrec : linSum W B (c + 1) k p n = Frac.add (slotTerm B k (p % 2 ^ W) (n % 2 ^ W))
        (linSum W B c (k + 1) (p >>> W) (n >>> W)) := rfl
    obtain ⟨h1, h2⟩ := ih (k + 1) (p >>> W) (n >>> W)
    obtain ⟨h3, h4⟩ := Frac.add_spec (slotTerm_den B k (p % 2 ^ W) (n % 2 ^ W)) h1
    rw [hrec]
    refine ⟨h3, ?_⟩
    rw [h4, h2, Finset.sum_range_succ' _ c, add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        Nat.div_div_eq_div_mul, ← pow_succ', show k + 1 + i = k + (i + 1) by omega]
    · simp

private theorem mod_pow_div_mod {b p h i : Nat} (hi : i < h) :
    p % b ^ h / b ^ i % b = p / b ^ i % b := by
  have e : b ^ h = b ^ i * b ^ (h - i) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self b (by omega)

private theorem boxSum_spec (W : Nat) (B : Box) (d : Nat) : ∀ cnt k p n : Nat,
    0 < (boxSum W B d cnt k p n).den ∧ (boxSum W B d cnt k p n).val =
      ∑ i ∈ range cnt,
        (slotTerm B (k + i) (p / (2 ^ W) ^ i % 2 ^ W) (n / (2 ^ W) ^ i % 2 ^ W)).val := by
  induction d with
  | zero => exact linSum_spec W B
  | succ d ih =>
    intro cnt k p n
    have hrec : boxSum W B (d + 1) cnt k p n = bif Nat.ble cnt 1 then linSum W B cnt k p n
      else Frac.add (boxSum W B d (cnt / 2) k (p % 2 ^ (W * (cnt / 2))) (n % 2 ^ (W * (cnt / 2))))
        (boxSum W B d (cnt - cnt / 2) (k + cnt / 2) (p >>> (W * (cnt / 2)))
          (n >>> (W * (cnt / 2)))) := rfl
    rw [hrec]
    cases Nat.ble cnt 1 with
    | true => rw [Bool.cond_true]; exact linSum_spec W B cnt k p n
    | false =>
      rw [Bool.cond_false]
      obtain ⟨h1, h2⟩ := ih (cnt / 2) k (p % 2 ^ (W * (cnt / 2))) (n % 2 ^ (W * (cnt / 2)))
      obtain ⟨h3, h4⟩ := ih (cnt - cnt / 2) (k + cnt / 2) (p >>> (W * (cnt / 2)))
        (n >>> (W * (cnt / 2)))
      obtain ⟨h5, h6⟩ := Frac.add_spec h1 h3
      refine ⟨h5, ?_⟩
      rw [h6, h2, h4]
      have hc : cnt = cnt / 2 + (cnt - cnt / 2) := by omega
      conv_rhs => rw [hc, Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [pow_mul, mod_pow_div_mod (mem_range.1 hi), mod_pow_div_mod (mem_range.1 hi)]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, pow_mul,
          Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_add, Nat.add_assoc]

/-- The box sum of chunk `q` with packed parts `x` and `y` (proof-side). -/
noncomputable def chunkVal (W L : Nat) (B : Box) (q x y : Nat) : ℝ :=
  ∑ i ∈ range L, (slotTerm B (q * L + i) (x / (2 ^ W) ^ i % 2 ^ W) (y / (2 ^ W) ^ i % 2 ^ W)).val

private theorem chunkVal_zero (W L : Nat) (B : Box) (q : Nat) : chunkVal W L B q 0 0 = 0 := by
  unfold chunkVal
  apply Finset.sum_eq_zero
  intro i _
  simp only [Nat.zero_div, Nat.zero_mod]
  exact slotTerm_self B _ 0

private theorem decodeTrie_spec (W L : Nat) (B : Box) (d : Nat) : ∀ (q : Nat) (tp tn : PackTrie),
    0 < (decodeTrie W L B d q tp tn).den ∧ (decodeTrie W L B d q tp tn).val =
      ∑ j ∈ range (2 ^ d), chunkVal W L B (q + j) (tp.get d j) (tn.get d j) := by
  induction d with
  | zero =>
    intro q tp tn
    have hrec : decodeTrie W L B 0 q tp tn = boxSum W B 64 L (q * L) tp.val tn.val := rfl
    obtain ⟨h1, h2⟩ := boxSum_spec W B 64 L (q * L) tp.val tn.val
    rw [hrec]
    refine ⟨h1, ?_⟩
    rw [h2]
    simp [chunkVal, PackTrie.get_zero_depth]
  | succ d ih =>
    intro q tp tn
    have hrec : decodeTrie W L B (d + 1) q tp tn = bif tp.isZero && tn.isZero then ⟨0, 1⟩
        else Frac.add (decodeTrie W L B d q tp.left tn.left)
          (decodeTrie W L B d (q + 2 ^ d) tp.right tn.right) := rfl
    rw [hrec]
    cases hz : (tp.isZero && tn.isZero) with
    | true =>
      rw [Bool.cond_true]
      rw [Bool.and_eq_true] at hz
      rw [PackTrie.eq_zero_of_isZero hz.1, PackTrie.eq_zero_of_isZero hz.2]
      refine ⟨Nat.one_pos, ?_⟩
      simp only [PackTrie.get_zero, chunkVal_zero, Finset.sum_const_zero]
      simp [Frac.val]
    | false =>
      rw [Bool.cond_false]
      obtain ⟨h1, h2⟩ := ih q tp.left tn.left
      obtain ⟨h3, h4⟩ := ih (q + 2 ^ d) tp.right tn.right
      obtain ⟨h5, h6⟩ := Frac.add_spec h1 h3
      refine ⟨h5, ?_⟩
      rw [h6, h2, h4, pow_succ, mul_two, Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [PackTrie.get_succ_eq, PackTrie.get_succ_eq, ite_eq_left (mem_range.1 hj),
          ite_eq_left (mem_range.1 hj)]
      · apply Finset.sum_congr rfl
        intro j _
        rw [PackTrie.get_succ_eq, PackTrie.get_succ_eq, ite_eq_right (by omega),
          ite_eq_right (by omega),
          Nat.add_sub_cancel_left, Nat.add_assoc]

/-! ### Soundness: base-`b` digits -/

private theorem digits_lt {b : Nat} (s : Nat → Nat) : ∀ m : Nat, (∀ i < m, s i < b) →
    ∑ i ∈ range m, s i * b ^ i < b ^ m
  | 0, _ => by simp
  | m + 1, hs => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := digits_lt s m (fun i hi ↦ hs i (by omega))
    have h3 : (s m + 1) * b ^ m ≤ b * b ^ m := Nat.mul_le_mul_right _ (hs m (by omega))
    calc _ < b ^ m + s m * b ^ m := Nat.add_lt_add_right h1 _
      _ = (s m + 1) * b ^ m := by ring
      _ ≤ b * b ^ m := h3
      _ = b ^ m * b := Nat.mul_comm _ _

/-- Base-`b` digit uniqueness: digit `j` of `∑_{i<m} s i * b ^ i` is `s j` when every `s i < b`. -/
private theorem digit_eq {b : Nat} (hb : 0 < b) (s : Nat → Nat) : ∀ m : Nat, (∀ i < m, s i < b) →
    ∀ j < m, (∑ i ∈ range m, s i * b ^ i) / b ^ j % b = s j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, hs, j, hj => by
    rw [Finset.sum_range_succ]
    have hs' : ∀ i < m, s i < b := fun i hi ↦ hs i (by omega)
    rcases Nat.lt_or_ge j m with hjm | hjm
    · have e : s m * b ^ m = b ^ j * (s m * b ^ (m - j)) := by
        rw [Nat.mul_left_comm, ← pow_add, Nat.add_sub_cancel' hjm.le]
      rw [e, Nat.add_mul_div_left _ _ (pow_pos hb j)]
      have e2 : s m * b ^ (m - j) = b * (s m * b ^ (m - j - 1)) := by
        rw [Nat.mul_left_comm, ← pow_succ']; congr 2; omega
      rw [e2, Nat.add_mul_mod_self_left]
      exact digit_eq hb s m hs' j hjm
    · obtain rfl : j = m := by omega
      rw [Nat.add_mul_div_right _ _ (pow_pos hb j), Nat.div_eq_of_lt (digits_lt s j hs'),
        Nat.zero_add, Nat.mod_eq_of_lt (hs j (by omega))]

private theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : Nat → M) (L : Nat) :
    ∀ Q : Nat, ∑ j ∈ range Q, ∑ i ∈ range L, f (j * L + i) = ∑ k ∈ range (Q * L), f k
  | 0 => by simp
  | Q + 1 => by
    rw [Finset.sum_range_succ, sum_range_mul_eq f L Q, Nat.succ_mul, Finset.sum_range_add]

/-! ### Soundness: weighted trees -/

section TreeProofs

variable {T : Type}

/-- Sum over the leaves of a weighted tree (proof-side). -/
def WTree.sum {M : Type*} [AddCommMonoid M] (f : Nat → T → M) : WTree T → M
  | .leaf z t => f z t
  | .node l r => l.sum f + r.sum f

/-- `P` holds at every leaf of a weighted tree (proof-side). -/
def WTree.Forall (P : Nat → T → Prop) : WTree T → Prop
  | .leaf z t => P z t
  | .node l r => l.Forall P ∧ r.Forall P

private theorem WTree.Forall.imp {P Q : Nat → T → Prop} {w : WTree T} (h : w.Forall P)
    (hPQ : ∀ z t, P z t → Q z t) : w.Forall Q := by
  induction w with
  | leaf z t => exact hPQ z t h
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

private theorem WTree.sumNat_eq (f : Nat → T → Nat) (w : WTree T) : w.sumNat f = w.sum f := by
  induction w with
  | leaf z t => rfl
  | node l r ihl ihr => change Nat.add (l.sumNat f) (r.sumNat f) = _; rw [ihl, ihr]; rfl

private theorem WTree.sumInt_eq (f : Nat → T → Int) (w : WTree T) : w.sumInt f = w.sum f := by
  induction w with
  | leaf z t => rfl
  | node l r ihl ihr => change Int.add (l.sumInt f) (r.sumInt f) = _; rw [ihl, ihr]; rfl

private theorem WTree.get_sumTrie (f : Nat → T → PackTrie) (w : WTree T) (d q : Nat) :
    (w.sumTrie f).get d q = w.sum fun z t ↦ (f z t).get d q := by
  induction w with
  | leaf z t => rfl
  | node l r ihl ihr =>
    change (PackTrie.add (l.sumTrie f) (r.sumTrie f)).get d q = _
    rw [PackTrie.get_add, ihl, ihr]; rfl

private theorem WTree.forall_of_sum_lt {f : Nat → T → Nat} {c : Nat} {w : WTree T}
    (h : w.sum f < c) : w.Forall fun z t ↦ f z t < c := by
  induction w with
  | leaf z t => exact h
  | node l r ihl ihr =>
    change l.sum f + r.sum f < c at h
    exact ⟨ihl (by omega), ihr (by omega)⟩

private theorem WTree.sum_congr {M : Type*} [AddCommMonoid M] {f g : Nat → T → M} {w : WTree T}
    (h : w.Forall fun z t ↦ f z t = g z t) : w.sum f = w.sum g := by
  induction w with
  | leaf z t => exact h
  | node l r ihl ihr => exact congrArg₂ (· + ·) (ihl h.1) (ihr h.2)

private theorem WTree.sum_eq_zero {M : Type*} [AddCommMonoid M] {f : Nat → T → M} {w : WTree T}
    (h : w.Forall fun z t ↦ f z t = 0) : w.sum f = 0 := by
  induction w with
  | leaf z t => exact h
  | node l r ihl ihr => change l.sum f + r.sum f = 0; rw [ihl h.1, ihr h.2, add_zero]

private theorem WTree.sum_le_sum_nat {f g : Nat → T → Nat} (h : ∀ z t, f z t ≤ g z t)
    (w : WTree T) : w.sum f ≤ w.sum g := by
  induction w with
  | leaf z t => exact h z t
  | node l r ihl ihr => exact Nat.add_le_add ihl ihr

private theorem WTree.sum_finset {M : Type*} [AddCommMonoid M] {ι : Type*} (s : Finset ι)
    (g : Nat → T → ι → M) (w : WTree T) :
    w.sum (fun z t ↦ ∑ i ∈ s, g z t i) = ∑ i ∈ s, w.sum (fun z t ↦ g z t i) := by
  induction w with
  | leaf z t => rfl
  | node l r ihl ihr => change l.sum _ + r.sum _ = _; rw [ihl, ihr, ← Finset.sum_add_distrib]; rfl

private theorem WTree.sum_mul_right (f : Nat → T → Nat) (c : Nat) (w : WTree T) :
    w.sum f * c = w.sum (fun z t ↦ f z t * c) := by
  induction w with
  | leaf z t => rfl
  | node l r ihl ihr =>
    change (l.sum f + r.sum f) * c = l.sum _ + r.sum _
    rw [Nat.add_mul, ihl, ihr]

private theorem WTree.cast_sum (f : Nat → T → Int) (w : WTree T) :
    ((w.sum f : Int) : ℝ) = w.sum (fun z t ↦ (f z t : ℝ)) := by
  induction w with
  | leaf z t => rfl
  | node l r ihl ihr =>
    change ((l.sum f + r.sum f : Int) : ℝ) = l.sum _ + r.sum _
    push_cast; rw [ihl, ihr]

/-- The leaf's row builds and every variable index in it is `< nv` (proof-side). -/
def LeafOK (nv : Nat) (build : T → Option Row) (_z : Nat) (t : T) : Prop :=
  ∃ r, build t = some r ∧ (∀ e ∈ r.pos, e.1 < nv) ∧ ∀ e ∈ r.neg, e.1 < nv

/-- `∑_{leaves} z * coeff (sel r) k` (proof-side). -/
def coefT (build : T → Option Row) (sel : Row → List (Nat × Nat)) (k : Nat) (w : WTree T) : Nat :=
  w.sum fun z t ↦ (build t).elim 0 fun r ↦ z * coeff (sel r) k

private theorem leafOK_of_cost {W nv : Nat} {build : T → Option Row} {z : Nat} {t : T}
    (h : leafCost W nv build z t < 2 ^ W) : LeafOK nv build z t := by
  unfold leafCost at h
  cases hb : build t with
  | none => rw [hb] at h; change 2 ^ W < 2 ^ W at h; omega
  | some r =>
    rw [hb] at h
    change costEntries W nv z r.pos + costEntries W nv z r.neg < 2 ^ W at h
    exact ⟨r, hb, valid_of_costEntries_lt (W := W) (z := z) (by omega),
      valid_of_costEntries_lt (W := W) (z := z) (by omega)⟩

private theorem get_pack {W L D nv : Nat} {build : T → Option Row} {sel : Row → List (Nat × Nat)}
    (hsel : ∀ r, sel r = r.pos ∨ sel r = r.neg) (hL : nv ≤ L * 2 ^ D) {w : WTree T}
    (hw : w.Forall (LeafOK nv build)) {q : Nat} (hq : q < 2 ^ D) :
    (w.sumTrie (leafPack W L D build sel)).get D q =
      ∑ i ∈ range L, coefT build sel (q * L + i) w * (2 ^ W) ^ i := by
  rw [WTree.get_sumTrie]
  have h1 : (w.sum fun z t ↦ (leafPack W L D build sel z t).get D q) =
      w.sum (fun z t ↦ ∑ i ∈ range L,
        (build t).elim 0 (fun r ↦ z * coeff (sel r) (q * L + i)) * (2 ^ W) ^ i) := by
    apply WTree.sum_congr
    refine hw.imp fun z t ⟨r, hr, hp, hn⟩ ↦ ?_
    have hE : ∀ e ∈ sel r, e.1 < L * 2 ^ D := fun e he ↦ by
      rcases hsel r with h | h <;> rw [h] at he
      · exact lt_of_lt_of_le (hp e he) hL
      · exact lt_of_lt_of_le (hn e he) hL
    have hp' : leafPack W L D build sel z t = packEntries W L D z (sel r) := by
      unfold leafPack; rw [hr]
    rw [hp', get_packEntries hE hq, hr]
    rfl
  rw [h1, WTree.sum_finset]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefT, WTree.sum_mul_right]

private theorem coefT_le_cost {W nv : Nat} {build : T → Option Row} {sel : Row → List (Nat × Nat)}
    (hsel : ∀ r, sel r = r.pos ∨ sel r = r.neg) (k : Nat) (w : WTree T) :
    coefT build sel k w ≤ w.sum (leafCost W nv build) := by
  apply WTree.sum_le_sum_nat
  intro z t
  unfold leafCost
  cases hb : build t with
  | none => exact Nat.zero_le _
  | some r =>
    change z * coeff (sel r) k ≤ costEntries W nv z r.pos + costEntries W nv z r.neg
    have h1 := Nat.mul_le_mul_left z (coeff_le (sel r) k)
    rcases hsel r with h | h <;> rw [h] at h1 ⊢
    · have := tot_le_costEntries W nv z r.pos; omega
    · have := tot_le_costEntries W nv z r.neg; omega

private theorem coefT_eq_zero {nv : Nat} {build : T → Option Row} {sel : Row → List (Nat × Nat)}
    (hsel : ∀ r, sel r = r.pos ∨ sel r = r.neg) {w : WTree T} (hw : w.Forall (LeafOK nv build))
    {k : Nat} (hk : nv ≤ k) : coefT build sel k w = 0 := by
  apply WTree.sum_eq_zero
  refine hw.imp fun z t ⟨r, hr, hp, hn⟩ ↦ ?_
  rw [hr]
  change z * coeff (sel r) k = 0
  rcases hsel r with h | h <;> rw [h]
  · rw [coeff_eq_zero hp hk, Nat.mul_zero]
  · rw [coeff_eq_zero hn hk, Nat.mul_zero]

private theorem rows_le {nv : Nat} {build : T → Option Row} (v : Nat → ℝ)
    (hrow : ∀ t r, build t = some r → r.Holds v) {w : WTree T} (hw : w.Forall (LeafOK nv build)) :
    ∑ k ∈ range nv, ((coefT build Row.pos k w : ℝ) - coefT build Row.neg k w) * v k ≤
      w.sum fun z t ↦ ((leafRhs build z t : Int) : ℝ) := by
  induction w with
  | leaf z t =>
    obtain ⟨r, hr, hp, hn⟩ := hw
    have hH : r.lhs v ≤ r.rhs := hrow t r hr
    have hc : ∀ (sel : Row → List (Nat × Nat)) k,
        coefT build sel k (.leaf z t) = z * coeff (sel r) k := by
      intro sel k; change (build t).elim 0 _ = _; rw [hr]; rfl
    have hrhs : leafRhs build z t = (z : Int) * r.rhs := by unfold leafRhs; rw [hr]
    change _ ≤ ((leafRhs build z t : Int) : ℝ)
    simp only [hc, hrhs]
    have e : ∑ k ∈ range nv, (((z * coeff r.pos k : Nat) : ℝ) - ((z * coeff r.neg k : Nat) : ℝ)) *
        v k = (z : ℝ) * r.lhs v := by
      rw [Row.lhs, entrySum_eq hp v, entrySum_eq hn v, mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      push_cast; ring
    rw [e]
    push_cast
    exact mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg z)
  | node l r ihl ihr =>
    obtain ⟨hl, hr⟩ := hw
    have e : ∀ k, ((coefT build Row.pos k (.node l r) : ℝ) - coefT build Row.neg k (.node l r)) *
        v k = ((coefT build Row.pos k l : ℝ) - coefT build Row.neg k l) * v k +
          ((coefT build Row.pos k r : ℝ) - coefT build Row.neg k r) * v k := by
      intro k
      change (((l.sum _ + r.sum _ : Nat) : ℝ) - ((l.sum _ + r.sum _ : Nat) : ℝ)) * v k = _
      push_cast; simp only [coefT]; ring
    simp only [e, Finset.sum_add_distrib]
    exact add_le_add (ihl hl) (ihr hr)

end TreeProofs

/-! ### Soundness: the checker -/

/-- Soundness of `checkWith`: if it accepts, no point `v` of the box satisfies every row. -/
theorem checkWith_sound {T : Type} {W D : Nat} {B : Box} {build : T → Option Row} {w : WTree T}
    (v : Nat → ℝ) (hrow : ∀ t r, build t = some r → r.Holds v)
    (hbox : ∀ k < B.nv, (B.lo k : ℝ) ≤ v k ∧ v k ≤ (B.hi k : ℝ))
    (hc : checkWith W D B build w = true) : False := by
  unfold checkWith at hc
  rw [Bool.and_eq_true, Nat.blt_eq] at hc
  obtain ⟨hcost, hgt⟩ := hc
  set L := chunkLen B.nv D with hLdef
  set P := w.sumTrie (leafPack W L D build Row.pos)
  set N := w.sumTrie (leafPack W L D build Row.neg)
  rw [WTree.sumNat_eq] at hcost
  have hw : w.Forall (LeafOK B.nv build) :=
    (WTree.forall_of_sum_lt hcost).imp fun _ _ h ↦ leafOK_of_cost h
  have hb : 0 < 2 ^ W := Nat.two_pow_pos W
  have hL : B.nv ≤ L * 2 ^ D := by
    rw [hLdef, chunkLen, Nat.add_mul, Nat.one_mul]
    exact (Nat.lt_div_mul_add (Nat.two_pow_pos D)).le
  have hsp : ∀ r : Row, Row.pos r = r.pos ∨ Row.pos r = r.neg := fun _ ↦ Or.inl rfl
  have hsn : ∀ r : Row, Row.neg r = r.pos ∨ Row.neg r = r.neg := fun _ ↦ Or.inr rfl
  have hdig : ∀ (sel : Row → List (Nat × Nat)), (∀ r, sel r = r.pos ∨ sel r = r.neg) →
      ∀ j < 2 ^ D, ∀ i < L, (w.sumTrie (leafPack W L D build sel)).get D j / (2 ^ W) ^ i % 2 ^ W =
        coefT build sel (j * L + i) w := by
    intro sel hsel j hj i hi
    rw [get_pack hsel hL hw hj]
    exact digit_eq hb (fun i ↦ coefT build sel (j * L + i) w) L
      (fun i _ ↦ lt_of_le_of_lt (coefT_le_cost hsel _ w) hcost) i hi
  obtain ⟨hden, hval⟩ := decodeTrie_spec W L B D 0 P N
  have hF : (decodeTrie W L B D 0 P N).val = ∑ k ∈ range (2 ^ D * L),
      (slotTerm B k (coefT build Row.pos k w) (coefT build Row.neg k w)).val := by
    rw [hval, ← sum_range_mul_eq]
    apply Finset.sum_congr rfl
    intro j hj
    unfold chunkVal
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.zero_add, hdig Row.pos hsp j (mem_range.1 hj) i (mem_range.1 hi),
      hdig Row.neg hsn j (mem_range.1 hj) i (mem_range.1 hi)]
  have hle : (decodeTrie W L B D 0 P N).val ≤ ((w.sumInt (leafRhs build) : Int) : ℝ) := by
    rw [hF]
    have hle' : B.nv ≤ 2 ^ D * L := by rw [Nat.mul_comm]; exact hL
    calc _ ≤ ∑ k ∈ range (2 ^ D * L),
          ((coefT build Row.pos k w : ℝ) - coefT build Row.neg k w) * v k := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hkv : k < B.nv
          · exact slotTerm_le B k _ _ (hbox k hkv).1 (hbox k hkv).2
          · rw [coefT_eq_zero hsp hw (Nat.not_lt.1 hkv), coefT_eq_zero hsn hw (Nat.not_lt.1 hkv),
              slotTerm_self]
            simp
      _ = ∑ k ∈ range B.nv,
          ((coefT build Row.pos k w : ℝ) - coefT build Row.neg k w) * v k := by
          rw [← Nat.add_sub_cancel' hle', Finset.sum_range_add]
          have h0 : ∑ i ∈ range (2 ^ D * L - B.nv),
              ((coefT build Row.pos (B.nv + i) w : ℝ) - coefT build Row.neg (B.nv + i) w) *
                v (B.nv + i) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rw [coefT_eq_zero hsp hw (Nat.le_add_right _ _),
              coefT_eq_zero hsn hw (Nat.le_add_right _ _)]
            simp
          rw [h0, add_zero]
      _ ≤ w.sum fun z t ↦ ((leafRhs build z t : Int) : ℝ) := rows_le v hrow hw
      _ = ((w.sumInt (leafRhs build) : Int) : ℝ) := by rw [WTree.sumInt_eq, WTree.cast_sum]
  have hgt' : ((w.sumInt (leafRhs build) : Int) : ℝ) < (decodeTrie W L B D 0 P N).val := by
    unfold fracGt at hgt
    have h := of_decide_eq_true hgt
    unfold Frac.val
    rw [lt_div_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast h
  linarith

/-- Soundness of `check`: if it accepts, no point `v` of the box satisfies every row. -/
theorem check_sound {T : Type} {W : Nat} {B : Box} {build : T → Option Row} {w : WTree T}
    (v : Nat → ℝ) (hrow : ∀ t r, build t = some r → r.Holds v)
    (hbox : ∀ k < B.nv, (B.lo k : ℝ) ≤ v k ∧ v k ≤ (B.hi k : ℝ))
    (hc : check W B build w = true) : False :=
  checkWith_sound v hrow hbox hc

end Esgk.FarkasPackedCheck
