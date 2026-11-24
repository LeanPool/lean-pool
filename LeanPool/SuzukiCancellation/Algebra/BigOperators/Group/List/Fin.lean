/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.ProdSigma

/-!
# Ordered list products and finite-index reindexing

Splitting and telescoping rules for noncommutative products, reindexing by list
positions, and products of finite-index lists. No calculus is needed.

## Main results

* `TrotterError.List.prod_map_eq_take_mul_get_mul_drop` splits an ordered product at the first
  occurrence of a chosen element.
* `TrotterError.List.prod_mul_rev_eq_one_of_mul_eq_one` cancels an ordered product against its
  pointwise right inverses in reverse order.
* `TrotterError.List.sum_get_eq_sum_idxOf` reindexes a sum along a list containing each element
  exactly once.
-/

@[expose] public section

namespace TrotterError.List

/-- A finite sum commutes with summing a list, including repeated list entries. -/
lemma sum_map_sum {ι κ M : Type*} [AddCommMonoid M]
    (l : List ι) (s : Finset κ) (f : ι → κ → M) :
    (l.map fun a ↦ ∑ k ∈ s, f a k).sum = ∑ k ∈ s, (l.map fun a ↦ f a k).sum := by
  simpa using (Multiset.sum_map_sum (m := (l : Multiset ι)) (s := s) (f := f))

/-! ### Products over sublists -/

/-- The product over `l.drop k` splits as `f (l.get k)` times the product over `l.drop (k + 1)`. -/
@[to_additive /-- The sum over a suffix splits into its first summand and the remaining sum. -/]
lemma prod_drop_eq_get_mul {ι M : Type*} [Monoid M] (l : List ι) (f : ι → M) (k : Fin l.length) :
    ((l.drop (k : ℕ)).map f).prod = f (l.get k) * ((l.drop ((k : ℕ) + 1)).map f).prod := by
  rw [← List.cons_get_drop_succ (l := l) (n := k)]
  simp only [List.map_cons, List.prod_cons]

/-- Splitting the product `(l.map f).prod` at the occurrence of `i`: it is the product over the
prefix strictly before `i`, times `f i`, times the product over the suffix strictly after `i`. -/
@[to_additive]
lemma prod_map_eq_take_mul_get_mul_drop {ι M : Type*} [BEq ι] [LawfulBEq ι] [Monoid M]
    (l : List ι) (f : ι → M) (i : ι) (hi : i ∈ l) :
    (l.map f).prod = ((l.take (l.idxOf i)).map f).prod * f i *
      ((l.drop (l.idxOf i + 1)).map f).prod := by
  let k : Fin l.length := ⟨l.idxOf i, List.idxOf_lt_length_iff.mpr hi⟩
  have h := (l.map f).prod_take_mul_prod_drop (l.idxOf i)
  rw [← List.map_take, ← List.map_drop, prod_drop_eq_get_mul l f k, List.idxOf_get k.isLt] at h
  simpa only [mul_assoc] using h.symm

/-- If `g i` is a right inverse of `f i` for every `i`, then the product of `f` over `l` times the
product of `g` over `l.reverse` is `1`. -/
lemma prod_mul_rev_eq_one_of_mul_eq_one {ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M)
    (hfg : ∀ i, f i * g i = 1) : (l.map f).prod * (l.reverse.map g).prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_one]
      calc
        _ = f a * ((l.map f).prod * (l.reverse.map g).prod) * g a := by simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hfg a]

/-- If `g i` is a left inverse of `f i` for every `i`, then the product of `g` over `l.reverse`
times the product of `f` over `l` is `1`. -/
lemma rev_mul_prod_eq_one_of_mul_eq_one {ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M)
    (hgf : ∀ i, g i * f i = 1) : (l.reverse.map g).prod * (l.map f).prod = 1 := by
  simpa only [List.reverse_reverse] using prod_mul_rev_eq_one_of_mul_eq_one l.reverse g f hgf

/-! ### Reindexing a sum by a nodup list -/

/-- A sum over positions `Fin l.length` reindexes to a sum over the (pairwise distinct) elements
of `l`, using `l.idxOf i` as the inverse of `l.get`. -/
lemma sum_get_eq_sum_idxOf {ι A : Type*} [Fintype ι] [BEq ι] [LawfulBEq ι] [AddCommMonoid A]
    {l : List ι} (hnodup : l.Nodup) (hmem : ∀ i : ι, i ∈ l) (G : ι → ℕ → A) :
    (∑ k : Fin l.length, G (l.get k) (k : ℕ)) = ∑ i : ι, G i (l.idxOf i) := by
  refine (Finset.sum_bij (fun i _ => ⟨l.idxOf i, List.idxOf_lt_length_iff.mpr (hmem i)⟩)
    (fun i _ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro a₁ ha₁ a₂ ha₂ h
    have h₁ := List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a₁))
    have h₂ := List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a₂))
    exact h₁.symm.trans ((congrArg l.get h).trans h₂)
  · intro b hb
    refine ⟨l.get b, Finset.mem_univ _, ?_⟩
    ext; exact List.get_idxOf hnodup b
  · intro a ha
    rw [List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a))]

/-! ### Products of `List.ofFn` suffixes -/

/-- Peeling the outermost entry off a dropped suffix of a `List.ofFn`: the reverse product of the
suffix of `f : Fin (s+1) → 𝔸` is `f (Fin.last s)` times the reverse product of the corresponding
suffix of the inner `Fin s` sequence. -/
lemma ofFn_castSucc_drop_reverse_prod {s} {𝔸 : Type*} [Monoid 𝔸] (f : Fin (s + 1) → 𝔸) (k : ℕ)
    (hk : k ≤ s) :
    f (Fin.last s) * ((List.ofFn (fun i : Fin s => f i.castSucc)).drop k).reverse.prod
      = ((List.ofFn f).drop k).reverse.prod := by
  rw [List.ofFn_succ', List.concat_eq_append]
  rw [List.drop_append_of_le_length (l₁ := List.ofFn (fun i : Fin s => f i.castSucc))
    (l₂ := [f (Fin.last s)]) (by simpa using hk)]
  rw [List.reverse_concat', List.prod_cons]

/-- Peeling the outermost entry off a dropped suffix of a `List.ofFn` (no reversal): the product of
the suffix of `f : Fin (s+1) → 𝔸` is the product of the inner `Fin s` suffix times
`f (Fin.last s)`. -/
lemma ofFn_castSucc_drop_prod {s} {𝔸 : Type*} [Monoid 𝔸] (f : Fin (s + 1) → 𝔸) (k : ℕ)
    (hk : k ≤ s) :
    ((List.ofFn (fun i : Fin s => f i.castSucc)).drop k).prod * f (Fin.last s)
      = ((List.ofFn f).drop k).prod := by
  rw [List.ofFn_succ', List.concat_eq_append]
  rw [List.drop_append_of_le_length (l₁ := List.ofFn (fun i : Fin s => f i.castSucc))
    (l₂ := [f (Fin.last s)]) (by simpa using hk)]
  rw [List.prod_append, List.prod_singleton]

/-- `List.product` of two `List.ofFn` lists is the `List.ofFn` of the `divNat`/`modNat` pairing. -/
lemma product_ofFn {α β : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → β) :
    List.product (List.ofFn f) (List.ofFn g) =
      List.ofFn (fun k : Fin (m * n) => (f k.divNat, g k.modNat)) := by
  change List.ofFn f ×ˢ List.ofFn g = List.ofFn (fun k : Fin (m * n) => (f k.divNat, g k.modNat))
  induction m with
  | zero => simp [List.nil_product]
  | succ m ih =>
      by_cases hn : n = 0
      · subst n; simp
      · rw [List.ofFn_succ, List.product_cons, List.map_ofFn, ih (fun i => f i.succ)]
        rw [List.ofFn_congr (show (m + 1) * n = n + m * n by rw [Nat.succ_mul, Nat.add_comm])
          (fun k : Fin ((m + 1) * n) => (f k.divNat, g k.modNat))]
        rw [List.ofFn_add]
        congr 1
        · congr 1
          funext j
          simp only [Function.comp_apply]
          apply Prod.ext
          · apply congrArg f
            apply Fin.ext
            rw [Fin.coe_divNat, Fin.val_cast, Fin.val_castLE]
            simpa using (Nat.div_eq_of_lt j.isLt : j.val / n = 0).symm
          · apply congrArg g
            apply Fin.ext
            rw [Fin.coe_modNat, Fin.val_cast, Fin.val_castLE]
            simpa using (Nat.mod_eq_of_lt j.isLt : j.val % n = j.val).symm
        · congr 1
          funext k
          apply Prod.ext
          · apply congrArg f
            apply Fin.ext
            rw [Fin.val_succ, Fin.coe_divNat, Fin.coe_divNat, Fin.val_cast, Fin.val_natAdd]
            rw [show (n + k.val) / n = k.val / n + 1 by
              rw [congrArg (fun x => (x + k.val) / n) (Nat.mul_one n).symm]
              rw [Nat.mul_add_div (Nat.pos_of_ne_zero hn) 1 k.val, Nat.add_comm]]
          · apply congrArg g
            apply Fin.ext
            rw [Fin.coe_modNat, Fin.coe_modNat, Fin.val_cast, Fin.val_natAdd,
              congrArg (fun x => (x + k.val) % n) (Nat.mul_one n).symm, Nat.mul_add_mod]

/-! ### `List.finRange` / `Fin.cast` reindexing -/

/-- `List.finRange (n + m)` splits into the `n`-part and the `m`-part. -/
lemma finRange_add {n m : ℕ} :
    List.finRange (n + m) =
      (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  rw [show List.finRange (n + m) = List.ofFn (fun i : Fin (n + m) => i) from rfl]
  rw [List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  rfl

/-- The reversed `finRange` splits accordingly. -/
lemma finRange_reverse_add {n m : ℕ} :
    (List.finRange (n + m)).reverse =
      (List.finRange m).reverse.map (Fin.natAdd n) ++
        (List.finRange n).reverse.map (Fin.castAdd m) := by
  rw [finRange_add, List.reverse_append, List.map_reverse, List.map_reverse]

/-- Mapping `g ∘ Fin.revPerm` over the reversed `finRange` is mapping `g` over `finRange`. -/
lemma finRange_reverse_map_comp_revPerm {n : ℕ} {α : Type*} (g : Fin n → α) :
    ((List.finRange n).reverse).map (g ∘ Fin.revPerm) = (List.finRange n).map g := by
  rw [List.finRange_reverse, List.map_map]
  congr 1
  funext γ
  change g (Fin.revPerm (Fin.rev γ)) = g γ
  rw [Fin.revPerm_apply, Fin.rev_rev]

end TrotterError.List
