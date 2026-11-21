/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Multiplexors.Transpositor
public import Mathlib.Order.SuccPred.Nat

/-!
# Lafont, "Interaction Combinators" (1997): the transpositor `T_σ` of an involution

Page 84 (PDF page 16). "If σ is an involutive permutation of `{1, …, n}`, one constructs a
principal net `T_σ` of arity `n` such that two copies plugged by their roots reduce to the wiring
σ. Any such permutation is a product of disjoint transpositions; that is,
`σ = ρ⁻¹ ∘ ι_{p,q} ∘ ρ` where ρ is a permutation of `{1, …, n}` and `2p + q = n`." The
implementation is the transpositor `T_{p,q}` of page 83 with its ports permuted by ρ: no new cell.

Ports are numbered from `0`. The permutation ρ is given by a list of the ports, `portList σ`:
first, for each port `a` with `a < σ a` in increasing order, the two ports `a, σ a`; then the
fixed points of σ in increasing order. Port `j` of `T_{p,q}` is port `(portList σ)[j]` of `T_σ`.

Contents, in the order of the file:

1. Definitions: `swapIdx`, `ι_{p,q}` on positions, with the two facts `swapIdx_swapIdx` and
   `swapIdx_lt` that make `swapPerm`, `ι_{p,q}` as a permutation of `Fin n`; `pairFst`,
   `fixedPts` and `portList`, the list of ports (the permutation ρ⁻¹); `transpositorPerm`, the
   net `T_σ`.
2. Auxiliary lemmas: `getElem?_swapPairs` (`swapPairs p`, `ι_{p,q}` on lists, performs
   `swapIdx p`); `mem_portList`, `nodup_portList`, `length_portList` (every port occurs once in
   `portList σ`); `swapPairs_portList` (`ι_{p,q}` on the list of ports is σ on it);
   `transpositorPerm_eq_ofFn` (`T_σ` is `T_{p,q}` on the trees reordered by ρ⁻¹);
   `vars_transpositorPerm` (the names of `T_σ`).
3. Main results: `involutive_decomp`, the decomposition `σ = ρ⁻¹ * ι_{p,q} * ρ` of an involution;
   `transpositorPerm_transpositorPerm`, the property of page 84.
4. Example: `transpositorPerm_swap02`, the net `T_σ` for the transposition of ports `0` and `2`.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- `ι_{p,q}` (page 83) on positions numbered from `0`: exchange `0` with `1`, `2` with `3`, …,
`2p - 2` with `2p - 1`, and fix the positions from `2p` on. -/
def swapIdx
    -- the number `p` of exchanged pairs, and the position
    (p k : ℕ) :
    ℕ :=
  if k < 2 * p then (if k % 2 = 0 then k + 1 else k - 1) else k

-- The two facts about `swapIdx` that `swapPerm` needs.

/-- `swapIdx p` is an involution. -/
theorem swapIdx_swapIdx
    -- the number of exchanged pairs, and the position
    (p k : ℕ) :
    swapIdx p (swapIdx p k) = k := by
  unfold swapIdx
  split_ifs <;> omega

/-- `swapIdx p` maps `{0, …, n - 1}` to itself when `2p ≤ n`. -/
theorem swapIdx_lt
    -- `n` positions, of which the first `2p` are exchanged in pairs
    {n p k : ℕ}
    (h : 2 * p ≤ n)
    -- a position below `n`
    (hk : k < n) :
    swapIdx p k < n := by
  unfold swapIdx
  split_ifs <;> omega

/-- `ι_{p,q}` (page 83) as a permutation of `Fin n`, with `q = n - 2p`. -/
def swapPerm
    -- `n` positions, of which the first `2p` are exchanged in pairs
    (n p : ℕ)
    (h : 2 * p ≤ n) :
    Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun i => ⟨swapIdx p i, swapIdx_lt h i.2⟩)
    (fun i => Fin.ext (swapIdx_swapIdx p i))

-- `swapPerm` computes `swapIdx` on the values of the positions.
@[simp] theorem swapPerm_apply_val
    -- `n` positions, of which the first `2p` are exchanged in pairs
    (n p : ℕ)
    (h : 2 * p ≤ n)
    -- a position
    (i : Fin n) :
    (swapPerm n p h i : ℕ) = swapIdx p i := rfl

variable {n : ℕ}

/-- The first port of each transposition of σ: the ports `a` with `a < σ a`, increasing. -/
def pairFst
    -- a permutation of the `n` ports
    (σ : Equiv.Perm (Fin n)) :
    List (Fin n) :=
  (List.finRange n).filter fun x => x < σ x

/-- The fixed points of σ, increasing. -/
def fixedPts
    -- a permutation of the `n` ports
    (σ : Equiv.Perm (Fin n)) :
    List (Fin n) :=
  (List.finRange n).filter fun x => σ x = x

/-- The ports of `T_σ` in the order of the ports of `T_{p,q}` (page 84): `a, σ a` for each `a` of
`pairFst σ`, then the fixed points. This list is the permutation ρ⁻¹ of the paper. -/
def portList
    -- a permutation of the `n` ports
    (σ : Equiv.Perm (Fin n)) :
    List (Fin n) :=
  (pairFst σ).flatMap (fun a => [a, σ a]) ++ fixedPts σ

/-- The transpositor `T_σ` of an involutive permutation σ of the `n` ports (Lafont, page 84),
applied to the trees `ts i` plugged into its ports: the transpositor `T_{p,q}` of page 83, with
`p` the number of transpositions of σ, whose ports are permuted by ρ, port `j` of `T_{p,q}` being
port `(portList σ)[j]` of `T_σ`. It has no cell beyond those of `T_{p,q}`. -/
def transpositorPerm
    -- an involutive permutation of the `n` ports
    (σ : Equiv.Perm (Fin n))
    (_hσ : Function.Involutive σ)
    -- the trees plugged into the ports
    (ts : Fin n → Term sig ℕ) :
    Term sig ℕ :=
  transpositor (pairFst σ).length ((portList σ).map ts)

-- ============================================================================================
-- 2. Auxiliary lemmas
-- ============================================================================================

-- `ι_{p,q}` on lists.

/-- `swapPairs` does not change the length. -/
theorem length_swapPairs
    -- the type of the elements
    {α : Type*} :
    -- for every number of pairs `p` and every list `l`
    ∀ (p : ℕ) (l : List α),
      (swapPairs p l).length = l.length
  | 0, _ => rfl
  | p + 1, _ :: _ :: l => by simp [swapPairs, length_swapPairs p l]
  | _ + 1, [] => rfl
  | _ + 1, [_] => rfl

/-- `swapPairs p` (`ι_{p,q}` on lists, page 83) puts at position `k` the element at position
`swapIdx p k`, for a list of length at least `2p`. -/
theorem getElem?_swapPairs
    -- the type of the elements
    {α : Type*} :
    -- for every number of pairs `p` and every list `l` of length at least `2p`,
    ∀ (p : ℕ) (l : List α), 2 * p ≤ l.length →
      -- position `k` of `swapPairs p l` is position `swapIdx p k` of `l`
      ∀ k, (swapPairs p l)[k]? = l[swapIdx p k]?
  | 0, l, _, k => by simp [swapPairs, swapIdx]
  | p + 1, a :: b :: l, h, k => by
    have h' : 2 * p ≤ l.length := by simp at h; omega
    match k with
    | 0 => simp [swapPairs, swapIdx]
    | 1 =>
      have h1 : 1 < 2 * (p + 1) := by omega
      simp [swapPairs, swapIdx, h1]
    | k + 2 =>
      have hs : swapIdx (p + 1) (k + 2) = swapIdx p k + 2 := by
        unfold swapIdx
        split_ifs <;> omega
      simp [swapPairs, hs, getElem?_swapPairs p l h' k]
  | _ + 1, [], h, _ => by simp at h
  | _ + 1, [_], h, _ => by simp at h; omega

-- The length of the list `a₁, f a₁, a₂, f a₂, …` is twice that of `a₁, a₂, …`.
theorem length_flatMap_pair
    -- the type of the elements
    {α : Type*}
    -- the function giving the second element of each pair, and the first elements
    (f : α → α)
    (A : List α) :
    (A.flatMap fun a => [a, f a]).length = 2 * A.length := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [ih]; ring

-- `ι_{p,q}` exchanges the two elements of each of the `p` pairs and fixes the rest.
theorem swapPairs_flatMap_pair
    -- the type of the elements
    {α : Type*}
    -- the second element of each pair, the first elements, and the rest of the list
    (f : α → α)
    (A F : List α) :
    swapPairs A.length (A.flatMap (fun a => [a, f a]) ++ F)
      = A.flatMap (fun a => [f a, a]) ++ F := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [swapPairs, ih]

-- `ι_{p,q}` commutes with `List.map`.
theorem swapPairs_map
    -- the types of the elements, and the function mapped
    {α β : Type*}
    (g : α → β) :
    -- for every number of pairs `p` and every list `l`
    ∀ (p : ℕ) (l : List α),
      swapPairs p (l.map g) = (swapPairs p l).map g
  | 0, _ => rfl
  | p + 1, _ :: _ :: l => by simp [swapPairs, swapPairs_map g p l]
  | _ + 1, [] => rfl
  | _ + 1, [_] => rfl

-- The list of ports.

/-- Every port occurs in `portList σ`. -/
theorem mem_portList
    -- an involutive permutation of the `n` ports
    {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ)
    -- a port
    (x : Fin n) :
    x ∈ portList σ := by
  simp only [portList, pairFst, fixedPts, List.mem_append, List.mem_flatMap, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false]
  rcases lt_trichotomy x (σ x) with h | h | h
  · exact Or.inl ⟨x, h, Or.inl rfl⟩
  · exact Or.inr h.symm
  · refine Or.inl ⟨σ x, ?_, Or.inr (hσ x).symm⟩
    rwa [hσ x]

/-- No port occurs twice in `portList σ`. -/
theorem nodup_portList
    -- an involutive permutation of the `n` ports
    {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) :
    (portList σ).Nodup := by
  have hA : (pairFst σ).Nodup := (List.nodup_finRange n).filter _
  have hF : (fixedPts σ).Nodup := (List.nodup_finRange n).filter _
  have memA : ∀ a, a ∈ pairFst σ ↔ a < σ a := by simp [pairFst]
  have memF : ∀ a, a ∈ fixedPts σ ↔ σ a = a := by simp [fixedPts]
  rw [portList, List.nodup_append]
  refine ⟨?_, hF, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun a ha => ?_, ?_⟩
    · have := (memA a).1 ha
      simp [ne_of_lt this]
    · refine hA.imp_of_mem fun {a b} ha hb hab => ?_
      have ha' := (memA a).1 ha
      have hb' := (memA b).1 hb
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro x hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with h | h
      · exact hab h
      · rw [h, hσ] at ha'; exact lt_asymm hb' ha'
      · rw [← h, hσ] at hb'; exact lt_asymm ha' hb'
      · exact hab (σ.injective h)
  · intro x hx y hy hxy
    subst hxy
    rw [List.mem_flatMap] at hx
    obtain ⟨a, ha, hx⟩ := hx
    have ha' := (memA a).1 ha
    have hy' := (memF x).1 hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact absurd hy'.symm (ne_of_lt ha')
    · rw [hσ] at hy'; exact absurd hy' (ne_of_lt ha')

/-- `ι_{p,q}` applied to the list of ports gives σ applied to it: this is the decomposition
`σ ∘ ρ⁻¹ = ρ⁻¹ ∘ ι_{p,q}` of page 84, on lists. -/
theorem swapPairs_portList
    -- an involutive permutation of the `n` ports
    {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) :
    swapPairs (pairFst σ).length (portList σ) = (portList σ).map σ := by
  rw [portList, swapPairs_flatMap_pair, List.map_append, List.map_flatMap]
  congr 1
  · simp [hσ _]
  · symm
    rw [List.map_congr_left (g := id) fun x hx => by simpa [fixedPts] using hx]
    exact List.map_id _

-- The list of ports has `n` elements.
theorem length_portList
    -- an involutive permutation of the `n` ports
    {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) :
    (portList σ).length = n := by
  have := Fintype.card_congr ((nodup_portList hσ).getEquivOfForallMemList _ (mem_portList hσ))
  simpa using this

-- The `p` transpositions of σ take `2p ≤ n` ports.
theorem two_mul_le
    -- an involutive permutation of the `n` ports
    {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) :
    2 * (pairFst σ).length ≤ n := by
  have h := length_portList hσ
  rw [portList, List.length_append, length_flatMap_pair] at h
  omega

/-- The multiset of the ports, read in the order of `portList σ`, is the multiset of all ports. -/
theorem coe_portList
    -- an involutive permutation of the `n` ports
    {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) :
    ((portList σ : List (Fin n)) : Multiset (Fin n)) = Finset.univ.val := by
  have : (⟨(portList σ : Multiset (Fin n)), nodup_portList hσ⟩ : Finset (Fin n)) =
      Finset.univ :=
    Finset.eq_univ_iff_forall.2 (mem_portList hσ)
  exact congrArg Finset.val this

-- The transpositor `T_σ`.

/-- `T_σ` is `T_{p,q}` applied to the trees reordered by the permutation ρ⁻¹ of
`involutive_decomp` (page 84). -/
theorem transpositorPerm_eq_ofFn
    -- an involutive permutation of the `n` ports
    (σ : Equiv.Perm (Fin n))
    (hσ : Function.Involutive σ)
    -- the trees plugged into the ports
    (ts : Fin n → Term sig ℕ) :
    -- `T_σ` is `T_{p,q}` with, on its port `j`, the tree of port `(portList σ)[j]`
    transpositorPerm σ hσ ts
      = transpositor (pairFst σ).length
          (List.ofFn fun j : Fin n =>
            ts ((portList σ)[(j : ℕ)]'((length_portList hσ).symm ▸ j.2))) := by
  rw [transpositorPerm]
  congr 1
  apply List.ext_getElem
  · simp [length_portList hσ]
  · intro i h1 h2
    simp

/-- The names of `T_σ` (page 84) are those of the trees plugged into its ports. -/
theorem vars_transpositorPerm
    -- an involutive permutation of the `n` ports
    (σ : Equiv.Perm (Fin n))
    (hσ : Function.Involutive σ)
    -- the trees plugged into the ports
    (ts : Fin n → Term sig ℕ) :
    (transpositorPerm σ hσ ts).vars = Finset.univ.val.bind fun i => (ts i).vars := by
  rw [transpositorPerm, vars_transpositor, List.map_map, ← coe_portList hσ]
  simp [Multiset.bind, Multiset.join, Function.comp_def]

-- ============================================================================================
-- 3. Main results: the decomposition of an involution, and the property of `T_σ`
-- ============================================================================================

/-- The decomposition of an involution (Lafont, page 84): every involutive permutation σ of
`{0, …, n - 1}` is `ρ⁻¹ ∘ ι_{p,q} ∘ ρ` for a permutation ρ and `2p + q = n`. Here
`p = (pairFst σ).length` and ρ⁻¹ sends `j` to `(portList σ)[j]`. -/
theorem involutive_decomp
    -- an involutive permutation of the `n` ports
    (σ : Equiv.Perm (Fin n))
    (hσ : Function.Involutive σ) :
    -- there are a number `p` of pairs with `2p ≤ n` and a permutation ρ such that
    ∃ (p : ℕ) (h : 2 * p ≤ n) (ρ : Equiv.Perm (Fin n)),
      -- σ is `ι_{p,q}` conjugated by ρ
      σ = ρ⁻¹ * swapPerm n p h * ρ := by
  set l := portList σ
  have hlen : n = l.length := (length_portList hσ).symm
  let τ : Equiv.Perm (Fin n) :=
    (finCongr hlen).trans ((nodup_portList hσ).getEquivOfForallMemList _ (mem_portList hσ))
  have hτ : ∀ j : Fin n, (τ j : Fin n) = l[(j : ℕ)]'(hlen ▸ j.2) := fun j => rfl
  refine ⟨(pairFst σ).length, two_mul_le hσ, τ.symm, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨j, rfl⟩ := τ.surjective x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_symm]
  rw [show τ.symm (τ j) = j from τ.symm_apply_apply j]
  have key := getElem?_swapPairs (pairFst σ).length l (hlen ▸ two_mul_le hσ) j
  rw [swapPairs_portList hσ, List.getElem?_map] at key
  have hj : (j : ℕ) < l.length := hlen ▸ j.2
  have hj' : swapIdx (pairFst σ).length j < l.length := hlen ▸ swapIdx_lt (two_mul_le hσ) j.2
  rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] at key
  simp only [Option.map_some, Option.some.injEq] at key
  rw [hτ, hτ]
  simpa using key

/-- The property of the transpositor `T_σ` (Lafont, page 84): two copies of `T_σ` plugged by their
roots reduce to the wiring σ, the equations joining port `i` of one copy to port `σ i` of the
other. It follows from the property of `T_{p,q}` (`transpositor_transpositor`, page 83), since
`ι_{p,q}` on the list of ports is σ on it (`swapPairs_portList`). -/
theorem transpositorPerm_transpositorPerm
    -- an involutive permutation of the `n` ports
    {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (hσ : Function.Involutive σ)
    -- the trees plugged into the ports of the two copies
    (ts us : Fin n → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet) :
    -- the two copies of `T_σ`, plugged by their roots, reduce to the equations joining
    -- port `i` of the first to port `σ i` of the second
    Red (s(transpositorPerm σ hσ ts, transpositorPerm σ hσ us) ::ₘ Δ)
      ((Finset.univ.val.map fun i => s(ts i, us (σ i))) + Δ) := by
  have h := transpositor_transpositor (pairFst σ).length ((portList σ).map ts)
    ((portList σ).map us) Δ (by simp)
  refine h.cast rfl ?_
  rw [swapPairs_map, swapPairs_portList hσ, List.map_map, List.zipWith_map, List.zipWith_self,
    ← Multiset.map_coe, coe_portList hσ]
  rfl

-- ============================================================================================
-- 4. Example
-- ============================================================================================

/-- `T_σ` for `n = 3` and σ the transposition of ports `0` and `2`: `p = 1`, the list of ports
is `0, 2, 1`, so `T_σ` is `T_{1,1}` with the trees on ports `0, 2` under the `con` and the tree on
port `1` on the free auxiliary port of the `dup` (page 83, figure of `T_{1,1}`). -/
theorem transpositorPerm_swap02
    -- the trees plugged into the three ports
    (ts : Fin 3 → Term sig ℕ) :
    transpositorPerm (Equiv.swap 0 2) (Equiv.swap_apply_self 0 2) ts
      = mkDup (mkCon (ts 0) (ts 2)) (ts 1) := by
  have hl : portList (Equiv.swap (0 : Fin 3) 2) = [0, 2, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 3) 2) = [0] := by decide
  simp only [transpositorPerm, hl, hp, List.map_cons, List.map_nil, List.length_singleton]
  rfl

end INet.Comb
