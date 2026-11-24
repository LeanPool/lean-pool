/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Count
public import Mathlib.Data.Fintype.Fin

/-!
# Iterated commutators in associative algebras

Powers and sequences of adjoint maps, nested brackets, and their list and tuple
representations. The first layer is innermost. These constructions and identities
require no norm or topology. The existing `TrotterError` names are retained.
`adSequence` applies the linear endomorphism `adSequenceLinear`.

## Main definitions and results

* `TrotterError.adSequence` applies a sequence of adjoint powers, starting with the innermost layer.
* `TrotterError.adSequence_eq_nestedCommOfList` rewrites that action as a nested bracket of a list.
* `TrotterError.adSequence_eq_nestedComm_expandTuple` gives the corresponding finite-tuple formula.
-/

@[expose] public section

namespace TrotterError

open Finset LieAlgebra
open scoped algebraMap

attribute [local instance] LieRing.ofAssociativeRing

@[simp] lemma ad_pow_succ {R 𝔸 : Type*} [CommRing R] [Ring 𝔸] [LieAlgebra R 𝔸] (A : 𝔸) (q : ℕ)
    (B : 𝔸) : ((ad R 𝔸 A) ^ (q + 1)) B = ⁅A, ((ad R 𝔸 A) ^ q) B⁆ := by simp [pow_succ']

/-- The `q`-fold iterated adjoint `ad_A^q = (ad A)^q`, as an ℝ-linear endomorphism of `𝔸`. -/
abbrev adPow {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (q : ℕ) : Module.End ℝ 𝔸 :=
  (ad ℝ 𝔸 A) ^ q

/-- The composed adjoint sequence as a linear endomorphism, with the last layer outermost. -/
def adSequenceLinear {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) : Module.End ℝ 𝔸 :=
  match s with
  | 0 => 1
  | s + 1 =>
      adPow (A (Fin.last s)) (q (Fin.last s)) *
        adSequenceLinear (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc)

/-- The iterated `ad` over a sequence of operators with multiplicities,
`ad_{A ⟨s-1⟩}^{q ⟨s-1⟩} ⋯ ad_{A ⟨0⟩}^{q ⟨0⟩}(B)`, where `A ⟨0⟩` is applied first
(innermost) and `A ⟨s-1⟩` is applied last (outermost). -/
def adSequence {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) : 𝔸 :=
  adSequenceLinear A q B

@[simp] lemma adSequence_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    (A : Fin 0 → 𝔸) (q : Fin 0 → ℕ) (B : 𝔸) : adSequence A q B = B := rfl

lemma adSequence_succ {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (q : Fin (s + 1) → ℕ) (B : 𝔸) :
    adSequence A q B = adPow (A (Fin.last s)) (q (Fin.last s))
      (adSequence (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc) B) := rfl

/-- The linear-map view evaluates to the original iterated adjoint sequence. -/
lemma adSequenceLinear_apply {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) : adSequenceLinear A q B = adSequence A q B := rfl

/-- The nested commutator `[H ⟨p⟩, [H ⟨p-1⟩, ⋯ [H ⟨1⟩, H ⟨0⟩] ⋯]]` with exactly `p`
brackets: `H ⟨0⟩` is innermost and `H ⟨p⟩` is outermost. -/
def nestedComm {𝔸 : Type*} [Ring 𝔸] {p : ℕ} (H : Fin (p + 1) → 𝔸) : 𝔸 :=
  match p with
  | 0 => H ⟨0, by simp⟩
  | p + 1 => ⁅H ⟨p + 1, by simp⟩, nestedComm (fun i : Fin (p + 1) => H i.castSucc)⁆

/-- Appending a zero multiplicity on the outermost layer does not change `adSequence`. -/
lemma adSequence_snoc_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q 0) B = adSequence (fun i : Fin m => A i.castSucc) q B := by
  rw [adSequence_succ]
  simp [Fin.snoc_last]

/-- Appending a multiplicity on the outermost layer of `adSequence`: the `k`-fold commutator of
`A ⟨m⟩` applied to the inner sequence. -/
lemma adSequence_snoc {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (k : ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q k) B =
      adPow (A (Fin.last m)) k (adSequence (fun i : Fin m => A i.castSucc) q B) := by
  rw [adSequence_succ]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

/-- `adSequence A q` commutes with ℝ-scalar multiplication in its last argument `B`. -/
lemma adSequence_smul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (r : ℝ) (X : 𝔸) :
    adSequence A q (r • X) = r • adSequence A q X := by
  simpa only [adSequenceLinear_apply] using (adSequenceLinear A q).map_smul r X

/-- `nestedComm` commutes with reindexing a tuple by a `Fin.cast`. -/
lemma nestedComm_cast {𝔸 : Type*} [Ring 𝔸] {n m : ℕ} (h : n = m) (H : Fin (m + 1) → 𝔸) :
    nestedComm (H ∘ Fin.cast (congrArg (· + 1) h)) = nestedComm H := by
  subst h
  rfl

/-- The nested commutator of a list with an innermost seed: `nestedCommOfList b [x₁, …, xₙ] =
⁅xₙ, ⋯ ⁅x₁, b⁆ ⋯⁆` (the head `x₁` is innermost and the last element `xₙ` is outermost). -/
def nestedCommOfList {𝔸 : Type*} [Ring 𝔸] (b : 𝔸) : List 𝔸 → 𝔸 :=
  List.foldl (fun acc X => ⁅X, acc⁆) b

@[simp] lemma nestedCommOfList_nil {𝔸 : Type*} [Ring 𝔸] (b : 𝔸) :
    nestedCommOfList b [] = b := rfl

@[simp] lemma nestedCommOfList_append {𝔸 : Type*} [Ring 𝔸] (b X : 𝔸) (L : List 𝔸) :
    nestedCommOfList b (L ++ [X]) = ⁅X, nestedCommOfList b L⁆ := by
  rw [nestedCommOfList, List.foldl_append]
  rfl

/-- `nestedCommOfList b (L ++ replicate k X) = adPow X k (nestedCommOfList b L)`: the `k`
outermost copies of `X` contribute the `k`-fold iterated commutator. -/
lemma nestedCommOfList_append_replicate {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (b X : 𝔸) (L : List 𝔸)
    (k : ℕ) :
    nestedCommOfList b (L ++ List.replicate k X) = adPow X k (nestedCommOfList b L) := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [List.replicate_succ', ← List.append_assoc, nestedCommOfList_append, ad_pow_succ, ih]

/-- The tuple `Fin (L.length + 1) → 𝔸` with `0 ↦ b` and `t + 1 ↦ f (L[t])`. -/
def listIndexed {ι 𝔸 : Type*} (b : 𝔸) (L : List ι) (f : ι → 𝔸) : Fin (L.length + 1) → 𝔸 :=
  Fin.cons b (fun t : Fin L.length => f (L[t.val]'t.2))

/-- `nestedComm` peels the outermost element of a `Fin.cons`-built tuple. -/
lemma nestedComm_cons_succ {𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin (n + 1) → 𝔸) :
    nestedComm (Fin.cons b tail) =
      ⁅tail (Fin.last n), nestedComm (Fin.cons b (fun i : Fin n => tail i.castSucc))⁆ := by
  rw [nestedComm]
  apply congrArg₂ (fun x y : 𝔸 => ⁅x, y⁆)
  · rw [show ((⟨n + 1, by simp⟩ : Fin (n + 2)) = Fin.succ (Fin.last n)) by rfl]
    rw [Fin.cons_succ]
  · congr 1
    funext i
    refine Fin.cases ?zero ?succ i
    · simp [Fin.cons_zero]
    · intro j
      rw [Fin.castSucc_succ, Fin.cons_succ, Fin.cons_succ]

/-- `nestedComm` of a `Fin.cons`-built tuple equals the list nested commutator of the
`List.ofFn` image of the tail. -/
lemma nestedComm_ofFn_cons {𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin n → 𝔸) :
    nestedComm (Fin.cons b tail) = nestedCommOfList b (List.ofFn tail) := by
  induction n with
  | zero => simp [Fin.cons, List.ofFn, nestedComm]
  | succ n ih =>
      rw [nestedComm_cons_succ, List.ofFn_succ_last, nestedCommOfList_append,
        ih (fun i : Fin n => tail i.castSucc)]

/-- `nestedComm` of `listIndexed` is the list nested commutator. -/
lemma nestedComm_listIndexed {𝔸 : Type*} [Ring 𝔸] {ι : Type*} (b : 𝔸) (L : List ι)
    (f : ι → 𝔸) :
    nestedComm (listIndexed b L f) = nestedCommOfList b (L.map f) := by
  rw [listIndexed, nestedComm_ofFn_cons, List.ofFn_getElem_eq_map]

/-- The list of the non-innermost operators of `expandTuple f q b`, each `f i` repeated `q i`
times, in increasing order of `i`. -/
def layersOf {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) : List α :=
  (List.finRange s).flatMap fun i => List.replicate (q i) (f i)

/-- Prepending a multiplicity places that many copies of the first layer at the head. -/
lemma layersOf_cons {α : Type*} {s : ℕ} (f : Fin (s + 1) → α) (q : Fin s → ℕ) (k : ℕ) :
    layersOf f (Fin.cons k q) = List.replicate k (f 0) ++ layersOf (fun i ↦ f i.succ) q := by
  simp only [layersOf, List.finRange_succ, List.flatMap_cons, List.flatMap_map,
    Fin.cons_zero, Fin.cons_succ]

/-- `layersOf f q` has length `∑ q`. -/
lemma layersOf_length {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) :
    (layersOf f q).length = ∑ i : Fin s, q i := by
  induction s with
  | zero => simp [layersOf]
  | succ s ih =>
      rw [layersOf, List.finRange_succ]
      simp only [List.flatMap_cons, List.flatMap_map, List.length_append, List.length_replicate]
      change q 0 + (layersOf (f ∘ Fin.succ) (q ∘ Fin.succ)).length = ∑ i : Fin (s + 1), q i
      rw [ih (f ∘ Fin.succ) (q ∘ Fin.succ)]
      simp [Fin.sum_univ_succ]

/-- `layersOf` commutes with post-composition. -/
lemma layersOf_map {α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) :
    layersOf (g ∘ f) q = (layersOf f q).map g := by
  rw [layersOf, layersOf, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  simp [List.map_replicate]

/-- The list of indices, each `i : Fin s` repeated `q i` times. -/
def layerIndices {s : ℕ} (q : Fin s → ℕ) : List (Fin s) := layersOf (fun i : Fin s => i) q

/-- The index `i` occurs exactly `q i` times in `layerIndices q`. -/
lemma layersOf_count {s : ℕ} (q : Fin s → ℕ) (i : Fin s) :
    (layersOf (fun i : Fin s => i) q).count i = q i := by
  induction s with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      rw [layersOf, List.finRange_succ_last]
      simp only [List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
      rw [List.count_append]
      refine Fin.lastCases ?_ ?_ i
      · change List.count (Fin.last s)
            (layersOf (Fin.castSucc ∘ (fun i : Fin s => i)) (q ∘ Fin.castSucc)) +
              List.count (Fin.last s) (List.replicate (q (Fin.last s)) (Fin.last s)) =
            q (Fin.last s)
        rw [layersOf_map Fin.castSucc (fun i : Fin s => i) (q ∘ Fin.castSucc)]
        have hmem : Fin.last s ∉
            (layersOf (fun i : Fin s => i) (q ∘ Fin.castSucc)).map Fin.castSucc := by
          intro h
          rw [List.mem_map] at h
          rcases h with ⟨x, -, hx⟩
          exact (Fin.castSucc_lt_last x).ne hx
        rw [List.count_eq_zero_of_not_mem hmem, List.count_replicate]
        simp
      · intro j
        change List.count j.castSucc
            (layersOf (Fin.castSucc ∘ (fun i : Fin s => i)) (q ∘ Fin.castSucc)) +
              List.count j.castSucc (List.replicate (q (Fin.last s)) (Fin.last s)) =
            q j.castSucc
        rw [layersOf_map Fin.castSucc (fun i : Fin s => i) (q ∘ Fin.castSucc),
          List.count_map_of_injective _ Fin.castSucc (Fin.castSucc_injective s) j,
          ih (q ∘ Fin.castSucc) j]
        have hne : Fin.last s ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
        rw [List.count_replicate]
        simp [hne]

/-- Expand a multiplicity vector `q : Fin s → ℕ` into a tuple of length `∑ q + 1`: the entry at
position `0` is `b`, and the entries at positions `1` through `∑ q` are the layer operators
`f i`, each repeated `q i` times. -/
def expandTuple {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    Fin (∑ i : Fin s, q i + 1) → α :=
  Fin.cons b (fun t : Fin (∑ i : Fin s, q i) =>
    f ((layerIndices q)[t.val]'(by simp [layerIndices, layersOf_length])))

/-- The entry at position `0` of `expandTuple` is the innermost `b`. -/
lemma expandTuple_zero {α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    expandTuple f q b 0 = b := by
  simp [expandTuple]

/-- The entry at position `t + 1` of `expandTuple f q b` is `f` applied to the `t`-th layer
index. -/
lemma expandTuple_succ {α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) (t : ℕ)
    (ht : t < ∑ i : Fin s, q i) :
    expandTuple f q b ⟨t + 1, Nat.succ_lt_succ ht⟩ =
      f ((layersOf (fun i : Fin s => i) q)[t]'(by simpa [layersOf_length] using ht)) := by
  rw [expandTuple]
  rw [show (⟨t + 1, Nat.succ_lt_succ ht⟩ : Fin ((∑ i : Fin s, q i) + 1)) =
      Fin.succ (⟨t, ht⟩ : Fin (∑ i : Fin s, q i)) by simp]
  rw [Fin.cons_succ]
  congr

/-- `expandTuple` is natural in the target:
`expandTuple (g ∘ f) q (g b) = g ∘ expandTuple f q b`. -/
lemma expandTuple_nat {α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    expandTuple (g ∘ f) q (g b) = g ∘ expandTuple f q b := by
  funext j
  cases j using Fin.cases <;> rfl

/-- `adSequence A q B` equals the list nested commutator of the layers. -/
lemma adSequence_eq_nestedCommOfList {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A q B = nestedCommOfList B (layersOf A q) := by
  induction s with
  | zero => simp [layersOf]
  | succ s ih =>
      rw [adSequence_succ, ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc)]
      have hlayers : layersOf A q = layersOf (fun i : Fin s => A i.castSucc)
          (fun i : Fin s => q i.castSucc) ++
          List.replicate (q (Fin.last s)) (A (Fin.last s)) := by
        simp [layersOf, List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      rw [hlayers, nestedCommOfList_append_replicate]

/-- `adSequence A q B` is exactly the nested commutator of the expanded tuple. -/
lemma adSequence_eq_nestedComm_expandTuple {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A q B = nestedComm (expandTuple A q B) := by
  rw [adSequence_eq_nestedCommOfList A q B]
  rw [show layersOf A q = (layerIndices q).map A by
    rw [layerIndices]
    exact layersOf_map A (fun i : Fin s => i) q]
  rw [← nestedComm_listIndexed B (layerIndices q) A]
  rw [show expandTuple A q B =
      listIndexed B (layerIndices q) A ∘ Fin.cast (congrArg (· + 1)
        (show (∑ i : Fin s, q i) = (layerIndices q).length by
          rw [layerIndices, layersOf_length])) by
    ext j
    refine Fin.cases ?zero ?succ j
    · simp [expandTuple, listIndexed, Fin.cons_zero]
    · intro t
      simp [expandTuple, listIndexed, Fin.cons_succ, Fin.cast_succ_eq, Fin.val_cast]]
  rw [nestedComm_cast (show (∑ i : Fin s, q i) = (layerIndices q).length by
    rw [layerIndices, layersOf_length]) (listIndexed B (layerIndices q) A)]

/-- `adPow (c • A) k X = c ^ k • adPow A k X`. -/
lemma adPow_smul_left {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (c : ℝ) (A : 𝔸) (k : ℕ) (X : 𝔸) :
    adPow (c • A) k X = c ^ k • adPow A k X := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [ad_pow_succ, ad_pow_succ, ih, smul_lie, lie_smul, smul_smul, pow_succ, mul_comm]

/-- `adSequence (fun i => c i • A i) q B = (∏ i, c i ^ q i) • adSequence A q B`. -/
lemma adSequence_smul_fun {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (c : Fin s → ℝ)
    (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) :
    adSequence (fun i => c i • A i) q B = (∏ i : Fin s, (c i) ^ q i) • adSequence A q B := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [adSequence_succ, adSequence_succ, ih (fun i => c i.castSucc) (fun i => A i.castSucc)
          (fun i => q i.castSucc), adPow_smul_left, (adPow (A (Fin.last s))
          (q (Fin.last s))).map_smul, smul_smul, Fin.prod_univ_castSucc, mul_comm]

/-- Transporting operators and multiplicities along a length equality preserves `adSequence`.
This only changes the index type; it does not permute the commutators. -/
lemma adSequence_cast {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s t : ℕ} (h : s = t)
    (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) :
    adSequence (fun i : Fin t => A (Fin.cast h.symm i))
      (fun i => q (Fin.cast h.symm i)) B = adSequence A q B := by
  subst h
  rfl

/-- `adSequence A q (∑ γ, H γ) = ∑ γ, adSequence A q (H γ)`. -/
lemma adSequence_sum {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ)
    {ι : Type*} [Fintype ι] (H : ι → 𝔸) :
    adSequence A q (∑ γ : ι, H γ) = ∑ γ : ι, adSequence A q (H γ) := by
  simpa only [adSequenceLinear_apply] using map_sum (adSequenceLinear A q) H Finset.univ

/-- Splitting off the innermost multiplicity first applies its iterated adjoint. -/
lemma adSequence_cons {A : Type*} [Ring A] [Algebra ℝ A] {s : ℕ}
    (Z : Fin (s + 1) → A) (q : Fin s → ℕ) (k : ℕ) (B : A) :
    adSequence Z (Fin.cons k q) B =
      adSequence (fun i ↦ Z i.succ) q (adPow (Z 0) k B) := by
  rw [adSequence_eq_nestedCommOfList, adSequence_eq_nestedCommOfList, layersOf_cons,
    nestedCommOfList, List.foldl_append]
  have hrepl := nestedCommOfList_append_replicate B (Z 0) [] k
  simpa only [List.nil_append, nestedCommOfList, List.foldl_nil] using
    congrArg (fun b ↦ (layersOf (fun i ↦ Z i.succ) q).foldl (fun b z ↦ ⁅z, b⁆) b) hrepl

/-- Prepending a zero multiplicity shifts the layers: the innermost `f 0` contributes nothing and
each `f (i.succ)` becomes the `i`-th layer. -/
lemma layersOf_cons_zero {α : Type*} {s : ℕ} (f : Fin (s + 1) → α) (q : Fin s → ℕ) :
    layersOf f (Fin.cons 0 q) = layersOf (fun i : Fin s => f i.succ) q := by
  rw [layersOf_cons, List.replicate_zero, List.nil_append]

/-- `adSequence A (Fin.cons 0 q) B = adSequence (fun i => A i.succ) q B`: a zero innermost
multiplicity lets the innermost `A ⟨0⟩` drop out. -/
lemma adSequence_cons_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A (Fin.cons 0 q) B = adSequence (fun i : Fin s => A i.succ) q B := by
  simpa only [adPow, pow_zero, one_apply_eq_self] using adSequence_cons A q 0 B

end TrotterError
