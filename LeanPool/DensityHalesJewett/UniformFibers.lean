/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.Subspace
public import LeanPool.DensityHalesJewett.Word
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Preliminary density lemmas

Multidimensional density Hales--Jewett, uniform fibers, and the restricted-alphabet subspace
lemma. All subspaces below are Mathlib's `Combinatorics.Subspace`.

Lemmas that use density Hales--Jewett over `k` letters take a bound `F` for it, `IsDHJBound k F`,
and their dimensions are explicit in `F`.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- `n` is a dimension in which density Hales--Jewett holds for `k` letters and density `δ`: every
set of at least `δ * k ^ n` words of length `n` over `k` letters contains a combinatorial line. -/
def IsDHJDimension (k : ℕ) (δ : ℝ) (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n → Fin k), δ * (k : ℝ) ^ n ≤ #A →
    ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A

/-- A dimension in which density Hales--Jewett holds for a density also works for every larger
density. -/
lemma IsDHJDimension.mono {k n : ℕ} {δ ρ : ℝ} (h : IsDHJDimension k δ n) (hδρ : δ ≤ ρ) :
    IsDHJDimension k ρ n :=
  fun A hA ↦ h A ((mul_le_mul_of_nonneg_right hδρ (by positivity)).trans hA)

/-- `F` is a bound for density Hales--Jewett over `k` letters: for every density `δ > 0`, it holds
in every dimension `n ≥ F δ`. -/
def IsDHJBound (k : ℕ) (F : ℝ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ n, F δ ≤ n → IsDHJDimension k δ n

namespace Subspace

/-- The one-dimensional case of multidimensional density Hales--Jewett. -/
lemma exists_one_of_density {k n : ℕ} {δ : ℝ} (h : IsDHJDimension k δ n)
    {A : Finset (Fin n → Fin k)} (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin 1) (Fin k) (Fin n), IsContained V A := by
  obtain ⟨l, hl⟩ := h A hA
  refine ⟨lineToSubspaceFinOne l, ?_⟩
  intro x
  simpa using hl (x 0)

/-- A line is equivalently an `Option`-valued index word with at least one variable
coordinate. -/
private noncomputable def lineIndexEquiv (α ι : Type*) :
    Combinatorics.Line α ι ≃
      {f : ι → Option α // ¬ ∀ i, f i ≠ none} where
  toFun l := ⟨l.idxFun, by simpa using l.proper⟩
  invFun f := ⟨f, by simpa using f.property⟩
  left_inv l := by cases l; rfl
  right_inv _ := Subtype.ext rfl

/-- An index word with no variable coordinate is equivalently an ordinary alphabet word. -/
private noncomputable def fixedIndexWordEquiv (α ι : Type*) [Nonempty α] :
    {f : ι → Option α // ∀ i, f i ≠ none} ≃ (ι → α) where
  toFun f i := (f.1 i).getD (Classical.arbitrary α)
  invFun x := ⟨some ∘ x, by simp⟩
  left_inv f := by
    refine Subtype.ext (funext ?_)
    intro i
    cases hi : f.1 i with
    | none => exact (f.2 i hi).elim
    | some b => simp [hi]
  right_inv x := by simp

/-- The exact number of combinatorial line structures in a nonempty finite-alphabet word cube. -/
lemma card_line {k : ℕ} (m : ℕ) (hk : 0 < k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))] :
    Fintype.card (Combinatorics.Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [Fintype.card_congr (lineIndexEquiv (Fin k) (Fin m)),
    Fintype.card_subtype_compl (fun f : Fin m → Option (Fin k) ↦ ∀ i, f i ≠ none),
    Fintype.card_pi_const, Fintype.card_option, Fintype.card_fin,
    Fintype.card_congr (fixedIndexWordEquiv (Fin k) (Fin m)),
    Fintype.card_pi_const, Fintype.card_fin]

/-- The finite enumeration of line structures induced by their index words. -/
@[instance_reducible]
noncomputable def lineFintype (k m : ℕ) : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
  Fintype.ofInjective (fun l ↦ l.idxFun) fun l₁ l₂ h ↦ by
    cases l₁
    cases l₂
    cases h
    rfl

/-- A subspace over the empty alphabet, obtained by repeating parameter coordinates. -/
def emptyAlphabetSubspace {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Combinatorics.Subspace (Fin m) (Fin 0) (Fin n) where
  idxFun i := Sum.inr ⟨i.val % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm)⟩
  proper e := ⟨Fin.castLE hmn e, by simp [Nat.mod_eq_of_lt e.isLt]⟩

/-- Convert the cardinal density hypothesis to the normalized finite-set density inequality. -/
lemma density_le_of_card_le {k n : ℕ} (hk : 0 < k) {δ : ℝ}
    {A : Finset (Fin n → Fin k)} (hA : δ * (k : ℝ) ^ n ≤ #A) :
    δ ≤ (A.dens : ℝ) := by
  rw [nnratCast_dens, le_div_iff₀ (by simp [hk])]
  simpa using hA

/-- Convert a normalized density lower bound back to the cardinal form used by the
density Hales--Jewett assertion. -/
lemma card_le_of_density_le {k n : ℕ} (hk : 0 < k) {δ : ℝ}
    {A : Finset (Fin n → Fin k)} (hA : δ ≤ (A.dens : ℝ)) :
    δ * (k : ℝ) ^ n ≤ #A := by
  rw [nnratCast_dens, le_div_iff₀ (by simp [hk])] at hA
  simpa using hA

/-- One fiber of a map to a finite nonempty type has at least the average relative density. -/
lemma exists_fiber_density {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (s : Finset X) (f : X → Y) :
    ∃ y, (s.filter fun x ↦ f x = y).dens ≥ (s.dens : ℝ) / Fintype.card Y := by
  obtain ⟨y, -, hy⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun _ _ ↦ mem_univ _)
    univ_nonempty (s := s) (f := f) (b := (#s : ℝ) / Fintype.card Y) (by simp [mul_div_cancel₀])
  refine ⟨y, ?_⟩
  rw [ge_iff_le, nnratCast_dens, nnratCast_dens, div_right_comm]
  gcongr

/-- At least half the ambient density lies on prefixes with fiber density at least half as large. -/
lemma half_density_prefixes {k p q : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ)
    {A : Finset (Fin p ⊕ Fin q → Fin k)} (hA : δ ≤ (A.dens : ℝ)) :
    δ / 2 ≤
      ((univ.filter fun x : Fin p → Fin k ↦ δ / 2 ≤ ((fiber A x).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hδ₁ : δ ≤ 1 := hA.trans (by exact_mod_cast dens_le_one)
  refine le_trans ?_ (density_ge_threshold (fun x ↦ by exact_mod_cast dens_le_one)
    (by linarith : δ / 2 < δ) (by rwa [average_density_fiber]))
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- A dense suffix fiber contains a line whose points remain in the ambient family. -/
lemma exists_line_of_fiber_density {k p q : ℕ} (hk : 0 < k) {δ : ℝ}
    (hq : IsDHJDimension k δ q)
    {A : Finset (Fin p ⊕ Fin q → Fin k)} {x : Fin p → Fin k}
    (hx : δ ≤ ((fiber A x).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin q), ∀ a, Sum.elim x (l a) ∈ A := by
  obtain ⟨l, hl⟩ := hq (fiber A x) (card_le_of_density_le hk hx)
  exact ⟨l, fun a ↦ mem_fiber.mp (hl a)⟩

/-- Density Hales--Jewett in many slices, followed by pigeonhole on lines: if a set `B` of indices
of density at least `ρ > 0` has slices of density at least `δ`, in a dimension `q` where density
Hales--Jewett holds at density `δ`, then one line lies in the slices over a set of indices of
density at least `ρ` divided by the number of lines. -/
lemma exists_line_forall_mem_slices {P : Type*} [Fintype P] {k q : ℕ} (hk : 0 < k) {δ ρ : ℝ}
    (hq : IsDHJDimension k δ q) (S : P → Finset (Fin q → Fin k)) {B : Finset P} (hρ : 0 < ρ)
    (hB : ρ ≤ (B.dens : ℝ)) (hS : ∀ y ∈ B, δ ≤ ((S y).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin q),
      ρ / ((k + 1) ^ q - k ^ q : ℕ) ≤ ((univ.filter fun y ↦ ∀ a, l a ∈ S y).dens : ℝ) := by
  classical
  let := lineFintype k q
  have hline (y : P) (hy : y ∈ B) : ∃ l : Combinatorics.Line (Fin k) (Fin q), ∀ a, l a ∈ S y :=
    hq (S y) (card_le_of_density_le hk (hS y hy))
  obtain ⟨y₀, hy₀⟩ := (dens_pos (s := B)).1 (by exact_mod_cast hρ.trans_le hB)
  have : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨(hline y₀ hy₀).choose⟩
  choose! lineAt hlineAt using hline
  obtain ⟨l, hl⟩ := exists_fiber_density B lineAt
  refine ⟨l, le_trans ?_ (hl.trans ?_)⟩
  · rw [← card_line q hk]
    gcongr
  · refine mod_cast dens_le_dens ?_
    intro y hy
    obtain ⟨hyB, rfl⟩ := mem_filter.1 hy
    simpa using hlineAt y hyB

/-- One suffix line is complete above a positive-density family of prefixes. -/
lemma exists_common_dense_line {k p q : ℕ} (hk : 0 < k)
    {δ : ℝ} (hδ : 0 < δ) (hq : IsDHJDimension k (δ / 2) q)
    {A : Finset (Fin p ⊕ Fin q → Fin k)} (hA : δ ≤ (A.dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin q),
      δ / (2 * ((k + 1) ^ q - k ^ q : ℕ)) ≤
        ((univ.filter fun x : Fin p → Fin k ↦ ∀ a, Sum.elim x (l a) ∈ A).dens : ℝ) := by
  obtain ⟨l, hl⟩ := exists_line_forall_mem_slices hk hq (fiber A) (half_pos hδ)
    (half_density_prefixes hk hδ hA) fun x hx ↦ (mem_filter.1 hx).2
  exact ⟨l, by simpa [div_div] using hl⟩

/-- Split the coordinates of a word family into a prefix and a suffix along a cut equivalence. -/
def splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : Finset (Fin p ⊕ Fin q → Fin alphabet) :=
  A.map (e.arrowCongr (Equiv.refl (Fin alphabet))).symm.toEmbedding

@[simp]
lemma mem_splitWords {alphabet p q n : ℕ} {e : Fin p ⊕ Fin q ≃ Fin n}
    {A : Finset (Fin n → Fin alphabet)} {w : Fin p ⊕ Fin q → Fin alphabet} :
    w ∈ splitWords e A ↔ w ∘ e.symm ∈ A := by
  rw [splitWords, mem_map_equiv, Equiv.symm_symm]
  rfl

@[simp]
lemma dens_splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : (splitWords e A).dens = A.dens := by
  rw [splitWords, dens_map_equiv]

/-- The canonical cut equivalence associated with a decomposition of the ambient dimension. -/
def cutEquiv {p q n : ℕ} (h : p + q = n) : Fin p ⊕ Fin q ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

/-- A dimension for multidimensional density Hales--Jewett over `k` letters, by induction on the
dimension `m` of the subspace sought, given a bound `F` for density Hales--Jewett over `k`
letters. -/
noncomputable def densityBound (k : ℕ) (F : ℝ → ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | 1, δ => F δ
  | m + 2, δ =>
    densityBound k F (m + 1)
        (δ / (2 * ((k + 1) ^ max 1 (F (δ / 2)) - k ^ max 1 (F (δ / 2)) : ℕ))) +
      max 1 (F (δ / 2))

lemma densityBound_succ (k : ℕ) (F : ℝ → ℕ) {m : ℕ} (hm : 1 ≤ m) (δ : ℝ) :
    densityBound k F (m + 1) δ =
      densityBound k F m
          (δ / (2 * ((k + 1) ^ max 1 (F (δ / 2)) - k ^ max 1 (F (δ / 2)) : ℕ))) +
        max 1 (F (δ / 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

/-- An `m`-dimensional subspace of the prefix coordinates and a line of the suffix coordinates
whose concatenations all lie in a family give an `(m + 1)`-dimensional subspace in it. -/
private lemma exists_isContained_of_concat_mem {k m p q n : ℕ} {e : Fin p ⊕ Fin q ≃ Fin n}
    {A : Finset (Fin n → Fin k)} {V : Combinatorics.Subspace (Fin m) (Fin k) (Fin p)}
    {l : Combinatorics.Line (Fin k) (Fin q)} (h : ∀ x a, Sum.elim (V x) (l a) ∈ splitWords e A) :
    ∃ W : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin n), IsContained W A := by
  refine ⟨(concat V (lineToSubspaceFinOne l)).reindex finSumFinEquiv (Equiv.refl _) e, ?_⟩
  intro z
  have hz : z ∘ finSumFinEquiv = Sum.elim (fun i ↦ z (Fin.castAdd 1 i)) fun _ ↦ z (Fin.last m) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => rw [Fin.eq_zero i]; rfl
  convert mem_splitWords.1 (h (fun i ↦ z (Fin.castAdd 1 i)) (z (Fin.last m))) using 1
  funext i
  simp [Combinatorics.Subspace.reindex_apply, hz]

/-- Multidimensional density Hales--Jewett: in every dimension `n ≥ densityBound k F m δ`, a family
of density `δ` over `k` letters contains an `m`-dimensional subspace. -/
lemma exists_of_density {k : ℕ} (hk : 0 < k) {F : ℝ → ℕ} (hF : IsDHJBound k F)
    {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : densityBound k F m δ ≤ n)
    {A : Finset (Fin n → Fin k)} (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  classical
  induction m, hm using Nat.le_induction generalizing δ n with
  | base => exact exists_one_of_density (hF δ hδ n hn) hA
  | succ m hm ih =>
    rw [densityBound_succ k F hm] at hn
    set q := max 1 (F (δ / 2))
    have hpq : n - q + q = n := Nat.sub_add_cancel (by omega)
    obtain ⟨l, hl⟩ := exists_common_dense_line (A := splitWords (cutEquiv hpq) A) hk hδ
      (hF _ (half_pos hδ) q (le_max_right _ _)) (by simpa using density_le_of_card_le hk hA)
    obtain ⟨V, hV⟩ := ih (div_pos hδ (mul_pos two_pos (Nat.cast_pos.2 (Nat.sub_pos_of_lt
      (Nat.pow_lt_pow_left (lt_add_one k) (by positivity)))))) (by omega)
      (card_le_of_density_le hk hl)
    exact exists_isContained_of_concat_mem fun x ↦ (mem_filter.1 (hV x)).2

/-- The subspace of a coordinate block whose parameter directions are all of its coordinates. -/
def blockSubspace (α : Type*) (m : ℕ) : Combinatorics.Subspace (Fin m) α (Fin m) where
  idxFun i := Sum.inr i
  proper e := ⟨e, rfl⟩

@[simp]
lemma blockSubspace_apply {α : Type*} {m : ℕ} (x : Fin m → α) : blockSubspace α m x = x := by
  funext i
  exact (blockSubspace α m).apply_inr rfl

/-- Prepend a fixed block of letters to the coordinates of a subspace. -/
def prependFixed {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) : Combinatorics.Subspace η α (Fin (m + p)) :=
  transportSubspace finSumFinEquiv.symm u V

@[simp]
lemma prependFixed_apply {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) (x : η → α) :
    prependFixed u V x = Sum.elim u (V x) ∘ finSumFinEquiv.symm :=
  transportSubspace_apply finSumFinEquiv.symm u V x

/-- Regroup a cut of the coordinates following a fixed block. -/
def prependCoords {m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin m ⊕ Fin r :=
  ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin q))).trans
      (Equiv.sumAssoc (Fin m) (Fin p) (Fin q))).trans ((Equiv.refl (Fin m)).sumCongr e)

/-- Prepend a fixed coordinate block to a cut of the remaining coordinates. -/
def prependCut {m p q r n : ℕ} (h : m + r = n) (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin n :=
  (prependCoords e).trans (cutEquiv h)

/-- Regrouping the coordinates identifies a prepended word with the concatenation of the fixed
block and the cut word. -/
lemma concat_prependFixed {alphabet η m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r)
    (u : Fin m → Fin alphabet) (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (prependFixed u V x) y ∘ (prependCoords e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) := by
  funext s
  cases s with
  | inl a => simp [prependCoords]
  | inr b =>
      cases hb : e.symm b <;> simp [prependCoords, hb]

/-- The same identification stated for the cut of the ambient coordinates. -/
lemma concat_prependFixed_cut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (prependFixed u V x) y ∘ (prependCut h e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) ∘
        (cutEquiv h).symm := by
  rw [← concat_prependFixed e u V x y]
  rfl

/-- The suffix fibers of a prepended cut are the suffix fibers of the family already restricted
to the fixed prefix block. -/
lemma fiber_splitWords_prependCut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (A : Finset (Fin n → Fin alphabet)) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p)) (x : Fin η → Fin alphabet) :
    fiber (splitWords (prependCut h e) A) (prependFixed u V x) =
      fiber (splitWords e (fiber (splitWords (cutEquiv h) A) u)) (V x) := by
  ext y
  simp only [mem_fiber, mem_splitWords]
  rw [concat_prependFixed_cut]

/-- A prefix fiber sparser than the ambient density by `ε` forces another prefix fiber denser
than the ambient density by a fixed amount. -/
lemma exists_denser_fiber {alphabet m q : ℕ} (halphabet : 0 < alphabet) {ε : ℝ} (hε : 0 < ε)
    {A : Finset (Fin m ⊕ Fin q → Fin alphabet)} {u₀ : Fin m → Fin alphabet}
    (hu₀ : ((fiber A u₀).dens : ℝ) < (A.dens : ℝ) - ε) :
    ∃ u, (A.dens : ℝ) + ε / (alphabet : ℝ) ^ m ≤ ((fiber A u).dens : ℝ) := by
  by_contra! h
  have hpow : (0 : ℝ) < (alphabet : ℝ) ^ m := pow_pos (Nat.cast_pos.2 halphabet) m
  have hsum : ∑ u : Fin m → Fin alphabet,
      ((A.dens : ℝ) + ε / (alphabet : ℝ) ^ m - (fiber A u).dens) = ε := by
    rw [sum_sub_distrib, sum_const, ← card_mul_expect, average_density_fiber, card_univ,
      nsmul_eq_mul]
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
    rw [mul_add, mul_div_cancel₀ _ hpow.ne']
    ring
  linarith [(single_le_sum (fun u _ ↦ sub_nonneg.2 (h u).le) (mem_univ u₀)).trans_eq hsum,
    div_pos hε hpow]

/-- Every word family in dimension `n` has a cut into a prefix and a nonempty suffix, and a subspace
of the prefix above which all fibers are almost as dense as the whole family. -/
def VariableCutFibersSufficient (alphabet dimension : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n → Fin alphabet),
    ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
      ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
        ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ)

/-- Cutting off a first block of coordinates either leaves every suffix fiber almost as dense as the
family, or gives a suffix fiber denser than the family by `ε / alphabet ^ dimension`. -/
private lemma forall_or_exists_denser_fiber {alphabet dimension r n : ℕ} (halphabet : 0 < alphabet)
    {ε : ℝ} (hε : 0 < ε) (hd : dimension + r = n) (A : Finset (Fin n → Fin alphabet)) :
    (∀ u, (A.dens : ℝ) - ε ≤ ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ)) ∨
      ∃ u, (A.dens : ℝ) + ε / (alphabet : ℝ) ^ dimension ≤
        ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ) := by
  rw [or_iff_not_imp_left, not_forall]
  rintro ⟨u₀, hu₀⟩
  simpa using exists_denser_fiber halphabet hε (A := splitWords (cutEquiv hd) A) (u₀ := u₀)
    (by rw [dens_splitWords]; exact not_le.1 hu₀)

/-- The variable-cut lemma by density increments: as long as at most `t` increments of
`ε / alphabet ^ dimension` fit below density one, `t + 1` blocks of `dimension` coordinates
suffice. Each block either leaves all suffix fibers almost as dense as the family, or passes to a
denser suffix fiber. -/
private lemma exists_variableCut_of_one_le_add_mul {alphabet dimension : ℕ}
    (halphabet : 0 < alphabet) {ε : ℝ} (hε : 0 < ε) (t : ℕ) {n : ℕ}
    (hn : dimension * (t + 1) < n) (A : Finset (Fin n → Fin alphabet))
    (hA : 1 ≤ (A.dens : ℝ) + t * (ε / (alphabet : ℝ) ^ dimension)) :
    ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
      ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
        ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ) := by
  induction t using Nat.strong_induction_on generalizing n A with
  | _ t ih =>
    have hdn : dimension < n := (Nat.le_mul_of_pos_right _ t.succ_pos).trans_lt hn
    have hd : dimension + (n - dimension) = n := by omega
    obtain h | ⟨u, hu⟩ := forall_or_exists_denser_fiber halphabet hε hd A
    · exact ⟨dimension, n - dimension, cutEquiv hd, by omega, blockSubspace _ dimension,
        by simpa using h⟩
    have hε' := div_pos hε (pow_pos (Nat.cast_pos.2 halphabet) dimension)
    obtain _ | t := t
    · rw [Nat.cast_zero, zero_mul, add_zero] at hA
      linarith [hu.trans (by exact_mod_cast dens_le_one : _ ≤ (1 : ℝ))]
    obtain ⟨p, q, e, hq, V, hV⟩ := ih t (lt_add_one t)
      (Nat.lt_sub_of_add_lt (by rwa [mul_add_one] at hn)) (fiber (splitWords (cutEquiv hd) A) u)
      (by rw [Nat.cast_add_one] at hA; linarith)
    refine ⟨dimension + p, q, prependCut hd e, hq, prependFixed u V, ?_⟩
    intro x
    rw [fiber_splitWords_prependCut]
    linarith [hV x]

/-- An ambient dimension sufficient for the variable-cut uniform-fibers lemma: one coordinate block
for each possible density increment, and one more coordinate. -/
noncomputable def variableCutFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ :=
  dimension * (⌊(alphabet : ℝ) ^ dimension / ε⌋₊ + 1 + 1) + 1

/-- `VariableCutFibersSufficient alphabet dimension ε n` holds for every
`n ≥ variableCutFibersBound alphabet dimension ε`. -/
lemma variableCutFibersSufficient_of_le {alphabet dimension : ℕ}
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : variableCutFibersBound alphabet dimension ε ≤ n) :
    VariableCutFibersSufficient alphabet dimension ε n := by
  rw [variableCutFibersBound] at hn
  intro A
  obtain rfl | halphabet := Nat.eq_zero_or_pos alphabet
  · have hdn : dimension < n := (Nat.le_mul_of_pos_right _ (by omega)).trans_lt hn
    exact ⟨dimension, n - dimension, cutEquiv (by omega), by omega,
      emptyAlphabetSubspace hdimension le_rfl, fun x ↦ (x ⟨0, hdimension⟩).elim0⟩
  refine exists_variableCut_of_one_le_add_mul halphabet hε _ hn A
    (le_add_of_nonneg_of_le (by positivity) ?_)
  rw [mul_div_assoc', ← div_div_eq_mul_div, one_le_div (by positivity)]
  exact_mod_cast (Nat.lt_floor_add_one _).le

/-- The variable-cut dimension is monotone in the dimension of the subspace and antitone in the
tolerance. -/
lemma variableCutFibersBound_mono {a d d' : ℕ} {ε ε' : ℝ} (ha : 1 ≤ a) (hd : d ≤ d')
    (hε' : 0 < ε') (hε : ε' ≤ ε) :
    variableCutFibersBound a d ε ≤ variableCutFibersBound a d' ε' := by
  unfold variableCutFibersBound
  gcongr
  exact_mod_cast ha

/-- Double counting: for a relation between two finite types, the average density of the sets
of related elements is the same from either side. -/
lemma expect_dens_filter_comm {X Y : Type*} [Fintype X] [Fintype Y] (P : X → Y → Prop)
    [∀ x y, Decidable (P x y)] :
    𝔼 x, ((univ.filter (P x)).dens : ℝ) = 𝔼 y, ((univ.filter fun x ↦ P x y).dens : ℝ) := by
  simp_rw [← expect_indicator_one]
  rw [expect_comm]
  simp [Set.indicator_apply]

/-- Averaging restricted-parameter slice densities over suffixes equals averaging their ambient
fiber densities over restricted parameter words. -/
lemma average_restrictedParameterSlice {k M : ℕ}
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) :
    expect univ (fun y : κ → Fin (k + 1) ↦
      ((univ.filter fun x : Fin M → Fin k ↦
        Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) =
      expect univ (fun x : Fin M → Fin k ↦
        ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) :=
  (expect_dens_filter_comm fun x y ↦ Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).symm

/-- Averaging a pointwise-dense family of suffix fibers produces one suffix above which the
restricted parameter family is dense. -/
lemma exists_dense_suffix_of_restricted_fibers {k M : ℕ} (hk : 0 < k) {δ : ℝ}
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    {A : Finset (ι ⊕ κ → Fin (k + 1))}
    {W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι}
    (hW : ∀ x : Fin M → Fin k,
      δ / 2 ≤ ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) :
    ∃ y : κ → Fin (k + 1),
      δ / 2 ≤
        ((univ.filter fun x : Fin M → Fin k ↦
          Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨y, -, hy⟩ := exists_le_of_le_expect univ_nonempty
    ((le_expect univ_nonempty fun x _ ↦ hW x).trans_eq (average_restrictedParameterSlice A W).symm)
  exact ⟨y, hy⟩

/-- Extend a restricted parameter subspace to the full alphabet, attach a fixed suffix, and
transport the resulting subspace along an equivalence of ambient coordinates. -/
lemma extend_restricted_subspace {k m M : ℕ} {ι κ ζ : Type*}
    [DecidableEq (ζ → Fin (k + 1))] {e : ι ⊕ κ ≃ ζ}
    {A : Finset (ζ → Fin (k + 1))}
    {W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι} {y : κ → Fin (k + 1)}
    {S : Combinatorics.Subspace (Fin m) (Fin k) (Fin M)}
    (hS : ∀ x, (Sum.elim (W (Fin.castSucc ∘ S x)) y) ∘ e.symm ∈ A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ,
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  use compose (fixSuffixReindex e W y) (map Fin.castSucc S)
  intro w hw
  obtain ⟨x, -, rfl⟩ := mem_image.1 hw
  simpa using hS x

/-- A dimension in which every family of density `δ` over `k + 1` letters contains the `Fin k`
restriction of an `m`-dimensional subspace, given a bound `F` for density Hales--Jewett over `k`
letters. -/
noncomputable def restrictAlphabetBound (k : ℕ) (F : ℝ → ℕ) (m : ℕ) (δ : ℝ) : ℕ :=
  variableCutFibersBound (k + 1) (max 1 (densityBound k F m (δ / 2))) (δ / 2)

/-- In every dimension `n ≥ restrictAlphabetBound k F m δ`, a family of density `δ` over `k + 1`
letters contains the `Fin k` restriction of an `m`-dimensional subspace. -/
lemma exists_restrictAlphabet_subset {k : ℕ} (hk : 0 < k) {F : ℝ → ℕ} (hF : IsDHJBound k F)
    {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : restrictAlphabetBound k F m δ ≤ n)
    {A : Finset (Fin n → Fin (k + 1))} (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  classical
  have hA' := density_le_of_card_le k.succ_pos (A := A) (δ := δ) (by exact_mod_cast hA)
  obtain ⟨p, q, e, -, W, hW⟩ :=
    variableCutFibersSufficient_of_le (le_max_left _ _) (half_pos hδ) hn A
  obtain ⟨y, hy⟩ := exists_dense_suffix_of_restricted_fibers hk (δ := δ) (A := splitWords e A)
    (W := W) fun x ↦ by linarith [hW (Fin.castSucc ∘ x)]
  obtain ⟨S, hS⟩ := exists_of_density hk hF hm (half_pos hδ) (le_max_right 1 _)
    (card_le_of_density_le hk hy)
  refine extend_restricted_subspace (e := e) (W := W) (y := y) (S := S) ?_
  intro x
  simpa using hS x

end Subspace
end DensityHalesJewett
