/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.Subspace
public import LeanPool.ShelahHalesJewett.HalesJewett
import Mathlib.Tactic.Ring.RingNF

/-!
# Canonization of the constant letters

A word over the alphabet `Option α` is a word over `α` with variable positions marked by `none`;
its support is the set of variable positions. Substituting such a word into a combinatorial
subspace gives `Subspace.wordMap`, which turns a subspace of dimension `ℓ` into a map from words
of length `ℓ` to words of length the ambient dimension.

The main result `exists_canonical` is support canonization: after passing to a suitable
`ℓ`-dimensional subspace, the colour of a substituted word depends only on its support. It is
proved by induction on `ℓ`, one application of the ordinary Hales--Jewett theorem per variable,
each of them applied to the profile of colours obtained by letting the remaining positions vary.
The dimension it needs is `Canonization.bound`, an explicit expression in Shelah's bound
`Combinatorics.Line.shelahBound` for the Hales--Jewett numbers.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Two words over `Option α` have the same support when their variable positions agree. -/
def SameSupport {α ι : Type*} (x y : ι → Option α) : Prop := ∀ i, x i = none ↔ y i = none

namespace Line

variable {α ι : Type*}

/-- The word obtained from a line by substituting a letter, or the variable itself, at its
variable positions. -/
def fillOption (l : Combinatorics.Line α ι) (v : Option α) : ι → Option α :=
  fun i ↦ (l.idxFun i).elim v some

@[simp]
lemma fillOption_some (l : Combinatorics.Line α ι) (a : α) :
    fillOption l (some a) = some ∘ l a := by
  funext i
  cases h : l.idxFun i <;> simp [fillOption, Combinatorics.Line.coe_apply, h]

end Line

namespace Subspace

variable {α η θ ι : Type*}

/-- Substitute a word over `Option α` into a combinatorial subspace, marking variable positions
of the parameter word by `none`. -/
def wordMap (V : Combinatorics.Subspace η α ι) (x : η → Option α) : ι → Option α :=
  fun i ↦ Sum.elim some x (V.idxFun i)

lemma wordMap_compose (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η)
    (x : θ → Option α) : wordMap (compose V W) x = wordMap V (wordMap W x) := by
  funext i
  cases h : V.idxFun i <;> simp [wordMap, compose, h]

lemma composeLine_idxFun (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    (composeLine V l).idxFun = wordMap V l.idxFun :=
  rfl

/-- Prepend a new variable direction, realized by a line on a fresh block of coordinates, to the
directions of a subspace. -/
def consLine {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') : Combinatorics.Subspace (Fin (ℓ + 1)) α (B ⊕ B') where
  idxFun := Sum.elim (fun b ↦ (V.idxFun b).map id Fin.succ)
    fun i ↦ (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    induction e using Fin.cases with
    | zero =>
      obtain ⟨i, hi⟩ := l.proper
      exact ⟨Sum.inr i, by simp [hi]⟩
    | succ j =>
      obtain ⟨b, hb⟩ := V.proper j
      exact ⟨Sum.inl b, by simp [hb]⟩

lemma wordMap_consLine {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') (x : Fin (ℓ + 1) → Option α) :
    wordMap (consLine V l) x
      = Sum.elim (wordMap V fun i ↦ x i.succ) (Line.fillOption l (x 0)) := by
  funext i
  cases i with
  | inl b => cases h : V.idxFun b <;> simp [wordMap, consLine, h]
  | inr i => cases h : l.idxFun i <;> simp [wordMap, consLine, Line.fillOption, h]

lemma wordMap_reindex {ι' : Type*} (V : Combinatorics.Subspace η α ι) (e : ι ≃ ι')
    (x : η → Option α) :
    wordMap (V.reindex (Equiv.refl _) (Equiv.refl _) e) x = wordMap V x ∘ e.symm := by
  funext i
  cases h : V.idxFun (e.symm i) <;> simp [wordMap, Combinatorics.Subspace.reindex, h]

/-- Embed the first `N` coordinates of a cube into a larger one, filling the remaining
coordinates with a fixed letter. -/
noncomputable def padInitial (α : Type*) [Nonempty α] {N n : ℕ} (h : N ≤ n) :
    Combinatorics.Subspace (Fin N) α (Fin n) where
  idxFun i := if hi : i.val < N then Sum.inr ⟨i.val, hi⟩ else Sum.inl (Classical.arbitrary α)
  proper e := ⟨Fin.castLE h e, by simp [Fin.castLE, e.isLt]⟩

end Subspace

namespace Canonization

open Subspace

/-- The number of positions used by support canonization of `ℓ` variables over `k` letters with
`c` colours, when `p` positions precede the block and `s` variable slots follow it. Each variable
adds the dimension of one application of the Hales--Jewett theorem, to the colouring by profiles
over the remaining positions. -/
def bound (k c : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | ℓ + 1, p, s =>
    bound k c ℓ p (s + 1) +
      Combinatorics.Line.shelahBound k (c ^ (k + 1) ^ (p + bound k c ℓ p (s + 1) + s))

/-- The inductive form of support canonization: for any block of positions preceding the
variables and any block of variable slots following them, there is a block of positions with
`ℓ` variables on which every colouring becomes a function of the support alone. -/
private lemma exists_canonical_aux (α : Type*) [Fintype α] (κ : Type*) [Fintype κ] (ℓ : ℕ) :
    ∀ (P S : Type) [Fintype P] [Fintype S], ∃ (B : Type) (_ : Fintype B),
      Fintype.card B = bound (Fintype.card α) (Fintype.card κ) ℓ (Fintype.card P)
        (Fintype.card S) ∧
      ∀ C : (P → Option α) → (B → Option α) → (S → Option α) → κ,
        ∃ V : Combinatorics.Subspace (Fin ℓ) α B,
          ∀ (p : P → Option α) (s : S → Option α) (x y : Fin ℓ → Option α),
            SameSupport x y → C p (wordMap V x) s = C p (wordMap V y) s := by
  classical
  induction ℓ with
  | zero =>
    intro P S _ _
    refine ⟨PEmpty, inferInstance, by simp [bound], ?_⟩
    intro C
    refine ⟨⟨PEmpty.elim, fun e ↦ e.elim0⟩, ?_⟩
    intro p s _ _ _
    exact congrArg (fun w ↦ C p w s) (funext fun i ↦ i.elim)
  | succ ℓ ih =>
    intro P S _ _
    obtain ⟨B, _, hcard, hB⟩ := ih P (Unit ⊕ S)
    rw [Fintype.card_sum, Fintype.card_unit, add_comm 1] at hcard
    have hprofiles : Fintype.card ((P → Option α) → (B → Option α) → (S → Option α) → κ) =
        Fintype.card κ ^ (Fintype.card α + 1) ^ (Fintype.card P + Fintype.card B +
          Fintype.card S) := by
      simp only [Fintype.card_fun, Fintype.card_option, ← pow_mul, ← pow_add]
      congr 2
      ring
    refine ⟨B ⊕ Fin (Combinatorics.Line.shelahBound (Fintype.card α)
      (Fintype.card ((P → Option α) → (B → Option α) → (S → Option α) → κ))),
      inferInstance, by rw [Fintype.card_sum, Fintype.card_fin, hprofiles, hcard, bound], ?_⟩
    intro C
    -- A line on the new block along which the colouring of the other positions is constant.
    obtain ⟨l, profile, hl⟩ := Combinatorics.Line.exists_mono_of_card_eq_shelahBound
      (Fintype.card_fin _) fun (u : _ → α) p b s ↦ C p (Sum.elim b (some ∘ u)) s
    have hprofile (a : α) (p : P → Option α) (b : B → Option α) (s : S → Option α) :
        C p (Sum.elim b (some ∘ l a)) s = profile p b s :=
      congrFun (congrFun (congrFun (hl a) p) b) s
    -- Canonize the earlier variables, with the new one among the slots that follow them.
    obtain ⟨V, hV⟩ := hB fun p b q ↦
      C p (Sum.elim b (Line.fillOption l (q (Sum.inl ())))) fun s ↦ q (Sum.inr s)
    refine ⟨consLine V l, ?_⟩
    intro p s x y hxy
    rw [wordMap_consLine, wordMap_consLine]
    refine (hV p (Sum.elim (fun _ ↦ x 0) s) (fun i ↦ x i.succ) (fun i ↦ y i.succ)
      fun i ↦ hxy i.succ).trans ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    cases hx : x 0 with
    | none => rw [(hxy 0).1 hx]
    | some a =>
      cases hy : y 0 with
      | none => simp [(hxy 0).2 hy] at hx
      | some b => rw [Line.fillOption_some, Line.fillOption_some, hprofile a, hprofile b]

variable {α κ : Type*} [Fintype α] [Fintype κ] {ℓ : ℕ}

/-- **Support canonization**: in a large enough cube every colouring of words over `Option α`
admits an `ℓ`-dimensional subspace on which the colour of a substituted word depends only on its
support. -/
lemma exists_canonical
    (C : (Fin (bound (Fintype.card α) (Fintype.card κ) ℓ 0 0) → Option α) → κ) :
    ∃ V : Combinatorics.Subspace (Fin ℓ) α
        (Fin (bound (Fintype.card α) (Fintype.card κ) ℓ 0 0)),
      ∀ x y : Fin ℓ → Option α, SameSupport x y → C (wordMap V x) = C (wordMap V y) := by
  obtain ⟨B, _, hcard, hB⟩ := exists_canonical_aux α κ ℓ PEmpty PEmpty
  rw [Fintype.card_pempty] at hcard
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨V, hV⟩ := hB fun _ w _ ↦ C (w ∘ e.symm)
  refine ⟨V.reindex (Equiv.refl _) (Equiv.refl _) e, ?_⟩
  intro x y hxy
  rw [wordMap_reindex, wordMap_reindex]
  exact hV PEmpty.elim PEmpty.elim x y hxy

/-- Support canonization holds in every ambient dimension beyond the one it produces. -/
lemma exists_canonical_of_le [Nonempty α] {n : ℕ}
    (hn : bound (Fintype.card α) (Fintype.card κ) ℓ 0 0 ≤ n) (C : (Fin n → Option α) → κ) :
    ∃ V : Combinatorics.Subspace (Fin ℓ) α (Fin n),
      ∀ x y : Fin ℓ → Option α, SameSupport x y → C (wordMap V x) = C (wordMap V y) := by
  obtain ⟨V, hV⟩ := exists_canonical fun w ↦ C (wordMap (padInitial α hn) w)
  refine ⟨compose (padInitial α hn) V, ?_⟩
  intro x y hxy
  rw [wordMap_compose, wordMap_compose]
  exact hV x y hxy

end Canonization
end DensityHalesJewett
