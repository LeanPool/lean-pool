/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.ArrowNumber
public import LeanPool.FiniteRamsey.RamseyExistence
public import Mathlib.Data.Fin.VecNotation
import LeanPool.FiniteRamsey.MulticolorRamseyUnconditional
import LeanPool.FiniteRamsey.RamseyTheorem
import Mathlib.Tactic.FinCases

/-!
# Ramsey numbers

For a finite colour type `ι` and clique sizes `n : ι → ℕ`, the Ramsey number `ramseyNumber n` is
the least `N` such that every `ι`-colouring of the edges of the complete graph on `N` vertices
contains, for some colour `c`, a clique of size `n c` all of whose edges have colour `c`. The
classical two-colour number `R(r, s)` is `ramseyNumber ![r, s]` and the diagonal number `R(k)` is
`ramseyNumber ![k, k]`.

## Main declarations

* `SimpleGraph.ramseyNumber n`: the arrow number (`arrowNumber`) of the clique targets
  `fun c => completeGraph (Fin (n c))`.
* `SimpleGraph.exists_arrow`: every family of finite targets indexed by a finite colour type is
  arrowed by some finite complete graph (Ramsey's theorem in arrow form).
* `SimpleGraph.arrow_iff_ramseyNumber_le`, `SimpleGraph.exists_isNClique_iff_ramseyNumber_le`: the
  least-number characterisation, in copy form and in monochromatic-clique form.
* Two-colour API: `ramseyProperty_iff_ramseyNumber_le`, `ramseyNumber_comm`, monotonicity,
  `ramseyNumber_le_binomialBound`, and the values `R(1, s) = 1`, `R(2, s) = s`.

## Design notes

This follows the design of B. Mehta's formalisation (the origin of mathlib's `EdgeLabeling`): one
definition for an arbitrary finite colour type with a target size per colour, of which the
two-colour and diagonal numbers are specialisations. The two-colour vocabulary
`RamseyProperty`/`RedClique`/`BlueClique` (`RamseyProperty.lean`) is kept as a convenient
interface and is related to the general definition by `ramseyProperty_iff_ramseyNumber_le`.

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2) 30 (1930), 264-286.

## Tags

ramsey theory, ramsey number, combinatorics
-/

@[expose] public section

namespace SimpleGraph

universe u v

/-! ### Ramsey's theorem in arrow form -/

/-- **Ramsey's theorem, arrow form.** For a finite colour type and finite target graphs, some
finite complete graph arrows the target family. -/
theorem exists_arrow {ι : Type u} {W : ι → Type v} [Finite ι] [∀ c, Finite (W c)]
    (H : (c : ι) → SimpleGraph (W c)) : ∃ N, (⊤ : SimpleGraph (Fin N)).Arrow H := by
  classical
  have : ∀ c, Fintype (W c) := fun c => Fintype.ofFinite _
  obtain ⟨N, hN⟩ := exists_isRamseyValid fun c => Fintype.card (W c)
  refine ⟨N, ?_⟩
  have h1 : (⊤ : SimpleGraph (Fin N)).Arrow fun c => completeGraph (Fin (Fintype.card (W c))) := by
    intro C
    obtain ⟨c, s, hs⟩ := hN (Fin N) (by simp) C
    exact ⟨c, (not_cliqueFree_iff_top_isContained _).mp fun hf => hf s hs⟩
  exact h1.mono_target fun c => isContained_top_iff.mpr ⟨(Fintype.equivFin (W c)).toEmbedding⟩

/-! ### The Ramsey number -/

section General

variable {ι : Type u} (n : ι → ℕ)

/-- **The Ramsey number** `R(n)` for clique sizes `n : ι → ℕ`: the least `N` such that every
`ι`-colouring of the edges of `K_N` has, for some colour `c`, a `c`-coloured clique of size
`n c`. -/
noncomputable def ramseyNumber : ℕ :=
  arrowNumber fun c => completeGraph (Fin (n c))

variable {n} {N : ℕ}

theorem ramseyNumber_le_of_arrow
    (h : (⊤ : SimpleGraph (Fin N)).Arrow fun c => completeGraph (Fin (n c))) :
    ramseyNumber n ≤ N :=
  arrowNumber_le_of_arrow h

variable [Finite ι]

variable (n) in
/-- The complete graph on `ramseyNumber n` vertices arrows the clique targets. -/
theorem arrow_ramseyNumber :
    (⊤ : SimpleGraph (Fin (ramseyNumber n))).Arrow fun c => completeGraph (Fin (n c)) :=
  arrow_arrowNumber (exists_arrow _)

/-- **The least-number characterisation**, copy form. -/
theorem arrow_iff_ramseyNumber_le :
    (⊤ : SimpleGraph (Fin N)).Arrow (fun c => completeGraph (Fin (n c))) ↔ ramseyNumber n ≤ N :=
  arrow_iff_arrowNumber_le (exists_arrow _)

/-- **The least-number characterisation**, monochromatic-clique form: every `ι`-colouring of `K_N`
has a `c`-coloured `n c`-clique for some `c` iff `ramseyNumber n ≤ N`. -/
theorem exists_isNClique_iff_ramseyNumber_le :
    (∀ C : TopEdgeLabeling (Fin N) ι, ∃ c s, (C.labelGraph c).IsNClique (n c) s) ↔
      ramseyNumber n ≤ N := by
  rw [← arrow_iff_ramseyNumber_le]
  refine forall_congr' fun C => exists_congr fun c => ?_
  rw [← not_cliqueFree_iff_top_isContained]
  simp [CliqueFree]

theorem lt_ramseyNumber_of_not_arrow
    (h : ¬ (⊤ : SimpleGraph (Fin N)).Arrow fun c => completeGraph (Fin (n c))) :
    N < ramseyNumber n :=
  lt_arrowNumber_of_not_arrow (exists_arrow _) h

end General

/-- Renaming the colours does not change the Ramsey number. -/
theorem ramseyNumber_comp_equiv {ι : Type u} {ι' : Type v} (n : ι → ℕ) (e : ι' ≃ ι) :
    ramseyNumber (n ∘ e) = ramseyNumber n :=
  arrowNumber_reindex (H := fun c => completeGraph (Fin (n c))) e

/-! ### Two colours -/

/-- The colour renaming `true ↦ 0`, `false ↦ 1` matching `![r, s]` with `RamseyProperty`'s
convention (`true` = red = first size). -/
private def boolEquivFinTwo : Bool ≃ Fin 2 where
  toFun b := if b then 0 else 1
  invFun i := decide (i = 0)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- **The two-colour Ramsey property and the Ramsey number.** `RamseyProperty N r s` holds exactly
when `ramseyNumber ![r, s] ≤ N`. -/
theorem ramseyProperty_iff_ramseyNumber_le {N r s : ℕ} :
    RamseyProperty N r s ↔ ramseyNumber ![r, s] ≤ N := by
  rw [ramseyProperty_iff_arrow, ← arrow_iff_ramseyNumber_le,
    ← Arrow.reindex (H := fun c => completeGraph (Fin (![r, s] c))) boolEquivFinTwo]
  exact Arrow.iso_target fun b => Iso.completeGraph (finCongr (by cases b <;> rfl))

/-- **The defining specification**, two-colour form. -/
theorem ramseyNumber_spec (r s : ℕ) : RamseyProperty (ramseyNumber ![r, s]) r s :=
  ramseyProperty_iff_ramseyNumber_le.mpr le_rfl

/-- Any host size with the two-colour Ramsey property bounds `R(r, s)`. -/
theorem ramseyNumber_le_of_ramseyProperty {N r s : ℕ} (h : RamseyProperty N r s) :
    ramseyNumber ![r, s] ≤ N :=
  ramseyProperty_iff_ramseyNumber_le.mp h

/-- **`ramseyNumber` is symmetric.** -/
theorem ramseyNumber_comm (r s : ℕ) : ramseyNumber ![r, s] = ramseyNumber ![s, r] :=
  le_antisymm (ramseyNumber_le_of_ramseyProperty (ramseyProperty_swap (ramseyNumber_spec s r)))
    (ramseyNumber_le_of_ramseyProperty (ramseyProperty_swap (ramseyNumber_spec r s)))

/-- **Monotonicity in the clique-size parameters.** -/
theorem ramseyNumber_mono_cliqueSizes {redSmall redLarge blueSmall blueLarge : ℕ}
    (hred : redSmall ≤ redLarge) (hblue : blueSmall ≤ blueLarge) :
    ramseyNumber ![redSmall, blueSmall] ≤ ramseyNumber ![redLarge, blueLarge] :=
  ramseyNumber_le_of_ramseyProperty
    (ramseyProperty_mono_cliqueSizes hred hblue (ramseyNumber_spec redLarge blueLarge))

theorem ramseyNumber_mono_left {redSmall redLarge blueSize : ℕ} (hred : redSmall ≤ redLarge) :
    ramseyNumber ![redSmall, blueSize] ≤ ramseyNumber ![redLarge, blueSize] :=
  ramseyNumber_mono_cliqueSizes hred le_rfl

theorem ramseyNumber_mono_right {redSize blueSmall blueLarge : ℕ} (hblue : blueSmall ≤ blueLarge) :
    ramseyNumber ![redSize, blueSmall] ≤ ramseyNumber ![redSize, blueLarge] :=
  ramseyNumber_mono_cliqueSizes le_rfl hblue

/-- **`ramseyNumber ![r, s] ≤ ramseyBinomialBound r s`.** The classical binomial bound is, in
particular, an upper bound on the Ramsey number itself. -/
theorem ramseyNumber_le_binomialBound (r s : ℕ) : ramseyNumber ![r, s] ≤ ramseyBinomialBound r s :=
  ramseyNumber_le_of_ramseyProperty (ramsey_upper_bound r s)

/-! ### Small values -/

/-- **`R(1, s) = 1`.** A single vertex is trivially a red `1`-clique, so a one-vertex host always
suffices; a zero-vertex host does not, once `s ≥ 1`, since it cannot supply the red `1`-clique
either. -/
theorem ramseyNumber_one_left {s : ℕ} (hs : 1 ≤ s) : ramseyNumber ![1, s] = 1 :=
  le_antisymm (ramseyNumber_le_of_ramseyProperty (ramseyProperty_one_red s)) <|
    Nat.pos_of_ne_zero fun h0 => not_ramseyProperty_zero_of_pos Nat.one_pos hs
      (ramseyProperty_iff_ramseyNumber_le.mpr h0.le)

/-- **`R(r, 1) = 1`.** The colour-swapped mirror of `ramseyNumber_one_left`. -/
theorem ramseyNumber_one_right {r : ℕ} (hr : 1 ≤ r) : ramseyNumber ![r, 1] = 1 :=
  (ramseyNumber_comm r 1).trans (ramseyNumber_one_left hr)

/-- **`R(2, s) = s`.** A host of size `s` always suffices (`ramseyProperty_two_left`); a host of
size `s - 1` does not, since the all-blue colouring has neither a red `2`-clique (its red label
graph is `⊥`) nor a blue `s`-clique (there are not enough vertices). -/
theorem ramseyNumber_two_left {s : ℕ} (hs : 1 ≤ s) : ramseyNumber ![2, s] = s := by
  refine le_antisymm (ramseyNumber_le_of_ramseyProperty (ramseyProperty_two_left s)) ?_
  by_contra! hlt
  let C : TwoColoring (Fin (s - 1)) := fun _ => false
  have hbot : C.labelGraph true = ⊥ := by ext; rw [EdgeLabeling.labelGraph_adj]; simp [C]
  rcases (ramseyProperty_iff_ramseyNumber_le (r := 2) (s := s)).mpr (by omega) C with
    ⟨t, ht⟩ | hblue
  · exact cliqueFree_bot le_rfl t (hbot ▸ ht)
  · exact not_hasMonochromaticClique_of_card_lt C (by simp; omega) hblue

/-- **`R(r, 2) = r`.** The colour-swapped mirror of `ramseyNumber_two_left`. -/
theorem ramseyNumber_two_right {r : ℕ} (hr : 1 ≤ r) : ramseyNumber ![r, 2] = r :=
  (ramseyNumber_comm r 2).trans (ramseyNumber_two_left hr)

/-! ### A worked example -/

/-- A concrete instance of the small-value lemmas: `ramseyNumber ![2, 4] = 4`, via
`ramseyNumber_two_left`. -/
theorem ramseyNumber_two_four : ramseyNumber ![2, 4] = 4 :=
  ramseyNumber_two_left (by omega)

end SimpleGraph
