/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.ArrowSemantics
public import Mathlib.Order.Lattice.Nat

/-!
# The arrow number of a target family

For a family of target graphs `H : (c : ι) → SimpleGraph (W c)`, one per colour, the
*arrow number* `arrowNumber H` is the least `n` such that every `ι`-colouring of the edges of the
complete graph on `n` vertices contains, in some colour `c`, a copy of `H c`. Every finite Ramsey
number of graphs is an instance:

* clique Ramsey numbers `R(n₁, …, n_k)`, taking `H c = completeGraph (Fin (n c))`
  (`SimpleGraph.ramseyNumber`, in `RamseyNumber.lean`);
* graph Ramsey numbers `R(G, H)`, taking a two-element colour type
  (`SimpleGraph.graphRamseyNumber`, in `GraphRamseyNumber.lean`).

## Main declarations

* `SimpleGraph.arrowNumber H`: the least such `n`, defined with `sInf`, so that no existence proof
  is needed to state it. When no complete host arrows `H` its value is the junk value `0`; lemmas
  that need the true value take an existence hypothesis. For finite colour types and finite targets
  that hypothesis is discharged once and for all by `SimpleGraph.exists_arrow`
  (`RamseyNumber.lean`).
* `SimpleGraph.arrow_iff_arrowNumber_le`: given existence, `K_n` arrows `H` iff `arrowNumber H ≤ n`.
* `SimpleGraph.arrowNumber_reindex`: invariance under renaming colours.

## Design notes

Following the advice recorded on the Lean Zulip (definitions general, lemmas restricted), there is
a single primitive number, for arbitrary colour types and arbitrary targets; the clique and graph
Ramsey numbers are specialisations rather than separate constructions.

## Tags

ramsey theory, ramsey number, edge coloring, combinatorics
-/

@[expose] public section

namespace SimpleGraph

universe u u' v w w'

variable {V : Type u} {G : SimpleGraph V} {ι : Type w} {ι' : Type w'} {W W' : ι → Type v}

/-! ### The arrow number -/

/-- **The arrow number** of a target family `H`: the least `n` such that the complete graph on
`Fin n` arrows `H`. Defined by `sInf`, so it is `0` when no such `n` exists. -/
noncomputable def arrowNumber (H : (c : ι) → SimpleGraph (W c)) : ℕ :=
  sInf {n | (⊤ : SimpleGraph (Fin n)).Arrow H}

variable {H : (c : ι) → SimpleGraph (W c)} {n : ℕ}

/-- Any complete host that arrows `H` bounds the arrow number from above. -/
theorem arrowNumber_le_of_arrow (h : (⊤ : SimpleGraph (Fin n)).Arrow H) : arrowNumber H ≤ n :=
  Nat.sInf_le h

/-- Below the arrow number, the complete host does not arrow `H`. No existence hypothesis is
needed. -/
theorem not_arrow_of_lt_arrowNumber (h : n < arrowNumber H) :
    ¬ (⊤ : SimpleGraph (Fin n)).Arrow H :=
  fun ha => (arrowNumber_le_of_arrow ha).not_gt h

/-- If some complete host arrows `H`, then so does the one of size `arrowNumber H`. -/
theorem arrow_arrowNumber (hex : ∃ n, (⊤ : SimpleGraph (Fin n)).Arrow H) :
    (⊤ : SimpleGraph (Fin (arrowNumber H))).Arrow H :=
  Nat.sInf_mem (s := {n | (⊤ : SimpleGraph (Fin n)).Arrow H}) hex

/-- Larger complete hosts arrow whatever smaller ones do. -/
theorem Arrow.mono_card {m : ℕ} (hle : m ≤ n) (h : (⊤ : SimpleGraph (Fin m)).Arrow H) :
    (⊤ : SimpleGraph (Fin n)).Arrow H :=
  h.mono_host (Embedding.completeGraph (Fin.castLEEmb hle))

/-- **The least-number characterisation.** Given that some complete host arrows `H`, the complete
host on `Fin n` arrows `H` exactly when `arrowNumber H ≤ n`. -/
theorem arrow_iff_arrowNumber_le (hex : ∃ n, (⊤ : SimpleGraph (Fin n)).Arrow H) :
    (⊤ : SimpleGraph (Fin n)).Arrow H ↔ arrowNumber H ≤ n :=
  ⟨arrowNumber_le_of_arrow, fun hle => (arrow_arrowNumber hex).mono_card hle⟩

/-- Given existence, a complete host that fails to arrow `H` is strictly smaller than the arrow
number. -/
theorem lt_arrowNumber_of_not_arrow (hex : ∃ n, (⊤ : SimpleGraph (Fin n)).Arrow H)
    (h : ¬ (⊤ : SimpleGraph (Fin n)).Arrow H) : n < arrowNumber H :=
  not_le.mp (mt (arrow_iff_arrowNumber_le hex).mpr h)

/-- Renaming colours does not change the arrow number. -/
theorem arrowNumber_reindex (e : ι' ≃ ι) : arrowNumber (fun c' => H (e c')) = arrowNumber H :=
  congrArg sInf (Set.ext fun _ => Arrow.reindex e)

/-- **Monotonicity in the targets.** Easier targets have a smaller arrow number, provided the
harder family is arrowed by some complete host. -/
theorem arrowNumber_mono_target {H' : (c : ι) → SimpleGraph (W' c)}
    (hex : ∃ n, (⊤ : SimpleGraph (Fin n)).Arrow H) (hsub : ∀ c, H' c ⊑ H c) :
    arrowNumber H' ≤ arrowNumber H :=
  arrowNumber_le_of_arrow ((arrow_arrowNumber hex).mono_target hsub)

end SimpleGraph
