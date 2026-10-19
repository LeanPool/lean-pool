/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.FlipCore
import all LeanPool.PDL.FlipCore -- shake: keep
public import LeanPool.PDL.Soundness

meta import LeanPool.PDL.General.ImportCompatibility
import Mathlib.Util.TermReduce -- shake: keep

/-! # Flipping a tableau (for section 7)

Like the paper, we only prove interpolation for clusters with a loaded formulas on the right side.
For the case where the loaded formula is on the left, we flip the tableau left-to-right.

The lemmas here then allow us to prove `clusterInterpolation` from `clusterInterpolationRight`.
-/

@[expose] public section

namespace PDL

-- Retain the original auxiliary proposition after the proof moves to FlipCore.
private theorem Sequent.flip_isLoaded._proof_1_5 :
    ∀ (L R : Finset Formula) (O : Olf),
      (delta% Sequent.isLoaded ((R, L, Option.map Sum.swap O) :
        Finset Formula × Finset Formula × Option (NegLoadFormula ⊕ NegLoadFormula))) ↔
        (delta% Sequent.isLoaded ((L, R, O) :
          Finset Formula × Finset Formula × Option (NegLoadFormula ⊕ NegLoadFormula))) := by
  intro L R O
  change Sequent.isLoaded (Sequent.flip (L, R, O)) ↔ Sequent.isLoaded (L, R, O)
  exact Sequent.flip_isLoaded

/-- Flipping a tableau preserves the companion relation. -/
lemma companion_flip_of_companion {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ♥ q → p.flip ♥ q.flip := by
  rintro ⟨lpr, h, rfl⟩
  obtain ⟨lpr', h', hval⟩ := tabAt_flip_lrep p lpr h
  refine ⟨lpr', h', ?_⟩
  unfold companionOf
  apply PathIn.flip_rewind
  simp [hval]

/-- Flipping a tableau preserves the `cEdge` relation `◃`. -/
lemma cEdge_flip_of_cEdge {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ◃ q → p.flip ◃ q.flip := by
  rintro (h | h)
  · exact Or.inl (edge_flip_of_edge _ _ h)
  · exact Or.inr (companion_flip_of_companion h)

/-- Flipping a tableau preserves reachability via `◃`. -/
lemma cReach_flip_of_cReach {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ◃* q → p.flip ◃* q.flip := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (cEdge_flip_of_cEdge hstep)

/-- Flipping a tableau preserves chains of `◃`. (Note the ⁺ instead of *.) -/
lemma cEdgeTrans_flip_of_cEdgeTrans {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ◃⁺ q → p.flip ◃⁺ q.flip := by
  intro h
  induction h with
  | single h => apply Relation.TransGen.single (cEdge_flip_of_cEdge h)
  | tail _ hstep ih => exact ih.tail (cEdge_flip_of_cEdge hstep)

/-- Reachability via `◃` only depends on paths up to heterogeneous equality. -/
lemma cReach_heq_congr {X1 X2} {t1 : Tableau [] X1} {t2 : Tableau [] X2}
    {p1 q1 : PathIn t1} {p2 q2 : PathIn t2}
    (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) (hq : HEq q1 q2) :
    (p1 ◃* q1) ↔ (p2 ◃* q2) := by
  subst hX
  obtain rfl := eq_of_heq ht
  rw [eq_of_heq hp, eq_of_heq hq]

/-- Flipping a tableau changes neither the child nor the companion relation,
hence it also does not change reachability. -/
lemma cReach_flip {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    (p.flip ◃* q.flip) ↔ p ◃* q := by
  constructor
  · intro h
    exact (cReach_heq_congr (X2 := X) (by simp) (flip_aux_Tableau_flip_flip_heq tab)
      (eqRec_heq_iff.mp (heq_of_eq (PathIn.flip_flip p)))
      (eqRec_heq_iff.mp (heq_of_eq (PathIn.flip_flip q)))).mp (cReach_flip_of_cReach h)
  · exact cReach_flip_of_cReach

lemma cEquiv_flip {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    (p.flip ≡ᶜ q.flip) ↔ p ≡ᶜ q := by
  unfold cEquiv
  rw [cReach_flip, cReach_flip]

end PDL

run_cmd do
  let source := `LeanPool.PDL.FlipCore
  let target := `LeanPool.PDL.Flip
  Lean.Elab.Command.liftCoreM (PDL.ImportCompatibility.retainPrivateDeclarations source target)
