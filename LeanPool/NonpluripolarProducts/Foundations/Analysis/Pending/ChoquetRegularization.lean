/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.Envelopes
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Choquet's lemma for regularized suprema

On a second-countable space, every nonempty family of extended-real functions
has a countable subfamily whose upper-semicontinuous regularized supremum is
the regularized supremum of the whole family (Choquet's lemma; Xia,
Proposition 1.2.3, used in the proof of Proposition 3.2.6,
`xia-sgpt:page-0141`).

For each set `b` of a countable basis, a sequence of members realizes the
supremum over `b` of the family's pointwise supremum; the union of these
sequences is the required subfamily.
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

open FirstPass

section RunningMax

variable {Y : Type*}

/-- The running maxima of a sequence of extended-real functions.  Choquet's
lemma produces a countable subfamily; replacing it by its running maxima turns
it into an *increasing* sequence with the same pointwise supremum, which is
how every consumer of the lemma uses it. -/
def runningMax (s : ℕ → Y → EReal) : ℕ → Y → EReal
  | 0 => s 0
  | k + 1 => fun x => max (runningMax s k x) (s (k + 1) x)

theorem runningMax_monotone (s : ℕ → Y → EReal) : Monotone (runningMax s) := by
  refine monotone_nat_of_le_succ fun k x => ?_
  exact le_max_left _ _

theorem le_runningMax (s : ℕ → Y → EReal) (k : ℕ) (x : Y) :
    s k x ≤ runningMax s k x := by
  cases k with
  | zero => exact le_rfl
  | succ m => exact le_max_right _ _

/-- A pointwise bound for every member bounds every running maximum. -/
theorem runningMax_apply_le {s : ℕ → Y → EReal} {c : EReal} {x : Y}
    (hs : ∀ k, s k x ≤ c) (k : ℕ) : runningMax s k x ≤ c := by
  induction k with
  | zero => exact hs 0
  | succ m ih => exact max_le ih (hs (m + 1))

theorem runningMax_le {s : ℕ → Y → EReal} {g : Y → EReal}
    (hs : ∀ k, s k ≤ g) (k : ℕ) (x : Y) : runningMax s k x ≤ g x :=
  runningMax_apply_le (fun j => hs j x) k

theorem iSup_runningMax (s : ℕ → Y → EReal) (x : Y) :
    (⨆ k, runningMax s k x) = ⨆ k, s k x :=
  le_antisymm
    (iSup_le fun k => runningMax_apply_le (fun j => le_iSup (fun i => s i x) j) k)
    (iSup_mono fun k => le_runningMax s k x)

end RunningMax

variable {X : Type*} [TopologicalSpace X]

/-- Choquet's lemma: a countable subfamily with the same regularized
supremum. -/
theorem exists_countable_uscRegularization_sSup_eq [SecondCountableTopology X]
    {F : Set (X → EReal)} (hF : F.Nonempty) :
    ∃ T ⊆ F, T.Countable ∧ T.Nonempty ∧
      uscRegularization (sSup T) = uscRegularization (sSup F) := by
  classical
  -- For each basic set, a sequence of members realizing the local supremum.
  have hseq : ∀ b : Set X, ∃ g : ℕ → X → EReal, (∀ k, g k ∈ F) ∧
      ∀ f ∈ F, (⨆ y ∈ b, f y) ≤ ⨆ k, ⨆ y ∈ b, g k y := by
    intro b
    let S : Set EReal := (fun f => ⨆ y ∈ b, f y) '' F
    obtain ⟨u, hmono, htend, hmem⟩ :=
      exists_seq_tendsto_sSup (hF.image _) (OrderTop.bddAbove S)
    choose g hgF hgu using hmem
    refine ⟨g, hgF, fun f hf => ?_⟩
    have hsup : (⨆ k, u k) = sSup S := iSup_eq_of_tendsto hmono htend
    calc
      (⨆ y ∈ b, f y) ≤ sSup S := le_sSup ⟨f, hf, rfl⟩
      _ = ⨆ k, u k := hsup.symm
      _ = ⨆ k, ⨆ y ∈ b, g k y := by simp only [hgu]
  choose g hgF hgsup using hseq
  obtain ⟨f₀, hf₀⟩ := hF
  let B := countableBasis X
  let T : Set (X → EReal) := insert f₀ (⋃ b ∈ B, range (g b))
  have hTF : T ⊆ F := by
    rintro f (rfl | hf)
    · exact hf₀
    · simp only [mem_iUnion, mem_range] at hf
      obtain ⟨b, _, k, rfl⟩ := hf
      exact hgF b k
  refine ⟨T, hTF, ?_, ⟨f₀, mem_insert _ _⟩, ?_⟩
  · exact (((countable_countableBasis X).biUnion fun b _ => countable_range (g b))).insert f₀
  apply le_antisymm (uscRegularization_mono (sSup_le_sSup hTF))
  intro x
  apply le_iInf₂
  intro U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨b, hbB, hxb, hbV⟩ :=
    (isBasis_countableBasis X).exists_subset_of_mem_open hxV hV
  have hb : IsOpen b := isOpen_of_mem_countableBasis hbB
  calc
    uscRegularization (sSup F) x ≤ ⨆ y ∈ b, sSup F y :=
      uscRegularization_le_localSup _ (hb.mem_nhds hxb)
    _ ≤ ⨆ k, ⨆ y ∈ b, g b k y := by
      refine iSup₂_le fun y hy => ?_
      rw [sSup_apply]
      refine iSup_le fun f => ?_
      exact (le_iSup₂ (f := fun y (_ : y ∈ b) => f.1 y) y hy).trans (hgsup b f.1 f.2)
    _ ≤ ⨆ y ∈ U, sSup T y := by
      refine iSup_le fun k => iSup₂_le fun y hy => ?_
      have hk : g b k ∈ T := mem_insert_of_mem _ (mem_biUnion hbB (mem_range_self k))
      exact (le_sSup hk y).trans (le_iSup₂ (f := fun y (_ : y ∈ U) => sSup T y) y
        (hVU (hbV hy)))

/-- Choquet's lemma, sequence form. -/
theorem exists_seq_uscRegularization_iSup_eq [SecondCountableTopology X]
    {F : Set (X → EReal)} (hF : F.Nonempty) :
    ∃ s : ℕ → X → EReal, (∀ k, s k ∈ F) ∧
      uscRegularization (⨆ k, s k) = uscRegularization (sSup F) := by
  obtain ⟨T, hTF, hTc, hTne, hT⟩ := exists_countable_uscRegularization_sSup_eq hF
  obtain ⟨s, rfl⟩ := hTc.exists_eq_range hTne
  exact ⟨s, fun k => hTF (mem_range_self k), hT⟩

end

end SGPT.Foundations.Analysis.Pending
