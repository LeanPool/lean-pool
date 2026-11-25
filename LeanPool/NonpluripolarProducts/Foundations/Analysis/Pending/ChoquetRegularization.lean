/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscRegularization
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Choquet's lemma for regularized suprema

On a second-countable space, every nonempty family of extended-real functions
has a countable subfamily whose upper-semicontinuous regularized supremum is
the regularized supremum of the whole family. This is a topological generalization of
[Xia, Proposition 1.2.3](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_pshfunctions.tex#L258-L265).
Xia considers a locally uniformly upper-bounded family of plurisubharmonic
functions on a complex manifold with countably many connected components.

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
