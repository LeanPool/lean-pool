/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73TwoArcLoop
import LeanPool.GraphMinor.GM12.Section73WalkPaths

/-!
# Removing the constant arc from the collapsed circle

For XII (7.3), Claim (1), page 262, parameterize the old circle
by its two complementary arcs. The collapse makes the first arc
constant. The image of the other arc is a loop injective apart
from its ends, so it parameterizes the new circle. The constant
first half of the collapsed loop can be removed by the usual
path homotopy, inside the image of the remaining arc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Collapsing one arc of a two-arc circle leaves, up to homotopy,
the embedded circle parameterized by the complementary arc. This
compares the circuit parameters in XII (7.3), Claim (1), page 262. -/
theorem exists_circle_parameters_after_arc_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] {p q : S} {Z : Set S}
    (α : Path p q) (β : Path q p) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcap : range α ∩ range β ⊆ {p, q}) (f : C(S, S))
    (hconstant : ∀ t, f (α t) = f p)
    (hinj : InjOn (fun t => f (β t)) (Ico (0 : unitInterval) 1))
    (hZ : ∀ t, f (β t) ∈ Z) :
    ∃ φ ψ : C(Circle, S), IsEmbedding φ ∧ IsEmbedding ψ ∧
      range φ = range α ∪ range β ∧ range ψ = f '' range β ∧
      ClosedCurvesHomotopicIn Z (f.comp φ) ψ := by
  have h01 : (α.trans β).toContinuousMap 0 = (α.trans β).toContinuousMap 1 :=
    (α.trans β).source.trans (α.trans β).target.symm
  obtain ⟨φ, hφ, hφrange, hφpar⟩ := exists_embedded_circle_of_loop
    (α.trans β).toContinuousMap h01 (two_arc_loop_injOn α β hα hβ hcap)
  have hfpq : f p = f q := by
    have hh := hconstant 1
    rw [α.target] at hh
    exact hh.symm
  let γ : Path (f p) (f p) := (β.map f.continuous).cast hfpq rfl
  have hγ01 : γ.toContinuousMap 0 = γ.toContinuousMap 1 := γ.source.trans γ.target.symm
  obtain ⟨ψ, hψ, hψrange, hψpar⟩ := exists_embedded_circle_of_loop γ.toContinuousMap hγ01 hinj
  have hpZ : f p ∈ Z := by simpa only [β.target] using hZ 1
  let a : Z := ⟨f p, hpZ⟩
  let γZ : Path a a := {
    toFun := fun t => ⟨γ t, hZ t⟩
    continuous_toFun := by fun_prop
    source' := Subtype.ext γ.source
    target' := Subtype.ext γ.target }
  have hh : ClosedCurvesHomotopicIn Z (f.comp φ) ψ := by
    apply closedCurvesHomotopicIn_of_path 1 (f.comp φ) ψ ((Path.refl a).trans γZ) γZ
    · intro t
      rw [ContinuousMap.comp_apply, hφpar]
      change (((Path.refl a).trans γZ) t).val = f ((α.trans β) t)
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs with ht
      · exact (hconstant _).symm
      · rfl
    · intro t
      rw [hψpar]
      rfl
    · exact Path.Homotopic.refl_trans γZ
  refine ⟨φ, ψ, hφ, hψ, ?_, ?_, hh⟩
  · exact hφrange.trans (Path.trans_range α β)
  · rw [hψrange]
    change range (fun t => f (β t)) = f '' range β
    exact range_comp f β

/-- Exact collapse fibres make the complementary arc's image
injective on the half-open interval. Thus the parameter comparison
for XII (7.3), Claim (1), follows from the arc and fibre data,
without assuming injectivity of the collapsed parameterization. -/
theorem exists_circle_parameters_of_collapse_fibres
    {S : Type*} [TopologicalSpace S] [T2Space S] {p q : S} {A Z : Set S}
    (α : Path p q) (β : Path q p) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcap : range α ∩ range β ⊆ {p, q}) (hαA : range α ⊆ A)
    (hβA : range β ∩ A ⊆ {p, q}) (f : C(S, S))
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hZ : f '' range β ⊆ Z) :
    ∃ φ ψ : C(Circle, S), IsEmbedding φ ∧ IsEmbedding ψ ∧
      range φ = range α ∪ range β ∧ range ψ = f '' range β ∧
      ClosedCurvesHomotopicIn Z (f.comp φ) ψ := by
  have hpA : p ∈ A := α.source ▸ hαA (mem_range_self 0)
  have hconstant : ∀ t, f (α t) = f p := fun t => (hfibre _ _).mpr
    (Or.inr ⟨hαA (mem_range_self t), hpA⟩)
  have hends : ∀ t ∈ Ico (0 : unitInterval) 1, β t ∈ A → t = 0 := by
    intro t ht htA
    rcases hβA ⟨mem_range_self t, htA⟩ with htp | htq
    · have htone : t = 1 := hβ (htp.trans β.target.symm)
      exact (ht.2.ne htone).elim
    · exact hβ (htq.trans β.source.symm)
  have hinj : InjOn (fun t => f (β t)) (Ico (0 : unitInterval) 1) := by
    intro s hs t ht hst
    rcases (hfibre _ _).mp hst with heq | hA
    · exact hβ heq
    · exact (hends s hs hA.1).trans (hends t ht hA.2).symm
  exact exists_circle_parameters_after_arc_collapse α β hα hβ hcap f hconstant hinj
    (fun t => hZ ⟨β t, mem_range_self t, rfl⟩)

end GraphMinor.GM12
