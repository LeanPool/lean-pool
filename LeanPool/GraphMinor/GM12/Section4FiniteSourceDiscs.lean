/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
import LeanPool.GraphMinor.GM12.Section4SourceDiscs

/-!
# Finite labelled source discs for topological feasibility

In XII (4.3), claim (7), page 251, the vertex discs and
residual edge discs carry the target graph's finite labels.
Reindex the disc system by the vertex and edge enumerations.
The vertex-disc contacts become exactly the oriented end classes
used in the connection theorem.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The finite labelled source configuration for XII (4.3), claim
(7), page 251. Its end partition is topologically feasible before
the ambient homeomorphism is applied. -/
theorem exists_finite_source_disc_system
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {p t : ℕ}
    (ν : Fin p ≃ Γ.V) (ε : Fin t ≃ Γ.E) (κ : Fin t × Bool → Fin p)
    (hl : ∀ i, Γ.toGraph.IsLink (ε i).val (ν (κ (i, true))).val (ν (κ (i, false))).val)
    (hne : ∀ i, κ (i, true) ≠ κ (i, false)) :
    ∃ (Δ : Fin t → Set S) (a b : Fin t → S),
      (∀ i, IsClosedDisc (Δ i) ∧ a i ≠ b i ∧ ({a i, b i} : Set S) ⊆ discBd (Δ i)) ∧
      (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
      IsTopologicallyFeasible Δ
        (edgeEndClass (fun q : Fin t × Bool => if q.2 then a q.1 else b q.1) κ) := by
  let u : Γ.E → Γ.V := fun e => ν (κ (ε.symm e, true))
  let v : Γ.E → Γ.V := fun e => ν (κ (ε.symm e, false))
  have hl' : ∀ e, Γ.toGraph.IsLink e.val (u e).val (v e).val := by
    intro e
    simpa only [u, v, ε.apply_symm_apply] using hl (ε.symm e)
  have hne' : ∀ e, u e ≠ v e := by
    intro e heq
    exact hne (ε.symm e) (ν.injective heq)
  obtain ⟨D, Δ, a, b, hD, hDD, hΔ, hΔΔ, hcontact⟩ := exists_source_disc_system hS Γ u v hl' hne'
  let E : Fin t × Bool ≃ Γ.E × Bool := ε.prodCongr (Equiv.refl Bool)
  let ends : Γ.E × Bool → S := fun q => if q.2 then a q.1 else b q.1
  let owner : Γ.E × Bool → Γ.V := fun q => if q.2 then u q.1 else v q.1
  have howner : ∀ q, owner (E q) = ν (κ q) := by
    intro ⟨i, c⟩
    cases c <;> simp [owner, E, Equiv.prodCongr_apply, Prod.map, u, v]
  have hclass : ∀ w, edgeEndClass ends owner (ν w) =
      edgeEndClass (fun q : Fin t × Bool => if q.2 then a (ε q.1) else b (ε q.1)) κ w := by
    intro w
    simpa [ends, E, Function.comp_def, Equiv.prodCongr_apply, Prod.map] using
      edgeEndClass_reindex E ν ends owner κ howner w
  have hunion : (⋃ i : Fin t, Δ (ε i)) = ⋃ e : Γ.E, Δ e := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨ε i, hi⟩
    · intro hx
      obtain ⟨e, he⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨ε.symm e, by simpa only [ε.apply_symm_apply] using he⟩
  refine ⟨(fun i => Δ (ε i)), (fun i => a (ε i)), (fun i => b (ε i)),
    (fun i => hΔ (ε i)), (fun i j hij => hΔΔ (ε i) (ε j) (fun h => hij (ε.injective h))), ?_⟩
  refine ⟨(fun w => D (ν w)), (fun w => hD (ν w)), ?_, ?_⟩
  · intro w z hwz
    exact hDD (ν w) (ν z) (fun h => hwz (ν.injective h))
  · intro w
    rw [hunion]
    exact (hcontact (ν w)).trans (hclass w)

end GraphMinor.GM12
