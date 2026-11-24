/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CircleQuadTransfer
public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM12.Section4ProtectedDiscMatch
import LeanPool.GraphMinor.GM12.Section4DiscMatch
import LeanPool.GraphMinor.GM12.Section4DiscEnlargement
import LeanPool.GraphMinor.GM19.MarkedMatch
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Matching a disc with four crossing marks

For XII (4.5), claim (1), page 253, first match the two whole
discs while fixing the protected disc family. Compare their
boundary parametrizations through this ambient map. The circle
quadruple adjustment matches the four marks, either in order
or with the second and fourth exchanged, preserving opposite
pairs in both cases. Extend it through a collar of the target
disc, chosen away from the protected family.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Match whole discs and four crossing marks, preserving the
two opposite pairs and fixing a disjoint protected disc family.
The possible reversal of the boundary direction exchanges
only the second and fourth target marks. This is the single
disc match in XII (4.5), claim (1), page 253. -/
theorem exists_quad_disc_match_fixing_discs {S ι : Type}
    [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (D : ι → Set S) (hD : ∀ i, IsClosedDisc (D i))
    (hDD : Pairwise (fun i j => Disjoint (D i) (D j)))
    {A B : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (hAD : Disjoint A (⋃ i, D i)) (hBD : Disjoint B (⋃ i, D i))
    (p q : Circle → S)
    (hp : Continuous p ∧ Function.Injective p ∧ range p = discBd A)
    (hq : Continuous q ∧ Function.Injective q ∧ range q = discBd B)
    {b₀ b₁ b₂ b₃ : ℝ} (hb₀₁ : b₀ < b₁) (hb₁₂ : b₁ < b₂)
    (hb₂₃ : b₂ < b₃) (hb₃ : b₃ < b₀ + 1) :
    ∃ e : S ≃ₜ S, e '' A = B ∧
      ((e (p (ee 0)) = q (ee b₀) ∧ e (p (ee (1 / 4))) = q (ee b₁) ∧
        e (p (ee (1 / 2))) = q (ee b₂) ∧ e (p (ee (3 / 4))) = q (ee b₃)) ∨
       (e (p (ee 0)) = q (ee b₀) ∧ e (p (ee (1 / 4))) = q (ee b₃) ∧
        e (p (ee (1 / 2))) = q (ee b₂) ∧ e (p (ee (3 / 4))) = q (ee b₁))) ∧
      ∀ i z, z ∈ D i → e z = z := by
  obtain ⟨f, hfA, hffix⟩ := exists_disc_match_fixing_discs hS D hD hDD hA hB hAD hBD
  have hp' : GM19.IsBdParam A p := hp
  have hq' : GM19.IsBdParam B q := hq
  obtain ⟨τ, hτ⟩ := GM19.exists_circle_transfer hp' hq' f hA hfA
  obtain ⟨g, hg, hmarks⟩ := exists_circle_quad_transfer τ hb₀₁ hb₁₂ hb₂₃ hb₃
  obtain ⟨qH, hqH⟩ := GM19.IsBdParam.exists_homeo hq'
  have hZ : IsClosed (⋃ i, D i) := isClosed_iUnion_of_finite (fun i => (hD i).isClosed)
  obtain ⟨E, hE, hBE, hEZ⟩ := exists_disc_enlargement_avoiding hS hB hZ hBD
  obtain ⟨k, hkB, hkmarks, hkfix⟩ := exists_boundary_twist
    (fun z => (hS.2.2 z).isManifoldPoint) hB hE hBE qH hg
  have hcomp : ∀ w, (f.trans k) (p w) = q (g (τ w)) := by
    intro w
    change k (f (p w)) = _
    rw [← hτ w, ← hqH (τ w), hkmarks, hqH]
  refine ⟨f.trans k, ?_, ?_, ?_⟩
  · change (fun z => k (f z)) '' A = B
    have h := congrArg (fun C => k '' C) hfA
    simpa only [image_image, hkB] using h
  · rcases hmarks with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · exact Or.inl ⟨(hcomp (ee 0)).trans (congrArg q h0),
        (hcomp (ee (1 / 4))).trans (congrArg q h1),
        (hcomp (ee (1 / 2))).trans (congrArg q h2),
        (hcomp (ee (3 / 4))).trans (congrArg q h3)⟩
    · exact Or.inr ⟨(hcomp (ee 0)).trans (congrArg q h0),
        (hcomp (ee (1 / 4))).trans (congrArg q h1),
        (hcomp (ee (1 / 2))).trans (congrArg q h2),
        (hcomp (ee (3 / 4))).trans (congrArg q h3)⟩
  · intro i z hz
    change k (f z) = z
    rw [hffix i z hz]
    exact hkfix z (fun hzE => disjoint_left.mp hEZ hzE (mem_iUnion.mpr ⟨i, hz⟩))

end GraphMinor.GM12
