/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6a
public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM19.Conditional
public import LeanPool.GraphMinor.GM19.Cited
public import LeanPool.GraphMinor.GM19.Section4c
public import LeanPool.GraphMinor.GM20.Draw10
import LeanPool.GraphMinor.Surface.OpenDisc

import LeanPool.GraphMinor.GM07.Bridge

import LeanPool.GraphMinor.GM07.Section9

/-!
# Graph Minors XIX: proved deductions from Section6a

The deductions use existing proofs after the preliminary geometry has been defined.
-/

public section
namespace GraphMinor.GM19
open Set Topology Metric GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- If `rep(G) ≥ k` then `α(G) ≥ k`: a set that competes for `α(G)` is not planar, so it holds a
non-null-homotopic `O`-arc, and this arc is `G`-normal because the set is. -/
theorem le_alpha_of_le_rep
     (hS : IsSurface S) [ConnectedSpace S] (hbd : bd S = ∅)
    (hsph : ¬ IsSphere S) (G : Drawing S) {k : ℕ} (hk : (k : ℕ∞) ≤ G.rep) : k ≤ alpha G := by
  have hne : {n : ℕ | ∃ X : Set S, IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = n}.Nonempty := by
    obtain ⟨X, hX⟩ := GraphMinor.GM07.gm07_alpha_exists.{u} S hS ‹_› hbd hsph G
    exact ⟨_, X, hX, rfl⟩
  obtain ⟨X, ⟨hsol, -, hnorm, hnear⟩, hn⟩ := Nat.sInf_mem hne
  have hnp : ¬ IsPlanar X := fun h ↦ hnear (Or.inl h)
  obtain ⟨F, hF, hFX, hnull⟩ : ∃ F, IsOArc F ∧ F ⊆ X ∧ ¬ IsNullHomotopicOArc F := by
    by_cases hX : X = univ
    · obtain ⟨F, hF, hnull⟩ := exists_not_nullHomotopic hS hbd hsph
      exact ⟨F, hF, hX ▸ subset_univ F, hnull⟩
    · by_contra hno
      push Not at hno
      exact hnp ((GraphMinor.GM07.gm07_planar_iff.{u} S hS ‹_› X hsol hX).2 fun F hF hFX ↦ hno F hF
        hFX)
  have hFn : G.IsNormal F := fun x hx ↦ hnorm ⟨hFX hx.1, hx.2⟩
  have h1 : (k : ℕ∞) ≤ ((F ∩ G.V).ncard : ℕ) := hk.trans (rep_le_of_arc G hF hFn hnull)
  have h2 : (F ∩ G.V).ncard ≤ (X ∩ G.V).ncard :=
    ncard_le_ncard (fun x hx ↦ ⟨hFX hx.1, hx.2⟩) (G.finite_V.subset inter_subset_right)
  have h3 : k ≤ (F ∩ G.V).ncard := by exact_mod_cast h1
  change k ≤ sInf {n : ℕ | ∃ X : Set S, IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = n}
  omega

/-- **Graph Minors XIX, (6.4).** The proof uses VII (9.2), VII (5.1), and the proved existence of
`α(G)`. -/
theorem theorem_6_4_proof : Theorem64Statement.{u} := by
  intro S _ hS hconn hbd hsph H _
  have : T2Space S := hS.2.1
  have : Nonempty S := hconn.toNonempty
  obtain ⟨a, b, c, ⟨hom⟩⟩ := classification S hS hconn
  obtain rfl : c = 0 := model_c_eq_zero hom hbd
  have hab : a + b ≥ 1 := by
    by_contra hab
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    obtain ⟨g⟩ := isSphere_model
    exact hsph ⟨hom.trans g⟩
  obtain ⟨DH, rfl⟩ := exists_directed H
  obtain ⟨N, hN⟩ := GraphMinor.GM07.gm07_theorem_9_2.{u} S hS a b hab ⟨hom⟩ DH
  refine ⟨N, fun G _ hk ↦ ?_⟩
  obtain ⟨DG, rfl⟩ := exists_directed G
  exact isEnlargement_of_minor (hN DG (le_alpha_of_le_rep hS hbd hsph _ hk))

end GraphMinor.GM19
