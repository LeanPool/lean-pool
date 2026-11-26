/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM16.Section5Linkage
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Regions

import LeanPool.GraphMinor.GM11.CitedResults

import LeanPool.GraphMinor.GM12.Bridge

/-!
# Graph Minors XVI (5.5)

Choose the threshold from (5.2) and double it. Claim (1), proved in
Section5Linkage, supplies the required number of disjoint old-graph paths
with separated ends. Their disjointness also makes all these ends
distinct, so (5.2) gives the controlled clique minor.
-/

public section
namespace GraphMinor.GM16
open Set Function Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w

/-- **Graph Minors XVI, (5.5)** (pages 57–58), by the paper's induction
on disjoint paths and then (5.2). The metric laws include the triangle inequality from XI (9.1),
and (5.2) uses XII (4.4). No statement of XVI is assumed. -/
theorem theorem_5_5_proof
     : GM16Theorem55Statement.{u, v, w} := by
  classical
  intro S _ _ hS hConn p
  let μ := p * (p - 1) / 2
  obtain ⟨r, hr, h52⟩ := theorem_5_2_proof hS hConn p
  refine ⟨2 * r, by omega, ?_⟩
  intro α β G θ_star T_star hT hAnimal
  obtain ⟨H, η, θ_span, T, d, X, Y, hAnim⟩ := hAnimal
  have hσ : 8 * μ ≤ 4 * p * (p - 1) := by
    calc
      8 * μ = 4 * (μ * 2) := by ring
      _ ≤ 4 * (p * (p - 1)) := Nat.mul_le_mul_left 4 (Nat.div_mul_le_self _ _)
      _ = 4 * p * (p - 1) := by ring
  have hAnim' : IsAnimal G T_star θ_star H η θ_span T d X Y μ 0 (2 * r) (8 * μ) :=
    hAnim.mono (by omega) le_rfl hσ
  obtain ⟨_, horder, hSpan, hMet, hXsub, hXcard, _, _, hhorns, _, _⟩ := hAnim'
  have hXfin : X.Finite := hT.finite_V.subset (fun x hx => (hXsub hx).1)
  obtain ⟨_, _, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ_span T d hS hConn
    hMet
  have hsymV : ∀ a ∈ H.V, ∀ b ∈ H.V, d {a} {b} = d {b} {a} := by
    intro a ha b hb
    exact hsymm {a} ((Or.inl (Or.inl ⟨a, ha, rfl⟩))) {b} ((Or.inl (Or.inl ⟨b, hb, rfl⟩)))
  have htriV : ∀ a ∈ H.V, ∀ b ∈ H.V, ∀ c ∈ H.V,
      d {a} {c} ≤ d {a} {b} + d {b} {c} := by
    intro a ha b hb c hc
    exact htri {a} ((Or.inl (Or.inl ⟨a, ha, rfl⟩))) {b} ((Or.inl (Or.inl ⟨b, hb, rfl⟩)))
      {c} ((Or.inl (Or.inl ⟨c, hc, rfl⟩)))
  obtain ⟨Q, s, t, hst, hQ, hQQ, _, hdist⟩ := theorem_5_5_claim_1
    hT.finite_V hT.finite_E hXfin hXcard hhorns hsymV htriV μ le_rfl
  have hs : Injective s := by
    intro i j hij
    by_contra hne
    have hsi := IsGraphPathWithEnds.left_mem (hQ i).2.1
    have hsj := IsGraphPathWithEnds.left_mem (hQ j).2.1
    have heq := congrArg η.vMap hij
    exact (Set.disjoint_left.mp (hQQ hne)) hsi (heq ▸ hsj)
  have ht : Injective t := by
    intro i j hij
    by_contra hne
    have hti := IsGraphPathWithEnds.right_mem (hQ i).2.1
    have htj := IsGraphPathWithEnds.right_mem (hQ j).2.1
    have heq := congrArg η.vMap hij
    exact (Set.disjoint_left.mp (hQQ hne)) hti (heq ▸ htj)
  have hstdisj : Disjoint (range s) (range t) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨i, rfl⟩ ⟨j, htj⟩
    by_cases hij : i = j
    · subst j
      exact (hst i).2.2 htj.symm
    · have hsi := IsGraphPathWithEnds.left_mem (hQ i).2.1
      have htj' := IsGraphPathWithEnds.right_mem (hQ j).2.1
      have heq := congrArg η.vMap htj
      exact (Set.disjoint_left.mp (hQQ hij)) hsi (heq ▸ htj')
  exact h52 G θ_star θ_span T_star H η T d s t Q hSpan hMet (by omega)
    hst hs ht hstdisj hdist hQ hQQ

end GraphMinor.GM16
