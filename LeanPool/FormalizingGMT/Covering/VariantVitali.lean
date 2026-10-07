/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Tactic

/-!
# A variant of Vitali's covering theorem

This file proves Theorem 1.25 from [EG].
-/

@[expose] public section

open Set Metric
open scoped Topology

section VariantVitali

variable {α ι : Type*} [PseudoMetricSpace α]

lemma closedBall_subset_closedBall_five_mul
    {ca cb y : α} {ra rb : ℝ}
    (hy : y ∈ Metric.closedBall ca ra)
    (hinter : (Metric.closedBall ca ra ∩ Metric.closedBall cb rb).Nonempty)
    (hra : ra ≤ 2 * rb) :
    y ∈ Metric.closedBall cb (5 * rb) :=
  Metric.closedBall_subset_closedBall'
    (by linarith [Metric.dist_le_add_of_nonempty_closedBall_inter_closedBall hinter]) hy

lemma closedBall_subset_removed_of_fine
    (w : Finset ι) (c : ι → α) (r : ι → ℝ)
    {x : α} {a : ι} {ε : ℝ}
    (hεpos : 0 < ε)
    (hεsubset : Metric.ball x ε ⊆ (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ)
    (hca : c a = x) (hra : r a ≤ ε / 2) :
    Metric.closedBall (c a) (r a) ⊆
      (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := by
  subst hca; exact (Metric.closedBall_subset_ball (by linarith)).trans hεsubset

lemma not_mem_finset_of_inter_nonempty_and_subset_compl
    (w : Finset ι) (c : ι → α) (r : ι → ℝ)
    {a b : ι}
    (hab_nonempty :
      (Metric.closedBall (c a) (r a) ∩ Metric.closedBall (c b) (r b)).Nonempty)
    (hBa_compl : Metric.closedBall (c a) (r a) ⊆
      (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ) :
    b ∉ (w : Set ι) := by
  obtain ⟨y, hya, hyb⟩ := hab_nonempty
  exact fun hbw => hBa_compl hya (mem_iUnion₂.2 ⟨b, hbw, hyb⟩)

/-- Variant of Vitali's covering theorem (Theorem 1.25 in [EG]).
Given a set `X` and a cover of `X` by a fine family
of balls `F` with bounded radii, there exists a
countable disjoint subfamily `G` of `F` such that
for each finite subset `w` of `F`, the set `X \ ⋃ w`
is covered by the union of the balls in `G \ w`
enlarged by a factor of 5. -/
theorem vitali_variant_classical
    {X : Set α} [SecondCountableTopology α]
    (t : Set ι) (c : ι → α) (r : ι → ℝ)
    (hf : ∀ x ∈ X, ∀ ε > (0 : ℝ), ∃ a ∈ t, r a ≤ ε ∧ c a = x)
    (hrad : ∃ R, ∀ a ∈ t, r a ≤ R)
    (hpos : ∀ a ∈ t, 0 < r a) :
    ∃ u ⊆ t,
      u.Countable ∧
      u.PairwiseDisjoint (fun a => Metric.closedBall (c a) (r a)) ∧
      ∀ w : Finset ι, (w : Set ι) ⊆ t →
        X \ (⋃ a ∈ w, Metric.closedBall (c a) (r a)) ⊆
          ⋃ b ∈ (u \ (w : Set ι)), Metric.closedBall (c b) (5 * r b) := by
  classical
  let B : ι → Set α := fun a => Metric.closedBall (c a) (r a)
  obtain ⟨R, hR⟩ := hrad
  have hnonneg : ∀ a ∈ t, 0 ≤ r a := fun a ha => (hpos a ha).le
  obtain ⟨u, hut, hdisj, hcovering⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      B t r 2 (by norm_num) hnonneg R hR
      (fun a ha => ⟨c a, Metric.mem_closedBall_self (hnonneg a ha)⟩)
  have hu_countable : u.Countable :=
    hdisj.countable_of_nonempty_interior fun a ha =>
      Set.Nonempty.mono Metric.ball_subset_interior_closedBall
        ⟨c a, Metric.mem_ball_self (hpos a (hut ha))⟩
  refine ⟨u, hut, hu_countable, by simpa [B] using hdisj, fun w hw x hx => ?_⟩
  rcases hx with ⟨hxX, hx_not_removed⟩
  have hclosed : IsClosed (⋃ a ∈ (w : Set ι), Metric.closedBall (c a) (r a)) :=
    w.finite_toSet.isClosed_biUnion fun _ _ => Metric.isClosed_closedBall
  obtain ⟨ε, hεpos, hεsubset⟩ := Metric.mem_nhds_iff.mp
    (hclosed.isOpen_compl.mem_nhds (by simpa using hx_not_removed))
  obtain ⟨a, hat, hra, hca⟩ := hf x hxX (ε / 2) (half_pos hεpos)
  have hBa_compl := closedBall_subset_removed_of_fine w c r hεpos hεsubset hca hra
  rcases hcovering a hat with ⟨b, hbu, hab_nonempty, hab_radius⟩
  have hb_not_w : b ∉ (w : Set ι) :=
    not_mem_finset_of_inter_nonempty_and_subset_compl w c r hab_nonempty hBa_compl
  have hxa : x ∈ Metric.closedBall (c a) (r a) := by
    simp only [B, hca] at *; exact Metric.mem_closedBall_self (hnonneg a hat)
  refine mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨⟨hbu, hb_not_w⟩, ?_⟩⟩
  exact closedBall_subset_closedBall_five_mul hxa hab_nonempty hab_radius

end VariantVitali
