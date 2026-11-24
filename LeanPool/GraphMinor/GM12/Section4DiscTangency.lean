/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM12.Section4NormalArcDisc
import LeanPool.GraphMinor.Surface.Wedge

/-!
# A disc touching one boundary point

For the singleton prescriptions in XII (4.4), page 251, a source
contact disc can be attached to a connecting disc at one boundary
point. Follow an outward radius of a collar for a short distance,
avoiding a closed forbidden set. Thicken this arc while forbidding
the original disc. Only its initial endpoint remains in that disc.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric Topology

/-- Attach a disc at one boundary point, avoiding a closed set that
does not contain that point, and retain a second boundary mark. -/
theorem exists_disc_touching_boundary_point
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {D Z : Set S} (hD : IsClosedDisc D)
    (hZ : IsClosed Z) {p : S} (hp : p ∈ discBd D) (hpZ : p ∉ Z) :
    ∃ (Q : Set S) (q : S), IsClosedDisc Q ∧ Q ∩ D = {p} ∧
      Disjoint Q Z ∧ p ≠ q ∧ ({p, q} : Set S) ⊆ discBd Q := by
  obtain ⟨E, hE, hDE, _⟩ := exists_disc_around (fun x => (hS.2.2 x).isManifoldPoint)
    hD (fun x _ => hS.2.2 x) isOpen_univ (subset_univ _)
  obtain ⟨P⟩ := hD.isOArc_discBd
  obtain ⟨c, c', hcc, _, _, _, hl, _, hcD, _, hcP⟩ := exists_disc_collar hD hE hDE P
  let w : Circle := P.symm ⟨p, hp⟩
  have hwP : c w = p := (hcP w).trans (congrArg Subtype.val (P.apply_symm_apply ⟨p, hp⟩))
  have hwint : (w : ℂ) ∈ interior (closedBall (0 : ℂ) 2) :=
    mem_interior.mpr ⟨ball 0 2, ball_subset_closedBall, isOpen_ball,
      by rw [mem_ball_zero_iff, Circle.norm_coe]; norm_num⟩
  have hcAt := hcc.continuousAt (mem_interior_iff_mem_nhds.mp hwint)
  have hwavoid : c w ∈ Zᶜ := by rw [hwP]; exact hpZ
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hcAt.preimage_mem_nhds (hZ.isOpen_compl.mem_nhds hwavoid))
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  let z : unitInterval → ℂ := fun t => (1 + δ * t.val : ℝ) • (w : ℂ)
  have hzN : ∀ t, ‖z t‖ = 1 + δ * t.val := by
    intro t
    dsimp only [z]
    have hnonneg : 0 ≤ 1 + δ * t.val := by
      have hmul := mul_nonneg hδ.le t.property.1
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, Circle.norm_coe, mul_one]
  have hz2 : ∀ t, z t ∈ closedBall 0 2 := by
    intro t
    rw [mem_closedBall_zero_iff, hzN]
    have hmul := mul_le_mul_of_nonneg_left t.property.2 hδ.le
    have hδhi := min_le_right (ε / 2) (1 / 2 : ℝ)
    change δ ≤ 1 / 2 at hδhi
    linarith
  have hzε : ∀ t, z t ∈ ball (w : ℂ) ε := by
    intro t
    rw [mem_ball, dist_eq_norm]
    have heq : z t - w = (δ * t.val : ℝ) • (w : ℂ) := by
      dsimp only [z]
      rw [add_smul, one_smul, add_sub_cancel_left]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hδ.le t.property.1),
      Circle.norm_coe, mul_one]
    exact (mul_le_mul_of_nonneg_left t.property.2 hδ.le).trans_lt (by simpa using hδε)
  let a : unitInterval → S := fun t => c (z t)
  have hac : Continuous a := hcc.comp_continuous (by dsimp only [z]; fun_prop) hz2
  have hai : Function.Injective a := by
    intro s t heq
    have hst := congrArg norm (hl.injOn (hz2 s) (hz2 t) heq)
    rw [hzN, hzN] at hst
    apply Subtype.ext
    exact mul_left_cancel₀ hδ.ne' (add_left_cancel hst)
  have ha0 : a 0 = p := by
    change c ((1 + δ * 0 : ℝ) • (w : ℂ)) = p
    simpa only [mul_zero, add_zero, one_smul] using hwP
  have haZ : ∀ t, a t ∉ Z := fun t => hεsub (hzε t)
  have haD : ∀ t, a t ∈ D → t = 0 := by
    intro t ht
    obtain ⟨v, hv, hve⟩ := hcD.symm ▸ ht
    have hvz := hl.injOn (closedBall_subset_closedBall (by norm_num) hv) (hz2 t) hve
    have hle : ‖z t‖ ≤ 1 := hvz ▸ mem_closedBall_zero_iff.mp hv
    rw [hzN] at hle
    have ht0 : t.val = 0 := le_antisymm (by nlinarith) t.property.1
    exact Subtype.ext ht0
  have ha1D : a 1 ∉ D := fun ht => zero_ne_one (haD 1 ht).symm
  let B := D ∪ Z ∪ {a 1}
  have hB : IsClosed B := (hD.isClosed.union hZ).union isClosed_singleton
  have hmeet : range a ∩ B ⊆ {a 0, a 1} := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    rcases ht with (htD | htZ) | ht1
    · rw [haD t htD]
      exact Or.inl rfl
    · exact (haZ t htZ).elim
    · exact Or.inr ht1
  obtain ⟨Q, hQ, hQB, hbd, _⟩ := exists_normal_arc_disc hS ⟨hac, hai⟩ hB
    (Or.inl (Or.inl (ha0.symm ▸ discBd_subset D hp))) (Or.inr (by simp)) hmeet
  refine ⟨Q, a 1, hQ, ?_, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      have hends := hQB.subset ⟨hx.1, Or.inl (Or.inl hx.2)⟩
      rcases hends with hx0 | hx1
      · exact Set.mem_singleton_iff.mpr (hx0.trans ha0)
      · exact False.elim (ha1D ((Set.mem_singleton_iff.mp hx1) ▸ hx.2))
    · rintro x rfl
      exact ⟨discBd_subset Q (ha0 ▸ hbd (Or.inl rfl)), discBd_subset D hp⟩
  · apply Set.disjoint_left.mpr
    intro x hxQ hxZ
    have hends := hQB.subset ⟨hxQ, Or.inl (Or.inr hxZ)⟩
    rcases hends with hx0 | hx1
    · exact haZ 0 (hx0 ▸ hxZ)
    · exact haZ 1 ((Set.mem_singleton_iff.mp hx1) ▸ hxZ)
  · intro hpq
    exact zero_ne_one (hai (ha0.trans hpq))
  · rwa [ha0] at hbd

end GraphMinor.GM12
