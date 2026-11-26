/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Small neighborhoods for outer vertex pieces

In the crossing construction of XII (4.5), page 253, choose small
disjoint convex neighborhoods around the vertex blocks on the
circle. A short outward radial move gives the vertex. The strict
tangent inequality holds at the center port and hence throughout
a smaller open neighborhood of ports. Convexity keeps every outer
piece in the chosen vertex neighborhood.
-/

public section

namespace GraphMinor.GM12

open Set Metric Topology

/-- A unit circle point in an open convex neighborhood has a
nearby outer vertex and an open neighborhood of ports visible
from that vertex. This localizes the vertex stars in the crossing
construction of XII (4.5), page 253. -/
theorem exists_outer_vertex_port_neighborhood {U : Set ℂ} (hU : IsOpen U)
    (hUc : Convex ℝ U) {c : ℂ} (hc : ‖c‖ = 1) (hcU : c ∈ U) :
    ∃ v : ℂ, ∃ O : Set ℂ, v ∈ U ∧ 1 < ‖v‖ ∧ IsOpen O ∧ c ∈ O ∧ O ⊆ U ∧
      ∀ a ∈ O, 1 < ((starRingEnd ℂ) a * v).re ∧ segment ℝ a v ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU c hcU
  let v : ℂ := (1 + r / 2 : ℝ) • c
  have hvdist : dist v c = r / 2 := by
    rw [dist_eq_norm]
    have heq : v - c = (r / 2 : ℝ) • c := by
      change (1 + r / 2 : ℝ) • c - c = (r / 2 : ℝ) • c
      rw [add_smul, one_smul, add_sub_cancel_left]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hc, mul_one]
  have hvU : v ∈ U := hrU (mem_ball.mpr (by rw [hvdist]; linarith))
  have hvnorm : 1 < ‖v‖ := by
    change 1 < ‖(1 + r / 2 : ℝ) • c‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hc, mul_one]
    linarith
  have hcv : 1 < ((starRingEnd ℂ) c * v).re := by
    have hcc : ((starRingEnd ℂ) c * c).re = 1 := by
      rw [RCLike.conj_mul, hc]; norm_num
    change 1 < ((starRingEnd ℂ) c * ((1 + r / 2 : ℝ) • c)).re
    rw [mul_smul_comm, Complex.smul_re, hcc, smul_eq_mul, mul_one]
    linarith
  let O : Set ℂ := U ∩ {a : ℂ | 1 < ((starRingEnd ℂ) a * v).re}
  have hO : IsOpen O := hU.inter (isOpen_lt continuous_const (by fun_prop))
  exact ⟨v, O, hvU, hvnorm, hO, ⟨hcU, hcv⟩, inter_subset_left,
    fun a ha => ⟨ha.2, hUc.segment_subset ha.1 hvU⟩⟩

/-- Choose disjoint convex vertex neighborhoods and visible port
neighborhoods for any finite set of distinct unit circle centers.
This is the simultaneous local choice in the crossing construction
of XII (4.5), page 253. -/
theorem exists_disjoint_outer_vertex_neighborhoods {ι : Type*} [Finite ι]
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) (hinj : Function.Injective c) :
    ∃ (v : ι → ℂ) (U O : ι → Set ℂ),
      (∀ i, IsOpen (U i) ∧ Convex ℝ (U i) ∧ c i ∈ U i ∧ v i ∈ U i ∧
        1 < ‖v i‖ ∧ IsOpen (O i) ∧ c i ∈ O i ∧ O i ⊆ U i ∧
        ∀ a ∈ O i, 1 < ((starRingEnd ℂ) a * v i).re ∧ segment ℝ a (v i) ⊆ U i) ∧
      ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
  classical
  obtain ⟨W, hW, hWdisj⟩ := (finite_range c).t2_separation
  have hball : ∀ i, ∃ r : ℝ, 0 < r ∧ ball (c i) r ⊆ W (c i) := by
    intro i
    exact Metric.isOpen_iff.mp (hW (c i)).2 (c i) (hW (c i)).1
  choose r hr hrW using hball
  have hchoice : ∀ i, ∃ v : ℂ, ∃ O : Set ℂ,
      v ∈ ball (c i) (r i) ∧ 1 < ‖v‖ ∧ IsOpen O ∧ c i ∈ O ∧
      O ⊆ ball (c i) (r i) ∧
      ∀ a ∈ O, 1 < ((starRingEnd ℂ) a * v).re ∧ segment ℝ a v ⊆ ball (c i) (r i) := by
    intro i
    exact exists_outer_vertex_port_neighborhood isOpen_ball (convex_ball _ _)
      (hc i) (mem_ball_self (hr i))
  choose v O hv hvnorm hO hcO hOU hseg using hchoice
  refine ⟨v, fun i => ball (c i) (r i), O, ?_, ?_⟩
  · intro i
    exact ⟨isOpen_ball, convex_ball _ _, mem_ball_self (hr i), hv i, hvnorm i,
      hO i, hcO i, hOU i, hseg i⟩
  · intro i j hij
    exact (hWdisj (mem_range_self i) (mem_range_self j) (fun h => hij (hinj h))).mono
      (hrW i) (hrW j)

end GraphMinor.GM12
