/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic


/-!
# Weak sequential compactness in a Hilbert space

A bounded sequence in a real Hilbert space has a subsequence along which every inner product
converges, to the inner product against one fixed vector. This is the sequential form of
Banach-Alaoglu on a reflexive space. The direct method of the calculus of variations runs on
this compactness, with `EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt` supplying the
strong compactness at the lower exponent.

Mathlib has Banach-Alaoglu as `WeakDual.isCompact_closedBall` and the weak topology as
`WeakSpace`, and stops short of the sequential statement, which needs the ball to be metrisable
and so the space to be separable. The proof here avoids separability of the whole space by
working inside the closed span of the sequence.

## Three steps

* the diagonal: `⟪u n, u m⟫` lies in a fixed compact box for each `m`, so the sequence of
  functions `m ↦ ⟪u n, u m⟫` lies in a compact subset of `ℕ → ℝ`, which is metrisable, and a
  subsequence converges pointwise;
* the extension: the vectors against which the inner products converge form a closed submodule,
  since the bound `M` makes the convergence uniform in the direction, and it contains the
  sequence, hence the closed span, hence everything by orthogonal decomposition;
* the limit: the resulting functional is linear and bounded by `M`, so Riesz representation names
  the weak limit.

## Main declarations

* `EllipticPdes.Analysis.exists_weakLimit`: the weak sequential compactness statement.

## References

James Guo, *Partial Differential Equations*, Theorem V.2.5.
-/

@[expose] public section

open Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Weak sequential compactness.** A bounded sequence in a real Hilbert space has a subsequence
whose inner products against every vector converge, to the inner products against one vector. -/
theorem exists_weakLimit {u : ℕ → H} {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ (w : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ v : H, Tendsto (fun k => ⟪u (φ k), v⟫) atTop (𝓝 ⟪w, v⟫) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  -- The diagonal, through the compactness of a box in `ℕ → ℝ`.
  have hbox : ∀ n m, ⟪u n, u m⟫ ∈ Set.Icc (-(M * ‖u m‖)) (M * ‖u m‖) := by
    intro n m
    have habs : |⟪u n, u m⟫| ≤ ‖u n‖ * ‖u m‖ := abs_real_inner_le_norm _ _
    have hle : ‖u n‖ * ‖u m‖ ≤ M * ‖u m‖ :=
      mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _)
    rw [Set.mem_Icc]
    exact ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩
  obtain ⟨L, -, φ, hφ, hφtend⟩ :=
    (isCompact_pi_infinite
      (fun m => isCompact_Icc (a := -(M * ‖u m‖)) (b := M * ‖u m‖))).tendsto_subseq
      (x := fun n m => ⟪u n, u m⟫) (fun n => hbox n)
  have hdiag : ∀ m, Tendsto (fun k => ⟪u (φ k), u m⟫) atTop (𝓝 (L m)) :=
    fun m => (tendsto_pi_nhds.mp hφtend) m
  -- The directions along which the inner products converge.
  set T : Submodule ℝ H :=
    { carrier := {v | ∃ l : ℝ, Tendsto (fun k => ⟪u (φ k), v⟫) atTop (𝓝 l)}
      add_mem' := by
        rintro x y ⟨lx, hx⟩ ⟨ly, hy⟩
        exact ⟨lx + ly, by simpa only [inner_add_right] using hx.add hy⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨lx, hx⟩
        refine ⟨c * lx, ?_⟩
        simpa only [real_inner_smul_right] using hx.const_mul c } with hTdef
  have hTmem : ∀ m, u m ∈ T := fun m => ⟨L m, hdiag m⟩
  -- `T` is closed, since the bound makes the convergence uniform in the direction.
  have hTclosed : IsClosed (T : Set H) := by
    rw [← isSeqClosed_iff_isClosed]
    intro x v hx hxv
    have hcauchy : CauchySeq (fun k => ⟪u (φ k), v⟫) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨j, hj⟩ : ∃ j, ‖v - x j‖ < ε / (3 * (M + 1)) := by
        obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp hxv (ε / (3 * (M + 1))) (by positivity)
        exact ⟨j, by simpa [dist_eq_norm, norm_sub_rev] using hj j le_rfl⟩
      obtain ⟨l, hl⟩ := hx j
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (ε / 3) (by positivity)
      refine ⟨N, fun k hk m hm => ?_⟩
      have hbd : ∀ i, |⟪u (φ i), v⟫ - ⟪u (φ i), x j⟫| ≤ M * ‖v - x j‖ := by
        intro i
        rw [← inner_sub_right]
        exact le_trans (abs_real_inner_le_norm _ _)
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
      have hMv : M * ‖v - x j‖ < ε / 3 := by
        have hlt : M * ‖v - x j‖ ≤ M * (ε / (3 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hj.le hM0
        have hkey : M * (ε / (3 * (M + 1))) < ε / 3 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hε, hM0]
        linarith
      have hmid := hN k hk m hm
      rw [Real.dist_eq] at hmid ⊢
      have e1 := hbd k
      have e2 := hbd m
      have e2' : |⟪u (φ m), x j⟫ - ⟪u (φ m), v⟫| ≤ M * ‖v - x j‖ := by
        rw [abs_sub_comm]; exact e2
      have t1 := abs_sub_le (⟪u (φ k), v⟫) (⟪u (φ k), x j⟫) (⟪u (φ m), v⟫)
      have t2 := abs_sub_le (⟪u (φ k), x j⟫) (⟪u (φ m), x j⟫) (⟪u (φ m), v⟫)
      linarith
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
    exact ⟨l, hl⟩
  -- Every direction is reached: the closed span by closedness, its complement trivially.
  have hspan : (Submodule.span ℝ (Set.range u)).topologicalClosure ≤ T := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hTmem m
    · exact hTclosed
  have hTtop : ∀ v : H, ∃ l : ℝ, Tendsto (fun k => ⟪u (φ k), v⟫) atTop (𝓝 l) := by
    intro v
    set K := (Submodule.span ℝ (Set.range u)).topologicalClosure with hKdef
    have : CompleteSpace K :=
      (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    have h1 : (K.starProjection v) ∈ T := hspan (K.starProjection_apply_mem v)
    have h2 : (v - K.starProjection v) ∈ T := by
      refine ⟨0, ?_⟩
      have hperp : (v - K.starProjection v) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
      have hzero : ∀ k, ⟪u (φ k), v - K.starProjection v⟫ = 0 := fun k =>
        hperp _ ((Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨φ k, rfl⟩))
      simp only [hzero]
      exact tendsto_const_nhds
    have hsum := T.add_mem h1 h2
    rwa [add_sub_cancel] at hsum
  -- The limit functional, and the vector Riesz gives for it.
  choose g hg using hTtop
  have hlin : IsLinearMap ℝ g := by
    constructor
    · intro y z
      refine (tendsto_nhds_unique (hg (y + z)) ?_)
      simpa only [inner_add_right] using (hg y).add (hg z)
    · intro c y
      refine (tendsto_nhds_unique (hg (c • y)) ?_)
      simpa only [real_inner_smul_right, smul_eq_mul] using (hg y).const_mul c
  have hbound : ∀ v, |g v| ≤ M * ‖v‖ := by
    intro v
    refine le_of_tendsto (hg v).abs (Eventually.of_forall (fun k => ?_))
    exact le_trans (abs_real_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  set f : H →L[ℝ] ℝ :=
    LinearMap.mkContinuous (IsLinearMap.mk' g hlin) M (fun v => by
      simpa [Real.norm_eq_abs] using hbound v) with hfdef
  refine ⟨(InnerProductSpace.toDual ℝ H).symm f, φ, hφ, fun v => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hg v


/-! ### What a weak limit inherits -/

variable {u : ℕ → H} {w : H}

omit [CompleteSpace H] in
/-- **Weak lower semicontinuity of the norm.** A bound along the sequence bounds the weak
limit. -/
theorem norm_weakLimit_le {M : ℝ} (hM : ∀ k, ‖u k‖ ≤ M)
    (hw : ∀ v : H, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪w, v⟫)) :
    ‖w‖ ≤ M := by
  rcases eq_or_lt_of_le (norm_nonneg w) with h | h
  · exact h ▸ le_trans (norm_nonneg _) (hM 0)
  · have hsq : ‖w‖ ^ 2 ≤ M * ‖w‖ := by
      have hlim : Tendsto (fun k => ⟪u k, w⟫) atTop (𝓝 (‖w‖ ^ 2)) := by
        simpa [real_inner_self_eq_norm_sq] using hw w
      refine le_of_tendsto hlim (Eventually.of_forall (fun k => ?_))
      exact le_trans (real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
    nlinarith

/-- **Stability of a closed subspace under weak limits.** -/
theorem mem_of_weakLimit {K : Submodule ℝ H} (hK : IsClosed (K : Set H)) (hu : ∀ k, u k ∈ K)
    (hw : ∀ v : H, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪w, v⟫)) :
    w ∈ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  have hperp : w ∈ Kᗮᗮ := by
    intro v hv
    have hzero : ∀ k, ⟪u k, v⟫ = 0 := fun k => hv _ (hu k)
    have := hw v
    rw [show (fun k => ⟪u k, v⟫) = fun _ => (0 : ℝ) from funext hzero] at this
    have := tendsto_nhds_unique this tendsto_const_nhds
    rw [real_inner_comm]
    exact this
  rwa [Submodule.orthogonal_orthogonal] at hperp


omit [CompleteSpace H] in
/-- The weak limit of a sequence whose norms converge is bounded by that limit. -/
theorem norm_weakLimit_le_of_tendsto {m : ℝ} (hm : Tendsto (fun k => ‖u k‖) atTop (𝓝 m))
    (hw : ∀ v : H, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪w, v⟫)) :
    ‖w‖ ≤ m := by
  have hm0 : 0 ≤ m := ge_of_tendsto hm (Eventually.of_forall (fun k => norm_nonneg _))
  rcases eq_or_lt_of_le (norm_nonneg w) with h | h
  · exact h ▸ hm0
  · have hlim : Tendsto (fun k => ⟪u k, w⟫) atTop (𝓝 (‖w‖ ^ 2)) := by
      simpa [real_inner_self_eq_norm_sq] using hw w
    have hsq : ‖w‖ ^ 2 ≤ m * ‖w‖ :=
      le_of_tendsto_of_tendsto' hlim (hm.mul_const ‖w‖)
        (fun k => le_trans (real_inner_le_norm _ _) le_rfl)
    nlinarith

end EllipticPdes.Analysis
