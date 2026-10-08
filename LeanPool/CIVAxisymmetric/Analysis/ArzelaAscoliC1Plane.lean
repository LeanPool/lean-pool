/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.ArzelaAscoliC1HalfPlane

/-!
# `C¹` extraction on the whole plane

The recentred variables `eq:aniso:zoom:receding:variables` put the selected point at the origin
of `ℝ × ℝ` and send the axis to `R = -A_n` with `A_n → ∞`, so the meridional fields of the
receding-axis case live on the *whole* plane and the compact sets that exhaust their domain are
the centred squares `[-(j+1), j+1]²` rather than the half-plane squares of
`CIV.halfPlaneRectangle`.

A sequence of smooth functions on `ℝ × ℝ` whose values, gradients and second derivatives are
bounded by one constant `L` on each centred square — for all large `n`, the threshold being
allowed to depend on the square — has a subsequence converging, together with its gradient,
uniformly on every one of those squares.  The limit is bounded by `L` on all of `ℝ × ℝ` and is
differentiable at *every* point, since every point of the plane is interior to a centred square;
this is the difference with the half-plane statement, where the axis is a boundary and the
derivative is identified only off it.

The extraction on one square is `CIV.exists_subseq_tendstoUniformlyOn_c1`; the passage from one
square to all of them at once is the diagonal extraction
`CIV.exists_subseq_tendstoUniformlyOn_forall_of_subseq`, applied to the pair `(V_n, ∇V_n)` so
that the function and its gradient are extracted along a single subsequence.

The whole statement is at a fixed value of any remaining parameter: no time variable occurs, and
no equicontinuity in a parameter is claimed or used.
-/

public section

open Filter Topology Set

noncomputable section

namespace CIV

/-! ### The centred squares -/

/-- The closed squares `[-(j+1), j+1] × [-(j+1), j+1]`, which exhaust `ℝ × ℝ` and whose
interiors already do. -/
@[expose] def planeRectangle (j : ℕ) : Set (ℝ × ℝ) :=
  Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1)

theorem isCompact_planeRectangle (j : ℕ) : IsCompact (planeRectangle j) :=
  isCompact_Icc.prod isCompact_Icc

theorem convex_planeRectangle (j : ℕ) : Convex ℝ (planeRectangle j) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

/-- The selected point of the recentred variables is the origin, and it lies in every centred
square. -/
theorem zero_mem_planeRectangle (j : ℕ) : ((0 : ℝ), (0 : ℝ)) ∈ planeRectangle j := by
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  exact ⟨⟨by linarith only [hj], hj⟩, by linarith only [hj], hj⟩

/-- Every point of the plane is interior to one of the centred squares. -/
theorem exists_mem_interior_planeRectangle (p : ℝ × ℝ) :
    ∃ j : ℕ, p ∈ interior (planeRectangle j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max |p.1| |p.2|)
  have h1 : |p.1| < (j : ℝ) + 1 := lt_of_le_of_lt (le_max_left _ _) (by linarith only [hj])
  have h2 : |p.2| < (j : ℝ) + 1 := lt_of_le_of_lt (le_max_right _ _) (by linarith only [hj])
  have h1' := abs_lt.mp h1
  have h2' := abs_lt.mp h2
  refine ⟨j, ?_⟩
  rw [planeRectangle, interior_prod_eq, interior_Icc]
  exact ⟨⟨h1'.1, h1'.2⟩, h2'.1, h2'.2⟩

/-- Every point of the plane lies in one of the centred squares. -/
theorem exists_mem_planeRectangle (p : ℝ × ℝ) : ∃ j : ℕ, p ∈ planeRectangle j := by
  obtain ⟨j, hj⟩ := exists_mem_interior_planeRectangle p
  exact ⟨j, interior_subset hj⟩

/-- A compact subset of the plane is contained in one of the centred squares. -/
theorem exists_planeRectangle_superset {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ j : ℕ, K ⊆ planeRectangle j := by
  obtain ⟨a, ha⟩ := (hK.image continuous_fst.abs).bddAbove
  obtain ⟨b, hb⟩ := (hK.image continuous_snd.abs).bddAbove
  obtain ⟨j, hj⟩ := exists_nat_gt (max a b)
  have haj : a ≤ (j : ℝ) := le_trans (le_max_left a b) hj.le
  have hbj : b ≤ (j : ℝ) := le_trans (le_max_right a b) hj.le
  refine ⟨j, fun p hp => ?_⟩
  have hpa : |p.1| ≤ a := ha ⟨p, hp, rfl⟩
  have hpb : |p.2| ≤ b := hb ⟨p, hp, rfl⟩
  have h1 := abs_le.mp hpa
  have h2 := abs_le.mp hpb
  exact ⟨⟨by linarith only [h1.1, haj], by linarith only [h1.2, haj]⟩,
    by linarith only [h2.1, hbj], by linarith only [h2.2, hbj]⟩

/-! ### The extraction -/

/-- `C¹` compactness on the plane: from a sequence of smooth functions whose value, gradient and
second derivative are bounded by `L` on each centred square for all large `n`, one subsequence
converges together with its gradient, uniformly on every centred square.  The limit obeys the
same bound everywhere, its gradient limit is continuous on each square, and the limit is
differentiable at every point with derivative the limit of the gradients. -/
theorem exists_subseq_tendstoUniformlyOn_c1_plane
    (Vseq : ℕ → ℝ × ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ planeRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : ℝ × ℝ → ℝ, ∃ DV : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ),
      (∀ j, TendstoUniformlyOn (fun n => Vseq (φ n)) V atTop (planeRectangle j)) ∧
      (∀ j, TendstoUniformlyOn (fun n => fderiv ℝ (Vseq (φ n))) DV atTop
        (planeRectangle j)) ∧
      (∀ j, ContinuousOn DV (planeRectangle j)) ∧
      (∀ p : ℝ × ℝ, |V p| ≤ L) ∧
      (∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p) := by
  classical
  have hdiff : ∀ n, Differentiable ℝ (Vseq n) := fun n => (contDiff_infty_iff_fderiv.mp
    (hsmooth n)).1
  have hfderivCont : ∀ n, Continuous (fderiv ℝ (Vseq n)) := fun n =>
    (contDiff_infty_iff_fderiv.mp (hsmooth n)).2.continuous
  set P : ℕ → (ℝ × ℝ) → ℝ × ((ℝ × ℝ) →L[ℝ] ℝ) :=
    fun n p => (Vseq n p, fderiv ℝ (Vseq n) p)
  -- The refinement step on one square, after discarding the indices below its threshold.
  have hstep : ∀ (j : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : (ℝ × ℝ) → ℝ × ((ℝ × ℝ) →L[ℝ] ℝ),
        TendstoUniformlyOn (fun n => P (g (g' n))) w atTop (planeRectangle j) := by
    intro j g hg
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hbdd j)
    have hshift : ∀ n : ℕ, N ≤ g (n + N) := fun n =>
      le_trans (Nat.le_add_left N n) hg.le_apply
    obtain ⟨ψ, hψ, Vlim, DVlim, hVunif, hDVunif, -, -, -⟩ :=
      exists_subseq_tendstoUniformlyOn_c1 (planeRectangle j) (isCompact_planeRectangle j)
        (convex_planeRectangle j) (fun n => Vseq (g (n + N))) L hL
        (fun n => hsmooth _) (fun n y hy => (hN _ (hshift n) y hy).1)
        (fun n y hy => (hN _ (hshift n) y hy).2.1)
        (fun n y hy => (hN _ (hshift n) y hy).2.2)
    refine ⟨fun n => ψ n + N, fun a b hab => by simpa using hψ hab,
      fun p => (Vlim p, DVlim p), ?_⟩
    exact tendstoUniformlyOn_prod_mk hVunif hDVunif
  obtain ⟨φ, hφ, w, hw⟩ :=
    exists_subseq_tendstoUniformlyOn_forall_of_subseq planeRectangle P hstep
  refine ⟨φ, hφ, fun p => (w p).1, fun p => (w p).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact uniformContinuous_fst.comp_tendstoUniformlyOn (hw j)
  · intro j
    exact uniformContinuous_snd.comp_tendstoUniformlyOn (hw j)
  · intro j
    refine TendstoUniformlyOn.continuousOn
      (uniformContinuous_snd.comp_tendstoUniformlyOn (hw j)) ?_
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
      (hfderivCont (φ n)).continuousOn)
  · intro p
    obtain ⟨j, hj⟩ := exists_mem_planeRectangle p
    have hlim : Tendsto (fun n => Vseq (φ n) p) atTop (𝓝 ((w p).1)) :=
      (uniformContinuous_fst.comp_tendstoUniformlyOn (hw j)).tendsto_at hj
    have hev : ∀ᶠ n in atTop, |Vseq (φ n) p| ≤ L := by
      have h := hφ.tendsto_atTop.eventually (hbdd j)
      filter_upwards [h] with n hn
      exact (hn p hj).1
    have hev' : ∀ᶠ n in atTop, -L ≤ Vseq (φ n) p ∧ Vseq (φ n) p ≤ L := by
      filter_upwards [hev] with n hn
      exact abs_le.mp hn
    rw [abs_le]
    constructor
    · exact ge_of_tendsto hlim (by filter_upwards [hev'] with n hn using hn.1)
    · exact le_of_tendsto hlim (by filter_upwards [hev'] with n hn using hn.2)
  · intro p
    obtain ⟨j, hj⟩ := exists_mem_interior_planeRectangle p
    refine hasFDerivAt_of_tendstoUniformlyOn isOpen_interior
      ((uniformContinuous_snd.comp_tendstoUniformlyOn (hw j)).mono interior_subset)
      (fun n x _ => (hdiff (φ n) x).hasFDerivAt) (fun x hx => ?_) hj
    exact (uniformContinuous_fst.comp_tendstoUniformlyOn (hw j)).tendsto_at (interior_subset hx)

end CIV
