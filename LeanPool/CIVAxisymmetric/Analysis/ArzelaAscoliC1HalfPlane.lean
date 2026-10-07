/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.ArzelaAscoliC1
public import LeanPool.CIVAxisymmetric.Analysis.DiagonalUniformExtraction

/-!
# `C¹` extraction on the closed half-plane

A sequence of smooth functions on `ℝ × ℝ` whose values, gradients and second derivatives are
bounded by one constant `L` on each of the squares `[0, j+1] × [-(j+1), j+1]` — for all large
`n`, the threshold being allowed to depend on the square — has a subsequence converging, together
with its gradient, uniformly on every one of those squares.  The limit is bounded by `L` on the
closed half-plane `{R ≥ 0}` and is differentiable at every point of the open half-plane
`{R > 0}`, with derivative the limit of the gradients.

This is `C¹` compactness on compact subsets of the *closed* half-plane, so the limit and the
convergence reach the axis `{R = 0}`; only the identification of the limit of the gradients with
a derivative is restricted to the open half-plane, where the squares have interior points.

The extraction on one square is `CIV.exists_subseq_tendstoUniformlyOn_c1`; the passage from one
square to all of them at once is the diagonal extraction
`CIV.exists_subseq_tendstoUniformlyOn_forall_of_subseq`, applied to the pair
`(V_n, ∇V_n)` so that the function and its gradient are extracted along a single subsequence.

The whole statement is at a fixed value of any remaining parameter: no time variable occurs, and
no equicontinuity in a parameter is claimed or used.
-/

public section

open Filter Topology Set

noncomputable section

namespace CIV

/-! ### Uniform convergence into a product -/

/-- Uniform convergence of two families into pseudometric spaces gives uniform convergence of the
pair, along the same filter. -/
theorem tendstoUniformlyOn_prod_mk {ι X : Type*} {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β}
    {p : Filter ι} {s : Set X} (hF : TendstoUniformlyOn F f p s)
    (hG : TendstoUniformlyOn G g p s) :
    TendstoUniformlyOn (fun n x => (F n x, G n x)) (fun x => (f x, g x)) p s := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  filter_upwards [hF ε hε, hG ε hε] with n h1 h2 x hx
  rw [Prod.dist_eq]
  exact max_lt (h1 x hx) (h2 x hx)

/-! ### The exhausting squares of the closed half-plane -/

/-- The closed squares `[0, j+1] × [-(j+1), j+1]`, which exhaust the closed half-plane
`{p : ℝ × ℝ | 0 ≤ p.1}` and whose interiors exhaust the open half-plane `{0 < p.1}`. -/
@[expose] def halfPlaneRectangle (j : ℕ) : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) ((j : ℝ) + 1) ×ˢ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1)

theorem isCompact_halfPlaneRectangle (j : ℕ) : IsCompact (halfPlaneRectangle j) :=
  isCompact_Icc.prod isCompact_Icc

theorem convex_halfPlaneRectangle (j : ℕ) : Convex ℝ (halfPlaneRectangle j) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

theorem nonneg_of_mem_halfPlaneRectangle {j : ℕ} {p : ℝ × ℝ} (hp : p ∈ halfPlaneRectangle j) :
    0 ≤ p.1 := hp.1.1

/-- Every point of the closed half-plane lies in one of the squares. -/
theorem exists_mem_halfPlaneRectangle {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    ∃ j : ℕ, p ∈ halfPlaneRectangle j := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max p.1 |p.2|)
  have h1 : p.1 ≤ (j : ℝ) + 1 := le_trans (le_trans (le_max_left _ _) hj.le) (by linarith only)
  have h2 : |p.2| ≤ (j : ℝ) + 1 := le_trans (le_trans (le_max_right _ _) hj.le) (by linarith only)
  have h3 := abs_le.mp h2
  exact ⟨j, ⟨hp, h1⟩, h3.1, h3.2⟩

/-- Every point of the open half-plane lies in the interior of one of the squares. -/
theorem exists_mem_interior_halfPlaneRectangle {p : ℝ × ℝ} (hp : 0 < p.1) :
    ∃ j : ℕ, p ∈ interior (halfPlaneRectangle j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max p.1 |p.2|)
  have h1 : p.1 < (j : ℝ) + 1 := lt_of_le_of_lt (le_max_left _ _) (by linarith only [hj])
  have h2 : |p.2| < (j : ℝ) + 1 := lt_of_le_of_lt (le_max_right _ _) (by linarith only [hj])
  have h3 := abs_lt.mp h2
  refine ⟨j, ?_⟩
  rw [halfPlaneRectangle, interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨⟨hp, h1⟩, h3.1, h3.2⟩

/-- The segment `[0, A] × {0}` of the axis line sits inside every square of index at least `A`. -/
theorem segment_subset_halfPlaneRectangle {A : ℝ} {j : ℕ} (hA : A ≤ (j : ℝ) + 1) :
    Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ) ⊆ halfPlaneRectangle j := by
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  rintro ⟨r, y⟩ ⟨hr, hy⟩
  have hy0 : y = 0 := hy
  subst hy0
  exact ⟨⟨hr.1, le_trans hr.2 hA⟩, by linarith only [hj], hj⟩

/-! ### The extraction -/

/-- `C¹` compactness on the closed half-plane: from a sequence of smooth functions whose value,
gradient and second derivative are bounded by `L` on each square `[0, j+1] × [-(j+1), j+1]` for
all large `n`, one subsequence converges together with its gradient, uniformly on every square.
The limit obeys the same bound on the closed half-plane, its gradient limit is continuous on each
square, and at every point of the open half-plane the limit is differentiable with derivative the
limit of the gradients. -/
theorem exists_subseq_tendstoUniformlyOn_c1_halfPlane
    (Vseq : ℕ → ℝ × ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : ℝ × ℝ → ℝ, ∃ DV : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ),
      (∀ j, TendstoUniformlyOn (fun n => Vseq (φ n)) V atTop (halfPlaneRectangle j)) ∧
      (∀ j, TendstoUniformlyOn (fun n => fderiv ℝ (Vseq (φ n))) DV atTop
        (halfPlaneRectangle j)) ∧
      (∀ j, ContinuousOn DV (halfPlaneRectangle j)) ∧
      (∀ p : ℝ × ℝ, 0 ≤ p.1 → |V p| ≤ L) ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p) := by
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
        TendstoUniformlyOn (fun n => P (g (g' n))) w atTop (halfPlaneRectangle j) := by
    intro j g hg
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hbdd j)
    have hshift : ∀ n : ℕ, N ≤ g (n + N) := fun n =>
      le_trans (Nat.le_add_left N n) hg.le_apply
    obtain ⟨ψ, hψ, Vlim, DVlim, hVunif, hDVunif, -, -, -⟩ :=
      exists_subseq_tendstoUniformlyOn_c1 (halfPlaneRectangle j) (isCompact_halfPlaneRectangle j)
        (convex_halfPlaneRectangle j) (fun n => Vseq (g (n + N))) L hL
        (fun n => hsmooth _) (fun n y hy => (hN _ (hshift n) y hy).1)
        (fun n y hy => (hN _ (hshift n) y hy).2.1)
        (fun n y hy => (hN _ (hshift n) y hy).2.2)
    refine ⟨fun n => ψ n + N, fun a b hab => by simpa using hψ hab,
      fun p => (Vlim p, DVlim p), ?_⟩
    exact tendstoUniformlyOn_prod_mk hVunif hDVunif
  obtain ⟨φ, hφ, w, hw⟩ :=
    exists_subseq_tendstoUniformlyOn_forall_of_subseq halfPlaneRectangle P hstep
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
  · intro p hp
    obtain ⟨j, hj⟩ := exists_mem_halfPlaneRectangle hp
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
  · intro p hp
    obtain ⟨j, hj⟩ := exists_mem_interior_halfPlaneRectangle hp
    refine hasFDerivAt_of_tendstoUniformlyOn isOpen_interior
      ((uniformContinuous_snd.comp_tendstoUniformlyOn (hw j)).mono interior_subset)
      (fun n x _ => (hdiff (φ n) x).hasFDerivAt) (fun x hx => ?_) hj
    exact (uniformContinuous_fst.comp_tendstoUniformlyOn (hw j)).tendsto_at (interior_subset hx)

/-- A subsequence of a uniformly convergent sequence converges uniformly to the same limit. -/
theorem tendstoUniformlyOn_comp_strictMono {X α : Type*} [UniformSpace α] {F : ℕ → X → α}
    {f : X → α} {s : Set X} (hF : TendstoUniformlyOn F f atTop s) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ) : TendstoUniformlyOn (fun n => F (ψ n)) f atTop s := by
  intro u hu
  exact hψ.tendsto_atTop.eventually (hF u hu)

end CIV
