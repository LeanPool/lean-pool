/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Zoom.OmegaEquicontinuous
public import LeanPool.CIVAxisymmetric.Analysis.DiagonalUniformExtraction
public import LeanPool.CIVAxisymmetric.Analysis.LipschitzBoundOfPointwiseLimit
public import LeanPool.CIVAxisymmetric.Analysis.MeasurableOfPointwiseLimit
public import LeanPool.CIVAxisymmetric.Zoom.DriftLimitPassage
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Extracting an admissible drift from a sequence of drifts

Generic in the ambient dimension `m` and the time horizon `T`: given a sequence of drifts
`(b n, divb n)` that are, eventually in `n`, bounded and Lipschitz in space on every compact
time-window `J ⊆ Iic T` (deviation D14 in `docs/DEVIATIONS.md`), this file
extracts a subsequence along which `(b, divb)` converges, in the sense required by
`CIV.IsAdmissibleDrift`, to an admissible drift `(B, divB)` on `Iio T`.

The route avoids weak-* (Banach-Alaoglu) compactness, which the hypotheses do not support in
general (a bounded, equi-Lipschitz-in-space sequence such as `b n (x, τ) = sin (n τ)` need not
have any pointwise- or weak-*-convergent subsequence in time). Instead it uses:

* time-`T`-clamped primitives `z ↦ ∫ s in (T - 1)..(min z.2 T), φ i n (z.1, s)`, built from each
  scalar component of `(b, divb)`, which inherit a *joint* space-time Lipschitz bound from the
  space-Lipschitz bound on `(b, divb)`;
* a box-diagonal chaining of the classical (Arzelà-Ascoli) compactness theorem to extract one
  subsequence along which every primitive converges, locally uniformly, to a continuous limit;
* a from-scratch real-analysis lemma (`exists_measurable_ae_hasDerivAt_of_lipschitz_mixed`)
  recovering a Borel, a.e.-Lipschitz-and-bounded classical time-derivative of each limit from
  its joint Lipschitz structure, via a countable dense set, absolute continuity, the McShane
  extension of a Lipschitz function, and a limsup/liminf sandwich of difference quotients;
* `CIV.ae_weakDiv_of_tendstoUniformlyOn_primitive` and
  `CIV.tendsto_integral_mul_of_tendstoUniformlyOn_primitive` (`CIV/Zoom/DriftLimitPassage.lean`),
  which pass the finite-`n` weak-divergence identity and the weak-convergence conclusion to the
  limit along the same subsequence.

The oscillatory example above is fine on this route: `a_n → 0` uniformly and the limit drift is
`0`, matching the conclusion of `CIV.exists_subseq_admissibleDrift` below.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open CKN

noncomputable section

namespace CIV

/-! ### Chaining finitely many scalar Arzelà–Ascoli extractions -/

/-- Chain scalar Arzelà–Ascoli extractions (`exists_subseq_tendstoUniformlyOn_of_modulus`) over
a finite family of scalar sequences sharing one bound and modulus of continuity on a compact
set, producing one subsequence along which every member of the family converges uniformly. -/
theorem exists_subseq_forall_tendstoUniformlyOn_of_modulus_finset {X : Type*} [MetricSpace X]
    {ι : Type*} (S : Set X) (hS : IsCompact S) (f : ι → ℕ → X → ℝ) (M : ℝ) (s : Finset ι)
    (hbdd : ∀ i ∈ s, ∀ n, ∀ x ∈ S, |f i n x| ≤ M)
    (hmod : ∀ i ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ →
      |f i n x - f i n y| ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ s, ∃ g : X → ℝ, ContinuousOn g S ∧ TendstoUniformlyOn (fun n => f i (φ n)) g atTop S
        := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | @insert a s' ha ih =>
    obtain ⟨φ', hφ', hφ'i⟩ := ih (fun i hi => hbdd i (Finset.mem_insert_of_mem hi))
      (fun i hi => hmod i (Finset.mem_insert_of_mem hi))
    obtain ⟨φ'', hφ'', g, hgc, hgu⟩ := exists_subseq_tendstoUniformlyOn_of_modulus S hS
      (fun n => f a (φ' n)) M
      (fun n x hx => hbdd a (Finset.mem_insert_self a s') (φ' n) x hx)
      (fun ε hε => by
        obtain ⟨δ, hδ, hd⟩ := hmod a (Finset.mem_insert_self a s') ε hε
        exact ⟨δ, hδ, fun n x hx y hy hxy => hd (φ' n) x hx y hy hxy⟩)
    refine ⟨φ' ∘ φ'', hφ'.comp hφ'', ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨g, hgc, hgu⟩
    · obtain ⟨g', hg'c, hg'u⟩ := hφ'i i hi'
      exact ⟨g', hg'c, hg'u.seq_tendstoUniformlyOn φ'' hφ''.tendsto_atTop⟩

/-- Uniform convergence of every coordinate of a finite-dimensional vector-valued sequence,
with a shared subsequence and a shared set, glues into joint uniform convergence in the
(sup-metric) product `ι → ℝ`. -/
theorem tendstoUniformlyOn_pi_of_forall {X ι : Type*} [Fintype ι] [Nonempty ι] {S : Set X}
    {F : ℕ → X → ι → ℝ} {g : X → ι → ℝ}
    (h : ∀ i : ι, TendstoUniformlyOn (fun n x => F n x i) (fun x => g x i) atTop S) :
    TendstoUniformlyOn F g atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h' : ∀ i ∈ (Finset.univ : Finset ι),
      ∀ᶠ n in atTop, ∀ x ∈ S, dist (g x i) (F n x i) < ε := by
    intro i _
    exact Metric.tendstoUniformlyOn_iff.mp (h i) ε hε
  rw [← Finset.eventually_all] at h'
  filter_upwards [h'] with n hn x hx
  exact (dist_pi_lt_iff hε).mpr (fun i => hn i (Finset.mem_univ i) x hx)

/-! ### From a mixed Lipschitz bound on a primitive to its a.e.-Lipschitz time-derivative -/

/-- Given `F : Vec m × ℝ → ℝ`, continuous, such that on every compact time-window `Icc c d`
there is one constant `Λ` bounding both the time-Lipschitz constant of `F(x, ·)` (each `x`) and
the "mixed" Lipschitz constant of its increments over `[τ, τ']` as a function of `x` — the
structure enjoyed by the time-primitive of a field that is bounded and Lipschitz in space,
uniformly in time on `Icc c d` — the classical (limsup-of-difference-quotients) time-derivative
`G` of `F` is Borel measurable, and for a.e. `τ` in every compact time-window it is, at every
`x`, the genuine derivative of `F(x, ·)`, again bounded and Lipschitz in `x` with the same `Λ`. -/
theorem exists_measurable_ae_hasDerivAt_of_lipschitz_mixed {m : ℕ} {F : Vec m × ℝ → ℝ}
    (hFc : Continuous F)
    (hmix : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧
      (∀ x : Vec m, LipschitzOnWith Λ.toNNReal (fun τ => F (x, τ)) (Icc c d)) ∧
      (∀ x y : Vec m, ∀ τ ∈ Icc c d, ∀ τ' ∈ Icc c d,
        |F (x, τ') - F (x, τ) - (F (y, τ') - F (y, τ))| ≤ Λ * ‖x - y‖ * |τ' - τ|)) :
    ∃ G : Vec m × ℝ → ℝ, Measurable G ∧
      ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧
        ∀ᵐ τ ∂(volume.restrict (Icc c d)),
          (∀ x : Vec m, HasDerivAt (fun τ' => F (x, τ')) (G (x, τ)) τ) ∧
          (∀ x : Vec m, |G (x, τ)| ≤ Λ) ∧
          LipschitzWith Λ.toNNReal (fun x => G (x, τ)) := by
  classical
  let dq : ℕ → Vec m × ℝ → ℝ :=
    fun k z => slope (fun τ' => F (z.1, τ')) z.2 (z.2 + 1 / ((k : ℝ) + 1))
  have hdqmeas : ∀ k, Measurable (dq k) := by
    intro k
    have h1 : Continuous (fun z : Vec m × ℝ => F (z.1, z.2 + 1 / ((k : ℝ) + 1))) :=
      hFc.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have heq : dq k = fun z => (F (z.1, z.2 + 1 / ((k : ℝ) + 1)) - F z) * ((k : ℝ) + 1) := by
      funext z
      show slope (fun τ' => F (z.1, τ')) z.2 (z.2 + 1 / ((k : ℝ) + 1)) = _
      rw [slope_def_field]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      rw [show z.2 + 1 / ((k : ℝ) + 1) - z.2 = 1 / ((k : ℝ) + 1) from by ring,
        div_div_eq_mul_div, div_one]
    rw [heq]
    exact ((h1.sub hFc).mul continuous_const).measurable
  have hGmeas : Measurable (fun z => limsup (fun k => dq k z) atTop) := Measurable.limsup hdqmeas
  set G : Vec m × ℝ → ℝ := fun z => limsup (fun k => dq k z) atTop with hGdef
  refine ⟨G, hGmeas, ?_⟩
  intro c d hcd
  obtain ⟨Λ, hΛnn, hLip, hMix⟩ := hmix (c - 1) (d + 1) (by linarith only [hcd])
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (α := Vec m)
  have hDdiff : ∀ x ∈ D, ∀ᵐ τ ∂(volume.restrict (Icc (c - 1) (d + 1))),
      DifferentiableAt ℝ (fun τ' => F (x, τ')) τ := by
    intro x _
    have hlip : LipschitzOnWith Λ.toNNReal (fun τ => F (x, τ)) (uIcc (c - 1) (d + 1)) := by
      rw [uIcc_of_le (by linarith only [hcd] : c - 1 ≤ d + 1)]; exact hLip x
    have hac := hlip.absolutelyContinuousOnInterval.ae_differentiableAt
    rw [uIcc_of_le (by linarith only [hcd] : c - 1 ≤ d + 1)] at hac
    have hac' : ∀ᵐ τ ∂(volume.restrict (Icc (c - 1) (d + 1))),
        τ ∈ Icc (c - 1) (d + 1) → DifferentiableAt ℝ (fun τ' => F (x, τ')) τ :=
      hac.filter_mono (ae_mono (Measure.restrict_le_self (μ := (volume : Measure ℝ))
        (s := Icc (c - 1) (d + 1))))
    filter_upwards [hac', ae_restrict_mem measurableSet_Icc] with τ h1 h2
    exact h1 h2
  have hDdiff' : ∀ᵐ τ ∂(volume.restrict (Icc (c - 1) (d + 1))),
      ∀ x ∈ D, DifferentiableAt ℝ (fun τ' => F (x, τ')) τ := (ae_ball_iff hDc).mpr hDdiff
  have hDdiff'' : ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      ∀ x ∈ D, DifferentiableAt ℝ (fun τ' => F (x, τ')) τ :=
    hDdiff'.filter_mono
      (ae_mono (Measure.restrict_mono (Icc_subset_Icc (by linarith only []) (by linarith only
        [])) le_rfl))
  refine ⟨Λ, hΛnn, ?_⟩
  filter_upwards [hDdiff'', ae_restrict_mem measurableSet_Icc] with τ hτdiff hτmem
  have hτmem' : τ ∈ Icc (c - 1) (d + 1) := ⟨by linarith only [hτmem.1], by linarith only [hτmem.2]⟩
  have hτnbhd : Icc (c - 1) (d + 1) ∈ 𝓝 τ :=
    Icc_mem_nhds (by linarith only [hτmem.1]) (by linarith only [hτmem.2])
  have hτnbhd' : Icc (c - 1) (d + 1) ∈ 𝓝[≠] τ := nhdsWithin_le_nhds hτnbhd
  -- The marginal slope bound, eventually as `τ' → τ` (in the punctured neighborhood filter).
  have hslopebd : ∀ x : Vec m, ∀ᶠ τ' in 𝓝[≠] τ,
      |slope (fun τ'' => F (x, τ'')) τ τ'| ≤ Λ := by
    intro x
    filter_upwards [hτnbhd', self_mem_nhdsWithin] with τ' hτ'mem hτ'ne0
    have hτ'ne : τ' ≠ τ := Set.mem_compl_singleton_iff.mp hτ'ne0
    rw [slope_def_field, abs_div]
    rw [div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hτ'ne))]
    have hd := (hLip x).dist_le_mul τ hτmem' τ' hτ'mem
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal Λ hΛnn] at hd
    rwa [abs_sub_comm (F (x, τ')) (F (x, τ)), abs_sub_comm τ' τ]
  -- The mixed bound, eventually as `τ' → τ`, comparing any two spatial points.
  have hmixbd : ∀ x y : Vec m, ∀ᶠ τ' in 𝓝[≠] τ,
      |slope (fun τ'' => F (x, τ'')) τ τ' - slope (fun τ'' => F (y, τ'')) τ τ'| ≤
        Λ * ‖x - y‖ := by
    intro x y
    filter_upwards [hτnbhd', self_mem_nhdsWithin] with τ' hτ'mem hτ'ne0
    have hτ'ne : τ' ≠ τ := Set.mem_compl_singleton_iff.mp hτ'ne0
    have hne : τ' - τ ≠ 0 := sub_ne_zero.mpr hτ'ne
    have hkey := hMix x y τ hτmem' τ' hτ'mem
    have heq : slope (fun τ'' => F (x, τ'')) τ τ' - slope (fun τ'' => F (y, τ'')) τ τ'
        = (F (x, τ') - F (x, τ) - (F (y, τ') - F (y, τ))) / (τ' - τ) := by
      rw [slope_def_field, slope_def_field]; ring
    rw [heq, abs_div, div_le_iff₀ (abs_pos.mpr hne)]
    exact hkey
  have hbdd_ge : ∀ x : Vec m, IsBoundedUnder (· ≥ ·) (𝓝[≠] τ)
      (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') :=
    fun x => ⟨-Λ, (hslopebd x).mono (fun τ' h => (abs_le.mp h).1)⟩
  have hbdd_le : ∀ x : Vec m, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') :=
    fun x => ⟨Λ, (hslopebd x).mono (fun τ' h => (abs_le.mp h).2)⟩
  have hcobdd_le : ∀ x : Vec m, IsCoboundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') :=
    fun x => (hbdd_ge x).isCoboundedUnder_le
  have hcobdd_ge : ∀ x : Vec m, IsCoboundedUnder (· ≥ ·) (𝓝[≠] τ)
      (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') :=
    fun x => (hbdd_le x).isCoboundedUnder_ge
  have hle_of_forall_le_add : ∀ a b : ℝ, (∀ ε > 0, a ≤ b + ε) → a ≤ b := by
    intro a b h
    by_contra hcon
    push Not at hcon
    linarith only [hcon, h ((a - b) / 2) (by linarith only [hcon])]
  set g : Vec m → ℝ := fun x => deriv (fun τ' => F (x, τ')) τ with hgdef
  have hgLip : ∀ x ∈ D, ∀ y ∈ D, |g x - g y| ≤ Λ * ‖x - y‖ := by
    intro x hx y hy
    have hdx : HasDerivAt (fun τ' => F (x, τ')) (g x) τ := (hτdiff x hx).hasDerivAt
    have hdy : HasDerivAt (fun τ' => F (y, τ')) (g y) τ := (hτdiff y hy).hasDerivAt
    have hsub : Tendsto (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ' -
        slope (fun τ'' => F (y, τ'')) τ τ') (𝓝[≠] τ) (𝓝 (g x - g y)) :=
      (hasDerivAt_iff_tendsto_slope.mp hdx).sub (hasDerivAt_iff_tendsto_slope.mp hdy)
    exact le_of_tendsto hsub.abs (hmixbd x y)
  have hgLipOn : LipschitzOnWith Λ.toNNReal g D := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal Λ hΛnn]
    exact hgLip x hx y hy
  obtain ⟨Ĝ, hĜLip, hĜeq⟩ := hgLipOn.extend_real
  have hĜLipR : ∀ x y : Vec m, |Ĝ x - Ĝ y| ≤ Λ * ‖x - y‖ := by
    intro x y
    have hthis := hĜLip.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal Λ hΛnn] at hthis
  have hHasDeriv : ∀ x : Vec m, HasDerivAt (fun τ' => F (x, τ')) (Ĝ x) τ := by
    intro x
    rw [hasDerivAt_iff_tendsto_slope]
    have hupper : limsup (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') (𝓝[≠] τ) ≤ Ĝ x := by
      refine hle_of_forall_le_add _ _ (fun ε hε => ?_)
      obtain ⟨x', hx'D, hx'close⟩ := Metric.mem_closure_iff.mp (hDd x) (ε / (2 * (Λ + 1)))
        (by positivity)
      have hbdd_le' : IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' + Λ * ‖x - x'‖) := by
        obtain ⟨b, hb⟩ := hbdd_le x'
        rw [Filter.eventually_map] at hb
        exact ⟨b + Λ * ‖x - x'‖, hb.mono (fun τ' h => by
          show slope (fun τ'' => F (x', τ'')) τ τ' + Λ * ‖x - x'‖ ≤ b + Λ * ‖x - x'‖
          linarith only [h])⟩
      have hstep1 : limsup (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') (𝓝[≠] τ) ≤
          limsup (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' + Λ * ‖x - x'‖) (𝓝[≠] τ) := by
        apply limsup_le_limsup _ (hcobdd_le x) hbdd_le'
        filter_upwards [hmixbd x x'] with τ' hτ'
        have := (abs_le.mp hτ').2
        linarith only [this]
      have hstep2 : limsup (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' + Λ * ‖x - x'‖)
          (𝓝[≠] τ) = g x' + Λ * ‖x - x'‖ := by
        have htend : Tendsto (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' + Λ * ‖x - x'‖)
            (𝓝[≠] τ) (𝓝 (g x' + Λ * ‖x - x'‖)) :=
          (hasDerivAt_iff_tendsto_slope.mp ((hτdiff x' hx'D).hasDerivAt)).add_const _
        exact htend.limsup_eq
      have hstep3 : g x' = Ĝ x' := hĜeq hx'D
      have hΛnn' : (0:ℝ) < 2 * (Λ + 1) := by linarith only [hΛnn]
      have hnormlt : ‖x - x'‖ * (2 * (Λ + 1)) < ε := by
        rw [← dist_eq_norm]; exact (lt_div_iff₀ hΛnn').mp hx'close
      calc limsup (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') (𝓝[≠] τ)
          ≤ g x' + Λ * ‖x - x'‖ := by rw [← hstep2]; exact hstep1
        _ = Ĝ x' + Λ * ‖x - x'‖ := by rw [hstep3]
        _ ≤ (Ĝ x + Λ * ‖x - x'‖) + Λ * ‖x - x'‖ := by
              have := (abs_le.mp (hĜLipR x' x)).2
              rw [norm_sub_rev x' x] at this
              linarith only [this]
        _ = Ĝ x + 2 * Λ * ‖x - x'‖ := by ring
        _ ≤ Ĝ x + ε := by nlinarith only [hnormlt, hΛnn, norm_nonneg (x - x')]
    have hlower : Ĝ x ≤ liminf (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') (𝓝[≠] τ) := by
      have haux : ∀ ε > 0,
          liminf (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') (𝓝[≠] τ) + ε ≥ Ĝ x := by
        intro ε hε
        obtain ⟨x', hx'D, hx'close⟩ := Metric.mem_closure_iff.mp (hDd x) (ε / (2 * (Λ + 1)))
          (by positivity)
        have hbdd_ge' : IsBoundedUnder (· ≥ ·) (𝓝[≠] τ)
            (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' - Λ * ‖x - x'‖) := by
          obtain ⟨b, hb⟩ := hbdd_ge x'
          rw [Filter.eventually_map] at hb
          exact ⟨b - Λ * ‖x - x'‖, hb.mono (fun τ' h => by
            show slope (fun τ'' => F (x', τ'')) τ τ' - Λ * ‖x - x'‖ ≥ b - Λ * ‖x - x'‖
            linarith only [h])⟩
        have hstep1 : liminf (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' - Λ * ‖x - x'‖)
            (𝓝[≠] τ) ≤ liminf (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') (𝓝[≠] τ) := by
          apply liminf_le_liminf _ hbdd_ge' (hcobdd_ge x)
          filter_upwards [hmixbd x x'] with τ' hτ'
          have := (abs_le.mp hτ').1
          linarith only [this]
        have hstep2 : liminf (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' - Λ * ‖x - x'‖)
            (𝓝[≠] τ) = g x' - Λ * ‖x - x'‖ := by
          have htend : Tendsto (fun τ' => slope (fun τ'' => F (x', τ'')) τ τ' - Λ * ‖x - x'‖)
              (𝓝[≠] τ) (𝓝 (g x' - Λ * ‖x - x'‖)) :=
            (hasDerivAt_iff_tendsto_slope.mp ((hτdiff x' hx'D).hasDerivAt)).sub_const _
          exact htend.liminf_eq
        have hstep3 : g x' = Ĝ x' := hĜeq hx'D
        have hΛnn' : (0:ℝ) < 2 * (Λ + 1) := by linarith only [hΛnn]
        have hnormlt : ‖x - x'‖ * (2 * (Λ + 1)) < ε := by
          rw [← dist_eq_norm]; exact (lt_div_iff₀ hΛnn').mp hx'close
        have h4 := (abs_le.mp (hĜLipR x' x)).1
        rw [norm_sub_rev x' x] at h4
        have hcalc : g x' - Λ * ‖x - x'‖ ≤ liminf
            (fun τ' => slope (fun τ'' => F (x, τ'')) τ τ') (𝓝[≠] τ) := by
          rw [← hstep2]; exact hstep1
        nlinarith only [hcalc, h4, hnormlt, hΛnn, hstep3, norm_nonneg (x - x')]
      exact hle_of_forall_le_add _ _ (fun ε hε => by linarith only [haux ε hε])
    exact tendsto_of_le_liminf_of_limsup_le hlower hupper (hbdd_le x) (hbdd_ge x)
  have hĜbdd : ∀ x : Vec m, |Ĝ x| ≤ Λ :=
    fun x => le_of_tendsto (hasDerivAt_iff_tendsto_slope.mp (hHasDeriv x)).abs (hslopebd x)
  have htau_tendsto : Tendsto (fun k : ℕ => τ + 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] τ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)), ?_⟩
    refine Eventually.of_forall fun k => ?_
    have hk1 : (1 : ℝ) / ((k : ℝ) + 1) ≠ 0 := by positivity
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcontra
    exact hk1 (by linarith only [hcontra])
  have hGeq : ∀ x : Vec m, G (x, τ) = Ĝ x := by
    intro x
    have htend : Tendsto (fun k => dq k (x, τ)) atTop (𝓝 (Ĝ x)) :=
      (hasDerivAt_iff_tendsto_slope.mp (hHasDeriv x)).comp htau_tendsto
    have hGeq' : limsup (fun k => dq k (x, τ)) atTop = Ĝ x := htend.limsup_eq
    show limsup (fun k => dq k (x, τ)) atTop = Ĝ x
    exact hGeq'
  refine ⟨?_, ?_, ?_⟩
  · intro x; rw [hGeq x]; exact hHasDeriv x
  · intro x; rw [hGeq x]; exact hĜbdd x
  · have : (fun x => G (x, τ)) = Ĝ := funext hGeq
    rw [this]; exact hĜLip

/-! ### Time-clamped primitives of a globally space-Lipschitz, space-time-bounded family -/

/-- `min` is `1`-Lipschitz in its first argument. -/
theorem abs_min_sub_min_le (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have h := lipschitzWith_min.dist_le_mul (a, c) (b, c)
  simp only [Prod.dist_eq, Real.dist_eq, dist_self, NNReal.coe_one, one_mul,
    max_eq_left (abs_nonneg (a - b))] at h
  exact h

/-- Given `m + 1` families of scalar fields `φ i n` (indexed by `Option (Fin m)`, standing for
the `m` components of a drift plus its divergence) that are, eventually in `n`, globally
`Λ`-Lipschitz in space and `Λ`-bounded on every time-window `J` compact in `Iic T` — the
structure `hbd` of `eq:aniso:comparison:drift` — the time-`T`-clamped primitives
`z ↦ ∫_{T-1}^{min(z.2,T)} φ i n (z.1, s) ds` converge, along one common subsequence, locally
uniformly to continuous limits `p i`, each of which has a Borel, a.e.-Lipschitz-and-bounded
time-derivative on every compact time-window (via
`exists_measurable_ae_hasDerivAt_of_lipschitz_mixed`). -/
theorem exists_subseq_primitives_ae_hasDerivAt {m : ℕ} {T : ℝ}
    (φ : Option (Fin m) → ℕ → Vec m × ℝ → ℝ)
    (hcontJ : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ∀ i : Option (Fin m), ContinuousOn (φ i n) K)
    (hbd : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ i : Option (Fin m), ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec m) r,
        ∀ y ∈ Metric.closedBall (0 : Vec m) r,
          |φ i n (x, τ)| ≤ Λ ∧ |φ i n (x, τ) - φ i n (y, τ)| ≤ Λ * ‖x - y‖) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ p : Option (Fin m) → Vec m × ℝ → ℝ,
      (∀ i, Continuous (p i)) ∧
      (∀ K : Set (Vec m × ℝ), IsCompact K → ∀ i,
        TendstoUniformlyOn (fun n z => ∫ s in (T - 1)..(min z.2 T), φ i (ψ n) (z.1, s))
          (p i) atTop K) ∧
      ∀ i, ∃ B : Vec m × ℝ → ℝ, Measurable B ∧
        ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
          (∀ x, HasDerivAt (fun τ' => p i (x, τ')) (B (x, τ)) τ) ∧ (∀ x, |B (x, τ)| ≤ Λ) ∧
          LipschitzWith Λ.toNNReal (fun x => B (x, τ)) := by
  classical
  have hsliceOf : ∀ (S : Set (Vec m × ℝ)) (a b : ℝ), ∀ i : Option (Fin m), ∀ n : ℕ,
      ContinuousOn (φ i n) S → ∀ x : Vec m, (∀ s ∈ Icc a b, (x, s) ∈ S) →
      ContinuousOn (fun s => φ i n (x, s)) (Icc a b) := by
    intro S a b i n hCn x hx
    exact hCn.comp (continuous_const.prodMk continuous_id).continuousOn hx
  set pn : Option (Fin m) → ℕ → Vec m × ℝ → ℝ :=
    fun i n z => ∫ s in (T - 1)..(min z.2 T), φ i n (z.1, s) with hpndef
  set Bx : ℕ → Set (Vec m × ℝ) :=
    fun k => Metric.closedBall (0 : Vec m) (k : ℝ) ×ˢ Icc (-(k : ℝ) - |T| - 2) ((k : ℝ) + |T| + 2)
    with hBxdef
  have hBxcpt : ∀ k, IsCompact (Bx k) :=
    fun k => (isCompact_closedBall _ _).prod isCompact_Icc
  have hTbound : ∀ k : ℕ, -(k : ℝ) - |T| - 2 ≤ T := fun k => by
    nlinarith only [neg_abs_le T, Nat.cast_nonneg (α := ℝ) k]
  have hTbound1 : ∀ k : ℕ, -(k : ℝ) - |T| - 2 ≤ T - 1 := fun k => by
    nlinarith only [neg_abs_le T, Nat.cast_nonneg (α := ℝ) k]
  have hclamp : ∀ k : ℕ, ∀ z : Vec m × ℝ, z ∈ Bx k →
      min z.2 T ∈ Icc (-(k : ℝ) - |T| - 2) T :=
    fun k z hz => ⟨le_min hz.2.1 (hTbound k), min_le_right _ _⟩
  -- `Bx k` clipped to time `≤ T`: compact, and inside `univ ×ˢ Iic T`, so `hcontJ` applies.
  set BxT : ℕ → Set (Vec m × ℝ) :=
    fun k => Metric.closedBall (0 : Vec m) (k : ℝ) ×ˢ Icc (-(k : ℝ) - |T| - 2) T with hBxTdef
  have hBxTcpt : ∀ k : ℕ, IsCompact (BxT k) :=
    fun k => (isCompact_closedBall _ _).prod isCompact_Icc
  have hBxTsub : ∀ k : ℕ, BxT k ⊆ univ ×ˢ Iic T := fun k z hz => ⟨mem_univ _, hz.2.2⟩
  -- The eventual joint (space-time) Lipschitz bound of `pn` on `Bx k`.
  have hkey : ∀ k : ℕ, ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᶠ n in atTop, ∀ i : Option (Fin m),
      ∀ z1 ∈ Bx k, ∀ z2 ∈ Bx k, |pn i n z1 - pn i n z2| ≤ Λ * dist z1 z2 := by
    intro k
    obtain ⟨Λ, hΛnn, hΛr⟩ := hbd (Icc (-(k : ℝ) - |T| - 2) T) isCompact_Icc (fun τ hτ => hτ.2)
    have hΛ := hΛr (k : ℝ)
    have hCk := hcontJ (BxT k) (hBxTcpt k) (hBxTsub k)
    refine ⟨Λ * (((k : ℝ) + 2 * |T| + 3) + 1), by positivity, ?_⟩
    filter_upwards [hΛ, hCk] with n hn hCn i z1 hz1 z2 hz2
    have hm1 := hclamp k z1 hz1
    have hm2 := hclamp k z2 hz2
    have hT1mem : (T - 1) ∈ Icc (-(k : ℝ) - |T| - 2) T := ⟨hTbound1 k, by linarith only []⟩
    have hcontz1 : ContinuousOn (fun s => φ i n (z1.1, s)) (Icc (-(k : ℝ) - |T| - 2) T) :=
      hsliceOf (BxT k) _ _ i n (hCn i) z1.1 (fun s hs => ⟨hz1.1, hs⟩)
    have hcontz2 : ContinuousOn (fun s => φ i n (z2.1, s)) (Icc (-(k : ℝ) - |T| - 2) T) :=
      hsliceOf (BxT k) _ _ i n (hCn i) z2.1 (fun s hs => ⟨hz2.1, hs⟩)
    have hA : IntervalIntegrable (fun s => φ i n (z1.1, s)) volume (T - 1) (min z2.2 T) :=
      (hcontz1.mono (uIcc_subset_Icc hT1mem hm2)).intervalIntegrable
    have hB : IntervalIntegrable (fun s => φ i n (z2.1, s)) volume (T - 1) (min z2.2 T) :=
      (hcontz2.mono (uIcc_subset_Icc hT1mem hm2)).intervalIntegrable
    have hC : IntervalIntegrable (fun s => φ i n (z1.1, s)) volume (min z2.2 T) (min z1.2 T) :=
      (hcontz1.mono (uIcc_subset_Icc hm2 hm1)).intervalIntegrable
    have hsplit : pn i n z1 - pn i n z2 =
        (∫ s in (min z2.2 T)..(min z1.2 T), φ i n (z1.1, s)) +
          ∫ s in (T - 1)..(min z2.2 T), (φ i n (z1.1, s) - φ i n (z2.1, s)) := by
      show (∫ s in (T - 1)..(min z1.2 T), φ i n (z1.1, s)) -
          ∫ s in (T - 1)..(min z2.2 T), φ i n (z2.1, s) = _
      have hsub : (∫ s in (T - 1)..(min z2.2 T), (φ i n (z1.1, s) - φ i n (z2.1, s)))
          = (∫ s in (T - 1)..(min z2.2 T), φ i n (z1.1, s)) -
            ∫ s in (T - 1)..(min z2.2 T), φ i n (z2.1, s) :=
        intervalIntegral.integral_sub hA hB
      have hadj : (∫ s in (T - 1)..(min z2.2 T), φ i n (z1.1, s)) +
          ∫ s in (min z2.2 T)..(min z1.2 T), φ i n (z1.1, s)
          = ∫ s in (T - 1)..(min z1.2 T), φ i n (z1.1, s) :=
        intervalIntegral.integral_add_adjacent_intervals hA hC
      rw [hsub]
      linarith only [hadj]
    rw [hsplit]
    have hb1 : |∫ s in (min z2.2 T)..(min z1.2 T), φ i n (z1.1, s)| ≤ Λ * |min z1.2 T - min z2.2
      T| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := min z2.2 T) (b := min z1.2 T) (f := fun s => φ i n (z1.1, s)) (C := Λ)
        (fun s hs => by
          have hsmem : s ∈ Icc (-(k : ℝ) - |T| - 2) T := by
            rcases le_total (min z2.2 T) (min z1.2 T) with hle | hle
            · rw [Set.uIoc_of_le hle] at hs
              exact ⟨le_trans hm2.1 hs.1.le, le_trans hs.2 hm1.2⟩
            · rw [Set.uIoc_of_ge hle] at hs
              exact ⟨le_trans hm1.1 hs.1.le, le_trans hs.2 hm2.2⟩
          rw [Real.norm_eq_abs]
          exact (hn i s hsmem z1.1 hz1.1 z1.1 hz1.1).1)
      rwa [Real.norm_eq_abs] at this
    have hb2 : |∫ s in (T - 1)..(min z2.2 T), (φ i n (z1.1, s) - φ i n (z2.1, s))| ≤
        Λ * ‖z1.1 - z2.1‖ * |min z2.2 T - (T - 1)| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (T - 1)) (b := min z2.2 T) (f := fun s => φ i n (z1.1, s) - φ i n (z2.1, s))
        (C := Λ * ‖z1.1 - z2.1‖)
        (fun s hs => by
          have hsmem : s ∈ Icc (-(k : ℝ) - |T| - 2) T := by
            rcases le_total ((T - 1)) (min z2.2 T) with hle | hle
            · rw [Set.uIoc_of_le hle] at hs
              exact ⟨le_trans (hTbound1 k) hs.1.le, le_trans hs.2 hm2.2⟩
            · rw [Set.uIoc_of_ge hle] at hs
              exact ⟨le_trans hm2.1 hs.1.le, le_trans hs.2 (by linarith only [])⟩
          rw [Real.norm_eq_abs]
          exact (hn i s hsmem z1.1 hz1.1 z2.1 hz2.1).2)
      rwa [Real.norm_eq_abs] at this
    have hd1 : |min z1.2 T - min z2.2 T| ≤ dist z1 z2 := by
      have h1 := abs_min_sub_min_le z1.2 z2.2 T
      have h2 : |z1.2 - z2.2| ≤ dist z1 z2 := by
        rw [Prod.dist_eq]; exact le_trans (le_max_right _ _) (le_of_eq (by rw [Real.dist_eq]))
      linarith only [h1, h2]
    have hd2 : ‖z1.1 - z2.1‖ ≤ dist z1 z2 := by
      rw [Prod.dist_eq]
      exact le_trans (le_max_left _ _) (le_of_eq (by rw [dist_eq_norm]))
    have hd3 : |min z2.2 T - (T - 1)| ≤ (k : ℝ) + 2 * |T| + 3 := by
      have := hclamp k z2 hz2
      have hlow := hTbound1 k
      rw [abs_le]
      constructor <;> nlinarith only [this.1, this.2, abs_nonneg T, le_abs_self T, hlow]
    calc |(∫ s in (min z2.2 T)..(min z1.2 T), φ i n (z1.1, s)) +
          ∫ s in (T - 1)..(min z2.2 T), (φ i n (z1.1, s) - φ i n (z2.1, s))|
        ≤ |∫ s in (min z2.2 T)..(min z1.2 T), φ i n (z1.1, s)| +
            |∫ s in (T - 1)..(min z2.2 T), (φ i n (z1.1, s) - φ i n (z2.1, s))| := by
              rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
              exact norm_add_le _ _
      _ ≤ Λ * |min z1.2 T - min z2.2 T| +
            Λ * ‖z1.1 - z2.1‖ * |min z2.2 T - (T - 1)| := add_le_add hb1 hb2
      _ ≤ Λ * dist z1 z2 + Λ * dist z1 z2 * ((k : ℝ) + 2 * |T| + 3) := by
            gcongr
      _ = Λ * (((k : ℝ) + 2 * |T| + 3) + 1) * dist z1 z2 := by ring
  -- A reference point in `Bx k`, where every `pn i n` vanishes, and a diameter bound.
  have hz0mem : ∀ k : ℕ, ((0 : Vec m), T - 1) ∈ Bx k := by
    intro k
    refine ⟨Metric.mem_closedBall_self (by positivity : (0:ℝ) ≤ (k:ℝ)), ?_, ?_⟩
    · exact hTbound1 k
    · nlinarith only [le_abs_self T, Nat.cast_nonneg (α := ℝ) k]
  have hpnz0 : ∀ (i : Option (Fin m)) (n : ℕ), pn i n ((0 : Vec m), T - 1) = 0 := by
    intro i n
    show (∫ s in (T - 1)..(min (T - 1) T), φ i n ((0 : Vec m), s)) = 0
    rw [min_eq_left (by linarith only [] : T - 1 ≤ T), intervalIntegral.integral_same]
  have hdiam : ∀ k : ℕ, ∀ z ∈ Bx k, dist z ((0 : Vec m), T - 1) ≤ 2 * (k : ℝ) + 2 * |T| + 4 := by
    intro k z hz
    rw [Prod.dist_eq]
    refine max_le ?_ ?_
    · show dist z.1 (0 : Vec m) ≤ 2 * (k : ℝ) + 2 * |T| + 4
      have := hz.1
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
      rw [dist_eq_norm, sub_zero]
      nlinarith only [this, Nat.cast_nonneg (α := ℝ) k, abs_nonneg T]
    · show dist z.2 (T - 1) ≤ 2 * (k : ℝ) + 2 * |T| + 4
      rw [Real.dist_eq]
      have h1 := hz.2.1
      have h2 := hz.2.2
      rw [abs_le]; constructor <;>
        nlinarith only [h1, h2, abs_nonneg T, le_abs_self T, neg_abs_le T, Nat.cast_nonneg (α :=
          ℝ) k]
  -- The eventual bound of `pn` on `Bx k`, from the Lipschitz bound and the reference point.
  have hboundk : ∀ k : ℕ, ∃ M : ℝ, ∀ᶠ n in atTop, ∀ i : Option (Fin m),
      ∀ z ∈ Bx k, |pn i n z| ≤ M := by
    intro k
    obtain ⟨Λk, hΛknn, hΛkev⟩ := hkey k
    refine ⟨Λk * (2 * (k : ℝ) + 2 * |T| + 4), ?_⟩
    filter_upwards [hΛkev] with n hn i z hz
    have := hn i z hz ((0 : Vec m), T - 1) (hz0mem k)
    rw [hpnz0 i n, sub_zero] at this
    calc |pn i n z| ≤ Λk * dist z ((0 : Vec m), T - 1) := this
      _ ≤ Λk * (2 * (k : ℝ) + 2 * |T| + 4) := by
          gcongr
          exact hdiam k z hz
  -- Combine the eventual bound and Lipschitz constant into a shared modulus for `pn`.
  have hmodk : ∀ k : ℕ, ∃ M : ℝ, ∀ᶠ n in atTop, (∀ i : Option (Fin m), ∀ z ∈ Bx k, |pn i n z| ≤ M) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ i : Option (Fin m), ∀ z1 ∈ Bx k, ∀ z2 ∈ Bx k, dist z1 z2 < δ →
        |pn i n z1 - pn i n z2| ≤ ε := by
    intro k
    obtain ⟨M, hM⟩ := hboundk k
    obtain ⟨Λk, hΛknn, hΛkev⟩ := hkey k
    refine ⟨M, ?_⟩
    filter_upwards [hM, hΛkev] with n hMn hΛn
    refine ⟨hMn, fun ε hε => ⟨ε / (Λk + 1), by positivity, fun i z1 hz1 z2 hz2 hd => ?_⟩⟩
    have hb := hΛn i z1 hz1 z2 hz2
    have hΛpos : (0:ℝ) < Λk + 1 := by linarith only [hΛknn]
    have : Λk * dist z1 z2 ≤ Λk * (ε / (Λk + 1)) :=
      mul_le_mul_of_nonneg_left hd.le hΛknn
    have hfin : Λk * (ε / (Λk + 1)) ≤ ε := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ hΛpos]
      nlinarith only [hε, hΛpos]
    linarith only [hb, this, hfin]
  have hLtoM : ∀ Λ' : ℝ, 0 ≤ Λ' → ∀ ε : ℝ, 0 < ε → ∀ d : ℝ, d < ε / (Λ' + 1) → 0 ≤ d →
      Λ' * d ≤ ε := by
    intro Λ' hΛ'nn ε hε d hd hdnn
    have h1 : Λ' * d ≤ Λ' * (ε / (Λ' + 1)) := mul_le_mul_of_nonneg_left hd.le hΛ'nn
    have h2 : Λ' * (ε / (Λ' + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith only [hΛ'nn] : (0:ℝ) < Λ' + 1)]
      nlinarith only [hε, hΛ'nn]
    linarith only [h1, h2]
  have hshift : ∀ (P : ℕ → Prop), (∀ᶠ n in atTop, P n) → ∀ (g : ℕ → ℕ), StrictMono g →
      ∃ S : ℕ, ∀ j, P (g (S + j)) := by
    intro P hP g hg
    obtain ⟨N, hN⟩ := eventually_atTop.mp hP
    obtain ⟨S, hS⟩ := eventually_atTop.mp (hg.tendsto_atTop.eventually_ge_atTop N)
    exact ⟨S, fun j => hN _ (hS (S + j) (by omega))⟩
  -- The refinement step of the box-diagonal extraction.
  have hstep : ∀ (k : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : Vec m × ℝ → (Option (Fin m) → ℝ),
        TendstoUniformlyOn (fun n z => fun i => pn i (g (g' n)) z) w atTop (Bx k) := by
    intro k g hg
    obtain ⟨M, hM⟩ := hboundk k
    obtain ⟨Λk, hΛknn, hΛkev⟩ := hkey k
    obtain ⟨S, hS⟩ := hshift _ (hM.and hΛkev) g hg
    obtain ⟨φAA, hφAA, hcombined⟩ := exists_subseq_forall_tendstoUniformlyOn_of_modulus_finset
      (Bx k) (hBxcpt k) (fun i n => pn i (g (S + n))) M Finset.univ
      (fun i _ n z hz => (hS n).1 i z hz)
      (fun i _ ε hε => ⟨ε / (Λk + 1), by positivity, fun n z hz z' hz' hd => by
        have hb := (hS n).2 i z hz z' hz'
        exact le_trans hb (hLtoM Λk hΛknn ε hε (dist z z') hd dist_nonneg)⟩)
    refine ⟨fun j => S + φAA j, (strictMono_id.const_add S).comp hφAA, ?_⟩
    refine ⟨fun z i => (hcombined i (Finset.mem_univ i)).choose z, ?_⟩
    exact tendstoUniformlyOn_pi_of_forall
      (fun i => (hcombined i (Finset.mem_univ i)).choose_spec.2)
  obtain ⟨ψ, hψ, w, hw⟩ := exists_subseq_tendstoUniformlyOn_forall_of_subseq Bx
    (fun n z i => pn i n z) hstep
  set p : Option (Fin m) → Vec m × ℝ → ℝ := fun i z => w z i with hpdef
  -- Continuity of `pn i n` on `Bx k`, eventually in `n`, derived directly from `hkey`'s
  -- Lipschitz bound (so it needs no joint continuity of `φ`).
  have hpnLipOn : ∀ k : ℕ, ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᶠ n in atTop, ∀ i : Option (Fin m),
      LipschitzOnWith Λ.toNNReal (fun z => pn i n z) (Bx k) := by
    intro k
    obtain ⟨Λ, hΛnn, hΛkev⟩ := hkey k
    refine ⟨Λ, hΛnn, ?_⟩
    filter_upwards [hΛkev] with n hn i
    refine LipschitzOnWith.of_dist_le_mul (fun z1 hz1 z2 hz2 => ?_)
    rw [Real.dist_eq, Real.coe_toNNReal Λ hΛnn]
    exact hn i z1 hz1 z2 hz2
  have hpcont : ∀ i, Continuous (p i) := by
    intro i
    refine continuous_iff_continuousAt.mpr fun z => ?_
    set k : ℕ := ⌈‖z.1‖⌉₊ + ⌈|z.2|⌉₊ + ⌈|T|⌉₊ + 10 with hkdef
    have hzk : Bx k ∈ 𝓝 z := by
      have h1 : Metric.ball (0 : Vec m) (k : ℝ) ×ˢ Ioo (-(k : ℝ) - |T| - 2) ((k : ℝ) + |T| + 2)
          ∈ 𝓝 z := by
        refine IsOpen.mem_nhds (Metric.isOpen_ball.prod isOpen_Ioo) ⟨?_, ?_, ?_⟩
        · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
          have : ‖z.1‖ < (⌈‖z.1‖⌉₊ : ℝ) + 1 := by
            calc ‖z.1‖ ≤ (⌈‖z.1‖⌉₊ : ℝ) := Nat.le_ceil _
              _ < (⌈‖z.1‖⌉₊ : ℝ) + 1 := by linarith only []
          push_cast [hkdef]
          nlinarith only [this, Nat.le_ceil |z.2|, Nat.le_ceil |T|]
        · have h2 : -|z.2| ≤ z.2 := neg_abs_le z.2
          have h3 : (|z.2| : ℝ) ≤ (⌈|z.2|⌉₊ : ℝ) := Nat.le_ceil _
          push_cast [hkdef]
          nlinarith only [h2, h3, Nat.cast_nonneg (α := ℝ) ⌈‖z.1‖⌉₊, Nat.cast_nonneg (α := ℝ)
            ⌈|T|⌉₊, abs_nonneg T]
        · have h2 : z.2 ≤ |z.2| := le_abs_self z.2
          have h3 : (|z.2| : ℝ) ≤ (⌈|z.2|⌉₊ : ℝ) := Nat.le_ceil _
          push_cast [hkdef]
          nlinarith only [h2, h3, Nat.cast_nonneg (α := ℝ) ⌈‖z.1‖⌉₊, Nat.cast_nonneg (α := ℝ)
            ⌈|T|⌉₊, abs_nonneg T]
      refine mem_of_superset h1 ?_
      rintro ⟨x, τ⟩ ⟨hx, hτ⟩
      exact ⟨Metric.ball_subset_closedBall hx, hτ.1.le, hτ.2.le⟩
    obtain ⟨Λk', hΛk'nn, hΛk'ev⟩ := hpnLipOn k
    have hCfreq : ∃ᶠ n in atTop, ContinuousOn (fun z i => pn i (ψ n) z) (Bx k) :=
      (hψ.tendsto_atTop.eventually hΛk'ev).frequently.mono
        (fun n hn => continuousOn_pi' (fun i => (hn i).continuousOn))
    have hcontOn : ContinuousOn w (Bx k) := (hw k).continuousOn hCfreq
    exact ((continuous_apply i).continuousOn.comp hcontOn (mapsTo_univ _ _)).continuousAt hzk
  -- The time-only Lipschitz bound on `pn`, from `hbd`'s boundedness clause, restricted to a
  -- spatial ball of radius `r` (matching `hbd`'s own space-restricted shape).
  have htimeLipn : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ i : Option (Fin m), ∀ x ∈ Metric.closedBall (0 : Vec m) r, ∀ τ ∈ Icc c d, ∀ τ' ∈ Icc c d,
        |pn i n (x, τ') - pn i n (x, τ)| ≤ Λ * |τ' - τ| := by
    intro c d hcd
    obtain ⟨Λ, hΛnn, hΛr⟩ := hbd (Icc (min c (T - 1)) T) isCompact_Icc (fun τ hτ => hτ.2)
    refine ⟨Λ, hΛnn, fun r => ?_⟩
    have hΛ := hΛr r
    have hCr := hcontJ (Metric.closedBall (0 : Vec m) r ×ˢ Icc (min c (T - 1)) T)
      ((isCompact_closedBall _ _).prod isCompact_Icc) (fun z hz => ⟨mem_univ _, hz.2.2⟩)
    filter_upwards [hΛ, hCr] with n hn hCn i x hx τ hτ τ' hτ'
    have hcontx : ContinuousOn (fun s => φ i n (x, s)) (Icc (min c (T - 1)) T) :=
      hsliceOf (Metric.closedBall (0 : Vec m) r ×ˢ Icc (min c (T - 1)) T) _ _ i n (hCn i) x
        (fun s hs => ⟨hx, hs⟩)
    have hT1mem : (T - 1) ∈ Icc (min c (T - 1)) T := ⟨min_le_right _ _, by linarith only []⟩
    have hmemτ : min τ T ∈ Icc (min c (T - 1)) T :=
      ⟨min_le_min hτ.1 (by linarith only [] : (T : ℝ) - 1 ≤ T), min_le_right _ _⟩
    have hmemτ' : min τ' T ∈ Icc (min c (T - 1)) T :=
      ⟨min_le_min hτ'.1 (by linarith only [] : (T : ℝ) - 1 ≤ T), min_le_right _ _⟩
    have hA : IntervalIntegrable (fun s => φ i n (x, s)) volume (T - 1) (min τ T) :=
      (hcontx.mono (uIcc_subset_Icc hT1mem hmemτ)).intervalIntegrable
    have hC : IntervalIntegrable (fun s => φ i n (x, s)) volume (min τ T) (min τ' T) :=
      (hcontx.mono (uIcc_subset_Icc hmemτ hmemτ')).intervalIntegrable
    have hspx : pn i n (x, τ') - pn i n (x, τ) = ∫ s in (min τ T)..(min τ' T), φ i n (x, s) := by
      show (∫ s in (T - 1)..(min τ' T), φ i n (x, s)) -
          ∫ s in (T - 1)..(min τ T), φ i n (x, s) = _
      have hB : IntervalIntegrable (fun s => φ i n (x, s)) volume (T - 1) (min τ' T) :=
        (hcontx.mono (uIcc_subset_Icc hT1mem hmemτ')).intervalIntegrable
      have hadj : (∫ s in (T - 1)..(min τ T), φ i n (x, s)) +
          ∫ s in (min τ T)..(min τ' T), φ i n (x, s)
          = ∫ s in (T - 1)..(min τ' T), φ i n (x, s) :=
        intervalIntegral.integral_add_adjacent_intervals hA hC
      linarith only [hadj]
    rw [hspx]
    have hbound : |∫ s in (min τ T)..(min τ' T), φ i n (x, s)| ≤ Λ * |min τ' T - min τ T| := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := min τ T) (b := min τ' T) (f := fun s => φ i n (x, s)) (C := Λ)
        (fun s hs => by
          have hsmem : s ∈ Icc (min c (T - 1)) T := by
            rcases le_total (min τ T) (min τ' T) with hle | hle
            · rw [Set.uIoc_of_le hle] at hs
              exact ⟨le_trans hmemτ.1 hs.1.le, le_trans hs.2 hmemτ'.2⟩
            · rw [Set.uIoc_of_ge hle] at hs
              exact ⟨le_trans hmemτ'.1 hs.1.le, le_trans hs.2 hmemτ.2⟩
          rw [Real.norm_eq_abs]
          exact (hn i s hsmem x hx x hx).1)
      rwa [Real.norm_eq_abs] at hle
    calc |∫ s in (min τ T)..(min τ' T), φ i n (x, s)| ≤ Λ * |min τ' T - min τ T| := hbound
      _ ≤ Λ * |τ' - τ| := mul_le_mul_of_nonneg_left (abs_min_sub_min_le τ' τ T) hΛnn
  -- The mixed (double-difference) Lipschitz bound on `pn`, from `hbd`'s space-Lipschitz clause,
  -- restricted to a spatial ball of radius `r`.
  have hmixedn : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ i : Option (Fin m), ∀ x ∈ Metric.closedBall (0 : Vec m) r,
        ∀ y ∈ Metric.closedBall (0 : Vec m) r, ∀ τ ∈ Icc c d, ∀ τ' ∈ Icc c d,
          |pn i n (x, τ') - pn i n (x, τ) - (pn i n (y, τ') - pn i n (y, τ))| ≤
            Λ * ‖x - y‖ * |τ' - τ| := by
    intro c d hcd
    obtain ⟨Λ, hΛnn, hΛr⟩ := hbd (Icc (min c (T - 1)) T) isCompact_Icc (fun τ hτ => hτ.2)
    refine ⟨Λ, hΛnn, fun r => ?_⟩
    have hΛ := hΛr r
    have hCr := hcontJ (Metric.closedBall (0 : Vec m) r ×ˢ Icc (min c (T - 1)) T)
      ((isCompact_closedBall _ _).prod isCompact_Icc) (fun z hz => ⟨mem_univ _, hz.2.2⟩)
    filter_upwards [hΛ, hCr] with n hn hCn i x hx y hy τ hτ τ' hτ'
    have hcontx : ContinuousOn (fun s => φ i n (x, s)) (Icc (min c (T - 1)) T) :=
      hsliceOf (Metric.closedBall (0 : Vec m) r ×ˢ Icc (min c (T - 1)) T) _ _ i n (hCn i) x
        (fun s hs => ⟨hx, hs⟩)
    have hconty : ContinuousOn (fun s => φ i n (y, s)) (Icc (min c (T - 1)) T) :=
      hsliceOf (Metric.closedBall (0 : Vec m) r ×ˢ Icc (min c (T - 1)) T) _ _ i n (hCn i) y
        (fun s hs => ⟨hy, hs⟩)
    have hT1mem : (T - 1) ∈ Icc (min c (T - 1)) T := ⟨min_le_right _ _, by linarith only []⟩
    have hmemτ : min τ T ∈ Icc (min c (T - 1)) T :=
      ⟨min_le_min hτ.1 (by linarith only [] : (T : ℝ) - 1 ≤ T), min_le_right _ _⟩
    have hmemτ' : min τ' T ∈ Icc (min c (T - 1)) T :=
      ⟨min_le_min hτ'.1 (by linarith only [] : (T : ℝ) - 1 ≤ T), min_le_right _ _⟩
    have hAx : IntervalIntegrable (fun s => φ i n (x, s)) volume (T - 1) (min τ T) :=
      (hcontx.mono (uIcc_subset_Icc hT1mem hmemτ)).intervalIntegrable
    have hBx : IntervalIntegrable (fun s => φ i n (x, s)) volume (T - 1) (min τ' T) :=
      (hcontx.mono (uIcc_subset_Icc hT1mem hmemτ')).intervalIntegrable
    have hCx : IntervalIntegrable (fun s => φ i n (x, s)) volume (min τ T) (min τ' T) :=
      (hcontx.mono (uIcc_subset_Icc hmemτ hmemτ')).intervalIntegrable
    have hAy : IntervalIntegrable (fun s => φ i n (y, s)) volume (T - 1) (min τ T) :=
      (hconty.mono (uIcc_subset_Icc hT1mem hmemτ)).intervalIntegrable
    have hBy : IntervalIntegrable (fun s => φ i n (y, s)) volume (T - 1) (min τ' T) :=
      (hconty.mono (uIcc_subset_Icc hT1mem hmemτ')).intervalIntegrable
    have hCy : IntervalIntegrable (fun s => φ i n (y, s)) volume (min τ T) (min τ' T) :=
      (hconty.mono (uIcc_subset_Icc hmemτ hmemτ')).intervalIntegrable
    have hspx : pn i n (x, τ') - pn i n (x, τ) = ∫ s in (min τ T)..(min τ' T), φ i n (x, s) := by
      show (∫ s in (T - 1)..(min τ' T), φ i n (x, s)) -
          ∫ s in (T - 1)..(min τ T), φ i n (x, s) = _
      have hadj : (∫ s in (T - 1)..(min τ T), φ i n (x, s)) +
          ∫ s in (min τ T)..(min τ' T), φ i n (x, s)
          = ∫ s in (T - 1)..(min τ' T), φ i n (x, s) :=
        intervalIntegral.integral_add_adjacent_intervals hAx hCx
      linarith only [hadj]
    have hspy : pn i n (y, τ') - pn i n (y, τ) = ∫ s in (min τ T)..(min τ' T), φ i n (y, s) := by
      show (∫ s in (T - 1)..(min τ' T), φ i n (y, s)) -
          ∫ s in (T - 1)..(min τ T), φ i n (y, s) = _
      have hadj : (∫ s in (T - 1)..(min τ T), φ i n (y, s)) +
          ∫ s in (min τ T)..(min τ' T), φ i n (y, s)
          = ∫ s in (T - 1)..(min τ' T), φ i n (y, s) :=
        intervalIntegral.integral_add_adjacent_intervals hAy hCy
      linarith only [hadj]
    have heq : pn i n (x, τ') - pn i n (x, τ) - (pn i n (y, τ') - pn i n (y, τ))
        = ∫ s in (min τ T)..(min τ' T), (φ i n (x, s) - φ i n (y, s)) := by
      rw [hspx, hspy, intervalIntegral.integral_sub hCx hCy]
    rw [heq]
    have hbound : |∫ s in (min τ T)..(min τ' T), (φ i n (x, s) - φ i n (y, s))| ≤
        Λ * ‖x - y‖ * |min τ' T - min τ T| := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := min τ T) (b := min τ' T) (f := fun s => φ i n (x, s) - φ i n (y, s))
        (C := Λ * ‖x - y‖)
        (fun s hs => by
          have hsmem : s ∈ Icc (min c (T - 1)) T := by
            rcases le_total (min τ T) (min τ' T) with hle | hle
            · rw [Set.uIoc_of_le hle] at hs
              exact ⟨le_trans hmemτ.1 hs.1.le, le_trans hs.2 hmemτ'.2⟩
            · rw [Set.uIoc_of_ge hle] at hs
              exact ⟨le_trans hmemτ'.1 hs.1.le, le_trans hs.2 hmemτ.2⟩
          rw [Real.norm_eq_abs]
          exact (hn i s hsmem x hx y hy).2)
      rwa [Real.norm_eq_abs] at hle
    have hΛxynn : 0 ≤ Λ * ‖x - y‖ := by positivity
    calc |∫ s in (min τ T)..(min τ' T), (φ i n (x, s) - φ i n (y, s))| ≤
          Λ * ‖x - y‖ * |min τ' T - min τ T| := hbound
      _ ≤ Λ * ‖x - y‖ * |τ' - τ| := mul_le_mul_of_nonneg_left (abs_min_sub_min_le τ' τ T) hΛxynn
  -- Every compact set of space-time points lies inside `Bx k` for `k` large enough.
  have hKsub : ∀ K : Set (Vec m × ℝ), IsCompact K → ∃ k : ℕ, K ⊆ Bx k := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0, T - 1)
    set k : ℕ := ⌈R⌉₊ + ⌈|T|⌉₊ + 10 with hkdef
    refine ⟨k, fun z hz => ?_⟩
    have hzmem := hR hz
    rw [← closedBall_prod_same, Real.closedBall_eq_Icc] at hzmem
    obtain ⟨hz1, hz2⟩ := hzmem
    have hkbound : R + |T| + 10 ≤ (k : ℝ) := by
      have h1 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : |T| ≤ (⌈|T|⌉₊ : ℝ) := Nat.le_ceil _
      push_cast [hkdef]
      linarith only [h1, h2]
    have hRk : R ≤ (k : ℝ) := by linarith only [hkbound, abs_nonneg T]
    refine ⟨Metric.closedBall_subset_closedBall hRk hz1, ?_, ?_⟩
    · nlinarith only [hkbound, hz2.1, le_abs_self T, neg_abs_le T, abs_nonneg T]
    · nlinarith only [hkbound, hz2.2, le_abs_self T, neg_abs_le T, abs_nonneg T]
  -- Uniform convergence on every compact set, and pointwise convergence, of `pn i` to `p i`.
  have htendsto : ∀ K : Set (Vec m × ℝ), IsCompact K → ∀ i,
      TendstoUniformlyOn (fun n z => pn i (ψ n) z) (p i) atTop K := by
    intro K hK i
    obtain ⟨k, hk⟩ := hKsub K hK
    have h1 : TendstoUniformlyOn (fun n z => pn i (ψ n) z) (p i) atTop (Bx k) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hw k) ε hε] with n hn z hz
      have hproj : dist (w z i) (pn i (ψ n) z) ≤ dist (w z) (fun j => pn j (ψ n) z) :=
        dist_le_pi_dist (w z) (fun j => pn j (ψ n) z) i
      have := hn z hz
      rw [hpdef]
      exact lt_of_le_of_lt hproj this
    exact h1.mono hk
  have hptendsto : ∀ i, ∀ z : Vec m × ℝ, Tendsto (fun n => pn i (ψ n) z) atTop (𝓝 (p i z)) :=
    fun i z => (htendsto {z} isCompact_singleton i).tendsto_at (Set.mem_singleton z)
  -- Passing an eventual real inequality to the limit along a convergent sequence.
  have habs_le_of_tendsto : ∀ (a : ℕ → ℝ) (A C : ℝ), Tendsto a atTop (𝓝 A) →
      (∀ᶠ n in atTop, |a n| ≤ C) → |A| ≤ C := fun a A C hA hev => le_of_tendsto hA.abs hev
  refine ⟨ψ, hψ, p, hpcont, htendsto, fun i => ?_⟩
  refine exists_measurable_ae_hasDerivAt_of_lipschitz_mixed (hpcont i) ?_
  intro c d hcd
  obtain ⟨Λ1, hΛ1nn, hΛ1r⟩ := htimeLipn c d hcd
  obtain ⟨Λ2, hΛ2nn, hΛ2r⟩ := hmixedn c d hcd
  refine ⟨max Λ1 Λ2, le_trans hΛ1nn (le_max_left _ _), ?_, ?_⟩
  · intro x
    have hx : x ∈ Metric.closedBall (0 : Vec m) ‖x‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hΛ1 := hΛ1r ‖x‖
    apply LipschitzOnWith.of_dist_le_mul
    intro τ hτ τ' hτ'
    rw [Real.coe_toNNReal (max Λ1 Λ2) (le_trans hΛ1nn (le_max_left _ _))]
    have hbound : |p i (x, τ') - p i (x, τ)| ≤ Λ1 * |τ' - τ| := by
      have ha : Tendsto (fun n => pn i (ψ n) (x, τ') - pn i (ψ n) (x, τ)) atTop
          (𝓝 (p i (x, τ') - p i (x, τ))) :=
        (hptendsto i (x, τ')).sub (hptendsto i (x, τ))
      have hev : ∀ᶠ n in atTop,
          |pn i (ψ n) (x, τ') - pn i (ψ n) (x, τ)| ≤ Λ1 * |τ' - τ| :=
        (hψ.tendsto_atTop.eventually hΛ1).mono (fun n hn => hn i x hx τ hτ τ' hτ')
      exact habs_le_of_tendsto _ _ _ ha hev
    calc dist (p i (x, τ)) (p i (x, τ')) = |p i (x, τ') - p i (x, τ)| := by
          rw [Real.dist_eq, abs_sub_comm]
      _ ≤ Λ1 * |τ' - τ| := hbound
      _ ≤ max Λ1 Λ2 * |τ' - τ| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ = max Λ1 Λ2 * dist τ τ' := by rw [Real.dist_eq, abs_sub_comm]
  · intro x y τ hτ τ' hτ'
    have hx : x ∈ Metric.closedBall (0 : Vec m) (‖x‖ ⊔ ‖y‖) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_max_left _ _
    have hy : y ∈ Metric.closedBall (0 : Vec m) (‖x‖ ⊔ ‖y‖) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_max_right _ _
    have hΛ2 := hΛ2r (‖x‖ ⊔ ‖y‖)
    have hbound : |p i (x, τ') - p i (x, τ) - (p i (y, τ') - p i (y, τ))| ≤
        Λ2 * ‖x - y‖ * |τ' - τ| := by
      have ha : Tendsto (fun n => pn i (ψ n) (x, τ') - pn i (ψ n) (x, τ) -
          (pn i (ψ n) (y, τ') - pn i (ψ n) (y, τ))) atTop
          (𝓝 (p i (x, τ') - p i (x, τ) - (p i (y, τ') - p i (y, τ)))) :=
        ((hptendsto i (x, τ')).sub (hptendsto i (x, τ))).sub
          ((hptendsto i (y, τ')).sub (hptendsto i (y, τ)))
      have hev : ∀ᶠ n in atTop,
          |pn i (ψ n) (x, τ') - pn i (ψ n) (x, τ) -
              (pn i (ψ n) (y, τ') - pn i (ψ n) (y, τ))| ≤ Λ2 * ‖x - y‖ * |τ' - τ| :=
        (hψ.tendsto_atTop.eventually hΛ2).mono (fun n hn => hn i x hx y hy τ hτ τ' hτ')
      exact habs_le_of_tendsto _ _ _ ha hev
    calc |p i (x, τ') - p i (x, τ) - (p i (y, τ') - p i (y, τ))| ≤ Λ2 * ‖x - y‖ * |τ' - τ| :=
        hbound
      _ ≤ max Λ1 Λ2 * ‖x - y‖ * |τ' - τ| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- Pack `b` (vector-valued drift) and `divb` (scalar divergence) into one `Option (Fin m)`
indexed family of scalar fields, with `some i` picking out the `i`-th component of `b` and
`none` picking out `divb`. -/
@[expose] def packBD {m : ℕ} (b : ℕ → Vec m × ℝ → Vec m) (divb : ℕ → Vec m × ℝ → ℝ) :
    Option (Fin m) → ℕ → Vec m × ℝ → ℝ :=
  fun i n z => Option.rec (divb n z) (fun i0 => b n z i0) i

/-- Weak-in-time, Lipschitz-in-space extraction of an admissible drift, via the
route of deviation D14 (time primitives, box-diagonal Arzelà-Ascoli, and the a.e.-derivative lemma
`exists_measurable_ae_hasDerivAt_of_lipschitz_mixed` above) rather than weak-* compactness.
`b` and `divb` are packed into one `Option (Fin m)`-indexed family of scalar fields via
`packBD`, fed to `exists_subseq_primitives_ae_hasDerivAt`, and the resulting per-component
limits and derivatives are reassembled into a vector-valued admissible drift `(B, divB)`;
the weak divergence identity and the weak-convergence conclusion are supplied by
`CIV.ae_weakDiv_of_tendstoUniformlyOn_primitive` and
`CIV.tendsto_integral_mul_of_tendstoUniformlyOn_primitive`. -/
theorem exists_subseq_admissibleDrift {m : ℕ} {T : ℝ} (b : ℕ → Vec m × ℝ → Vec m)
    (divb : ℕ → Vec m × ℝ → ℝ)
    (hcont : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (b n) K ∧ ContinuousOn (divb n) K)
    (hbd : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec m) r, ∀ y ∈ Metric.closedBall (0 : Vec m) r,
        ‖b n (x, τ)‖ ≤ Λ ∧ |divb n (x, τ)| ≤ Λ ∧
        ‖b n (x, τ) - b n (y, τ)‖ ≤ Λ * ‖x - y‖ ∧
        |divb n (x, τ) - divb n (y, τ)| ≤ Λ * ‖x - y‖)
    (hdiv : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∀ᶠ n in atTop, ∀ τ ∈ J,
        ∫ x, divb n (x, τ) * ψ x = -∫ x, ∑ i, b n (x, τ) i * fderiv ℝ ψ x (basisVec i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ),
      IsAdmissibleDrift m (Iio T) B divB ∧
      ∀ g : Vec m × ℝ → ℝ, Integrable g → HasCompactSupport g → tsupport g ⊆ univ ×ˢ Iio T →
        (∀ i, Tendsto (fun n => ∫ z, g z * b (φ n) z i) atTop (nhds (∫ z, g z * B z i))) ∧
        Tendsto (fun n => ∫ z, g z * divb (φ n) z) atTop (nhds (∫ z, g z * divB z)) := by
  classical
  set φfam : Option (Fin m) → ℕ → Vec m × ℝ → ℝ := packBD b divb with hφfamdef
  have hcontJ : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ∀ i : Option (Fin m), ContinuousOn (φfam i n) K := by
    intro K hK hKsub
    filter_upwards [hcont K hK hKsub] with n hn i
    cases i with
    | none => exact hn.2
    | some i0 => exact (continuous_apply i0).comp_continuousOn hn.1
  have hbdJ : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ i : Option (Fin m), ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec m) r,
        ∀ y ∈ Metric.closedBall (0 : Vec m) r,
          |φfam i n (x, τ)| ≤ Λ ∧ |φfam i n (x, τ) - φfam i n (y, τ)| ≤ Λ * ‖x - y‖ := by
    intro J hJ hJsub
    obtain ⟨Λ, hΛr⟩ := hbd J hJ hJsub
    refine ⟨max Λ 0, le_max_right _ _, fun r => ?_⟩
    filter_upwards [hΛr r] with n hn i τ hτ x hx y hy
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hn τ hτ x hx y hy
    cases i with
    | none =>
        exact ⟨le_trans hb2 (le_max_left _ _),
          le_trans hb4 (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
    | some i0 =>
        refine ⟨le_trans (norm_le_pi_norm (b n (x, τ)) i0) (le_trans hb1 (le_max_left _ _)), ?_⟩
        have hsub : (b n (x, τ) - b n (y, τ)) i0 = b n (x, τ) i0 - b n (y, τ) i0 := rfl
        calc |b n (x, τ) i0 - b n (y, τ) i0|
            = ‖(b n (x, τ) - b n (y, τ)) i0‖ := by rw [hsub, ← Real.norm_eq_abs]
          _ ≤ ‖b n (x, τ) - b n (y, τ)‖ := norm_le_pi_norm _ i0
          _ ≤ Λ * ‖x - y‖ := hb3
          _ ≤ max Λ 0 * ‖x - y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨ψ, hψ, p, hpcont, htendsto, hderiv⟩ :=
    exists_subseq_primitives_ae_hasDerivAt φfam hcontJ hbdJ
  set a : Vec m × ℝ → Vec m := fun z i => p (some i) z with hadef
  set adiv : Vec m × ℝ → ℝ := p none with hadivdef
  have ha : ∀ i, Continuous (fun z => a z i) := fun i => hpcont (some i)
  have hadiv : Continuous adiv := hpcont none
  have hconv : ∀ K : Set (Vec m × ℝ), IsCompact K → ∀ i,
      TendstoUniformlyOn (fun n z => ∫ s in (T - 1)..(min z.2 T), b (ψ n) (z.1, s) i)
        (fun z => a z i) atTop K :=
    fun K hK i => htendsto K hK (some i)
  have hconvd : ∀ K : Set (Vec m × ℝ), IsCompact K →
      TendstoUniformlyOn (fun n z => ∫ s in (T - 1)..(min z.2 T), divb (ψ n) (z.1, s))
        adiv atTop K :=
    fun K hK => htendsto K hK none
  set Gfun : Option (Fin m) → Vec m × ℝ → ℝ := fun i => (hderiv i).choose with hGfundef
  have hGfunspec : ∀ i, Measurable (Gfun i) ∧ ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ᵐ τ ∂(volume.restrict (Icc c d)), (∀ x, HasDerivAt (fun τ' => p i (x, τ')) (Gfun i (x,
        τ)) τ) ∧
        (∀ x, |Gfun i (x, τ)| ≤ Λ) ∧ LipschitzWith Λ.toNNReal (fun x => Gfun i (x, τ)) :=
    fun i => (hderiv i).choose_spec
  set B : Vec m × ℝ → Vec m := fun z i => Gfun (some i) z with hBdef
  set divB : Vec m × ℝ → ℝ := Gfun none with hdivBdef
  have hBm : Measurable B := measurable_pi_iff.mpr (fun i => (hGfunspec (some i)).1)
  have hdivBm : Measurable divB := (hGfunspec none).1
  have hB : ∀ i, ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      (∀ x, HasDerivAt (fun τ' => a (x, τ') i) (B (x, τ) i) τ) ∧ (∀ x, |B (x, τ) i| ≤ Λ) ∧
      LipschitzWith Λ.toNNReal (fun x => B (x, τ) i) :=
    fun i => (hGfunspec (some i)).2
  have hdivB : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      (∀ x, HasDerivAt (fun τ' => adiv (x, τ')) (divB (x, τ)) τ) ∧ (∀ x, |divB (x, τ)| ≤ Λ) ∧
      LipschitzWith Λ.toNNReal (fun x => divB (x, τ)) :=
    (hGfunspec none).2
  have hweakdiv := ae_weakDiv_of_tendstoUniformlyOn_primitive b divb hcont hbd hdiv
    ψ hψ a adiv ha hadiv hconv hconvd B divB hBm hdivBm hB hdivB
  have hadm : IsAdmissibleDrift m (Iio T) B divB := by
    refine ⟨hBm, hdivBm, fun J hJ hJsub => ?_⟩
    obtain ⟨c0, hc0⟩ := hJ.bddBelow
    obtain ⟨d0, hd0⟩ := hJ.bddAbove
    set c := c0 with hcdef
    set d := max c0 d0 with hddef
    have hcd : c ≤ d := le_max_left _ _
    have hJIcc : J ⊆ Icc c d := fun x hx => ⟨hc0 hx, le_trans (hd0 hx) (le_max_right _ _)⟩
    set Λall : Fin m → ℝ := fun i => (hB i c d hcd).choose with hΛalldef
    have hΛallspec : ∀ i, 0 ≤ Λall i ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
        (∀ x, HasDerivAt (fun τ' => a (x, τ') i) (B (x, τ) i) τ) ∧
          (∀ x, |B (x, τ) i| ≤ Λall i) ∧
          LipschitzWith (Λall i).toNNReal (fun x => B (x, τ) i) :=
      fun i => (hB i c d hcd).choose_spec
    set Λdiv : ℝ := (hdivB c d hcd).choose with hΛdivdef
    have hΛdivspec : 0 ≤ Λdiv ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
        (∀ x, HasDerivAt (fun τ' => adiv (x, τ')) (divB (x, τ)) τ) ∧ (∀ x, |divB (x, τ)| ≤ Λdiv) ∧
        LipschitzWith Λdiv.toNNReal (fun x => divB (x, τ)) :=
      (hdivB c d hcd).choose_spec
    set Λcomb : ℝ := Λdiv + ∑ i, Λall i with hΛcombdef
    have hΛcombnn : 0 ≤ Λcomb :=
      add_nonneg hΛdivspec.1 (Finset.sum_nonneg (fun i _ => (hΛallspec i).1))
    have hΛille : ∀ i, Λall i ≤ Λcomb := by
      intro i
      have h1 : Λall i ≤ ∑ j, Λall j :=
        Finset.single_le_sum (fun j _ => (hΛallspec j).1) (Finset.mem_univ i)
      have h2 : (∑ j, Λall j : ℝ) ≤ Λdiv + ∑ j, Λall j := le_add_of_nonneg_left hΛdivspec.1
      exact le_trans h1 h2
    have hΛdivle : Λdiv ≤ Λcomb := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
      (hΛallspec i).1))
    refine ⟨Λcomb.toNNReal, ?_⟩
    have hae1 : ∀ᵐ τ ∂(volume.restrict J), ∀ i,
        (∀ x, HasDerivAt (fun τ' => a (x, τ') i) (B (x, τ) i) τ) ∧
          (∀ x, |B (x, τ) i| ≤ Λall i) ∧ LipschitzWith (Λall i).toNNReal (fun x => B (x, τ) i) :=
      (ae_all_iff.mpr (fun i => (hΛallspec i).2)).filter_mono
        (ae_mono (Measure.restrict_mono hJIcc le_rfl))
    have hae2 : ∀ᵐ τ ∂(volume.restrict J),
        (∀ x, HasDerivAt (fun τ' => adiv (x, τ')) (divB (x, τ)) τ) ∧ (∀ x, |divB (x, τ)| ≤ Λdiv) ∧
        LipschitzWith Λdiv.toNNReal (fun x => divB (x, τ)) :=
      hΛdivspec.2.filter_mono (ae_mono (Measure.restrict_mono hJIcc le_rfl))
    have hae3 := hweakdiv J hJ hJsub
    filter_upwards [hae1, hae2, hae3] with τ h1 h2 h3
    refine ⟨?_, ?_, ?_, h3⟩
    · intro x
      rw [Real.coe_toNNReal Λcomb hΛcombnn, pi_norm_le_iff_of_nonneg hΛcombnn]
      intro i
      rw [Real.norm_eq_abs]
      exact le_trans ((h1 i).2.1 x) (hΛille i)
    · refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      rw [Real.coe_toNNReal Λcomb hΛcombnn, dist_eq_norm,
        pi_norm_le_iff_of_nonneg (mul_nonneg hΛcombnn dist_nonneg)]
      intro i
      have hi := ((h1 i).2.2).dist_le_mul x y
      rw [Real.coe_toNNReal (Λall i) (hΛallspec i).1] at hi
      show ‖(B (x, τ) - B (y, τ)) i‖ ≤ Λcomb * dist x y
      rw [Pi.sub_apply, Real.norm_eq_abs, ← Real.dist_eq]
      exact le_trans hi (mul_le_mul_of_nonneg_right (hΛille i) dist_nonneg)
    · intro x
      rw [Real.coe_toNNReal Λcomb hΛcombnn]
      exact le_trans ((h2).2.1 x) hΛdivle
  refine ⟨ψ, hψ, B, divB, hadm,
    tendsto_integral_mul_of_tendstoUniformlyOn_primitive b divb hcont hbd
      ψ hψ a adiv ha hadiv hconv hconvd B divB hBm hdivBm hB hdivB⟩

end CIV
