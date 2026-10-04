/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.PointwiseEquation
public import LeanPool.EllipticPDE.Existence.WeakMaximum


/-!
# Truncation in `H₀¹`

`H₀¹(Ω)` is closed under the truncation `u ↦ (u - k)⁺` for `k ≥ 0`. Two steps. A class on the
whole space with an `L²` weak gradient and compact support inside the open set `Ω` lies in
`H₀¹(Ω)`: its mollifications are test functions of `Ω` once the radius is below the distance
from the support to the complement, and they converge to it in `H¹` together with their
gradients, which are the mollified weak gradient. Then, for `V ∈ H₀¹(Ω)` approximated by test
functions `φ_n`, the truncations `(φ_n - k)⁺` have compact support in `Ω` because `k ≥ 0`,
have the weak gradient `∇φ_n` on `{φ_n > k}` by the chain rule for the positive part, so lie in
`H₀¹(Ω)` by the first step, and converge in `H¹(Ω)` to `(v - k)⁺` with gradient `∇v` on
`{v > k}`: the function coordinates because truncation is `1`-Lipschitz, the gradient
coordinates along a subsequence converging almost everywhere by dominated convergence, the
level set `{v = k}` giving nothing because the weak gradient vanishes there.

This is the step the proof of the weak maximum principle takes for granted when it tests
against `(u - k)⁺`. With it, the principle applies to every subsolution in `H₀¹(Ω)`, and the
uniqueness of the generalised Dirichlet problem follows by applying it to the solution and to
its negative.

## Main declarations

* `EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport`: a compactly supported class with `L²`
  weak gradient lies in `H₀¹`.
* `EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const`: `H₀¹` is closed under
  `u ↦ (u - k)⁺` for `k ≥ 0`.
* `EllipticPdes.Sobolev.weak_maximum_principle_H01`: a subsolution in `H₀¹` is nonpositive.
* `EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01`: uniqueness of the generalised Dirichlet
  problem.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 and Corollary 8.2 (pp. 179–180);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.1 Theorem 1 (p. 264).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding EllipticPdes.Extension EllipticPdes.Regularity

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Compactly supported classes lie in `H₀¹` -/

/-- **Compactly supported classes with `L²` weak gradient lie in `H₀¹`.** A class on the whole
space with an `L²` weak gradient whose support is a compact subset of the open set `Ω` is, with
its gradient, the `H¹(Ω)` limit of its mollifications, which are test functions of `Ω`. -/
theorem mem_H01_of_hasCompactSupport (hΩ : IsOpen Ω) {w : EuclideanSpace ℝ (Fin d) → ℝ}
    {h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hwg : HasWeakGradOn univ w h)
    (hw : MemLp w 2 volume) (hh : ∀ k, MemLp (h k) 2 volume) (hwcs : HasCompactSupport w)
    (hwΩ : tsupport w ⊆ Ω) :
    WithLp.toLp 2 (Fin.cons ((hw.mono_measure Measure.restrict_le_self).toLp w)
      fun k => ((hh k).mono_measure Measure.restrict_le_self).toLp (h k)) ∈ H01 Ω := by
  classical
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  -- integrability of `w` on the whole space, from its compact support
  have hwint : Integrable w volume := by
    have : IsFiniteMeasure (volume.restrict (tsupport w)) :=
      isFiniteMeasure_restrict.2 hwcs.measure_lt_top.ne
    have : IntegrableOn w (tsupport w) volume :=
      (hw.mono_measure Measure.restrict_le_self).integrable one_le_two
    exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport w)).mp this
  obtain ⟨δ, hδ, hK'⟩ := IsCompact.exists_cthickening_subset_open hwcs hΩ hwΩ
  -- the mollifiers
  let φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := δ / (n + 1 : ℝ) / 2
      rOut := δ / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hrOut : ∀ n : ℕ, (φb n).rOut = δ / (n + 1 : ℝ) := fun _ => rfl
  have hrIn : ∀ n : ℕ, (φb n).rIn = δ / (n + 1 : ℝ) / 2 := fun _ => rfl
  have hφrOut : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    ring
  have hφratio : ∀ᶠ n in atTop, (φb n).rOut ≤ 2 * (φb n).rIn :=
    Eventually.of_forall fun n => le_of_eq (by rw [hrOut, hrIn]; ring)
  have hrOut_le : ∀ n : ℕ, (φb n).rOut ≤ δ := fun n => by
    rw [hrOut]
    exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => w ⋆[L, volume] (φb n).normed volume with hvdef
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L)
      hwint.locallyIntegrable (φb n).contDiff_normed
  have hvcs : ∀ n, HasCompactSupport (v n) := fun n =>
    HasCompactSupport.convolution (L := L) hwcs (φb n).hasCompactSupport_normed
  -- the mollifications are supported inside the domain
  have hvsupp : ∀ n, tsupport (v n) ⊆ Ω := fun n => by
    refine (closure_minimal ?_ isClosed_cthickening).trans hK'
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp (support_convolution_subset L hx)
    rw [(φb n).support_normed_eq] at hb
    refine mem_cthickening_of_dist_le (a + b) a δ _ (subset_tsupport w ha) ?_
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (mem_ball_zero_iff.mp hb).le.trans (hrOut_le n)
  have hv : ∀ n, IsTestFn Ω (v n) := fun n => ⟨hvsmooth n, hvcs n, hvsupp n⟩
  -- the partials of the mollifications are the mollified weak gradient
  have hpartial : ∀ n k, partialD k (v n) = h k ⋆[L, volume] (φb n).normed volume := by
    intro n k
    funext x
    have := partialD_convolution_eq_of_hasWeakGradOn MeasurableSet.univ hwint.integrableOn hwg
      (φb n) k (x := x) (subset_univ _)
    simpa only [indicator_univ] using this
  -- `L²` convergence of the mollifications on the whole space
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hw' : MemLp w (ENNReal.ofReal 2) volume := by rw [h2]; exact hw
  have hh' : ∀ k, MemLp (h k) (ENNReal.ofReal 2) volume := fun k => by rw [h2]; exact hh k
  have hconvw : Tendsto (fun n => eLpNorm (v n - w) 2 volume) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_convolution_sub one_le_two hw' hφrOut hφratio
    rwa [h2] at this
  have hconvh : ∀ k, Tendsto (fun n =>
      eLpNorm ((h k ⋆[L, volume] (φb n).normed volume) - h k) 2 volume) atTop (𝓝 0) := by
    intro k
    have := tendsto_eLpNorm_convolution_sub one_le_two (hh' k) hφrOut hφratio
    rwa [h2] at this
  -- the graphs of the mollifications converge to the graph of `w`
  have hclosed : IsClosed (H01 Ω : Set (H1amb Ω)) := Submodule.isClosed_topologicalClosure _
  refine hclosed.mem_of_tendsto (b := atTop) ?_
    (Eventually.of_forall fun n => testGraph_mem_H01 (hv n))
  have hgraph : (fun n => (hv n).testGraph)
      = fun n => WithLp.toLp 2 (Fin.cons (hv n).testCls fun i => (hv n).partialCls i) :=
    rfl
  rw [hgraph]
  refine ((PiLp.continuous_toLp 2 fun _ : Fin (d + 1) => L2D Ω).tendsto _).comp
    (tendsto_pi_nhds.mpr fun j => ?_)
  induction j using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, IsTestFn.testCls]
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconvw
      (fun _ => zero_le) fun n => eLpNorm_mono_measure _ Measure.restrict_le_self
  | succ k =>
    simp only [Fin.cons_succ, IsTestFn.partialCls]
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconvh k)
      (fun _ => zero_le) fun n => ?_
    rw [hpartial n k]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-! ### Truncation -/

/-- The truncation `t ↦ max (t - k) 0` is `1`-Lipschitz. -/
theorem abs_max_sub_le (a b k : ℝ) : |max (a - k) 0 - max (b - k) 0| ≤ |a - b| := by
  have := abs_max_sub_max_le_abs (a - k) (b - k) 0
  rwa [sub_sub_sub_cancel_right] at this

/-- **Truncation in `H₀¹`.** For `V ∈ H₀¹(Ω)` and `k ≥ 0` there is `W ∈ H₀¹(Ω)` whose function
coordinate is `(v - k)⁺` and whose gradient coordinates are those of `V` on `{v > k}` and zero
elsewhere. -/
theorem exists_mem_H01_posPart_sub_const (hΩ : IsOpen Ω) {V : H1amb Ω} (hV : V ∈ H01 Ω)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ W ∈ H01 Ω,
      ((W 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (fun x => max ((V 0 x : ℝ) - k) 0) ∧
      ∀ i : Fin d, ((W i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => if k < (V 0 x : ℝ) then (V i.succ x : ℝ) else 0 := by
  classical
  -- approximating test functions
  have hVcl : V ∈ closure ((Submodule.span ℝ (testGraphSet Ω) : Submodule ℝ (H1amb Ω)) :
      Set (H1amb Ω)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hV
  obtain ⟨X, hXmem, hXt⟩ := mem_closure_iff_seq_limit.mp hVcl
  have hXmem' : ∀ n, X n ∈ testGraphSet Ω := fun n => by
    have := hXmem n
    rw [span_testGraphSet] at this
    exact this
  choose φ hφ hXφ using hXmem'
  -- the coordinates of `V`
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (V 0 x : ℝ) with hvdef
  set g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x => (V i.succ x : ℝ) with hgdef
  have hvm : MemLp v 2 (volume.restrict Ω) := Lp.memLp _
  have hgm : ∀ i, MemLp (g i) 2 (volume.restrict Ω) := fun i => Lp.memLp _
  -- coordinatewise convergence in `L²(Ω)`
  have hXcoord : Tendsto (fun n => (X n).ofLp) atTop (𝓝 V.ofLp) :=
    ((PiLp.continuous_ofLp 2 fun _ : Fin (d + 1) => L2D Ω).tendsto V).comp hXt
  have hX0 : Tendsto (fun n => eLpNorm (φ n - v) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => X n 0) atTop (𝓝 (V 0)) := tendsto_pi_nhds.mp hXcoord 0
    have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp h1
    refine h2.congr fun n => eLpNorm_congr_ae ?_
    have e : X n 0 = (hφ n).testCls := by rw [hXφ n, IsTestFn.testGraph_zero]
    rw [e]
    filter_upwards [(hφ n).mem_lp.coeFn_toLp] with x hx
    simp only [IsTestFn.testCls, Pi.sub_apply, hvdef, hx]
  have hXi : ∀ i : Fin d, Tendsto (fun n => eLpNorm (partialD i (φ n) - g i) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
    intro i
    have h1 : Tendsto (fun n => X n i.succ) atTop (𝓝 (V i.succ)) :=
      tendsto_pi_nhds.mp hXcoord i.succ
    have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp h1
    refine h2.congr fun n => eLpNorm_congr_ae ?_
    have e : X n i.succ = (hφ n).partialCls i := by rw [hXφ n, IsTestFn.testGraph_succ]
    rw [e]
    filter_upwards [((hφ n).memLp_partialD i).coeFn_toLp] with x hx
    simp only [IsTestFn.partialCls, Pi.sub_apply, hgdef, hx]
  -- a subsequence converging almost everywhere
  have hmeas : TendstoInMeasure (volume.restrict Ω) φ atTop v :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
      hX0
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  -- the weak gradient of `V` vanishes on the level set
  have hvloc : LocallyIntegrableOn v Ω volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hvm.locallyIntegrable one_le_two)
  have hgloc : ∀ i, LocallyIntegrableOn (g i) Ω volume := fun i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hgm i).locallyIntegrable one_le_two)
  have hlevel : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), v x = k → g i x = 0 := fun i =>
    ae_eq_zero_of_eq_const_of_hasWeakGradOn hΩ hvloc hgloc
      (hasWeakGradOn_of_mem_W12 (H01_le_W12 Ω hV)) k i
  -- the truncations of the approximants
  set ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun i => φ (ns i) with hψdef
  have hψ : ∀ i, IsTestFn Ω (ψ i) := fun i => hφ (ns i)
  have hψc : ∀ i, Continuous (ψ i) := fun i => (hψ i).continuous
  have hψwg : ∀ i, HasWeakGradOn univ (fun x => max (ψ i x - k) 0)
      fun j x => if k < ψ i x then partialD j (ψ i) x else 0 := fun i =>
    hasWeakGradOn_posPart_sub_const isOpen_univ
      ((hψc i).locallyIntegrable.locallyIntegrableOn _)
      (fun j => ((hψ i).continuous_partialD j).locallyIntegrable.locallyIntegrableOn _)
      (hasWeakGradOn_of_contDiffOn isOpen_univ
        ((hψ i).1.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) k
  have hsupp : ∀ i, Function.support (fun x => max (ψ i x - k) 0) ⊆ tsupport (ψ i) :=
    fun i x hx => by
    refine subset_tsupport _ fun h0 => Function.mem_support.mp hx ?_
    simp only [h0, zero_sub]
    exact max_eq_right (neg_nonpos.mpr hk)
  have hcs : ∀ i, HasCompactSupport (fun x => max (ψ i x - k) 0) := fun i =>
    (hψ i).2.1.of_isClosed_subset isClosed_closure
      (closure_minimal (hsupp i) (isClosed_tsupport _))
  have hsuppΩ : ∀ i, tsupport (fun x => max (ψ i x - k) 0) ⊆ Ω := fun i =>
    (closure_minimal (hsupp i) (isClosed_tsupport _)).trans (hψ i).2.2
  have hwm : ∀ i, MemLp (fun x => max (ψ i x - k) 0) 2 volume := fun i =>
    (((hψc i).sub continuous_const).max continuous_const).memLp_of_hasCompactSupport (hcs i)
  have hhm : ∀ i j, MemLp (fun x => if k < ψ i x then partialD j (ψ i) x else 0) 2 volume :=
    fun i j =>
      (((hψ i).continuous_partialD j).memLp_of_hasCompactSupport
        ((hψ i).hasCompactSupport_partialD j)).of_le
        (aestronglyMeasurable_ite_lt (hψc i).aestronglyMeasurable
          ((hψ i).continuous_partialD j).aestronglyMeasurable k)
        (Eventually.of_forall fun x => by split_ifs <;> simp)
  have hWmem : ∀ i, WithLp.toLp 2
      (Fin.cons (((hwm i).mono_measure Measure.restrict_le_self).toLp _)
        fun j => ((hhm i j).mono_measure Measure.restrict_le_self).toLp _) ∈ H01 Ω :=
    fun i => mem_H01_of_hasCompactSupport hΩ (hψwg i) (hwm i) (hhm i) (hcs i) (hsuppΩ i)
  -- the limit
  have hwlim : MemLp (fun x => max (v x - k) 0) 2 (volume.restrict Ω) := by
    refine hvm.of_le (((continuous_id.sub continuous_const).max
      continuous_const).comp_aestronglyMeasurable hvm.aestronglyMeasurable)
          (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self (v x)]) (abs_nonneg _)
  have hhlim : ∀ i, MemLp (fun x => if k < v x then g i x else 0) 2 (volume.restrict Ω) :=
    fun i => (hgm i).of_le (aestronglyMeasurable_ite_lt hvm.aestronglyMeasurable (hgm
        i).aestronglyMeasurable k)
      (Eventually.of_forall fun x => by split_ifs <;> simp)
  refine ⟨WithLp.toLp 2 (Fin.cons (hwlim.toLp _) fun i => (hhlim i).toLp _), ?_, ?_, ?_⟩
  · -- membership: `H₀¹` is closed and the truncations converge to the limit
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (b := atTop) ?_
      (Eventually.of_forall hWmem)
    refine ((PiLp.continuous_toLp 2 fun _ : Fin (d + 1) => L2D Ω).tendsto _).comp
      (tendsto_pi_nhds.mpr fun j => ?_)
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hX0.comp hns.tendsto_atTop) (fun _ => zero_le) fun i => ?_
      refine eLpNorm_mono ((((hwm i).restrict Ω).aestronglyMeasurable).sub
        hwlim.aestronglyMeasurable) fun x => ?_
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      exact abs_max_sub_le _ _ _
    | succ j =>
      simp only [Fin.cons_succ]
      refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr ?_
      -- split into the gradient difference on `{ψ > k}` and the indicator difference
      set A : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
        fun i x => if k < ψ i x then partialD j (ψ i) x - g j x else 0 with hAdef
      set B : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
        fun i x => (if k < ψ i x then g j x else 0) - (if k < v x then g j x else 0) with hBdef
      have hsplit : ∀ i, ((fun x => if k < ψ i x then partialD j (ψ i) x else 0)
          - fun x => if k < v x then g j x else 0) = A i + B i := by
        intro i
        funext x
        simp only [Pi.sub_apply, Pi.add_apply, hAdef, hBdef]
        split_ifs <;> ring
      have hAm : ∀ i, AEStronglyMeasurable (A i) (volume.restrict Ω) := fun i =>
        aestronglyMeasurable_ite_lt (hψc i).aestronglyMeasurable
          (((hψ i).continuous_partialD j).aestronglyMeasurable.sub (hgm j).aestronglyMeasurable) k
      have hBm : ∀ i, AEStronglyMeasurable (B i) (volume.restrict Ω) := fun i =>
        (aestronglyMeasurable_ite_lt (hψc i).aestronglyMeasurable (hgm j).aestronglyMeasurable
            k).sub
          (aestronglyMeasurable_ite_lt hvm.aestronglyMeasurable (hgm j).aestronglyMeasurable k)
      have hA : Tendsto (fun i => eLpNorm (A i) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          ((hXi j).comp hns.tendsto_atTop) (fun _ => zero_le) fun i => ?_
        refine eLpNorm_mono (hAm i) fun x => ?_
        simp only [hAdef, Pi.sub_apply, hψdef]
        split_ifs <;> simp
      have hB : Tendsto (fun i => eLpNorm (B i) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
        have hrepr : ∀ i, eLpNorm (B i) 2 (volume.restrict Ω)
            = (∫⁻ x, ‖B i x‖ₑ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := fun i => by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hBm i),
            ENNReal.toReal_ofNat]
        simp only [hrepr]
        have hlim : Tendsto (fun i => ∫⁻ x, ‖B i x‖ₑ ^ (2 : ℝ) ∂(volume.restrict Ω)) atTop
            (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂(volume.restrict Ω))) := by
          refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖g j x‖ₑ ^ (2 : ℝ))
            (fun i => (hBm i).enorm.pow_const _)
            (fun i => Eventually.of_forall fun x => ?_) ?_ ?_
          · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
            rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
              coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
            simp only [hBdef]
            split_ifs <;> simp
          · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
              (hgm j).eLpNorm_lt_top).ne
          · filter_upwards [hae, hlevel j] with x hx hxl
            have hBzero : ∀ᶠ i in atTop, B i x = 0 := by
              rcases lt_trichotomy (v x) k with hlt | heq | hgt
              · filter_upwards [hx.eventually (gt_mem_nhds hlt)] with i hi
                have hi' : φ (ns i) x < k := hi
                simp only [hBdef, hψdef]
                rw [ite_eq_right (not_lt.mpr hi'.le), ite_eq_right (not_lt.mpr hlt.le), sub_zero]
              · refine Eventually.of_forall fun i => ?_
                simp only [hBdef, hxl heq]
                split_ifs <;> simp
              · filter_upwards [hx.eventually (lt_mem_nhds hgt)] with i hi
                have hi' : k < φ (ns i) x := hi
                simp only [hBdef, hψdef]
                rw [ite_eq_left hi', ite_eq_left hgt, sub_self]
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [hBzero] with i hi
            rw [hi, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
        rw [lintegral_zero] at hlim
        have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hlim
        rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
        exact this
      have hsum := hA.add hB
      rw [add_zero] at hsum
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ => zero_le) fun i => ?_
      rw [hsplit i]
      exact eLpNorm_add_le one_le_two
  · simp only [Fin.cons_zero]
    exact hwlim.coeFn_toLp
  · intro i
    simp only [Fin.cons_succ]
    exact (hhlim i).coeFn_toLp

/-! ### The maximum principle in `H₀¹` -/

/-- **Weak maximum principle for a subsolution in `H₀¹`.** With the boundary inequality
`u ≤ 0` supplied by membership of the subsolution in `H₀¹(Ω)`, a subsolution of a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
nonpositive almost everywhere. -/
theorem weak_maximum_principle_H01 (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x) (U : H01 Ω)
    (hsub : ∀ V : H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ)) →
      Op.fullBilin Ω U V ≤ 0) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) ≤ 0 := by
  obtain ⟨W, hW, hW0, -⟩ := exists_mem_H01_posPart_sub_const hΩopen U.2 (le_refl (0 : ℝ))
  refine weak_maximum_principle hd hΩopen hΩb Op hb hc (H01_le_W12 Ω U.2) (fun V hV => ?_)
    (le_refl (0 : ℝ))
    ⟨⟨W, hW⟩, ?_⟩
  · have := hsub V hV
    rwa [FullEllipticOp.fullBilin_apply, EllipticCoeff.bilin_apply, FullEllipticOp.lowerBilin_apply,
      ← add_assoc] at this
  · filter_upwards [hW0] with x hx
    simpa only [sub_zero] using hx

/-- **Uniqueness of the generalised Dirichlet problem** (Gilbarg and Trudinger Corollary 8.2,
transport-free case). A weak solution in `H₀¹(Ω)` of the homogeneous equation for a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
zero. -/
theorem eq_zero_of_weakSolution_H01 (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x) (U : H01 Ω)
    (hsol : ∀ V : H01 Ω, Op.fullBilin Ω U V = 0) : U = 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  -- the function coordinate vanishes, by the principle applied to `U` and to `-U`
  have hle := weak_maximum_principle_H01 hd hΩopen hΩb Op hb hc U fun V _ => (hsol V).le
  have hge := weak_maximum_principle_H01 hd hΩopen hΩb Op hb hc (-U) fun V _ => by
    rw [map_neg, _root_.neg_apply, hsol V, neg_zero]
  have h0 : ((U : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] 0 := by
    have hneg : ((-U : H01 Ω) : H1amb Ω) 0 = -((U : H1amb Ω) 0) := rfl
    rw [hneg] at hge
    filter_upwards [hle, hge, Lp.coeFn_neg ((U : H1amb Ω) 0)] with x hx1 hx2 hx3
    rw [hx3, Pi.neg_apply] at hx2
    simp only [Pi.zero_apply]
    linarith
  have hU0 : (U : H1amb Ω) 0 = 0 := by
    apply Lp.ext
    exact h0.trans (Lp.coeFn_zero _ _ _).symm
  -- the gradient coordinates vanish by uniqueness of the weak gradient
  have hwg := hasWeakGradOn_of_mem_W12 (H01_le_W12 Ω U.2)
  have hwg0 : HasWeakGradOn Ω (fun x => ((U : H1amb Ω) 0 x : ℝ)) fun _ _ => (0 : ℝ) :=
    hasWeakGradOn_zero.congr_ae (by
      filter_upwards [h0] with x hx
      simp only [Pi.zero_apply] at hx
      exact hx.symm) fun _ => EventuallyEq.rfl
  have hgrad : ∀ i : Fin d, (U : H1amb Ω) i.succ = 0 := fun i => by
    apply Lp.ext
    have := hasWeakGradOn_unique_ae hΩopen hΩopen.measurableSet
      (fun i => (Lp.memLp ((U : H1amb Ω) i.succ)).integrable one_le_two)
      (fun _ => integrableOn_zero) hwg hwg0 i
    exact this.trans (Lp.coeFn_zero _ _ _).symm
  apply Subtype.ext
  apply PiLp.ext
  intro j
  induction j using Fin.cases with
  | zero => simpa using hU0
  | succ i => simpa using hgrad i

end EllipticPdes.Sobolev
