/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Mollification
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.SmoothBall

/-!
# Cutoff gluing and compact smooth weak-derivative approximation
-/

@[expose] public section

section
open MeasureTheory
open scoped ContDiff

section WeakDerivativeGluing

open MeasureTheory Set Filter Metric
open scoped Topology

/-! Gluing local weak derivatives along cutoffs into a global one. -/

namespace FunctionalInequalities.Analysis

/-- **Gluing local weak derivatives**: if for every `C¹` cutoff `χ` with
compact support the product `χ f` has a weak derivative along `v` that is locally `L²`, then `f`
itself has a weak
derivative along `v` that is `L²` on every compact set. -/
theorem exists_hasWeakDerivAlong_of_forall_cutoff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ∀ S : Set E, IsCompact S → MemLp f 2 ((volume : Measure E).restrict S))
    (v : E)
    (hloc :
      ∀ χ : E → ℝ,
        ContDiff ℝ 1 χ →
          HasCompactSupport χ →
            ∃ g : E → ℝ,
              HasWeakDerivAlong (fun x => χ x * f x) g v ∧ MemLp g 2 (volume : Measure E)) :
    ∃ g : E → ℝ,
      HasWeakDerivAlong f g v ∧
        ∀ S : Set E, IsCompact S → MemLp g 2 ((volume : Measure E).restrict S) := by
  classical
  have compact_bound : ∀ S : Set E, IsCompact S → ∃ n : ℕ, ∀ x ∈ S, ‖x‖ < (n : ℝ) + 1 := by
    intro S hS
    obtain ⟨r, hr⟩ := hS.isBounded.subset_ball (0 : E)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨n, ?_⟩
    intro x hx
    have hxr : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using hr hx
    exact hxr.trans (hn.trans (lt_add_one _))
  have local_integrability :
    ∀ u : E → ℝ,
      (∀ S : Set E, IsCompact S → MemLp u 2 ((volume : Measure E).restrict S)) →
        LocallyIntegrable u (volume : Measure E) := by
    intro u hu
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure ((volume : Measure E).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hu S hS).integrable (by norm_num)
  let χ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  have hχ_one : ∀ (n : ℕ) (x : E), ‖x‖ < (n : ℝ) + 1 → χ n x = 1 := by
    intro n x hx
    apply (χ n).one_of_mem_closedBall
    change dist x 0 ≤ (n : ℝ) + 1
    rw [dist_zero_right]
    exact hx.le
  have hχ_deriv : ∀ (n : ℕ) (x : E), ‖x‖ < (n : ℝ) + 1 → fderiv ℝ (χ n : E → ℝ) x = 0 := by
    intro n x hx
    have he : (χ n : E → ℝ) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      have hxball : x ∈ ball (0 : E) ((n : ℝ) + 1) := by
        simpa only [mem_ball, dist_zero_right] using hx
      filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
      apply hχ_one n y
      simpa only [mem_ball, dist_zero_right] using hy
    exact he.fderiv_eq.trans (congrFun (fderiv_const (𝕜 := ℝ) (E := E) (1 : ℝ)) x)
  have hex :
    ∀ n : ℕ,
      ∃ G : E → ℝ,
        HasWeakDerivAlong (fun x => χ n x * f x) G v ∧ MemLp G 2 (volume : Measure E) := by
    intro n
    exact hloc (χ n) (χ n).contDiff (χ n).hasCompactSupport
  choose G hG hGL using hex
  have consistency :
    ∀ m n : ℕ,
      ∀ᵐ x ∂(volume : Measure E), ‖x‖ < (m : ℝ) + 1 → ‖x‖ < (n : ℝ) + 1 → G m x = G n x := by
    intro m n
    have H := (hG m).mul_contDiff (χ n).contDiff (χ n).hasCompactSupport
    have K := (hG n).mul_contDiff (χ m).contDiff (χ m).hasCompactSupport
    have e : (fun x => χ n x * (χ m x * f x)) = (fun x => χ m x * (χ n x * f x)) := by
      funext x
      ring
    rw [e] at H
    have he := H.ae_eq K
    filter_upwards [he] with x hx
    intro hm hn
    simpa only [hχ_one m x hm, hχ_one n x hn, hχ_deriv m x hm, hχ_deriv n x hn, zero_apply,
      one_mul, zero_mul, add_zero] using hx
  let g : E → ℝ := fun x => G ⌈‖x‖⌉₊ x
  have agreement : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure E), ‖x‖ < (n : ℝ) + 1 → g x = G n x := by
    have hall :
      ∀ᵐ x ∂(volume : Measure E),
        ∀ m n : ℕ, ‖x‖ < (m : ℝ) + 1 → ‖x‖ < (n : ℝ) + 1 → G m x = G n x :=
      ae_all_iff.mpr (fun m => ae_all_iff.mpr (consistency m))
    intro n
    filter_upwards [hall] with x hx
    intro hxn
    exact hx ⌈‖x‖⌉₊ n (lt_of_le_of_lt (Nat.le_ceil ‖x‖) (lt_add_one _)) hxn
  have hgL : ∀ S : Set E, IsCompact S → MemLp g 2 ((volume : Measure E).restrict S) := by
    intro S hS
    obtain ⟨n, hn⟩ := compact_bound S hS
    have he : g =ᵐ[(volume : Measure E).restrict S] G n := by
      apply (ae_restrict_iff' hS.measurableSet).mpr
      filter_upwards [agreement n] with x hx
      exact fun hxS => hx (hn x hxS)
    exact (memLp_congr_ae he).mpr ((hGL n).restrict S)
  refine ⟨g, ⟨local_integrability f hf, local_integrability g hgL, ?_⟩, hgL⟩
  intro ψ hψ hψc
  obtain ⟨n, hn⟩ := compact_bound (tsupport ψ) hψc.isCompact
  have hleft : (fun x => f x * fderiv ℝ ψ x v) = (fun x => (χ n x * f x) * fderiv ℝ ψ x v) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [hχ_one n x (hn x hx), one_mul]
    · have hz : fderiv ℝ ψ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
      simp only [hz, zero_apply, mul_zero]
  have hright : (fun x => G n x * ψ x) =ᵐ[(volume : Measure E)] (fun x => g x * ψ x) := by
    filter_upwards [agreement n] with x hx
    by_cases hs : x ∈ tsupport ψ
    · rw [hx (hn x hs)]
    · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
  calc
    (∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, (χ n x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E) :=
      congrArg (fun u : E → ℝ => ∫ x, u x ∂(volume : Measure E)) hleft
    _ = -∫ x, G n x * ψ x ∂(volume : Measure E) := (hG n).2.2 ψ hψ hψc
    _ = -∫ x, g x * ψ x ∂(volume : Measure E) := congrArg Neg.neg (integral_congr_ae hright)

end FunctionalInequalities.Analysis

end WeakDerivativeGluing
section CompactWeakDerivativeTesting
section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/-! Common-support smooth approximation and compact rough curl testing, used for
Letwin2607.24164v1 (2.6). These are scalar weak-calculus supports; they do not
establish the moment-law evolution, energy comparison, Theorem2.5 or compact8. -/

/-- A compact rough test with two compact L2 weak derivatives admits smooth tests
with common compact support and simultaneous L2 convergence of those derivatives.
Supporting density component for Letwin2607.24164v1 (2.6). -/
theorem exists_contDiff_compact_weak_deriv_approximation {n : ℕ}
    {η a b : EuclideanSpace ℝ (Fin n) → ℝ} {v w : EuclideanSpace ℝ (Fin n)}
    (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      Function.support (η) ⊆ S ∧ Function.support (a) ⊆ S ∧
      Function.support (b) ⊆ S ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (v)) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (w)) ⊆ S ∧
          MemLp (fun x => fderiv ℝ (θ m) x (v)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          MemLp (fun x => fderiv ℝ (θ m) x (w)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (v) - (a) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (w) - (b) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hm : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφlim : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hφle (m : ℕ) : (φ m).rOut ≤ 1 := by
    dsimp [φ]
    have hm : 0 ≤ (m : ℝ) := by positivity
    have hm' : 0 < (m : ℝ) + 1 := by linarith
    apply (div_le_iff₀ hm').2
    nlinarith
  let Kη : Set (EuclideanSpace ℝ (Fin n)) := cthickening 1 (tsupport η)
  let Ka : Set (EuclideanSpace ℝ (Fin n)) := cthickening 1 (tsupport a)
  let Kb : Set (EuclideanSpace ℝ (Fin n)) := cthickening 1 (tsupport b)
  have hKη : IsCompact Kη := by
    dsimp [Kη]
    exact hηc.isCompact.cthickening
  have hKa : IsCompact Ka := by
    dsimp [Ka]
    exact hac.isCompact.cthickening
  have hKb : IsCompact Kb := by
    dsimp [Kb]
    exact hbc.isCompact.cthickening
  let θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η
  let dvm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a
  let dwm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b
  have hθsmooth (m : ℕ) : ContDiff ℝ ∞ (θ m) := by
    dsimp [θ]
    exact
      ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ m).contDiff_normed (n := (⊤ : ℕ∞))) hηv.1
  have hθcompact (m : ℕ) : HasCompactSupport (θ m) := by
    dsimp [θ]
    exact
      HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ m).hasCompactSupport_normed (μ := volume)) hηc
  have hθsupport (m : ℕ) : Function.support (θ m) ⊆ Kη := by
    change
      Function.support
          ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) ⊆ Kη
    simpa [Kη] using
      (Mollification.support_convolution_subset_cthickening (φ m) (hφle m) η)
  have hdvsupport (m : ℕ) : Function.support (dvm m) ⊆ Ka := by
    change
      Function.support
          ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) ⊆ Ka
    simpa [Ka] using
      (Mollification.support_convolution_subset_cthickening (φ m) (hφle m) a)
  have hdwsupport (m : ℕ) : Function.support (dwm m) ⊆ Kb := by
    change
      Function.support
          ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b) ⊆ Kb
    simpa [Kb] using
      (Mollification.support_convolution_subset_cthickening (φ m) (hφle m) b)
  have hderivv (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (θ m) x v = dvm m x := by
    simpa [θ, dvm] using fderiv_convolution_eq_of_hasWeakDerivAlong hηv (φ m) x
  have hderivw (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (θ m) x w = dwm m x := by
    simpa [θ, dwm] using fderiv_convolution_eq_of_hasWeakDerivAlong hηw (φ m) x
  have hdvactual (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x v) ⊆ Ka := by
    intro x hx
    have hx' : x ∈ Function.support (dvm m) := by
      change dvm m x ≠ 0
      rw [← hderivv m x]
      exact hx
    exact hdvsupport m hx'
  have hdwactual (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x w) ⊆ Kb := by
    intro x hx
    have hx' : x ∈ Function.support (dwm m) := by
      change dwm m x ≠ 0
      rw [← hderivw m x]
      exact hx
    exact hdwsupport m hx'
  have hdvmem (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x v) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h :
        MemLp (dvm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      Mollification.memLp_convolution (φ m) ha2
    rw [show (fun x => fderiv ℝ (θ m) x v) = dvm m by
      funext x
      exact hderivv m x]
    exact h
  have hdwmem (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x w) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h :
        MemLp (dwm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      Mollification.memLp_convolution (φ m) hb2
    rw [show (fun x => fderiv ℝ (θ m) x w) = dwm m by
      funext x
      exact hderivw m x]
    exact h
  have hdvlim :
      Tendsto (fun m => eLpNorm (dvm m - a) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφlim ha2
  have hdwlim :
      Tendsto (fun m => eLpNorm (dwm m - b) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφlim hb2
  have hdvlim' :
      Tendsto
        (fun m => eLpNorm
          (fun x => fderiv ℝ (θ m) x v - a x) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
    have heq :
        (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x v - a x) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (fun m => eLpNorm (dvm m - a) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      funext m
      congr 2
      funext x
      simp only [Pi.sub_apply]
      rw [hderivv m x]
    rw [heq]
    exact hdvlim
  have hdwlim' :
      Tendsto
        (fun m => eLpNorm
          (fun x => fderiv ℝ (θ m) x w - b x) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
    have heq :
        (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x w - b x) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (fun m => eLpNorm (dwm m - b) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      funext m
      congr 2
      funext x
      simp only [Pi.sub_apply]
      rw [hderivw m x]
    rw [heq]
    exact hdwlim
  have hηsupport : Function.support η ⊆ Kη := by
    exact (subset_tsupport η).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  have hasupport : Function.support a ⊆ Ka := by
    exact (subset_tsupport a).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  have hbsupport : Function.support b ⊆ Kb := by
    exact (subset_tsupport b).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  refine ⟨Kη ∪ (Ka ∪ Kb), hKη.union (hKa.union hKb), ?_, ?_, ?_, ?_⟩
  · exact hηsupport.trans (by
      intro x hx
      exact Or.inl hx)
  · exact hasupport.trans (by
      intro x hx
      exact Or.inr (Or.inl hx))
  · exact hbsupport.trans (by
      intro x hx
      exact Or.inr (Or.inr hx))
  · refine ⟨θ, ?_, hdvlim', hdwlim'⟩
    intro m
    exact
      ⟨hθsmooth m, hθcompact m,
        hθsupport m |>.trans (by
          intro x hx
          exact Or.inl hx),
        hdvactual m |>.trans (by
          intro x hx
          exact Or.inr (Or.inl hx)),
        hdwactual m |>.trans (by
          intro x hx
          exact Or.inr (Or.inr hx)),
        hdvmem m, hdwmem m⟩

end FunctionalInequalities.Analysis
end
end CompactWeakDerivativeTesting
section BoundedWeakDerivativeApproximation
open MeasureTheory Filter Set Metric
open scoped ContDiff Convolution Topology
namespace FunctionalInequalities.Analysis

/-! Bounded all-coordinate common-support approximation. -/

/-- The existing normalized-bump estimate supplies one common uniform bound. -/
private theorem norm_normed_convolution_le_three_mul {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x‖ ≤ 3 * C := by
  have hxy (y : EuclideanSpace ℝ (Fin n)) : dist (η y) (η x) ≤ 2 * C := by
    calc
      dist (η y) (η x) = ‖η y - η x‖ := dist_eq_norm _ _
      _ ≤ ‖η y‖ + ‖η x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound y) (hbound x)
      _ = 2 * C := by ring
  have hd := φ.dist_normed_convolution_le hη.aestronglyMeasurable (fun y _ => hxy y)
  calc
    _ ≤ ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x - η x‖ + ‖η x‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 2 * C + C := add_le_add (by simpa only [dist_eq_norm] using hd) (hbound x)
    _ = 3 * C := by ring

/--
Support- and radius-controlled form of the bounded all-coordinate approximation: when the supports
of `η`
and of every `a i` lie in a compact `K`, then for every `ε > 0` the smooth approximants, their
coordinate
derivatives and the original data all live in ONE compact `S ⊆ cthickening ε K` (bump radii at most
`ε`), with
the uniform bound `3 * C`, global L2 coordinate derivatives converging in L2, and full-sequence
almost-everywhere
convergence. Every finite dimension, zero included. Support for Letwin arXiv:2607.24164v1 (2.6). -/
theorem exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin n, Function.support (a i) ⊆ K) {ε : ℝ}
    (hε : 0 < ε)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S ∧
        S ⊆ cthickening ε K ∧
          Function.support η ⊆ S ∧
            (∀ i : Fin n, Function.support (a i) ⊆ S) ∧
              ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
                (∀ m : ℕ,
                    ContDiff ℝ ∞ (θ m) ∧
                      HasCompactSupport (θ m) ∧
                        Function.support (θ m) ⊆ S ∧
                          (∀ x, ‖θ m x‖ ≤ 3 * C) ∧
                            ∀ i : Fin n,
                              Function.support
                                    (fun x =>
                                      fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆
                                  S ∧
                                MemLp
                                  (fun x =>
                                    fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i))
                                  2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                  (∀ i : Fin n,
                      Tendsto
                        (fun m =>
                          eLpNorm
                            (fun x =>
                              fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
                            2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
                        atTop (𝓝 0)) ∧
                    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                      Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by
  have hηc : HasCompactSupport η := HasCompactSupport.of_support_subset_isCompact hK hηK
  have hac (i : Fin n) : HasCompactSupport (a i) :=
    HasCompactSupport.of_support_subset_isCompact hK (haK i)
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (ε / ((m : ℝ) + 1)) / 2
      rOut := ε / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hm : 0 < ε / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφlim : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => ε / ((m : ℝ) + 1)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, mul_zero, one_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε
  have hφle (m : ℕ) : (φ m).rOut ≤ ε := by
    dsimp [φ]
    have hm : 0 ≤ (m : ℝ) := by positivity
    have hm' : 0 < (m : ℝ) + 1 := by linarith
    apply (div_le_iff₀ hm').2
    nlinarith [hε]
  have hφratio : ∀ᶠ m : ℕ in (atTop : Filter ℕ), (φ m).rOut ≤ 2 * (φ m).rIn :=
    Filter.Eventually.of_forall
      (fun m : ℕ => by
        change (ε / ((m : ℝ) + 1)) ≤ 2 * ((ε / ((m : ℝ) + 1)) / 2)
        have h : (2 : ℝ) * ((ε / ((m : ℝ) + 1)) / 2) = ε / ((m : ℝ) + 1) := by ring
        rw [h])
  let Kη : Set (EuclideanSpace ℝ (Fin n)) := cthickening ε (tsupport η)
  let Ki : Fin n → Set (EuclideanSpace ℝ (Fin n)) := fun i => cthickening ε (tsupport (a i))
  have hKη : IsCompact Kη := by
    dsimp [Kη]
    exact hηc.isCompact.cthickening
  have hKi : ∀ i : Fin n, IsCompact (Ki i) := by
    intro i
    dsimp [Ki]
    exact (hac i).isCompact.cthickening
  let S : Set (EuclideanSpace ℝ (Fin n)) := Kη ∪ ⋃ i, Ki i
  have hS : IsCompact S := by
    dsimp [S]
    exact hKη.union (isCompact_iUnion hKi)
  let θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η
  let dvm : Fin n → ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun i m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (a i)
  have hθsmooth (m : ℕ) : ContDiff ℝ ∞ (θ m) := by
    dsimp [θ]
    exact
      ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) ((φ m).contDiff_normed (n := (⊤ : ℕ∞))) hη
  have hθcompact (m : ℕ) : HasCompactSupport (θ m) := by
    dsimp [θ]
    exact
      HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ m).hasCompactSupport_normed (μ := volume)) hηc
  have hθsupport (m : ℕ) : Function.support (θ m) ⊆ Kη := by
    change
      Function.support ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) ⊆ Kη
    simpa [Kη] using
      (Mollification.support_convolution_subset_cthickening_of_rOut_le (φ m) (hφle m) η)
  have hdisupport (i : Fin n) (m : ℕ) : Function.support (dvm i m) ⊆ Ki i := by
    change
      Function.support ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (a i)) ⊆
        Ki i
    simpa [Ki] using
      (Mollification.support_convolution_subset_cthickening_of_rOut_le (φ m) (hφle m) (a i))
  have hderiv (i : Fin n) (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) = dvm i m x := by
    simpa [θ, dvm] using fderiv_convolution_eq_of_hasWeakDerivAlong (hweak i) (φ m) x
  have hdactual (i : Fin n) (m : ℕ) :
    Function.support (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆ Ki i := by
    intro x hx
    have hx' : x ∈ Function.support (dvm i m) := by
      change dvm i m x ≠ 0
      rw [← hderiv i m x]
      exact hx
    exact hdisupport i m hx'
  have hdmem (i : Fin n) (m : ℕ) :
    MemLp (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h : MemLp (dvm i m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      Mollification.memLp_convolution (φ m) (ha2 i)
    rw [show (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) = dvm i m by
        funext x
        exact hderiv i m x]
    exact h
  have hdlim (i : Fin n) :
    Tendsto (fun m => eLpNorm (dvm i m - a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      atTop (𝓝 0) := by
    simpa [dvm] using (Mollification.tendsto_eLpNorm_convolution_sub (φ := φ) hφlim (ha2 i))
  have hdlim' (i : Fin n) :
    Tendsto
      (fun m =>
        eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))))
      atTop (𝓝 0) := by
    have heq :
      (fun m =>
          eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (fun m => eLpNorm (dvm i m - a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      funext m
      congr 2
      funext x
      change fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x = dvm i m x - a i x
      rw [hderiv i m x]
    rw [heq]
    exact hdlim i
  have hηsupport : Function.support η ⊆ Kη := by
    exact
      (subset_tsupport η).trans
        (by
          intro x hx
          exact Metric.self_subset_cthickening _ hx)
  have hasupport (i : Fin n) : Function.support (a i) ⊆ Ki i := by
    exact
      (subset_tsupport (a i)).trans
        (by
          intro x hx
          exact Metric.self_subset_cthickening _ hx)
  have hθbound (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ‖θ m x‖ ≤ 3 * C := by
    simpa [θ] using (norm_normed_convolution_le_three_mul hη hbound (φ m) x)
  have hae :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by
    simpa [θ] using
      (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := φ) hφlim hφratio hη)
  have hηKs : tsupport η ⊆ K := closure_minimal hηK hK.isClosed
  have haKs (i : Fin n) : tsupport (a i) ⊆ K := closure_minimal (haK i) hK.isClosed
  have hSK : S ⊆ cthickening ε K := by
    intro x hx
    rcases hx with hx | hx
    · exact (Metric.cthickening_subset_of_subset ε hηKs) hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact (Metric.cthickening_subset_of_subset ε (haKs i)) hi
  refine ⟨S, hS, hSK, ?_, ?_, ?_⟩
  · exact
      hηsupport.trans
        (by
          intro x hx
          exact Or.inl hx)
  · intro i
    exact
      (hasupport i).trans
        (by
          intro x hx
          exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
  · refine ⟨θ, ?_, ?_, hae⟩
    · intro m
      refine ⟨hθsmooth m, hθcompact m, ?_, hθbound m, ?_⟩
      · exact
          hθsupport m |>.trans
            (by
              intro x hx
              exact Or.inl hx)
      · intro i
        exact
          ⟨(hdactual i m).trans
              (by
                intro x hx
                exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)),
            hdmem i m⟩
    · intro i
      exact hdlim' i

/--
A bounded compact rough test whose weak derivatives along every coordinate are compactly supported
and globally L2 admits ONE smooth compactly supported sequence with supports in one compact set, the
uniform bound `3 * C`, global L2 coordinate derivatives converging in L2 to the given weak
derivatives,
and full-sequence almost-everywhere convergence. Every finite dimension, zero included; no
continuity of
`η` is assumed. Support for Letwin arXiv:2607.24164v1 (2.6). -/
theorem exists_contDiff_compact_bounded_all_weak_deriv_approximation {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S ∧
        Function.support η ⊆ S ∧
          (∀ i : Fin n, Function.support (a i) ⊆ S) ∧
            ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
              (∀ m : ℕ,
                  ContDiff ℝ ∞ (θ m) ∧
                    HasCompactSupport (θ m) ∧
                      Function.support (θ m) ⊆ S ∧
                        (∀ x, ‖θ m x‖ ≤ 3 * C) ∧
                          ∀ i : Fin n,
                            Function.support
                                  (fun x =>
                                    fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆
                                S ∧
                              MemLp
                                (fun x =>
                                  fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i))
                                2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                (∀ i : Fin n,
                    Tendsto
                      (fun m =>
                        eLpNorm
                          (fun x =>
                            fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
                          2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
                      atTop (𝓝 0)) ∧
                  ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                    Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by
  have hK : IsCompact (tsupport η ∪ ⋃ i, tsupport (a i)) :=
    hηc.isCompact.union (isCompact_iUnion fun i => (hac i).isCompact)
  obtain ⟨S, hS, -, hηS, haS, hθ⟩ :=
    exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset hη hbound hK
      ((subset_tsupport η).trans subset_union_left)
      (fun i =>
        (subset_tsupport (a i)).trans
          ((subset_iUnion (fun i => tsupport (a i)) i).trans subset_union_right))
      one_pos hweak ha2
  exact ⟨S, hS, hηS, haS, hθ⟩

end FunctionalInequalities.Analysis
end BoundedWeakDerivativeApproximation
