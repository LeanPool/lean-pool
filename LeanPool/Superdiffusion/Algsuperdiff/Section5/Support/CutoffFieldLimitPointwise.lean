/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ComparatorComparison
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CutoffFieldLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedFinite

/-!
# CutoffFieldLimitPointwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Pointwise bounds survive the `L²` limit

A bound valid for every truncation `a_L` with `L ≥ m` is a bound on a family
whose `L²` limit is the full-field solution.  Two elementary transfers make it a
bound on the limit.

*From `L²` convergence to an almost-everywhere bound.*  If `f_L ≤ c` almost
everywhere for all large `L` and `‖f_L - g‖_{L²} → 0`, then `g ≤ c` almost
everywhere: the positive part `(g - c)_+` satisfies `(g - c)_+ ≤ |f_L - g|`
almost everywhere, so its `L²` norm is at most `‖f_L - g‖_{L²} → 0`, and a
nonnegative function of vanishing `L²` norm vanishes almost everywhere.

*From an almost-everywhere bound to a pointwise bound.*  On an open set, a
function continuous there that satisfies a bound away from a null set satisfies
it at every point.  This is `le_of_ae_le_of_continuousOn`, applied against a
constant.

Together: a bound holding for the continuous representatives of the truncated
solutions, uniformly in `L`, holds at every point of the cube for the continuous
representative of the full-field solution.

## Main results

* `ae_le_of_tendsto_l2`, `ae_ge_of_tendsto_l2` — the almost-everywhere transfer.
* `le_on_open_subset_of_tendsto_l2`, `ge_on_open_subset_of_tendsto_l2` — the two
  combined, on an open subset of the cube, for continuous representatives.

## References

* ABK26, the passage `L → ∞` from the truncated fields `a_L` to `a`.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. An `L²` limit inherits an almost-everywhere bound -/

private theorem memLp_posPart_sub_const {U : Set (Vec d)} (hUfin : volume U ≠ ⊤)
    {g : Vec d → ℝ} (hg : MemLp g 2 (volume.restrict U)) (c : ℝ) :
    MemLp (fun x => max (g x - c) 0) 2 (volume.restrict U) := by
  have : IsFiniteMeasure (volume.restrict U) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hUfin
  have hsub : MemLp (fun x => g x - c) 2 (volume.restrict U) := hg.sub (memLp_const c)
  refine MemLp.of_le hsub (hsub.aestronglyMeasurable.sup aestronglyMeasurable_const)
    (Filter.Eventually.of_forall fun x => ?_)
  rcases le_or_gt (g x - c) 0 with h | h
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, max_eq_right h, abs_zero]
    exact abs_nonneg _
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, max_eq_left h.le]

/-- **An almost-everywhere upper bound passes to the `L²` limit.** -/
theorem ae_le_of_tendsto_l2 {U : Set (Vec d)} (hUfin : volume U ≠ ⊤)
    {f : ℤ → Vec d → ℝ} {g : Vec d → ℝ} {c : ℝ}
    (hf : ∀ L : ℤ, MemLp (f L) 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (hbound : ∀ᶠ L : ℤ in atTop, ∀ᵐ x ∂(volume.restrict U), f L x ≤ c)
    (hlim : Tendsto
      (fun L : ℤ => Real.sqrt (∫ x in U, (f L x - g x) ^ (2 : ℕ) ∂volume)) atTop (𝓝 0)) :
    ∀ᵐ x ∂(volume.restrict U), g x ≤ c := by
  have hhmem : MemLp (fun x => max (g x - c) 0) 2 (volume.restrict U) :=
    memLp_posPart_sub_const hUfin hg c
  have hhint : IntegrableOn (fun x => max (g x - c) 0 ^ (2 : ℕ)) U volume :=
    hhmem.integrable_sq
  have hstep : ∀ᶠ L : ℤ in atTop,
      Real.sqrt (∫ x in U, max (g x - c) 0 ^ (2 : ℕ) ∂volume) ≤
        Real.sqrt (∫ x in U, (f L x - g x) ^ (2 : ℕ) ∂volume) := by
    filter_upwards [hbound] with L hL
    refine Real.sqrt_le_sqrt ?_
    have hdiff : IntegrableOn (fun x => (f L x - g x) ^ (2 : ℕ)) U volume :=
      ((hf L).sub hg).integrable_sq
    refine integral_mono_ae hhint hdiff ?_
    filter_upwards [hL] with x hx
    change max (g x - c) 0 ^ (2 : ℕ) ≤ (f L x - g x) ^ (2 : ℕ)
    rcases le_or_gt (g x - c) 0 with hle | hlt
    · rw [max_eq_right hle, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
    · rw [max_eq_left hlt.le]
      have habs : |g x - c| ≤ |f L x - g x| := by
        rw [abs_of_nonneg hlt.le, abs_sub_comm]
        exact le_trans (by linarith only [hx]) (le_abs_self (g x - f L x))
      calc (g x - c) ^ (2 : ℕ) = |g x - c| ^ (2 : ℕ) := by rw [sq_abs]
        _ ≤ |f L x - g x| ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = (f L x - g x) ^ (2 : ℕ) := by rw [sq_abs]
  have hle0 : Real.sqrt (∫ x in U, max (g x - c) 0 ^ (2 : ℕ) ∂volume) ≤ 0 :=
    ge_of_tendsto hlim hstep
  have hnn : (0 : ℝ) ≤ ∫ x in U, max (g x - c) 0 ^ (2 : ℕ) ∂volume :=
    integral_nonneg fun x => by positivity
  have hzero : (∫ x in U, max (g x - c) 0 ^ (2 : ℕ) ∂volume) = 0 := by
    refine le_antisymm ?_ hnn
    by_contra hcon
    push Not at hcon
    exact absurd hle0 (not_le.2 (Real.sqrt_pos.2 hcon))
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hhint).1 hzero
  filter_upwards [hae] with x hx
  have hsq : max (g x - c) 0 ^ (2 : ℕ) = 0 := hx
  have hposPart : (0 : ℝ) ≤ max (g x - c) 0 := le_max_right _ _
  have hzero' : max (g x - c) 0 ≤ 0 := by nlinarith only [hsq, hposPart]
  have hleft : g x - c ≤ max (g x - c) 0 := le_max_left _ _
  linarith only [hleft, hzero']

/-- **An almost-everywhere lower bound passes to the `L²` limit.** -/
theorem ae_ge_of_tendsto_l2 {U : Set (Vec d)} (hUfin : volume U ≠ ⊤)
    {f : ℤ → Vec d → ℝ} {g : Vec d → ℝ} {c : ℝ}
    (hf : ∀ L : ℤ, MemLp (f L) 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (hbound : ∀ᶠ L : ℤ in atTop, ∀ᵐ x ∂(volume.restrict U), c ≤ f L x)
    (hlim : Tendsto
      (fun L : ℤ => Real.sqrt (∫ x in U, (f L x - g x) ^ (2 : ℕ) ∂volume)) atTop (𝓝 0)) :
    ∀ᵐ x ∂(volume.restrict U), c ≤ g x := by
  have hlim' : Tendsto
      (fun L : ℤ => Real.sqrt (∫ x in U, (-f L x - -g x) ^ (2 : ℕ) ∂volume))
      atTop (𝓝 0) := by
    refine hlim.congr fun L => ?_
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change (f L x - g x) ^ (2 : ℕ) = (-f L x - -g x) ^ (2 : ℕ)
    ring
  have hbound' : ∀ᶠ L : ℤ in atTop,
      ∀ᵐ x ∂(volume.restrict U), (fun z => -f L z) x ≤ -c := by
    filter_upwards [hbound] with L hL
    filter_upwards [hL] with x hx using by linarith only [hx]
  have hae := ae_le_of_tendsto_l2 (f := fun L z => -f L z) (g := fun z => -g z)
    (c := -c) hUfin (fun L => (hf L).neg) hg.neg hbound' hlim'
  filter_upwards [hae] with x hx using by linarith only [hx]

/-! ## 2. The transfer to the continuous representatives on the cube -/

private theorem memLp_toFun_restrict {y : Vec d} {n : ℤ} {V : Set (Vec d)}
    (hV : V ⊆ cubeSetAt y n) (u : H1Function (cubeSetAt y n)) :
    MemLp u.toFun 2 (volume.restrict V) :=
  u.memL2.mono_measure (Measure.restrict_mono hV le_rfl)

private theorem tendsto_sqrt_setIntegral_mono {y : Vec d} {n : ℤ} {V : Set (Vec d)}
    (hV : V ⊆ cubeSetAt y n)
    {u : ℤ → H1Function (cubeSetAt y n)} {v : H1Function (cubeSetAt y n)}
    (hint : ∀ L : ℤ,
      IntegrableOn (fun x => ((u L).toFun x - v.toFun x) ^ (2 : ℕ)) (cubeSetAt y n) volume)
    (hlim : Tendsto (fun L : ℤ => Real.sqrt
      (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume)) atTop (𝓝 0)) :
    Tendsto (fun L : ℤ => Real.sqrt
      (∫ x in V, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume)) atTop (𝓝 0) := by
  refine squeeze_zero (fun L => Real.sqrt_nonneg _) (fun L => ?_) hlim
  refine Real.sqrt_le_sqrt ?_
  exact setIntegral_mono_set (hint L) (Filter.Eventually.of_forall fun x => by positivity)
    (LE.le.eventuallyLE hV)

/-- **A uniform bound on the truncated solutions' representatives passes to the
representative of the `L²` limit**, at every point of an open subset of the
cube. -/
theorem le_on_open_subset_of_tendsto_l2 {y : Vec d} {n : ℤ} {V : Set (Vec d)}
    (hVopen : IsOpen V) (hV : V ⊆ cubeSetAt y n)
    {u : ℤ → H1Function (cubeSetAt y n)} {uRep : ℤ → Vec d → ℝ}
    {v : H1Function (cubeSetAt y n)} {vRep : Vec d → ℝ} {c : ℝ}
    (hu : ∀ L : ℤ, IsCubeRepresentative y n (u L) (uRep L))
    (hv : IsCubeRepresentative y n v vRep)
    (hbound : ∀ᶠ L : ℤ in atTop, ∀ x ∈ V, uRep L x ≤ c)
    (hlim : Tendsto (fun L : ℤ => Real.sqrt
      (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume)) atTop (𝓝 0))
    {x : Vec d} (hx : x ∈ V) : vRep x ≤ c := by
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hVfin : volume V ≠ ⊤ :=
    ne_top_of_le_ne_top ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne
      (measure_mono hV)
  have hmono : volume.restrict V ≤ volume.restrict (cubeSetAt y n) :=
    Measure.restrict_mono hV le_rfl
  have hint : ∀ L : ℤ,
      IntegrableOn (fun x => ((u L).toFun x - v.toFun x) ^ (2 : ℕ)) (cubeSetAt y n) volume :=
    fun L => ((u L).memL2.sub v.memL2).integrable_sq
  have hlimV := tendsto_sqrt_setIntegral_mono hV hint hlim
  have haeV : ∀ᶠ L : ℤ in atTop, ∀ᵐ z ∂(volume.restrict V), (u L).toFun z ≤ c := by
    filter_upwards [hbound] with L hL
    have hrep : uRep L =ᵐ[volume.restrict V] (u L).toFun := ae_mono hmono (hu L).1
    filter_upwards [hrep, (ae_restrict_iff' hVmeas).2
      (Filter.Eventually.of_forall fun z (hz : z ∈ V) => hz)] with z hz hzV
    rw [← hz]
    exact hL z hzV
  have hae : ∀ᵐ z ∂(volume.restrict V), v.toFun z ≤ c :=
    ae_le_of_tendsto_l2 hVfin (fun L => memLp_toFun_restrict hV (u L))
      (memLp_toFun_restrict hV v) haeV hlimV
  have haeRep : ∀ᵐ z ∂(volume.restrict V), vRep z ≤ c := by
    filter_upwards [hae, ae_mono hmono hv.1] with z hz hzrep
    rw [hzrep]
    exact hz
  exact le_of_ae_le_of_continuousOn hVopen haeRep (hv.2.mono hV) continuousOn_const x hx

/-- The lower-bound form of the same transfer. -/
theorem ge_on_open_subset_of_tendsto_l2 {y : Vec d} {n : ℤ} {V : Set (Vec d)}
    (hVopen : IsOpen V) (hV : V ⊆ cubeSetAt y n)
    {u : ℤ → H1Function (cubeSetAt y n)} {uRep : ℤ → Vec d → ℝ}
    {v : H1Function (cubeSetAt y n)} {vRep : Vec d → ℝ} {c : ℝ}
    (hu : ∀ L : ℤ, IsCubeRepresentative y n (u L) (uRep L))
    (hv : IsCubeRepresentative y n v vRep)
    (hbound : ∀ᶠ L : ℤ in atTop, ∀ x ∈ V, c ≤ uRep L x)
    (hlim : Tendsto (fun L : ℤ => Real.sqrt
      (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume)) atTop (𝓝 0))
    {x : Vec d} (hx : x ∈ V) : c ≤ vRep x := by
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hVfin : volume V ≠ ⊤ :=
    ne_top_of_le_ne_top ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne
      (measure_mono hV)
  have hmono : volume.restrict V ≤ volume.restrict (cubeSetAt y n) :=
    Measure.restrict_mono hV le_rfl
  have hint : ∀ L : ℤ,
      IntegrableOn (fun x => ((u L).toFun x - v.toFun x) ^ (2 : ℕ)) (cubeSetAt y n) volume :=
    fun L => ((u L).memL2.sub v.memL2).integrable_sq
  have hlimV := tendsto_sqrt_setIntegral_mono hV hint hlim
  have haeV : ∀ᶠ L : ℤ in atTop, ∀ᵐ z ∂(volume.restrict V), c ≤ (u L).toFun z := by
    filter_upwards [hbound] with L hL
    have hrep : uRep L =ᵐ[volume.restrict V] (u L).toFun := ae_mono hmono (hu L).1
    filter_upwards [hrep, (ae_restrict_iff' hVmeas).2
      (Filter.Eventually.of_forall fun z (hz : z ∈ V) => hz)] with z hz hzV
    rw [← hz]
    exact hL z hzV
  have hae : ∀ᵐ z ∂(volume.restrict V), c ≤ v.toFun z :=
    ae_ge_of_tendsto_l2 hVfin (fun L => memLp_toFun_restrict hV (u L))
      (memLp_toFun_restrict hV v) haeV hlimV
  have haeRep : ∀ᵐ z ∂(volume.restrict V), c ≤ vRep z := by
    filter_upwards [hae, ae_mono hmono hv.1] with z hz hzrep
    rw [hzrep]
    exact hz
  exact le_of_ae_le_of_continuousOn hVopen haeRep continuousOn_const (hv.2.mono hV) x hx

end

end Algsuperdiff.Section5.Support
