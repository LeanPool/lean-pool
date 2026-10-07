/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality4
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Interchanging a parameter limit with the outer time integral

The comparison energy inequality `eq:aniso:comparison:positive:energy` is assembled from a
per-slice statement: for each time `s` a regularization parameter `kap` is sent to `0⁺`, and the
resulting slice limits must then be integrated over the time interval `[a, b]`. Carrying out that
last step means moving the limit across `∫ s in a..b, ·`, which is dominated convergence along the
filter `𝓝[>] 0` rather than along a sequence.

Mathlib supplies the two ingredients —
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
and its interval counterpart `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` —
but both are stated with hypotheses restricted to the half-open interval `Set.uIoc a b`, while every
slice estimate in this development is produced on the closed interval `Set.Icc a b`. Bridging
the two
by hand at each call site is exactly the friction this file removes.

## Main results

* `tendsto_intervalIntegral_of_tendsto_of_dominated_filter` — the general form: along any countably
  generated filter `l`, eventual measurability on `Set.Icc a b`, an almost-everywhere slice limit,
  an eventual almost-everywhere domination `|f n s| ≤ G s` by an integrable `G`, and `a ≤ b` give
  `∫ s in a..b, f n s → ∫ s in a..b, g s`.
* `tendsto_intervalIntegral_of_tendsto_of_dominated` — the specialization to `kap ↓ 0`, the shape
  the comparison argument consumes.
* `tendsto_intervalIntegral_of_tendsto_of_dominated_atTop` — the sequential specialization.
* `tendsto_intervalIntegral_of_tendsto_of_dominated_const` — the frequent case of a constant
  dominating function, whose integrability on a bounded interval is automatic.
* `tendsto_intervalIntegral_of_tendsto_of_dominated_nonneg` — the one-sided bound `0 ≤ f kap s ≤
G s`
  in place of the absolute-value bound, which is how the quadratic terms of the energy identity
  present themselves.
* `tendsto_intervalIntegral_of_tendsto_zero_of_dominated` — the vanishing corollary, for the error
  terms that are shown to converge to `0` slice by slice.
* `tendsto_setIntegral_Icc_of_tendsto_of_dominated` and
  `tendsto_setIntegral_Icc_of_tendsto_of_dominated_const` — the same conclusions phrased for the set
  integral `∫ s in Set.Icc a b, ·`.

The two small conversion lemmas `intervalIntegrable_of_integrableOn_Icc` and
`intervalIntegral_eq_setIntegral_Icc` record the closed/half-open interval bridge separately, since
they are useful on their own.
-/

public section

open MeasureTheory Set Filter Topology
open CKN


noncomputable section

namespace CIV

/-! ### Closed versus half-open interval -/

/-- A function integrable on the closed interval `Set.Icc a b` is interval integrable on `a..b`.
The closed interval is the domain on which the slice estimates of the comparison argument are
produced, while `IntervalIntegrable` is phrased through `Set.uIoc a b`. -/
theorem intervalIntegrable_of_integrableOn_Icc {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG : IntegrableOn G (Set.Icc a b) volume) : IntervalIntegrable G volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact hG.mono_set Set.Ioc_subset_Icc_self

/-- The interval integral over `a..b` agrees with the set integral over the closed interval
`Set.Icc a b` whenever `a ≤ b`: the endpoint `a` is a null set for Lebesgue measure. No
integrability hypothesis is needed, both sides being `0` when the integrand is not integrable. -/
theorem intervalIntegral_eq_setIntegral_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, f s) = ∫ s in Set.Icc a b, f s := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-! ### Dominated convergence along a filter -/

/-- Dominated convergence for the interval integral, with every hypothesis stated on the **closed**
interval `Set.Icc a b` and along an arbitrary countably generated filter `l`.

Measurability and the dominating bound are only required *eventually* along `l`, which is what the
underlying Mathlib lemma provides and what the applications supply: a bound valid for all small
positive parameters, not for every parameter. -/
theorem tendsto_intervalIntegral_of_tendsto_of_dominated_filter {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → ℝ → ℝ} {g G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmeas : ∀ᶠ n in l, AEStronglyMeasurable (f n) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun n => f n s) l (nhds (g s)))
    (hdom : ∀ᶠ n in l, ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), |f n s| ≤ G s)
    (hG : IntegrableOn G (Set.Icc a b) volume) :
    Tendsto (fun n => ∫ s in a..b, f n s) l (nhds (∫ s in a..b, g s)) := by
  have huioc : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  have hsub : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have hGint : IntervalIntegrable G volume a b := intervalIntegrable_of_integrableOn_Icc hab hG
  have hFmeas : ∀ᶠ n in l, AEStronglyMeasurable (f n) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [hmeas] with n hn
    rw [huioc]
    exact hn.mono_set hsub
  have hbound : ∀ᶠ n in l, ∀ᵐ s ∂volume, s ∈ Set.uIoc a b → ‖f n s‖ ≤ G s := by
    filter_upwards [hdom] with n hn
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at hn
    filter_upwards [hn] with s hs hsmem
    rw [huioc] at hsmem
    rw [Real.norm_eq_abs]
    exact hs (hsub hsmem)
  have hptlim : ∀ᵐ s ∂volume, s ∈ Set.uIoc a b →
      Tendsto (fun n => f n s) l (nhds (g s)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at hlim
    filter_upwards [hlim] with s hs hsmem
    rw [huioc] at hsmem
    exact hs (hsub hsmem)
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence G hFmeas hbound hGint
    hptlim

/-- Dominated convergence for the interval integral as the regularization parameter `kap` tends to
`0` from the right. This is the form the comparison energy argument consumes: the slice limits are
known for almost every time `s`, the slice bound `|f kap s| ≤ G s` holds for all small `kap > 0`,
and `G` is integrable over the time interval. -/
theorem tendsto_intervalIntegral_of_tendsto_of_dominated {f : ℝ → ℝ → ℝ} {g G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hmeas : ∀ kap : ℝ, AEStronglyMeasurable (f kap) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun kap : ℝ => f kap s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g s)))
    (hdom : ∀ᶠ kap in nhdsWithin 0 (Set.Ioi (0:ℝ)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), |f kap s| ≤ G s)
    (hG : IntegrableOn G (Set.Icc a b) volume) :
    Tendsto (fun kap : ℝ => ∫ s in a..b, f kap s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in a..b, g s)) :=
  tendsto_intervalIntegral_of_tendsto_of_dominated_filter hab
    (Filter.Eventually.of_forall hmeas) hlim hdom hG

/-- The sequential form of `tendsto_intervalIntegral_of_tendsto_of_dominated`: a sequence of
integrands dominated by a single integrable `G` on `Set.Icc a b` may be passed to the limit under
the interval integral. -/
theorem tendsto_intervalIntegral_of_tendsto_of_dominated_atTop {f : ℕ → ℝ → ℝ} {g G : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (f n) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun n : ℕ => f n s) atTop (nhds (g s)))
    (hdom : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), |f n s| ≤ G s)
    (hG : IntegrableOn G (Set.Icc a b) volume) :
    Tendsto (fun n : ℕ => ∫ s in a..b, f n s) atTop (nhds (∫ s in a..b, g s)) :=
  tendsto_intervalIntegral_of_tendsto_of_dominated_filter hab
    (Filter.Eventually.of_forall hmeas) hlim (Filter.Eventually.of_forall hdom) hG

/-- Dominated convergence with a **constant** dominating function. On a bounded interval a constant
is automatically integrable, so no integrability hypothesis survives: a uniform slice bound
`|f kap s| ≤ C` valid for all small `kap > 0` suffices. -/
theorem tendsto_intervalIntegral_of_tendsto_of_dominated_const {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    {a b C : ℝ} (hab : a ≤ b)
    (hmeas : ∀ kap : ℝ, AEStronglyMeasurable (f kap) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun kap : ℝ => f kap s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g s)))
    (hdom : ∀ᶠ kap in nhdsWithin 0 (Set.Ioi (0:ℝ)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), |f kap s| ≤ C) :
    Tendsto (fun kap : ℝ => ∫ s in a..b, f kap s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in a..b, g s)) := by
  have hC : IntegrableOn (fun _ : ℝ => C) (Set.Icc a b) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact tendsto_intervalIntegral_of_tendsto_of_dominated hab hmeas hlim hdom hC

/-- Dominated convergence for a nonnegative integrand, where the domination is naturally a one-sided
bound `0 ≤ f kap s ≤ G s` rather than a bound on the absolute value. The squared quantities of the
energy identity arrive in exactly this shape. -/
theorem tendsto_intervalIntegral_of_tendsto_of_dominated_nonneg {f : ℝ → ℝ → ℝ} {g G : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (hmeas : ∀ kap : ℝ, AEStronglyMeasurable (f kap) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun kap : ℝ => f kap s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g s)))
    (hdom : ∀ᶠ kap in nhdsWithin 0 (Set.Ioi (0:ℝ)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), 0 ≤ f kap s ∧ f kap s ≤ G s)
    (hG : IntegrableOn G (Set.Icc a b) volume) :
    Tendsto (fun kap : ℝ => ∫ s in a..b, f kap s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in a..b, g s)) := by
  refine tendsto_intervalIntegral_of_tendsto_of_dominated hab hmeas hlim ?_ hG
  filter_upwards [hdom] with kap hkap
  filter_upwards [hkap] with s hs
  rw [abs_of_nonneg hs.1]
  exact hs.2

/-- The vanishing corollary: if the slice integrand tends to `0` for almost every time `s` and is
dominated by an integrable `G`, then the time integral itself tends to `0`. This is the shape the
error terms of the comparison argument take. -/
theorem tendsto_intervalIntegral_of_tendsto_zero_of_dominated {f : ℝ → ℝ → ℝ} {G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hmeas : ∀ kap : ℝ, AEStronglyMeasurable (f kap) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun kap : ℝ => f kap s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hdom : ∀ᶠ kap in nhdsWithin 0 (Set.Ioi (0:ℝ)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), |f kap s| ≤ G s)
    (hG : IntegrableOn G (Set.Icc a b) volume) :
    Tendsto (fun kap : ℝ => ∫ s in a..b, f kap s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmain := tendsto_intervalIntegral_of_tendsto_of_dominated (g := fun _ : ℝ => (0 : ℝ))
    hab hmeas hlim hdom hG
  simpa using hmain

/-! ### The same limits for the set integral over `Set.Icc a b` -/

/-- The conclusion of `tendsto_intervalIntegral_of_tendsto_of_dominated` phrased for the set
integral over the closed interval, which is how the time integral is written when it is produced by
a slice-wise construction rather than by the fundamental theorem of calculus. -/
theorem tendsto_setIntegral_Icc_of_tendsto_of_dominated {f : ℝ → ℝ → ℝ} {g G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hmeas : ∀ kap : ℝ, AEStronglyMeasurable (f kap) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun kap : ℝ => f kap s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g s)))
    (hdom : ∀ᶠ kap in nhdsWithin 0 (Set.Ioi (0:ℝ)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), |f kap s| ≤ G s)
    (hG : IntegrableOn G (Set.Icc a b) volume) :
    Tendsto (fun kap : ℝ => ∫ s in Set.Icc a b, f kap s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in Set.Icc a b, g s)) := by
  have hmain := tendsto_intervalIntegral_of_tendsto_of_dominated hab hmeas hlim hdom hG
  rw [intervalIntegral_eq_setIntegral_Icc (f := g) hab] at hmain
  refine hmain.congr fun kap => ?_
  exact intervalIntegral_eq_setIntegral_Icc (f := f kap) hab

/-- The constant-dominating-function form of `tendsto_setIntegral_Icc_of_tendsto_of_dominated`: on a
bounded time interval a uniform slice bound alone licenses the interchange. -/
theorem tendsto_setIntegral_Icc_of_tendsto_of_dominated_const {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    {a b C : ℝ} (hab : a ≤ b)
    (hmeas : ∀ kap : ℝ, AEStronglyMeasurable (f kap) (volume.restrict (Set.Icc a b)))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun kap : ℝ => f kap s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g s)))
    (hdom : ∀ᶠ kap in nhdsWithin 0 (Set.Ioi (0:ℝ)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), |f kap s| ≤ C) :
    Tendsto (fun kap : ℝ => ∫ s in Set.Icc a b, f kap s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in Set.Icc a b, g s)) := by
  have hC : IntegrableOn (fun _ : ℝ => C) (Set.Icc a b) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact tendsto_setIntegral_Icc_of_tendsto_of_dominated hab hmeas hlim hdom hC

end CIV
