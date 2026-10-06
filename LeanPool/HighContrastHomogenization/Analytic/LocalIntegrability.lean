/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Analytic.WeightedEnergy
public import LeanPool.HighContrastHomogenization.Analytic.WeakPairing
public import LeanPool.HighContrastHomogenization.Analytic.ClassHonesty

/-!
# High-contrast homogenization: Analytic.LocalIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local integrability of a member of `H¹_{s,loc}(ℝ^d)`

The class `H¹_{s,loc}(ℝ^d)` of `s.introduction`, in the local form read by the
Liouville class `e.random.liouville.growth`, is defined by approximation in the
`H¹_s` norm on every centred ball.  That norm is built from
the `L¹` mass `∫ |u|` and the weighted energy `∫ ∇u · s ∇u`, both taken as lower
Lebesgue integrals of nonnegative integrands.

This module extracts from the definition the integrability facts that the
weak-gradient relation needs in order to be an identity between convergent
integrals.  The mechanism is the `L¹` term: convergence to `0` in `ℝ≥0∞` forces
`(∫⁻ |w n - v|)²` to be eventually finite, so `∫⁻ |w n - v| < ∞` for some `n`;
the smooth approximant `w n` is bounded on the bounded ball; hence
`∫⁻ |v| < ∞` there.

The `L¹` half of that statement needs no measurability input at all, because the
lower Lebesgue integral is defined for every function.  Upgrading it to genuine
integrability does need a measurability hypothesis, and that hypothesis is not
removable: the lower Lebesgue integral is a supremum over simple functions
*below* the integrand and is therefore blind to a perturbation supported on a set
of inner measure zero, while the Bochner integrals compared by the weak-gradient
relation value a non-integrable integrand at `0`.  A function invisible to both
would satisfy the defining conditions without being almost everywhere strongly
measurable, hence without being integrable on any ball.  In the formalization the
measurability is supplied by the class itself, which carries it as part of its
definition; the lemmas here are stated with it explicit so that the dependence is
visible.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## The `L¹` mass of a member of the local class -/

/-- Along a sequence whose `H¹_s` distance to the pair tends to `0`, some
approximant is at finite `L¹` distance. -/
theorem exists_lintegral_ofReal_abs_sub_ne_top {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} {w : ℕ → Vec d → ℝ}
    (htend : _root_.Filter.Tendsto
      (fun n => h1sNormSqOn b V (fun x => w n x - u x)
        (fun x => smoothGrad (w n) x - Du x)) _root_.Filter.atTop (nhds 0)) :
    ∃ n : ℕ, (∫⁻ x in V, ENNReal.ofReal |w n x - u x| ∂volume) ≠ ⊤ := by
  obtain ⟨n, hn⟩ :=
    (htend.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)).exists
  refine ⟨n, ?_⟩
  intro htop
  have hle : (∫⁻ x in V, ENNReal.ofReal |w n x - u x| ∂volume) ^ 2 ≤
      h1sNormSqOn b V (fun x => w n x - u x)
        (fun x => smoothGrad (w n) x - Du x) := by
    simp only [h1sNormSqOn]
    exact le_self_add
  rw [htop, ENNReal.top_pow (by norm_num)] at hle
  exact absurd (lt_of_le_of_lt hle hn) (not_lt.mpr le_top)

/-- A continuous function has finite `L¹` mass on a bounded set. -/
theorem lintegral_ofReal_abs_ne_top_of_isBounded {V : Set (Vec d)}
    (hV : Bornology.IsBounded V) {g : Vec d → ℝ} (hg : Continuous g) :
    (∫⁻ x in V, ENNReal.ofReal |g x| ∂volume) ≠ ⊤ := by
  have hcl : IsCompact (closure V) := hV.isCompact_closure
  obtain ⟨C, hC⟩ := hcl.exists_bound_of_continuousOn hg.continuousOn
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C * volume V) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV.measure_lt_top.ne
  · rw [← setLIntegral_const V (ENNReal.ofReal C)]
    refine lintegral_mono_ae ?_
    have hmem : ∀ᵐ x ∂(volume.restrict V : Measure (Vec d)), x ∈ closure V :=
      (ae_restrict_mem isClosed_closure.measurableSet).filter_mono
        (ae_mono (Measure.restrict_mono subset_closure le_rfl))
    filter_upwards [hmem] with x hx
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hC x hx)

/-- The `L¹` triangle step. -/
theorem lintegral_ofReal_abs_ne_top_of_sub {V : Set (Vec d)} {g h : Vec d → ℝ}
    (hgmeas : AEMeasurable (fun x => ENNReal.ofReal |g x|) (volume.restrict V))
    (hg : (∫⁻ x in V, ENNReal.ofReal |g x| ∂volume) ≠ ⊤)
    (hd : (∫⁻ x in V, ENNReal.ofReal |g x - h x| ∂volume) ≠ ⊤) :
    (∫⁻ x in V, ENNReal.ofReal |h x| ∂volume) ≠ ⊤ := by
  have hpt : ∀ x : Vec d, ENNReal.ofReal |h x| ≤
      ENNReal.ofReal |g x| + ENNReal.ofReal |g x - h x| := by
    intro x
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have htri := abs_add_le (g x) (-(g x - h x))
    rw [abs_neg] at htri
    have hid : g x + -(g x - h x) = h x := by ring
    rwa [hid] at htri
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left' hgmeas]
  exact ENNReal.add_ne_top.2 ⟨hg, hd⟩

/-- **The `L¹` half of the local class is honest**, with no measurability input
at all: the *lower* Lebesgue integral of `|v|` over any centred ball is
finite. -/
theorem lintegral_ofReal_abs_ne_top_of_memH1sLoc {b : CoeffField d} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (hv : MemH1sLoc b v Dv) {R : ℝ} (hR : 0 < R) :
    (∫⁻ x in euclideanBall d R, ENNReal.ofReal |v x| ∂volume) ≠ ⊤ := by
  obtain ⟨-, w, hw, htend⟩ := hv.2 R hR
  obtain ⟨n, hn⟩ := exists_lintegral_ofReal_abs_sub_ne_top htend
  have hwc : Continuous (w n) := (hw n).continuous
  refine lintegral_ofReal_abs_ne_top_of_sub (g := w n) (h := v) ?_
    (lintegral_ofReal_abs_ne_top_of_isBounded (isBounded_euclideanBall d hR) hwc) hn
  exact (ENNReal.measurable_ofReal.comp hwc.abs.measurable).aemeasurable

/-- A pair of the local class has an `L¹` representative on every centred ball.

The measurability hypothesis `hvmeas` is **not** removable.  Membership in
`MemH1sLoc` is blind to a perturbation of `v` by the indicator of a set of inner
measure zero — the lower Lebesgue integral does not see it, and the Bochner
integrals of `HasWeakGradientOn` fall into the branch that values a
non-integrable integrand at `0` — so membership alone does not make `v` almost
everywhere strongly measurable. -/
theorem integrableOn_of_memH1sLoc {b : CoeffField d} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (h : MemH1sLoc b v Dv) {R : ℝ} (hR : 0 < R)
    (hvmeas : AEStronglyMeasurable v (volume.restrict (euclideanBall d R))) :
    IntegrableOn v (euclideanBall d R) volume := by
  refine ⟨hvmeas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  exact lt_of_le_of_ne le_top (lintegral_ofReal_abs_ne_top_of_memH1sLoc h hR)

/-! ## Components of a square-integrable field, and bounds on a local test -/

/-- A square-integrable field has integrable components on a finite measure
set. -/
theorem integrableOn_apply_of_integrableOn_vecNormSq {V : Set (Vec d)}
    (hVfin : volume V ≠ ⊤) {F : Vec d → Vec d}
    (hFmeas : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hF : IntegrableOn (fun x => vecNormSq (F x)) V volume) (j : Fin d) :
    IntegrableOn (fun x => F x j) V volume := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  refine Integrable.mono' (g := fun x => (1 + vecNormSq (F x)) / 2)
    (((integrable_const (1 : ℝ)).add hF).div_const 2) (hFmeas j) ?_
  filter_upwards with x
  have h1 : (F x j) ^ 2 ≤ vecNormSq (F x) := sq_apply_le_vecNormSq (F x) j
  have h2 : |F x j| ≤ (1 + (F x j) ^ 2) / 2 := by
    nlinarith only [sq_nonneg (|F x j| - 1), sq_abs (F x j)]
  rw [Real.norm_eq_abs]
  linarith only [h1, h2]

/-- A local test is uniformly bounded. -/
theorem exists_bound_of_isLocalTest {V : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsLocalTest V φ) : ∃ C : ℝ, ∀ x, |φ x| ≤ C := by
  have hK : IsCompact (tsupport φ) := hφ.hasCompactSupport
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn hφ.contDiff.continuous.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport φ
  · exact le_trans (by simpa only [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact le_max_right _ _

/-- The coordinate gradient of a local test is uniformly bounded. -/
theorem exists_bound_smoothGrad_of_isLocalTest {V : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsLocalTest V φ) (i : Fin d) : ∃ B : ℝ, ∀ x, |smoothGrad φ x i| ≤ B := by
  have hcont : Continuous (smoothGrad φ) := continuous_smoothGrad hφ.contDiff
  have hK : IsCompact (tsupport φ) := hφ.hasCompactSupport
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport φ
  · refine le_trans ?_ (le_max_left _ _)
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (smoothGrad φ x) i).trans (hB x hx)
  · have hzero : smoothGrad φ x = 0 := smoothGrad_eq_zero_of_notMem_tsupport hx
    rw [hzero]
    simp

end

end HighContrast
end HCPolySupport
