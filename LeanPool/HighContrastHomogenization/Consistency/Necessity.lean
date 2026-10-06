/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Analytic.ClassHonesty
public import LeanPool.HighContrastHomogenization.Analytic.LocalIntegrability
public import LeanPool.HighContrastHomogenization.Analytic.WeakGradientClosure

/-!
# High-contrast homogenization: Consistency.Necessity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# What the measurability condition of the local class `MemH1sLoc` excludes

This module checks `MemH1sLoc`, the local form of the coefficient Sobolev space
of `s.introduction`.  `MemH1sLoc` asks of a pair
`(v, Dv)` that it be measurable and that, on every centred Euclidean ball, it be
a weak-gradient pair approximated by smooth functions in the `H¹_σ` norm, and
`MemH1sLocOld` is the same class with the measurability conjunct removed.  The
module isolates that conjunct and asks what it does.

If the check failed — if the measurability conjunct excluded no pair, so that
`MemH1sLoc` and `MemH1sLocOld` coincided — then the exclusion lemma and the
template for the necessity of the conjunct below would be vacuous, and nothing
would force the conjunct to do any work: the lower Lebesgue integral of `|v|`, a
supremum over simple functions below the integrand, is `0` for a reason unrelated
to its argument, so a function invisible to that supremum would carry finite
`H¹_σ` norm without the conjunct.  This module is a consistency check of that
definition and is not a result of the paper.

Three statements.  First, an exclusion lemma: every pair satisfying all the
other requirements whose function fails to be integrable on some centred ball
fails the measurability conjunct.  This is uniform over all such pairs and needs
no set-theoretic construction, because the other requirements already supply the
finite-integral half of integrability on every ball.

Second, a conditional template for the necessity of the conjunct: a function
invisible to both readings the other requirements make of it yields a pair in
the wider class and outside the narrower one.  The template exhibits nothing.
Its hypotheses are met by no function constructed here or anywhere else in this
development, so the exclusion lemma may be vacuously true, and the possibility
that the two classes coincide — that the measurability conjunct excludes nothing
— is not ruled out.

Third, the degeneracy of that template once measurability is assumed: under a
measurability hypothesis on `v` the template can produce nothing but the zero
function up to a null set.  The argument needs that hypothesis to be absent,
which is exactly what makes it conditional.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The local class before the measurability conjunct -/

/-- The local class without the measurability conjunct: on every centred
Euclidean ball, a weak-gradient pair approximated by smooth functions in the
`H¹_s` norm, with nothing asked of the measurability of the pair itself. -/
@[expose]
def MemH1sLocOld (b : CoeffField d) (v : Vec d → ℝ) (Dv : Vec d → Vec d) : Prop :=
  ∀ R : ℝ, 0 < R →
    HasWeakGradientOn (euclideanBall d R) v Dv ∧
      ∃ w : ℕ → Vec d → ℝ,
        (∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n)) ∧
        _root_.Filter.Tendsto
          (fun n => h1sNormSqOn b (euclideanBall d R) (fun x => w n x - v x)
            (fun x => smoothGrad (w n) x - Dv x)) _root_.Filter.atTop (nhds 0)

/-- `MemH1sLoc` is that class together with the measurability of the pair, and
nothing else: the two sides are the same proposition, so the measurability
conjunct is the whole of the difference. -/
theorem memH1sLoc_iff_isMeasurableGradientPair_and_memH1sLocOld
    (b : CoeffField d) (v : Vec d → ℝ) (Dv : Vec d → Vec d) :
    MemH1sLoc b v Dv ↔ IsMeasurableGradientPair volume v Dv ∧ MemH1sLocOld b v Dv :=
  Iff.rfl

/-- Membership in the old class already gives the finite-integral half of
integrability: the lower Lebesgue integral of `|v|` over any centred ball is
finite, with no measurability input at all.

The mechanism is the `L¹` term of the approximation quantity: its convergence to
`0` in `ℝ≥0∞` forces some approximant to be at finite `L¹` distance from `v`,
and a smooth approximant has finite `L¹` mass on a bounded ball. -/
theorem lintegral_ofReal_abs_ne_top_of_memH1sLocOld {b : CoeffField d}
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} (hv : MemH1sLocOld b v Dv) {R : ℝ}
    (hR : 0 < R) :
    (∫⁻ x in euclideanBall d R, ENNReal.ofReal |v x| ∂volume) ≠ ⊤ := by
  obtain ⟨-, w, hw, htend⟩ := hv R hR
  obtain ⟨n, hn⟩ := exists_lintegral_ofReal_abs_sub_ne_top htend
  have hwc : Continuous (w n) := (hw n).continuous
  refine lintegral_ofReal_abs_ne_top_of_sub (g := w n) (h := v) ?_
    (lintegral_ofReal_abs_ne_top_of_isBounded (isBounded_euclideanBall d hR) hwc) hn
  exact (ENNReal.measurable_ofReal.comp hwc.abs.measurable).aemeasurable

/-! ## (1) The exclusion lemma -/

/-- **What the measurability conjunct excludes.**  Let `(v, Dv)` satisfy every
requirement of the old local class, and suppose `v` fails to be integrable on
some centred ball.  Then the pair fails the measurability conjunct, so it is not
in the current class.

This is uniform over all such pairs and needs no set-theoretic construction: the
old class already supplies the finite-integral half of integrability on every
ball, so the only way integrability can fail is a failure of measurability, and
the conjunct is exactly what forbids that.

Whether any pair satisfies the hypotheses is a separate question, and it is the
same open question as for the template below: no member of the old class that
fails to be integrable on a ball is constructed anywhere in this development, so
this statement may be vacuously true, and the possibility that the two classes
coincide is not ruled out. -/
theorem not_isMeasurableGradientPair_of_not_integrableOn {b : CoeffField d}
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} (hold : MemH1sLocOld b v Dv) {R : ℝ}
    (hR : 0 < R) (hni : ¬ IntegrableOn v (euclideanBall d R) volume) :
    ¬ IsMeasurableGradientPair volume v Dv := by
  intro hm
  refine hni ⟨hm.1.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  exact lt_of_le_of_ne le_top (lintegral_ofReal_abs_ne_top_of_memH1sLocOld hold hR)

/-- The same statement read on the current class: a pair of the old class whose
function is not integrable on some centred ball is not a member of the current
class. -/
theorem not_memH1sLoc_of_not_integrableOn {b : CoeffField d} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (hold : MemH1sLocOld b v Dv) {R : ℝ} (hR : 0 < R)
    (hni : ¬ IntegrableOn v (euclideanBall d R) volume) :
    ¬ MemH1sLoc b v Dv := fun hv =>
  not_isMeasurableGradientPair_of_not_integrableOn hold hR hni hv.1

/-! ## (2) The necessity template -/

/-- **A conditional template for the necessity of the measurability conjunct.**

Given a function `v` that is invisible to the two readings the old class makes
of it — the Bochner pairings of the weak-gradient relation, which value a
divergent integrand at `0`, and the lower Lebesgue integral of `|v|`, which is a
supremum over simple functions below the integrand — this lemma produces a
member of the old class with zero weak gradient that is integrable on no ball on
which `v` fails to be a.e. strongly measurable.  If such a `v` exists, the old
class is strictly wider than the current one and the measurability conjunct is
necessary rather than merely convenient.

**This lemma exhibits nothing.**  It is conditional on the hypothesis triple
`hw`, `hz`, `hnm`, and no function satisfying that triple is constructed here or
anywhere else in this development.  The intended instance is the indicator of a
Bernstein set — a set meeting every uncountable closed set without containing
one, hence of inner measure zero and full outer measure in every ball — and the
existence of such a set is a transfinite (choice-based) construction that
Mathlib does not carry.  So the necessity of the conjunct is argued, not
formalized: what is formalized is the implication from the triple, and the
triple is currently uninhabited as far as this development is concerned.  In
particular the possibility that the two classes coincide — that the measurability
condition excludes nothing — is not ruled out here. -/
theorem memH1sLocOld_and_not_integrableOn_of_blind {b : CoeffField d}
    {v : Vec d → ℝ}
    (hw : ∀ R : ℝ, 0 < R → HasWeakGradientOn (euclideanBall d R) v (fun _ => 0))
    (hz : ∀ R : ℝ, 0 < R →
      (∫⁻ x in euclideanBall d R, ENNReal.ofReal |v x| ∂volume) = 0)
    {R : ℝ} (_hR : 0 < R)
    (hnm : ¬ AEStronglyMeasurable v (volume.restrict (euclideanBall d R))) :
    MemH1sLocOld b v (fun _ => 0) ∧ ¬ IntegrableOn v (euclideanBall d R) volume := by
  refine ⟨?_, fun hI => hnm hI.1⟩
  intro S hS
  refine ⟨hw S hS, fun _ => fun _ : Vec d => (0 : ℝ), fun _ => contDiff_const, ?_⟩
  refine tendsto_const_nhds.congr fun n => ?_
  symm
  simp only [h1sNormSqOn]
  have h1 : (∫⁻ x in euclideanBall d S,
      ENNReal.ofReal |(0 : ℝ) - v x| ∂volume) = 0 := by
    rw [lintegral_congr fun x => by rw [zero_sub, abs_neg]]
    exact hz S hS
  have h2 : sEnergyOn b (euclideanBall d S)
      (fun x => smoothGrad (fun _ : Vec d => (0 : ℝ)) x - (0 : Vec d)) = 0 :=
    sEnergyOn_eq_zero_of_eq_zero fun x => by rw [smoothGrad_const, sub_zero]
  rw [h1, h2]
  simp

/-- The template, packaged as the statement it is meant to support: a function
satisfying the triple lies in the old class but not in the current one.  It is
conditional in exactly the same way. -/
theorem memH1sLocOld_and_not_memH1sLoc_of_blind {b : CoeffField d} {v : Vec d → ℝ}
    (hw : ∀ R : ℝ, 0 < R → HasWeakGradientOn (euclideanBall d R) v (fun _ => 0))
    (hz : ∀ R : ℝ, 0 < R →
      (∫⁻ x in euclideanBall d R, ENNReal.ofReal |v x| ∂volume) = 0)
    {R : ℝ} (hR : 0 < R)
    (hnm : ¬ AEStronglyMeasurable v (volume.restrict (euclideanBall d R))) :
    MemH1sLocOld b v (fun _ => 0) ∧ ¬ MemH1sLoc b v (fun _ => 0) := by
  obtain ⟨hold, hni⟩ := memH1sLocOld_and_not_integrableOn_of_blind (b := b) hw hz hR hnm
  exact ⟨hold, not_memH1sLoc_of_not_integrableOn hold hR hni⟩

/-! ## (3) With measurability assumed, the template is degenerate -/

/-- **A function invisible to the lower Lebesgue integral on every centred ball,
and a.e. strongly measurable, vanishes a.e.**

Consequently, a form of the blindness template that carries a measurability
hypothesis on `v` can produce nothing but the zero function (up to a null set),
and so cannot witness anything about the width of the class: the pair it
produces is a.e. the zero pair, which is in the class on any reading.  The
blindness argument needs the measurability hypothesis to be absent, which is
what makes it conditional. -/
theorem eq_zero_ae_of_lintegral_abs_eq_zero {v : Vec d → ℝ}
    (hmeas : AEStronglyMeasurable v volume)
    (hz : ∀ R : ℝ, 0 < R →
      (∫⁻ x in euclideanBall d R, ENNReal.ofReal |v x| ∂volume) = 0) :
    v =ᵐ[volume] 0 := by
  have hball : ∀ R : ℝ, 0 < R →
      volume ({x : Vec d | ¬ v x = 0} ∩ euclideanBall d R) = 0 := by
    intro R hR
    have hae : AEMeasurable (fun x => ENNReal.ofReal |v x|)
        (volume.restrict (euclideanBall d R)) := by
      simpa only [Real.norm_eq_abs] using
        (hmeas.restrict.norm.aemeasurable).ennreal_ofReal
    have hzero := (lintegral_eq_zero_iff' hae).mp (hz R hR)
    have h0 : ∀ᵐ x ∂(volume.restrict (euclideanBall d R)), v x = 0 := by
      filter_upwards [hzero] with x hx
      have hx' : ENNReal.ofReal |v x| = 0 := by
        simpa only [Pi.zero_apply] using hx
      exact abs_nonpos_iff.mp (ENNReal.ofReal_eq_zero.mp hx')
    have hres : (volume.restrict (euclideanBall d R)) {x : Vec d | ¬ v x = 0} = 0 :=
      ae_iff.mp h0
    have hle : volume ({x : Vec d | ¬ v x = 0} ∩ euclideanBall d R) ≤
        (volume.restrict (euclideanBall d R)) {x : Vec d | ¬ v x = 0} :=
      Measure.le_restrict_apply _ _
    rw [hres] at hle
    exact le_antisymm hle zero_le
  have hcover : {x : Vec d | ¬ v x = 0} ⊆
      ⋃ n : ℕ, ({x : Vec d | ¬ v x = 0} ∩ euclideanBall d ((n : ℝ) + 1)) := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (vecNormSq x)
    refine Set.mem_iUnion.2 ⟨n, hx, ?_⟩
    rw [mem_euclideanBall_iff]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    linarith only [hn, hn0, hsq]
  have hnull : volume {x : Vec d | ¬ v x = 0} = 0 :=
    measure_mono_null hcover
      (measure_iUnion_null fun n : ℕ => hball ((n : ℝ) + 1) (by positivity))
  have hae0 : ∀ᵐ x ∂(volume : Measure (Vec d)), v x = 0 := ae_iff.mpr hnull
  filter_upwards [hae0] with x hx
  simpa only [Pi.zero_apply] using hx

/-- The degeneracy in the form it is used: under a measurability hypothesis, the
blindness template produces a pair that agrees a.e. with the zero pair. -/
theorem eq_zero_ae_and_grad_of_lintegral_abs_eq_zero {v : Vec d → ℝ}
    (hmeas : AEStronglyMeasurable v volume)
    (hz : ∀ R : ℝ, 0 < R →
      (∫⁻ x in euclideanBall d R, ENNReal.ofReal |v x| ∂volume) = 0) :
    v =ᵐ[volume] 0 ∧ (fun _ : Vec d => (0 : Vec d)) =ᵐ[volume] 0 :=
  ⟨eq_zero_ae_of_lintegral_abs_eq_zero hmeas hz, _root_.Filter.EventuallyEq.rfl⟩

end

end HighContrast
end HCPolySupport
