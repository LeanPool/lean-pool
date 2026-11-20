/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleSlices
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleSurface

/-!
# Whole-line integration by parts with two jumps

The discontinuous Ponomarenko mode of the paper (`lem:jump-horizontal-mode`)
is smooth inside and outside the unit circle but jumps across
it.  Realizing it as a whole-plane weak-derivative field therefore needs an integration-by-parts
identity whose only extra term is the circle jump.  This module provides its one-dimensional
input: the fundamental theorem of calculus on a line crossing an interface twice
(`integral_eq_end_sub_start_sub_two_jumps`), and its almost-everywhere Fubini wrapper over a
product space (`integral_prod_eq_integral_end_sub_start_sub_two_jumps_ae`).

On a line, three branch primitives with distinct endpoint values are allowed; those values are
precisely the one-sided traces, so the integral of the common branch derivative records both jumps
instead of silently imposing continuity.  The disk geometry is in
`WholePlaneUnitDiskSliceGeometry`, and the whole-plane weak-derivative identity is built
from both in `WholePlaneUnitDiskFibreDerivativeSource`.
-/

@[expose] public section

/-!
## The two-jump fundamental theorem of calculus

This part isolates the one-dimensional analytic identity needed when a coordinate line crosses
an interface twice.  The three branch primitives are allowed to have distinct endpoint values;
these values are precisely their one-sided traces.  Consequently the integral of the common
branch derivative records both jumps instead of silently imposing continuity.

Using separate branch primitives avoids assigning incompatible values to a discontinuous
function at the two interface points.  It is also the natural interface for applications, where
the interior and exterior formulas are already available as smooth functions on
overlapping open sets.
-/

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set Topology

/-- Fundamental theorem of calculus on the real line, split at two points.

`fLeft a`, `fMiddle a`, `fMiddle b`, and `fRight b` are the four one-sided traces.  The conclusion
has the orientation used by distributional derivatives: the classical derivative integrates to
the endpoint change minus the two right-minus-left jumps.
-/
theorem integral_eq_end_sub_start_sub_two_jumps
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {fLeft fMiddle fRight f' : ℝ → F} {a b : ℝ} {atNegInf atPosInf : F}
    (hab : a < b)
    (hLeftCont : ContinuousWithinAt fLeft (Iic a) a)
    (hLeftDeriv : ∀ x ∈ Iio a, HasDerivAt fLeft (f' x) x)
    (hMiddleCont : ContinuousOn fMiddle (Icc a b))
    (hMiddleDeriv : ∀ x ∈ Ioo a b, HasDerivAt fMiddle (f' x) x)
    (hRightCont : ContinuousWithinAt fRight (Ici b) b)
    (hRightDeriv : ∀ x ∈ Ioi b, HasDerivAt fRight (f' x) x)
    (hi : Integrable f')
    (hneg : Tendsto fLeft atBot (nhds atNegInf))
    (hpos : Tendsto fRight atTop (nhds atPosInf)) :
    ∫ x : ℝ, f' x =
      atPosInf - atNegInf -
        ((fMiddle a - fLeft a) + (fRight b - fMiddle b)) := by
  have hleft : ∫ x in Iic a, f' x = fLeft a - atNegInf :=
    integral_Iic_of_hasDerivAt_of_tendsto hLeftCont hLeftDeriv hi.integrableOn hneg
  have hmiddle : ∫ x in Ioo a b, f' x = fMiddle b - fMiddle a := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [← intervalIntegral.integral_of_le hab.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hMiddleCont
      hMiddleDeriv hi.intervalIntegrable
  have hrightIoi : ∫ x in Ioi b, f' x = atPosInf - fRight b :=
    integral_Ioi_of_hasDerivAt_of_tendsto hRightCont hRightDeriv hi.integrableOn hpos
  have hright : ∫ x in Ici b, f' x = atPosInf - fRight b := by
    rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
    exact hrightIoi
  have hdisjointLeftMiddle : Disjoint (Iic a) (Ioo a b) := by
    rw [Set.disjoint_left]
    intro x hxa hxab
    exact (not_lt_of_ge hxa) hxab.1
  have hdisjointAllRight : Disjoint (Iic a ∪ Ioo a b) (Ici b) := by
    rw [Set.disjoint_left]
    intro x hx hxb
    rcases hx with hxa | hxab
    · exact (not_lt_of_ge hxb) (lt_of_le_of_lt hxa hab)
    · exact (not_lt_of_ge hxb) hxab.2
  have hunion : (Iic a ∪ Ioo a b) ∪ Ici b = (Set.univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ioo, mem_Ici, mem_univ, iff_true]
    by_cases hxa : x ≤ a
    · exact Or.inl (Or.inl hxa)
    by_cases hbx : b ≤ x
    · exact Or.inr hbx
    · exact Or.inl (Or.inr ⟨lt_of_not_ge hxa, lt_of_not_ge hbx⟩)
  have hsplit :
      ∫ x : ℝ, f' x =
        (∫ x in Iic a, f' x) + (∫ x in Ioo a b, f' x) +
          ∫ x in Ici b, f' x := by
    rw [← setIntegral_univ, ← hunion]
    rw [setIntegral_union hdisjointAllRight measurableSet_Ici hi.integrableOn hi.integrableOn]
    rw [setIntegral_union hdisjointLeftMiddle measurableSet_Ioo hi.integrableOn hi.integrableOn]
  rw [hsplit, hleft, hmiddle, hright]
  abel

/-- Almost-everywhere version of the fiberwise Fubini wrapper.

This is the form suited to circle slices: the two crossing points coalesce on tangent fibers,
but those outer parameters form a null set.  No arbitrary analytic data need be manufactured on
those fibers; only the product-space derivative itself remains globally integrable. -/
theorem integral_prod_eq_integral_end_sub_start_sub_two_jumps_ae
    {X F : Type*} [MeasurableSpace X] {mu : Measure X} [SigmaFinite mu]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {fLeft fMiddle fRight f' : X × ℝ → F}
    {a b : X → ℝ} {atNegInf atPosInf : X → F}
    (hab : ∀ᵐ x ∂mu, a x < b x)
    (hLeftCont : ∀ᵐ x ∂mu, ContinuousWithinAt
      (fun t : ℝ ↦ fLeft (x, t)) (Iic (a x)) (a x))
    (hLeftDeriv : ∀ᵐ x ∂mu, ∀ t, t ∈ Iio (a x) →
      HasDerivAt (fun u : ℝ ↦ fLeft (x, u)) (f' (x, t)) t)
    (hMiddleCont : ∀ᵐ x ∂mu, ContinuousOn
      (fun t : ℝ ↦ fMiddle (x, t)) (Icc (a x) (b x)))
    (hMiddleDeriv : ∀ᵐ x ∂mu, ∀ t, t ∈ Ioo (a x) (b x) →
      HasDerivAt (fun u : ℝ ↦ fMiddle (x, u)) (f' (x, t)) t)
    (hRightCont : ∀ᵐ x ∂mu, ContinuousWithinAt
      (fun t : ℝ ↦ fRight (x, t)) (Ici (b x)) (b x))
    (hRightDeriv : ∀ᵐ x ∂mu, ∀ t, t ∈ Ioi (b x) →
      HasDerivAt (fun u : ℝ ↦ fRight (x, u)) (f' (x, t)) t)
    (hi : Integrable f' (mu.prod volume))
    (hneg : ∀ᵐ x ∂mu,
      Tendsto (fun t : ℝ ↦ fLeft (x, t)) atBot (nhds (atNegInf x)))
    (hpos : ∀ᵐ x ∂mu,
      Tendsto (fun t : ℝ ↦ fRight (x, t)) atTop (nhds (atPosInf x))) :
    ∫ p : X × ℝ, f' p ∂mu.prod volume =
      ∫ x : X, atPosInf x - atNegInf x -
        ((fMiddle (x, a x) - fLeft (x, a x)) +
          (fRight (x, b x) - fMiddle (x, b x))) ∂mu := by
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae, hab, hLeftCont, hLeftDeriv,
    hMiddleCont, hMiddleDeriv, hRightCont, hRightDeriv, hneg, hpos]
      with x hix habx hLeftContx hLeftDerivx hMiddleContx hMiddleDerivx
        hRightContx hRightDerivx hnegx hposx
  exact integral_eq_end_sub_start_sub_two_jumps habx hLeftContx hLeftDerivx
    hMiddleContx hMiddleDerivx hRightContx hRightDerivx hix hnegx hposx

end

end FastDynamo
