/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedIdentities

/-!
# CruxUpperPenalizedReal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Signed real algebra for the whole-space exterior-penalized resolvent

The exterior-penalized resolvent of the cubic exhaustion is defined on
nonnegative data as a supremum of extended reals.  The comparison family
required by the process layer acts on signed bounded measurable observables,
so this module builds the signed real form as the difference of the values on
the positive and negative parts, and transports cube linearity to it.

The pattern is the one already used for the analytic minimal resolvent: the
signed zero-extended cube resolvents converge to the signed real value, and
additivity, homogeneity, the sharp maximum-principle bound and independence of
the numerical bound follow from the corresponding cube statements.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

omit [NeZero d] in
/-- A bound for an observable bounds its nonnegative part. -/
theorem abs_analyticPositivePart_le_of_bound {f : Vec d → ℝ} {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) : |analyticPositivePart f x| ≤ D := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hpart : 0 ≤ analyticPositivePart f x := le_max_right _ _
  rw [abs_of_nonneg hpart, analyticPositivePart]
  exact max_le ((le_abs_self (f x)).trans (hfD x)) hD

omit [NeZero d] in
/-- The nonnegative parts of an observable and of its negative reconstruct
it. -/
theorem analyticPositivePart_sub_neg (f : Vec d → ℝ) :
    (fun x ↦ analyticPositivePart f x - analyticPositivePart (fun y ↦ -f y) x) = f := by
  funext x
  exact max_zero_sub_max_neg_zero_eq_self (f x)

variable (A : WholeSpaceAnalyticData d)

/-- The value of a local penalized representative does not depend on the
numerical bound certifying boundedness of its datum. -/
theorem analyticPenalizedCubeResolvent_bound_irrel {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hfE : ∀ x, |f x| ≤ E)
    (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x =
      A.analyticPenalizedCubeResolvent hV n mu f hf hfE m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · refine eqOn_of_continuousOn_of_ae_eq
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen
      (A.continuousOn_analyticPenalizedCubeResolvent hV n mu hf hfD m)
      (A.continuousOn_analyticPenalizedCubeResolvent hV n mu hf hfE m) ?_ hx
    filter_upwards [A.analyticPenalizedCubeResolvent_ae hV n mu hf hfD m,
      A.analyticPenalizedCubeResolvent_ae hV n mu hf hfE m] with y h1 h2
    rw [h1, h2]
    rfl
  · rw [analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticPenalizedCubeResolvent, dite_eq_right hx]

/-- Two equal data with possibly different bounds have the same local
penalized representative. -/
theorem analyticPenalizedCubeResolvent_congr {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f g : Vec d → ℝ}
    (hfg : f = g) (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x =
      A.analyticPenalizedCubeResolvent hV n mu g hg hgE m x := by
  subst g
  exact A.analyticPenalizedCubeResolvent_bound_irrel hV n mu hf hfD hgE m x

/-- A local penalized representative splits along the positive and negative
parts of its datum. -/
theorem analyticPenalizedCubeResolvent_eq_parts {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x =
      A.analyticPenalizedCubeResolvent hV n mu (analyticPositivePart f)
          (measurable_analyticPositivePart hf)
          (abs_analyticPositivePart_le_of_bound hfD) m x -
        A.analyticPenalizedCubeResolvent hV n mu (analyticPositivePart fun y ↦ -f y)
          (measurable_analyticPositivePart hf.neg)
          (abs_analyticPositivePart_le_of_bound (D := D)
            (fun y ↦ by simpa only [abs_neg] using hfD y)) m x := by
  set fp := analyticPositivePart f with hfpdef
  set fn := analyticPositivePart fun y ↦ -f y with hfndef
  have hfp : Measurable fp := measurable_analyticPositivePart hf
  have hfn : Measurable fn := measurable_analyticPositivePart hf.neg
  have hfpD : ∀ y, |fp y| ≤ D := abs_analyticPositivePart_le_of_bound hfD
  have hfnD : ∀ y, |fn y| ≤ D :=
    abs_analyticPositivePart_le_of_bound
      (fun y ↦ by simpa only [abs_neg] using hfD y)
  have hnegD : ∀ y, |(-1 : ℝ) * fn y| ≤ |(-1 : ℝ)| * D := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfnD y) (abs_nonneg (-1 : ℝ))
  have hsplit : (fun y ↦ fp y + (-1 : ℝ) * fn y) = f := by
    funext y
    have := congrFun (analyticPositivePart_sub_neg f) y
    simp only [hfpdef, hfndef] at this ⊢
    linarith only [this]
  have hsumD : ∀ y, |fp y + (-1 : ℝ) * fn y| ≤ D + |(-1 : ℝ)| * D := by
    intro y
    rw [congrFun hsplit y]
    have hD : 0 ≤ D := (abs_nonneg (f y)).trans (hfD y)
    calc
      |f y| ≤ D := hfD y
      _ ≤ D + |(-1 : ℝ)| * D :=
        le_add_of_nonneg_right (mul_nonneg (abs_nonneg (-1 : ℝ)) hD)
  have hadd := A.analyticPenalizedCubeResolvent_add hV n mu hfp
    (measurable_const.mul hfn) hfpD hnegD hsumD m x
  have hsmul := A.analyticPenalizedCubeResolvent_smul hV n mu (-1) hfn hfnD
    hnegD m x
  have hstart : A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x =
      A.analyticPenalizedCubeResolvent hV n mu
        (fun y ↦ fp y + (-1 : ℝ) * fn y)
        (hfp.add (measurable_const.mul hfn)) hsumD m x :=
    A.analyticPenalizedCubeResolvent_congr hV n mu hsplit.symm hf
      (hfp.add (measurable_const.mul hfn)) hfD hsumD m x
  have hadd' : A.analyticPenalizedCubeResolvent hV n mu
      (fun y ↦ fp y + (-1 : ℝ) * fn y) (hfp.add (measurable_const.mul hfn)) hsumD m x =
      A.analyticPenalizedCubeResolvent hV n mu fp hfp hfpD m x +
        A.analyticPenalizedCubeResolvent hV n mu (fun y ↦ (-1 : ℝ) * fn y)
          (measurable_const.mul hfn) hnegD m x := hadd
  rw [hstart, hadd']
  have hneg : A.analyticPenalizedCubeResolvent hV n mu (fun y ↦ (-1 : ℝ) * fn y)
      (measurable_const.mul hfn) hnegD m x =
      -A.analyticPenalizedCubeResolvent hV n mu fn hfn hfnD m x := by
    have := hsmul
    simpa only [neg_mul, one_mul] using this
  rw [hneg, sub_eq_add_neg]

/-- **The signed real whole-space exterior-penalized resolvent.**  It is the
difference of the values on the positive and negative parts of the datum. -/
def analyticPenalizedResolventReal {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) : ℝ :=
  (A.analyticPenalizedResolvent hV n mu (analyticPositivePart f)
      (measurable_analyticPositivePart hf)
      (abs_analyticPositivePart_le_of_bound hfD) x).toReal -
    (A.analyticPenalizedResolvent hV n mu (analyticPositivePart fun y ↦ -f y)
      (measurable_analyticPositivePart hf.neg)
      (abs_analyticPositivePart_le_of_bound (D := D)
        (fun y ↦ by simpa only [abs_neg] using hfD y)) x).toReal

/-- The signed zero-extended penalized cube resolvents converge to the signed
real whole-space penalized resolvent. -/
theorem tendsto_analyticPenalizedCubeResolvent_real {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Tendsto (fun m ↦ A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x)
      atTop (nhds (A.analyticPenalizedResolventReal hV n mu f hf hfD x)) := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hp := A.tendsto_analyticPenalizedCubeResolvent hV n mu
    (measurable_analyticPositivePart hf) (fun y ↦ le_max_right (f y) 0) hD
    (abs_analyticPositivePart_le_of_bound hfD) x
  have hn := A.tendsto_analyticPenalizedCubeResolvent hV n mu
    (measurable_analyticPositivePart hf.neg) (fun y ↦ le_max_right (-f y) 0) hD
    (abs_analyticPositivePart_le_of_bound (D := D)
      (fun y ↦ by simpa only [abs_neg, Pi.neg_apply] using! hfD y)) x
  apply (hp.sub hn).congr'
  filter_upwards with m
  exact (A.analyticPenalizedCubeResolvent_eq_parts hV n mu hf hfD m x).symm

/-- On nonnegative data the signed real form is the real value of the
extended-real penalized resolvent. -/
theorem analyticPenalizedResolventReal_eq_toReal {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu f hf hfD x =
      (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  exact tendsto_nhds_unique
    (A.tendsto_analyticPenalizedCubeResolvent_real hV n mu hf hfD x)
    (A.tendsto_analyticPenalizedCubeResolvent hV n mu hf hf0 hD hfD x)

/-- The signed real penalized resolvent is additive. -/
theorem analyticPenalizedResolventReal_add {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f g : Vec d → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu (fun y ↦ f y + g y) (hf.add hg)
        (D := D + E) (fun y ↦ (abs_add_le (f y) (g y)).trans
          (add_le_add (hfD y) (hgE y))) x =
      A.analyticPenalizedResolventReal hV n mu f hf hfD x +
        A.analyticPenalizedResolventReal hV n mu g hg hgE x := by
  have hfg : ∀ y, |f y + g y| ≤ D + E := fun y ↦
    (abs_add_le (f y) (g y)).trans (add_le_add (hfD y) (hgE y))
  have hleft := A.tendsto_analyticPenalizedCubeResolvent_real hV n mu
    (hf.add hg) hfg x
  have hright := (A.tendsto_analyticPenalizedCubeResolvent_real hV n mu hf hfD x).add
    (A.tendsto_analyticPenalizedCubeResolvent_real hV n mu hg hgE x)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with m
  exact (A.analyticPenalizedCubeResolvent_add hV n mu hf hg hfD hgE hfg m x).symm

/-- Scalar multiplication commutes with the signed real penalized
resolvent. -/
theorem analyticPenalizedResolventReal_smul {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) (c : ℝ) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu (fun y ↦ c * f y)
        (hf.const_smul c) (D := |c| * D) (fun y ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hfD y) (abs_nonneg c)) x =
      c * A.analyticPenalizedResolventReal hV n mu f hf hfD x := by
  have hcf : ∀ y, |c * f y| ≤ |c| * D := fun y ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfD y) (abs_nonneg c)
  have hleft := A.tendsto_analyticPenalizedCubeResolvent_real hV n mu
    (hf.const_smul c) hcf x
  have hright := (A.tendsto_analyticPenalizedCubeResolvent_real hV n mu hf hfD
    x).const_mul c
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with m
  exact (A.analyticPenalizedCubeResolvent_smul hV n mu c hf hfD hcf m x).symm

/-- The signed real penalized resolvent inherits the sharp maximum-principle
bound of every cube. -/
theorem abs_analyticPenalizedResolventReal_le {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    |A.analyticPenalizedResolventReal hV n mu f hf hfD x| ≤ D / (mu : ℝ) := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  refine le_of_tendsto
    ((A.tendsto_analyticPenalizedCubeResolvent_real hV n mu hf hfD x).abs)
    (Eventually.of_forall fun m ↦
      A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m x)

/-- The signed real penalized resolvent does not depend on the numerical
bound certifying boundedness of its datum. -/
theorem analyticPenalizedResolventReal_bound_irrel {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hfE : ∀ x, |f x| ≤ E)
    (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu f hf hfD x =
      A.analyticPenalizedResolventReal hV n mu f hf hfE x :=
  tendsto_nhds_unique
    (A.tendsto_analyticPenalizedCubeResolvent_real hV n mu hf hfD x)
    (A.tendsto_analyticPenalizedCubeResolvent_real hV n mu hf hfE x)

/-- Two data agreeing everywhere have the same signed real penalized
resolvent. -/
theorem analyticPenalizedResolventReal_congr {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f g : Vec d → ℝ}
    (hfg : f = g) (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu f hf hfD x =
      A.analyticPenalizedResolventReal hV n mu g hg hgE x := by
  subst g
  exact A.analyticPenalizedResolventReal_bound_irrel hV n mu hf hfD hgE x

/-- The signed real penalized resolvent is measurable. -/
theorem measurable_analyticPenalizedResolventReal {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.analyticPenalizedResolventReal hV n mu f hf hfD) :=
  ((A.measurable_analyticPenalizedResolvent hV n mu
      (measurable_analyticPositivePart hf)
      (abs_analyticPositivePart_le_of_bound hfD)).ennreal_toReal).sub
    ((A.measurable_analyticPenalizedResolvent hV n mu
      (measurable_analyticPositivePart hf.neg)
      (abs_analyticPositivePart_le_of_bound (D := D)
        (fun y ↦ by simpa only [abs_neg, Pi.neg_apply] using! hfD y))).ennreal_toReal)

/-- The difference of the values on two nonnegative data is the value on
their difference. -/
theorem analyticPenalizedResolventReal_sub_of_nonneg {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {u v : Vec d → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hu0 : ∀ x, 0 ≤ u x)
    (hv0 : ∀ x, 0 ≤ v x) {B C E : ℝ} (huC : ∀ x, |u x| ≤ C)
    (hvE : ∀ x, |v x| ≤ E) (huvB : ∀ x, |u x - v x| ≤ B) (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu (fun y ↦ u y - v y) (hu.sub hv)
        huvB x =
      (A.analyticPenalizedResolvent hV n mu u hu huC x).toReal -
        (A.analyticPenalizedResolvent hV n mu v hv hvE x).toReal := by
  have hnegE : ∀ y, |(-1 : ℝ) * v y| ≤ |(-1 : ℝ)| * E := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvE y) (abs_nonneg (-1 : ℝ))
  have hsumD : ∀ y, |u y + (-1 : ℝ) * v y| ≤ C + |(-1 : ℝ)| * E := fun y ↦
    (abs_add_le (u y) ((-1 : ℝ) * v y)).trans (add_le_add (huC y) (hnegE y))
  have hfun : (fun y ↦ u y - v y) = fun y ↦ u y + (-1 : ℝ) * v y := by
    funext y
    ring
  calc
    A.analyticPenalizedResolventReal hV n mu (fun y ↦ u y - v y) (hu.sub hv)
        huvB x =
        A.analyticPenalizedResolventReal hV n mu
          (fun y ↦ u y + (-1 : ℝ) * v y) (hu.add (measurable_const.mul hv))
          hsumD x :=
      A.analyticPenalizedResolventReal_congr hV n mu hfun (hu.sub hv)
        (hu.add (measurable_const.mul hv)) huvB hsumD x
    _ = A.analyticPenalizedResolventReal hV n mu u hu huC x +
          A.analyticPenalizedResolventReal hV n mu
            (fun y ↦ (-1 : ℝ) * v y) (measurable_const.mul hv) hnegE x :=
      A.analyticPenalizedResolventReal_add hV n mu hu
        (measurable_const.mul hv) huC hnegE x
    _ = A.analyticPenalizedResolventReal hV n mu u hu huC x -
          A.analyticPenalizedResolventReal hV n mu v hv hvE x := by
        have hs := A.analyticPenalizedResolventReal_smul hV n mu (-1) hv hvE x
        rw [show A.analyticPenalizedResolventReal hV n mu
            (fun y ↦ (-1 : ℝ) * v y) (measurable_const.mul hv) hnegE x =
              -A.analyticPenalizedResolventReal hV n mu v hv hvE x by
          simpa only [neg_mul, one_mul] using hs]
        ring
    _ = (A.analyticPenalizedResolvent hV n mu u hu huC x).toReal -
          (A.analyticPenalizedResolvent hV n mu v hv hvE x).toReal := by
        rw [A.analyticPenalizedResolventReal_eq_toReal hV n mu hu hu0 huC x,
          A.analyticPenalizedResolventReal_eq_toReal hV n mu hv hv0 hvE x]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
