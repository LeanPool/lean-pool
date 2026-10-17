/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxUpperPenalizedReal
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedResolventIdentity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PositiveC0Resolvent

/-!
# CruxUpperIdentities

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The signed penalized identities

The resolvent identity and the subtraction-free perturbation identity of the
whole-space exterior-penalized resolvent are proved on nonnegative data.  The
comparison family of the process layer acts on signed bounded measurable
observables, so this module transports both identities to the signed real form
by splitting the datum into its positive and negative parts.

The perturbation identity is stated in its subtracted form against the signed
real analytic minimal resolvent, which is the shape the process layer
consumes.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- Equal data have the same signed real minimal resolvent. -/
theorem analyticMinimalResolventReal_eq_of_eq (mu : PositiveShift)
    {f g : Vec d → ℝ} (hfg : f = g) (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (x : Vec d) :
    A.analyticMinimalResolventReal mu f hf hfD x =
      A.analyticMinimalResolventReal mu g hg hgE x := by
  subst g
  exact A.analyticMinimalResolventReal_bound_irrel mu hf hfD hgE x

/-- The signed real minimal resolvent is subtractive. -/
theorem analyticMinimalResolventReal_sub (mu : PositiveShift)
    {u v : Vec d → ℝ} (hu : Measurable u) (hv : Measurable v) {C E B : ℝ}
    (huC : ∀ x, |u x| ≤ C) (hvE : ∀ x, |v x| ≤ E)
    (huvB : ∀ x, |u x - v x| ≤ B) (x : Vec d) :
    A.analyticMinimalResolventReal mu (fun y ↦ u y - v y) (hu.sub hv) huvB x =
      A.analyticMinimalResolventReal mu u hu huC x -
        A.analyticMinimalResolventReal mu v hv hvE x := by
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
    A.analyticMinimalResolventReal mu (fun y ↦ u y - v y) (hu.sub hv) huvB x =
        A.analyticMinimalResolventReal mu (fun y ↦ u y + (-1 : ℝ) * v y)
          (hu.add (measurable_const.mul hv)) hsumD x :=
      A.analyticMinimalResolventReal_eq_of_eq mu hfun (hu.sub hv)
        (hu.add (measurable_const.mul hv)) huvB hsumD x
    _ = A.analyticMinimalResolventReal mu u hu huC x +
          A.analyticMinimalResolventReal mu (fun y ↦ (-1 : ℝ) * v y)
            (measurable_const.mul hv) hnegE x :=
      A.analyticMinimalResolventReal_add mu hu (measurable_const.mul hv) huC
        hnegE x
    _ = A.analyticMinimalResolventReal mu u hu huC x -
          A.analyticMinimalResolventReal mu v hv hvE x := by
        have hs := A.analyticMinimalResolventReal_smul mu (-1) hv hvE x
        rw [show A.analyticMinimalResolventReal mu (fun y ↦ (-1 : ℝ) * v y)
            (measurable_const.mul hv) hnegE x =
              -A.analyticMinimalResolventReal mu v hv hvE x by
          simpa only [neg_mul, one_mul] using hs]
        ring

/-- **The signed penalized resolvent identity.**  The exterior-penalized
resolvents at two shifts differ by the composed resolvent, on signed bounded
measurable data. -/
theorem analyticPenalizedResolventReal_resolventIdentity {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu nu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu f hf hfD x =
      A.analyticPenalizedResolventReal hV n nu f hf hfD x +
        ((nu : ℝ) - (mu : ℝ)) *
          A.analyticPenalizedResolventReal hV n nu
            (A.analyticPenalizedResolventReal hV n mu f hf hfD)
            (A.measurable_analyticPenalizedResolventReal hV n mu hf hfD)
            (D := D / (mu : ℝ))
            (A.abs_analyticPenalizedResolventReal_le hV n mu hf hfD) x := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hC : 0 ≤ D / (mu : ℝ) := div_nonneg hD mu.property.le
  have hfp : Measurable (analyticPositivePart f) :=
    measurable_analyticPositivePart hf
  have hfn : Measurable (analyticPositivePart fun y ↦ -f y) :=
    measurable_analyticPositivePart hf.neg
  have hfp0 : ∀ y, 0 ≤ analyticPositivePart f y := fun y ↦ le_max_right (f y) 0
  have hfn0 : ∀ y, 0 ≤ analyticPositivePart (fun y ↦ -f y) y := fun y ↦
    le_max_right (-f y) 0
  have hfpD : ∀ y, |analyticPositivePart f y| ≤ D :=
    abs_analyticPositivePart_le_of_bound hfD
  have hfnD : ∀ y, |analyticPositivePart (fun y ↦ -f y) y| ≤ D :=
    abs_analyticPositivePart_le_of_bound
      (fun y ↦ by simpa only [abs_neg] using hfD y)
  set up : Vec d → ℝ := fun y ↦
    (A.analyticPenalizedResolvent hV n mu (analyticPositivePart f) hfp hfpD y).toReal
    with hupdef
  set un : Vec d → ℝ := fun y ↦
    (A.analyticPenalizedResolvent hV n mu (analyticPositivePart fun z ↦ -f z)
      hfn hfnD y).toReal with hundef
  have hup : Measurable up :=
    (A.measurable_analyticPenalizedResolvent hV n mu hfp hfpD).ennreal_toReal
  have hun : Measurable un :=
    (A.measurable_analyticPenalizedResolvent hV n mu hfn hfnD).ennreal_toReal
  have hup0 : ∀ y, 0 ≤ up y := fun _ ↦ ENNReal.toReal_nonneg
  have hun0 : ∀ y, 0 ≤ un y := fun _ ↦ ENNReal.toReal_nonneg
  have hupC : ∀ y, |up y| ≤ D / (mu : ℝ) := by
    intro y
    rw [abs_of_nonneg (hup0 y)]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (A.analyticPenalizedResolvent_le hV n mu hfp hfp0 hD hfpD y)
  have hunC : ∀ y, |un y| ≤ D / (mu : ℝ) := by
    intro y
    rw [abs_of_nonneg (hun0 y)]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (A.analyticPenalizedResolvent_le hV n mu hfn hfn0 hD hfnD y)
  have hinner : A.analyticPenalizedResolventReal hV n nu
      (A.analyticPenalizedResolventReal hV n mu f hf hfD)
      (A.measurable_analyticPenalizedResolventReal hV n mu hf hfD)
      (A.abs_analyticPenalizedResolventReal_le hV n mu hf hfD) x =
      (A.analyticPenalizedResolvent hV n nu up hup hupC x).toReal -
        (A.analyticPenalizedResolvent hV n nu un hun hunC x).toReal := by
    change A.analyticPenalizedResolventReal hV n nu (fun y ↦ up y - un y)
        (hup.sub hun) (A.abs_analyticPenalizedResolventReal_le hV n mu hf hfD) x = _
    exact A.analyticPenalizedResolventReal_sub_of_nonneg hV n nu hup hun hup0
      hun0 hupC hunC
      (A.abs_analyticPenalizedResolventReal_le hV n mu hf hfD) x
  have hp := A.analyticPenalizedResolvent_toReal_resolventIdentity hV n mu nu
    hfp hfp0 hD hfpD x
  have hn := A.analyticPenalizedResolvent_toReal_resolventIdentity hV n mu nu
    hfn hfn0 hD hfnD x
  rw [hinner]
  unfold analyticPenalizedResolventReal
  change
    (A.analyticPenalizedResolvent hV n mu (analyticPositivePart f) hfp hfpD
        x).toReal -
      (A.analyticPenalizedResolvent hV n mu
        (analyticPositivePart fun z ↦ -f z) hfn hfnD x).toReal =
    ((A.analyticPenalizedResolvent hV n nu (analyticPositivePart f) hfp hfpD
        x).toReal -
      (A.analyticPenalizedResolvent hV n nu
        (analyticPositivePart fun z ↦ -f z) hfn hfnD x).toReal) +
      ((nu : ℝ) - (mu : ℝ)) *
        ((A.analyticPenalizedResolvent hV n nu up hup hupC x).toReal -
          (A.analyticPenalizedResolvent hV n nu un hun hunC x).toReal)
  linear_combination hp - hn

/-- **The signed subtraction-free perturbation identity.**  The signed real
exterior-penalized resolvent is the minimal resolvent of the datum minus the
minimal resolvent of the penalized load. -/
theorem analyticPenalizedResolventReal_perturbation {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (x : Vec d) :
    A.analyticPenalizedResolventReal hV n mu f hf hfD x =
      A.analyticMinimalResolventReal mu f hf hfD x -
        A.analyticMinimalResolventReal mu
          (fun y ↦ wholeSpacePenalizationPotential V n y *
            A.analyticPenalizedResolventReal hV n mu f hf hfD y)
          ((measurable_wholeSpacePenalizationPotential hV n).mul
            (A.measurable_analyticPenalizedResolventReal hV n mu hf hfD))
          (D := (n : ℝ) * (D / (mu : ℝ)))
          (fun y ↦ by
            rw [abs_mul,
              abs_of_nonneg (wholeSpacePenalizationPotential_nonneg V n y)]
            exact mul_le_mul (wholeSpacePenalizationPotential_le V n y)
              (A.abs_analyticPenalizedResolventReal_le hV n mu hf hfD y)
              (abs_nonneg _) (Nat.cast_nonneg n)) x := by
  have hC : 0 ≤ D / (mu : ℝ) := div_nonneg hD mu.property.le
  have hqm : Measurable (wholeSpacePenalizationPotential V n) :=
    measurable_wholeSpacePenalizationPotential hV n
  have hfp : Measurable (analyticPositivePart f) :=
    measurable_analyticPositivePart hf
  have hfn : Measurable (analyticPositivePart fun y ↦ -f y) :=
    measurable_analyticPositivePart hf.neg
  have hfp0 : ∀ y, 0 ≤ analyticPositivePart f y := fun y ↦ le_max_right (f y) 0
  have hfn0 : ∀ y, 0 ≤ analyticPositivePart (fun y ↦ -f y) y := fun y ↦
    le_max_right (-f y) 0
  have hfpD : ∀ y, |analyticPositivePart f y| ≤ D :=
    abs_analyticPositivePart_le_of_bound hfD
  have hfnD : ∀ y, |analyticPositivePart (fun y ↦ -f y) y| ≤ D :=
    abs_analyticPositivePart_le_of_bound
      (fun y ↦ by simpa only [abs_neg] using hfD y)
  set up : Vec d → ℝ := fun y ↦
    (A.analyticPenalizedResolvent hV n mu (analyticPositivePart f) hfp hfpD y).toReal
    with hupdef
  set un : Vec d → ℝ := fun y ↦
    (A.analyticPenalizedResolvent hV n mu (analyticPositivePart fun z ↦ -f z)
      hfn hfnD y).toReal with hundef
  have hup : Measurable up :=
    (A.measurable_analyticPenalizedResolvent hV n mu hfp hfpD).ennreal_toReal
  have hun : Measurable un :=
    (A.measurable_analyticPenalizedResolvent hV n mu hfn hfnD).ennreal_toReal
  have hloadp0 : ∀ y, 0 ≤ wholeSpacePenalizationPotential V n y * up y := fun y ↦
    mul_nonneg (wholeSpacePenalizationPotential_nonneg V n y)
      ENNReal.toReal_nonneg
  have hloadn0 : ∀ y, 0 ≤ wholeSpacePenalizationPotential V n y * un y := fun y ↦
    mul_nonneg (wholeSpacePenalizationPotential_nonneg V n y)
      ENNReal.toReal_nonneg
  have hloadpB : ∀ y, |wholeSpacePenalizationPotential V n y * up y| ≤
      (n : ℝ) * (D / (mu : ℝ)) :=
    A.abs_analyticPenalizedLoad_le hV n mu hfp hfp0 hD hfpD
  have hloadnB : ∀ y, |wholeSpacePenalizationPotential V n y * un y| ≤
      (n : ℝ) * (D / (mu : ℝ)) :=
    A.abs_analyticPenalizedLoad_le hV n mu hfn hfn0 hD hfnD
  have hp := A.analyticPenalizedResolvent_perturbation hV n mu hfp hfp0 hD hfpD x
  have hn := A.analyticPenalizedResolvent_perturbation hV n mu hfn hfn0 hD hfnD x
  have hpload : (A.analyticMinimalResolvent mu
      (A.analyticPenalizedLoad hV n mu (analyticPositivePart f) hfp hfpD)
      (A.measurable_analyticPenalizedLoad hV n mu hfp hfpD)
      (A.abs_analyticPenalizedLoad_le hV n mu hfp hfp0 hD hfpD) x).toReal =
      A.analyticMinimalResolventReal mu
        (fun y ↦ wholeSpacePenalizationPotential V n y * up y)
        (hqm.mul hup) hloadpB x :=
    (A.analyticMinimalResolventReal_eq_toReal mu (hqm.mul hup) hloadp0
      hloadpB x).symm
  have hnload : (A.analyticMinimalResolvent mu
      (A.analyticPenalizedLoad hV n mu (analyticPositivePart fun z ↦ -f z) hfn hfnD)
      (A.measurable_analyticPenalizedLoad hV n mu hfn hfnD)
      (A.abs_analyticPenalizedLoad_le hV n mu hfn hfn0 hD hfnD) x).toReal =
      A.analyticMinimalResolventReal mu
        (fun y ↦ wholeSpacePenalizationPotential V n y * un y)
        (hqm.mul hun) hloadnB x :=
    (A.analyticMinimalResolventReal_eq_toReal mu (hqm.mul hun) hloadn0
      hloadnB x).symm
  have hfppos : (A.analyticMinimalResolvent mu (analyticPositivePart f) hfp
      hfpD x).toReal =
      A.analyticMinimalResolventReal mu (analyticPositivePart f) hfp hfpD x :=
    (A.analyticMinimalResolventReal_eq_toReal mu hfp hfp0 hfpD x).symm
  have hfnpos : (A.analyticMinimalResolvent mu
      (analyticPositivePart fun z ↦ -f z) hfn hfnD x).toReal =
      A.analyticMinimalResolventReal mu (analyticPositivePart fun z ↦ -f z) hfn
        hfnD x :=
    (A.analyticMinimalResolventReal_eq_toReal mu hfn hfn0 hfnD x).symm
  rw [hpload, hfppos] at hp
  rw [hnload, hfnpos] at hn
  have hdiffB : ∀ y, |wholeSpacePenalizationPotential V n y * up y -
      wholeSpacePenalizationPotential V n y * un y| ≤
      (n : ℝ) * (D / (mu : ℝ)) + (n : ℝ) * (D / (mu : ℝ)) := by
    intro y
    have h1 := hloadpB y
    have h2 := hloadnB y
    rw [abs_le] at h1 h2 ⊢
    exact ⟨by linarith only [h1.1, h1.2, h2.1, h2.2],
      by linarith only [h1.1, h1.2, h2.1, h2.2]⟩
  have hfsplit : A.analyticMinimalResolventReal mu f hf hfD x =
      A.analyticMinimalResolventReal mu (analyticPositivePart f) hfp hfpD x -
        A.analyticMinimalResolventReal mu (analyticPositivePart fun z ↦ -f z)
          hfn hfnD x := by
    rw [A.analyticMinimalResolventReal_eq_toReal mu hfp hfp0 hfpD x,
      A.analyticMinimalResolventReal_eq_toReal mu hfn hfn0 hfnD x]
    rfl
  have hloadfun : (fun y ↦ wholeSpacePenalizationPotential V n y *
        A.analyticPenalizedResolventReal hV n mu f hf hfD y) =
      fun y ↦ wholeSpacePenalizationPotential V n y * up y -
        wholeSpacePenalizationPotential V n y * un y := by
    funext y
    change wholeSpacePenalizationPotential V n y * (up y - un y) = _
    ring
  have hloadsplit : A.analyticMinimalResolventReal mu
      (fun y ↦ wholeSpacePenalizationPotential V n y *
        A.analyticPenalizedResolventReal hV n mu f hf hfD y)
      (hqm.mul (A.measurable_analyticPenalizedResolventReal hV n mu hf hfD))
      (D := (n : ℝ) * (D / (mu : ℝ)))
      (fun y ↦ by
        rw [abs_mul,
          abs_of_nonneg (wholeSpacePenalizationPotential_nonneg V n y)]
        exact mul_le_mul (wholeSpacePenalizationPotential_le V n y)
          (A.abs_analyticPenalizedResolventReal_le hV n mu hf hfD y)
          (abs_nonneg _) (Nat.cast_nonneg n)) x =
      A.analyticMinimalResolventReal mu
          (fun y ↦ wholeSpacePenalizationPotential V n y * up y)
          (hqm.mul hup) hloadpB x -
        A.analyticMinimalResolventReal mu
          (fun y ↦ wholeSpacePenalizationPotential V n y * un y)
          (hqm.mul hun) hloadnB x := by
    rw [A.analyticMinimalResolventReal_eq_of_eq mu hloadfun
      (hqm.mul (A.measurable_analyticPenalizedResolventReal hV n mu hf hfD))
      ((hqm.mul hup).sub (hqm.mul hun)) _ hdiffB x]
    exact A.analyticMinimalResolventReal_sub mu (hqm.mul hup) (hqm.mul hun)
      hloadpB hloadnB hdiffB x
  rw [hloadsplit, hfsplit]
  change up x - un x = _
  linarith only [hp, hn]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
