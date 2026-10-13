/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.C0
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.RealResolvent
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0Resolvent

/-!
# PositiveC0Resolvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The positive `C₀` resolvent of the analytic whole-space exhaustion

The signed real minimal resolvent is the limit of the signed zero-extended
cube resolvents.  Their linearity gives additivity and homogeneity of the
limit, while their sharp maximum-principle estimate gives the exact
`‖f‖ / mu` bound.  These facts package the analytic map as a positive
contractive `C₀` resolvent once dense range is supplied.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

omit [NeZero d] in
private theorem abs_analyticPositivePart_le' {f : Vec d → ℝ} {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    |analyticPositivePart f x| ≤ D := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hpart : 0 ≤ analyticPositivePart f x := le_max_right _ _
  rw [abs_of_nonneg hpart, analyticPositivePart]
  exact max_le ((le_abs_self (f x)).trans (hfD x)) hD

/-- The real minimal resolvent is positivity preserving. -/
theorem analyticMinimalResolventReal_nonneg (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    0 ≤ A.analyticMinimalResolventReal mu f hf hfD x := by
  apply neg_nonpos.mp
  refine le_of_tendsto
    ((A.tendsto_analyticCubeResolvent_real mu hf hfD x).neg)
    (Eventually.of_forall fun m ↦ ?_)
  exact neg_nonpos.mpr (A.analyticCubeResolvent_nonneg mu hf hf0 hfD m x)

/-- The real minimal resolvent is measurable on bounded measurable data. -/
theorem measurable_analyticMinimalResolventReal (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.analyticMinimalResolventReal mu f hf hfD) :=
  ((A.measurable_analyticMinimalResolvent mu (measurable_analyticPositivePart hf)
      (abs_analyticPositivePart_le' hfD)).ennreal_toReal).sub
    ((A.measurable_analyticMinimalResolvent mu (measurable_analyticPositivePart hf.neg)
      (abs_analyticPositivePart_le'
        (fun y ↦ by simpa only [Pi.neg_apply, abs_neg] using! hfD y))).ennreal_toReal)

/-- On nonnegative data the signed real form agrees with the real value of
the positive minimal resolvent. -/
theorem analyticMinimalResolventReal_eq_toReal (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticMinimalResolventReal mu f hf hfD x =
      (A.analyticMinimalResolvent mu f hf hfD x).toReal := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  exact tendsto_nhds_unique (A.tendsto_analyticCubeResolvent_real mu hf hfD x)
    (A.tendsto_analyticCubeResolvent mu hf hf0 hD hfD x)

private theorem analyticMinimalResolventReal_sub_of_nonneg (mu : PositiveShift)
    {u v : Vec d → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    {B C E : ℝ}
    (huC : ∀ x, |u x| ≤ C) (hvE : ∀ x, |v x| ≤ E)
    (huvB : ∀ x, |u x - v x| ≤ B) (x : Vec d) :
    A.analyticMinimalResolventReal mu (fun y ↦ u y - v y) (hu.sub hv) huvB x =
      (A.analyticMinimalResolvent mu u hu huC x).toReal -
        (A.analyticMinimalResolvent mu v hv hvE x).toReal := by
  have hneg : ∀ y, |-v y| ≤ E := fun y ↦ by simpa only [abs_neg] using hvE y
  have hsum : ∀ y, |u y + -v y| ≤ C + E := fun y ↦
    (abs_add_le (u y) (-v y)).trans (add_le_add (huC y) (hneg y))
  calc
    A.analyticMinimalResolventReal mu (fun y ↦ u y - v y) (hu.sub hv) huvB x =
        A.analyticMinimalResolventReal mu (fun y ↦ u y + -v y) (hu.add hv.neg)
          hsum x := by
            apply A.analyticMinimalResolventReal_bound_irrel mu
              (hu.sub hv) huvB
              (fun y ↦ by simpa only [sub_eq_add_neg] using! hsum y)
    _ = A.analyticMinimalResolventReal mu u hu huC x +
        A.analyticMinimalResolventReal mu (fun y ↦ -v y) hv.neg hneg x :=
      A.analyticMinimalResolventReal_add mu hu hv.neg huC hneg x
    _ = A.analyticMinimalResolventReal mu u hu huC x -
        A.analyticMinimalResolventReal mu v hv hvE x := by
          have hs : A.analyticMinimalResolventReal mu (fun y ↦ -v y) hv.neg hneg x =
              -A.analyticMinimalResolventReal mu v hv hvE x := by
            simpa only [neg_mul, one_mul] using!
              A.analyticMinimalResolventReal_smul mu (-1) hv hvE x
          rw [hs, sub_eq_add_neg]
    _ = (A.analyticMinimalResolvent mu u hu huC x).toReal -
        (A.analyticMinimalResolvent mu v hv hvE x).toReal := by
          rw [A.analyticMinimalResolventReal_eq_toReal mu hu hu0 huC x,
            A.analyticMinimalResolventReal_eq_toReal mu hv hv0 hvE x]

/-- The signed real analytic minimal resolvent satisfies the resolvent
equation at both orders. -/
theorem analyticMinimalResolventReal_resolventEquation
    (lam mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    A.analyticMinimalResolventReal lam f hf hfD x =
      A.analyticMinimalResolventReal mu f hf hfD x +
        ((mu : ℝ) - (lam : ℝ)) *
          A.analyticMinimalResolventReal lam
            (A.analyticMinimalResolventReal mu f hf hfD)
            (A.measurable_analyticMinimalResolventReal mu hf hfD)
            (D := D / (mu : ℝ))
            (A.abs_analyticMinimalResolventReal_le mu hf hfD) x := by
  have hD : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  let fp : Vec d → ℝ := analyticPositivePart f
  let fn : Vec d → ℝ := analyticPositivePart fun y ↦ -f y
  let up : Vec d → ℝ := fun y ↦
    (A.analyticMinimalResolvent mu fp (measurable_analyticPositivePart hf)
      (abs_analyticPositivePart_le' hfD) y).toReal
  let un : Vec d → ℝ := fun y ↦
    (A.analyticMinimalResolvent mu fn (measurable_analyticPositivePart hf.neg)
      (abs_analyticPositivePart_le'
        (fun z ↦ by simpa only [abs_neg] using hfD z)) y).toReal
  have hfp0 : ∀ y, 0 ≤ fp y := fun y ↦ le_max_right (f y) 0
  have hfn0 : ∀ y, 0 ≤ fn y := fun y ↦ le_max_right (-f y) 0
  have hfpD : ∀ y, |fp y| ≤ D := abs_analyticPositivePart_le' hfD
  have hfnD : ∀ y, |fn y| ≤ D :=
    abs_analyticPositivePart_le' (fun y ↦ by simpa only [abs_neg] using hfD y)
  have hC : 0 ≤ D / (mu : ℝ) := div_nonneg hD mu.property.le
  have hup : Measurable up :=
    (A.measurable_analyticMinimalResolvent mu
      (measurable_analyticPositivePart hf) hfpD).ennreal_toReal
  have hun : Measurable un :=
    (A.measurable_analyticMinimalResolvent mu
      (measurable_analyticPositivePart hf.neg) hfnD).ennreal_toReal
  have hup0 : ∀ y, 0 ≤ up y := fun _ ↦ ENNReal.toReal_nonneg
  have hun0 : ∀ y, 0 ≤ un y := fun _ ↦ ENNReal.toReal_nonneg
  have hupC : ∀ y, |up y| ≤ D / (mu : ℝ) := by
    intro y
    rw [abs_of_nonneg (hup0 y)]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (A.analyticMinimalResolvent_le mu (measurable_analyticPositivePart hf)
        hfp0 hD hfpD y)
  have hunC : ∀ y, |un y| ≤ D / (mu : ℝ) := by
    intro y
    rw [abs_of_nonneg (hun0 y)]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (A.analyticMinimalResolvent_le mu (measurable_analyticPositivePart hf.neg)
        hfn0 hD hfnD y)
  have hinner : A.analyticMinimalResolventReal lam
      (A.analyticMinimalResolventReal mu f hf hfD)
      (A.measurable_analyticMinimalResolventReal mu hf hfD)
      (A.abs_analyticMinimalResolventReal_le mu hf hfD) x =
      (A.analyticMinimalResolvent lam up hup hupC x).toReal -
        (A.analyticMinimalResolvent lam un hun hunC x).toReal := by
    change A.analyticMinimalResolventReal lam (fun y ↦ up y - un y)
        (hup.sub hun) (A.abs_analyticMinimalResolventReal_le mu hf hfD) x = _
    exact A.analyticMinimalResolventReal_sub_of_nonneg lam hup hun hup0 hun0
      hupC hunC (A.abs_analyticMinimalResolventReal_le mu hf hfD) x
  have hp := A.analyticMinimalResolvent_toReal_resolventEquation lam mu
    (measurable_analyticPositivePart hf) hfp0 hD hfpD x
  have hn := A.analyticMinimalResolvent_toReal_resolventEquation lam mu
    (measurable_analyticPositivePart hf.neg) hfn0 hD hfnD x
  rw [hinner]
  unfold analyticMinimalResolventReal
  change
    (A.analyticMinimalResolvent lam fp _ hfpD x).toReal -
      (A.analyticMinimalResolvent lam fn _ hfnD x).toReal =
    ((A.analyticMinimalResolvent mu fp _ hfpD x).toReal -
      (A.analyticMinimalResolvent mu fn _ hfnD x).toReal) +
      ((mu : ℝ) - (lam : ℝ)) *
        ((A.analyticMinimalResolvent lam up hup hupC x).toReal -
          (A.analyticMinimalResolvent lam un hun hunC x).toReal)
  linear_combination hp - hn

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
