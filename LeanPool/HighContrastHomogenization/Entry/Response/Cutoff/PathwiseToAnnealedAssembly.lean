/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# High-contrast homogenization: Entry.Response.Cutoff.PathwiseToAnnealedAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembling the Annealed Cutoff Bound From Its Pathwise Form

This file completes the reduction of the annealed cutoff-pairing bound of
`e.response.cutoff.estimate` to its pathwise form: the elementary integration step that turns a
pathwise domination by the weak response energy `respWeakEnergy` into a bound on its expectation,
and the resulting pathwise-to-annealed frames for both signs of the recentring, combined into a
single positive constant bounding the annealed pairing for either sign. It records the weak
quantities `W^-` and `W^+` - the weak energies of the two recentred coefficients at the two
response loads on the selected grid - together with `W^-`'s defining equation and both signs'
nonnegativity. It closes with two measurability prerequisites the sample-dependent weak quantity
needs: cell averages of the canonical optimizer state are measurable in the sample, and a
countable sum such as the scale-average seminorm is measurable whenever its summands are.
-/

section
/-!
## Passing a pathwise cutoff bound through the law

The weak response energy `respWeakEnergy` bounds the scale-weighted squared scale-average
seminorm of the doubled optimizer state, uniformly over admissible families of cell
maximizers.  This file records the elementary integration step that turns a bound holding at
each sample into a bound on the expectation: if a pathwise quantity is dominated by a
nonnegative multiple of that seminorm square, and the seminorm square is Bochner integrable,
then the expectation of the absolute value of the quantity is bounded by the same multiple of
the weak response energy.  This is the integration in the sample variable `a` of the weak
estimate `e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- If a pathwise quantity `G` is dominated, sample by sample, by `C₀` times the
scale-weighted squared scale-average seminorm of the doubled optimizer state of an admissible
family of cell maximizers, with `C₀ ≥ 0`, and that seminorm square is Bochner integrable, then
the expectation of `|G|` is at most `C₀` times the weak response energy `W`.  The integrability
hypothesis is what makes the dominating function Bochner integrable, so that monotonicity of the
integral applies; the branch where `|G|` is not integrable is handled by the junk value of the
Bochner integral and the nonnegativity of `W`.  This is the annealed form of
`e.response.weak.estimate`. -/
theorem integral_abs_le_respWeakEnergy_of_pathwise {d : ℕ}
    (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ) (M0 : BlockMat d) (p q' : Vec d)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) (G : CoeffSpace d → ℝ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hbdd : BddAbove (respWeakEnergySet P qq t M0 p q' b Y))
    (u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t))
    (hu : ∀ a, IsResponseMaximizer (HighContrast.adaptedCell qq t) p q' (b a) (u a))
    (hintegrable : Integrable (fun a => besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt M0)
          (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
            (optimizerField (b a) (u a)) - Y)) ^ 2) P)
    (hptwise : ∀ a : CoeffSpace d, |G a| ≤
      C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt M0)
          (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
            (optimizerField (b a) (u a)) - Y)) ^ 2)) :
    (∫ a, |G a| ∂P) ≤ C₀ * respWeakEnergy P qq t M0 p q' b Y := by
  set Gsq : CoeffSpace d → ℝ := fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt M0)
        (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
          (optimizerField (b a) (u a)) - Y)) ^ 2
  have hsup : (3 : ℝ) ^ (-(t : ℝ)) * ∫ a, Gsq a ∂P ≤ respWeakEnergy P qq t M0 p q' b Y :=
    le_respWeakEnergy P qq t M0 p q' b Y hbdd u hu
  by_cases hI : Integrable (fun a => |G a|) P
  · have hIg : Integrable (fun a => C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * Gsq a)) P :=
      (hintegrable.const_mul ((3 : ℝ) ^ (-(t : ℝ)))).const_mul C₀
    calc (∫ a, |G a| ∂P)
        ≤ ∫ a, C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * Gsq a) ∂P := integral_mono hI hIg hptwise
      _ = C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * ∫ a, Gsq a ∂P) := by
          rw [integral_const_mul, integral_const_mul]
      _ ≤ C₀ * respWeakEnergy P qq t M0 p q' b Y := mul_le_mul_of_nonneg_left hsup hC₀
  · rw [integral_undef hI]
    exact mul_nonneg hC₀ (respWeakEnergy_nonneg P qq t M0 p q' b Y)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed cutoff pairing bound from its pathwise form

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the expectation, over
the sample law, of the absolute value of the volume average over the selected cell of the
cutoff-weighted pairing of the centred optimizer field with the recentring vector.  This file
reduces the annealed bound to its pathwise form: assuming the deterministic estimate at every
sample, the singular-grid branch is discharged by the degeneration of the adapted cell (every
volume average collapses to the junk value `0`) and the positive-definite branch by monotonicity
of the Bochner integral, so that only the pathwise estimate remains as a hypothesis.  This is the
annealed form of `e.response.cutoff.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The annealed cutoff pairing bound `e.response.cutoff.estimate`, reduced to the pathwise
estimate `hpath`: if at every sample and for every elliptic data the pairing average is dominated
by `C₀` times the scale-weighted squared scale-average seminorm of the doubled optimizer state,
and that seminorm square is Bochner integrable, then the expectation of the absolute pairing is at
most `C₀` times the weak response energy `W^-`.  The dichotomy
`metric_posDef_or_respGrid_det_eq_zero` splits the proof: on the singular-grid branch the adapted
cell is Lebesgue null and the integral vanishes, while on the positive-definite branch the
pathwise bound is integrated against the law. -/
theorem exists_integral_abs_pairing_le_respWeak_of_pathwise (d : ℕ) [NeZero d]
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpath : ∀ (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ),
       2 * d ≤ 3 ^ jStar → IsResponseCutoff (respGrid jStar F) t φ →
       (explicitCanonicalMetric F).PosDef →
       ∀ (b : CoeffField d) (Y : BlockVec d)
         (u : AHarmonicFunction b (respCell jStar F t)),
         (∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
           IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
             b =ᵐ[volumeMeasureOn (respCell jStar F t)] f) →
         |volumeAverage (respCell jStar F t) (fun x =>
             φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))| ≤
           C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
             blockMatVecMul (blockSqrt (respM0 F))
               (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                 (optimizerField b u) - Y)) ^ 2)) :
    ∀ (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
      (t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
      2 * d ≤ 3 ^ jStar →
      IsResponseCutoff (respGrid jStar F) t φ →
      ∀ uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t),
        (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) →
        Integrable (fun a => besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffMinus F a) (uM a)) -
              respYMinus P jStar F t e)) ^ 2) P →
        (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
            φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
                - (respYMinus P jStar F t e).1)
              ((optimizerField (respCoeffMinus F a) (uM a) x).2
                - (respYMinus P jStar F t e).2))| ∂P)
          ≤ C₀ * respWMinus P jStar F t e := by
  intro P jStar F t e φ hjStar hφ uM hu hintegrable
  rcases metric_posDef_or_respGrid_det_eq_zero jStar F with hm | hdet
  · -- Positive-definite branch: integrate the pathwise bound against the law.
    let G : CoeffSpace d → ℝ := fun a => volumeAverage (respCell jStar F t) (fun x =>
      φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
          - (respYMinus P jStar F t e).1)
        ((optimizerField (respCoeffMinus F a) (uM a) x).2
          - (respYMinus P jStar F t e).2))
    have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
    have hbdd : BddAbove (respWeakEnergySet P (respGrid jStar F) t (respM0 F)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
        (respYMinus P jStar F t e)) :=
      bddAbove_respWeakEnergySet_respWMinus P jStar F t e hgrid
    have hptwise : ∀ a : CoeffSpace d, |G a| ≤
        C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField (respCoeffMinus F a) (uM a)) - respYMinus P jStar F t e)) ^ 2) := by
      intro a
      exact hpath jStar F t φ hjStar hφ hm (respCoeffMinus F a) (respYMinus P jStar F t e) (uM a)
        (exists_elliptic_representative_respCoeffMinus (respGrid jStar F) hgrid t F a)
    exact integral_abs_le_respWeakEnergy_of_pathwise P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
      (respYMinus P jStar F t e) G C₀ hC₀ hbdd uM hu hintegrable hptwise
  · -- Singular-grid branch: the adapted cell is null, so every average is the junk value `0`.
    have hzero : (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
            - (respYMinus P jStar F t e).1)
          ((optimizerField (respCoeffMinus F a) (uM a) x).2
            - (respYMinus P jStar F t e).2))| ∂P) = 0 := by
      simpa only [respCell] using
        (integral_abs_volumeAverage_adaptedCell_eq_zero_of_det_eq_zero (P := P)
          (q := respGrid jStar F) hdet t (fun a x => φ x * vecDot
            ((optimizerField (respCoeffMinus F a) (uM a) x).1 - (respYMinus P jStar F t e).1)
            ((optimizerField (respCoeffMinus F a) (uM a) x).2 - (respYMinus P jStar F t e).2)))
    rw [hzero]
    exact mul_nonneg hC₀ (respWeakEnergy_nonneg P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
      (respYMinus P jStar F t e))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed plus-sign cutoff pairing bound from its pathwise form

The cutoff pairing bound `e.response.cutoff.estimate` is an expectation, over the law of the
coefficient field, of the absolute volume average of the cutoff times the centred doubled
optimizer state.  This file reduces that annealed estimate to its deterministic pathwise form on
the plus-sign branch: the metric dichotomy splits off the singular-grid branch, where every
volume average is the junk value `0`, and on the positive definite branch a pathwise estimate at
each sample is passed through the integral by monotonicity together with the nonnegativity of the
weak response energy.  What remains is a single deterministic inequality, hypothesis `hpath`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The annealed cutoff pairing bound of `e.response.cutoff.estimate`, reduced to its pathwise
form.  Suppose that, for every doubled block on the positive definite branch of the canonical
metric and every admissible coefficient, the cutoff pairing of the centred doubled optimizer
state obeys the deterministic estimate with constant `C₀`.  Then for every probability law of the
coefficient field and every admissible family of cell maximizers, the expectation of the absolute
pairing is at most `C₀` times the weak response energy `W^+`.  The probabilistic content and the
singular-grid branch of the metric dichotomy are discharged here, so the only remaining input is
the pathwise estimate. -/
theorem exists_integral_abs_pairing_le_respWeakPlus_of_pathwise (d : ℕ) [NeZero d]
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpath : ∀ (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ),
      2 * d ≤ 3 ^ jStar → IsResponseCutoff (respGrid jStar F) t φ →
      (explicitCanonicalMetric F).PosDef →
      ∀ (b : CoeffField d) (Y : BlockVec d)
        (u : AHarmonicFunction b (respCell jStar F t)),
        (∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
          IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
            b =ᵐ[volumeMeasureOn (respCell jStar F t)] f) →
        |volumeAverage (respCell jStar F t) (fun x =>
            φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))| ≤
          C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField b u) - Y)) ^ 2)) :
    ∀ (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
      (t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
      2 * d ≤ 3 ^ jStar →
      IsResponseCutoff (respGrid jStar F) t φ →
      ∀ uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
        (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) (uM a)) →
        Integrable (fun a => besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffPlus F a) (uM a)) -
              respYPlus P jStar F t e)) ^ 2) P →
        (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
            φ x * vecDot ((optimizerField (respCoeffPlus F a) (uM a) x).1
                - (respYPlus P jStar F t e).1)
              ((optimizerField (respCoeffPlus F a) (uM a) x).2
                - (respYPlus P jStar F t e).2))| ∂P)
          ≤ C₀ * respWPlus P jStar F t e := by
  intro P jStar F t e φ hjStar hφ uM hu hintegrable
  rcases metric_posDef_or_respGrid_det_eq_zero jStar F with hm | hdet
  · have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
    have hmain := integral_abs_le_respWeakEnergy_of_pathwise P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F)
      (respYPlus P jStar F t e)
      (fun a => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffPlus F a) (uM a) x).1
            - (respYPlus P jStar F t e).1)
          ((optimizerField (respCoeffPlus F a) (uM a) x).2
            - (respYPlus P jStar F t e).2)))
      C₀ hC₀ (bddAbove_respWeakEnergySet_respWPlus P jStar F t e hgrid) uM hu hintegrable
      (fun a => hpath jStar F t φ hjStar hφ hm (respCoeffPlus F a) (respYPlus P jStar F t e)
        (uM a) (exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a))
    simpa only [respWPlus_eq] using hmain
  · have hzero : (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffPlus F a) (uM a) x).1
            - (respYPlus P jStar F t e).1)
          ((optimizerField (respCoeffPlus F a) (uM a) x).2
            - (respYPlus P jStar F t e).2))| ∂P) = 0 := by
      simpa only [respCell] using
        integral_abs_volumeAverage_adaptedCell_eq_zero_of_det_eq_zero P hdet t
          (fun a x => φ x * vecDot
            ((optimizerField (respCoeffPlus F a) (uM a) x).1 - (respYPlus P jStar F t e).1)
            ((optimizerField (respCoeffPlus F a) (uM a) x).2 - (respYPlus P jStar F t e).2))
    rw [hzero]
    simpa only [respWPlus_eq] using mul_nonneg hC₀ (respWeakEnergy_nonneg P (respGrid jStar F) t
      (respM0 F) (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F)
      (respYPlus P jStar F t e))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The weak quantities of the two signs

The weak response quantities `W^-` and `W^+` of the response estimate are the weak energies of
the two recentred coefficients `a_- = a - g` and `a_+ = a^t + g` at the two response loads
`q^-` and `q^+`, evaluated on the selected grid with the self-dual metric `M_0`.  This file
records `W^-`'s defining equation (`respWMinus_eq`; `respWPlus_eq` lives with `respWPlus`'s own
definition) and their nonnegativity, the two elementary facts used whenever `W^±` is consumed.
These are the elementary parts of the weak estimate `e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- `W^-` is the weak energy of the recentred coefficient `a_- = a - g` at the load `q^-`: by
definition `W^- = W(U_t, p, q^-; a_-, Y^-)` for the weak response energy `W`. -/
theorem respWMinus_eq {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) :
    respWMinus P jStar F t e
      = respWeakEnergy P (respGrid jStar F) t (respM0 F) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F) (respYMinus P jStar F t e) := rfl

/-- The weak response quantity `W^-` is nonnegative: it is the weak energy of the recentred
coefficient `a_-` at the load `q^-`. -/
theorem respWMinus_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) : 0 ≤ respWMinus P jStar F t e := by
  rw [respWMinus_eq]
  exact respWeakEnergy_nonneg P (respGrid jStar F) t (respM0 F)
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
    (respYMinus P jStar F t e)

/-- The weak response quantity `W^+` is nonnegative: it is the weak energy of the recentred
coefficient `a_+` at the load `q^+`. -/
theorem respWPlus_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) : 0 ≤ respWPlus P jStar F t e := by
  rw [respWPlus_eq]
  exact respWeakEnergy_nonneg P (respGrid jStar F) t (respM0 F)
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F)
    (respYPlus P jStar F t e)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed cutoff pairing bound for both signs under one constant

The cutoff pairing bound `e.response.cutoff.estimate` is an expectation, over the law of the
coefficient field, of the absolute volume average of the cutoff times the centred doubled optimizer
state.  The two signs of the recentring are handled by the separate frames
`exists_integral_abs_pairing_le_respWeak_of_pathwise` and
`exists_integral_abs_pairing_le_respWeakPlus_of_pathwise`, each with its own constant `C₀`.  This
file combines the two into a single statement carrying one strictly positive constant valid for
both signs simultaneously; the constant is `max C₀ 1`, which is positive and dominates the constant
of either frame, so each row is obtained by integrating the same pathwise hypothesis at `C₀` and
then relaxing it with the nonnegativity of the corresponding weak response energy `W^±`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The annealed cutoff pairing bound of `e.response.cutoff.estimate` for both signs under one
constant.  Given a nonnegative constant `C₀` and the deterministic pathwise estimate, at every
doubled block on the positive definite branch of the canonical metric and every admissible
coefficient, bounding the cutoff pairing of the centred doubled optimizer state by `C₀` times the
scale-weighted squared scale-average seminorm of the doubled optimizer state, there is a strictly
positive constant `C` such that for every probability law of the coefficient field, every selected
cell and cutoff, and every admissible family of cell maximizers for either recentring, the
expectation of the absolute pairing is at most `C` times the weak response energy `W^-` for the
minus sign and at most `C` times `W^+` for the plus sign.  The constant may be taken to be
`max C₀ 1`. -/
theorem exists_pos_const_integral_abs_pairing_le_respWeak (d : ℕ) [NeZero d]
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpath : ∀ (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ),
       2 * d ≤ 3 ^ jStar → IsResponseCutoff (respGrid jStar F) t φ →
       (explicitCanonicalMetric F).PosDef →
       ∀ (b : CoeffField d) (Y : BlockVec d)
         (u : AHarmonicFunction b (respCell jStar F t)),
         (∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
           IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
             b =ᵐ[volumeMeasureOn (respCell jStar F t)] f) →
         |volumeAverage (respCell jStar F t) (fun x =>
             φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))| ≤
           C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
             blockMatVecMul (blockSqrt (respM0 F))
               (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                 (optimizerField b u) - Y)) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
        (t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
        2 * d ≤ 3 ^ jStar →
        IsResponseCutoff (respGrid jStar F) t φ →
        ∀ uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) →
          Integrable (fun a => besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                  (optimizerField (respCoeffMinus F a) (uM a)) -
                respYMinus P jStar F t e)) ^ 2) P →
          ∀ uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
            (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) →
            Integrable (fun a => besovSeminorm t (fun n z =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                    (optimizerField (respCoeffPlus F a) (uP a)) -
                  respYPlus P jStar F t e)) ^ 2) P →
          (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
                  - (respYMinus P jStar F t e).1)
                ((optimizerField (respCoeffMinus F a) (uM a) x).2
                  - (respYMinus P jStar F t e).2))| ∂P) ≤ C * respWMinus P jStar F t e ∧
            (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField (respCoeffPlus F a) (uP a) x).1
                  - (respYPlus P jStar F t e).1)
                ((optimizerField (respCoeffPlus F a) (uP a) x).2
                  - (respYPlus P jStar F t e).2))| ∂P) ≤ C * respWPlus P jStar F t e := by
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1), ?_⟩
  intro P _ jStar F t e φ hjStar hφ uM huM hIntM uP huP hIntP
  have hminus := exists_integral_abs_pairing_le_respWeak_of_pathwise d C₀ hC₀ hpath
    P jStar F t e φ hjStar hφ uM huM hIntM
  have hplus := exists_integral_abs_pairing_le_respWeakPlus_of_pathwise d C₀ hC₀ hpath
    P jStar F t e φ hjStar hφ uP huP hIntP
  exact ⟨le_trans hminus (mul_le_mul_of_nonneg_right (le_max_left C₀ 1)
      (respWMinus_nonneg P jStar F t e)),
    le_trans hplus (mul_le_mul_of_nonneg_right (le_max_left C₀ 1)
      (respWPlus_nonneg P jStar F t e))⟩

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Cell averages of the canonical optimizer depend measurably on the sample

The weak quantity `W^\pm` of the response estimate `e.response.weak.estimate` is a volume
average, over a measurable subcell, of a coordinate of the canonical optimizer state of a
recentred coefficient sample.  This file records the specialization of the localized weighted
readout to the constant weight `1`, so that a plain cell average is measurable in the sample;
the indicator of a measurable set by a constant is bounded and therefore locally `L²`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The indicator of a measurable set by the constant `1` is square-integrable on every open
bounded convex domain: it is measurable, bounded by `1`, and the restricted Lebesgue measure is
finite.  This is the constant-weight input to the cell averages of the weak quantity
`e.response.weak.estimate`. -/
theorem memScalarL2_indicator_one {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hV : MeasurableSet V) :
    MemScalarL2 U (V.indicator (fun _ : Vec d => (1 : ℝ))) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  refine MemLp.of_bound ?_ 1 (Filter.Eventually.of_forall ?_)
  · exact (measurable_const.indicator hV).aestronglyMeasurable
  · intro x
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx, norm_one, le_refl]
    · simp only [Set.indicator_of_notMem hx, norm_zero, zero_le_one]

/-- The cell average of a coordinate of the canonical minus optimizer state is measurable in the
coefficient sample, for every measurable subcell of the adapted cell.  This is the
constant-weight case of the localized weighted readout entering the weak quantity `W^-` of
`e.response.weak.estimate`. -/
theorem measurable_cellAverage_canonicalRespCoeffMinus {d : ℕ}
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) (alpha : BlockCoord d)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x) alpha) := by
  simpa only [one_mul] using
    (measurable_volumeAverage_weighted_canonicalRespCoeffMinus q hq t F p r alpha hV hVU
      (eta := fun _ : Vec d => (1 : ℝ))
      (memScalarL2_indicator_one (adaptedCell_isOpenBoundedConvexDomain q hq t) hV))

/-- The cell average of a coordinate of the canonical plus optimizer state is measurable in the
coefficient sample, for every measurable subcell of the adapted cell.  This is the
constant-weight case of the localized weighted readout entering the weak quantity `W^+` of
`e.response.weak.estimate`. -/
theorem measurable_cellAverage_canonicalRespCoeffPlus {d : ℕ}
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) (alpha : BlockCoord d)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x) alpha) := by
  simpa only [one_mul] using
    (measurable_volumeAverage_weighted_canonicalRespCoeffPlus q hq t F p r alpha hV hVU
      (eta := fun _ : Vec d => (1 : ℝ))
      (memScalarL2_indicator_one (adaptedCell_isOpenBoundedConvexDomain q hq t) hV))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Measurability of the scale-average seminorm

The scale-average seminorm `besovSeminorm` is a countable sum whose summands are built from the
sample-dependent cell averages of a doubled field. This file records that such a sum is a
measurable function of the sample whenever its summands are, and applies this to
`besovSeminorm`.

The only point requiring care is that the real `tsum` is defined by a junk value `0` where the
series is not summable; the summability set is nevertheless measurable, because for real series it
agrees with the boundedness of the partial sums of the absolute values.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Filter

noncomputable section

variable {d : ℕ}

/-- A pointwise countable sum of measurable real-valued functions is measurable. No summability
hypothesis is needed: the series is summable on a measurable set, where the real `tsum` is the
limit of the partial sums, and takes the junk value `0` off that set. -/
theorem measurable_tsum_of_measurable {α : Type*} [MeasurableSpace α] {g : ℕ → α → ℝ}
    (hg : ∀ n, Measurable (g n)) : Measurable fun a => ∑' n, g n a := by
  classical
  have hpart : ∀ N : ℕ, Measurable fun a => ∑ n ∈ Finset.range N, g n a :=
    fun N => Finset.measurable_sum (Finset.range N) fun n _ => hg n
  have hbdd : MeasurableSet
      {a | BddAbove (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, |g n a|)} :=
    measurableSet_bddAbove_range fun N =>
      Finset.measurable_sum (Finset.range N) fun n _ => by
        simpa only [Real.norm_eq_abs] using (hg n).norm
  have hset : {a | Summable fun n => g n a} =
      {a | BddAbove (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, |g n a|)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨∑' n, |g n a|,
        fun x ⟨N, hN⟩ => hN ▸ Summable.sum_le_tsum (Finset.range N)
          (fun n _ => abs_nonneg _) h.abs⟩
    · intro h
      obtain ⟨C, hC⟩ := h
      exact Summable.of_abs
        (summable_of_sum_range_le (fun n => abs_nonneg _) fun N => hC (Set.mem_range_self N))
  have hsum : MeasurableSet {a | Summable fun n => g n a} := by
    rw [hset]
    exact hbdd
  have hfun : (fun a => if Summable fun n => g n a then
        liminf (fun N => ∑ n ∈ Finset.range N, g n a) atTop else (0 : ℝ)) =
      fun a => ∑' n, g n a := by
    funext a
    by_cases ha : Summable fun n => g n a
    · rw [ite_eq_left ha]
      exact ((Summable.hasSum ha).tendsto_sum_nat).liminf_eq
    · rw [ite_eq_right ha, tsum_eq_zero_of_not_summable ha]
  rw [← hfun]
  exact Measurable.ite hsum (Measurable.liminf hpart) measurable_const

/-- The scale-average seminorm `besovSeminorm` of AK.HC (2.130) is a measurable function of the
sample. Each summand is a constant times the square root of a finite sum of products of the
coordinates of the sample-dependent cell averages, hence measurable; the countable sum is
measurable by `measurable_tsum_of_measurable`. -/
theorem measurable_besovSeminorm {α : Type*} [MeasurableSpace α] (t : ℤ)
    {avg : α → ℕ → (Fin d → ℤ) → BlockVec d}
    (h1 : ∀ n w i, Measurable fun a => (avg a n w).1 i)
    (h2 : ∀ n w i, Measurable fun a => (avg a n w).2 i) :
    Measurable fun a => besovSeminorm t (avg a) := by
  refine measurable_tsum_of_measurable fun n => ?_
  have hinner : Measurable fun a =>
      ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg a n w) (avg a n w) := by
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum (triadicIndexBox d n) fun w _ => ?_
    simp only [blockVecDot, vecDot]
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum Finset.univ fun i _ => ?_
      exact (h1 n w i).mul (h1 n w i)
    · refine Finset.measurable_sum Finset.univ fun i _ => ?_
      exact (h2 n w i).mul (h2 n w i)
  exact hinner.sqrt.const_mul _

end

end HCPolySupport.HighContrast.Multiscale
end
