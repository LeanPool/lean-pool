/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantEnergyAndFenchelSlots
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantFenchelProbe
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.AdjointRecentHeadEstimate
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CarrierIntegrabilityConditions

/-!
# High-contrast homogenization: Entry.Response.Rows.CellOscillationSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Oscillation and Cell Parts of the Cutoff-Mean Defect

Weighted averages are not additive in the weight, but they split at a chosen level `c`: the
average of `w * f` is the average of the fluctuation `(w - c) * f` plus `c` times the unweighted
average of `f`. Applying this cell by cell, after first replacing the average over the adapted
cell by the flat average over its triadic subcells by exact partition averaging, splits the
normalized average of `(φ - 1) * g` into a within-cell oscillation part, estimated pathwise, and
a cell part carrying the departure of the subcell cutoff values from a common level; the
state-valued analogue for the doubled optimizer state `X = (∇v, b∇v)` is recorded
coordinatewise. The file also shows the cell average of the crossed pairing `⟨Y₂, ∇u⟩ +
⟨Y₁, a∇u⟩` is `P`-integrable on every aligned cell of every generation below the terminal
one, dominating its Fenchel-probe bound by Young's inequality.  The splitting of the normalized
cutoff-weighted average into its within-cell oscillation part and its cell part, together with the
exact partition averaging behind it, serves `e.response.cutoff.estimate`; the `P`-integrability of
the cell average of the crossed pairing on every aligned cell below the terminal one serves
`p.response.transfer`.
-/

section
/-!
## The cell average of the crossed pairing is integrable in the sample

The descendant sum of the oscillation half of `p.response.transfer` reads the cell average of the
crossed pairing `⟨Y₂, ∇u⟩ + ⟨Y₁, a ∇u⟩` of the terminal optimizer on every aligned cell of every
generation below the terminal one.  That readout is measurable in the sample by
`CarrierIntegrabilityConditions`, and the Fenchel probe of `DescendantFenchelProbe` dominates its
modulus by the
two-term head of the cell times the square root of twice the doubled cell energy.  Young's
inequality turns that product into the sum of the squared head and the cell energy, both of which
are `P`-integrable — the first from the entrywise integrability of the pathwise coarse block on
that cell, the second from the integrability of the terminal response.  So the readout is
`P`-integrable on every cell of every generation.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Young's inequality in the shape the Fenchel probe leaves behind: a nonnegative head times the
square root of twice a doubled nonnegative energy is at most the squared head plus the energy. -/
private theorem mul_sqrt_two_mul_two_mul_le {G D : ℝ} (hD : 0 ≤ D) :
    G * Real.sqrt (2 * (2 * D)) ≤ G ^ 2 + D := by
  have h4 : (2 : ℝ) * (2 * D) = 2 ^ 2 * D := by ring
  have hsqrt : Real.sqrt (2 * (2 * D)) = 2 * Real.sqrt D := by
    rw [h4, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) D,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  have hsq : 0 ≤ (G - Real.sqrt D) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt hD] at hsq
  rw [hsqrt]
  linarith only [hsq]

/-- **The annealed cell energy of the terminal optimizer on an aligned cell of any generation,
minus sign.**  `TerminalHalfEnergyIntegrability` makes the readout `P`-integrable on the cells of
one fixed
generation aligned with a scale `s` under `t = s + H`; every generation `t - m` is that statement
at `s := t - m` and `H := m`. -/
theorem integrable_volumeAverage_energy_depth_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := by
  have ht' : t = (t - (m : ℤ)) + (m : ℤ) := by ring
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
    m (t - (m : ℤ)) t ht' e uM hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F
      hm m (t - (m : ℤ)) t ht' e uM hmax w hw).aestronglyMeasurable) W hW

/-- **The annealed cell energy of the terminal optimizer on an aligned cell of any generation,
plus sign.**  The adjoint twin of `integrable_volumeAverage_energy_depth_respCoeffMinus`. -/
theorem integrable_volumeAverage_energy_depth_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := by
  have ht' : t = (t - (m : ℤ)) + (m : ℤ) := by ring
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
    m (t - (m : ℤ)) t ht' e uP hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F
      hm m (t - (m : ℤ)) t ht' e uP hmax w hw).aestronglyMeasurable) W hW

/-- **The cell average of the crossed pairing is `P`-integrable, minus sign.**  On every aligned
cell of every generation below the terminal one, the cell average of the scalar crossed pairing of
the deterministic dual variable with the terminal optimizer state is `P`-integrable. -/
theorem integrable_volumeAverage_cross_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hblk : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w))
    (Y : BlockVec d) (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
        + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq _ W).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W ⊆ respCell jStar F t :=
    adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hmeas := measurable_volumeAverage_cross_optimizerField_respCoeffMinus P jStar hjStar F hm
    t e uM hmax hV hVU Y
  -- the squared two-term head of the cell
  have hUL0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).1
  have hLR0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).2
  have hheadsq : Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) (respCoeffMinus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffMinus F a)).lowerRight Y.2))) ^ 2) P :=
    integrable_sq_sqrt_add_sqrt_coarseBlockMatrix Y
      (integrable_vecDot_coarseBlockMatrix_upperLeft Y
        (integrable_coarseBlockMatrix_upperLeft_respCoeffMinus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      (integrable_vecDot_coarseBlockMatrix_lowerRight Y
        (integrable_coarseBlockMatrix_lowerRight_respCoeffMinus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      hUL0 hLR0
  have hE := integrable_volumeAverage_energy_depth_respCoeffMinus P jStar hjStar F hm t e uM
    hmax hJt m W hW
  refine Integrable.mono' (hheadsq.add hE) hmeas.aestronglyMeasurable ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  have hbd := abs_volumeAverage_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter_le jStar hjStar
    F hm t m a (uM a) Y hW
    (fun i => (integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hq t F a
      (uM a) m W hW i).1)
    (fun i => (integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hq t F a
      (uM a) m W hW i).2)
    ((integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uM a) hW).1 Y.2)
    ((integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uM a) hW).2 Y.1)
  have hDnn := zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffMinus_adaptedCellAtCenter
    jStar hjStar F hm t m a (uM a) hW
  have hyoung := mul_sqrt_two_mul_two_mul_le (G := Real.sqrt (vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1))
    + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (respCoeffMinus F a)).lowerRight Y.2))) hDnn
  simp only [Pi.add_apply]
  linarith only [hbd, hyoung]

/-- **The cell average of the crossed pairing is `P`-integrable, plus sign.**  The adjoint twin of
`integrable_volumeAverage_cross_optimizerField_respCoeffMinus`. -/
theorem integrable_volumeAverage_cross_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hblk : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w))
    (Y : BlockVec d) (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
        + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq _ W).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W ⊆ respCell jStar F t :=
    adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hmeas := measurable_volumeAverage_cross_optimizerField_respCoeffPlus P jStar hjStar F hm
    t e uP hmax hV hVU Y
  have hUL0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).1
  have hLR0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).2
  have hheadsq : Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) (respCoeffPlus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffPlus F a)).lowerRight Y.2))) ^ 2) P :=
    integrable_sq_sqrt_add_sqrt_coarseBlockMatrix Y
      (integrable_vecDot_coarseBlockMatrix_upperLeft Y
        (integrable_coarseBlockMatrix_upperLeft_respCoeffPlus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      (integrable_vecDot_coarseBlockMatrix_lowerRight Y
        (integrable_coarseBlockMatrix_lowerRight_respCoeffPlus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      hUL0 hLR0
  have hE := integrable_volumeAverage_energy_depth_respCoeffPlus P jStar hjStar F hm t e uP
    hmax hJt m W hW
  refine Integrable.mono' (hheadsq.add hE) hmeas.aestronglyMeasurable ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  have hbd := abs_volumeAverage_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter_le jStar hjStar
    F hm t m a (uP a) Y hW
    (fun i => (integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hq t F a
      (uP a) m W hW i).1)
    (fun i => (integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hq t F a
      (uP a) m W hW i).2)
    ((integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uP a) hW).1 Y.2)
    ((integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uP a) hW).2 Y.1)
  have hDnn := zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffPlus_adaptedCellAtCenter
    jStar hjStar F hm t m a (uP a) hW
  have hyoung := mul_sqrt_two_mul_two_mul_le (G := Real.sqrt (vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1))
    + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (respCoeffPlus F a)).lowerRight Y.2))) hDnn
  simp only [Pi.add_apply]
  linarith only [hbd, hyoung]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Splitting a weighted cell average over a partition

Weighted averages are not additive in the weight, but they split at a chosen level `c`:
the average of `w * f` is the average of the fluctuation `(w - c) * f` plus the level `c`
times the unweighted average of `f`.  Applying this identity cell by cell and recombining
with the equal-volume partition identity gives the cell decomposition behind the two
cutoff-mean rows of `e.response.cutoff.estimate`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- **Splitting a weighted cell average at a level `c`.**  For any constant `c`, the average
of `w * f` over `V` is the average of `(w - c) * f` over `V` plus `c` times the average of `f`
over `V`.  The first summand records the part of the weight that fluctuates about the level `c`;
the second is that level times the unweighted cell average.  The identity is purely pointwise
under the average and needs only the integrability of the two summands on `V`. -/
theorem volumeAverage_weight_mul_split {d : ℕ} {V : Set (Vec d)} (w : Vec d → ℝ) (c : ℝ)
    (f : Vec d → ℝ)
    (h1 : IntegrableOn (fun x => (w x - c) * f x) V)
    (h2 : IntegrableOn (fun x => c * f x) V) :
    volumeAverage V (fun x => w x * f x)
      = volumeAverage V (fun x => (w x - c) * f x) + c * volumeAverage V f := by
  have hdecomp : (fun x => w x * f x) =
      (fun x => (w x - c) * f x) + (fun x => c * f x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have hsmul : volumeAverage V (fun x => c * f x) = c * volumeAverage V f := by
    rw [show (fun x => c * f x) = c • f by
      funext x
      simp [smul_eq_mul]]
    exact volumeAverage_smul V c f
  rw [hdecomp, volumeAverage_add h1 h2, hsmul]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Exact partition averaging on the adapted cell

The cell decomposition used in the response cutoff estimate first replaces the average over the
adapted cell `HighContrast.adaptedCell q t` by the flat average of the normalized averages over its
`3^{nd}` triadic subcells `adaptedCellAtCenter q (t - n) w`, `w ∈ triadicIndexBox d n`.  Unlike the
recombination of the optimizer energy, this step needs neither positivity of the integrand nor a
bound on it: the parent cell is the disjoint union of its open subcells up to the null grid seams,
the subcells have equal volume, and the identity follows from finite additivity of the integral.
This file records the index box nonemptiness used to normalize the finite sum and the exact
averaging identity itself.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The triadic index box of generation `n` is nonempty: the constant index `0` has every
coordinate in the interval `[-(3^n - 1)/2, (3^n - 1)/2]`. -/
theorem triadicIndexBox_nonempty (d : ℕ) [NeZero d] (n : ℕ) : (triadicIndexBox d n).Nonempty := by
  refine ⟨0, ?_⟩
  rw [triadicIndexBox, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_Icc.mpr
    ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩

/-- **Exact partition averaging on the adapted cell** (`e.response.cutoff.estimate`).  For an
invertible grid `q`, generation `t` and depth `n`, the normalized average of an integrand `g`
over the adapted cell `HighContrast.adaptedCell q t` is the flat average of the normalized averages
of `g` over the `3^{nd}` triadic subcells `adaptedCellAtCenter q (t - n) w`.  Only the
integrability of
`g` on the parent cell is needed; the subcells cover the parent up to the null grid seams, and
their equal volumes make the unweighted mean the correct recombination. -/
theorem volumeAverage_adaptedCell_eq_flat_average {d : ℕ} [NeZero d] (q : Mat d)
    (hq : IsUnit q) (t : ℤ) (n : ℕ) (g : Vec d → ℝ)
    (hint : IntegrableOn g (HighContrast.adaptedCell q t)) :
    volumeAverage (HighContrast.adaptedCell q t) g
      = ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n, volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g := by
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hUpos : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  exact (average_over_aePartition (Z := triadicIndexBox d n)
    (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
    (U := HighContrast.adaptedCell q t) (g := g)
    (fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet)
    (fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww')
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (adaptedCell_diff_biUnion_null q hq t n)
    (fun w _ => volume_adaptedCellAtCenter_card_eq q hq t n w)
    hint hUpos hUfin (triadicIndexBox_nonempty d n)).symm

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff-fluctuation average splits on the adapted cell

The cutoff estimate `e.response.cutoff.estimate` bounds the normalized average over the terminal
cell `HighContrast.adaptedCell q t` of the pairing `(φ - 1) * g`.  The two terms of that bound have
different natures: the oscillation of the cutoff inside a scale-`s` subcell is estimated pathwise,
whereas the departure of the subcell values from a common level is only controlled after taking
expectations.  This file records the exact algebraic identity that separates them.

The terminal average is first written as the flat average of the normalized averages over the
`3^{nd}` triadic subcells `adaptedCellAtCenter q (t - n) w` by
`volumeAverage_adaptedCell_eq_flat_average`.
Each subcell term is then split at the level `⨍_{cell} φ - 1` of its own cutoff average by
`volumeAverage_weight_mul_split`: the fluctuation part `(φ - ⨍_{cell} φ) * g` carries the
within-cell oscillation, and the cell part `(⨍_{cell} φ - 1) * ⨍_{cell} g` carries the subcell
cutoff values.  Distributing the flat mean over the two parts gives the stated decomposition.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Splitting the cutoff-fluctuation average over the adapted cell**
(`e.response.cutoff.estimate`).  Let `q` be an invertible grid, `t` a generation, `n` a depth and
`φ`, `g` functions on the terminal cell `HighContrast.adaptedCell q t`, with `(φ - 1) * g`
integrable
there.  Assume that on every depth-`n` triadic subcell `adaptedCellAtCenter q (t - n) w` the two
summands
of the split of `(φ - 1) * g` at the level `⨍_{cell} φ - 1` are integrable, namely the fluctuation
`(φ - ⨍_{cell} φ) * g` and the level term `(⨍_{cell} φ - 1) * g`.  Then the terminal average of
`(φ - 1) * g` is the flat average over the subcells of the within-cell oscillation
`⨍_{cell} (φ - ⨍_{cell} φ) * g` plus the flat average over the subcells of the cell part
`(⨍_{cell} φ - 1) * ⨍_{cell} g`.  The identity is purely algebraic and needs no positivity of
either function. -/
theorem volumeAverage_fluct_eq_osc_add_cell {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) (φ g : Vec d → ℝ)
    (hint : IntegrableOn (fun x => (φ x - 1) * g x) (HighContrast.adaptedCell q t))
    (h1 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
      (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) * g x)
      (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * g x)
      = ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
        + ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g := by
  rw [volumeAverage_adaptedCell_eq_flat_average q hq t n (fun x => (φ x - 1) * g x) hint]
  have hsum : ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => (φ x - 1) * g x)
      = ∑ w ∈ triadicIndexBox d n,
          (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
            + (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g) := by
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hf : (fun x =>
          ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
        = (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x) := by
      funext x
      ring
    have havg : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x =>
            ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
        = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x) := by
      rw [hf]
    have hint1 : IntegrableOn
        (fun x =>
          ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
      rw [hf]
      exact h1 w hw
    calc volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => (φ x - 1) * g x)
        = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x =>
                ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
            + (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g :=
          volumeAverage_weight_mul_split (fun x => φ x - 1)
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) g hint1 (h2 w hw)
      _ = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
            + (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g := by
          rw [havg]
  rw [hsum, Finset.sum_add_distrib, mul_add]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff-mean defect splits coordinatewise on the adapted cell

The cutoff-mean defect of `e.response.cutoff.estimate` is, in each coordinate of each slot, the
`(φ - 1)`-weighted average of the optimizer state `X = (∇v, b ∇v)`
(`cutoffStateMeanAux_fst_sub`, `cutoffStateMeanAux_snd_sub`).  The cell decomposition of
`volumeAverage_fluct_eq_osc_add_cell` then splits that average over the depth-`n` triadic
subcells into a within-cell oscillation part of size `3^{-n}` and a cell part that cancels
after expectation.  This is the state-valued analogue of the split already landed for the
energy.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Coordinatewise split of the first cutoff-mean defect** (`e.response.cutoff.estimate`).
For an invertible grid `q`, a generation `t`, a depth `n` and a cutoff `φ`, the first-coordinate
cutoff-mean defect at the load coordinate `i`, namely `(cutoffStateMeanAux U φ b v).1 i` minus
the plain cell average `(cellAverage U (optimizerField b v)).1 i`, equals the flat average over
the depth-`n` triadic subcells of the within-cell oscillation
`⨍_{cell} (φ - ⨍_{cell} φ) * (X).1 i` plus the flat average of the cell part
`(⨍_{cell} φ - 1) * ⨍_{cell} (X).1 i`.  The identity is purely algebraic: it needs only the
integrability of the cutoff-weighted coordinate, of the coordinate itself, and of the two
summands of the split on every subcell. -/
theorem cutoffStateMeanAux_fst_eq_osc_add_cell {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) (φ : Vec d → ℝ) {b : CoeffField d}
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t)) (i : Fin d)
    (hφG : IntegrableOn (fun x => φ x * (optimizerField b v x).1 i) (HighContrast.adaptedCell q t))
    (hG : IntegrableOn (fun x => (optimizerField b v x).1 i) (HighContrast.adaptedCell q t))
    (hint : IntegrableOn (fun x => (φ x - 1) * (optimizerField b v x).1 i)
      (HighContrast.adaptedCell q t))
    (h1 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
        (optimizerField b v x).1 i) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
        (optimizerField b v x).1 i) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).1 i
        - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).1 i
      = ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
                (optimizerField b v x).1 i)
        + ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (fun x => (optimizerField b v x).1 i) := by
  have hsub : (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).1 i
      - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).1 i
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * (optimizerField b v x).1 i) := by
    simp only [cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_sub hφG hG]
    refine congrArg (volumeAverage (HighContrast.adaptedCell q t)) ?_
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  exact volumeAverage_fluct_eq_osc_add_cell q hq t n φ
    (fun x => (optimizerField b v x).1 i) hint h1 h2

/-- **Coordinatewise split of the second cutoff-mean defect** (`e.response.cutoff.estimate`).
For an invertible grid `q`, a generation `t`, a depth `n` and a cutoff `φ`, the second-coordinate
cutoff-mean defect at the flux coordinate `i`, namely `(cutoffStateMeanAux U φ b v).2 i` minus
the plain cell average `(cellAverage U (optimizerField b v)).2 i`, equals the flat average over
the depth-`n` triadic subcells of the within-cell oscillation
`⨍_{cell} (φ - ⨍_{cell} φ) * (X).2 i` plus the flat average of the cell part
`(⨍_{cell} φ - 1) * ⨍_{cell} (X).2 i`.  The identity is purely algebraic: it needs only the
integrability of the cutoff-weighted coordinate, of the coordinate itself, and of the two
summands of the split on every subcell. -/
theorem cutoffStateMeanAux_snd_eq_osc_add_cell {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) (φ : Vec d → ℝ) {b : CoeffField d}
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t)) (i : Fin d)
    (hφG : IntegrableOn (fun x => φ x * (optimizerField b v x).2 i) (HighContrast.adaptedCell q t))
    (hG : IntegrableOn (fun x => (optimizerField b v x).2 i) (HighContrast.adaptedCell q t))
    (hint : IntegrableOn (fun x => (φ x - 1) * (optimizerField b v x).2 i)
      (HighContrast.adaptedCell q t))
    (h1 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
        (optimizerField b v x).2 i) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
        (optimizerField b v x).2 i) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).2 i
        - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).2 i
      = ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
                (optimizerField b v x).2 i)
        + ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (fun x => (optimizerField b v x).2 i) := by
  have hsub : (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).2 i
      - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).2 i
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * (optimizerField b v x).2 i) := by
    simp only [cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_sub hφG hG]
    refine congrArg (volumeAverage (HighContrast.adaptedCell q t)) ?_
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  exact volumeAverage_fluct_eq_osc_add_cell q hq t n φ
    (fun x => (optimizerField b v x).2 i) hint h1 h2

end

end HCPolySupport.HighContrast.Multiscale
end
