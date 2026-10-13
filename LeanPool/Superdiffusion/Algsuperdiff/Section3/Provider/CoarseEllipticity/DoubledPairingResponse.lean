/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.BlockBesovPositive
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledPairingSolutions

/-!
# DoubledPairingResponse

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Poincare leg of Step 2 at a doubled response field

Source displays in ABK26: Step 2 of `l.approximate.recurrence.formula`,

* The doubled coarse-grained Poincare inequality `e.CG.Poincare.doubled.vars`
  of `r.cg.poincare.doubled.variables`, which bounds the `H^{-1}`-side seminorm
  of `bfAhom^{-1/2} bfA_m tilde S_z` **linearly** in `|| bfA_m^{1/2} tilde S_z
  ||`;
* The ellipticity display, whose gauged sum is reached here through
  `sqrt_mul_add_inv_sqrt_mul_sq_le_two_mul`.

## What this module supplies

`DoubledCoarsePoincare.lean` states the Poincare inequality for the *explicit*
fields `doubledStateField` / `doubledFluxField` of a primal/adjoint cube-solution
pair.  The Step-2 consumer instead holds an abstract doubled response field `T`
-- the `tilde S_z` produced by `LocalizationRecurrenceMesh` -- and needs the
finite-depth negative `q = 2` seminorms of the two components of
`bfAhom^{-1/2} bfA_m T`, which is the shape in which
`LocalizationFluctuationDuality.two_mul_doubledMuValue_le_besovDualityConst_localizationFz`
consumes them.

Three things bridge the gap.

* `Ch02.doubledResponseTheory ... |>.response_space_by_solutions` turns
  `IsDoubledResponseField` into a solution pair `(v, v^*)` with
  `T = doubledFieldOfSolutions` **almost everywhere** (`e.findSfull`).
* The a.e.-congruence kit below transports the negative seminorms and the
  `mu`-value across that null set.  CoarseGraining carries only the pointwise
  `cubeAverage_congr_on_cubeSet`; the a.e. version is proved here by unfolding
  the depth averages -- each depth-`j` term is a `descendantsAverage` of cube
  averages, and a.e. equality on the parent restricts to every descendant.
* The `BddAbove` kit discharges the boundedness premises of
  `BlockBesovPositive.cubeBesovNegativeVectorPartialSeminormTwo_*_le_blockNegativeBesovTwo`
  from the same `MemVectorL2` and truncation data that
  `DoubledCoarsePoincare.lean` already uses.

`doubledPoincareEllipticityFactor` is the display's own factor, and
`doubledPoincareEllipticityFactor_sq_le` records the arithmetic link in the
gauged form `2 (sigma_0^{-1} Lambda + sigma_0 lambda^{-1})` that the
ellipticity display consumes.

## Binders

`0 < s < 1` is the exponent window of the CoarseGraining coarse Poincare
package (the manuscript names `s = 1` and discards to `s = gamma`); `0 <
sigma_0` is the source's own positivity of the scalar `sigma_0` of
`e.form.of.A.naught`; `[NeZero d]` is typing, dischargeable from the standing
`d >= 2`.  No smallness, moment, measurability or integrability proposition
occurs, and no proposition about the coefficient family beyond its own
`CoeffOn` data is assumed.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2;
  `r.cg.poincare.doubled.variables`; `e.findSfull`; `e.bfA.magic.swapping`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open HCPolySupport.Book
open HCPolySupport.Book.Ch03
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The a.e.-congruence kit for the negative seminorms -/

/-- The cube average sees the function only a.e. on the cube. -/
theorem cubeAverage_congr_ae_cubeSet (Q : TriadicCube d) {u v : Vec d → ℝ}
    (h : u =ᵐ[volume.restrict (cubeSet Q)] v) :
    cubeAverage Q u = cubeAverage Q v := by
  unfold cubeAverage
  exact congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) (integral_congr_ae h)

/-- The vector cube average sees the field only a.e. on the cube. -/
theorem cubeAverageVec_congr_ae_cubeSet (Q : TriadicCube d) {u v : Vec d → Vec d}
    (h : u =ᵐ[volume.restrict (cubeSet Q)] v) :
    cubeAverageVec Q u = cubeAverageVec Q v := by
  funext i
  refine cubeAverage_congr_ae_cubeSet Q ?_
  filter_upwards [h] with x hx
  exact congrFun hx i

/-- A.e. equality on a cube restricts to every subcube. -/
theorem ae_restrict_mono_cubeSet {Q R : TriadicCube d} (hsub : cubeSet R ⊆ cubeSet Q)
    {u v : Vec d → Vec d} (h : u =ᵐ[volume.restrict (cubeSet Q)] v) :
    u =ᵐ[volume.restrict (cubeSet R)] v :=
  Filter.Eventually.filter_mono
    (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl)) h

/-- The closed and open cube carry the same restricted Lebesgue measure. -/
theorem restrict_cubeSet_eq_restrict_openCubeSet (Q : TriadicCube d) :
    volume.restrict (cubeSet Q) = volume.restrict (openCubeSet Q) :=
  Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)

/-- The depth-`j` negative block average is an a.e. functional. -/
theorem cubeBesovNegativeVectorDepthAverage_congr_ae (Q : TriadicCube d) (j : ℕ)
    {u v : Vec d → Vec d} (h : u =ᵐ[volume.restrict (cubeSet Q)] v) :
    cubeBesovNegativeVectorDepthAverage Q u j =
      cubeBesovNegativeVectorDepthAverage Q v j := by
  unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [cubeAverageVec_congr_ae_cubeSet R
    (ae_restrict_mono_cubeSet (cubeSet_subset_of_mem_descendantsAtDepth hR) h)]

/-- The depth-`j` negative seminorm is an a.e. functional. -/
theorem cubeBesovNegativeVectorDepthSeminorm_congr_ae (Q : TriadicCube d) (s : ℝ) (j : ℕ)
    {u v : Vec d → Vec d} (h : u =ᵐ[volume.restrict (cubeSet Q)] v) :
    cubeBesovNegativeVectorDepthSeminorm Q s u j =
      cubeBesovNegativeVectorDepthSeminorm Q s v j := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  rw [cubeBesovNegativeVectorDepthAverage_congr_ae Q j h]

/-- **The missing a.e.-congruence.**  The finite-depth negative `q = 2` seminorm
sees the field only a.e. on the cube.  This is what transports the Poincare
bound of `DoubledCoarsePoincare.lean`, stated for the explicit solution field, to
the abstract response field that agrees with it off a null set. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_congr_ae (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) {u v : Vec d → Vec d} (h : u =ᵐ[volume.restrict (cubeSet Q)] v) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N u =
      cubeBesovNegativeVectorPartialSeminormTwo Q s N v := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun j _ => ?_)
  rw [cubeBesovNegativeVectorDepthSeminorm_congr_ae Q s j h]

/-! ## The boundedness kit -/

private theorem bddAbove_of_forall_le {f : ℕ → ℝ} {B : ℝ} (h : ∀ N, f N ≤ B) :
    BddAbove (Set.range f) := by
  refine ⟨B, ?_⟩
  rintro x ⟨N, rfl⟩
  exact h N

/-- Boundedness of the finite-depth negative seminorms of a scaled sum. -/
theorem bddAbove_partialSeminormTwo_const_smul_add (Q : TriadicCube d) (s c : ℝ)
    (hc : 0 ≤ c) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v)
    (hbu : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hbv : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => c • (u x + v x))) := by
  refine bddAbove_of_forall_le (B := c * Real.sqrt 2 *
    (cubeBesovNegativeVectorSeminormTwo Q s u +
      cubeBesovNegativeVectorSeminormTwo Q s v)) ?_
  intro N
  rw [cubeBesovNegativeVectorPartialSeminormTwo_const_smul Q s N c hc (fun y => u y + v y)]
  have hpad :=
    cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add Q s u v hu hv N
  have hu' : cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤
      cubeBesovNegativeVectorSeminormTwo Q s u := le_csSup hbu ⟨N, rfl⟩
  have hv' : cubeBesovNegativeVectorPartialSeminormTwo Q s N v ≤
      cubeBesovNegativeVectorSeminormTwo Q s v := le_csSup hbv ⟨N, rfl⟩
  have hnn2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc
    c * cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun y => u y + v y)
        ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :=
          mul_le_mul_of_nonneg_left hpad hc
    _ ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          refine mul_le_mul_of_nonneg_left ?_ hnn2
          linarith
    _ = c * Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v) := by ring

/-- Boundedness of the finite-depth negative seminorms of a scaled difference. -/
theorem bddAbove_partialSeminormTwo_const_smul_sub (Q : TriadicCube d) (s c : ℝ)
    (hc : 0 ≤ c) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v)
    (hbu : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hbv : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => c • (u x - v x))) := by
  refine bddAbove_of_forall_le (B := c * Real.sqrt 2 *
    (cubeBesovNegativeVectorSeminormTwo Q s u +
      cubeBesovNegativeVectorSeminormTwo Q s v)) ?_
  intro N
  rw [cubeBesovNegativeVectorPartialSeminormTwo_const_smul Q s N c hc (fun y => u y - v y)]
  have hpsub :=
    cubeBesovNegativeVectorPartialSeminormTwo_sub_le_sqrtTwo_mul_add Q s u v hu hv N
  have hu' : cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤
      cubeBesovNegativeVectorSeminormTwo Q s u := le_csSup hbu ⟨N, rfl⟩
  have hv' : cubeBesovNegativeVectorPartialSeminormTwo Q s N v ≤
      cubeBesovNegativeVectorSeminormTwo Q s v := le_csSup hbv ⟨N, rfl⟩
  have hnn2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc
    c * cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun y => u y - v y)
        ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :=
          mul_le_mul_of_nonneg_left hpsub hc
    _ ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          refine mul_le_mul_of_nonneg_left ?_ hnn2
          linarith
    _ = c * Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v) := by ring

/-- The first component of the flux carrier is bounded in the seminorm scale. -/
theorem bddAbove_doubledFluxField_fst [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a))
    (sig0 : ℝ) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => (doubledFluxField sig0 Q a v vStar x).1)) :=
  bddAbove_partialSeminormTwo_const_smul_add Q s _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ _ (solutionFluxField_memVectorL2 Q a v)
    (solutionFluxField_memVectorL2 Q (adjointFamily a) vStar)
    (solutionFluxField_bddAbove Q a hs v)
    (solutionFluxField_bddAbove Q (adjointFamily a) hs vStar)

/-- The second component of the flux carrier is bounded in the seminorm scale. -/
theorem bddAbove_doubledFluxField_snd [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a))
    (sig0 : ℝ) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => (doubledFluxField sig0 Q a v vStar x).2)) :=
  bddAbove_partialSeminormTwo_const_smul_sub Q s _ (Real.sqrt_nonneg _)
    _ _ (solutionGradientField_memVectorL2 Q a v)
    (solutionGradientField_memVectorL2 Q (adjointFamily a) vStar)
    (solutionGradientField_bddAbove Q a hs v)
    (solutionGradientField_bddAbove Q (adjointFamily a) hs vStar)

/-! ## The `mu`-value and the flux carrier across the null set -/

/-- The `mu`-value sees the doubled field only a.e. on the domain. -/
theorem doubledMuValue_congr_sameAE (R : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain R)) {X Y : Ch02.DoubledField d}
    (h : Ch02.DoubledField.SameAE (U := Ch02.cubeDomain R) X Y) :
    Ch02.doubledMuValue (Ch02.cubeDomain R) a X =
      Ch02.doubledMuValue (Ch02.cubeDomain R) a Y := by
  unfold Ch02.doubledMuValue Ch02.average
  refine congrArg (fun t : ℝ =>
    (volume ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))).toReal⁻¹ * t) ?_
  refine integral_congr_ae ?_
  filter_upwards [h.1, h.2] with x hx1 hx2
  have hev : X.eval x = Y.eval x := by
    unfold Ch02.DoubledField.eval
    rw [hx1, hx2]
  rw [hev]

/-- **`e.bfA.magic.swapping` across the null set.**  For a doubled field agreeing
a.e. with the field of a solution pair, the gauged `bfA`-image is a.e. the
display's own flux carrier. -/
theorem doubledFluxField_ae_eq_blockGaugeDown (sig0 : ℝ) (R : TriadicCube d)
    (a : CoeffFamily d) (v : CubeSolution R a) (vStar : CubeSolution R (adjointFamily a))
    {T : Ch02.DoubledField d}
    (hsame : Ch02.DoubledField.SameAE (U := Ch02.cubeDomain R) T
      (Ch02.doubledFieldOfSolutions (a.coeffOn R) v vStar)) :
    (fun x => blockGaugeDown sig0
        (blockMatVecMul (Ch02.blockMatrixField (a.coeffOn R) x) (T.eval x))) =ᵐ[
      volume.restrict (cubeSet R)]
      fun x => doubledFluxField sig0 R a v vStar x := by
  rw [restrict_cubeSet_eq_restrict_openCubeSet R]
  filter_upwards [hsame.1, hsame.2, (a.coeffOn R).aeElliptic] with x hx1 hx2 hell
  have heval : T.eval x = (Ch02.doubledFieldOfSolutions (a.coeffOn R) v vStar).eval x := by
    unfold Ch02.DoubledField.eval
    rw [hx1, hx2]
  rw [heval,
    doubledFluxField_apply_eq_blockGaugeDown sig0 R a v vStar
      (HCPolySupport.isUnit_det_symmPart_of_isEllipticMatrix hell)]

/-! ## The Poincare ellipticity factor, in square-root form -/

/-- The lower factor `lambda_{s,q}^{-1/2}` as a square root. -/
theorem poincareLowerEllipticityFactor_eq_sqrt (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (q : Ch02.MultiscaleExponent) (hlam : 0 ≤ Ch02.lambdaSq Q s q a) :
    poincareLowerEllipticityFactor Q a s q = Real.sqrt (Ch02.lambdaSq Q s q a)⁻¹ := by
  unfold poincareLowerEllipticityFactor
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hlam]
  norm_num

/-- The upper factor `Lambda_{s,q}^{1/2}` as a square root. -/
theorem poincareUpperEllipticityFactor_eq_sqrt (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    poincareUpperEllipticityFactor Q a s q = Real.sqrt (Ch02.LambdaSq Q s q a) := by
  unfold poincareUpperEllipticityFactor
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- **The ellipticity factor of `e.CG.Poincare.doubled.vars`** at `q = 2`, in the
gauge of `e.form.of.A.naught`. -/
def doubledPoincareEllipticityFactor (sig0 : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) : ℝ :=
  4 * poincareDiscountFactor s (.finite 2) *
    (Real.sqrt sig0 * poincareLowerEllipticityFactor Q a s (.finite 2) +
      (Real.sqrt sig0)⁻¹ * poincareUpperEllipticityFactor Q a s (.finite 2))

theorem doubledPoincareEllipticityFactor_nonneg [NeZero d] (sig0 : ℝ) (Q : TriadicCube d)
    (a : CoeffFamily d) {s : ℝ} (hs : 0 < s) :
    0 ≤ doubledPoincareEllipticityFactor sig0 Q a s := by
  have hc : 0 ≤ poincareDiscountFactor s (.finite 2) := by
    unfold poincareDiscountFactor
    refine Real.rpow_nonneg ?_ _
    have h := HCPolySupport.geometricDiscount_pos
      (mul_pos hs (by norm_num : (0 : ℝ) < 2))
    have hpos : 0 < Ch02.geometricDiscount s 2 := by
      simpa [Ch02.geometricDiscount, HCPolySupport.geometricDiscount] using h
    exact hpos.le
  have hlam : 0 ≤ poincareLowerEllipticityFactor Q a s (.finite 2) := by
    unfold poincareLowerEllipticityFactor
    exact Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a hs (by norm_num)) _
  have hLam : 0 ≤ poincareUpperEllipticityFactor Q a s (.finite 2) := by
    unfold poincareUpperEllipticityFactor
    exact Real.rpow_nonneg (Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)) _
  unfold doubledPoincareEllipticityFactor
  have h1 : 0 ≤ Real.sqrt sig0 * poincareLowerEllipticityFactor Q a s (.finite 2) :=
    mul_nonneg (Real.sqrt_nonneg _) hlam
  have h2 : 0 ≤ (Real.sqrt sig0)⁻¹ * poincareUpperEllipticityFactor Q a s (.finite 2) :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hLam
  have h3 : 0 ≤ 4 * poincareDiscountFactor s (.finite 2) := by linarith
  exact mul_nonneg h3 (by linarith)

/-- **The arithmetic link.**  The square of the display's ellipticity factor is `32
c_{s,2}^{-1}` times the gauged ellipticity sum `sigma_0^{-1} Lambda_{s,2} +
sigma_0 lambda_{s,2}^{-1}`. -/
theorem doubledPoincareEllipticityFactor_sq_le [NeZero d] {sig0 : ℝ} (Q : TriadicCube d)
    (a : CoeffFamily d) {s : ℝ} (hs : 0 < s) (hsig0 : 0 < sig0) :
    doubledPoincareEllipticityFactor sig0 Q a s *
        doubledPoincareEllipticityFactor sig0 Q a s ≤
      32 * (poincareDiscountFactor s (.finite 2) * poincareDiscountFactor s (.finite 2)) *
        (sig0⁻¹ * Ch02.LambdaSq Q s (.finite 2) a +
          sig0 * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹) := by
  have hlamInv : 0 ≤ (Ch02.lambdaSq Q s (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_nonneg Q a hs (by norm_num))
  have hLam : 0 ≤ Ch02.LambdaSq Q s (.finite 2) a :=
    Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)
  have hkey := sqrt_mul_add_inv_sqrt_mul_sq_le_two_mul hsig0 hlamInv hLam
  have hc : 0 ≤ poincareDiscountFactor s (.finite 2) := by
    unfold poincareDiscountFactor
    refine Real.rpow_nonneg ?_ _
    have h := HCPolySupport.geometricDiscount_pos
      (mul_pos hs (by norm_num : (0 : ℝ) < 2))
    have hpos : 0 < Ch02.geometricDiscount s 2 := by
      simpa [Ch02.geometricDiscount, HCPolySupport.geometricDiscount] using h
    exact hpos.le
  set c : ℝ := poincareDiscountFactor s (.finite 2) with hcdef
  set A : ℝ := Real.sqrt sig0 * Real.sqrt (Ch02.lambdaSq Q s (.finite 2) a)⁻¹ +
    (Real.sqrt sig0)⁻¹ * Real.sqrt (Ch02.LambdaSq Q s (.finite 2) a) with hAdef
  have hfac : doubledPoincareEllipticityFactor sig0 Q a s = 4 * c * A := by
    unfold doubledPoincareEllipticityFactor
    rw [hAdef, hcdef,
      poincareLowerEllipticityFactor_eq_sqrt Q a s (.finite 2)
        (Ch02.lambdaSq_finite_nonneg Q a hs (by norm_num)),
      poincareUpperEllipticityFactor_eq_sqrt]
  rw [hfac]
  have hcc : 0 ≤ c * c := mul_nonneg hc hc
  have hstep : (4 * c * A) * (4 * c * A) = 16 * (c * c) * (A * A) := by ring
  rw [hstep]
  have hmul : 16 * (c * c) * (A * A) ≤
      16 * (c * c) * (2 * (sig0⁻¹ * Ch02.LambdaSq Q s (.finite 2) a +
        sig0 * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹)) := by
    refine mul_le_mul_of_nonneg_left hkey ?_
    linarith
  calc 16 * (c * c) * (A * A)
      ≤ 16 * (c * c) * (2 * (sig0⁻¹ * Ch02.LambdaSq Q s (.finite 2) a +
          sig0 * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹)) := hmul
    _ = 32 * (c * c) * (sig0⁻¹ * Ch02.LambdaSq Q s (.finite 2) a +
          sig0 * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹) := by ring

/-! ## The Poincare leg at a doubled response field -/

/-- **`e.CG.Poincare.doubled.vars` at an abstract doubled response field.**

For `T` a doubled response field of `a` on the cube `R`, every finite-depth
negative `q = 2` seminorm of either component of `bfAhom^{-1/2} bfA T` is at most
the display's ellipticity factor times `|| bfA^{1/2} T ||_{L^2(R)}`, and the
`mu`-value of `T` is nonnegative.

This is the `hpoin`/`hsq` pair of
`Variational.PerCubeFluctuationArithmetic.perCube_fluct_le`, with
`blockE = sqrt (2 mu)`.

on the exponent window, the gauge positivity and `[NeZero d]` only; see the
module docstring's binder census. -/
theorem partialSeminormTwo_blockGaugeDown_le_of_isDoubledResponseField [NeZero d]
    (R : TriadicCube d) (a : CoeffFamily d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {sig0 : ℝ} (hsig0 : 0 < sig0) {T : Ch02.DoubledField d}
    (hT : Ch02.IsDoubledResponseField (Ch02.cubeDomain R) (a.coeffOn R) T) :
    0 ≤ Ch02.doubledMuValue (Ch02.cubeDomain R) (a.coeffOn R) T ∧
      (∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo R s N
          (fun x => (blockGaugeDown sig0
            (blockMatVecMul (Ch02.blockMatrixField (a.coeffOn R) x) (T.eval x))).1) ≤
        doubledPoincareEllipticityFactor sig0 R a s *
          Real.sqrt (2 * Ch02.doubledMuValue (Ch02.cubeDomain R) (a.coeffOn R) T)) ∧
        ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => (blockGaugeDown sig0
              (blockMatVecMul (Ch02.blockMatrixField (a.coeffOn R) x) (T.eval x))).2) ≤
          doubledPoincareEllipticityFactor sig0 R a s *
            Real.sqrt (2 * Ch02.doubledMuValue (Ch02.cubeDomain R) (a.coeffOn R) T) := by
  obtain ⟨v, vStar, hsame⟩ :=
    ((Ch02.doubledResponseTheory (Ch02.cubeDomain R)
      (a.coeffOn R)).response_space_by_solutions T).mp hT
  -- the `mu`-value is that of the solution field, hence nonnegative
  have hmuT : Ch02.doubledMuValue (Ch02.cubeDomain R) (a.coeffOn R) T =
      Ch02.doubledMuValue (Ch02.cubeDomain R) (a.coeffOn R)
        (Ch02.doubledFieldOfSolutions (a.coeffOn R) v vStar) :=
    doubledMuValue_congr_sameAE R (a.coeffOn R) hsame
  have hmu0 : 0 ≤ Ch02.doubledMuValue (Ch02.cubeDomain R) (a.coeffOn R) T := by
    rw [hmuT, doubledMuValue_doubledFieldOfSolutions]
    exact add_nonneg (variationEnergyValue_nonneg _ _ _) (variationEnergyValue_nonneg _ _ _)
  -- the two carriers agree a.e.
  have hae := doubledFluxField_ae_eq_blockGaugeDown sig0 R a v vStar hsame
  have hae1 : (fun x => (blockGaugeDown sig0
        (blockMatVecMul (Ch02.blockMatrixField (a.coeffOn R) x) (T.eval x))).1) =ᵐ[
      volume.restrict (cubeSet R)]
      fun x => (doubledFluxField sig0 R a v vStar x).1 := by
    filter_upwards [hae] with x hx
    rw [hx]
  have hae2 : (fun x => (blockGaugeDown sig0
        (blockMatVecMul (Ch02.blockMatrixField (a.coeffOn R) x) (T.eval x))).2) =ᵐ[
      volume.restrict (cubeSet R)]
      fun x => (doubledFluxField sig0 R a v vStar x).2 := by
    filter_upwards [hae] with x hx
    rw [hx]
  -- the Poincare display, at the solution pair
  have hpoin := doubledCoarsePoincare_le_doubledEnergy R a hs hs1 v vStar hsig0
  have hstate0 : 0 ≤ blockNegativeBesovTwo R s (doubledStateField sig0 R a v vStar) :=
    blockNegativeBesovTwo_nonneg R s _
  have hflux : blockNegativeBesovTwo R s (doubledFluxField sig0 R a v vStar) ≤
      doubledPoincareEllipticityFactor sig0 R a s *
        Real.sqrt (2 * Ch02.doubledMuValue (Ch02.cubeDomain R) (a.coeffOn R)
          (Ch02.doubledFieldOfSolutions (a.coeffOn R) v vStar)) := by
    unfold doubledPoincareEllipticityFactor
    linarith [hpoin, hstate0]
  rw [← hmuT] at hflux
  refine ⟨hmu0, ?_, ?_⟩
  · intro N
    rw [cubeBesovNegativeVectorPartialSeminormTwo_congr_ae R s N hae1]
    exact le_trans
      (cubeBesovNegativeVectorPartialSeminormTwo_fst_le_blockNegativeBesovTwo R s _
        (bddAbove_doubledFluxField_fst R a hs v vStar sig0) N) hflux
  · intro N
    rw [cubeBesovNegativeVectorPartialSeminormTwo_congr_ae R s N hae2]
    exact le_trans
      (cubeBesovNegativeVectorPartialSeminormTwo_snd_le_blockNegativeBesovTwo R s _
        (bddAbove_doubledFluxField_snd R a hs v vStar sig0) N) hflux

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
