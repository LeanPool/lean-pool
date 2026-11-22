/-
Copyright (c) 2026 Dawid Trela and OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela, OpenAI
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005

/-!
# Faster exact arithmetic for the Gerver cell certificates

Use endpoint signs to select the extrema of an interval product, and reuse
the checked degree-ten Taylor coefficients across all rejection certificates.
The equivalence lemmas transport those computations back to the original checker.
-/

@[expose] public section

open GerverSofa.PartALeanCert LeanCert.Core

namespace GerverSofa.PartE.FastIntervals

private theorem interval_eq {I J : IntervalRat} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) :
    I = J := by
  cases I
  cases J
  cases hlo
  cases hhi
  rfl

private theorem endpoints_mul_of_nonneg_right (I J : IntervalRat) (h : 0 ≤ J.lo) :
    (I.mul J).lo = min (I.lo * J.lo) (I.lo * J.hi) ∧
    (I.mul J).hi = max (I.hi * J.lo) (I.hi * J.hi) := by
  have h' := h.trans J.le
  exact ⟨min_eq_left (min_le_min (mul_le_mul_of_nonneg_right I.le h)
    (mul_le_mul_of_nonneg_right I.le h')), max_eq_right
    (max_le_max (mul_le_mul_of_nonneg_right I.le h) (mul_le_mul_of_nonneg_right I.le h'))⟩

open IntervalRat

/-- In a nonnegative interval, choose the factor for a lower endpoint by its sign. -/
def lowerProduct (value : ℚ) (interval : IntervalRat) : ℚ :=
  value * if 0 ≤ value then interval.lo else interval.hi

/-- In a nonnegative interval, choose the factor for an upper endpoint by its sign. -/
def upperProduct (value : ℚ) (interval : IntervalRat) : ℚ :=
  value * if 0 ≤ value then interval.hi else interval.lo

private theorem lowerProduct_eq (value : ℚ) (interval : IntervalRat) :
    lowerProduct value interval = min (value * interval.lo) (value * interval.hi) := by
  unfold lowerProduct
  split_ifs with nonnegative
  · exact (min_eq_left (mul_le_mul_of_nonneg_left interval.le nonnegative)).symm
  · exact (min_eq_right
      (mul_le_mul_of_nonpos_left interval.le (le_of_not_ge nonnegative))).symm

private theorem upperProduct_eq (value : ℚ) (interval : IntervalRat) :
    upperProduct value interval = max (value * interval.lo) (value * interval.hi) := by
  unfold upperProduct
  split_ifs with nonnegative
  · exact (max_eq_right (mul_le_mul_of_nonneg_left interval.le nonnegative)).symm
  · exact (max_eq_left
      (mul_le_mul_of_nonpos_left interval.le (le_of_not_ge nonnegative))).symm

/-- Keep the endpoint computations independent when the fixed Horner factor is nonnegative. -/
def multiplyForTaylor (partialSum interval : IntervalRat) : IntervalRat :=
  if nonnegative : 0 ≤ interval.lo then
    ⟨lowerProduct partialSum.lo interval, upperProduct partialSum.hi interval, by
      rw [lowerProduct_eq, upperProduct_eq,
        ← (endpoints_mul_of_nonneg_right partialSum interval nonnegative).1,
        ← (endpoints_mul_of_nonneg_right partialSum interval nonnegative).2]
      exact (partialSum.mul interval).le⟩
  else
    partialSum.mulFast interval

private theorem multiplyForTaylor_eq (partialSum interval : IntervalRat) :
    multiplyForTaylor partialSum interval = partialSum.mul interval := by
  unfold multiplyForTaylor
  split_ifs with nonnegative
  · apply interval_eq
    · exact (lowerProduct_eq _ _).trans
        (endpoints_mul_of_nonneg_right partialSum interval nonnegative).1.symm
    · exact (upperProduct_eq _ _).trans
        (endpoints_mul_of_nonneg_right partialSum interval nonnegative).2.symm
  · exact mulFast_eq_mul partialSum interval

/-- Evaluate a Taylor polynomial by Horner iteration with sign-based multiplication. -/
def evalTaylor (coefficients : List ℚ) (interval : IntervalRat) : IntervalRat :=
  coefficients.foldr (fun coefficient partialSum =>
    (singleton coefficient).add (multiplyForTaylor partialSum interval)) (singleton 0)

private theorem evalTaylor_eq (coefficients : List ℚ) (interval : IntervalRat) :
    evalTaylor coefficients interval = evalTaylorSeries coefficients interval := by
  unfold evalTaylor evalTaylorSeries
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients _ =>
    simp only [List.foldr_cons, multiplyForTaylor_eq]

/-- Depth-ten sine coefficients, checked against the generated list. -/
def sineCoefficients : List ℚ :=
  [0, 1, 0, -1 / 6, 0, 1 / 120, 0, -1 / 5040, 0, 1 / 362880, 0]

/-- Depth-ten cosine coefficients, checked against the generated list. -/
def cosineCoefficients : List ℚ :=
  [1, 0, -1 / 2, 0, 1 / 24, 0, -1 / 720, 0, 1 / 40320, 0, -1 / 3628800]

private theorem sineCoefficients_eq : sineCoefficients = sinTaylorCoeffs 10 := by decide +kernel
private theorem cosineCoefficients_eq : cosineCoefficients = cosTaylorCoeffs 10 := by decide +kernel

/-- Intersect a trigonometric enclosure with the global range when the intersection exists. -/
def clip (interval : IntervalRat) : IntervalRat :=
  match interval.intersect ⟨-1, 1, by norm_num⟩ with
  | some refined => refined
  | none => interval

/-- Compute the depth-ten sine enclosure using sign-based multiplication. -/
def sine (interval : IntervalRat) : IntervalRat :=
  clip ((evalTaylor sineCoefficients interval).add (sinRemainderBoundComputable interval 10))

/-- Compute the depth-ten cosine enclosure using sign-based multiplication. -/
def cosine (interval : IntervalRat) : IntervalRat :=
  clip ((evalTaylor cosineCoefficients interval).add (cosRemainderBoundComputable interval 10))

private theorem sine_eq (interval : IntervalRat) : sine interval = sinComputable interval 10 := by
  simp only [sine, evalTaylor_eq, sineCoefficients_eq]
  rfl

private theorem cosine_eq (interval : IntervalRat) :
    cosine interval = cosComputable interval 10 := by
  simp only [cosine, evalTaylor_eq, cosineCoefficients_eq]
  rfl

/-- Compute the two scaled residuals using pre-evaluated trigonometric bounds. -/
def residualIntervals (multiply : IntervalRat → IntervalRat → IntervalRat)
    (phi theta cosinePhi sinePhi cosineTheta sineTheta : IntervalRat) : IntervalRat × IntervalRat :=
  let subtract := fun a b => IntervalRat.add a (IntervalRat.neg b)
  let scale := fun q a => multiply (IntervalRat.singleton q) a
  let one := IntervalRat.singleton 1
  let half := IntervalRat.singleton (1 / 2)
  let delta := subtract theta phi
  let base := IntervalRat.add
    (IntervalRat.add (subtract (subtract (scale (1 / 2) kernelPiInterval) phi) theta)
      (scale (1 / 2) delta)) (scale (1 / 4) (multiply delta delta))
  let denominator := subtract cosinePhi
    (multiply (IntervalRat.add one (scale (1 / 2) delta)) sinePhi)
  let numerator := IntervalRat.add
    (IntervalRat.add (IntervalRat.add sinePhi half) (IntervalRat.neg (scale (1 / 2) cosinePhi)))
    (multiply base sinePhi)
  let numeratorB := IntervalRat.add
    (multiply numerator (IntervalRat.add one (scale (1 / 2) delta)))
    (multiply base denominator)
  let first := IntervalRat.add
    (IntervalRat.add (IntervalRat.add (IntervalRat.add
      (subtract (multiply numerator (subtract cosineTheta cosinePhi))
        (multiply (scale 2 numeratorB) sinePhi))
      (multiply (multiply (subtract delta one) cosineTheta) denominator))
      (IntervalRat.neg (multiply sineTheta denominator)))
      (multiply cosinePhi denominator)) (multiply sinePhi denominator)
  let second := IntervalRat.add
    (IntervalRat.add (IntervalRat.add (IntervalRat.add
      (subtract (multiply numerator (IntervalRat.add (scale 3 sineTheta) sinePhi))
        (multiply (scale 2 numeratorB) cosinePhi))
      (multiply (multiply (scale 3 (subtract delta one)) sineTheta) denominator))
      (multiply (scale 3 cosineTheta) denominator))
      (IntervalRat.neg (multiply sinePhi denominator)))
    (multiply cosinePhi denominator)
  (first, second)

/-- Evaluate the rejection test with supplied interval operations and trigonometric bounds. -/
def rejectWith (multiply : IntervalRat → IntervalRat → IntervalRat)
    (cell : AngleCell) (cosinePhi sinePhi cosineTheta sineTheta : IntervalRat) : Bool :=
  let residuals :=
    residualIntervals multiply cell.phiI cell.thetaI cosinePhi sinePhi cosineTheta sineTheta
  intervalExcludesZero residuals.1 || intervalExcludesZero residuals.2

/-- Check rejection with sign-based interval multiplication and fixed Taylor coefficients. -/
def rejected (cell : AngleCell) : Bool :=
  rejectWith mulFast cell (cosine cell.phiI) (sine cell.phiI)
    (cosine cell.thetaI) (sine cell.thetaI)

private theorem rejectWith_eq (cell : AngleCell) :
    rejectWith mul cell (cosComputable cell.phiI 10) (sinComputable cell.phiI 10)
      (cosComputable cell.thetaI 10) (sinComputable cell.thetaI 10) = cell.rejected :=
  rfl

private theorem rejected_eq (cell : AngleCell) : rejected cell = cell.rejected := by
  have multiplication : mulFast = mul :=
    funext fun left => funext fun right => mulFast_eq_mul left right
  simp only [rejected, cosine_eq, sine_eq, multiplication, rejectWith_eq]

/-- Decide a rejection certificate through the faster exact evaluator. -/
@[instance_reducible] def decidableRejected (cell : AngleCell) : Decidable (cell.rejected = true) :=
  decidable_of_iff (rejected cell = true) (by rw [rejected_eq])

private theorem lo_multiplyForTaylor (left right : IntervalRat) (positive : 0 ≤ right.lo) :
    (multiplyForTaylor left right).lo = lowerProduct left.lo right := by
  simp only [multiplyForTaylor, dite_eq_left positive]

private theorem hi_multiplyForTaylor (left right : IntervalRat) (positive : 0 ≤ right.lo) :
    (multiplyForTaylor left right).hi = upperProduct left.hi right := by
  simp only [multiplyForTaylor, dite_eq_left positive]

private theorem square_lo (interval : IntervalRat) (positive : 0 ≤ interval.lo) :
    (multiplyForTaylor interval interval).lo = interval.lo * interval.lo := by
  rw [lo_multiplyForTaylor _ _ positive]
  simp only [lowerProduct, ite_eq_left positive]

private theorem square_hi (interval : IntervalRat) (positive : 0 ≤ interval.lo) :
    (multiplyForTaylor interval interval).hi = interval.hi * interval.hi := by
  rw [hi_multiplyForTaylor _ _ positive]
  simp only [upperProduct, ite_eq_left (positive.trans interval.le)]

private theorem lowerProduct_twice (value : ℚ) (interval : IntervalRat)
    (positive : 0 < interval.lo) :
    lowerProduct (lowerProduct value interval) interval =
      lowerProduct value (multiplyForTaylor interval interval) := by
  by_cases sign : 0 ≤ value
  · simp only [lowerProduct, ite_eq_left sign, ite_eq_left (mul_nonneg sign positive.le),
      square_lo _ positive.le, mul_assoc]
  · have negative : value < 0 := lt_of_not_ge sign
    simp only [lowerProduct, ite_eq_right sign, ite_eq_right (not_le.mpr
      (mul_neg_of_neg_of_pos negative (positive.trans_le interval.le))),
      square_hi _ positive.le, mul_assoc]

private theorem upperProduct_twice (value : ℚ) (interval : IntervalRat)
    (positive : 0 < interval.lo) :
    upperProduct (upperProduct value interval) interval =
      upperProduct value (multiplyForTaylor interval interval) := by
  by_cases sign : 0 ≤ value
  · simp only [upperProduct, ite_eq_left sign,
      ite_eq_left (mul_nonneg sign (positive.le.trans interval.le)),
      square_hi _ positive.le, mul_assoc]
  · have negative : value < 0 := lt_of_not_ge sign
    simp only [upperProduct, ite_eq_right sign,
      ite_eq_right (not_le.mpr (mul_neg_of_neg_of_pos negative positive)),
      square_lo _ positive.le, mul_assoc]

private theorem multiplyForTaylor_twice (accumulator interval : IntervalRat)
    (positive : 0 < interval.lo) :
    multiplyForTaylor (multiplyForTaylor accumulator interval) interval =
      multiplyForTaylor accumulator (multiplyForTaylor interval interval) := by
  have squareNonnegative : 0 ≤ (multiplyForTaylor interval interval).lo := by
    rw [square_lo _ positive.le]
    exact mul_nonneg positive.le positive.le
  apply interval_eq
  · rw [lo_multiplyForTaylor _ _ positive.le, lo_multiplyForTaylor _ _ positive.le,
      lo_multiplyForTaylor _ _ squareNonnegative, lowerProduct_twice _ _ positive]
  · rw [hi_multiplyForTaylor _ _ positive.le, hi_multiplyForTaylor _ _ positive.le,
      hi_multiplyForTaylor _ _ squareNonnegative, upperProduct_twice _ _ positive]

private theorem add_zero_coefficient (interval : IntervalRat) :
    (singleton 0).add interval = interval := by
  apply interval_eq <;> simp only [IntervalRat.add, IntervalRat.singleton, zero_add]

private theorem zero_multiplyForTaylor (interval : IntervalRat) :
    multiplyForTaylor (singleton 0) interval = singleton 0 := by
  rw [multiplyForTaylor_eq]
  apply interval_eq <;>
    simp only [IntervalRat.mul, min4, max4, IntervalRat.singleton, zero_mul, min_self, max_self]

private theorem evalTaylor_trailing_zero (coefficients : List ℚ) (interval : IntervalRat) :
    evalTaylor (coefficients ++ [0]) interval = evalTaylor coefficients interval := by
  induction coefficients with
  | nil =>
    simp only [List.nil_append, evalTaylor, List.foldr_cons, List.foldr_nil,
      zero_multiplyForTaylor, add_zero_coefficient]
  | cons coefficient coefficients ih =>
    simp only [List.cons_append, evalTaylor, List.foldr_cons] at ih ⊢
    rw [ih]

private def insertZeros : List ℚ → List ℚ
  | [] => []
  | coefficient :: coefficients => coefficient :: 0 :: insertZeros coefficients

private theorem evalTaylor_insertZeros (coefficients : List ℚ) (interval : IntervalRat)
    (positive : 0 < interval.lo) :
    evalTaylor (insertZeros coefficients) interval =
      evalTaylor coefficients (multiplyForTaylor interval interval) := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients ih =>
    change (singleton coefficient).add
      (multiplyForTaylor ((singleton 0).add
        (multiplyForTaylor (evalTaylor (insertZeros coefficients) interval) interval)) interval) =
      (singleton coefficient).add
        (multiplyForTaylor (evalTaylor coefficients (multiplyForTaylor interval interval))
          (multiplyForTaylor interval interval))
    rw [add_zero_coefficient, multiplyForTaylor_twice _ _ positive, ih]

/-- The even-degree coefficients of the depth-ten cosine polynomial, in ascending degree. -/
def cosineEvenCoefficients : List ℚ :=
  [1, -1 / 2, 1 / 24, -1 / 720, 1 / 40320, -1 / 3628800]

/-- The odd-degree coefficients of the depth-ten sine polynomial, in ascending degree. -/
def sineEvenCoefficients : List ℚ := [1, -1 / 6, 1 / 120, -1 / 5040, 1 / 362880]

private theorem cosineEven_expanded :
    insertZeros cosineEvenCoefficients = cosineCoefficients ++ [0] :=
  rfl

private theorem sineEven_expanded : 0 :: insertZeros sineEvenCoefficients = sineCoefficients := rfl

/-- Sine enclosure with two Horner steps combined for positive inputs. -/
def sineSparse (interval : IntervalRat) : IntervalRat :=
  if 0 < interval.lo then
    let square := multiplyForTaylor interval interval
    clip ((multiplyForTaylor (evalTaylor sineEvenCoefficients square) interval).add
      (sinRemainderBoundComputable interval 10))
  else
    sine interval

/-- Cosine enclosure with two Horner steps combined for positive inputs. -/
def cosineSparse (interval : IntervalRat) : IntervalRat :=
  if 0 < interval.lo then
    let square := multiplyForTaylor interval interval
    clip ((evalTaylor cosineEvenCoefficients square).add (cosRemainderBoundComputable interval 10))
  else
    cosine interval

theorem sineSparse_eq (interval : IntervalRat) :
    sineSparse interval = sinComputable interval 10 := by
  rw [← sine_eq]
  unfold sineSparse
  split_ifs with positive
  · unfold sine
    rw [← sineEven_expanded]
    change _ = clip (((singleton 0).add
      (multiplyForTaylor (evalTaylor (insertZeros sineEvenCoefficients) interval) interval)).add _)
    rw [add_zero_coefficient, evalTaylor_insertZeros _ _ positive]
  · rfl

theorem cosineSparse_eq (interval : IntervalRat) :
    cosineSparse interval = cosComputable interval 10 := by
  rw [← cosine_eq]
  unfold cosineSparse
  split_ifs with positive
  · unfold cosine
    rw [← evalTaylor_trailing_zero cosineCoefficients interval, ← cosineEven_expanded,
      evalTaylor_insertZeros _ _ positive]
  · rfl

/-- Decide the original rejection proposition using the sparse Taylor evaluator. -/
@[instance_reducible] def decidableRejectedSparse (cell : AngleCell) :
    Decidable (cell.rejected = true) :=
  decidable_of_iff (rejectWith mulFast cell (cosineSparse cell.phiI) (sineSparse cell.phiI)
    (cosineSparse cell.thetaI) (sineSparse cell.thetaI) = true) (by
      have multiplication : mulFast = mul :=
        funext fun left => funext fun right => mulFast_eq_mul left right
      simp only [cosineSparse_eq, sineSparse_eq, multiplication, rejectWith_eq])

end GerverSofa.PartE.FastIntervals
