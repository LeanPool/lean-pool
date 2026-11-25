/-
Copyright (c) 2026 Dawid Trela and OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela, OpenAI
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.AreaCertificateInputs
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.FastIntervals

/-!
# Fixed-point arithmetic for Gerver cell rejection

Use the existing scaled integer intervals to evaluate the degree-ten
trigonometric bounds and the two residual formulas. Every rounded product
is enclosed at the same grid scale. A strict sign for one of these wider
residuals certifies the original rational test. An inconclusive sign is
checked with the sparse exact evaluator.
-/

@[expose] public section

namespace GerverSofa.PartE.FixedPointResiduals

open LeanCert.Core IntervalRat GerverSofa.PartALeanCert MovingSofa.GerverAreaCert

private structure Covers (outer inner : IntervalRat) : Prop where
  lower : outer.lo ≤ inner.lo
  upper : inner.hi ≤ outer.hi

private theorem Covers.refl (interval : IntervalRat) : Covers interval interval :=
  ⟨le_rfl, le_rfl⟩

private theorem Covers.endpoints {outer inner : IntervalRat} (covered : Covers outer inner) :
    (inner.lo : ℝ) ∈ outer ∧ (inner.hi : ℝ) ∈ outer := by
  rw [IntervalRat.mem_def, IntervalRat.mem_def]
  exact ⟨⟨by exact_mod_cast covered.lower, by exact_mod_cast inner.le.trans covered.upper⟩,
    ⟨by exact_mod_cast covered.lower.trans inner.le, by exact_mod_cast covered.upper⟩⟩

private theorem Covers.mul {outerLeft outerRight innerLeft innerRight : IntervalRat}
    (left : Covers outerLeft innerLeft) (right : Covers outerRight innerRight) :
    Covers (outerLeft.mul outerRight) (innerLeft.mul innerRight) := by
  have ⟨leftLo, leftHi⟩ := left.endpoints
  have ⟨rightLo, rightHi⟩ := right.endpoints
  have ll := IntervalRat.mem_mul leftLo rightLo
  have lh := IntervalRat.mem_mul leftLo rightHi
  have hl := IntervalRat.mem_mul leftHi rightLo
  have hh := IntervalRat.mem_mul leftHi rightHi
  simp only [IntervalRat.mem_def, ← Rat.cast_mul] at ll lh hl hh
  constructor
  · simp only [IntervalRat.mul, IntervalRat.min4, le_min_iff]
    exact ⟨⟨by exact_mod_cast ll.1, by exact_mod_cast lh.1⟩,
      ⟨by exact_mod_cast hl.1, by exact_mod_cast hh.1⟩⟩
  · simp only [IntervalRat.mul, IntervalRat.max4, max_le_iff]
    exact ⟨⟨by exact_mod_cast ll.2, by exact_mod_cast lh.2⟩,
      ⟨by exact_mod_cast hl.2, by exact_mod_cast hh.2⟩⟩

private theorem scale_pos : (0 : ℚ) < (M : ℚ) := by norm_num [M]

/-- Round a rational down in grid units by dividing its scaled numerator. -/
def gridFloor (value : ℚ) : ℤ := (M * value.num) / (value.den : ℤ)

private theorem gridFloor_eq (value : ℚ) : gridFloor value = ⌊(M : ℚ) * value⌋ := by
  have fraction : (value.num : ℚ) / (value.den : ℚ) = value := by
    rw [← Int.cast_natCast, Rat.intCast_div_eq_divInt, Rat.num_divInt_den]
  unfold gridFloor
  rw [← Rat.floor_intCast_div_natCast, Int.cast_mul, mul_div_assoc, fraction]

/-- Convert to the grid with outward rounding. -/
def fromRat (interval : IntervalRat) : SI :=
  ⟨gridFloor interval.lo, gridFloor interval.hi + 1⟩

private structure Encloses (outer : SI) (inner : IntervalRat) : Prop where
  lower : (outer.lo : ℚ) / (M : ℚ) ≤ inner.lo
  upper : inner.hi ≤ (outer.hi : ℚ) / (M : ℚ)

private theorem fromRat_encloses (interval : IntervalRat) :
    Encloses (fromRat interval) interval := by
  constructor
  · change (gridFloor interval.lo : ℚ) / (M : ℚ) ≤ interval.lo
    rw [gridFloor_eq]
    exact (div_le_iff₀' scale_pos).2 (Int.floor_le _)
  · change interval.hi ≤ ((gridFloor interval.hi + 1 : ℤ) : ℚ) / (M : ℚ)
    apply (le_div_iff₀' scale_pos).2
    rw [gridFloor_eq]
    push_cast
    exact (Int.lt_floor_add_one _).le

private theorem Encloses.add {outerLeft outerRight : SI} {innerLeft innerRight : IntervalRat}
    (left : Encloses outerLeft innerLeft) (right : Encloses outerRight innerRight) :
    Encloses (SI.add outerLeft outerRight) (innerLeft.add innerRight) := by
  constructor
  · simpa only [SI.add, Int.cast_add, add_div, IntervalRat.add]
      using add_le_add left.lower right.lower
  · simpa only [SI.add, Int.cast_add, add_div, IntervalRat.add]
      using add_le_add left.upper right.upper

private theorem Encloses.neg {outer : SI} {inner : IntervalRat} (covered : Encloses outer inner) :
    Encloses (SI.neg outer) inner.neg := by
  constructor
  · simpa only [SI.neg, Int.cast_neg, neg_div, IntervalRat.neg] using neg_le_neg covered.upper
  · simpa only [SI.neg, Int.cast_neg, neg_div, IntervalRat.neg] using neg_le_neg covered.lower

private theorem floor_grid_le (scaled : ℤ) :
    ((scaled / M : ℤ) : ℚ) / (M : ℚ) ≤ (scaled : ℚ) / (M : ℚ) ^ 2 := by
  rw [pow_two, ← div_div]
  apply div_le_div_of_nonneg_right _ scale_pos.le
  apply (le_div_iff₀ scale_pos).2
  exact_mod_cast Int.ediv_mul_le scaled (by norm_num [M])

private theorem le_ceil_grid (scaled : ℤ) :
    (scaled : ℚ) / (M : ℚ) ^ 2 ≤ ((-((-scaled) / M) : ℤ) : ℚ) / (M : ℚ) := by
  rw [Int.cast_neg, neg_div, ← neg_le_neg_iff]
  simp only [neg_neg, ← neg_div, ← Int.cast_neg]
  exact floor_grid_le (-scaled)

private theorem imin_eq_min (a b : ℤ) : SI.imin a b = min a b := by
  unfold SI.imin
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

private theorem imax_eq_max (a b : ℤ) : SI.imax a b = max a b := by
  unfold SI.imax
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

private def toInterval (outer : SI) (ordered : (outer.lo : ℚ) / M ≤ (outer.hi : ℚ) / M) :
    IntervalRat :=
  ⟨(outer.lo : ℚ) / M, (outer.hi : ℚ) / M, ordered⟩

private theorem Encloses.ordered {outer : SI} {inner : IntervalRat}
    (enclosed : Encloses outer inner) : (outer.lo : ℚ) / M ≤ (outer.hi : ℚ) / M :=
  enclosed.lower.trans (inner.le.trans enclosed.upper)

private theorem Encloses.mul {outerLeft outerRight : SI} {innerLeft innerRight : IntervalRat}
    (left : Encloses outerLeft innerLeft) (right : Encloses outerRight innerRight) :
    Encloses (SI.mul outerLeft outerRight) (innerLeft.mul innerRight) := by
  let leftInterval := toInterval outerLeft left.ordered
  let rightInterval := toInterval outerRight right.ordered
  have leftCovered : Covers leftInterval innerLeft := ⟨left.lower, left.upper⟩
  have rightCovered : Covers rightInterval innerRight := ⟨right.lower, right.upper⟩
  have multiplied := leftCovered.mul rightCovered
  constructor
  · apply le_trans _ multiplied.lower
    simp only [SI.mul, imin_eq_min, leftInterval, rightInterval, IntervalRat.mul, toInterval,
      IntervalRat.min4, div_mul_div_comm, ← pow_two, ← Int.cast_mul, min_div_div_right
      (sq_nonneg (M : ℚ)), ← Int.cast_min]
    exact floor_grid_le _
  · apply le_trans multiplied.upper
    simp only [SI.mul, imax_eq_max, leftInterval, rightInterval, IntervalRat.mul, toInterval,
      IntervalRat.max4, div_mul_div_comm, ← pow_two, ← Int.cast_mul, max_div_div_right
      (sq_nonneg (M : ℚ)), ← Int.cast_max]
    exact le_ceil_grid _

/-- Test whether the grid interval has strictly positive or strictly negative sign. -/
def excludesZero (interval : SI) : Bool := decide (interval.hi < 0 ∨ 0 < interval.lo)

private theorem Encloses.excludesZero {outer : SI} {inner : IntervalRat}
    (enclosed : Encloses outer inner) (excluded : excludesZero outer = true) :
    intervalExcludesZero inner = true := by
  simp only [FixedPointResiduals.excludesZero, intervalExcludesZero,
    decide_eq_true_eq] at excluded ⊢
  rcases excluded with negative | positive
  · exact Or.inl (enclosed.upper.trans_lt (div_neg_of_neg_of_pos (by exact_mod_cast negative)
      scale_pos))
  · exact Or.inr ((div_pos (by exact_mod_cast positive) scale_pos).trans_le enclosed.lower)

private theorem Encloses.trans {outer : SI} {middle inner : IntervalRat}
    (first : Encloses outer middle) (second : Covers middle inner) :
    Encloses outer inner :=
  ⟨first.lower.trans second.lower, second.upper.trans first.upper⟩

private theorem covers_clip (interval : IntervalRat) :
    Covers interval (FastIntervals.clip interval) := by
  unfold FastIntervals.clip
  split
  · rename_i result equation
    exact ⟨(intersect_subset_left equation).1, (intersect_subset_left equation).2⟩
  · exact Covers.refl interval

/-- Evaluate a Taylor polynomial by Horner iteration on the grid. -/
def horner (coefficients : List ℚ) (interval : SI) : SI :=
  coefficients.foldr (fun coefficient value =>
    SI.add (fromRat (singleton coefficient)) (SI.mul value interval))
    (fromRat (singleton 0))

private theorem horner_encloses (coefficients : List ℚ) {outer : SI}
    {inner : IntervalRat} (covered : Encloses outer inner) :
    Encloses (horner coefficients outer) (evalTaylorSeries coefficients inner) := by
  induction coefficients with
  | nil => exact fromRat_encloses _
  | cons coefficient rest ih =>
    exact (fromRat_encloses (singleton coefficient)).add (ih.mul covered)

/-- Outward enclosure of the degree-ten sine approximation and its remainder. -/
def sine (interval : IntervalRat) : SI :=
  let input := fromRat interval
  let remainder := fromRat (sinRemainderBoundComputable interval 10)
  if 0 < interval.lo then
    SI.add (SI.mul (horner FastIntervals.sineEvenCoefficients (SI.mul input input)) input)
      remainder
  else
    SI.add (horner FastIntervals.sineCoefficients input) remainder

/-- Outward enclosure of the degree-ten cosine approximation and its remainder. -/
def cosine (interval : IntervalRat) : SI :=
  let input := fromRat interval
  let remainder := fromRat (cosRemainderBoundComputable interval 10)
  if 0 < interval.lo then
    SI.add (horner FastIntervals.cosineEvenCoefficients (SI.mul input input)) remainder
  else
    SI.add (horner FastIntervals.cosineCoefficients input) remainder

private theorem sine_encloses (interval : IntervalRat) :
    Encloses (sine interval) (sinComputable interval 10) := by
  rw [← FastIntervals.sineSparse_eq]
  simp only [sine, FastIntervals.sineSparse]
  have input := fromRat_encloses interval
  have remainder := fromRat_encloses (sinRemainderBoundComputable interval 10)
  split_ifs with positive
  · simp only [FastIntervals.multiplyForTaylor_eq_mul,
      FastIntervals.evalTaylor_eq_evalTaylorSeries]
    exact (((horner_encloses _ (input.mul input)).mul input).add remainder).trans
      (covers_clip _)
  · simp only [FastIntervals.sine, FastIntervals.evalTaylor_eq_evalTaylorSeries]
    exact ((horner_encloses _ input).add remainder).trans (covers_clip _)

private theorem cosine_encloses (interval : IntervalRat) :
    Encloses (cosine interval) (cosComputable interval 10) := by
  rw [← FastIntervals.cosineSparse_eq]
  simp only [cosine, FastIntervals.cosineSparse]
  have input := fromRat_encloses interval
  have remainder := fromRat_encloses (cosRemainderBoundComputable interval 10)
  split_ifs with positive
  · simp only [FastIntervals.multiplyForTaylor_eq_mul,
      FastIntervals.evalTaylor_eq_evalTaylorSeries]
    exact ((horner_encloses _ (input.mul input)).add remainder).trans (covers_clip _)
  · simp only [FastIntervals.cosine, FastIntervals.evalTaylor_eq_evalTaylorSeries]
    exact ((horner_encloses _ input).add remainder).trans (covers_clip _)

/-- Compute the two scaled residuals using pre-evaluated trigonometric bounds. -/
def residuals
    (phi theta cosinePhi sinePhi cosineTheta sineTheta : SI) :
    SI × SI :=
  let multiply := SI.mul
  let subtract := fun a b => SI.add a (SI.neg b)
  let scalar := fun q => fromRat (IntervalRat.singleton q)
  let scale := fun q a => multiply (scalar q) a
  let one := scalar 1
  let half := scalar (1 / 2)
  let pi := fromRat kernelPiInterval
  let delta := subtract theta phi
  let base := SI.add
    (SI.add (subtract (subtract (scale (1 / 2) pi) phi) theta)
      (scale (1 / 2) delta)) (scale (1 / 4) (multiply delta delta))
  let denominator := subtract cosinePhi
    (multiply (SI.add one (scale (1 / 2) delta)) sinePhi)
  let numerator := SI.add
    (SI.add (SI.add sinePhi half) (SI.neg (scale (1 / 2) cosinePhi)))
    (multiply base sinePhi)
  let numeratorB := SI.add
    (multiply numerator (SI.add one (scale (1 / 2) delta)))
    (multiply base denominator)
  let first := SI.add
    (SI.add (SI.add (SI.add
      (subtract (multiply numerator (subtract cosineTheta cosinePhi))
        (multiply (scale 2 numeratorB) sinePhi))
      (multiply (multiply (subtract delta one) cosineTheta) denominator))
      (SI.neg (multiply sineTheta denominator)))
      (multiply cosinePhi denominator)) (multiply sinePhi denominator)
  let second := SI.add
    (SI.add (SI.add (SI.add
      (subtract (multiply numerator (SI.add (scale 3 sineTheta) sinePhi))
        (multiply (scale 2 numeratorB) cosinePhi))
      (multiply (multiply (scale 3 (subtract delta one)) sineTheta) denominator))
      (multiply (scale 3 cosineTheta) denominator))
      (SI.neg (multiply sinePhi denominator)))
    (multiply cosinePhi denominator)
  (first, second)

private theorem residuals_enclose
    {phi theta cosinePhi sinePhi cosineTheta sineTheta : IntervalRat}
    {gridPhi gridTheta gridCosinePhi gridSinePhi gridCosineTheta gridSineTheta : SI}
    (phiEnclosed : Encloses gridPhi phi) (thetaEnclosed : Encloses gridTheta theta)
    (cosinePhiEnclosed : Encloses gridCosinePhi cosinePhi)
    (sinePhiEnclosed : Encloses gridSinePhi sinePhi)
    (cosineThetaEnclosed : Encloses gridCosineTheta cosineTheta)
    (sineThetaEnclosed : Encloses gridSineTheta sineTheta) :
    let outer := residuals gridPhi gridTheta gridCosinePhi gridSinePhi
      gridCosineTheta gridSineTheta
    let inner := FastIntervals.residualIntervals mul phi theta
      cosinePhi sinePhi cosineTheta sineTheta
    Encloses outer.1 inner.1 ∧ Encloses outer.2 inner.2 := by
  let scalar (value : ℚ) := fromRat_encloses (singleton value)
  let scale (value : ℚ) {outer : SI} {inner : IntervalRat} (covered : Encloses outer inner) :=
    (scalar value).mul covered
  let delta := thetaEnclosed.add phiEnclosed.neg
  let halfDelta := scale (1 / 2) delta
  let unit := scalar 1
  let base := (((scale (1 / 2) (fromRat_encloses kernelPiInterval)).add phiEnclosed.neg).add
    thetaEnclosed.neg).add halfDelta
  let base := base.add (scale (1 / 4) (delta.mul delta))
  let onePlusHalfDelta := unit.add halfDelta
  let denominator := cosinePhiEnclosed.add (onePlusHalfDelta.mul sinePhiEnclosed).neg
  let numerator := ((sinePhiEnclosed.add (scalar (1 / 2))).add
    (scale (1 / 2) cosinePhiEnclosed).neg).add (base.mul sinePhiEnclosed)
  let numeratorB := (numerator.mul onePlusHalfDelta).add (base.mul denominator)
  let centered := delta.add unit.neg
  let first := (numerator.mul (cosineThetaEnclosed.add cosinePhiEnclosed.neg)).add
    ((scale 2 numeratorB).mul sinePhiEnclosed).neg
  let first := (((first.add ((centered.mul cosineThetaEnclosed).mul denominator)).add
    (sineThetaEnclosed.mul denominator).neg).add (cosinePhiEnclosed.mul denominator)).add
    (sinePhiEnclosed.mul denominator)
  let second := (numerator.mul ((scale 3 sineThetaEnclosed).add sinePhiEnclosed)).add
    ((scale 2 numeratorB).mul cosinePhiEnclosed).neg
  let centeredSine := ((scale 3 centered).mul sineThetaEnclosed).mul denominator
  let second := (((second.add centeredSine).add
    ((scale 3 cosineThetaEnclosed).mul denominator)).add
    (sinePhiEnclosed.mul denominator).neg).add (cosinePhiEnclosed.mul denominator)
  exact ⟨first, second⟩

/-- Check whether the rounded residuals exclude zero. -/
def rejects (cell : AngleCell) : Bool :=
  let phi := cell.phiI
  let theta := cell.thetaI
  let bounds := residuals (fromRat phi) (fromRat theta)
    (cosine phi) (sine phi)
    (cosine theta) (sine theta)
  excludesZero bounds.1 || excludesZero bounds.2

private theorem rejected_of_rounded (cell : AngleCell) (checked : rejects cell = true) :
    cell.rejected = true := by
  have covered := residuals_enclose
    (fromRat_encloses cell.phiI) (fromRat_encloses cell.thetaI)
    (cosine_encloses cell.phiI)
    (sine_encloses cell.phiI)
    (cosine_encloses cell.thetaI)
    (sine_encloses cell.thetaI)
  have original : FastIntervals.rejectWith mul cell
      (cosComputable cell.phiI 10) (sinComputable cell.phiI 10)
      (cosComputable cell.thetaI 10) (sinComputable cell.thetaI 10) =
      cell.rejected := rfl
  rw [← original]
  simp only [rejects, Bool.or_eq_true] at checked
  simp only [FastIntervals.rejectWith, Bool.or_eq_true]
  exact checked.imp covered.1.excludesZero covered.2.excludesZero

/-- Check the grid first and use exact evaluation when the sign is inconclusive. -/
@[instance_reducible] def decidableRejected (cell : AngleCell) :
    Decidable (cell.rejected = true) :=
  if checked : rejects cell = true then
    isTrue (by exact rejected_of_rounded cell checked)
  else
    FastIntervals.decidableRejectedSparse cell

end GerverSofa.PartE.FixedPointResiduals
