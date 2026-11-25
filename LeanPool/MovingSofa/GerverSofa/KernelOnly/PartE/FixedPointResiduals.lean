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

/-- Replay `residuals` with a supplied grid product. -/
def residualsWithProduct
    (multiply : SI → SI → SI) (phi theta cosinePhi sinePhi cosineTheta sineTheta : SI) :
    SI × SI :=
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
  let cosinePhiProduct := multiply cosinePhi denominator
  let sinePhiProduct := multiply sinePhi denominator
  let first := SI.add
    (SI.add (SI.add (SI.add
      (subtract (multiply numerator (subtract cosineTheta cosinePhi))
        (multiply (scale 2 numeratorB) sinePhi))
      (multiply (multiply (subtract delta one) cosineTheta) denominator))
      (SI.neg (multiply sineTheta denominator)))
      cosinePhiProduct) sinePhiProduct
  let second := SI.add
    (SI.add (SI.add (SI.add
      (subtract (multiply numerator (SI.add (scale 3 sineTheta) sinePhi))
        (multiply (scale 2 numeratorB) cosinePhi))
      (multiply (multiply (scale 3 (subtract delta one)) sineTheta) denominator))
      (multiply (scale 3 cosineTheta) denominator))
      (SI.neg sinePhiProduct)) cosinePhiProduct
  (first, second)

private theorem residualsWithProduct_encloses
    (multiply : SI → SI → SI)
    (multiplyEncloses : ∀ {a b : SI} {x y : IntervalRat}, Encloses a x → Encloses b y →
      Encloses (multiply a b) (x.mul y))
    {phi theta cosinePhi sinePhi cosineTheta sineTheta : IntervalRat}
    {gridPhi gridTheta gridCosinePhi gridSinePhi gridCosineTheta gridSineTheta : SI}
    (phiEnclosed : Encloses gridPhi phi) (thetaEnclosed : Encloses gridTheta theta)
    (cosinePhiEnclosed : Encloses gridCosinePhi cosinePhi)
    (sinePhiEnclosed : Encloses gridSinePhi sinePhi)
    (cosineThetaEnclosed : Encloses gridCosineTheta cosineTheta)
    (sineThetaEnclosed : Encloses gridSineTheta sineTheta) :
    let outer := residualsWithProduct multiply gridPhi gridTheta gridCosinePhi gridSinePhi
      gridCosineTheta gridSineTheta
    let inner := FastIntervals.residualIntervals mul phi theta
      cosinePhi sinePhi cosineTheta sineTheta
    Encloses outer.1 inner.1 ∧ Encloses outer.2 inner.2 := by
  let scalar (value : ℚ) := fromRat_encloses (singleton value)
  let scale (value : ℚ) {outer : SI} {inner : IntervalRat} (covered : Encloses outer inner) :=
    multiplyEncloses (scalar value) covered
  let delta := thetaEnclosed.add phiEnclosed.neg
  let halfDelta := scale (1 / 2) delta
  let unit := scalar 1
  let base := (((scale (1 / 2) (fromRat_encloses kernelPiInterval)).add phiEnclosed.neg).add
    thetaEnclosed.neg).add halfDelta
  let base := base.add (scale (1 / 4) (multiplyEncloses delta delta))
  let onePlusHalfDelta := unit.add halfDelta
  let denominator := cosinePhiEnclosed.add
    (multiplyEncloses onePlusHalfDelta sinePhiEnclosed).neg
  let numerator := ((sinePhiEnclosed.add (scalar (1 / 2))).add
    (scale (1 / 2) cosinePhiEnclosed).neg).add (multiplyEncloses base sinePhiEnclosed)
  let numeratorB := (multiplyEncloses numerator onePlusHalfDelta).add
    (multiplyEncloses base denominator)
  let centered := delta.add unit.neg
  let firstDifference := cosineThetaEnclosed.add cosinePhiEnclosed.neg
  let first := (multiplyEncloses numerator firstDifference).add
    (multiplyEncloses (scale 2 numeratorB) sinePhiEnclosed).neg
  let centeredCosine := multiplyEncloses (multiplyEncloses centered cosineThetaEnclosed) denominator
  let sineThetaProduct := multiplyEncloses sineThetaEnclosed denominator
  let cosinePhiProduct := multiplyEncloses cosinePhiEnclosed denominator
  let sinePhiProduct := multiplyEncloses sinePhiEnclosed denominator
  let first := (((first.add centeredCosine).add sineThetaProduct.neg).add cosinePhiProduct).add
    sinePhiProduct
  let secondSum := (scale 3 sineThetaEnclosed).add sinePhiEnclosed
  let second := (multiplyEncloses numerator secondSum).add
    (multiplyEncloses (scale 2 numeratorB) cosinePhiEnclosed).neg
  let centeredSine := multiplyEncloses
    (multiplyEncloses (scale 3 centered) sineThetaEnclosed) denominator
  let scaledCosineTheta := multiplyEncloses (scale 3 cosineThetaEnclosed) denominator
  let second := (((second.add centeredSine).add scaledCosineTheta).add sinePhiProduct.neg).add
    cosinePhiProduct
  exact ⟨first, second⟩

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
    Encloses outer.1 inner.1 ∧ Encloses outer.2 inner.2 :=
  residualsWithProduct_encloses SI.mul Encloses.mul phiEnclosed thetaEnclosed
    cosinePhiEnclosed sinePhiEnclosed cosineThetaEnclosed sineThetaEnclosed

/-- Check whether the rounded residuals exclude zero. -/
def rejects (cell : AngleCell) : Bool :=
  let phi := cell.phiI
  let theta := cell.thetaI
  let bounds := residuals (fromRat phi) (fromRat theta)
    (cosine phi) (sine phi)
    (cosine theta) (sine theta)
  excludesZero bounds.1 || excludesZero bounds.2

private theorem rejected_of_enclosures (cell : AngleCell) {bounds : SI × SI}
    (covered :
      let inner := FastIntervals.residualIntervals mul cell.phiI cell.thetaI
        (cosComputable cell.phiI 10) (sinComputable cell.phiI 10)
        (cosComputable cell.thetaI 10) (sinComputable cell.thetaI 10)
      Encloses bounds.1 inner.1 ∧ Encloses bounds.2 inner.2)
    (checked : (excludesZero bounds.1 || excludesZero bounds.2) = true) :
    cell.rejected = true := by
  have original : FastIntervals.rejectWith mul cell
      (cosComputable cell.phiI 10) (sinComputable cell.phiI 10)
      (cosComputable cell.thetaI 10) (sinComputable cell.thetaI 10) =
      cell.rejected := rfl
  rw [← original]
  simp only [Bool.or_eq_true] at checked
  simp only [FastIntervals.rejectWith, Bool.or_eq_true]
  exact checked.imp covered.1.excludesZero covered.2.excludesZero

private theorem rejected_of_rounded (cell : AngleCell) (checked : rejects cell = true) :
    cell.rejected = true := by
  have covered := residuals_enclose
    (fromRat_encloses cell.phiI) (fromRat_encloses cell.thetaI)
    (cosine_encloses cell.phiI)
    (sine_encloses cell.phiI)
    (cosine_encloses cell.thetaI)
    (sine_encloses cell.thetaI)
  simp only [rejects] at checked
  exact rejected_of_enclosures cell covered checked

/-- Check the grid first and use exact evaluation when the sign is inconclusive. -/
@[instance_reducible] def decidableRejected (cell : AngleCell) :
    Decidable (cell.rejected = true) :=
  if checked : rejects cell = true then
    isTrue (by exact rejected_of_rounded cell checked)
  else
    FastIntervals.decidableRejectedSparse cell

/-! ## Sign-based grid replay -/

/-- Round a product outwards using two endpoints when the right interval is nonnegative. -/
def multiplyNonnegativeRight (left right : SI) : SI :=
  let lower := left.lo * (if 0 ≤ left.lo then right.lo else right.hi)
  let upper := left.hi * (if 0 ≤ left.hi then right.hi else right.lo)
  ⟨lower / M, -((-upper) / M)⟩

private theorem lowerProduct_eq (value : ℤ) (lower upper : ℤ) (ordered : lower ≤ upper) :
    value * (if 0 ≤ value then lower else upper) = min (value * lower) (value * upper) := by
  split_ifs with nonnegative
  · exact (min_eq_left (mul_le_mul_of_nonneg_left ordered nonnegative)).symm
  · exact (min_eq_right (mul_le_mul_of_nonpos_left ordered (le_of_not_ge nonnegative))).symm

private theorem upperProduct_eq (value : ℤ) (lower upper : ℤ) (ordered : lower ≤ upper) :
    value * (if 0 ≤ value then upper else lower) = max (value * lower) (value * upper) := by
  split_ifs with nonnegative
  · exact (max_eq_right (mul_le_mul_of_nonneg_left ordered nonnegative)).symm
  · exact (max_eq_left (mul_le_mul_of_nonpos_left ordered (le_of_not_ge nonnegative))).symm

private theorem multiplyNonnegativeRight_eq (left right : SI)
    (leftOrdered : left.lo ≤ left.hi) (rightOrdered : right.lo ≤ right.hi)
    (nonnegative : 0 ≤ right.lo) :
    multiplyNonnegativeRight left right = SI.mul left right := by
  have lower := mul_le_mul_of_nonneg_right leftOrdered nonnegative
  have upper := mul_le_mul_of_nonneg_right leftOrdered (nonnegative.trans rightOrdered)
  simp only [multiplyNonnegativeRight, SI.mul, imin_eq_min, imax_eq_max,
    lowerProduct_eq _ _ _ rightOrdered, upperProduct_eq _ _ _ rightOrdered,
    min_eq_left (min_le_min lower upper), max_eq_right (max_le_max lower upper)]

/-- Round the Taylor error radius for a nonnegative endpoint upwards in grid units,
without normalizing the rational error term. -/
def remainderRadius (value : ℚ) : ℤ :=
  (M * value.num ^ 11) / ((value.den ^ 11 * 39916800 : ℕ) : ℤ) + 1

private theorem remainderRadius_bound (value : ℚ) :
    value ^ 11 / 39916800 ≤ (remainderRadius value : ℚ) / M := by
  have fraction : (value.num : ℚ) / (value.den : ℚ) = value := by
    rw [← Int.cast_natCast, Rat.intCast_div_eq_divInt, Rat.num_divInt_den]
  apply (le_div_iff₀' scale_pos).2
  have floorBound := Int.lt_floor_add_one
    ((M : ℚ) * (value ^ 11 / 39916800))
  have scaledFloor : ⌊(M : ℚ) * (value ^ 11 / 39916800)⌋ =
      (M * value.num ^ 11) / ((value.den ^ 11 * 39916800 : ℕ) : ℤ) := by
    rw [← Rat.floor_intCast_div_natCast]
    push_cast
    have powerFraction : (value.num : ℚ) ^ 11 / (value.den : ℚ) ^ 11 = value ^ 11 := by
      rw [← div_pow, fraction]
    congr 1
    calc
      _ = (M : ℚ) * (((value.num : ℚ) ^ 11 / (value.den : ℚ) ^ 11) / 39916800) := by
        rw [powerFraction]
      _ = _ := by rw [div_div, ← mul_div_assoc]
  rw [scaledFloor] at floorBound
  simpa only [remainderRadius, Int.cast_add, Int.cast_one] using floorBound.le

private theorem Encloses.orderedGrid {outer : SI} {inner : IntervalRat}
    (enclosed : Encloses outer inner) : outer.lo ≤ outer.hi := by
  exact_mod_cast (div_le_div_iff_of_pos_right scale_pos).1 enclosed.ordered

private theorem Encloses.mulNonnegativeRight
    {outerLeft outerRight : SI} {innerLeft innerRight : IntervalRat}
    (left : Encloses outerLeft innerLeft) (right : Encloses outerRight innerRight)
    (nonnegative : 0 ≤ outerRight.lo) :
    Encloses (multiplyNonnegativeRight outerLeft outerRight) (innerLeft.mul innerRight) := by
  rw [multiplyNonnegativeRight_eq _ _ left.orderedGrid right.orderedGrid nonnegative]
  exact left.mul right

/-- Evaluate a Taylor polynomial by Horner iteration on a nonnegative grid interval. -/
def hornerNonnegative (coefficients : List ℚ) (input : SI) : SI :=
  coefficients.foldr (fun coefficient partialSum =>
    SI.add (fromRat (singleton coefficient)) (multiplyNonnegativeRight partialSum input))
    (fromRat (singleton 0))

private theorem hornerNonnegative_encloses (coefficients : List ℚ) {outer : SI}
    {inner : IntervalRat} (covered : Encloses outer inner) (nonnegative : 0 ≤ outer.lo) :
    Encloses (hornerNonnegative coefficients outer) (evalTaylorSeries coefficients inner) := by
  induction coefficients with
  | nil => exact fromRat_encloses _
  | cons coefficient rest ih =>
    exact (fromRat_encloses (singleton coefficient)).add
      (ih.mulNonnegativeRight covered nonnegative)

private theorem fromRat_lower_nonnegative (interval : IntervalRat) (nonnegative : 0 ≤ interval.lo) :
    0 ≤ (fromRat interval).lo := by
  change 0 ≤ gridFloor interval.lo
  rw [gridFloor_eq]
  exact Int.floor_nonneg.mpr (mul_nonneg scale_pos.le nonnegative)

private theorem multiplyNonnegativeRight_lower_nonnegative (left right : SI)
    (leftNonnegative : 0 ≤ left.lo) (rightNonnegative : 0 ≤ right.lo) :
    0 ≤ (multiplyNonnegativeRight left right).lo := by
  simp only [multiplyNonnegativeRight, ite_eq_left leftNonnegative]
  exact Int.ediv_nonneg (mul_nonneg leftNonnegative rightNonnegative) (by norm_num [M])

/-- Enclose the Taylor remainder symmetrically about zero. -/
def taylorRemainder (value : ℚ) : SI :=
  let radius := remainderRadius value
  ⟨-radius, radius⟩

private theorem taylorRemainder_encloses (interval : IntervalRat) (nonnegative : 0 ≤ interval.lo) :
    Encloses (taylorRemainder interval.hi) (sinRemainderBoundComputable interval 10) := by
  have hiNonnegative := nonnegative.trans interval.le
  have maxAbs_eq : maxAbs interval = interval.hi := by
    rw [maxAbs, abs_of_nonneg nonnegative, abs_of_nonneg hiNonnegative, max_eq_right interval.le]
  have factorial : ratFactorial 11 = 39916800 := by decide +kernel
  have upper : (sinRemainderBoundComputable interval 10).hi ≤
      (remainderRadius interval.hi : ℚ) / M := by
    change maxAbs interval ^ 11 / ratFactorial 11 ≤ _
    rw [maxAbs_eq, factorial]
    exact remainderRadius_bound _
  refine ⟨?_, upper⟩
  change ((-(remainderRadius interval.hi) : ℤ) : ℚ) / M ≤
    -(sinRemainderBoundComputable interval 10).hi
  simpa only [Int.cast_neg, neg_div] using neg_le_neg upper

/-- Enclose cosine and sine together for a positive input, using the same square and radius. -/
def positiveTrig (interval : IntervalRat) : SI × SI :=
  let input := fromRat interval
  let square := multiplyNonnegativeRight input input
  let remainder := taylorRemainder interval.hi
  (SI.add (hornerNonnegative FastIntervals.cosineEvenCoefficients square) remainder,
    SI.add (multiplyNonnegativeRight (hornerNonnegative FastIntervals.sineEvenCoefficients square)
      input) remainder)

private theorem positiveTrig_encloses (interval : IntervalRat) (positive : 0 < interval.lo) :
    Encloses (positiveTrig interval).1 (cosComputable interval 10) ∧
    Encloses (positiveTrig interval).2 (sinComputable interval 10) := by
  let input := fromRat_encloses interval
  let nonnegative := fromRat_lower_nonnegative interval positive.le
  let square := input.mulNonnegativeRight input nonnegative
  let squareNonnegative := multiplyNonnegativeRight_lower_nonnegative _ _ nonnegative nonnegative
  let remainder := taylorRemainder_encloses interval positive.le
  have cosineTaylor := hornerNonnegative_encloses FastIntervals.cosineEvenCoefficients
    square squareNonnegative
  have sineTaylor := hornerNonnegative_encloses FastIntervals.sineEvenCoefficients
    square squareNonnegative
  rw [← FastIntervals.cosineSparse_eq, ← FastIntervals.sineSparse_eq]
  simp only [FastIntervals.cosineSparse, FastIntervals.sineSparse, ite_eq_left positive,
    FastIntervals.multiplyForTaylor_eq_mul, FastIntervals.evalTaylor_eq_evalTaylorSeries]
  exact ⟨(cosineTaylor.add remainder).trans (covers_clip _),
    ((sineTaylor.mulNonnegativeRight input nonnegative).add remainder).trans (covers_clip _)⟩

/-- Select the specialized trigonometric evaluation on positive inputs. -/
def trigBounds (interval : IntervalRat) : SI × SI :=
  if 0 < interval.lo then positiveTrig interval else (cosine interval, sine interval)

private theorem trigBounds_encloses (interval : IntervalRat) :
    Encloses (trigBounds interval).1 (cosComputable interval 10) ∧
    Encloses (trigBounds interval).2 (sinComputable interval 10) := by
  unfold trigBounds
  split_ifs with positive
  · exact positiveTrig_encloses interval positive
  · exact ⟨cosine_encloses interval, sine_encloses interval⟩

/-- Use two endpoint products whenever one interval is nonnegative. -/
def multiplyGrid (left right : SI) : SI :=
  if 0 ≤ right.lo then multiplyNonnegativeRight left right
  else if 0 ≤ left.lo then multiplyNonnegativeRight right left
  else SI.mul left right

private theorem gridMul_comm (left right : SI) : SI.mul left right = SI.mul right left := by
  simp only [SI.mul, imin_eq_min, imax_eq_max]
  congr 2 <;> ac_rfl

private theorem Encloses.mulViaGrid
    {outerLeft outerRight : SI} {innerLeft innerRight : IntervalRat}
    (left : Encloses outerLeft innerLeft) (right : Encloses outerRight innerRight) :
    Encloses (multiplyGrid outerLeft outerRight) (innerLeft.mul innerRight) := by
  unfold multiplyGrid
  split_ifs with rightNonnegative leftNonnegative
  · exact left.mulNonnegativeRight right rightNonnegative
  · rw [multiplyNonnegativeRight_eq _ _ right.orderedGrid left.orderedGrid leftNonnegative,
      gridMul_comm]
    exact left.mul right
  · exact left.mul right

/-- Test for a strict residual sign using the specialized grid operations. -/
def rejectsFast (cell : AngleCell) : Bool :=
  let phi := cell.phiI
  let theta := cell.thetaI
  let phiTrig := trigBounds phi
  let thetaTrig := trigBounds theta
  let bounds := residualsWithProduct multiplyGrid (fromRat phi) (fromRat theta)
    phiTrig.1 phiTrig.2 thetaTrig.1 thetaTrig.2
  excludesZero bounds.1 || excludesZero bounds.2

private theorem rejected_of_fast (cell : AngleCell) (checked : rejectsFast cell = true) :
    cell.rejected = true := by
  have phi := trigBounds_encloses cell.phiI
  have theta := trigBounds_encloses cell.thetaI
  have covered := residualsWithProduct_encloses multiplyGrid Encloses.mulViaGrid
    (fromRat_encloses cell.phiI) (fromRat_encloses cell.thetaI) phi.1 phi.2 theta.1 theta.2
  exact rejected_of_enclosures cell covered checked

/-- Decide rejection with the specialized grid evaluator, falling back to exact arithmetic. -/
@[instance_reducible] def decidableRejectedFast (cell : AngleCell) :
    Decidable (cell.rejected = true) :=
  if checked : rejectsFast cell = true then
    isTrue (by exact rejected_of_fast cell checked)
  else
    FastIntervals.decidableRejectedSparse cell

end GerverSofa.PartE.FixedPointResiduals
