/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain
public import LeanPool.HighContrastHomogenization.Support.Geometry.BoundedConvexDomain

/-!
# High-contrast homogenization: Analytic.ConvexDomains

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Bounded open convex domains and the ball sandwich

The Dirichlet estimate `e.random.dirichlet`
is stated on a domain, and the shape datum a domain carries here is a *ball
sandwich*: concentric Euclidean balls of radii `ρ` and `Rad` inside and outside
it, `HasBallSandwich U ρ Rad`.

The first two sections exhibit the sandwich for the two domains that occur, the
ambient supremum-norm ball and the Euclidean ball, and show that the Euclidean
ball is a bounded open convex domain in the sense of the coarse-graining
library.  The third shows that this class is stable under images by an
invertible matrix and produces, for every invertible `M` and every radius
`r > 0`, a nonempty bounded open convex domain whose `M`-image carries the tight
sandwich `(r, r)`.  The last two sections record the measure-theoretic
consequences of the domain class and the sanity facts about the two radii.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The ball sandwich of the ambient (sup-norm) ball -/

/-- The sup-norm ball of `Vec d` is sandwiched between concentric Euclidean
balls of radii `r` and `r * √d`.  **The hypothesis `0 < d` is necessary**: for
`d = 0` the sup-ball is the whole (one-point) space while
`euclideanBallAt c (r * √0) = euclideanBallAt c 0 = ∅`. -/
theorem hasBallSandwich_metricBall {d : ℕ} (c : Vec d) {r : ℝ} (hr : 0 < r) (hd : 0 < d) :
    HasBallSandwich (Metric.ball c r) r (r * Real.sqrt d) := by
  refine ⟨hr, by positivity, c, euclideanBallAt_subset_metricBall c hr, ?_⟩
  intro x hx
  change vecNormSq (x - c) < (r * Real.sqrt d) ^ 2
  have hsq : (r * Real.sqrt d) ^ 2 = (d : ℝ) * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rw [hsq]
  exact vecNormSq_sub_lt_of_mem_metricBall hd hx

/-- The dimension-uniform version of the sandwich for the sup-norm ball, with
the slightly larger outer radius `r * √(d + 1)`; no positivity hypothesis on the
dimension is needed. -/
theorem hasBallSandwich_metricBall_succ {d : ℕ} (c : Vec d) {r : ℝ} (hr : 0 < r) :
    HasBallSandwich (Metric.ball c r) r (r * Real.sqrt ((d : ℝ) + 1)) := by
  refine ⟨hr, by positivity, c, euclideanBallAt_subset_metricBall c hr, ?_⟩
  intro x hx
  change vecNormSq (x - c) < (r * Real.sqrt ((d : ℝ) + 1)) ^ 2
  have hnn : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  have hsq : (r * Real.sqrt ((d : ℝ) + 1)) ^ 2 = ((d : ℝ) + 1) * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnn]
    ring
  have hle := vecNormSq_sub_le_of_mem_metricBall (c := c) (x := x) (r := r) hx
  have hrpos : (0 : ℝ) < r ^ 2 := pow_pos hr 2
  rw [hsq]
  linarith only [hle, hrpos]

/-! ## The Euclidean ball is a bounded open convex domain -/

theorem convex_euclideanBallAt (c : Vec d) (r : ℝ) : Convex ℝ (euclideanBallAt c r) := by
  intro x hx y hy a b ha hb hab
  have hA : vecNormSq (x - c) < r ^ 2 := hx
  have hB : vecNormSq (y - c) < r ^ 2 := hy
  have hcomb : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (c i) * hab
  change vecNormSq (a • x + b • y - c) < r ^ 2
  rw [hcomb]
  have hexp : vecNormSq (a • (x - c) + b • (y - c))
      = a ^ 2 * vecNormSq (x - c) + 2 * (a * b * vecDot (x - c) (y - c))
        + b ^ 2 * vecNormSq (y - c) := by
    rw [vecNormSq_add, vecDot_smul_left, vecDot_smul_right, vecNormSq_smul, vecNormSq_smul]
    ring
  have hdot : vecDot (x - c) (y - c) ≤ vecNormSq (x - c) / 2 + vecNormSq (y - c) / 2 :=
    le_trans (le_abs_self _) (abs_vecDot_le_add_halves_vecNormSq _ _)
  have hab2 : (0 : ℝ) ≤ a * b := mul_nonneg ha hb
  have hcross : 2 * (a * b * vecDot (x - c) (y - c))
      ≤ a * b * (vecNormSq (x - c) + vecNormSq (y - c)) := by
    have h := mul_le_mul_of_nonneg_left hdot hab2
    linarith only [h]
  have hfinal : a ^ 2 * vecNormSq (x - c)
      + a * b * (vecNormSq (x - c) + vecNormSq (y - c))
      + b ^ 2 * vecNormSq (y - c)
      = a * vecNormSq (x - c) + b * vecNormSq (y - c) := by
    have hb1 : b = 1 - a := by linarith only [hab]
    rw [hb1]
    ring
  have hkey : vecNormSq (a • (x - c) + b • (y - c))
      ≤ a * vecNormSq (x - c) + b * vecNormSq (y - c) := by
    rw [hexp]
    linarith only [hcross, hfinal]
  have hstrict : a * vecNormSq (x - c) + b * vecNormSq (y - c) < r ^ 2 := by
    have hconv : a * r ^ 2 + b * r ^ 2 = r ^ 2 := by linear_combination (r ^ 2) * hab
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith only [hab, ha0]
      rw [← ha0, hb1]
      linarith only [hB]
    · have h1 : a * vecNormSq (x - c) < a * r ^ 2 := mul_lt_mul_of_pos_left hA ha0
      have h2 : b * vecNormSq (y - c) ≤ b * r ^ 2 := mul_le_mul_of_nonneg_left hB.le hb
      linarith only [h1, h2, hconv]
  linarith only [hkey, hstrict]

theorem isBoundedDomain_euclideanBallAt (c : Vec d) {r : ℝ} (hr : 0 < r) :
    IsBoundedDomain (euclideanBallAt c r) :=
  Bornology.IsBounded.isBoundedDomain
    (Metric.isBounded_ball.subset (euclideanBallAt_subset_metricBall c hr))

/-- The Euclidean ball is a bounded open convex domain in the sense of the
coarse-graining library. -/
theorem isOpenBoundedConvexDomain_euclideanBallAt (c : Vec d) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (euclideanBallAt c r) :=
  ⟨isOpen_euclideanBallAt c r, isBoundedDomain_euclideanBallAt c hr,
    convex_euclideanBallAt c r⟩

/-- The tight ball sandwich: the Euclidean ball of radius `r` is its own inner
and outer ball. -/
theorem hasBallSandwich_euclideanBallAt {d : ℕ} (c : Vec d) {r : ℝ} (hr : 0 < r) :
    HasBallSandwich (euclideanBallAt c r) r r :=
  ⟨hr, le_of_lt hr, c, subset_rfl, subset_rfl⟩

/-! ## Linear images -/

theorem mem_matImage_iff {M : Mat d} {U : Set (Vec d)} (y : Vec d) :
    y ∈ matImage M U ↔ ∃ x ∈ U, matVecMul M x = y := Iff.rfl

/-- For an invertible `M`, the linear image is the preimage under the inverse. -/
theorem matImage_eq_preimage {M : Mat d} (hM : IsUnit M.det) (U : Set (Vec d)) :
    matImage M U = (fun y : Vec d => matVecMul M⁻¹ y) ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change matVecMul M⁻¹ (matVecMul M x) ∈ U
    rwa [matVecMul_mul, Matrix.nonsing_inv_mul M hM, matVecMul_one]
  · intro hy
    refine ⟨matVecMul M⁻¹ y, hy, ?_⟩
    rw [matVecMul_mul, Matrix.mul_nonsing_inv M hM, matVecMul_one]

theorem isOpen_matImage {M : Mat d} (hM : IsUnit M.det) {U : Set (Vec d)}
    (hU : IsOpen U) : IsOpen (matImage M U) := by
  rw [matImage_eq_preimage hM]
  exact hU.preimage (continuous_matVecMul M⁻¹)

theorem convex_matImage {M : Mat d} {U : Set (Vec d)} (hU : Convex ℝ U) :
    Convex ℝ (matImage M U) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hU hx hy ha hb hab, ?_⟩
  rw [matVecMul_add, matVecMul_smul, matVecMul_smul]

theorem isBoundedDomain_matImage {M : Mat d} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : IsBoundedDomain (matImage M U) := by
  obtain ⟨R, hR, hb⟩ := hU
  have hrows_nonneg : ∀ i : Fin d, (0 : ℝ) ≤ ∑ j, |M i j| := fun i =>
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hs : (0 : ℝ) ≤ ∑ i, ∑ j, |M i j| :=
    Finset.sum_nonneg fun i _ => hrows_nonneg i
  refine ⟨(∑ i, ∑ j, |M i j|) * R + 1, by positivity, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ i
  have hy : (matVecMul M x) i = ∑ j, M i j * x j := rfl
  have hrow : |∑ j, M i j * x j| ≤ (∑ j, |M i j|) * R := by
    calc |∑ j, M i j * x j| ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |M i j| * |x j| := Finset.sum_congr rfl fun j _ => abs_mul _ _
      _ ≤ ∑ j, |M i j| * R := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hb x hx j) (abs_nonneg _)
      _ = (∑ j, |M i j|) * R := (Finset.sum_mul _ _ _).symm
  have hrowle : (∑ j, |M i j|) ≤ ∑ i', ∑ j, |M i' j| :=
    Finset.single_le_sum (f := fun i' => ∑ j, |M i' j|)
      (fun i' _ => hrows_nonneg i') (Finset.mem_univ i)
  have h2 : (∑ j, |M i j|) * R ≤ (∑ i', ∑ j, |M i' j|) * R :=
    mul_le_mul_of_nonneg_right hrowle hR.le
  rw [hy]
  linarith only [hrow, h2]

/-- The linear image of a bounded open convex domain under an invertible matrix
is again a bounded open convex domain. -/
theorem isOpenBoundedConvexDomain_matImage {d : ℕ} {M : Mat d} {U : Set (Vec d)}
    (hM : IsUnit M.det) (hU : IsOpenBoundedConvexDomain U) :
    IsOpenBoundedConvexDomain (matImage M U) :=
  ⟨isOpen_matImage hM hU.isOpen, isBoundedDomain_matImage hU.isBoundedDomain,
    convex_matImage hU.convex⟩

theorem matImage_matImage_inv {d : ℕ} {M : Mat d} (hM : IsUnit M.det) (S : Set (Vec d)) :
    matImage M (matImage M⁻¹ S) = S := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rwa [matVecMul_mul, Matrix.mul_nonsing_inv M hM, matVecMul_one]
  · intro hy
    refine ⟨matVecMul M⁻¹ y, ⟨y, hy, rfl⟩, ?_⟩
    rw [matVecMul_mul, Matrix.mul_nonsing_inv M hM, matVecMul_one]

theorem nonempty_matImage {M : Mat d} {U : Set (Vec d)} (hU : U.Nonempty) :
    (matImage M U).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  exact ⟨matVecMul M x, ⟨x, hx, rfl⟩⟩

/-! ## Domains carrying a prescribed ball sandwich

For an invertible `M` and any `r > 0` there is a nonempty bounded open convex
domain whose `M`-image is exactly the Euclidean ball of radius `r`, hence carries
the tight ball sandwich `(r, r)`.  This is two of the three domain conditions the
Dirichlet estimate imposes; the third, containment in the unit ellipsoid, is
supplied separately, and only the two together inhabit that estimate. -/

theorem exists_domain_with_ballSandwich {d : ℕ} {M : Mat d} (hM : IsUnit M.det)
    {r : ℝ} (hr : 0 < r) :
    ∃ U : Set (Vec d), IsOpenBoundedConvexDomain U ∧ U.Nonempty ∧
      HasBallSandwich (matImage M U) r r := by
  refine ⟨matImage M⁻¹ (euclideanBallAt (0 : Vec d) r), ?_, ?_, ?_⟩
  · exact isOpenBoundedConvexDomain_matImage (Matrix.isUnit_nonsing_inv_det M hM)
      (isOpenBoundedConvexDomain_euclideanBallAt (0 : Vec d) hr)
  · exact nonempty_matImage ⟨(0 : Vec d), center_mem_euclideanBallAt (0 : Vec d) hr⟩
  · rw [matImage_matImage_inv hM]
    exact hasBallSandwich_euclideanBallAt (0 : Vec d) hr

/-! ## Structural consequences of the domain class

`IsOpenBoundedConvexDomain.volume_lt_top`, `.isSobolevRegularDomain` and
`.isFiniteMeasure_restrict_volume` already exist in the coarse-graining library;
the only missing piece is positivity of the volume, which needs nonemptiness. -/

theorem measurableSet_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : MeasurableSet U :=
  hU.isOpen.measurableSet

theorem volume_lt_top_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : volume U < ⊤ :=
  hU.volume_lt_top

theorem volume_pos_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) : 0 < volume U :=
  IsOpen.measure_pos volume hU.isOpen hne

theorem volume_ne_zero_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) : volume U ≠ 0 :=
  ne_of_gt (volume_pos_of_isOpenBoundedConvexDomain hU hne)

theorem volume_ne_top_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : volume U ≠ ⊤ :=
  ne_of_lt hU.volume_lt_top

/-! ## Sanity facts about the ball sandwich

`euclideanBallAt c r` depends on `r` only through `r ^ 2`, so the inclusions
alone cannot distinguish a radius from its negative; that is why the sign of
each radius is a field of the predicate.  With the signs fixed, the inner
radius does not exceed the outer one in positive dimension. -/

theorem euclideanBallAt_abs (c : Vec d) (r : ℝ) :
    euclideanBallAt c |r| = euclideanBallAt c r := by
  ext x
  change vecNormSq (x - c) < |r| ^ 2 ↔ vecNormSq (x - c) < r ^ 2
  rw [sq_abs]

/-- The radii of a sandwich are their own absolute values. -/
theorem HasBallSandwich.abs_radii {U : Set (Vec d)} {ρ Rad : ℝ}
    (h : HasBallSandwich U ρ Rad) : |ρ| = ρ ∧ |Rad| = Rad :=
  ⟨abs_of_pos h.1, abs_of_nonneg h.2.1⟩

/-- The inner radius of a sandwich never exceeds the outer radius in absolute
value, in positive dimension. -/
theorem HasBallSandwich.le_abs_of_pos_dim {d : ℕ} {U : Set (Vec d)} {ρ Rad : ℝ}
    (hd : 0 < d) (h : HasBallSandwich U ρ Rad) (hρ : 0 < ρ) : ρ ≤ |Rad| := by
  obtain ⟨-, -, c, hin, hout⟩ := h
  by_contra hcon
  push Not at hcon
  set t : ℝ := (|Rad| + ρ) / 2 with ht
  have hRad0 : (0 : ℝ) ≤ |Rad| := abs_nonneg _
  have ht0 : 0 < t := by rw [ht]; linarith only [hRad0, hρ]
  have htρ : t < ρ := by rw [ht]; linarith only [hcon]
  have htR : |Rad| < t := by rw [ht]; linarith only [hcon]
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  set z : Vec d := c + t • basisVec i0 with hz
  have hzc : z - c = t • basisVec i0 := by rw [hz]; ext j; simp
  have hnorm : vecNormSq (z - c) = t ^ 2 := by
    rw [hzc, vecNormSq_smul, vecNormSq_basisVec, mul_one]
  have hmemin : z ∈ euclideanBallAt c ρ := by
    change vecNormSq (z - c) < ρ ^ 2
    rw [hnorm]
    calc t ^ 2 = t * t := pow_two t
      _ < ρ * ρ := mul_self_lt_mul_self ht0.le htρ
      _ = ρ ^ 2 := (pow_two ρ).symm
  have hmemout : z ∈ euclideanBallAt c Rad := hout (hin hmemin)
  have hlt : vecNormSq (z - c) < Rad ^ 2 := hmemout
  rw [hnorm, ← sq_abs Rad] at hlt
  have : t < |Rad| := lt_of_sq_lt_sq' hRad0 hlt
  linarith only [this, htR]

/-- With the signs fixed by the predicate, the inner radius of a sandwich does
not exceed the outer radius. -/
theorem HasBallSandwich.le_of_pos_dim {d : ℕ} {U : Set (Vec d)} {ρ Rad : ℝ}
    (hd : 0 < d) (h : HasBallSandwich U ρ Rad) : ρ ≤ Rad := by
  have hle := HasBallSandwich.le_abs_of_pos_dim hd h h.1
  rwa [abs_of_nonneg h.2.1] at hle

end

end HighContrast
end HCPolySupport
