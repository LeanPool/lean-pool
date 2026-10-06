/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardBallGrowth
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1NormalizedRootEllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidWeightedNormBridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusBallGeometry

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ClosedBallGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the large-scale C¹ slope approximation clause (b2), first step: the exact-root pullback set is a
*closed* Euclidean ball

`ExactRootGaugeTerminal` states its row on
`{y | vecNormSq y ≤ r ^ 2}`, because that set is **exactly** the exact-root
pullback of the ellipsoid
(`Root.matImage_normalizedRoot_inv_ellipsoid_eq`),
whereas the ball geometry is all stated for the **open** ball
`euclideanBall d r = {y | vecNormSq y < r ^ 2}`.

The closed-ball analogue of `volume_euclideanBall_ne_zero/_ne_top` —
`volume {y | vecNormSq y ≤ r^2} ≠ 0, ≠ ⊤`, the sphere being null — is the one
measure fact of (b2) that is not already available.

**It is not needed, and this module removes it.**  A null-sphere argument would
be required only to prove the two volumes *equal*; every use in (b2) needs no
more than the two-sided sandwich

```
euclideanBall d r  ⊆  closedNormBall d r  ⊆  euclideanBall d (2 * r)
```

which is elementary, together with the `volume_euclideanBall_ne_zero` / `_ne_top` and monotonicity
of the measure.  The
cost is a factor `2 ^ d` in the law-free constants — `(6√d)^d` rather than
`(3√d)^d` on the inner side — and no measure theory beyond `measure_mono`.

Nothing here is an estimate: it is set inclusion and measure monotonicity.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- **The exact-root pullback of the ellipsoid.**  The closed Euclidean ball, in
the literal shape `ExactRootGaugeTerminal` names it. -/
@[expose]
def closedNormBall (d : ℕ) (r : ℝ) : Set (Vec d) :=
  {y : Vec d | vecNormSq y ≤ r ^ 2}

/-- The open ball sits inside the closed one. -/
theorem euclideanBall_subset_closedNormBall (d : ℕ) (r : ℝ) :
    euclideanBall d r ⊆ closedNormBall d r := by
  intro y hy
  exact le_of_lt ((mem_euclideanBall_iff y).mp hy)

/-- The closed ball sits inside the doubled open one.  This is the step that
replaces a null-sphere argument. -/
theorem closedNormBall_subset_euclideanBall_two_mul {r : ℝ} (hr : 0 < r) :
    closedNormBall d r ⊆ euclideanBall d (2 * r) := by
  intro y hy
  have hy' : vecNormSq y ≤ r ^ 2 := hy
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hfour : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
  rw [mem_euclideanBall_iff, hfour]
  linarith only [hy', hr2]

/-- The closed ball is bounded. -/
theorem isBounded_closedNormBall (d : ℕ) (r : ℝ) :
    Bornology.IsBounded (closedNormBall d r) := by
  refine Bornology.IsBounded.subset (isBounded_euclideanBall d
    (show (0 : ℝ) < |r| + 1 by positivity)) fun y hy => ?_
  have hy' : vecNormSq y ≤ r ^ 2 := hy
  have habs : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  have hlt : |r| ^ 2 < (|r| + 1) ^ 2 := by nlinarith only [abs_nonneg r]
  exact (mem_euclideanBall_iff y).2 (lt_of_le_of_lt (habs ▸ hy') hlt)

/-! ## The two measure facts, with no null-sphere argument -/

theorem volume_closedNormBall_ne_zero [NeZero d] {r : ℝ} (hr : 0 < r) :
    volume (closedNormBall d r) ≠ 0 := by
  have hmono : volume (euclideanBall d r) ≤ volume (closedNormBall d r) :=
    measure_mono (euclideanBall_subset_closedNormBall d r)
  intro hzero
  exact Root.volume_euclideanBall_ne_zero hr
    (le_antisymm (hzero ▸ hmono) (zero_le))

theorem volume_closedNormBall_ne_top [NeZero d] {r : ℝ} (hr : 0 < r) :
    volume (closedNormBall d r) ≠ ⊤ := by
  have hmono : volume (closedNormBall d r) ≤ volume (euclideanBall d (2 * r)) :=
    measure_mono (closedNormBall_subset_euclideanBall_two_mul hr)
  exact ne_top_of_le_ne_top (Root.volume_euclideanBall_ne_top (2 * r)) hmono

/-! ## The exact-root pullback identification, restated at `closedNormBall` -/

/-- The exact-root pullback of the ellipsoid **is** the closed Euclidean ball.
Restatement of the pullback identity in this module's vocabulary, so the two
volume comparisons below can be read directly against
`ExactRootGaugeTerminal`. -/
theorem matImage_normalizedRoot_inv_ellipsoid_eq_closedNormBall [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) (r : ℝ) :
    matImage (Selection.normalizedRoot (symmPart abar))⁻¹ (ellipsoid abar r) =
      closedNormBall d r :=
  Root.matImage_normalizedRoot_inv_ellipsoid_eq hS r

/-! ## The two volume comparisons of (b2), in structural form -/

/-- **(b2), inner side.**  The energy on the closed ball of radius `r` is
controlled by the energy on any triadic cube containing it, at the price of the
volume ratio — and the closed ball's two measure facts are the ones proved
above, with no null-sphere argument. -/
theorem weightedGradNorm_closedNormBall_le_cube [NeZero d]
    {r : ℝ} (hr : 0 < r) {m : ℤ}
    (hcube : closedNormBall d r ⊆ openCubeSet (originCube d m))
    (hczero : volume (openCubeSet (originCube d m)) ≠ 0)
    (hctop : volume (openCubeSet (originCube d m)) ≠ ⊤)
    (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b (closedNormBall d r) F ≤
      (volume (openCubeSet (originCube d m)) /
          volume (closedNormBall d r)) ^ (1 / 2 : ℝ) *
        weightedGradNorm b (openCubeSet (originCube d m)) F :=
  weightedGradNorm_mono_set_le_volumeRatio hcube
    (volume_closedNormBall_ne_zero hr) (volume_closedNormBall_ne_top hr)
    hczero hctop b F

/-- **(b2), outer side.**  The energy on a triadic cube contained in the closed
ball of radius `R` is controlled by the energy on that ball. -/
theorem weightedGradNorm_cube_le_closedNormBall [NeZero d]
    {R : ℝ} (hR : 0 < R) {m : ℤ}
    (hcube : openCubeSet (originCube d m) ⊆ closedNormBall d R)
    (hczero : volume (openCubeSet (originCube d m)) ≠ 0)
    (hctop : volume (openCubeSet (originCube d m)) ≠ ⊤)
    (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b (openCubeSet (originCube d m)) F ≤
      (volume (closedNormBall d R) /
          volume (openCubeSet (originCube d m))) ^ (1 / 2 : ℝ) *
        weightedGradNorm b (closedNormBall d R) F :=
  weightedGradNorm_mono_set_le_volumeRatio hcube hczero hctop
    (volume_closedNormBall_ne_zero hR) (volume_closedNormBall_ne_top hR)
    b F

/-! ## The two inclusions, at explicit generations -/

/-- The closed ball of radius `r` lies in the triadic cube canonically
enclosing the open ball of radius `2 r`, i.e. the one at radius `2 * (2 * r)`
= `4 r`.  (The radius is left in the `2 * (2 * r)` form the inclusion
produces; the generation congruence converts it to `4 * r` wherever a
consumer prefers that shape.) -/
theorem closedNormBall_subset_outerCube {r : ℝ} (hr : 0 < r) :
    closedNormBall d r ⊆
      openCubeSet (originCube d
        (outerTriadicGeneration (2 * (2 * r)) (by positivity))) :=
  (closedNormBall_subset_euclideanBall_two_mul hr).trans
    (euclideanBall_subset_openCubeSet_originCube_outerTriadicGeneration
      (by positivity))

/-- A triadic cube whose scale-matched ball has radius at most `R` lies in the
closed ball of radius `R`. -/
theorem openCubeSet_originCube_subset_closedNormBall [NeZero d] {R : ℝ}
    (q : ℕ) (hq : Real.sqrt d * (3 : ℝ) ^ q ≤ R) :
    openCubeSet (originCube d (q : ℤ)) ⊆ closedNormBall d R := by
  intro y hy
  have hball := openCubeSet_originCube_subset_scaleMatchedEuclideanBall q hy
  have hlt : vecNormSq y < (Real.sqrt d * (3 : ℝ) ^ q) ^ 2 :=
    (mem_euclideanBall_iff y).mp hball
  have hnonneg : (0 : ℝ) ≤ Real.sqrt d * (3 : ℝ) ^ q := by positivity
  have hsq : (Real.sqrt d * (3 : ℝ) ^ q) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hnonneg hq 2
  exact le_of_lt (lt_of_lt_of_le hlt hsq)

end

end CorrectorComposition
end HighContrast
end HCPolySupport
