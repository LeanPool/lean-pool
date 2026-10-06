/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastIsotropyCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRowEnvelope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The isotropic row envelope and its deep tail

The row estimate requires an envelope for every aligned adapted cell.  By
stationarity,
`annealedBlock P (adaptedCellAt q k w) = adaptedMean P q k`, so an isotropy
bound for the adapted mean gives the same bound for each aligned cell.  This is
formalized by `annealedBlock_adaptedCellAt_le_isotropy` at the scalar
`1 + cIso`.

The isotropy bound applies only beyond its threshold.  Splitting the row at
that threshold leaves a deep tail controlled by the coarse ellipticity
envelope.  The row weight
`Response.profileRowWeight k s = 3 ^ ((3/2) * (k-s))` combines with envelope growth
`3 ^ (g * (s-k))` to leave the geometric rate `3/2 - g`, which is positive for
every `g < 1`.  The identity is isolated in `rowWeight_mul_envelope`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The per-cell envelope at every aligned cell of the row -/

/-- **The per-cell isotropy envelope.**  Every aligned adapted cell past the two
near-identity thresholds obeys the `Π`-free envelope `1 + cIso`.  By
stationarity, the annealed block of an aligned cell is the adapted mean at that
scale, to which the isotropy bound applies. -/
theorem annealedBlock_adaptedCellAt_le_isotropy [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {k r : ℤ} {G : ℕ} (hk0 : 0 ≤ k) (hlr : l ≤ r)
    {sigma cEnt : ℝ} (hsigma : refContrast E - 1 ≤ sigma) (hsigma0 : 0 ≤ sigma)
    (hcEnt : 0 < cEnt)
    (hkthr : euclideanEntryThreshold K (cEnt / 2) sK ≤ k)
    (hgap : tiltGap Cd g (cEnt / 2) nu G ≤ r - k)
    (hDelta : 0 ≤ r + (G : ℤ) - 1 - sK)
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (r + (G : ℤ) - sK))
    (hsub : adaptedCell (roundedGrid l nu) r ⊆ centeredCube d (r + (G : ℤ)))
    (hint : HasFiniteAdaptedMean P (roundedGrid l nu) r)
    (w : Fin d → ℤ) :
    BlockMatLoewnerLE
      (annealedBlock P (adaptedCellAt (roundedGrid l nu) r w))
      (isotropyReference (nearIdentityDefect cEnt sigma) E) := by
  have hq : (roundedGrid l nu).PosDef := Recurrence.posDef_roundedGrid hl hnu
  have hgrid : IsRoundedGrid l (roundedGrid l nu) := ⟨hl, nu, hnu, rfl⟩
  have hmeas : HasMeasurableCoarseBlock P (adaptedCell (roundedGrid l nu) r) :=
    Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq r
  rw [Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hstat hgrid hlr hmeas w]
  exact (adaptedMean_near_reference hd hg hdag hstat hl hCd hnu hsK hk0 hsigma
    hsigma0 hcEnt hkthr hgap hDelta hentry hsub hint).2

/-! ## Piece two: the deep tail of the row is geometrically discounted -/

/-- The raw row weight
`3^{(3/2)(k-s)}` against the Dagger envelope `3^{g(T-k)}` at the row's base `s`:
`g` of the weight's `3/2` is consumed by the envelope's growth with depth, and
the residual rate is `3/2 - g`. -/
theorem rowWeight_mul_envelope (g k s T : ℝ) :
    (3 : ℝ) ^ (3 / 2 * (k - s)) * (3 : ℝ) ^ (g * (T - k)) =
      (3 : ℝ) ^ ((3 / 2 - g) * (k - s)) * (3 : ℝ) ^ (g * (T - s)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

end

end HCPolySupport.HighContrast.Quenched
