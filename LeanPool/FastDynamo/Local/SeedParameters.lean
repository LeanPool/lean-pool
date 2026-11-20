/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.Contour
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Scalar and contour data of the local instability seed

This is the portion of `prop:local-seed` (Proposition 2.2) that is independent of the
whole-plane Sobolev and operator layers.  It suffices for the scale selection in Section 3.2.

The axial Fourier index `kStar` (wavenumber `N = 2π k_*`) is a parameter of the formalisation:
the paper's local model uses the axial mode `e^{2πix₃}`, i.e. `k_* = 1`, which is also the
value of the seed constructed in `Local/LocalSeedC2Concrete.lean`.

The two-component seed record `LocalSeedC2` (`Local/LocalSeedC2.lean`) carries these parameters
with the helical velocity, the uniform contour resolvent bound and the spectral witness.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- Numeric and contour parameters supplied by uniform local instability. -/
structure LocalSeedParameters where
  /-- Positive local axial Fourier index. -/
  kStar : ℕ
  kStar_pos : 0 < kStar
  /-- Endpoints of the admissible rescaled-diffusivity interval. -/
  deltaMinus : ℝ
  /-- Upper endpoint of the admissible rescaled-diffusivity interval. -/
  deltaPlus : ℝ
  deltaMinus_pos : 0 < deltaMinus
  deltaMinus_lt_one : deltaMinus < 1
  one_lt_deltaPlus : 1 < deltaPlus
  /-- Fixed contour surrounding the unstable local spectrum. -/
  contour : SpectralCircle
  /-- Its closed interior is contained in the open right half-plane. -/
  growthFloor_pos : 0 < contour.growthFloor

namespace LocalSeedParameters

/-- Local axial wavenumber `N = 2π k₍`. -/
def wavenumber (p : LocalSeedParameters) : ℝ :=
  2 * Real.pi * p.kStar

/-- Admissible interval of rescaled diffusivities. -/
def interval (p : LocalSeedParameters) : Set ℝ :=
  Set.Icc p.deltaMinus p.deltaPlus

/-- The upper bound available for the ratio between consecutive integer
frequencies in Section 3.2. -/
def scaleRatioCeiling (p : LocalSeedParameters) : ℝ :=
  Real.sqrt (p.deltaPlus / p.deltaMinus)

/-- The admissible rescaled-diffusivity interval is nondegenerate: `δ₋ < δ₊`, because `δ₋ < 1 < δ₊`.
-/
theorem deltaMinus_lt_deltaPlus (p : LocalSeedParameters) :
    p.deltaMinus < p.deltaPlus :=
  p.deltaMinus_lt_one.trans p.one_lt_deltaPlus

/-- The upper endpoint of the rescaled-diffusivity interval is positive. -/
theorem deltaPlus_pos (p : LocalSeedParameters) : 0 < p.deltaPlus :=
  zero_lt_one.trans p.one_lt_deltaPlus

/-- The endpoints of the diffusivity interval have ratio `δ₊ / δ₋ > 1`. -/
theorem one_lt_deltaRatio (p : LocalSeedParameters) :
    1 < p.deltaPlus / p.deltaMinus := by
  rw [lt_div_iff₀ p.deltaMinus_pos]
  simpa using p.deltaMinus_lt_deltaPlus

/-- The scale-ratio ceiling `√(δ₊/δ₋)` exceeds `1`; this is what leaves room for the strict
ratio `1 < q < √(δ₊/δ₋)` of Section 3.2. -/
theorem one_lt_scaleRatioCeiling (p : LocalSeedParameters) :
    1 < p.scaleRatioCeiling := by
  rw [scaleRatioCeiling, ← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (by norm_num) p.one_lt_deltaRatio

/-- The strict scale ratio required in Section 3.2 always exists from the local
seed's diffusivity interval; it is not an additional assumption.  The paper
uses a single ratio, `1 < q < √(δ₊/δ₋)`, chosen in Section 3.2. -/
theorem exists_scaleRatios (p : LocalSeedParameters) :
    ∃ q : ℝ, 1 < q ∧ q < p.scaleRatioCeiling :=
  exists_between p.one_lt_scaleRatioCeiling

/-- The local axial wavenumber `N = 2π k_*` is positive, since `k_* ≥ 1`. -/
theorem wavenumber_pos (p : LocalSeedParameters) : 0 < p.wavenumber := by
  unfold wavenumber
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr p.kStar_pos)

/-- The local axial wavenumber is nonzero, as required for the fixed-`N` Fourier reduction. -/
theorem wavenumber_ne_zero (p : LocalSeedParameters) : p.wavenumber ≠ 0 :=
  ne_of_gt p.wavenumber_pos

end LocalSeedParameters

end

end FastDynamo
