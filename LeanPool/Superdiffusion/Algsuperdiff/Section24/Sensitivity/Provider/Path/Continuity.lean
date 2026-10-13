/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.PairingBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.DerivativeBridge

/-!
# Continuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Continuity of the linear response term along the perturbation path

The two-sided second-difference expansion of `mu` produces the base linear
term of the *perturbed* minimizer on the lower side and of the *base*
minimizer on the upper side.  Turning the expansion into a derivative
therefore requires

`ℓ(X_t) → ℓ(X_0)`  as  `t → 0`.

This module proves the quantitative version `|ℓ(X_t) - ℓ(X_0)| ≤ C √|t|`.
The two ingredients are:

* the *energy gap* `E_0(X_t) - mu_0 ≤ C |t|`, obtained by testing each of the
  two minimum problems with the other minimizer and absorbing the linear terms
  with `abs_pathLinearTerm_le`; and
* uniform convexity `½ E_0(X_0 - X_t) ≤ E_0(X_t) - mu_0` together with the
  Young estimate for the bilinear response pairing, whose free parameter is
  tuned to `|t|^{-1/2}`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Polarization of the linear response term -/

theorem pathLinearPairingDensity_add_eq {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X Y : DoubledField d) (x : Vec d) :
    pathLinearPairingDensity a hField (X - Y) X x
        + pathLinearPairingDensity a hField Y (X - Y) x
      = pathLinearDensity a hField X x - pathLinearDensity a hField Y x := by
  set V : DoubledField d → Vec d := fun Z =>
    (blockMatVecMul (blockMatrixField a x) (Z.eval x)).2 with hV
  have hVsub : V (X - Y) = V X - V Y := by
    have hev : (X - Y).eval x = X.eval x - Y.eval x := rfl
    show (blockMatVecMul (blockMatrixField a x) ((X - Y).eval x)).2 =
      (blockMatVecMul (blockMatrixField a x) (X.eval x)).2 -
        (blockMatVecMul (blockMatrixField a x) (Y.eval x)).2
    rw [hev, blockMatVecMul_sub]
    rfl
  have hmsub : matVecMul (hField x) ((X - Y).potential x) =
      matVecMul (hField x) (X.potential x) - matVecMul (hField x) (Y.potential x) := by
    have hp : (X - Y).potential x = X.potential x - Y.potential x := rfl
    rw [hp, sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
  have hleft : ∀ u v w : Vec d, vecDot (u - v) w = vecDot u w - vecDot v w := by
    intro u v w
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  have hright : ∀ u v w : Vec d, vecDot u (v - w) = vecDot u v - vecDot u w := by
    intro u v w
    rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, ← sub_eq_add_neg]
  show -vecDot (matVecMul (hField x) ((X - Y).potential x)) (V X)
      + -vecDot (matVecMul (hField x) (Y.potential x)) (V (X - Y))
    = -vecDot (matVecMul (hField x) (X.potential x)) (V X)
      - -vecDot (matVecMul (hField x) (Y.potential x)) (V Y)
  rw [hmsub, hVsub, hleft, hright]
  ring

/-- **Polarization of the linear response term.**  The difference of the linear
terms of two doubled fields splits into two bilinear pairings, each of which
carries the difference field in one slot. -/
theorem pathLinearTerm_sub_eq {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) {X Y : DoubledField d}
    (hXpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hXflux : MemVectorL2 (U : Set (Vec d)) X.flux)
    (hYpot : MemVectorL2 (U : Set (Vec d)) Y.potential)
    (hYflux : MemVectorL2 (U : Set (Vec d)) Y.flux) :
    pathLinearTerm a h.1 X - pathLinearTerm a h.1 Y
      = pathLinearPairing a h.1 (X - Y) X
        + pathLinearPairing a h.1 Y (X - Y) := by
  have hsubpot : MemVectorL2 (U : Set (Vec d)) ((X - Y).potential) :=
    hXpot.sub hYpot
  have hsubflux : MemVectorL2 (U : Set (Vec d)) ((X - Y).flux) :=
    hXflux.sub hYflux
  have hI1 := integrableOn_pathLinearPairingDensity a h hsubpot hXpot hXflux
  have hI2 := integrableOn_pathLinearPairingDensity a h hYpot hsubpot hsubflux
  have hLX := integrableOn_pathLinearDensity a h hXpot hXflux
  have hLY := integrableOn_pathLinearDensity a h hYpot hYflux
  have hfun :
      pathLinearPairingDensity a h.1 (X - Y) X
          + pathLinearPairingDensity a h.1 Y (X - Y)
        = pathLinearDensity a h.1 X - pathLinearDensity a h.1 Y := by
    funext x
    exact pathLinearPairingDensity_add_eq a h.1 X Y x
  show volumeAverage (U : Set (Vec d)) (pathLinearDensity a h.1 X)
      - volumeAverage (U : Set (Vec d)) (pathLinearDensity a h.1 Y) = _
  rw [← volumeAverage_sub hLX hLY, ← hfun, volumeAverage_add hI1 hI2]
  rfl

/-! ## Constants -/

/-- Domination constant of the linear response term by the doubled energy. -/
def pathLinConst {U : Domain d} (a : CoeffOn U) (h : LInfMatrixFieldOn U) : ℝ :=
  pathLinearConstL a h + pathLinearConstR a

theorem pathLinConst_nonneg {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) : 0 ≤ pathLinConst a h :=
  add_nonneg (pathLinearConstL_nonneg a h) (pathLinearConstR_nonneg a)

/-- The parameter window on which the energy gap is linear in `t`. -/
def pathSmallParam {U : Domain d} (a : CoeffOn U) (h : LInfMatrixFieldOn U) : ℝ :=
  1 / (2 * pathLinConst a h + 2)

theorem pathSmallParam_pos {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) : 0 < pathSmallParam a h := by
  unfold pathSmallParam
  have := pathLinConst_nonneg a h
  positivity

theorem pathSmallParam_le_one {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) : pathSmallParam a h ≤ 1 := by
  unfold pathSmallParam
  have hc := pathLinConst_nonneg a h
  rw [div_le_one (by linarith only [hc])]
  linarith only [hc]

/-- Energy-gap constant. -/
def pathGapConst {U : Domain d} (a : CoeffOn U) (h : LInfMatrixFieldOn U)
    (P : BlockVec d) : ℝ :=
  (4 * pathLinConst a h + 2 * pathQuadConst a h) * doubledMu U a P

theorem doubledMu_nonneg {U : Domain d} (a : CoeffOn U) (P : BlockVec d) :
    0 ≤ doubledMu U a P := by
  obtain ⟨X, hX⟩ := (doubledMuTheory U a).minimizer_exists P
  rw [← hX.doubledMuValue_eq_doubledMu]
  exact doubledMuValue_nonneg a X

theorem pathGapConst_nonneg {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (P : BlockVec d) : 0 ≤ pathGapConst a h P := by
  unfold pathGapConst
  have h1 := pathLinConst_nonneg a h
  have h2 := pathQuadConst_nonneg a h
  have h3 := doubledMu_nonneg a P
  positivity

/-- Continuity constant of the linear response term. -/
def pathContConst {U : Domain d} (a : CoeffOn U) (h : LInfMatrixFieldOn U)
    (P : BlockVec d) : ℝ :=
  2 * pathGapConst a h P * pathLinearConstL a h
    + pathLinearConstR a * doubledMu U a P
    + pathLinearConstL a h * (doubledMu U a P + pathGapConst a h P)
    + 2 * pathGapConst a h P * pathLinearConstR a

theorem pathContConst_nonneg {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (P : BlockVec d) : 0 ≤ pathContConst a h P := by
  unfold pathContConst
  have h1 := pathLinearConstL_nonneg a h
  have h2 := pathLinearConstR_nonneg a
  have h3 := pathGapConst_nonneg a h P
  have h4 := doubledMu_nonneg a P
  positivity

/-! ## The energy gap -/

/-- **Energy gap of the perturbed minimizer.**  Testing each minimum problem
with the other minimizer and absorbing the linear terms bounds the base energy
of the perturbed minimizer linearly in `t`. -/
theorem doubledMuValue_sub_doubledMu_le {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (P : BlockVec d) {t : ℝ}
    (ht : |t| ≤ pathSmallParam a h.1) {Xt : DoubledField d}
    (hXt : IsDoubledMuMinimizer U (perturbCoeffOn U a h t) P Xt) :
    doubledMuValue U a Xt - doubledMu U a P ≤ pathGapConst a h.1 P * |t| := by
  obtain ⟨X0, hX0⟩ := (doubledMuTheory U a).minimizer_exists P
  have hpot0 := memVectorL2_potential_of_isDoubledMuAdmissible hX0.1
  have hflux0 := memVectorL2_flux_of_isDoubledMuAdmissible hX0.1
  have hpotT := memVectorL2_potential_of_isDoubledMuAdmissible hXt.1
  have hfluxT := memVectorL2_flux_of_isDoubledMuAdmissible hXt.1
  set M : ℝ := doubledMu U a P with hM
  set A : ℝ := doubledMuValue U a Xt with hA
  set L0 : ℝ := pathLinearTerm a h.1.1 X0 with hL0
  set Lt : ℝ := pathLinearTerm a h.1.1 Xt with hLt
  set Q0 : ℝ := pathQuadraticTerm a h.1.1 X0 with hQ0
  set Qt : ℝ := pathQuadraticTerm a h.1.1 Xt with hQt
  set c : ℝ := pathLinConst a h.1 with hc
  set Cq : ℝ := pathQuadConst a h.1 with hCq
  have hX0value : doubledMuValue U a X0 = M := hX0.doubledMuValue_eq_doubledMu
  -- the two expansions
  have hexpT := doubledMuValue_perturbCoeffOn a h t hpotT hfluxT (X := Xt)
  have hexp0 := doubledMuValue_perturbCoeffOn a h t hpot0 hflux0 (X := X0)
  rw [hX0value] at hexp0
  have hcompare : doubledMuValue U (perturbCoeffOn U a h t) Xt ≤
      doubledMuValue U (perturbCoeffOn U a h t) X0 := hXt.2 X0 hX0.1
  have hmain : A + t * Lt + t ^ 2 * Qt ≤ M + t * L0 + t ^ 2 * Q0 := by
    rw [hexpT, hexp0] at hcompare
    exact hcompare
  -- structural facts
  have hMnonneg : 0 ≤ M := doubledMu_nonneg a P
  have hAge : M ≤ A := by
    have := hX0.2 Xt hXt.1
    rw [hX0value] at this
    exact this
  have hD : 0 ≤ A - M := by linarith only [hAge]
  have hQtnonneg : 0 ≤ Qt := pathQuadraticTerm_nonneg a h.1.1 Xt
  have hQ0nonneg : 0 ≤ Q0 := pathQuadraticTerm_nonneg a h.1.1 X0
  have hQ0le : Q0 ≤ Cq * M := by
    have := pathQuadraticTerm_le a h.1 hpot0 hflux0
    rw [hX0value] at this
    exact this
  have hL0le : |L0| ≤ c * M := by
    have := abs_pathLinearTerm_le a h.1 hpot0 hflux0
    rw [hX0value] at this
    exact this
  have hLtle : |Lt| ≤ c * A := abs_pathLinearTerm_le a h.1 hpotT hfluxT
  -- smallness of the parameter
  have hcnonneg : 0 ≤ c := pathLinConst_nonneg a h.1
  have habs : 0 ≤ |t| := abs_nonneg t
  have htone : |t| ≤ 1 := ht.trans (pathSmallParam_le_one a h.1)
  have htc : |t| * c ≤ 1 / 2 := by
    have hden : 0 < 2 * c + 2 := by linarith only [hcnonneg]
    have h1 : |t| ≤ 1 / (2 * c + 2) := ht
    have h2 : |t| * c ≤ (1 / (2 * c + 2)) * c :=
      mul_le_mul_of_nonneg_right h1 hcnonneg
    have h3 : (1 / (2 * c + 2)) * c ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
      linarith only [hcnonneg]
    linarith only [h2, h3]
  have htsq : t ^ 2 ≤ |t| := by
    have : t ^ 2 = |t| * |t| := by rw [← abs_mul, abs_mul_self, sq]
    rw [this]
    exact mul_le_of_le_one_left habs htone
  -- absorb the linear terms
  have hlin1 : t * L0 ≤ |t| * (c * M) := by
    have h1 : t * L0 ≤ |t * L0| := le_abs_self _
    have h2 : |t * L0| = |t| * |L0| := abs_mul t L0
    have h3 : |t| * |L0| ≤ |t| * (c * M) := mul_le_mul_of_nonneg_left hL0le habs
    linarith only [h1, h2, h3]
  have hlin2 : -(t * Lt) ≤ |t| * (c * A) := by
    have h1 : -(t * Lt) ≤ |t * Lt| := neg_le_abs _
    have h2 : |t * Lt| = |t| * |Lt| := abs_mul t Lt
    have h3 : |t| * |Lt| ≤ |t| * (c * A) := mul_le_mul_of_nonneg_left hLtle habs
    linarith only [h1, h2, h3]
  have hquad1 : t ^ 2 * Q0 ≤ |t| * (Cq * M) := by
    have h1 : t ^ 2 * Q0 ≤ |t| * Q0 := mul_le_mul_of_nonneg_right htsq hQ0nonneg
    have h2 : |t| * Q0 ≤ |t| * (Cq * M) := mul_le_mul_of_nonneg_left hQ0le habs
    linarith only [h1, h2]
  have hquad2 : (0 : ℝ) ≤ t ^ 2 * Qt := by positivity
  have hstep : A - M ≤ |t| * (c * M) + |t| * (c * A) + |t| * (Cq * M) := by
    linarith only [hmain, hlin1, hlin2, hquad1, hquad2]
  -- absorb the `A` on the right-hand side
  have habsorb : |t| * (c * A) ≤ |t| * (c * M) + (A - M) / 2 := by
    have hsplit : |t| * (c * A) = |t| * (c * M) + (|t| * c) * (A - M) := by ring
    have hmul : (|t| * c) * (A - M) ≤ (1 / 2) * (A - M) :=
      mul_le_mul_of_nonneg_right htc hD
    linarith only [hsplit, hmul]
  have hfinal : A - M ≤ |t| * ((4 * c + 2 * Cq) * M) := by
    linarith only [hstep, habsorb]
  calc
    A - M ≤ |t| * ((4 * c + 2 * Cq) * M) := hfinal
    _ = pathGapConst a h.1 P * |t| := by
      unfold pathGapConst
      rw [hc, hCq, hM]
      ring

/-! ## Continuity of the linear response term -/

/-- **Minimizer continuity.**  The base linear response term of the perturbed
minimizer converges to that of the base minimizer, with rate `√|t|`. -/
theorem abs_pathLinearTerm_sub_le {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (P : BlockVec d) {t : ℝ}
    (ht : |t| ≤ pathSmallParam a h.1) (ht0 : t ≠ 0)
    {X0 Xt : DoubledField d} (hX0 : IsDoubledMuMinimizer U a P X0)
    (hXt : IsDoubledMuMinimizer U (perturbCoeffOn U a h t) P Xt) :
    |pathLinearTerm a h.1.1 Xt - pathLinearTerm a h.1.1 X0|
      ≤ pathContConst a h.1 P * Real.sqrt |t| := by
  have hpot0 := memVectorL2_potential_of_isDoubledMuAdmissible hX0.1
  have hflux0 := memVectorL2_flux_of_isDoubledMuAdmissible hX0.1
  have hpotT := memVectorL2_potential_of_isDoubledMuAdmissible hXt.1
  have hfluxT := memVectorL2_flux_of_isDoubledMuAdmissible hXt.1
  have hsubpot : MemVectorL2 (U : Set (Vec d)) ((X0 - Xt).potential) :=
    hpot0.sub hpotT
  have hsubflux : MemVectorL2 (U : Set (Vec d)) ((X0 - Xt).flux) :=
    hflux0.sub hfluxT
  set M : ℝ := doubledMu U a P with hM
  set C2 : ℝ := pathGapConst a h.1 P with hC2
  set D1 : ℝ := pathLinearConstL a h.1 with hD1
  set D2 : ℝ := pathLinearConstR a with hD2
  set δ : ℝ := doubledMuValue U a (X0 - Xt) with hδ
  have hX0value : doubledMuValue U a X0 = M := hX0.doubledMuValue_eq_doubledMu
  have hD1nonneg : 0 ≤ D1 := pathLinearConstL_nonneg a h.1
  have hD2nonneg : 0 ≤ D2 := pathLinearConstR_nonneg a
  have hC2nonneg : 0 ≤ C2 := pathGapConst_nonneg a h.1 P
  have hMnonneg : 0 ≤ M := doubledMu_nonneg a P
  have hδnonneg : 0 ≤ δ := doubledMuValue_nonneg a (X0 - Xt)
  -- the square root parameter
  have habs : 0 < |t| := abs_pos.2 ht0
  set s : ℝ := Real.sqrt |t| with hs
  have hspos : 0 < s := Real.sqrt_pos.2 habs
  have hss : s * s = |t| := Real.mul_self_sqrt habs.le
  have htone : |t| ≤ 1 := ht.trans (pathSmallParam_le_one a h.1)
  -- the energy gap and the uniform convexity
  have hgap : doubledMuValue U a Xt - M ≤ C2 * |t| :=
    doubledMuValue_sub_doubledMu_le a h P ht hXt
  have hconv : (1 / 2 : ℝ) * δ ≤ doubledMuValue U a Xt - doubledMuValue U a X0 :=
    half_doubledMuValue_sub_le_of_isDoubledMuMinimizer a hX0 hXt.1
  rw [hX0value] at hconv
  have hδle : δ ≤ 2 * (C2 * (s * s)) := by
    rw [hss]
    linarith only [hgap, hconv]
  have hEtle : doubledMuValue U a Xt ≤ M + C2 := by
    have h1 : C2 * |t| ≤ C2 * 1 := mul_le_mul_of_nonneg_left htone hC2nonneg
    linarith only [hgap, h1]
  -- polarization and the two Young estimates
  have hpolar := pathLinearTerm_sub_eq a h.1 hpot0 hflux0 hpotT hfluxT
  have hY1 := abs_pathLinearPairing_le a h.1 hsubpot hsubflux hpot0 hflux0
    (η := s⁻¹) (by positivity)
  have hY2 := abs_pathLinearPairing_le a h.1 hpotT hfluxT hsubpot hsubflux
    (η := s) hspos
  rw [hX0value, inv_inv] at hY1
  -- bound each contribution by a multiple of `s`
  have hbound1 : s⁻¹ * D1 * δ ≤ 2 * C2 * D1 * s := by
    have hfac : 0 ≤ s⁻¹ * D1 := by positivity
    have h1 : s⁻¹ * D1 * δ ≤ s⁻¹ * D1 * (2 * (C2 * (s * s))) :=
      mul_le_mul_of_nonneg_left hδle hfac
    have h2 : s⁻¹ * D1 * (2 * (C2 * (s * s))) = 2 * C2 * D1 * s := by
      field_simp
    linarith only [h1, h2]
  have hbound2 : s⁻¹ * D2 * δ ≤ 2 * C2 * D2 * s := by
    have hfac : 0 ≤ s⁻¹ * D2 := by positivity
    have h1 : s⁻¹ * D2 * δ ≤ s⁻¹ * D2 * (2 * (C2 * (s * s))) :=
      mul_le_mul_of_nonneg_left hδle hfac
    have h2 : s⁻¹ * D2 * (2 * (C2 * (s * s))) = 2 * C2 * D2 * s := by
      field_simp
    linarith only [h1, h2]
  have hbound3 : s * D1 * doubledMuValue U a Xt ≤ D1 * (M + C2) * s := by
    have hfac : 0 ≤ s * D1 := by positivity
    have h1 : s * D1 * doubledMuValue U a Xt ≤ s * D1 * (M + C2) :=
      mul_le_mul_of_nonneg_left hEtle hfac
    have h2 : s * D1 * (M + C2) = D1 * (M + C2) * s := by ring
    linarith only [h1, h2]
  have hsum : |pathLinearTerm a h.1.1 X0 - pathLinearTerm a h.1.1 Xt|
      ≤ pathContConst a h.1 P * s := by
    have htri := abs_add_le (pathLinearPairing a h.1.1 (X0 - Xt) X0)
      (pathLinearPairing a h.1.1 Xt (X0 - Xt))
    rw [hpolar]
    have hcont : pathContConst a h.1 P =
        2 * C2 * D1 + D2 * M + D1 * (M + C2) + 2 * C2 * D2 := by
      unfold pathContConst
      rw [hC2, hD1, hD2, hM]
    rw [hcont]
    have hsD2 : s * D2 * M = D2 * M * s := by ring
    linarith only [htri, hY1, hY2, hbound1, hbound2, hbound3, hsD2]
  rw [abs_sub_comm]
  exact hsum

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
