/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Convexity

/-!
# PairingBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Domination of the response densities by the doubled energy density

The linear response term `ℓ` is the diagonal of the bilinear pairing

`B(X, Y) = -⨍ (h X₁) · (bfA(a) Y)₂`,

and the quadratic term `q` is a second quadratic form in the same variable.
Both are dominated pointwise by the doubled energy density of the base
coefficient, with a free Young parameter in the bilinear estimate.  Working
with the energy rather than with an `L²` norm is what keeps the whole
continuity argument inside the doubled functional.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Averaging helpers -/

theorem volumeAverage_mono_ae {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U) (hg : IntegrableOn g U)
    (hfg : f ≤ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f ≤ volumeAverage U g := by
  unfold volumeAverage
  refine mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg) ?_
  exact inv_nonneg.mpr ENNReal.toReal_nonneg

theorem volumeAverage_neg {U : Set (Vec d)} (f : Vec d → ℝ) :
    volumeAverage U (fun x => -f x) = -volumeAverage U f := by
  have h := volumeAverage_smul U (-1 : ℝ) f
  rw [show ((-1 : ℝ) • f) = (fun x => -f x) by funext x; simp] at h
  rw [h]
  ring

theorem abs_volumeAverage_le {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U) (hg : IntegrableOn g U)
    (hfg : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ g x) :
    |volumeAverage U f| ≤ volumeAverage U g := by
  have hup : volumeAverage U f ≤ volumeAverage U g :=
    volumeAverage_mono_ae hf hg (hfg.mono fun x hx => (le_abs_self (f x)).trans hx)
  have hneg : IntegrableOn (fun x => -g x) U := hg.neg
  have hlow : volumeAverage U (fun x => -g x) ≤ volumeAverage U f :=
    volumeAverage_mono_ae hneg hf
      (hfg.mono fun x hx => by
        have := (neg_abs_le (f x)).trans' (by linarith [hx] : -g x ≤ -|f x|)
        linarith [neg_abs_le (f x), hx])
  rw [volumeAverage_neg] at hlow
  exact abs_le.2 ⟨by linarith, hup⟩

/-! ## The bilinear response pairing -/

/-- Density of the bilinear response pairing `-(h X₁) · (bfA(a) Y)₂`, whose
diagonal is the linear response density. -/
def pathLinearPairingDensity {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X Y : DoubledField d) : Vec d → ℝ :=
  fun x =>
    -vecDot (matVecMul (hField x) (X.potential x))
      ((blockMatVecMul (blockMatrixField a x) (Y.eval x)).2)

/-- Averaged bilinear response pairing. -/
def pathLinearPairing {U : Domain d} (a : CoeffOn U) (hField : CoeffField d)
    (X Y : DoubledField d) : ℝ :=
  average U (pathLinearPairingDensity a hField X Y)

theorem pathLinearTerm_eq_pairing {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X : DoubledField d) :
    pathLinearTerm a hField X = pathLinearPairing a hField X X := rfl

theorem integrableOn_pathLinearPairingDensity {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) {X Y : DoubledField d}
    (hXpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hYpot : MemVectorL2 (U : Set (Vec d)) Y.potential)
    (hYflux : MemVectorL2 (U : Set (Vec d)) Y.flux) :
    IntegrableOn (pathLinearPairingDensity a h.1 X Y) (U : Set (Vec d)) := by
  have hmul :=
    Algsuperdiff.Section24.memVectorL2_matVecMul_of_lInfMatrixFieldOn U h hXpot
  have hdot := integrableOn_vecDot_of_memVectorL2 hmul
    (memVectorL2_blockMatrixField_snd a hYpot hYflux)
  exact hdot.neg

/-! ## Pointwise domination by the energy density -/

/-- The response constants attached to the base coefficient and the `L∞`
perturbation. -/
def pathLinearConstL {U : Domain d} (a : CoeffOn U) (h : LInfMatrixFieldOn U) : ℝ :=
  ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
    blockCoercivityConst a.lam a.Lam

def pathLinearConstR {U : Domain d} (a : CoeffOn U) : ℝ :=
  blockMatrixOfCoeffNormSqBound a.lam a.Lam * blockCoercivityConst a.lam a.Lam

def pathQuadConst {U : Domain d} (a : CoeffOn U) (h : LInfMatrixFieldOn U) : ℝ :=
  a.lam⁻¹ * pathLinearConstL a h

theorem pathLinearConstL_nonneg {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) : 0 ≤ pathLinearConstL a h := by
  unfold pathLinearConstL
  have := (blockCoercivityConst_pos (lam := a.lam) (Lam := a.Lam) a.lam_pos).le
  positivity

theorem pathLinearConstR_nonneg {U : Domain d} (a : CoeffOn U) :
    0 ≤ pathLinearConstR a := by
  unfold pathLinearConstR blockMatrixOfCoeffNormSqBound
  have hlam : 0 < a.lam := a.lam_pos
  have := (blockCoercivityConst_pos (lam := a.lam) (Lam := a.Lam) a.lam_pos).le
  positivity

theorem pathQuadConst_nonneg {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) : 0 ≤ pathQuadConst a h := by
  unfold pathQuadConst
  have hlam : 0 < a.lam := a.lam_pos
  have := pathLinearConstL_nonneg a h
  positivity

/-- The energy density is nonnegative wherever the coefficient is elliptic. -/
theorem blockEnergyDensityAt_nonneg {U : Domain d} (a : CoeffOn U)
    {x : Vec d} (hx : IsEllipticMatrix a.lam a.Lam (a.toCoeffField x))
    (Z : BlockVec d) : 0 ≤ blockEnergyDensityAt a Z x := by
  have h := blockQuadForm_nonneg hx Z
  change 0 ≤ (1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul (blockMatrixField a x) Z)
  rw [blockMatrixField_eq_blockMatrixOfCoeff]
  linarith

/-- **Young estimate for the bilinear response pairing.**  Both slots are
controlled by the doubled energy density, with a free positive parameter. -/
theorem abs_pathLinearPairingDensity_le {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (X Y : DoubledField d) {x : Vec d}
    (hx : IsEllipticMatrix a.lam a.Lam (a.toCoeffField x))
    (hb : ∀ i j : Fin d, |h.1 x i j| ≤ lInfEntryBound h)
    {η : ℝ} (hη : 0 < η) :
    |pathLinearPairingDensity a h.1 X Y x| ≤
      η * pathLinearConstL a h * blockEnergyDensityAt a (X.eval x) x
        + η⁻¹ * pathLinearConstR a * blockEnergyDensityAt a (Y.eval x) x := by
  set u : Vec d := matVecMul (h.1 x) (X.potential x) with hu
  set v : Vec d :=
    (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)).2 with hv
  have hdensity : pathLinearPairingDensity a h.1 X Y x = -vecDot u v := rfl
  -- Young's inequality for the Euclidean pairing
  have hc : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hcsq : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  have hcinv : (Real.sqrt η)⁻¹ ^ 2 = η⁻¹ := by rw [inv_pow, hcsq]
  have hkey := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    (Real.sqrt η) (Real.sqrt η)⁻¹ u v
  rw [mul_inv_cancel₀ hc.ne', one_mul, hcsq, hcinv] at hkey
  -- the two slot bounds
  have hQZ : 0 ≤ blockVecDot (X.eval x)
      (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) :=
    blockQuadForm_nonneg hx _
  have hQW : 0 ≤ blockVecDot (Y.eval x)
      (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)) :=
    blockQuadForm_nonneg hx _
  have hLeft : vecNormSq u ≤
      pathLinearConstL a h *
        blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := by
    have h1 : vecNormSq u ≤
        ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
          vecNormSq (X.eval x).1 :=
      vecNormSq_matVecMul_le_of_abs_apply_le hb (X.potential x)
    have h2 : vecNormSq (X.eval x).1 ≤ blockVecDot (X.eval x) (X.eval x) :=
      vecNormSq_fst_le_blockVecDot_self _
    have h3 := blockVecDot_self_le_blockQuadForm hx (X.eval x)
    have hdb : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2 := by positivity
    unfold pathLinearConstL
    calc
      vecNormSq u ≤ ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
          vecNormSq (X.eval x).1 := h1
      _ ≤ ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
          (blockCoercivityConst a.lam a.Lam *
            blockVecDot (X.eval x)
              (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x))
                (X.eval x))) := by
        exact mul_le_mul_of_nonneg_left (h2.trans h3) hdb
      _ = ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
            blockCoercivityConst a.lam a.Lam *
          blockVecDot (X.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := by
        ring
  have hRight : vecNormSq v ≤
      pathLinearConstR a *
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)) := by
    have h1 : vecNormSq v ≤
        blockVecDot (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x))
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)) :=
      vecNormSq_snd_le_blockVecDot_self _
    exact h1.trans (blockVecDot_image_self_le_blockQuadForm hx (Y.eval x))
  -- assemble
  have hEZ : blockEnergyDensityAt a (X.eval x) x =
      (1 / 2 : ℝ) * blockVecDot (X.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := rfl
  have hEW : blockEnergyDensityAt a (Y.eval x) x =
      (1 / 2 : ℝ) * blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)) := rfl
  rw [hdensity, abs_neg, hEZ, hEW]
  have hηinv : 0 < η⁻¹ := by positivity
  nlinarith [hkey, hLeft, hRight, hη.le, hηinv.le, hQZ, hQW]

/-- The quadratic response density is dominated by the energy density. -/
theorem pathQuadraticDensity_le {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (X : DoubledField d) {x : Vec d}
    (hx : IsEllipticMatrix a.lam a.Lam (a.toCoeffField x))
    (hb : ∀ i j : Fin d, |h.1 x i j| ≤ lInfEntryBound h) :
    pathQuadraticDensity a h.1 X x ≤
      pathQuadConst a h * blockEnergyDensityAt a (X.eval x) x := by
  set u : Vec d := matVecMul (h.1 x) (X.potential x) with hu
  have hlam : 0 < a.lam := a.lam_pos
  have hsInv : vecDot u (matVecMul (symmPart (a.toCoeffField x))⁻¹ u) ≤
      a.lam⁻¹ * vecNormSq u :=
    symmPart_inv_upperBound_of_isEllipticMatrix hx u
  have hLeft : vecNormSq u ≤
      pathLinearConstL a h *
        blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := by
    have h1 : vecNormSq u ≤
        ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) * vecNormSq (X.eval x).1 :=
      vecNormSq_matVecMul_le_of_abs_apply_le hb (X.potential x)
    have h2 : vecNormSq (X.eval x).1 ≤ blockVecDot (X.eval x) (X.eval x) :=
      vecNormSq_fst_le_blockVecDot_self _
    have h3 := blockVecDot_self_le_blockQuadForm hx (X.eval x)
    have hdb : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2 := by positivity
    unfold pathLinearConstL
    calc
      vecNormSq u ≤ ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
          vecNormSq (X.eval x).1 := h1
      _ ≤ ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
          (blockCoercivityConst a.lam a.Lam *
            blockVecDot (X.eval x)
              (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x))
                (X.eval x))) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hdb
      _ = ((d : ℝ) * (d : ℝ) * (lInfEntryBound h) ^ 2) *
            blockCoercivityConst a.lam a.Lam *
          blockVecDot (X.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := by
        ring
  have hdensity : pathQuadraticDensity a h.1 X x =
      (1 / 2 : ℝ) * vecDot u (matVecMul (symmPart (a.toCoeffField x))⁻¹ u) := rfl
  have hE : blockEnergyDensityAt a (X.eval x) x =
      (1 / 2 : ℝ) * blockVecDot (X.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := rfl
  have hlamInv : 0 < a.lam⁻¹ := by positivity
  rw [hdensity, hE]
  unfold pathQuadConst
  nlinarith [hsInv, hLeft, hlamInv.le, blockQuadForm_nonneg hx (X.eval x)]

/-! ## Averaged domination -/

/-- The doubled energy value of any doubled field is nonnegative. -/
theorem doubledMuValue_nonneg {U : Domain d} (a : CoeffOn U) (X : DoubledField d) :
    0 ≤ doubledMuValue U a X := by
  change 0 ≤ volumeAverage (U : Set (Vec d))
    (fun x => blockEnergyDensityAt a (X.eval x) x)
  unfold volumeAverage
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg_of_ae ?_
  filter_upwards [a.aeElliptic] with x hx
  exact blockEnergyDensityAt_nonneg a hx (X.eval x)

/-- Averaged Young estimate for the bilinear response pairing. -/
theorem abs_pathLinearPairing_le {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) {X Y : DoubledField d}
    (hXpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hXflux : MemVectorL2 (U : Set (Vec d)) X.flux)
    (hYpot : MemVectorL2 (U : Set (Vec d)) Y.potential)
    (hYflux : MemVectorL2 (U : Set (Vec d)) Y.flux)
    {η : ℝ} (hη : 0 < η) :
    |pathLinearPairing a h.1 X Y| ≤
      η * pathLinearConstL a h * doubledMuValue U a X
        + η⁻¹ * pathLinearConstR a * doubledMuValue U a Y := by
  have hf := integrableOn_pathLinearPairingDensity a h hXpot hYpot hYflux
  have hEX := integrableOn_blockEnergyDensity a hXpot hXflux
  have hEY := integrableOn_blockEnergyDensity a hYpot hYflux
  have hg : IntegrableOn
      (fun x => η * pathLinearConstL a h * blockEnergyDensityAt a (X.eval x) x
        + η⁻¹ * pathLinearConstR a * blockEnergyDensityAt a (Y.eval x) x)
      (U : Set (Vec d)) :=
    (hEX.const_mul _).add (hEY.const_mul _)
  have hbound := abs_volumeAverage_le hf hg ?_
  · calc
      |pathLinearPairing a h.1 X Y| ≤ volumeAverage (U : Set (Vec d))
          (fun x => η * pathLinearConstL a h * blockEnergyDensityAt a (X.eval x) x
            + η⁻¹ * pathLinearConstR a * blockEnergyDensityAt a (Y.eval x) x) :=
        hbound
      _ = η * pathLinearConstL a h * doubledMuValue U a X
            + η⁻¹ * pathLinearConstR a * doubledMuValue U a Y := by
        rw [show (fun x => η * pathLinearConstL a h *
              blockEnergyDensityAt a (X.eval x) x
            + η⁻¹ * pathLinearConstR a * blockEnergyDensityAt a (Y.eval x) x)
            = ((η * pathLinearConstL a h) •
                fun x => blockEnergyDensityAt a (X.eval x) x)
              + ((η⁻¹ * pathLinearConstR a) •
                fun x => blockEnergyDensityAt a (Y.eval x) x) from rfl,
          volumeAverage_add (hEX.smul (η * pathLinearConstL a h))
            (hEY.smul (η⁻¹ * pathLinearConstR a)),
          volumeAverage_smul, volumeAverage_smul]
        rfl
  · filter_upwards [a.aeElliptic, ae_forall_abs_apply_le_lInfEntryBound h]
      with x hx hb
    exact abs_pathLinearPairingDensity_le a h X Y hx hb hη

/-- Averaged domination of the quadratic response term. -/
theorem pathQuadraticTerm_le {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) {X : DoubledField d}
    (hXpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hXflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    pathQuadraticTerm a h.1 X ≤ pathQuadConst a h * doubledMuValue U a X := by
  have hf := integrableOn_pathQuadraticDensity a h hXpot
  have hEX := integrableOn_blockEnergyDensity a hXpot hXflux
  have hmono : volumeAverage (U : Set (Vec d)) (pathQuadraticDensity a h.1 X) ≤
      volumeAverage (U : Set (Vec d))
        (fun x => pathQuadConst a h * blockEnergyDensityAt a (X.eval x) x) := by
    refine volumeAverage_mono_ae hf (hEX.const_mul _) ?_
    filter_upwards [a.aeElliptic, ae_forall_abs_apply_le_lInfEntryBound h]
      with x hx hb
    exact pathQuadraticDensity_le a h X hx hb
  have hval : volumeAverage (U : Set (Vec d))
      (fun x => pathQuadConst a h * blockEnergyDensityAt a (X.eval x) x)
      = pathQuadConst a h * doubledMuValue U a X := by
    rw [show (fun x => pathQuadConst a h * blockEnergyDensityAt a (X.eval x) x)
        = (pathQuadConst a h) • fun x => blockEnergyDensityAt a (X.eval x) x from rfl,
      volumeAverage_smul]
    rfl
  rw [hval] at hmono
  exact hmono

/-- The linear response term is dominated by the doubled energy value. -/
theorem abs_pathLinearTerm_le {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) {X : DoubledField d}
    (hXpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hXflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    |pathLinearTerm a h.1 X| ≤
      (pathLinearConstL a h + pathLinearConstR a) * doubledMuValue U a X := by
  have h1 := abs_pathLinearPairing_le a h hXpot hXflux hXpot hXflux (η := 1)
    (by norm_num)
  rw [pathLinearTerm_eq_pairing]
  simpa using h1.trans_eq (by ring)

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
