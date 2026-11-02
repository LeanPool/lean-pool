/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseIndexBridges
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapWindow

/-!
# CoarseDirichletEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Dirichlet energy right-hand side at the pin `r = s/2`

Nothing here claims the anchor or any source node.

## What is proved

CoarseGraining's `dirichletEnergyWithRHSRHS` — the right-hand side of the
general-data energy estimate, which `BoundaryEnergyRebase` puts on the
covering cube — read at the fidelity plan's pin `r = s/2` and priced onto the
frozen clause's own legs:

```text
  dirichletEnergyWithRHSRHS C (□_{n+2}) ã (s/2) (−g(·+c)) v
      ≤ C (s/2)^{-3/2} √K √(σ_{n+3}^{-1}) · C_bg 3^{s(n+2)} C_gw [g]_{H^s(W')}
      + C (s/2)^{-1/2} √K √(σ_{n+3})
            · ( √d 3^d ‖∇h‖_{L²(W')} + C_bg 3^{s(n+2)} C_gw [∇h]_{H^s(W')} ) .
```

The three legs on the right are the frozen clause's own `[g]`, `‖∇h‖_{L²}` and
`[∇h]_{H^s}` legs, at the exact shapes the `CoarseAssemblyBudget` regrouping
consumes.

Ingredients, all proved:

* the two `q = 2` ellipticity caps at the pin's indices `s/2` and `s/4`
  (`CoarseIndexBridges.ae_coveringCubeRatioCap_le`);
* the positive-Besov index conversion `[·]_{s/2} → [·]_s`
  (`CoarseIndexBridges`; constant-free);
* the force window transport
  (`BoundaryTransports.besovVectorSeminormTwo_coveringCube_le_anchorWindow`);
* the two `∇h` conversions
  (`BoundaryGradH.besovVectorSeminormTwo_datumGrad_coveringCube_le_anchorWindow`
  and `...sqrt_vecNormSq_cubeAverageVec_coveringCube_le_anchorWindow`).

## References

* CoarseGraining, `dirichletEnergyWithRHSRHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The two capped ellipticity factors -/

/-- The lower ellipticity factor `λ^{-1/2}` from the `q = 2` ratio cap. -/
theorem rpow_neg_half_le_of_lower_cap {l sigma K : ℝ} (hl : 0 ≤ l)
    (hsigma : 0 < sigma) (hK : 0 ≤ K) (hcap : sigma * l⁻¹ ≤ K) :
    Real.rpow l (-(1 / 2 : ℝ)) ≤ Real.sqrt K * Real.sqrt sigma⁻¹ := by
  have hinv : l⁻¹ ≤ K * sigma⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hcap (inv_nonneg.mpr hsigma.le)
    rw [← mul_assoc, inv_mul_cancel₀ hsigma.ne', one_mul] at h
    calc l⁻¹ ≤ sigma⁻¹ * K := h
      _ = K * sigma⁻¹ := by ring
  have hid : Real.rpow l (-(1 / 2 : ℝ)) = Real.sqrt l⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_neg hl, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
  rw [hid, ← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt hinv

/-- The upper ellipticity factor `Λ^{1/2}` from the `q = 2` ratio cap. -/
theorem rpow_half_le_of_upper_cap {Lam sigma K : ℝ} (hLam : 0 ≤ Lam)
    (hsigma : 0 < sigma) (hcap : sigma⁻¹ * Lam ≤ K) :
    Real.rpow Lam (1 / 2 : ℝ) ≤ Real.sqrt K * Real.sqrt sigma := by
  have hle : Lam ≤ K * sigma := by
    have h := mul_le_mul_of_nonneg_left hcap hsigma.le
    rw [← mul_assoc, mul_inv_cancel₀ hsigma.ne', one_mul] at h
    calc Lam ≤ sigma * K := h
      _ = K * sigma := by ring
  have hKnn : 0 ≤ K := by
    by_contra hcon
    push Not at hcon
    have : K * sigma < 0 := mul_neg_of_neg_of_pos hcon hsigma
    linarith only [hLam, hle, this]
  rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hKnn]
  exact Real.sqrt_le_sqrt hle

/-! ## 2. The Dirichlet energy right-hand side, priced -/

/-- Dirichlet energy bound from covering-cube containment in the anchor window. -/
theorem dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow [NeZero d]
    {n m : ℤ} {x z c : Vec d} {s C₂ K sigma : ℝ} {g : Vec d → Vec d}
    {a : CoeffFamily d} (hcdef : c = wellPlacedCentre x m (n + 2))
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hs : 0 < s) (hs1 : s ≤ 1) (hC₂ : 0 ≤ C₂) (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hdat : H1Function (openCubeSet (originCube d m)))
    (v : DirichletForcedCubeSolution (originCube d (n + 2)) a
      (fun y => -g (y + c)))
    (hvgrad : ∀ y, v.boundaryData.grad y =
      hdat.grad (y + c))
    (hlam : sigma *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4)
        (Ch02.MultiscaleExponent.finite 2) a)⁻¹ ≤ K)
    (hLam : sigma⁻¹ *
      Ch02.LambdaSq (originCube d (n + 2)) (s / 2)
        (Ch02.MultiscaleExponent.finite 2) a ≤ K)
    (hgreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => -g (y + c)))
    (hhreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => hdat.grad (y + c)))
    (hgL2cov : MemLp g 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hgWcov : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))))
    (hhL2cov : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hhWcov : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hhW : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))))
    (hhL2W : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    dirichletEnergyWithRHSRHS C₂ (originCube d (n + 2)) a (s / 2)
        (fun y => -g (y + c)) v ≤
      C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma⁻¹) *
          (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
            (gagliardoWindowConst d *
              (Support.normalizedGagliardoESeminormOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))) s g).toReal)) +
        C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma) *
          (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
              (eLpNorm hdat.grad 2
                (Support.normalizedVolumeMeasureOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))))).toReal +
            besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
              (gagliardoWindowConst d *
                (Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) s hdat.grad).toReal)) := by
  classical
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  have hshalf : (0 : ℝ) < s / 2 := by linarith only [hs]
  -- the two ellipticity factors
  have hlamFactor : poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
      (Ch02.MultiscaleExponent.finite 2) ≤ Real.sqrt K * Real.sqrt sigma⁻¹ := by
    rw [poincareLowerEllipticityFactor, show s / 2 / 2 = s / 4 by ring]
    exact rpow_neg_half_le_of_lower_cap
      (Ch02.lambdaSq_nonneg (originCube d (n + 2)) a (by linarith only [hs])
        (by norm_num)) hsigma hK hlam
  have hLamFactor : poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
      (Ch02.MultiscaleExponent.finite 2) ≤ Real.sqrt K * Real.sqrt sigma := by
    rw [poincareUpperEllipticityFactor]
    exact rpow_half_le_of_upper_cap
      (Ch02.LambdaSq_nonneg (originCube d (n + 2)) a hshalf (by norm_num)) hsigma hLam
  -- the force leg: index conversion, then the window transport
  have hgIndex : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
      (fun y => -g (y + c)) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => -g (y + c)) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_le_of_exponent_le (originCube d (n + 2)) _
      (by linarith only [hs]) hgreg
  have hgTrans := besovVectorSeminormTwo_coveringCube_atWindow
    (x := x) (z := z) (g := g) hcov hs hs1 (hcdef ▸ hgL2cov)
    (hcdef ▸ hgWcov) hgW
  rw [← hcdef] at hgTrans
  have hgLeg : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
      (fun y => -g (y + c)) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn W s g).toReal) :=
    hgIndex.trans hgTrans
  -- the boundary-gradient leg
  have hbg : dirichletBoundaryGradientField v = fun y => hdat.grad (y + c) := by
    funext y
    rw [dirichletBoundaryGradientField, hvgrad y]
  have hhIndex : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
      (fun y => hdat.grad (y + c)) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => hdat.grad (y + c)) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_le_of_exponent_le (originCube d (n + 2)) _
      (by linarith only [hs]) hhreg
  have hhTrans := besovVectorSeminormTwo_datumGrad_coveringCube_atWindow
    (x := x) (z := z) (H := hdat.grad) hcov hs hs1 (hcdef ▸ hhL2cov)
    (hcdef ▸ hhWcov) hhW
  rw [← hcdef] at hhTrans
  have hhAvg := sqrt_vecNormSq_cubeAverageVec_coveringCube_atWindow
    (x := x) (z := z) (H := hdat.grad) hcov hhL2W
  rw [← hcdef] at hhAvg
  have hhNorm : scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
      (dirichletBoundaryGradientField v) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
          (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn W)).toReal +
        besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
          (gagliardoWindowConst d *
            (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal) := by
    rw [scaleNormalizedPositiveBesovVectorNormTwo, hbg]
    exact add_le_add hhAvg (hhIndex.trans hhTrans)
  -- assemble
  have hgLeg0 : (0 : ℝ) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
        (fun y => -g (y + c)) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_of_exponent_le hgreg (by linarith only [hs]))
  have hhNorm0 : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
      (dirichletBoundaryGradientField v) := by
    rw [scaleNormalizedPositiveBesovVectorNormTwo]
    refine add_nonneg (Real.sqrt_nonneg _) ?_
    rw [hbg]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_of_exponent_le hhreg (by linarith only [hs]))
  have hlow0 : (0 : ℝ) ≤ poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
      (Ch02.MultiscaleExponent.finite 2) := by
    rw [poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg (Ch02.lambdaSq_nonneg (originCube d (n + 2)) a (by linarith only [hs])
      (by norm_num)) _
  have hupp0 : (0 : ℝ) ≤ poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
      (Ch02.MultiscaleExponent.finite 2) := by
    rw [poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg (Ch02.LambdaSq_nonneg (originCube d (n + 2)) a hshalf (by norm_num)) _
  have hp32 : (0 : ℝ) ≤ Real.rpow (s / 2) (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hshalf.le _
  have hp12 : (0 : ℝ) ≤ Real.rpow (s / 2) (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hshalf.le _
  rw [dirichletEnergyWithRHSRHS]
  refine add_le_add ?_ ?_
  · have hstep : poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
          (Ch02.MultiscaleExponent.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
          (fun y => -g (y + c)) ≤
        (Real.sqrt K * Real.sqrt sigma⁻¹) *
          (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
            (gagliardoWindowConst d *
              (Support.normalizedGagliardoESeminormOn W s g).toReal)) :=
      mul_le_mul hlamFactor hgLeg hgLeg0
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
            (Ch02.MultiscaleExponent.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
            (fun y => -g (y + c))
        = (C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ))) *
            (poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
                (Ch02.MultiscaleExponent.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
                (fun y => -g (y + c))) := by ring
      _ ≤ (C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ))) *
            ((Real.sqrt K * Real.sqrt sigma⁻¹) *
              (besovGagliardoConstant d *
                Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
                (gagliardoWindowConst d *
                  (Support.normalizedGagliardoESeminormOn W s g).toReal))) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC₂ hp32)
      _ = C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
            (Real.sqrt K * Real.sqrt sigma⁻¹) *
            (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
              (gagliardoWindowConst d *
                (Support.normalizedGagliardoESeminormOn W s g).toReal)) := by ring
  · have hstep : poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
          (Ch02.MultiscaleExponent.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
          (dirichletBoundaryGradientField v) ≤
        (Real.sqrt K * Real.sqrt sigma) *
          (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
              (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn W)).toReal +
            besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
              (gagliardoWindowConst d *
                (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal)) :=
      mul_le_mul hLamFactor hhNorm hhNorm0
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
            (Ch02.MultiscaleExponent.finite 2) *
          scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
            (dirichletBoundaryGradientField v)
        = (C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ))) *
            (poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
                (Ch02.MultiscaleExponent.finite 2) *
              scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
                (dirichletBoundaryGradientField v)) := by ring
      _ ≤ (C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ))) *
            ((Real.sqrt K * Real.sqrt sigma) *
              (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
                  (eLpNorm hdat.grad 2
                    (Support.normalizedVolumeMeasureOn W)).toReal +
                besovGagliardoConstant d *
                  Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
                  (gagliardoWindowConst d *
                    (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal))) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC₂ hp12)
      _ = C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ)) *
            (Real.sqrt K * Real.sqrt sigma) *
            (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
                (eLpNorm hdat.grad 2
                  (Support.normalizedVolumeMeasureOn W)).toReal +
              besovGagliardoConstant d *
                Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
                (gagliardoWindowConst d *
                  (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal)) := by
          ring

/-- CoarseGraining's `dirichletEnergyWithRHSRHS` on the boundary covering
cube at the pin `r = s/2`, priced onto the frozen clause's three legs.

`hlam` and `hLam` are the two `q = 2` ratio caps of
`CoarseIndexBridges.ae_coveringCubeRatioCap_le` at the indices `s/4` and
`s/2`; `hvgrad` is the boundary-gradient identity carried by the produced
Dirichlet comparison of `BoundaryEnergyRebase`. -/
theorem dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs [NeZero d]
    {n m : ℤ} {x z c : Vec d} {s C₂ K sigma : ℝ} {g : Vec d → Vec d}
    {a : CoeffFamily d} (hcdef : c = wellPlacedCentre x m (n + 2))
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hs : 0 < s) (hs1 : s ≤ 1) (hC₂ : 0 ≤ C₂) (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hdat : H1Function (openCubeSet (originCube d m)))
    (v : DirichletForcedCubeSolution (originCube d (n + 2)) a
      (fun y => -g (y + c)))
    (hvgrad : ∀ y, v.boundaryData.grad y =
      hdat.grad (y + c))
    (hlam : sigma *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4)
        (Ch02.MultiscaleExponent.finite 2) a)⁻¹ ≤ K)
    (hLam : sigma⁻¹ *
      Ch02.LambdaSq (originCube d (n + 2)) (s / 2)
        (Ch02.MultiscaleExponent.finite 2) a ≤ K)
    (hgreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => -g (y + c)))
    (hhreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => hdat.grad (y + c)))
    (hgL2cov : MemLp g 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hgWcov : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))))
    (hhL2cov : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hhWcov : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hhW : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))))
    (hhL2W : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    dirichletEnergyWithRHSRHS C₂ (originCube d (n + 2)) a (s / 2)
        (fun y => -g (y + c)) v ≤
      C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma⁻¹) *
          (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
            (gagliardoWindowConst d *
              (Support.normalizedGagliardoESeminormOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))) s g).toReal)) +
        C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma) *
          (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
              (eLpNorm hdat.grad 2
                (Support.normalizedVolumeMeasureOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))))).toReal +
            besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
              (gagliardoWindowConst d *
                (Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) s hdat.grad).toReal)) := by
  exact dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow hcdef
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom)
    hs hs1 hC₂ hsigma hK hdat v hvgrad hlam hLam hgreg hhreg
    hgL2cov hgWcov hgW hhL2cov hhWcov hhW hhL2W

end

end Algsuperdiff.Section4.Provider.ExcessDecay
