/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseBoundaryClause
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseDirichletEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorComposedArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorClause

/-!
# CoarseAssemblyBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary assembly's square root, its scaled `L²` object, and its

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

1. **§1 — the square root of the boundary Caccioppoli's display.**  The
   general-data boundary Caccioppoli of `CoarseAssemblyDatum` is a *squared*
   display; the assembly consumes its square root.  The step is pure real
   arithmetic and is stated on abstract letters so that no cube, measure or
   coefficient field enters.
2. The two `3`-powers cancel on the data-Poincaré leg, and the open scalar `S`
   survives at coefficient `3^{-(n+2)}` — which the frame division later turns
   into the pure constant `3^{-2}`, so **`S` carries no `3`-power in the final
   display**.

## The `s`-powers, in words

With the proved envelope's `s^{-4}` on the coarse-graining energy term
(`ReindexEllipticity.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree`)
and the `r = s/2` pin of the fidelity plan:

```text
  direct Dirichlet-energy ∇h leg     s^{-4} · (s/2)^{-1/2}                 = 2^{1/2} · s^{-9/2}
  direct Dirichlet-energy [g] leg    s^{-4} · (s/2)^{-3/2}                 = 2^{3/2} · s^{-11/2}
  datum pricing, crude leg           s^{-4} · s^{-1/2}                     = s^{-9/2}
  datum pricing, force leg           s^{-4} · (s/2)^{-3}                   = 2^3 · s^{-7}
  datum pricing → DirE [g] leg       s^{-4} · (s/2)^{-3/2} · (s/2)^{-3/2}  = 2^3 · s^{-7}
  datum pricing → DirE ∇h leg        s^{-4} · (s/2)^{-3/2} · (s/2)^{-1/2}  = 2^2 · s^{-6}
```

The frozen legs are `s^{-4}` (first), `s^{-7}` (force), `s^{-9/2}`
(`[∇h]` seminorm) and `s^{-9/2}` (`‖∇h‖_{L²}`).  The first five rows land; the
sixth does not, and §4 shows it cannot be made to.

## References

* ABK26, `l.coarse.grained.Caccioppoli` (move 3); the boundary application;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The square root of the boundary Caccioppoli display -/

/-- **The square root of the boundary Caccioppoli's squared display.**

```text
  3^d ( 2 · pref · (λ_t · 3^{-2(n+2)} · N²) + 2 · 18^d · DirE² );
```

the assembly consumes the square root of the left-hand side.  Stated on
abstract letters: `D3 = 3^d`, `P = pref`, `Lam = λ_t`, `T2 = 3^{-2(n+2)}`, `Nsq
= N²`, `E18 = 18^d`. -/
theorem sqrt_le_of_boundaryCaccioppoliDisplay {LCE D3 P Lam T2 Nsq E18 DirE : ℝ}
    (hD3 : 0 ≤ D3) (hP : 0 ≤ P) (hLam : 0 ≤ Lam) (hT2 : 0 ≤ T2)
    (hNsq : 0 ≤ Nsq) (hE18 : 0 ≤ E18) (hDirE : 0 ≤ DirE)
    (h : LCE ≤ D3 * (2 * (P * (Lam * T2 * Nsq)) + 2 * (E18 * DirE ^ (2 : ℕ)))) :
    Real.sqrt LCE ≤
      Real.sqrt (2 * D3 * (P * Lam)) * (Real.sqrt T2 * Real.sqrt Nsq) +
        Real.sqrt (2 * D3 * E18) * DirE := by
  have hc1 : (0 : ℝ) ≤ 2 * D3 * (P * Lam) :=
    mul_nonneg (mul_nonneg (by norm_num) hD3) (mul_nonneg hP hLam)
  have hc2 : (0 : ℝ) ≤ 2 * D3 * E18 :=
    mul_nonneg (mul_nonneg (by norm_num) hD3) hE18
  have hA : (0 : ℝ) ≤ 2 * D3 * (P * Lam) * (T2 * Nsq) :=
    mul_nonneg hc1 (mul_nonneg hT2 hNsq)
  have hB : (0 : ℝ) ≤ 2 * D3 * E18 * DirE ^ (2 : ℕ) :=
    mul_nonneg hc2 (pow_nonneg hDirE 2)
  have hrw : D3 * (2 * (P * (Lam * T2 * Nsq)) + 2 * (E18 * DirE ^ (2 : ℕ))) =
      2 * D3 * (P * Lam) * (T2 * Nsq) + 2 * D3 * E18 * DirE ^ (2 : ℕ) := by ring
  have h1 : Real.sqrt LCE ≤
      Real.sqrt (2 * D3 * (P * Lam) * (T2 * Nsq) + 2 * D3 * E18 * DirE ^ (2 : ℕ)) := by
    refine Real.sqrt_le_sqrt ?_
    rw [← hrw]
    exact h
  have hA' : Real.sqrt (2 * D3 * (P * Lam) * (T2 * Nsq)) =
      Real.sqrt (2 * D3 * (P * Lam)) * (Real.sqrt T2 * Real.sqrt Nsq) := by
    rw [Real.sqrt_mul hc1 (T2 * Nsq), Real.sqrt_mul hT2 Nsq]
  have hB' : Real.sqrt (2 * D3 * E18 * DirE ^ (2 : ℕ)) =
      Real.sqrt (2 * D3 * E18) * DirE := by
    rw [Real.sqrt_mul hc2 (DirE ^ (2 : ℕ)), Real.sqrt_sq hDirE]
  refine h1.trans ((sqrt_add_le_sqrt_add_sqrt hA hB).trans (le_of_eq ?_))
  rw [hA', hB']

/-- The covering cube's Besov scale weight is the frame factor `3^{-(n+2)}`. -/
theorem cubeBesovScaleWeight_one_originCube_eq (k : ℤ) :
    cubeBesovScaleWeight (1 : ℝ) (originCube d k) = Real.rpow (3 : ℝ) (-((k : ℤ) : ℝ)) :=
  cubeBesovScaleWeight_one_originCube k

/-- The frame factor cancels the covering cube's own diameter. -/
theorem rpow_three_neg_mul_zpow_self (k : ℤ) :
    Real.rpow (3 : ℝ) (-((k : ℤ) : ℝ)) * (3 : ℝ) ^ (k : ℤ) = 1 := by
  rw [← Real.rpow_intCast (3 : ℝ) k]
  exact rpow_three_neg_mul_self k

/-! ## 2. The scaled parent-`L²` object of the boundary Caccioppoli -/

theorem rpow_three_neg_mul_sqrt_coveringDifference_le_atWindow
    {n m : ℤ} {x z : Vec d} {S R : ℝ} {a : CoeffFamily d} {g : Vec d → Vec d}
    (hnm : n + 2 ≤ m)
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (u hdat : H1Function (openCubeSet (originCube d m)))
    (v : DirichletForcedCubeSolution (originCube d (n + 2)) a g)
    (utr : H1Function (openCubeSet (originCube d (n + 2))))
    (hutr : ∀ y, utr.toFun y = u.toFun (y + wellPlacedCentre x m (n + 2)))
    (hvdat : ∀ y, v.boundaryData.toFun y =
      hdat.toFun (y + wellPlacedCentre x m (n + 2)))
    (hXfin : eLpNorm (fun y => u.toFun y -
        volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hHfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hmean : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - hdat.toFun y)| ≤ S)
    (hGA1 : cubeBesovScaleWeight (1 : ℝ) (originCube d (n + 2)) *
        cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ≤ R) :
    Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
          (fun y => utr.toFun y - v.toH1.toFun y)) ≤
      Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          ((3 : ℝ) ^ d *
            (eLpNorm (fun y => u.toFun y -
                volumeAverage ((((fun y' => z + y') ''
                    openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))) u.toFun) 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal) +
        Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * S +
        unitMeanZeroPoincareConst d *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        R := by
  classical
  set w : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hbase := normalizedL2On_coveringDifference_le_meanControl_atWindow
    (x := x) (z := z) (S := S) (a := a) (g := g) hnm hcov u hdat v utr hutr hvdat
    hXfin hHfin hmean
  have hscaled := mul_le_mul_of_nonneg_left hbase hw0
  have hcancel : w * ((3 : ℝ) ^ (n + 2 : ℤ)) = 1 := rpow_three_neg_mul_zpow_self (n + 2)
  have hweight : cubeBesovScaleWeight (1 : ℝ) (originCube d (n + 2)) = w :=
    cubeBesovScaleWeight_one_originCube_eq (n + 2)
  rw [hweight] at hGA1
  have hexpand : w *
      ((3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal +
        S +
        unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2 : ℤ) *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y)) =
      w * ((3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal) +
        w * S +
        (w * (3 : ℝ) ^ (n + 2 : ℤ)) * (unitMeanZeroPoincareConst d *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal))) +
        w * cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by ring
  rw [hexpand, hcancel, one_mul] at hscaled
  have hlhs : w * normalizedL2On (openCubeSet (originCube d (n + 2)))
      (fun y => utr.toFun y - v.toH1.toFun y) =
      w * Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
        (fun y => utr.toFun y - v.toH1.toFun y)) := rfl
  have hstep : w * Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
      (fun y => utr.toFun y - v.toH1.toFun y)) ≤
      w * ((3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal) +
        w * S +
        unitMeanZeroPoincareConst d *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        w * cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := hscaled
  linarith only [hstep, hGA1]

/-! ## 4. The Dirichlet energy right-hand side, at the hinge -/



/-- **The parent-`L²` pricing, scaled by the covering cube's frame factor.**

Two readings of the conclusion matter for the assembly:

* the data-Poincaré leg loses its `3`-power entirely (`3^{-(n+2)} · 3^{n+2} =
  1`), so after the frame division it proves at the frozen leg's `3^n`;
* the open scalar `S` survives at coefficient `3^{-(n+2)}` and at coefficient
  `1` in `S` itself, so after the frame division it is `3`-power-free. -/
theorem rpow_three_neg_mul_sqrt_coveringDifference_le
    {n m : ℤ} {x z : Vec d} {S R : ℝ} {a : CoeffFamily d} {g : Vec d → Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (u hdat : H1Function (openCubeSet (originCube d m)))
    (v : DirichletForcedCubeSolution (originCube d (n + 2)) a g)
    (utr : H1Function (openCubeSet (originCube d (n + 2))))
    (hutr : ∀ y, utr.toFun y = u.toFun (y + wellPlacedCentre x m (n + 2)))
    (hvdat : ∀ y, v.boundaryData.toFun y =
      hdat.toFun (y + wellPlacedCentre x m (n + 2)))
    (hXfin : eLpNorm (fun y => u.toFun y -
        volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hHfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hmean : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - hdat.toFun y)| ≤ S)
    (hGA1 : cubeBesovScaleWeight (1 : ℝ) (originCube d (n + 2)) *
        cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ≤ R) :
    Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
          (fun y => utr.toFun y - v.toH1.toFun y)) ≤
      Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          ((3 : ℝ) ^ d *
            (eLpNorm (fun y => u.toFun y -
                volumeAverage ((((fun y' => z + y') ''
                    openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))) u.toFun) 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal) +
        Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * S +
        unitMeanZeroPoincareConst d *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        R := by
  exact rpow_three_neg_mul_sqrt_coveringDifference_le_atWindow hnm
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom)
    u hdat v utr hutr hvdat hXfin hHfin hmean hGA1
/-- Powers of a fixed positive base add. -/
theorem rpow_mul_rpow_of_add {b : ℝ} (hb : 0 < b) (p q r : ℝ) (hpq : p + q = r) :
    Real.rpow b p * Real.rpow b q = Real.rpow b r := by
  change b ^ p * b ^ q = b ^ r
  rw [← Real.rpow_add hb, hpq]

/-- The pin's half-argument, extracted: `(s/2)^e = 2^{-e} · s^e`. -/
theorem rpow_half_arg {s : ℝ} (hs : 0 ≤ s) (e : ℝ) :
    Real.rpow (s / 2) e = Real.rpow (2 : ℝ) (-e) * Real.rpow s e := by
  change (s / 2) ^ e = (2 : ℝ) ^ (-e) * s ^ e
  rw [show s / 2 = s * (2 : ℝ)⁻¹ by ring, Real.mul_rpow hs (by norm_num),
    Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  ring

theorem rpow_half_arg_neg {s : ℝ} (hs : 0 ≤ s) (e : ℝ) :
    Real.rpow (s / 2) (-e) = Real.rpow (2 : ℝ) e * Real.rpow s (-e) := by
  have h2 := rpow_half_arg hs (-e)
  rw [neg_neg] at h2
  exact h2

/-! ## 4. The refutation: the frozen `∇h` legs cannot hold row 6 -/


end

end Algsuperdiff.Section4.Provider.ExcessDecay
