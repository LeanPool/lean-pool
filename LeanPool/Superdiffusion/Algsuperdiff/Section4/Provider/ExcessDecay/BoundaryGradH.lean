/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryEnergyRebase
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryTransports

/-!
# BoundaryGradH

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two `∇h` conversions of the boundary Caccioppoli, and the `σ`-leg fork

The boundary Caccioppoli's data leg is CoarseGraining's `dirichletEnergyWith`,
whose second summand carries the **full** Besov norm of the transported
boundary gradient,

```text
  ‖∇h‖_{B^r} = √(|(∇h)_{□_{n+2}}|²) + [∇h]_{B^r} ,   h = h(· + c) ,
```

`c = wellPlacedCentre x m (n+2)`.

* **the seminorm half** — the same lemma read at `g := −∇h`, together with the
  `gagliardoKernel` negation congruence it needs to see that `[−∇h] = [∇h]`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2; `e.cg.RHS`, the Dirichlet
  energy display.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The `gagliardoKernel` negation congruence, on the datum -/

/-- **The Gagliardo `L²` datum does not see a sign.** -/
theorem memLp_gagliardoKernel_neg (A : Set (Vec d)) (s : ℝ) {F : Vec d → E}
    (h : MemLp (Gagliardo.gagliardoKernel s 2 F) 2
      (Support.normalizedGagliardoMeasureOn A)) :
    MemLp (Gagliardo.gagliardoKernel s 2 (fun y => -F y)) 2
      (Support.normalizedGagliardoMeasureOn A) := by
  have hneg : (fun y => -F y) = -F := rfl
  rw [hneg, Gagliardo.gagliardoKernel_neg]
  exact h.neg

/-! ## 2. The seminorm half of the `∇h` leg -/

/-- The transported datum-gradient Besov budget under covering-cube containment. -/
theorem besovVectorSeminormTwo_datumGrad_coveringCube_atWindow [NeZero d]
    {n m : ℤ} {x z : Vec d} {s : ℝ} {H : Vec d → Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hWcov : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => H (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s H).toReal) := by
  have hbase := besovVectorSeminormTwo_coveringCube_atWindow
    (g := fun y => -H y) hcov hs hs1 hL2.neg
    (memLp_gagliardoKernel_neg _ s hWcov) (memLp_gagliardoKernel_neg _ s hW)
  rw [normalizedGagliardoESeminormOn_neg] at hbase
  simpa only [neg_neg] using hbase

/-- **The transported boundary gradient's cube Besov seminorm, priced on the
anchor window.** -/
theorem besovVectorSeminormTwo_datumGrad_coveringCube_le_anchorWindow [NeZero d]
    {n m : ℤ} {x z : Vec d} {s : ℝ} {H : Vec d → Vec d} (hnm : n + 2 ≤ m)
    (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hWcov : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => H (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s H).toReal) := by
  exact besovVectorSeminormTwo_datumGrad_coveringCube_atWindow
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom) hs hs1 hL2 hWcov hW

/-! ## 3. The average half of the `∇h` leg -/

/-- The Euclidean length of a vector is at most `√d` times its ambient (sup)
norm. -/
theorem sqrt_vecNormSq_le_sqrt_dim_mul_norm (v : Vec d) :
    Real.sqrt (vecNormSq v) ≤ Real.sqrt (d : ℝ) * ‖v‖ := by
  have hcoord : ∀ i : Fin d, v i * v i ≤ ‖v‖ * ‖v‖ := by
    intro i
    have h1 : |v i| ≤ ‖v‖ := by
      have h := norm_le_pi_norm v i
      rwa [Real.norm_eq_abs] at h
    have h2 : (0 : ℝ) ≤ |v i| := abs_nonneg _
    have h3 : v i * v i = |v i| * |v i| := (abs_mul_abs_self (v i)).symm
    rw [h3]
    exact mul_le_mul h1 h1 h2 (norm_nonneg v)
  have hsum : vecNormSq v ≤ (d : ℝ) * (‖v‖ * ‖v‖) := by
    rw [vecNormSq, vecDot]
    calc ∑ i : Fin d, v i * v i ≤ ∑ _i : Fin d, ‖v‖ * ‖v‖ :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (‖v‖ * ‖v‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (vecNormSq v) ≤ Real.sqrt ((d : ℝ) * (‖v‖ * ‖v‖)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_mul_self (norm_nonneg v)]

/-- The transported gradient-average budget under covering-cube containment. -/
theorem sqrt_vecNormSq_cubeAverageVec_coveringCube_atWindow {n m : ℤ}
    {x z : Vec d} {H : Vec d → Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hL2W : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Real.sqrt (vecNormSq (cubeAverageVec (originCube d (n + 2))
        (fun y => H (y + wellPlacedCentre x m (n + 2))))) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
        (eLpNorm H 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  classical
  -- the hinge, and section 1's transport, taken before the abbreviations
  have hsubcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) := hcov
  have hmove : (eLpNorm H 2 (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal := by
    have hbase := eLpNorm_coveringCube_atWindow hcov H
    have hne : eLpNorm H 2 (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ := hL2W.eLpNorm_ne_top
    have hRHSne : ENNReal.ofReal ((3 : ℝ) ^ d) *
        eLpNorm H 2 (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne
    have hstep := ENNReal.toReal_mono hRHSne hbase
    rwa [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cov : Set (Vec d) :=
    (fun y => c + y) '' openCubeSet (originCube d (n + 2)) with hcovDef
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hWDef
  have hcovne : volume cov ≠ 0 :=
    volume_image_add_openCubeSet_ne_zero c (originCube d (n + 2))
  have hWne : volume W ≠ 0 := by
    intro h0
    exact hcovne (le_antisymm (h0 ▸ measure_mono hsubcov) zero_le)
  have hWtop : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_openCubeSet_ne_top (originCube d m))
      (measure_mono Set.inter_subset_right)
  have hL2cov : MemLp H 2 (Support.normalizedVolumeMeasureOn cov) :=
    memLp_normalizedVolumeMeasureOn_subset hsubcov hWne hWtop hcovne hL2W
  have hL2cube : MemLp (fun y => H (y + c)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) := by
    have h := memLp_normalizedVolumeMeasureOn_image_add (p := 2) (by norm_num)
      (by norm_num) hL2cov
    rwa [normalizedVolumeMeasureOn_openCubeSet] at h
  -- the vector Jensen step on the covering cube
  have hjen : ‖cubeAverageVec (originCube d (n + 2)) (fun y => H (y + c))‖ ≤
      (eLpNorm (fun y => H (y + c)) 2
        (normalizedCubeMeasure (originCube d (n + 2)))).toReal :=
    norm_cubeAverageVec_le_cubeLpNorm_two (originCube d (n + 2)) _ hL2cube
  -- the frame move
  have hframe : eLpNorm (fun y => H (y + c)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) =
      eLpNorm H 2 (Support.normalizedVolumeMeasureOn cov) := by
    rw [hcovDef, eLpNorm_normalizedVolumeMeasureOn_image_add c
      (openCubeSet (originCube d (n + 2))) (by norm_num) (by norm_num),
      normalizedVolumeMeasureOn_openCubeSet]
  have hsqrtd : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  calc Real.sqrt (vecNormSq (cubeAverageVec (originCube d (n + 2))
        (fun y => H (y + c))))
      ≤ Real.sqrt (d : ℝ) *
          ‖cubeAverageVec (originCube d (n + 2)) (fun y => H (y + c))‖ :=
        sqrt_vecNormSq_le_sqrt_dim_mul_norm _
    _ ≤ Real.sqrt (d : ℝ) *
          (eLpNorm (fun y => H (y + c)) 2
            (normalizedCubeMeasure (originCube d (n + 2)))).toReal :=
        mul_le_mul_of_nonneg_left hjen hsqrtd
    _ = Real.sqrt (d : ℝ) * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn cov)).toReal := by
        rw [hframe]
    _ ≤ Real.sqrt (d : ℝ) *
          ((3 : ℝ) ^ d * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn W)).toReal) :=
        mul_le_mul_of_nonneg_left hmove hsqrtd
    _ = Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
          (eLpNorm H 2 (Support.normalizedVolumeMeasureOn W)).toReal := by ring

/-- **The transported boundary gradient's cube average, priced on the anchor
window.** -/
theorem sqrt_vecNormSq_cubeAverageVec_coveringCube_le_anchorWindow {n m : ℤ}
    {x z : Vec d} {H : Vec d → Vec d} (hnm : n + 2 ≤ m)
    (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hL2W : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Real.sqrt (vecNormSq (cubeAverageVec (originCube d (n + 2))
        (fun y => H (y + wellPlacedCentre x m (n + 2))))) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
        (eLpNorm H 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  exact sqrt_vecNormSq_cubeAverageVec_coveringCube_atWindow
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom) hL2W

end

end Algsuperdiff.Section4.Provider.ExcessDecay
