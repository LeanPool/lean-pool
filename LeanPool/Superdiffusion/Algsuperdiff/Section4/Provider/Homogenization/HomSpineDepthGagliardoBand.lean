/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthFarBandSize
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormClause

/-!
# HomSpineDepthGagliardoBand

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The band factor of the single-depth Gagliardo half, and the pinned converse

## What this file is for

`HomSpineCzGridDepthTest` reduces the depth-`j` dual-converse to ONE named input:
a Gagliardo bound `[g_j]^{p'} ≤ Cg^{p'}·(depth energy)` for the depth-`j` slice
`g_j = gridDualDepthTest Q j (gridDualTestCoeff Q s p F j)`
(`depthEnergy_rpow_le_smoothDual_of_gagliardo`).  `HomSpineDepthFarBandSize` pins
the size of the band sums the input must carry.  This file

* names that input in the exact BAND SHAPE the reduction produces —
  `Cg^{p'} = C(d)·(nearBandGeometricConstant + Σ_{i<j} 3^{-i·s·p'})`
  (`GridDepthGagliardoBandInput`), with the dimensional factor `C(d)` a
  parameter, not a numeral: the reduction that would fix it is NOT proved here;
* converts the far sum into the closed `2·(s·p')⁻¹` bound uniformly in the
  depth (`gridDepthBandFactor_le_pin`, from `farBand_sum_le_geom` plus the
  elementary `(1-3^{-x})⁻¹ ≤ 2·x⁻¹` of `§1`);
* composes with the endpoint to the depth-`j` converse at the EXPLICIT
  constant `(1 + C(d)·(near + 2·x₀⁻¹))^{1/p'}` on the two-sided order pin
  `x₀ ≤ s·p' ≤ 1/2` (`§3`);
* discharges the consumption interface
  `NegativeBesovGridSmoothDualConverseAtDepth` at that constant and produces the
  SUP-FORM multiscale clause from it (`§4`).

## The two-sided pin is necessary, not a convenience

The depth-summed grid/smooth-dual converse fixes `CA` BEFORE the order `s`,
over the whole band `s·p' ≤ 1/2`.  The far half of the single-depth Gagliardo
seminorm is `≍ min(j, (s·p')⁻¹)` (`farBand_sum_le_geom` and its lower mate),
so it is unbounded as `s → 0` at fixed `p`: no finite `CA` can serve the whole
band through this route.  Every statement below therefore carries the LOWER pin
`x₀ ≤ s·p'` as an explicit hypothesis, and the constant is displayed as a
function of `x₀`.  At the Step-3 realization `s ≍ |log γ|⁻¹` with `p` FIXED at
`4d`, `x₀ ≍ |log γ|⁻¹` and the constant is `≍ |log γ|^{1/p'}`.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

/-! ## 1. The closed form of the far half at a fixed order

`farBand_sum_le_geom` bounds the far half by `(1-3^{-x})⁻¹`.  On the admissible
band `x ≤ 1/2` that geometric factor is at most `2·x⁻¹`, which is the shape the
downstream constant is displayed in. -/

/-- `1 < log 3`, from `e < 3`. -/
private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have h : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr h

/-- **The elementary lower bound on the geometric gap.**  On `0 < x ≤ 1/2`,
`1 - 3^{-x} ≥ x/2`.  (Proved from `1 + u ≤ exp u` alone; no series.) -/
theorem half_mul_le_one_sub_three_rpow_neg {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    x / 2 ≤ 1 - (3 : ℝ) ^ (-x) := by
  have hlog : (1 : ℝ) < Real.log 3 := one_lt_log_three
  set u : ℝ := x * Real.log 3 with hu
  have hupos : 0 < u := mul_pos hx0 (by linarith only [hlog])
  have h1u : (0 : ℝ) < 1 + u := by linarith only [hupos]
  have hexp : 1 + u ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    linarith only [this]
  have h3 : (3 : ℝ) ^ (-x) = (Real.exp u)⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_neg]
    congr 1
    rw [hu]
    ring
  have hinv : (Real.exp u)⁻¹ ≤ (1 + u)⁻¹ := inv_anti₀ h1u hexp
  have hux : x ≤ u := by
    have hstep : x * 1 ≤ x * Real.log 3 :=
      mul_le_mul_of_nonneg_left hlog.le hx0.le
    rw [hu]
    linarith only [hstep]
  have hxu : x * u ≤ u / 2 := by
    have hstep : x * u ≤ (1 / 2 : ℝ) * u :=
      mul_le_mul_of_nonneg_right hx hupos.le
    linarith only [hstep]
  have hprod : (1 : ℝ) ≤ (1 - x / 2) * (1 + u) := by
    have hexpand : (1 - x / 2) * (1 + u) = 1 + u - x / 2 - x * u / 2 := by ring
    rw [hexpand]
    linarith only [hxu, hux, hx0]
  have hle : (1 + u)⁻¹ ≤ 1 - x / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ h1u]
    linarith only [hprod]
  rw [h3]
  linarith only [hinv, hle]

/-- **The geometric factor in closed form.**  On the admissible band
`0 < x ≤ 1/2` (read `x = s·p'`), `(1-3^{-x})⁻¹ ≤ 2·x⁻¹`. -/
theorem one_sub_three_rpow_neg_inv_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    (1 - (3 : ℝ) ^ (-x))⁻¹ ≤ 2 * x⁻¹ := by
  have hhalf : x / 2 ≤ 1 - (3 : ℝ) ^ (-x) := half_mul_le_one_sub_three_rpow_neg hx0 hx
  have hpos : (0 : ℝ) < x / 2 := by linarith only [hx0]
  have hstep : (1 - (3 : ℝ) ^ (-x))⁻¹ ≤ (x / 2)⁻¹ := inv_anti₀ hpos hhalf
  have hval : (x / 2 : ℝ)⁻¹ = 2 * x⁻¹ := by
    rw [div_eq_mul_inv, mul_inv]
    norm_num
    ring
  rw [← hval]
  exact hstep

/-- **The far half, closed and depth-uniform.** -/
theorem farBand_sum_le_two_mul_inv {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) (j : ℕ) :
    (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ))) ≤ 2 * x⁻¹ :=
  le_trans (farBand_sum_le_geom hx0 j) (one_sub_three_rpow_neg_inv_le hx0 hx)

/-! ## 2. The band factor of the single-depth Gagliardo half

The factor the reduction of the Gagliardo double integral of a depth-`j`
piecewise constant produces: the NEAR bands (`k ≥ j`, straddling measure
`3^{j-k}`-small against the kernel gain `3^{(k-j)·s·p'}`) sum to
`nearBandGeometricConstant` by `sum_near_band_le`, and the FAR bands (`k < j`,
every pair straddling) sum to `Σ_{i<j} 3^{-i·s·p'}`.  Only the DIMENSIONAL
prefactor is left open here. -/

/-- The band factor `near + Σ_{i<j} 3^{-i x}` of the single-depth Gagliardo
half, at order weight `x = s·p'` and depth `j`. -/
def gridDepthBandFactor (x : ℝ) (j : ℕ) : ℝ :=
  nearBandGeometricConstant + ∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ))

theorem nearBandGeometricConstant_pos : 0 < nearBandGeometricConstant := by
  have hr0lt : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  rw [nearBandGeometricConstant]
  exact inv_pos.mpr (by linarith only [hr0lt])

theorem gridDepthBandFactor_nonneg (x : ℝ) (j : ℕ) : 0 ≤ gridDepthBandFactor x j := by
  refine add_nonneg nearBandGeometricConstant_pos.le (Finset.sum_nonneg fun i _ => ?_)
  exact Real.rpow_nonneg (by norm_num) _

/-- **The band factor is depth-uniform at a pinned order.**  Below `x` the far
half saturates, so the whole factor is at most `near + 2·x⁻¹`, for EVERY depth. -/
theorem gridDepthBandFactor_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) (j : ℕ) :
    gridDepthBandFactor x j ≤ nearBandGeometricConstant + 2 * x⁻¹ := by
  have h := farBand_sum_le_two_mul_inv hx0 hx j
  rw [gridDepthBandFactor]
  linarith only [h]

/-- The same bound read at a LOWER pin `x₀ ≤ x`: the displayed constant is
monotone in the pin, so one constant serves the whole pinned band. -/
theorem gridDepthBandFactor_le_pin {x₀ x : ℝ} (hx₀ : 0 < x₀) (hpin : x₀ ≤ x)
    (hx : x ≤ 1 / 2) (j : ℕ) :
    gridDepthBandFactor x j ≤ nearBandGeometricConstant + 2 * x₀⁻¹ := by
  have hx0 : 0 < x := lt_of_lt_of_le hx₀ hpin
  have hstep := gridDepthBandFactor_le hx0 hx j
  have hinv : x⁻¹ ≤ x₀⁻¹ := inv_anti₀ hx₀ hpin
  linarith only [hstep, hinv]

/-! ## 3. The named band input, and the pinned depth converse -/

/-- **THE GAGLIARDO BAND INPUT.**

For every cube, admissible order, field and depth: a `W^{s,p'}(Q) ∩ L²(Q)`
carrier FOR THE DEPTH SLICE ITSELF, together with the Gagliardo bound in band
form

```text
  [g_j]_{W^{s,p'}(Q)}^{p'}  ≤  C(d)·(near + Σ_{i<j} 3^{-i·s·p'})·(depth energy).
```

This is exactly the `hgag` slot plus the carrier `hGfield`, with the constant
spelled in the band shape `HomSpineDepthFarBandSize` pins two-sidedly.  THIS IS
A HYPOTHESIS: the reduction of the Gagliardo double integral of a depth-`j`
piecewise constant to the band sums is NOT proved in this repository (see this
file report; the missing steps are the straddling-pair measure bound at the
near bands and the tail-kernel integral at the far bands). -/
def GridDepthGagliardoBandInput (d : ℕ) (p : FiniteLpExponent) (Cd : ℝ≥0∞) : Prop :=
  ∀ (Q : TriadicCube d) (s : FractionalOrder),
    s.1 * p.conjugate.exponent.toReal ≤ 1 / 2 →
    ∀ (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ),
      ∃ G : CubeEuclideanWspL2Field Q s p.conjugate,
        G.toField =
            gridDualDepthTest Q j
              (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j) ∧
          cubeEuclideanWspESeminorm Q s p.conjugate
              (gridDualDepthTest Q j
                (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j))
              ^ p.conjugate.exponent.toReal ≤
            Cd *
                ENNReal.ofReal
                  (gridDepthBandFactor (s.1 * p.conjugate.exponent.toReal) j) *
              cubeEuclideanNegativeBesovDepthEnergy Q s p F j

/-- The DEPTH-EXACT constant delivered by the band input at order weight `x` and
depth `j`: `(1 + C(d)·(near + Σ_{i<j} 3^{-i x}))^{1/p'}`. -/
def gridDepthConverseConstAt (p : FiniteLpExponent) (Cd : ℝ≥0∞) (x : ℝ) (j : ℕ) : ℝ≥0∞ :=
  (1 + Cd * ENNReal.ofReal (gridDepthBandFactor x j)) ^ (p.conjugate.exponent.toReal)⁻¹

/-- The PINNED constant: depth-uniform and order-uniform on `x₀ ≤ s·p' ≤ 1/2`,
namely `(1 + C(d)·(near + 2·x₀⁻¹))^{1/p'}`. -/
def gridDepthConverseConst (p : FiniteLpExponent) (Cd : ℝ≥0∞) (x₀ : ℝ) : ℝ≥0∞ :=
  (1 + Cd * ENNReal.ofReal (nearBandGeometricConstant + 2 * x₀⁻¹)) ^
    (p.conjugate.exponent.toReal)⁻¹

theorem gridDepthConverseConst_ne_top {p : FiniteLpExponent} {Cd : ℝ≥0∞} (hCd : Cd ≠ ⊤)
    (x₀ : ℝ) : gridDepthConverseConst p Cd x₀ ≠ ⊤ := by
  refine ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top hCd ENNReal.ofReal_ne_top⟩

/-- The depth-exact constant is below the pinned one on the pinned band. -/
theorem gridDepthConverseConstAt_le {p : FiniteLpExponent} {Cd : ℝ≥0∞} {x₀ x : ℝ}
    (hx₀ : 0 < x₀) (hpin : x₀ ≤ x) (hx : x ≤ 1 / 2) (j : ℕ) :
    gridDepthConverseConstAt p Cd x j ≤ gridDepthConverseConst p Cd x₀ := by
  refine ENNReal.rpow_le_rpow ?_ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  refine add_le_add le_rfl (mul_le_mul' le_rfl ?_)
  exact ENNReal.ofReal_le_ofReal (gridDepthBandFactor_le_pin hx₀ hpin hx j)

/-- **THE DEPTH-EXACT CONVERSE.**  The band input, composed with the endpoint
`depthEnergy_rpow_le_smoothDual_of_gagliardo`, at the constant that displays the
band factor of the depth actually used — no pin needed, no depth uniformity
claimed. -/
theorem depthEnergy_rpow_le_smoothDual_of_bandInput {d : ℕ} {p : FiniteLpExponent}
    {Cd : ℝ≥0∞} (h : GridDepthGagliardoBandInput d p Cd) (Q : TriadicCube d)
    (s : FractionalOrder) (hband : s.1 * p.conjugate.exponent.toReal ≤ 1 / 2)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (p.exponent.toReal)⁻¹ ≤
      gridDepthConverseConstAt p Cd (s.1 * p.conjugate.exponent.toReal) j *
        cubeEuclideanNegativeWspSmoothDualENorm Q s p F := by
  obtain ⟨G, hGfield, hgag⟩ := h Q s hband F j
  set r : ℝ := p.conjugate.exponent.toReal with hrs
  have hr : 0 < r := finiteLpExponent_toReal_pos p.conjugate
  set A : ℝ≥0∞ :=
    Cd * ENNReal.ofReal (gridDepthBandFactor (s.1 * r) j) with hA
  have hpow : (A ^ r⁻¹) ^ r = A := ENNReal.rpow_inv_rpow hr.ne' A
  have hgag' : cubeEuclideanWspESeminorm Q s p.conjugate
        (gridDualDepthTest Q j
          (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j)) ^ r ≤
      (A ^ r⁻¹) ^ r * cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
    rw [hpow]
    exact hgag
  have hmain := depthEnergy_rpow_le_smoothDual_of_gagliardo Q s p F j (A ^ r⁻¹) G
    hGfield hgag'
  rw [hpow] at hmain
  exact hmain

/-- **THE PINNED DEPTH CONVERSE.**  On the two-sided order pin
`x₀ ≤ s·p' ≤ 1/2` the constant is uniform in the depth AND in the order:
`(1 + C(d)·(near + 2·x₀⁻¹))^{1/p'}`. -/
theorem depthEnergy_rpow_le_smoothDual_of_bandInput_pin {d : ℕ} {p : FiniteLpExponent}
    {Cd : ℝ≥0∞} {x₀ : ℝ} (hx₀ : 0 < x₀) (h : GridDepthGagliardoBandInput d p Cd)
    (Q : TriadicCube d) (s : FractionalOrder)
    (hpin : x₀ ≤ s.1 * p.conjugate.exponent.toReal)
    (hband : s.1 * p.conjugate.exponent.toReal ≤ 1 / 2)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (p.exponent.toReal)⁻¹ ≤
      gridDepthConverseConst p Cd x₀ * cubeEuclideanNegativeWspSmoothDualENorm Q s p F := by
  refine le_trans (depthEnergy_rpow_le_smoothDual_of_bandInput h Q s hband F j) ?_
  exact mul_le_mul' (gridDepthConverseConstAt_le hx₀ hpin hband j) le_rfl

/-! ## 4. The consumption interface, and the sup-form clause

The depth-wise converse of `HomSpineCzGridDepthTest` fixes
one constant before the order, over the whole band `s·p' ≤ 1/2`; the far half
is `≍ (s·p')⁻¹` there, so that shape is out of reach of this route and is NOT
claimed.  The pinned predicate below is what the Step-3 realization actually
needs, and it discharges the interface verbatim. -/

/-- The two-sided order pin, as the predicate the clause producer takes. -/
def DepthBandPin (p : FiniteLpExponent) (x₀ : ℝ) (s : FractionalOrder) : Prop :=
  x₀ ≤ s.1 * p.conjugate.exponent.toReal ∧
    s.1 * p.conjugate.exponent.toReal ≤ 1 / 2

/-- **the CONSUMPTION INTERFACE, DISCHARGED** at the explicit pinned
constant. -/
theorem negativeBesovGridSmoothDualConverseAtDepth_of_bandInput {d : ℕ}
    {p : FiniteLpExponent} {Cd : ℝ≥0∞} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (h : GridDepthGagliardoBandInput d p Cd) (Q : TriadicCube d) (s : FractionalOrder)
    (hpin : DepthBandPin p x₀ s) (j : ℕ) :
    NegativeBesovGridSmoothDualConverseAtDepth Q s p j (gridDepthConverseConst p Cd x₀) := by
  intro F
  simpa [one_div] using
    depthEnergy_rpow_le_smoothDual_of_bandInput_pin hx₀ h Q s hpin.1 hpin.2 F j

/-- The producer's hypothesis, in its exact shape: the depth converse on every
origin cube, every depth and every pinned order. -/
theorem depthConverseOn_of_bandInput {d : ℕ} {p : FiniteLpExponent} {Cd : ℝ≥0∞}
    {x₀ : ℝ} (hx₀ : 0 < x₀) (h : GridDepthGagliardoBandInput d p Cd) :
    ∀ (m : ℤ) (j : ℕ) (s : FractionalOrder), DepthBandPin p x₀ s →
      NegativeBesovGridSmoothDualConverseAtDepth (originCube d m) s p j
        (gridDepthConverseConst p Cd x₀) :=
  fun m j s hpin =>
    negativeBesovGridSmoothDualConverseAtDepth_of_bandInput hx₀ h (originCube d m) s hpin j

end

end Algsuperdiff.Section4.Provider.Homogenization
