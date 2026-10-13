/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCzGridGauge

/-!
# HomSpineCzGridDualTest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The banded dual test `G₀`, and its pairing: EXACT `ℓ^p`–`ℓ^{p'}` duality

## The test

`HomSpineCzGridGaugeBanded.GridDualTestFamilyBanded` asks, per cube `Q` (scale
`m`), order `s`, field `F` and truncation depth `N`, for ONE
`W^{s,p'}(Q) ∩ L²(Q)` field of full norm at most one whose normalized pairing
against `F` sees the truncated grid mass.  The witness is the multi-depth
grid-piecewise-constant aggregate

```text
  G₀(x) = Σ_{j ≤ N} Σ_{R ∈ D_j} 3^{s·p·(m-j)} · ‖(F)_R‖^{p-1} · e_R · 1_R(x),
```

where `(F)_R` is the cell average of `F` on `R` and `e_R` is a Euclidean unit
vector dual to `(F)_R` for the SUP norm this development gauge is built on:
`e_R = ±e_{i}` at a coordinate `i` realizing `‖(F)_R‖ = |(F)_R i|`
(`vecSupDual`).  Such an `e_R` has Euclidean magnitude `1` and satisfies
`⟨(F)_R, e_R⟩ = ‖(F)_R‖` exactly, which is what makes the duality below EXACT
rather than approximate.

## What this file proves

The single-depth pairing, EXACTLY:

```text
  ⟨F, G₀⟩_{L²(Q)}  =  (truncated grid mass of F at depth ≤ N)          (EXACT)
```

— the depth-`≤ N` truncated grid mass, on the nose.  The mechanism is a pure
cell decomposition: at depth `j` the cells `D_j` partition `Q` exactly (the
half-open `cubeSet` realization), so the depth-`j` slice of `G₀` is the
constant `3^{s·p·(m-j)}‖(F)_R‖^{p-1}e_R` on each `R`, and
`cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn` turns the cube
average of `⟨F, ·⟩` against it into the descendant average of
`3^{s·p·(m-j)}‖(F)_R‖^{p-1}⟨(F)_R, e_R⟩ = 3^{s·p·(m-j)}‖(F)_R‖^{p}`.  Summing
over `j ≤ N` reproduces `CoarseGraining`'s
`cubeEuclideanNegativeBesovDepthEnergy` term by term.  No inequality is spent
anywhere; `√d` is NOT spent here (the sup-norm duality is exact, and
`vecSupDual` is a Euclidean unit vector).

## What this file does NOT prove — the residual, stated exactly

Two norm bounds on the SAME `G₀` remain, both at `s₀ ≤ s`, `s·p' ≤ 1/2`, with
`P` the truncated grid mass above:

* the FLAT part
  `3^{-s·m}·‖G₀‖_{L^{p'}(Q)} ≤ (1-3^{-s·p})^{-1/p}·P^{1/p'}` — Hölder in the
  depth index against the geometric weights, whose pure-algebra core is a
  geometric-series bound over the depth bands; the rate `(1-3^{-s·p})^{-1/p}`
  is the one the geometric sum forces and cannot be improved;
* the GAGLIARDO part
  `[G₀]_{W^{s,p'}(Q)} ≤ C(d,p)·(1-3^{-s·p})^{-1/p}·P^{1/p'}` — the band-first
  boundary-layer estimate: a depth-`j` piecewise constant differs only across
  the depth-`j` skeleton; banding the double integral at `|x-y| ~ 3^{-k}·3^m`,
  the straddling-pair measure at band `k ≥ j` is `3^{j-k}`-small, giving the
  factor `3^{-(k-j)(1-s·p')} ≤ 3^{-(k-j)/2}` ON THE BAND, and the depths inside
  each band are summed before the bands are (Minkowski in the band index).

Given both, `G:= G₀/K` with `K = (1+C(d,p))·(1-3^{-s·p})^{-1/p}·P^{1/p'}` has
full norm at most one and realizes `GridDualTestFamilyBanded` at
`CA = (1+C(d,p))·(1-3^{-s₀·p})^{-1/p}` (monotone in `s₀ ≤ s`).  The `L²(Q)`
membership of `G₀` is free: it is bounded and takes finitely many values.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Elementary bilinearity of `vecDot` -/

theorem vecDot_smul_right (a u : Vec d) (c : ℝ) :
    vecDot a (c • u) = c * vecDot a u := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecDot_finset_sum {ι : Type*} (a : Vec d) (T : Finset ι) (w : ι → Vec d) :
    vecDot a (∑ R ∈ T, w R) = ∑ R ∈ T, vecDot a (w R) := by
  simp only [vecDot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

@[simp] theorem vecDot_zero_right (a : Vec d) : vecDot a (0 : Vec d) = 0 := by
  simp [vecDot]

/-! ## 2. The sup-norm dual unit vector

This repository's gauge is built on `‖(F)_R‖`, the SUP norm of the cell
average, while the admissible dual tests are measured in the EUCLIDEAN
magnitude.  The two are compatible in the direction needed here at NO cost: a
signed coordinate unit vector has Euclidean magnitude `1` and realizes the sup
norm exactly. -/

/-- **Existence of the dual unit vector.**  Every `a: Vec d` admits `u` of
Euclidean magnitude at most one with `⟨a, u⟩ = ‖a‖` (the sup norm).  For
`d = 0` the statement is `0 = 0`; otherwise `u` is a signed coordinate unit
vector at a coordinate realizing the maximum. -/
theorem exists_vecSupDual (a : Vec d) :
    ∃ u : Vec d, euclideanNorm u ≤ 1 ∧ vecDot a u = ‖a‖ := by
  classical
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨0, by simp, ?_⟩
    have ha : a = 0 := funext fun i => (hd.false i).elim
    rw [ha]
    simp
  · have := hd
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d))
      (fun i => |a i|) Finset.univ_nonempty
    have hnorm : ‖a‖ = |a i| := by
      refine le_antisymm ?_ ?_
      · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => ?_
        simpa only [Real.norm_eq_abs] using hi j (Finset.mem_univ j)
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i
    set c : ℝ := if 0 ≤ a i then (1 : ℝ) else -1 with hc
    have hcabs : |c| = 1 := by rw [hc]; split_ifs <;> norm_num
    have hns : vecNormSq (Pi.single i c : Vec d) = c * c := by
      show (∑ j, (Pi.single i c : Vec d) j * (Pi.single i c : Vec d) j) = c * c
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hdot : vecDot a (Pi.single i c : Vec d) = a i * c := by
      show (∑ j, a j * (Pi.single i c : Vec d) j) = a i * c
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    refine ⟨Pi.single i c, ?_, ?_⟩
    · rw [euclideanNorm, hns, Real.sqrt_mul_self_eq_abs, hcabs]
    · rw [hdot, hnorm, hc]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]

/-- The sup-norm dual unit vector of `a`, chosen once and for all. -/
def vecSupDual (a : Vec d) : Vec d := (exists_vecSupDual a).choose

theorem euclideanNorm_vecSupDual_le_one (a : Vec d) : euclideanNorm (vecSupDual a) ≤ 1 :=
  (exists_vecSupDual a).choose_spec.1

/-- **The exactness of the sup-norm duality.**  No constant is spent passing
from the sup-norm cell averages to a Euclidean unit dual test. -/
theorem vecDot_vecSupDual (a : Vec d) : vecDot a (vecSupDual a) = ‖a‖ :=
  (exists_vecSupDual a).choose_spec.2

/-! ## 3. The grid-piecewise-constant test -/

/-- The depth-`j` slice of the dual test: the piecewise constant taking the
value `v R` on each cell `R ∈ D_j` and `0` off `Q`. -/
def gridDualDepthTest (Q : TriadicCube d) (j : ℕ) (v : TriadicCube d → Vec d) :
    Vec d → Vec d :=
  fun x => ∑ R ∈ descendantsAtDepth Q j, (cubeSet R).indicator (fun _ => v R) x

/-- Off `Q` the depth slice vanishes; on a cell it is that cell's value. -/
theorem gridDualDepthTest_apply_of_mem {Q : TriadicCube d} {j : ℕ} {R : TriadicCube d}
    (v : TriadicCube d → Vec d) (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ cubeSet R) : gridDualDepthTest Q j v x = v R := by
  classical
  have hdisj : (↑(descendantsAtDepth Q j) : Set (TriadicCube d)).PairwiseDisjoint cubeSet :=
    pairwiseDisjoint_descendantsAtDepth Q j
  rw [gridDualDepthTest, Finset.sum_eq_single R]
  · exact Set.indicator_of_mem hx _
  · intro S hS hSR
    refine Set.indicator_of_notMem ?_ _
    intro hxS
    exact (Set.disjoint_left.mp
      (hdisj (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hR) hSR) hxS) hx
  · intro h
    exact absurd hR h

/-- The pointwise pairing of a field with the depth slice, as an indicator sum. -/
theorem vecDot_gridDualDepthTest (Q : TriadicCube d) (j : ℕ) (v : TriadicCube d → Vec d)
    (F : Vec d → Vec d) (x : Vec d) :
    vecDot (F x) (gridDualDepthTest Q j v x) =
      ∑ R ∈ descendantsAtDepth Q j,
        (cubeSet R).indicator (fun y => vecDot (F y) (v R)) x := by
  rw [gridDualDepthTest, vecDot_finset_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  by_cases hx : x ∈ cubeSet R
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, vecDot_zero_right]

/-- The coefficient of the dual test at depth `j` and cell `R`. -/
def gridDualTestCoeff (Q : TriadicCube d) (s t : ℝ) (F : Vec d → Vec d) (j : ℕ)
    (R : TriadicCube d) : Vec d :=
  ((3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
      ‖cubeAverageVec R F‖ ^ (t - 1)) • vecSupDual (cubeAverageVec R F)

/-! ## 4. Integrability of the components on the cube -/

/-- Each component of an `L²(Q)` field is integrable on `Q` for Lebesgue
measure.  (`normalizedCubeMeasure Q` is a positive finite rescaling of
`volume.restrict (cubeSet Q)`, and a probability measure carries `L² ⊆ L¹`.) -/
theorem integrableOn_component_cubeSet {Q : TriadicCube d}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) :
    IntegrableOn (fun x => F.toField x i) (cubeSet Q) volume := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hmem : MemLp (fun x => F.toField x i) 2 (normalizedCubeMeasure Q) := by
    simpa only [FiniteLpExponent.two_exponent, HilbertVec.ofVec, PiLp.toLp_apply] using
      F.euclideanMemLp.eval_piLp i
  have hint : Integrable (fun x => F.toField x i) (normalizedCubeMeasure Q) :=
    hmem.integrable one_le_two
  rw [normalizedCubeMeasure] at hint
  have hc0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have hfin := (MeasureTheory.integrable_smul_measure hc0 ENNReal.ofReal_ne_top).mp hint
  rwa [cubeMeasure] at hfin

/-- The pairing against a CONSTANT vector is integrable on the cube. -/
theorem integrableOn_vecDot_const {Q : TriadicCube d} (Fv : Vec d → Vec d) (w : Vec d)
    (hF : ∀ i : Fin d, IntegrableOn (fun x => Fv x i) (cubeSet Q) volume) :
    IntegrableOn (fun x => vecDot (Fv x) w) (cubeSet Q) volume := by
  simp only [vecDot]
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  exact (hF i).mul_const (w i)

/-- The cube average of the pairing against a constant vector is the pairing of
the cell average against that vector. -/
theorem cubeAverage_vecDot_const {Q : TriadicCube d} (Fv : Vec d → Vec d) (w : Vec d)
    (hF : ∀ i : Fin d, IntegrableOn (fun x => Fv x i) (cubeSet Q) volume) :
    cubeAverage Q (fun x => vecDot (Fv x) w) = vecDot (cubeAverageVec Q Fv) w := by
  have hsum : ∫ x in cubeSet Q, vecDot (Fv x) w ∂volume =
      ∑ i : Fin d, (∫ x in cubeSet Q, Fv x i ∂volume) * w i := by
    simp only [vecDot]
    rw [integral_finsetSum Finset.univ fun i _ => (hF i).mul_const (w i)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  show (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, vecDot (Fv x) w ∂volume = _
  rw [hsum]
  show _ = ∑ i : Fin d, cubeAverageVec Q Fv i * w i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    show (cubeVolume Q)⁻¹ * ((∫ x in cubeSet Q, Fv x i ∂volume) * w i) =
      ((cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, Fv x i ∂volume) * w i
    ring

/-- `descendantsAverage` reads its argument only on the depth family. -/
theorem descendantsAverage_congr (Q : TriadicCube d) (j : ℕ) {f g : TriadicCube d → ℝ}
    (h : ∀ R ∈ descendantsAtDepth Q j, f R = g R) :
    descendantsAverage Q j f = descendantsAverage Q j g := by
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, f R =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, g R
  rw [Finset.sum_congr rfl h]

/-! ## 5. The depth-slice pairing -/

/-- **The depth-`j` cell decomposition of the pairing.**  The cube average of
`⟨F, ·⟩` against the depth-`j` slice is the descendant average of the pairing
of the cell averages against the cell values. -/
theorem cubeAverage_vecDot_gridDualDepthTest (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeAverage Q (fun x => vecDot (F.toField x) (gridDualDepthTest Q j v x)) =
      descendantsAverage Q j (fun R => vecDot (cubeAverageVec R F.toField) (v R)) := by
  classical
  have hFi := fun i : Fin d => integrableOn_component_cubeSet F i
  /- integrability of the paired slice on `Q` -/
  have hint : IntegrableOn (fun x => vecDot (F.toField x) (gridDualDepthTest Q j v x))
      (cubeSet Q) volume := by
    have hrw : (fun x => vecDot (F.toField x) (gridDualDepthTest Q j v x)) =
        fun x => ∑ R ∈ descendantsAtDepth Q j,
          (cubeSet R).indicator (fun y => vecDot (F.toField y) (v R)) x := by
      funext x
      exact vecDot_gridDualDepthTest Q j v F.toField x
    rw [hrw]
    refine integrable_finsetSum (descendantsAtDepth Q j) fun R _ => ?_
    exact (integrableOn_vecDot_const F.toField (v R) hFi).indicator (measurableSet_cubeSet R)
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hint]
  refine descendantsAverage_congr Q j fun R hR => ?_
  have hcongr : ∀ x ∈ cubeSet R,
      vecDot (F.toField x) (gridDualDepthTest Q j v x) = vecDot (F.toField x) (v R) := by
    intro x hx
    rw [gridDualDepthTest_apply_of_mem v hR hx]
  have hset : ∫ x in cubeSet R, vecDot (F.toField x) (gridDualDepthTest Q j v x) ∂volume =
      ∫ x in cubeSet R, vecDot (F.toField x) (v R) ∂volume :=
    setIntegral_congr_fun (measurableSet_cubeSet R) hcongr
  have hFR : ∀ i : Fin d, IntegrableOn (fun x => (F.toField x) i) (cubeSet R) volume :=
    fun i => (hFi i).mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  show (cubeVolume R)⁻¹ *
      ∫ x in cubeSet R, vecDot (F.toField x) (gridDualDepthTest Q j v x) ∂volume = _
  rw [hset]
  exact cubeAverage_vecDot_const (Q := R) F.toField (v R) hFR

/-! ## 6. THE EXACT DUALITY -/

/-- `‖a‖^{t-1}·‖a‖ = ‖a‖^t` for every `t > 0`, including at `‖a‖ = 0`. -/
theorem rpow_sub_one_mul_self (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    x ^ (t - 1) * x = x ^ t := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0]
    rw [Real.zero_rpow (ne_of_gt ht), mul_zero]
  · have h1 : x ^ (t - 1) * x ^ (1 : ℝ) = x ^ (t - 1 + 1) :=
      (Real.rpow_add hx0 (t - 1) 1).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    congr 1
    ring

/-! ## 7. The `ℝ≥0∞` form: the truncated grid mass, on the nose -/

/-- Each depth energy of `CoarseGraining`'s running-scale negative Besov seminorm is the
`ENNReal.ofReal` of the corresponding real depth term of `§6`. -/
theorem depthEnergy_eq_ofReal (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    cubeEuclideanNegativeBesovDepthEnergy Q s p F j =
      ENNReal.ofReal
        ((3 : ℝ) ^ (s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
          descendantsAverage Q j
            (fun R => ‖cubeAverageVec R F.toField‖ ^ p.exponent.toReal)) := by
  classical
  have ht : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  set D : Finset (TriadicCube d) := descendantsAtDepth Q j with hD
  have hcardR : (0 : ℝ) < (D.card : ℝ) := descendantsAtDepth_card_pos Q j
  have hscale : descendantsAtScale Q (Q.scale - (j : ℤ)) = D := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q (by omega : Q.scale - (j : ℤ) ≤ Q.scale)]
    congr 1
    omega
  have hsum : (∑ R ∈ D, (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal) =
      ENNReal.ofReal (∑ R ∈ D, ‖cubeAverageVec R F.toField‖ ^ p.exponent.toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun R _ => Real.rpow_nonneg (norm_nonneg _) _]
    exact Finset.sum_congr rfl fun R _ =>
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ht.le
  have hcard : ((D.card : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((D.card : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hcardR, ENNReal.ofReal_natCast]
  rw [cubeEuclideanNegativeBesovDepthEnergy,
    Finset.sum_attach (descendantsAtScale Q (Q.scale - (j : ℤ)))
      (fun R => (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal),
    hscale, hsum, hcard, real_rpow_three_eq,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  show _ = (3 : ℝ) ^ (s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
    ((D.card : ℝ)⁻¹ * ∑ R ∈ D, ‖cubeAverageVec R F.toField‖ ^ p.exponent.toReal)
  ring

/-- The Hilbert realization is additive on finite sums (it is the identity on
the underlying pi type). -/
theorem ofVec_finset_sum {ι : Type*} (T : Finset ι) (w : ι → Vec d) :
    HilbertVec.ofVec (∑ j ∈ T, w j) = ∑ j ∈ T, HilbertVec.ofVec (w j) :=
  WithLp.toLp_sum 2 (Vec d) T w

/-- The normalized field pairing of `CoarseGraining` is the cube average of `⟨F, ·⟩`: the
bridge from `§6`–`§7` to `GridDualTestFamilyBanded`, once a `W^{s,p'} ∩ L²`
carrier for the test is available. -/
theorem cubeEuclideanNormalizedFieldPairing_eq_cubeAverage {Q : TriadicCube d}
    {s : FractionalOrder} {q : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s q) :
    cubeEuclideanNormalizedFieldPairing F G =
      cubeAverage Q (fun x => vecDot (F.toField x) (G.toField x)) :=
  (cubeAverage_eq_integral_normalizedCubeMeasure Q
    (fun x => vecDot (F.toField x) (G.toField x))).symm

end

end Algsuperdiff.Section4.Provider.Homogenization
