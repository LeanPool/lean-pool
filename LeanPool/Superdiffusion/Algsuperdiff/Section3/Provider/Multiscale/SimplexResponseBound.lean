/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SimplexDissection
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.CrudeResponseBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.SubadditivityCountable

/-!
# SimplexResponseBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The crude response bounds at the manuscript's simplex carrier

All three steps are carried out (the decomposition itself is
`SimplexDissection.lean`), so ABK26's application of the crude response
bounds/6348 at `square = spx` a **simplex** is available at the printed
carrier, with an explicit constant.

## The estimate

Let `T` be a Kuhn cell (`e.simplex.def`) whose support cube is a triadic
descendant of `Q` at scale `k`, and let `{R_i}` be the triadic Whitney
dissection of the open simplex.  Then

```
J(T, p, 0; a) <= C(d,s) . 3^{2 s (Q.scale - k)} . Lambda_{s,q}(Q; a) . |p|^2 ,
J(T, 0, q; a) <= C(d,s) . 3^{2 s (Q.scale - k)} . lambda^{-1}_{s,q}(Q; a) . |q|^2 ,
```

with the explicit `d`- and `s`-only constant

```
C(d,s) = simplexCrudeConst d s = 6 d (d+1) / (1 - 3^{2s-1}) ,
```

finite exactly on the window `s < 1/2`; at the manuscript's `s =
1/4` it is `6 d (d+1) / (1 - 3^{-1/2}) < 15 d (d+1)`.

## The boundary estimate

The identified route describes the second ingredient as a boundary count.  What is proved
here is the equivalent *convex-collar* estimate, which needs no enumeration of
the `d+1` faces of the simplex:

* the open simplex `U` contains an explicit `sup`-ball `B(c, rho)` with
  `rho = 3^{scale} / (2(d+1))` (`ball_simplexIncenter_subset_openCarrier`);
* hence for `0 < lam <= 1` every point of the homothetic copy
  `c + (1-lam)(U - c)` has its whole `lam rho`-ball inside `U`
  (`ball_subset_of_mem_shrinkToward`), and that copy has volume `(1-lam)^d |U|`;
* a selected cube at depth `t` has a triadic parent that meets the complement of
  `U` and has diameter `3 . 3^{scale-t}`, so the cube misses the homothetic copy
  at `lam = 12 (d+1) 3^{-t}`;
* the selected cubes at depth `t` being disjoint, their total volume is at most
  `(1 - (1-lam)^d) |U| <= d lam |U| = 12 d (d+1) 3^{-t} |U|`
  (`sum_cubeVolume_simplexDissection_le`).

Summing the weights gives `sum_i (|R_i|/|T|) 3^{2 s t_i} <= 12 d (d+1) / (1 -
3^{2s-1})` (`tsum_cubeVolume_weight_le`), convergent exactly on that
window.

## Main results

* `responseJ_simplexDomain_zero_flux_le_LambdaSq`,
  `responseJ_simplexDomain_zero_slope_le_lambdaSq_inv` — **the crude response
  bounds at the simplex carrier**, for `0 < s < 1/2` and any admissible
  exponent.

## References

* ABK26, `p.bfA.multiscalebound`, Step 1, `l.subadd.betterer`, `e.simplex.def`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Provider.Whitney
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Homothetic shrinking of a convex set -/

/-- The homothetic copy `c + (1 - lam)(U - c)` of `U`. -/
def shrinkToward (c : Vec d) (lam : ℝ) (U : Set (Vec d)) : Set (Vec d) :=
  AffineMap.homothety c (1 - lam) '' U

theorem volume_shrinkToward (c : Vec d) {lam : ℝ} (hlam : lam ≤ 1) (U : Set (Vec d)) :
    volume (shrinkToward c lam U) = ENNReal.ofReal ((1 - lam) ^ d) * volume U := by
  have hnn : (0 : ℝ) ≤ (1 - lam) ^ d := pow_nonneg (by linarith) d
  rw [shrinkToward, MeasureTheory.Measure.addHaar_image_homothety,
    show Module.finrank ℝ (Vec d) = d from Module.finrank_fin_fun ℝ, abs_of_nonneg hnn]

theorem shrinkToward_subset {U : Set (Vec d)} (hU : Convex ℝ U) {c : Vec d} (hc : c ∈ U)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) : shrinkToward c lam U ⊆ U := by
  rintro _ ⟨y, hy, rfl⟩
  have hcomb : AffineMap.homothety c (1 - lam) y = (1 - lam) • y + lam • c := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub]
    module
  rw [hcomb]
  exact hU hy hc (by linarith) hlam0 (by ring)

/-- **The interior distance of the homothetic copy.**  If `B(c, rho) ⊆ U` and `U`
is convex, every point of `c + (1 - lam)(U - c)` has its whole `lam rho`-ball
inside `U`. -/
theorem ball_subset_of_mem_shrinkToward {U : Set (Vec d)} (hU : Convex ℝ U) {c : Vec d}
    {rho lam : ℝ} (hball : Metric.ball c rho ⊆ U) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    {x : Vec d} (hx : x ∈ shrinkToward c lam U) : Metric.ball x (lam * rho) ⊆ U := by
  obtain ⟨y, hy, rfl⟩ := hx
  intro z hz
  have hlamne : lam ≠ 0 := ne_of_gt hlam0
  have hvnorm : ‖z - AffineMap.homothety c (1 - lam) y‖ < lam * rho := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.1 hz
  have hwball : c + lam⁻¹ • (z - AffineMap.homothety c (1 - lam) y) ∈ Metric.ball c rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : c + lam⁻¹ • (z - AffineMap.homothety c (1 - lam) y) - c =
        lam⁻¹ • (z - AffineMap.homothety c (1 - lam) y) := by
      module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hlam0), inv_mul_eq_div,
      div_lt_iff₀ hlam0]
    calc ‖z - AffineMap.homothety c (1 - lam) y‖ < lam * rho := hvnorm
      _ = rho * lam := by ring
  have hcomb : (1 - lam) • y +
      lam • (c + lam⁻¹ • (z - AffineMap.homothety c (1 - lam) y)) = z := by
    rw [smul_add, smul_inv_smul₀ hlamne]
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub]
    module
  rw [← hcomb]
  exact hU hy (hball hwball) (by linarith) hlam0.le (by ring)

/-! ## Total volume of a disjoint family inside a set -/

private theorem dist_le_cubeScaleFactor {C : TriadicCube d} {x y : Vec d}
    (hx : x ∈ cubeSet C) (hy : y ∈ cubeSet C) : dist x y ≤ cubeScaleFactor C := by
  have hx' : dist x (cubeCenter C) ≤ cubeRadius C :=
    Metric.mem_closedBall.1 (cubeSet_subset_closedBall C hx)
  have hy' : dist (cubeCenter C) y ≤ cubeRadius C := by
    rw [dist_comm]
    exact Metric.mem_closedBall.1 (cubeSet_subset_closedBall C hy)
  have htri := dist_triangle x (cubeCenter C) y
  have hfac := cubeScaleFactor_eq_two_mul_cubeRadius C
  linarith

/-- Disjoint triadic cubes inside `U`, together with any set `V ⊆ U` they all
avoid, use up at most the volume of `U`. -/
theorem sum_cubeVolume_add_le_of_disjoint {U V : Set (Vec d)} (hUtop : volume U ≠ ⊤)
    (hVU : V ⊆ U) {F : Finset (TriadicCube d)}
    (hsub : ∀ R ∈ F, cubeSet R ⊆ U)
    (hdisj : (F : Set (TriadicCube d)).PairwiseDisjoint cubeSet)
    (hV : ∀ R ∈ F, Disjoint (cubeSet R) V) :
    (∑ R ∈ F, cubeVolume R) + (volume V).toReal ≤ (volume U).toReal := by
  classical
  have hmeas : ∀ R ∈ F, MeasurableSet (cubeSet R) := fun R _ => measurableSet_cubeSet R
  have hAmeas : MeasurableSet (⋃ R ∈ F, cubeSet R) := Finset.measurableSet_biUnion F hmeas
  have hAU : (⋃ R ∈ F, cubeSet R) ⊆ U := Set.iUnion₂_subset hsub
  have hdisjVA : Disjoint V (⋃ R ∈ F, cubeSet R) := by
    rw [Set.disjoint_iUnion₂_right]
    exact fun R hR => (hV R hR).symm
  have hunion : volume (V ∪ ⋃ R ∈ F, cubeSet R) = volume V + volume (⋃ R ∈ F, cubeSet R) :=
    measure_union hdisjVA hAmeas
  have hle : volume V + volume (⋃ R ∈ F, cubeSet R) ≤ volume U := by
    rw [← hunion]
    exact measure_mono (Set.union_subset hVU hAU)
  have hAvol : volume (⋃ R ∈ F, cubeSet R) = ∑ R ∈ F, volume (cubeSet R) :=
    measure_biUnion_finset hdisj hmeas
  have hVtop : volume V ≠ ⊤ := ne_top_of_le_ne_top hUtop (measure_mono hVU)
  have hAtop : volume (⋃ R ∈ F, cubeSet R) ≠ ⊤ := ne_top_of_le_ne_top hUtop (measure_mono hAU)
  have hreal := ENNReal.toReal_mono hUtop hle
  rw [ENNReal.toReal_add hVtop hAtop, hAvol] at hreal
  have hsum : (∑ R ∈ F, volume (cubeSet R)).toReal = ∑ R ∈ F, cubeVolume R := by
    rw [ENNReal.toReal_sum fun R _ => (volume_cubeSet_lt_top R).ne]
    exact Finset.sum_congr rfl fun R _ => volume_cubeSet_toReal R
  rw [hsum] at hreal
  linarith

/-! ## The depth-`t` volume bound for the simplex dissection -/

/-- **The boundary estimate of the identified route.**  The cubes of the triadic Whitney
dissection of an open Kuhn simplex that sit at depth `t` below the support cube
have total volume at most `12 d (d+1) 3^{-t}` times the volume of the simplex.

The proof is the convex-collar bound: at `lam = 12 (d+1) 3^{-t}` the homothetic
copy of the simplex is farther from the complement than the diameter of a
depth-`(t-1)` cube, while a selected cube's triadic parent meets the
complement. -/
theorem sum_cubeVolume_simplexDissection_le [NeZero d] (T : KuhnCell d) (t : ℕ)
    {F : Finset (TriadicCube d)} (hF : ∀ R ∈ F, R ∈ simplexDissection T)
    (hFt : ∀ R ∈ F, R ∈ descendantsAtDepth T.supportCube t) :
    (∑ R ∈ F, cubeVolume R) ≤
      12 * (d : ℝ) * ((d : ℝ) + 1) / (3 : ℝ) ^ t * (volume T.openCarrier).toReal := by
  classical
  have hsfpos : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hdpos : (1 : ℝ) ≤ (d : ℝ) := by
    have h : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    exact_mod_cast h
  have h3t : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hUtop : volume T.openCarrier ≠ ⊤ := (isBoundedDomain_openCarrier T).volume_lt_top.ne
  have hUpos : (0 : ℝ) < (volume T.openCarrier).toReal := by
    have h1 : 0 < volume T.openCarrier :=
      (isOpen_openCarrier T).measure_pos volume (openCarrier_nonempty T)
    exact ENNReal.toReal_pos h1.ne' hUtop
  have hconv : Convex ℝ T.openCarrier := convex_openCarrier T
  have hball : Metric.ball (simplexIncenter T) (simplexInradius T) ⊆ T.openCarrier :=
    ball_simplexIncenter_subset_openCarrier T
  have hsubU : ∀ R ∈ F, cubeSet R ⊆ T.openCarrier := fun R hR =>
    cubeSet_subset_openCarrier_of_mem_simplexDissection (hF R hR)
  have hdisjF : (F : Set (TriadicCube d)).PairwiseDisjoint cubeSet :=
    (pairwiseDisjoint_simplexDissection T).subset fun R hR => hF R (Finset.mem_coe.1 hR)
  -- the triadic parent of a selected cube meets the complement of the simplex
  have hparent : ∀ R ∈ F, ∃ y, y ∉ T.openCarrier ∧
      ∀ x ∈ cubeSet R, dist x y ≤ 3 * (cubeScaleFactor T.supportCube / (3 : ℝ) ^ t) := by
    intro R hR
    have hRsel := hF R hR
    have hRt := hFt R hR
    obtain ⟨y, hyC, hyU⟩ : ∃ y, y ∈ cubeSet (parentCube R) ∧ y ∉ T.openCarrier := by
      by_contra hcon
      push Not at hcon
      exact hRsel.2.2 fun z hz => hcon z hz
    have hone : 1 ≤ t := one_le_depth_of_mem_whitneyInnerCubes
      (not_cubeSet_supportCube_subset_openCarrier T) hRsel hRt
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨C, hC, hRC⟩ := mem_descendantsAtDepth_succ_iff.mp hRt
    obtain ⟨digits, hdig⟩ := mem_childCubes_iff.mp hRC
    have hpar : parentCube R = C := by rw [hdig]; exact childCube_parent C digits
    have hRsub : cubeSet R ⊆ cubeSet C := cubeSet_subset_of_mem_childCubes hRC
    have hCfac : cubeScaleFactor C = cubeScaleFactor T.supportCube / (3 : ℝ) ^ t' :=
      cubeScaleFactor_descendant_eq_div_pow hC
    refine ⟨y, hyU, fun x hx => ?_⟩
    have hd := dist_le_cubeScaleFactor (hRsub hx) (hpar ▸ hyC)
    rw [hCfac] at hd
    have h3t' : (0 : ℝ) < (3 : ℝ) ^ t' := by positivity
    have hpow : (3 : ℝ) ^ (t' + 1) = 3 * (3 : ℝ) ^ t' := by ring
    rw [hpow]
    refine hd.trans (le_of_eq ?_)
    field_simp
  by_cases hcase : 12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t ≤ 1
  · -- the collar case
    have hlam0 : (0 : ℝ) < 12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t := by positivity
    have hlamrho : 12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t * simplexInradius T =
        6 * (cubeScaleFactor T.supportCube / (3 : ℝ) ^ t) := by
      rw [simplexInradius]
      have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hVdisj : ∀ R ∈ F, Disjoint (cubeSet R)
        (shrinkToward (simplexIncenter T) (12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t) T.openCarrier) := by
      intro R hR
      obtain ⟨y, hyU, hy⟩ := hparent R hR
      rw [Set.disjoint_right]
      intro x hxs hxR
      have hbx := ball_subset_of_mem_shrinkToward hconv hball hlam0 hcase hxs
      refine hyU (hbx ?_)
      rw [Metric.mem_ball, dist_comm, hlamrho]
      have hxy := hy x hxR
      have hq : (0 : ℝ) < cubeScaleFactor T.supportCube / (3 : ℝ) ^ t := by positivity
      linarith
    have hVsub : shrinkToward (simplexIncenter T) (12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t)
        T.openCarrier ⊆ T.openCarrier :=
      shrinkToward_subset hconv (simplexIncenter_mem_openCarrier T) hlam0.le hcase
    have hmain := sum_cubeVolume_add_le_of_disjoint hUtop hVsub hsubU hdisjF hVdisj
    have hvol : (volume (shrinkToward (simplexIncenter T)
        (12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t) T.openCarrier)).toReal =
        (1 - 12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t) ^ d * (volume T.openCarrier).toReal := by
      rw [volume_shrinkToward _ hcase, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg (by linarith) d)]
    rw [hvol] at hmain
    have hbern : 1 - (d : ℝ) * (12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t) ≤
        (1 - 12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t) ^ d := by
      have h := one_add_mul_le_pow (a := -(12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t)) (by linarith) d
      simpa [sub_eq_add_neg] using h
    have hfinal : (∑ R ∈ F, cubeVolume R) ≤
        (d : ℝ) * (12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t) * (volume T.openCarrier).toReal := by
      nlinarith [hUpos, hmain, hbern]
    refine hfinal.trans (le_of_eq ?_)
    field_simp
  · -- the shallow case: the stated bound already exceeds the total volume
    push Not at hcase
    have hV : ∀ R ∈ F, Disjoint (cubeSet R) (∅ : Set (Vec d)) := fun _ _ => by simp
    have hmain := sum_cubeVolume_add_le_of_disjoint hUtop (Set.empty_subset T.openCarrier)
      hsubU hdisjF hV
    simp only [measure_empty, ENNReal.toReal_zero, add_zero] at hmain
    have hfac : (1 : ℝ) ≤ 12 * (d : ℝ) * ((d : ℝ) + 1) / (3 : ℝ) ^ t := by
      have h1 : 12 * ((d : ℝ) + 1) / (3 : ℝ) ^ t ≤
          12 * (d : ℝ) * ((d : ℝ) + 1) / (3 : ℝ) ^ t := by
        rw [div_le_div_iff_of_pos_right h3t]
        nlinarith
      linarith
    nlinarith [hUpos, hmain]

/-! ## The weighted sum over the dissection -/

/-- The depth of a dissection cube below the support cube of its simplex. -/
def dissectionDepth (T : KuhnCell d) (R : TriadicCube d) : ℕ :=
  (T.supportCube.scale - R.scale).toNat

theorem dissectionDepth_spec {T : KuhnCell d} {R : TriadicCube d}
    (hR : R ∈ simplexDissection T) :
    R ∈ descendantsAtDepth T.supportCube (dissectionDepth T R) ∧
      ((T.supportCube.scale - R.scale : ℤ) : ℝ) = ((dissectionDepth T R : ℕ) : ℝ) := by
  obtain ⟨t, ht⟩ := exists_depth_of_mem_whitneyInnerCubes hR
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth ht
  have hdepth : dissectionDepth T R = t := by
    rw [dissectionDepth, hscale]
    omega
  refine ⟨hdepth ▸ ht, ?_⟩
  have hz : (T.supportCube.scale - R.scale : ℤ) = ((dissectionDepth T R : ℕ) : ℤ) := by
    rw [hdepth, hscale]
    omega
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz

/-- **The summability constant of the identified route**, finite exactly on the window `s
< 1/2`. -/
def simplexDissectionConst (d : ℕ) (s : ℝ) : ℝ :=
  12 * (d : ℝ) * ((d : ℝ) + 1) / (1 - (3 : ℝ) ^ (2 * s - 1))

/-- Half of the summability constant: the constant of the crude response bounds
at the simplex carrier. -/
def simplexCrudeConst (d : ℕ) (s : ℝ) : ℝ :=
  6 * (d : ℝ) * ((d : ℝ) + 1) / (1 - (3 : ℝ) ^ (2 * s - 1))

private theorem geometricRatio_lt_one {s : ℝ} (hs : s < 1 / 2) :
    (3 : ℝ) ^ (2 * s - 1) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

private theorem geometricRatio_nonneg (s : ℝ) : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * s - 1) :=
  Real.rpow_nonneg (by norm_num) _

theorem simplexDissectionConst_nonneg (d : ℕ) {s : ℝ} (hs : s < 1 / 2) :
    0 ≤ simplexDissectionConst d s := by
  have h : (0 : ℝ) < 1 - (3 : ℝ) ^ (2 * s - 1) := by
    have := geometricRatio_lt_one hs
    linarith
  rw [simplexDissectionConst]
  exact div_nonneg (by positivity) h.le

theorem simplexCrudeConst_nonneg (d : ℕ) {s : ℝ} (hs : s < 1 / 2) :
    0 ≤ simplexCrudeConst d s := by
  have h : (0 : ℝ) < 1 - (3 : ℝ) ^ (2 * s - 1) := by
    have := geometricRatio_lt_one hs
    linarith
  rw [simplexCrudeConst]
  exact div_nonneg (by positivity) h.le

theorem two_mul_simplexCrudeConst (d : ℕ) (s : ℝ) :
    2 * simplexCrudeConst d s = simplexDissectionConst d s := by
  rw [simplexCrudeConst, simplexDissectionConst]
  ring

private theorem rpow_depth_div_pow (s : ℝ) (t : ℕ) :
    (3 : ℝ) ^ (2 * s * (t : ℝ)) / (3 : ℝ) ^ t = ((3 : ℝ) ^ (2 * s - 1)) ^ t := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [show ((3 : ℝ) ^ t) = (3 : ℝ) ^ ((t : ℕ) : ℝ) from (Real.rpow_natCast 3 t).symm,
    ← Real.rpow_natCast ((3 : ℝ) ^ (2 * s - 1)) t, ← Real.rpow_mul h3.le, ← Real.rpow_sub h3]
  ring_nf

/-- **The weighted sum of the identified route.**  For `s < 1/2` the series `sum_i
(|R_i|/|T|) 3^{2 s t_i}` over the triadic Whitney dissection of an open Kuhn simplex is
bounded by the explicit `d`- and `s`-only constant `12 d (d+1) / (1 - 3^{2s-1})`. -/
theorem tsum_cubeVolume_weight_le [NeZero d] (T : KuhnCell d) {s : ℝ} (hs : s < 1 / 2) :
    ∑' R : ↥(simplexDissection T),
        ENNReal.ofReal (cubeVolume (R : TriadicCube d) / (volume T.openCarrier).toReal *
          (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - (R : TriadicCube d).scale : ℤ) : ℝ)))
      ≤ ENNReal.ofReal (simplexDissectionConst d s) := by
  classical
  have hUtop : volume T.openCarrier ≠ ⊤ := (isBoundedDomain_openCarrier T).volume_lt_top.ne
  have hmupos : 0 < (volume T.openCarrier).toReal := by
    have h1 : 0 < volume T.openCarrier :=
      (isOpen_openCarrier T).measure_pos volume (openCarrier_nonempty T)
    exact ENNReal.toReal_pos h1.ne' hUtop
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * s - 1) := geometricRatio_nonneg s
  have hr1 : (3 : ℝ) ^ (2 * s - 1) < 1 := geometricRatio_lt_one hs
  have hcubenn : ∀ R : TriadicCube d,
      (0 : ℝ) ≤ cubeVolume R / (volume T.openCarrier).toReal *
        (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - R.scale : ℤ) : ℝ)) := by
    intro R
    have h2 : (0 : ℝ) ≤
        (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - R.scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg (div_nonneg (cubeVolume_nonneg _) hmupos.le) h2
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun J => ?_
  have hnnJ : ∀ R ∈ J, (0 : ℝ) ≤ cubeVolume (R : TriadicCube d) / (volume T.openCarrier).toReal *
      (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - (R : TriadicCube d).scale : ℤ) : ℝ)) :=
    fun R _ => hcubenn (R : TriadicCube d)
  rw [← ENNReal.ofReal_sum_of_nonneg hnnJ]
  refine ENNReal.ofReal_le_ofReal ?_
  -- transfer the finite sum from the subtype index to a finset of cubes
  have hinjJ : ∀ x ∈ J, ∀ y ∈ J, (x : TriadicCube d) = (y : TriadicCube d) → x = y :=
    fun _ _ _ _ h => Subtype.ext h
  have htransfer :
      (∑ R ∈ J, cubeVolume (R : TriadicCube d) / (volume T.openCarrier).toReal *
        (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - (R : TriadicCube d).scale : ℤ) : ℝ))) =
      ∑ R ∈ J.image Subtype.val,
        cubeVolume R / (volume T.openCarrier).toReal *
          (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - R.scale : ℤ) : ℝ)) :=
    (Finset.sum_image (f := fun R : TriadicCube d =>
      cubeVolume R / (volume T.openCarrier).toReal *
        (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - R.scale : ℤ) : ℝ))) hinjJ).symm
  rw [htransfer]
  set FJ : Finset (TriadicCube d) := J.image Subtype.val with hFJ
  have hFJsel : ∀ R ∈ FJ, R ∈ simplexDissection T := by
    intro R hR
    rw [hFJ] at hR
    obtain ⟨R', -, hR'⟩ := Finset.mem_image.1 hR
    exact hR' ▸ R'.property
  have hmaps : ∀ R ∈ FJ,
      dissectionDepth T R ∈ Finset.range (FJ.sup (dissectionDepth T) + 1) := fun R hR =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup hR))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hstep : ∀ n ∈ Finset.range (FJ.sup (dissectionDepth T) + 1),
      (∑ R ∈ FJ.filter fun R => dissectionDepth T R = n,
          cubeVolume R / (volume T.openCarrier).toReal *
            (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - R.scale : ℤ) : ℝ))) ≤
        12 * (d : ℝ) * ((d : ℝ) + 1) * ((3 : ℝ) ^ (2 * s - 1)) ^ n := by
    intro n _
    have hsel : ∀ R ∈ FJ.filter fun R => dissectionDepth T R = n,
        R ∈ simplexDissection T := fun R hR => hFJsel R (Finset.mem_filter.1 hR).1
    have hdep : ∀ R ∈ FJ.filter fun R => dissectionDepth T R = n,
        R ∈ descendantsAtDepth T.supportCube n := by
      intro R hR
      have hn : dissectionDepth T R = n := (Finset.mem_filter.1 hR).2
      exact hn ▸ (dissectionDepth_spec (hsel R hR)).1
    have hvolbound := sum_cubeVolume_simplexDissection_le T n hsel hdep
    have hrewrite : (∑ R ∈ FJ.filter fun R => dissectionDepth T R = n,
          cubeVolume R / (volume T.openCarrier).toReal *
            (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - R.scale : ℤ) : ℝ))) =
        (3 : ℝ) ^ (2 * s * (n : ℝ)) / (volume T.openCarrier).toReal *
          ∑ R ∈ FJ.filter fun R => dissectionDepth T R = n, cubeVolume R := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun R hR => ?_
      have hn : dissectionDepth T R = n := (Finset.mem_filter.1 hR).2
      rw [(dissectionDepth_spec (hsel R hR)).2, hn]
      field_simp
    rw [hrewrite]
    have hcoef : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * s * (n : ℝ)) / (volume T.openCarrier).toReal := by
      have h : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * s * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
      exact div_nonneg h hmupos.le
    calc (3 : ℝ) ^ (2 * s * (n : ℝ)) / (volume T.openCarrier).toReal *
            ∑ R ∈ FJ.filter fun R => dissectionDepth T R = n, cubeVolume R
        ≤ (3 : ℝ) ^ (2 * s * (n : ℝ)) / (volume T.openCarrier).toReal *
            (12 * (d : ℝ) * ((d : ℝ) + 1) / (3 : ℝ) ^ n * (volume T.openCarrier).toReal) :=
          mul_le_mul_of_nonneg_left hvolbound hcoef
      _ = 12 * (d : ℝ) * ((d : ℝ) + 1) * ((3 : ℝ) ^ (2 * s * (n : ℝ)) / (3 : ℝ) ^ n) := by
          field_simp
      _ = 12 * (d : ℝ) * ((d : ℝ) + 1) * ((3 : ℝ) ^ (2 * s - 1)) ^ n := by
          rw [rpow_depth_div_pow]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hgeom : (∑ n ∈ Finset.range (FJ.sup (dissectionDepth T) + 1),
      ((3 : ℝ) ^ (2 * s - 1)) ^ n) ≤ (1 - (3 : ℝ) ^ (2 * s - 1))⁻¹ := by
    have h := Summable.sum_le_tsum (Finset.range (FJ.sup (dissectionDepth T) + 1))
      (fun n _ => pow_nonneg hr0 n) (summable_geometric_of_lt_one hr0 hr1)
    rwa [tsum_geometric_of_lt_one hr0 hr1] at h
  have hcoef : (0 : ℝ) ≤ 12 * (d : ℝ) * ((d : ℝ) + 1) := by positivity
  refine (mul_le_mul_of_nonneg_left hgeom hcoef).trans (le_of_eq ?_)
  rw [simplexDissectionConst]
  field_simp

/-! ## Coefficient restriction -/

/-- The restriction of a Chapter 2 coefficient object to a subdomain, with the
*same* representative field.  Literal equality of representatives is what the
`haS` binder of `l.subadd.betterer` requires. -/
def restrictCoeffOn {U V : Ch02.Domain d} (a : Ch02.CoeffOn U)
    (h : (V : Set (Vec d)) ⊆ (U : Set (Vec d))) : Ch02.CoeffOn V where
  toCoeffField := a.toCoeffField
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have hmono : volumeMeasureOn (V : Set (Vec d)) ≤ volumeMeasureOn (U : Set (Vec d)) :=
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume h
    refine ((a.aeStronglyMeasurable i j).mono_measure hmono).congr ?_
    refine (MeasureTheory.ae_restrict_iff' V.measurableSet).2 (Filter.Eventually.of_forall ?_)
    intro x hx
    simp only [restrictCoeffField_apply_of_mem hx, restrictCoeffField_apply_of_mem (h hx)]
  aeElliptic :=
    a.aeElliptic.filter_mono
      (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume h))


/-- The coefficient object on the open Kuhn simplex: the restriction of the
support cube's representative. -/
def simplexCoeffOn (a : Ch02.TriadicCoeffFamily d) (T : KuhnCell d) :
    Ch02.CoeffOn (simplexDomain T) :=
  restrictCoeffOn (a.coeffOn T.supportCube) T.openCarrier_subset_openCubeSet

/-- The coefficient object on a cube of the dissection: the restriction of the
same support-cube representative. -/
def dissectionCoeffOn (a : Ch02.TriadicCoeffFamily d) (T : KuhnCell d)
    (R : ↥(simplexDissection T)) : Ch02.CoeffOn (Ch02.cubeDomain (R : TriadicCube d)) :=
  restrictCoeffOn (a.coeffOn T.supportCube)
    ((openCubeSet_subset_cubeSet _).trans
      ((cubeSet_subset_openCarrier_of_mem_simplexDissection R.2).trans
        T.openCarrier_subset_openCubeSet))

/-- On a dissection cube the restricted representative agrees a.e. with the
family's own one, so the two response functionals coincide. -/
theorem responseJ_dissectionCoeffOn (a : Ch02.TriadicCoeffFamily d) (T : KuhnCell d)
    (R : ↥(simplexDissection T)) (p q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain (R : TriadicCube d)) (dissectionCoeffOn a T R) p q =
      Ch02.responseJ (Ch02.cubeDomain (R : TriadicCube d))
        (a.coeffOn (R : TriadicCube d)) p q := by
  refine Ch02.responseJ_eq_ofAEEq ?_ p q
  exact (a.restrictsTo_of_subset
    ((openCubeSet_subset_cubeSet _).trans
      ((cubeSet_subset_openCarrier_of_mem_simplexDissection R.2).trans
        T.openCarrier_subset_openCubeSet))).symm

/-! ## The crude response bounds at the simplex carrier -/

/-- A nonempty scale-`k` descendant family forces `k <= Q.scale`, so the scale
bound is not an extra hypothesis. -/
private theorem le_scale_of_mem_descendantsAtScale {Q R : TriadicCube d} {k : ℤ}
    (h : R ∈ descendantsAtScale Q k) : k ≤ Q.scale := by
  by_contra hk
  rw [descendantsAtScale_eq_empty Q (by omega)] at h
  exact absurd h (Finset.notMem_empty _)

private theorem supportCube_scale_eq {Q : TriadicCube d} {k : ℤ} {T : KuhnCell d}
    (hT : T.supportCube ∈ descendantsAtScale Q k) : T.supportCube.scale = k := by
  have hk : k ≤ Q.scale := le_scale_of_mem_descendantsAtScale hT
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hT
  have h := scale_eq_sub_of_mem_descendantsAtDepth hT
  omega

private theorem mem_descendantsAtScale_of_mem_simplexDissection
    {Q : TriadicCube d} {k : ℤ} {T : KuhnCell d}
    (hT : T.supportCube ∈ descendantsAtScale Q k) {R : TriadicCube d}
    (hR : R ∈ simplexDissection T) : R ∈ descendantsAtScale Q R.scale := by
  have hk : k ≤ Q.scale := le_scale_of_mem_descendantsAtScale hT
  have hTs := supportCube_scale_eq hT
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hT
  obtain ⟨t, ht⟩ := exists_depth_of_mem_whitneyInnerCubes hR
  have hRs : R.scale = k - (t : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth ht
    omega
  have hRQ : R ∈ descendantsAtDepth Q ((Q.scale - k).toNat + t) :=
    mem_descendantsAtDepth_add hT ht
  have hle : R.scale ≤ Q.scale := by omega
  rw [descendantsAtScale_eq_descendantsAtDepth Q hle,
    show (Q.scale - R.scale).toNat = (Q.scale - k).toNat + t from by omega]
  exact hRQ

private theorem multiscaleDescendantWeight_split {Q : TriadicCube d} {k : ℤ}
    (R : TriadicCube d) (s : ℝ) :
    Ch02.multiscaleDescendantWeight Q R.scale s =
      Ch02.multiscaleDescendantWeight Q k s *
        (3 : ℝ) ^ (2 * s * ((k - R.scale : ℤ) : ℝ)) := by
  have hexp : (2 * s * ((Q.scale - R.scale : ℤ) : ℝ)) =
      2 * s * ((Q.scale - k : ℤ) : ℝ) + 2 * s * ((k - R.scale : ℤ) : ℝ) := by
    push_cast
    ring
  show (3 : ℝ) ^ (2 * s * ((Q.scale - R.scale : ℤ) : ℝ)) =
    (3 : ℝ) ^ (2 * s * ((Q.scale - k : ℤ) : ℝ)) * (3 : ℝ) ^ (2 * s * ((k - R.scale : ℤ) : ℝ))
  rw [hexp, Real.rpow_add (by norm_num)]

/-- For a Kuhn cell `T` whose support cube is a triadic descendant of `Q` at scale
`k`, every `0 < s < 1/2` and every admissible exponent,

```
J(T, p, 0; a) <= C(d,s) . 3^{2 s (Q.scale - k)} . Lambda_{s,q}(Q; a) . |p|^2
```

with `C(d,s) = simplexCrudeConst d s = 6 d (d+1) / (1 - 3^{2s-1})`.

The `s < 1/2` binder is the convergence window of the identified route: it is a
genuine hypothesis of the boundary estimate, not a proof convenience, and the
manuscript's own exponent `s = 1/4` lies in it. -/
theorem responseJ_simplexDomain_zero_flux_le_LambdaSq [NeZero d]
    {Q : TriadicCube d} {k : ℤ} {T : KuhnCell d}
    (hT : T.supportCube ∈ descendantsAtScale Q k) (a : Ch02.TriadicCoeffFamily d)
    {s : ℝ} {qe : Ch02.MultiscaleExponent} (hs0 : 0 < s) (hs : s < 1 / 2)
    (hq : qe.IsAdmissible) (p : Vec d) :
    Ch02.responseJ (simplexDomain T) (simplexCoeffOn a T) p 0 ≤
      simplexCrudeConst d s *
        (Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a) * vecNormSq p := by
  classical
  have hUtop : volume T.openCarrier ≠ ⊤ := (isBoundedDomain_openCarrier T).volume_lt_top.ne
  have hmupos : 0 < (volume T.openCarrier).toReal := by
    have h1 : 0 < volume T.openCarrier :=
      (isOpen_openCarrier T).measure_pos volume (openCarrier_nonempty T)
    exact ENNReal.toReal_pos h1.ne' hUtop
  have hTs : T.supportCube.scale = k := supportCube_scale_eq hT
  have hWnn : 0 ≤ Ch02.multiscaleDescendantWeight Q k s :=
    multiscaleDescendantWeight_nonneg Q k s
  have hLnn : 0 ≤ Ch02.LambdaSq Q s qe a := Ch02.LambdaSq_nonneg Q a hs0 hq
  have hpnn : 0 ≤ vecNormSq p := vecNormSq_nonneg p
  have hKnn : 0 ≤ Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a * vecNormSq p :=
    mul_nonneg (mul_nonneg hWnn hLnn) hpnn
  have hsubadd := ofReal_bfA_quadratic_le_simplex_weighted_tsum
    (ι := ↥(simplexDissection T)) (Q := simplexDomain T)
    (S := fun R => Ch02.cubeDomain (R : TriadicCube d))
    (simplexCoeffOn a T) (dissectionCoeffOn a T) (fun _ => rfl)
    (fun R => openCubeSet_subset_openCarrier_of_mem_simplexDissection R.2)
    (fun R R' hRR' => pairwiseDisjoint_openCubeSet_simplexDissection T R.2 R'.2
      fun h => hRR' (Subtype.ext h))
    (volume_openCarrier_diff_iUnion_eq_zero T)
    p 0 (fun _ => p) (fun _ => (0 : Vec d)) (fun _ => p) (fun _ => (0 : Vec d))
    (by simpa using (potentialZeroTraceFieldOn_zero (U := T.openCarrier)))
    (by simpa using (solenoidalZeroNormalTraceFieldOn_zero (U := T.openCarrier)))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [blockVecDot_coarseBlockMatrix_pure_potential (simplexDomain T) (simplexCoeffOn a T) p]
    at hsubadd
  have hterm : ∀ R : ↥(simplexDissection T),
      ENNReal.ofReal
        (((volume ((Ch02.cubeDomain (R : TriadicCube d) : Ch02.Domain d) : Set (Vec d))).toReal /
            (volume ((simplexDomain T : Ch02.Domain d) : Set (Vec d))).toReal) *
          blockVecDot ((p, 0) : BlockVec d)
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain (R : TriadicCube d))
                (dissectionCoeffOn a T R)) (p, 0))) ≤
      ENNReal.ofReal
          (Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a * vecNormSq p) *
        ENNReal.ofReal (cubeVolume (R : TriadicCube d) / (volume T.openCarrier).toReal *
          (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - (R : TriadicCube d).scale : ℤ) : ℝ))) := by
    intro R
    have hJ := responseJ_zero_flux_le_LambdaSq_of_mem_descendantsAtScale
      (Q := Q) (R := (R : TriadicCube d)) (k := (R : TriadicCube d).scale) a
      (mem_descendantsAtScale_of_mem_simplexDissection hT R.2) hs0 hq p
    rw [blockVecDot_coarseBlockMatrix_pure_potential, responseJ_dissectionCoeffOn,
      ← ENNReal.ofReal_mul hKnn]
    simp only [Ch02.cubeDomain_coe, simplexDomain_coe, volume_openCubeSet_toReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : 0 ≤ cubeVolume (R : TriadicCube d) / (volume T.openCarrier).toReal :=
      div_nonneg (cubeVolume_nonneg _) hmupos.le
    have hexp : (0 : ℝ) ≤
        (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - (R : TriadicCube d).scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hJ2 : 2 * Ch02.responseJ (Ch02.cubeDomain (R : TriadicCube d))
        (a.coeffOn (R : TriadicCube d)) p 0 ≤
        Ch02.multiscaleDescendantWeight Q k s *
          (3 : ℝ) ^ (2 * s * ((k - (R : TriadicCube d).scale : ℤ) : ℝ)) *
          Ch02.LambdaSq Q s qe a * vecNormSq p := by
      have hsplit := multiscaleDescendantWeight_split (Q := Q) (k := k) (R : TriadicCube d) s
      rw [← hsplit]
      linarith [hJ]
    rw [hTs]
    nlinarith [hJ2, hw, hexp]
  have hchain := hsubadd.trans (ENNReal.tsum_le_tsum hterm)
  rw [ENNReal.tsum_mul_left] at hchain
  have hfin : ENNReal.ofReal
      (2 * Ch02.responseJ (simplexDomain T) (simplexCoeffOn a T) p 0) ≤
      ENNReal.ofReal ((Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a *
        vecNormSq p) * simplexDissectionConst d s) := by
    refine hchain.trans ?_
    rw [ENNReal.ofReal_mul hKnn]
    exact mul_le_mul' le_rfl (tsum_cubeVolume_weight_le T hs)
  have hreal : 2 * Ch02.responseJ (simplexDomain T) (simplexCoeffOn a T) p 0 ≤
      (Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a * vecNormSq p) *
        simplexDissectionConst d s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKnn (simplexDissectionConst_nonneg d hs))).1 hfin
  have heq : (Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a * vecNormSq p) *
      simplexDissectionConst d s =
      2 * (simplexCrudeConst d s *
        (Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a) * vecNormSq p) := by
    rw [← two_mul_simplexCrudeConst d s]
    ring
  rw [heq] at hreal
  linarith

/-- The mirror of `responseJ_simplexDomain_zero_flux_le_LambdaSq` on the pure-flux
leg. -/
theorem responseJ_simplexDomain_zero_slope_le_lambdaSq_inv [NeZero d]
    {Q : TriadicCube d} {k : ℤ} {T : KuhnCell d}
    (hT : T.supportCube ∈ descendantsAtScale Q k) (a : Ch02.TriadicCoeffFamily d)
    {s : ℝ} {qe : Ch02.MultiscaleExponent} (hs0 : 0 < s) (hs : s < 1 / 2)
    (hq : qe.IsAdmissible) (q : Vec d) :
    Ch02.responseJ (simplexDomain T) (simplexCoeffOn a T) 0 q ≤
      simplexCrudeConst d s *
        (Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹) * vecNormSq q := by
  classical
  have hUtop : volume T.openCarrier ≠ ⊤ := (isBoundedDomain_openCarrier T).volume_lt_top.ne
  have hmupos : 0 < (volume T.openCarrier).toReal := by
    have h1 : 0 < volume T.openCarrier :=
      (isOpen_openCarrier T).measure_pos volume (openCarrier_nonempty T)
    exact ENNReal.toReal_pos h1.ne' hUtop
  have hTs : T.supportCube.scale = k := supportCube_scale_eq hT
  have hWnn : 0 ≤ Ch02.multiscaleDescendantWeight Q k s :=
    multiscaleDescendantWeight_nonneg Q k s
  have hLnn : 0 ≤ (Ch02.lambdaSq Q s qe a)⁻¹ :=
    inv_nonneg.2 (Ch02.lambdaSq_nonneg Q a hs0 hq)
  have hqnn : 0 ≤ vecNormSq q := vecNormSq_nonneg q
  have hKnn : 0 ≤ Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹ *
      vecNormSq q := mul_nonneg (mul_nonneg hWnn hLnn) hqnn
  have hsubadd := ofReal_bfA_quadratic_le_simplex_weighted_tsum
    (ι := ↥(simplexDissection T)) (Q := simplexDomain T)
    (S := fun R => Ch02.cubeDomain (R : TriadicCube d))
    (simplexCoeffOn a T) (dissectionCoeffOn a T) (fun _ => rfl)
    (fun R => openCubeSet_subset_openCarrier_of_mem_simplexDissection R.2)
    (fun R R' hRR' => pairwiseDisjoint_openCubeSet_simplexDissection T R.2 R'.2
      fun h => hRR' (Subtype.ext h))
    (volume_openCarrier_diff_iUnion_eq_zero T)
    0 q (fun _ => (0 : Vec d)) (fun _ => q) (fun _ => (0 : Vec d)) (fun _ => q)
    (by simpa using (potentialZeroTraceFieldOn_zero (U := T.openCarrier)))
    (by simpa using (solenoidalZeroNormalTraceFieldOn_zero (U := T.openCarrier)))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [blockVecDot_coarseBlockMatrix_pure_flux (simplexDomain T) (simplexCoeffOn a T) q]
    at hsubadd
  have hterm : ∀ R : ↥(simplexDissection T),
      ENNReal.ofReal
        (((volume ((Ch02.cubeDomain (R : TriadicCube d) : Ch02.Domain d) : Set (Vec d))).toReal /
            (volume ((simplexDomain T : Ch02.Domain d) : Set (Vec d))).toReal) *
          blockVecDot ((0, q) : BlockVec d)
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain (R : TriadicCube d))
                (dissectionCoeffOn a T R)) (0, q))) ≤
      ENNReal.ofReal
          (Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹ * vecNormSq q) *
        ENNReal.ofReal (cubeVolume (R : TriadicCube d) / (volume T.openCarrier).toReal *
          (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - (R : TriadicCube d).scale : ℤ) : ℝ))) := by
    intro R
    have hJ := responseJ_zero_slope_le_lambdaSq_inv_of_mem_descendantsAtScale
      (Q := Q) (R := (R : TriadicCube d)) (k := (R : TriadicCube d).scale) a
      (mem_descendantsAtScale_of_mem_simplexDissection hT R.2) hs0 hq q
    rw [blockVecDot_coarseBlockMatrix_pure_flux, responseJ_dissectionCoeffOn,
      ← ENNReal.ofReal_mul hKnn]
    simp only [Ch02.cubeDomain_coe, simplexDomain_coe, volume_openCubeSet_toReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : 0 ≤ cubeVolume (R : TriadicCube d) / (volume T.openCarrier).toReal :=
      div_nonneg (cubeVolume_nonneg _) hmupos.le
    have hexp : (0 : ℝ) ≤
        (3 : ℝ) ^ (2 * s * ((T.supportCube.scale - (R : TriadicCube d).scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hJ2 : 2 * Ch02.responseJ (Ch02.cubeDomain (R : TriadicCube d))
        (a.coeffOn (R : TriadicCube d)) 0 q ≤
        Ch02.multiscaleDescendantWeight Q k s *
          (3 : ℝ) ^ (2 * s * ((k - (R : TriadicCube d).scale : ℤ) : ℝ)) *
          (Ch02.lambdaSq Q s qe a)⁻¹ * vecNormSq q := by
      have hsplit := multiscaleDescendantWeight_split (Q := Q) (k := k) (R : TriadicCube d) s
      rw [← hsplit]
      linarith [hJ]
    rw [hTs]
    nlinarith [hJ2, hw, hexp]
  have hchain := hsubadd.trans (ENNReal.tsum_le_tsum hterm)
  rw [ENNReal.tsum_mul_left] at hchain
  have hfin : ENNReal.ofReal
      (2 * Ch02.responseJ (simplexDomain T) (simplexCoeffOn a T) 0 q) ≤
      ENNReal.ofReal ((Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹ *
        vecNormSq q) * simplexDissectionConst d s) := by
    refine hchain.trans ?_
    rw [ENNReal.ofReal_mul hKnn]
    exact mul_le_mul' le_rfl (tsum_cubeVolume_weight_le T hs)
  have hreal : 2 * Ch02.responseJ (simplexDomain T) (simplexCoeffOn a T) 0 q ≤
      (Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹ * vecNormSq q) *
        simplexDissectionConst d s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKnn (simplexDissectionConst_nonneg d hs))).1 hfin
  have heq : (Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹ *
      vecNormSq q) * simplexDissectionConst d s =
      2 * (simplexCrudeConst d s *
        (Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹) * vecNormSq q) := by
    rw [← two_mul_simplexCrudeConst d s]
    ring
  rw [heq] at hreal
  linarith

/-! ## The manuscript's exponent -/


end

end Algsuperdiff.Section3.Provider.Multiscale
