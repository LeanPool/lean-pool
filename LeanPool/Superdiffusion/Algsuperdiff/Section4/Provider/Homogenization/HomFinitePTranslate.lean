/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomFinitePSource
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyBox
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilityGeometry

/-!
# HomFinitePTranslate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The grid-to-translate extension of a multiscale negative gauge

## What this module closes

`hCG'` is transcribed at the PRINTED grid-summed carrier (the pure lattice `3^k
ℤ^d ∩ □_m`, i.e. `descendantsAtDepth`).  The Step-3c chain consumes the gauge
at EVERY TRANSLATE (`UniformBoxGaugeBound`), because the mollifier calculus
averages against `x + □_n` at arbitrary centres
(`norm_boxMixtureVec_le_of_uniformBoxGauge`).  The mismatch is recorded here, and
the reconstruction "grid ⟹ translate" is left unformalized.

**This module proves it**, at the explicit dimensional constant `6 d` times the
geometric factor `liftGeomFactor s'`:

```text
   ‖(F)_R‖ ≤ A·3^{-s' k}  for every grid cube R of scale k
     ⟹  ‖(F)_{x+□_n}‖ ≤ 6 d · liftGeomFactor s' · A · 3^{-s' n}   for EVERY x.
```

The mechanism is the printed one (a Whitney/greedy decomposition), and the
apparatus is already in this repository:
`OffGridStabilityGeometry` supplies

* `iUnion_maximalCubes_eq` — the maximal grid subcubes tile `x + □_n` EXACTLY;
* `scale_le_of_maximalCubeIn_offGridCube` — their scales are `≤ n`;
* `volume_iUnion_maximalCubesAtScale_toReal_le` — **the packing count**, the
  total volume of the scale-`k` maximal cubes is at most
  `2d·3^{k+1-n}` times the volume of the box.

Summing `|Q|·A·3^{-s' k_Q}` over the tiling and grouping by scale gives a
geometric series in `3^{-(1-s')}`, whose sum is `liftGeomFactor s'`; the boxes
at scale `k` contribute `2d·3^{1+k-n}`, whence `6d`.  Nothing else enters, and
the constant is dimension-only.

`liftGeomFactor s' ≤ 3` for `s' ≤ 1/2` (`liftGeomFactor_le_three`), so the
constant at the Step-3 pin is at most `18 d`.

## Main results

* `sum_cubeVolume_fiber_le` — the packing count at one scale, at `2d·3^{1-j}`;
* `finset_sum_maximalCubes_weight_le` — the packing sum, over any finite
  subfamily, at `6 d · liftGeomFactor s'`;
* `abs_setIntegral_offGridCube_le` — the scalar statement on an arbitrary
  translate of a triadic cube;
* `abs_boxAverage_le_of_gridGauge`, `norm_boxAverageVec_le_of_gridGauge` — the
  same at the box carrier, scalar and vector;
* `uniformBoxGaugeBound_of_gridGauge` — **the `UniformBoxGaugeBound`, from
  the whole-grid gauge**;
* `gridGauge_of_descendantBound` — the whole-grid gauge from the PRINTED
  descendants of `□_m`, for a field supported in `□_m`.
-/

open MeasureTheory HCPolySupport

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The packing sum -/

section Packing

variable [NeZero d]

/-- The depth of a maximal cube below the shape cube of the off-grid box. -/
def offDepth (P Q : TriadicCube d) : ℕ := (P.scale - Q.scale).toNat

omit [NeZero d] in
private theorem offDepth_spec {P Q : TriadicCube d} (h : Q.scale ≤ P.scale) :
    Q.scale = P.scale - (offDepth P Q : ℤ) := by
  rw [offDepth, Int.toNat_of_nonneg (by omega)]
  omega

/-- **The packing sum over one scale.**

The maximal grid cubes of the off-grid box `w + □_{P.scale}` at depth `j` have
total volume at most `2d·3^{1-j}` times the volume of the box. -/
theorem sum_cubeVolume_fiber_le (w : Vec d) (P : TriadicCube d) (j : ℕ)
    (S : Finset (TriadicCube d))
    (hS : ∀ Q ∈ S, MaximalCubeIn (offGridCube w P) Q ∧ Q.scale = P.scale - (j : ℤ)) :
    ∑ Q ∈ S, cubeVolume Q ≤
      2 * (d : ℝ) * (3 : ℝ) ^ (1 - (j : ℤ)) * cubeVolume P := by
  classical
  set k : ℤ := P.scale - (j : ℤ) with hk
  have hdisj : ∀ Q ∈ (S : Set (TriadicCube d)), ∀ R ∈ (S : Set (TriadicCube d)), Q ≠ R →
      Disjoint (cubeSet Q) (cubeSet R) := by
    intro Q hQ R hR hne
    exact disjoint_cubeSet_of_maximalCubeIn (hS Q (by exact_mod_cast hQ)).1
      (hS R (by exact_mod_cast hR)).1 hne
  have hunion : volume (⋃ Q ∈ S, cubeSet Q) = ∑ Q ∈ S, volume (cubeSet Q) :=
    measure_biUnion_finset hdisj fun Q _ => measurableSet_cubeSet Q
  have hsubset : (⋃ Q ∈ S, cubeSet Q) ⊆
      ⋃ Q ∈ maximalCubesAtScale (offGridCube w P) k, cubeSet Q := by
    refine Set.iUnion₂_subset ?_
    intro Q hQ
    refine Set.subset_iUnion₂ (s := fun Q (_ : Q ∈ maximalCubesAtScale (offGridCube w P) k) =>
      cubeSet Q) Q ?_
    exact ⟨(hS Q hQ).1, (hS Q hQ).2⟩
  have htop : volume (⋃ Q ∈ maximalCubesAtScale (offGridCube w P) k, cubeSet Q) ≠ ⊤ :=
    volume_iUnion_maximalCubesAtScale_ne_top w P k
  have hmono : (volume (⋃ Q ∈ S, cubeSet Q)).toReal ≤
      (volume (⋃ Q ∈ maximalCubesAtScale (offGridCube w P) k, cubeSet Q)).toReal :=
    ENNReal.toReal_mono htop (measure_mono hsubset)
  have hsumreal : (volume (⋃ Q ∈ S, cubeSet Q)).toReal = ∑ Q ∈ S, cubeVolume Q := by
    rw [hunion, ENNReal.toReal_sum fun Q _ => (volume_cubeSet_lt_top Q).ne]
    exact Finset.sum_congr rfl fun Q _ => volume_cubeSet_toReal Q
  have hpack := volume_iUnion_maximalCubesAtScale_toReal_le w P k
  have hexp : k + 1 - P.scale = 1 - (j : ℤ) := by rw [hk]; omega
  rw [hexp] at hpack
  rw [hsumreal] at hmono
  exact hmono.trans hpack

/-- **THE PACKING SUM.**

Over any finite subfamily of the maximal grid cubes of the off-grid box
`w + □_{P.scale}`, the volume-weighted sum of `3^{s'·depth}` is at most
`6 d · liftGeomFactor s'` times the volume of the box.  This is the whole
geometric content of the grid-to-translate extension. -/
theorem finset_sum_maximalCubes_weight_le (w : Vec d) (P : TriadicCube d) {s' : ℝ}
    (hs1 : s' < 1) (S : Finset (TriadicCube d))
    (hS : ∀ Q ∈ S, MaximalCubeIn (offGridCube w P) Q) :
    ∑ Q ∈ S, cubeVolume Q * (3 : ℝ) ^ (s' * ((P.scale : ℝ) - (Q.scale : ℝ))) ≤
      6 * (d : ℝ) * liftGeomFactor s' * cubeVolume P := by
  classical
  have hVol : (0 : ℝ) < cubeVolume P := cubeVolume_pos P
  set N : ℕ := S.sup (offDepth P) with hN
  have hmaps : ∀ Q ∈ S, offDepth P Q ∈ Finset.range (N + 1) := by
    intro Q hQ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := offDepth P) hQ))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun Q => cubeVolume Q * (3 : ℝ) ^ (s' * ((P.scale : ℝ) - (Q.scale : ℝ))))]
  /- each fiber contributes at most `6 d |P| · r^j` -/
  have hfiber : ∀ j ∈ Finset.range (N + 1),
      (∑ Q ∈ S.filter fun Q => offDepth P Q = j,
          cubeVolume Q * (3 : ℝ) ^ (s' * ((P.scale : ℝ) - (Q.scale : ℝ)))) ≤
        6 * (d : ℝ) * cubeVolume P * ((3 : ℝ) ^ (-(1 - s'))) ^ j := by
    intro j _
    have hscale : ∀ Q ∈ S.filter fun Q => offDepth P Q = j,
        Q.scale = P.scale - (j : ℤ) := by
      intro Q hQ
      obtain ⟨hQS, hQj⟩ := Finset.mem_filter.mp hQ
      have hle : Q.scale ≤ P.scale := scale_le_of_maximalCubeIn_offGridCube (hS Q hQS)
      rw [← hQj]
      exact offDepth_spec hle
    have hconst : ∀ Q ∈ S.filter fun Q => offDepth P Q = j,
        cubeVolume Q * (3 : ℝ) ^ (s' * ((P.scale : ℝ) - (Q.scale : ℝ))) =
          (3 : ℝ) ^ (s' * (j : ℝ)) * cubeVolume Q := by
      intro Q hQ
      rw [hscale Q hQ]
      push_cast
      rw [show (P.scale : ℝ) - ((P.scale : ℝ) - (j : ℝ)) = (j : ℝ) by ring]
      ring
    rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum]
    have hpack := sum_cubeVolume_fiber_le w P j (S.filter fun Q => offDepth P Q = j)
      (fun Q hQ => ⟨hS Q (Finset.mem_filter.mp hQ).1, hscale Q hQ⟩)
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (s' * (j : ℝ)) := three_rpow_nonneg _
    refine (mul_le_mul_of_nonneg_left hpack hw).trans (le_of_eq ?_)
    have hzpow : (3 : ℝ) ^ (1 - (j : ℤ)) = 3 * (3 : ℝ) ^ (-(j : ℝ)) := by
      rw [show (1 : ℤ) - (j : ℤ) = 1 + (-(j : ℤ)) by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
        zpow_one, ← Real.rpow_intCast (3 : ℝ) (-(j : ℤ))]
      push_cast
      ring
    have hr : ((3 : ℝ) ^ (-(1 - s'))) ^ j = (3 : ℝ) ^ (-(1 - s') * (j : ℝ)) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - s'))) j,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [hzpow, hr]
    have hcomb : (3 : ℝ) ^ (s' * (j : ℝ)) * (3 : ℝ) ^ (-(j : ℝ)) =
        (3 : ℝ) ^ (-(1 - s') * (j : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    calc (3 : ℝ) ^ (s' * (j : ℝ)) * (2 * (d : ℝ) * (3 * (3 : ℝ) ^ (-(j : ℝ))) * cubeVolume P)
        = 6 * (d : ℝ) * cubeVolume P *
            ((3 : ℝ) ^ (s' * (j : ℝ)) * (3 : ℝ) ^ (-(j : ℝ))) := by ring
      _ = 6 * (d : ℝ) * cubeVolume P * (3 : ℝ) ^ (-(1 - s') * (j : ℝ)) := by rw [hcomb]
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum]
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - s')) := three_rpow_nonneg _
  have hr1 : (3 : ℝ) ^ (-(1 - s')) < 1 := three_rpow_neg_lt_one (by linarith only [hs1])
  have hgeom := geom_sum_range_le_inv_one_sub hr0 hr1 N
  have hnn : (0 : ℝ) ≤ 6 * (d : ℝ) * cubeVolume P := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h6d : (0 : ℝ) ≤ 6 * (d : ℝ) := by linarith only [hd0]
    exact mul_nonneg h6d (cubeVolume_pos P).le
  refine (mul_le_mul_of_nonneg_left hgeom hnn).trans (le_of_eq ?_)
  rw [liftGeomFactor]
  ring

end Packing

/-! ## 2. The tiling turns the packing sum into an average bound -/

section Average

variable [NeZero d]

omit [NeZero d] in
/-- The maximal cubes' open realizations are pairwise disjoint. -/
private theorem pairwise_disjoint_openCubeSet_maximal (V : Set (Vec d)) :
    Pairwise (Function.onFun Disjoint fun Q : maximalCubes V =>
      openCubeSet (Q : TriadicCube d)) := by
  intro Q R hne
  refine Disjoint.mono (openCubeSet_subset_cubeSet _) (openCubeSet_subset_cubeSet _) ?_
  exact disjoint_cubeSet_of_maximalCubeIn Q.2 R.2 fun h => hne (Subtype.ext h)

/-- The maximal cubes' open realizations cover the off-grid cube up to the
countable union of the cubes' boundaries, hence up to a null set. -/
private theorem volume_offGridCube_diff_iUnion_open (w : Vec d) (P : TriadicCube d) :
    volume (offGridCube w P \
      ⋃ Q : maximalCubes (offGridCube w P), openCubeSet (Q : TriadicCube d)) = 0 := by
  classical
  have hsub : offGridCube w P \
      (⋃ Q : maximalCubes (offGridCube w P), openCubeSet (Q : TriadicCube d)) ⊆
      ⋃ Q : maximalCubes (offGridCube w P), cubeBoundary (Q : TriadicCube d) := by
    intro x hx
    obtain ⟨hxV, hxU⟩ := hx
    rw [← iUnion_maximalCubes_eq w P] at hxV
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.1 hxV
    refine Set.mem_iUnion.2 ⟨⟨Q, hQ⟩, ⟨hxQ, ?_⟩⟩
    intro hxopen
    exact hxU (Set.mem_iUnion.2 ⟨⟨Q, hQ⟩, hxopen⟩)
  refine measure_mono_null hsub ?_
  exact measure_iUnion_null fun Q => volume_cubeBoundary_eq_zero _

/-- The off-grid cube agrees a.e. with the union of the open maximal cubes. -/
private theorem offGridCube_ae_eq_iUnion (w : Vec d) (P : TriadicCube d) :
    offGridCube w P =ᵐ[volume]
      ⋃ Q : maximalCubes (offGridCube w P), openCubeSet (Q : TriadicCube d) := by
  refine MeasureTheory.ae_eq_set.2 ⟨volume_offGridCube_diff_iUnion_open w P, ?_⟩
  have hsub : (⋃ Q : maximalCubes (offGridCube w P), openCubeSet (Q : TriadicCube d)) \
      offGridCube w P = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro x ⟨hxU, hxV⟩
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.1 hxU
    exact hxV (Q.2.1 (openCubeSet_subset_cubeSet _ hxQ))
  rw [hsub]
  simp

omit [NeZero d] in
/-- The integral over one open cube, in terms of its cube average. -/
private theorem setIntegral_openCubeSet_eq (Q : TriadicCube d) (f : Vec d → ℝ) :
    ∫ y in openCubeSet Q, f y = cubeVolume Q * cubeAverage Q f := by
  have hae : openCubeSet Q =ᵐ[volume] cubeSet Q :=
    (MeasureTheory.ae_eq_set).2
      ⟨by
        have : openCubeSet Q \ cubeSet Q = ∅ :=
          Set.eq_empty_of_forall_notMem fun x hx => hx.2 (openCubeSet_subset_cubeSet Q hx.1)
        rw [this]; simp,
       by
        refine measure_mono_null ?_ (volume_cubeBoundary_eq_zero Q)
        intro x hx
        exact ⟨hx.1, hx.2⟩⟩
  have hvol : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  rw [MeasureTheory.setIntegral_congr_set hae, cubeAverage, ← mul_assoc,
    mul_inv_cancel₀ hvol, one_mul]

/-- **The grid-to-translate estimate, scalar form.**

If every grid cube average of `f` obeys the multiscale bound `A·3^{-s' k}`,
then so does the average over an ARBITRARY real translate of a triadic cube,
at the dimensional cost `6 d · liftGeomFactor s'`. -/
theorem abs_setIntegral_offGridCube_le (w : Vec d) (P : TriadicCube d) {s' A : ℝ}
    (hs1 : s' < 1) (hA : 0 ≤ A) {f : Vec d → ℝ} (hf : Integrable f volume)
    (hgrid : ∀ Q : TriadicCube d, Q.scale ≤ P.scale →
      |cubeAverage Q f| ≤ A * (3 : ℝ) ^ (-(s' * ((Q.scale : ℤ) : ℝ)))) :
    |∫ y in offGridCube w P, f y| ≤
      6 * (d : ℝ) * liftGeomFactor s' * A *
        (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) * cubeVolume P := by
  classical
  set V : Set (Vec d) := offGridCube w P with hV
  set cell : maximalCubes V → Set (Vec d) := fun Q => openCubeSet (Q : TriadicCube d) with hcell
  have hmeasc : ∀ Q : maximalCubes V, MeasurableSet (cell Q) :=
    fun Q => measurableSet_openCubeSet _
  have hdisjc : Pairwise (Function.onFun Disjoint cell) := pairwise_disjoint_openCubeSet_maximal V
  have hsum := MeasureTheory.hasSum_integral_iUnion hmeasc hdisjc
    (hf.integrableOn (s := ⋃ Q, cell Q))
  have hsumabs := MeasureTheory.hasSum_integral_iUnion hmeasc hdisjc
    (hf.abs.integrableOn (s := ⋃ Q, cell Q))
  have hmajor : ∀ Q : maximalCubes V,
      |∫ y in cell Q, f y| ≤ ∫ y in cell Q, |f y| := fun Q =>
    MeasureTheory.abs_integral_le_integral_abs
  have hsummable : Summable fun Q : maximalCubes V => |∫ y in cell Q, f y| :=
    Summable.of_nonneg_of_le (fun Q => abs_nonneg _) hmajor hsumabs.summable
  /- the spl -/
  have hsplit : |∫ y in V, f y| ≤ ∑' Q : maximalCubes V, |∫ y in cell Q, f y| := by
    rw [MeasureTheory.setIntegral_congr_set (offGridCube_ae_eq_iUnion w P), ← hsum.tsum_eq]
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun Q : maximalCubes V => ∫ y in cell Q, f y)
        (by simpa only [Real.norm_eq_abs] using hsummable)
  refine hsplit.trans ?_
  /- the termwise majora -/
  have hterm : ∀ Q : maximalCubes V, |∫ y in cell Q, f y| ≤
      A * (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) *
        (cubeVolume (Q : TriadicCube d) *
          (3 : ℝ) ^ (s' * (((P.scale : ℤ) : ℝ) - (((Q : TriadicCube d).scale : ℤ) : ℝ)))) := by
    intro Q
    simp only [hcell]
    rw [setIntegral_openCubeSet_eq (Q : TriadicCube d) f, abs_mul,
      abs_of_nonneg (cubeVolume_pos (Q : TriadicCube d)).le]
    have hstep := mul_le_mul_of_nonneg_left
      (hgrid (Q : TriadicCube d) (scale_le_of_maximalCubeIn_offGridCube Q.2))
      (cubeVolume_pos (Q : TriadicCube d)).le
    refine hstep.trans (le_of_eq ?_)
    have hpow : (3 : ℝ) ^ (-(s' * (((Q : TriadicCube d).scale : ℤ) : ℝ))) =
        (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) *
          (3 : ℝ) ^ (s' * (((P.scale : ℤ) : ℝ) - (((Q : TriadicCube d).scale : ℤ) : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [hpow]
    ring
  have hAw : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) :=
    mul_nonneg hA (three_rpow_nonneg _)
  /- the packing bound on every finite subsum of the majora -/
  have hfin : ∀ u : Finset (maximalCubes V),
      (∑ Q ∈ u, A * (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) *
        (cubeVolume (Q : TriadicCube d) *
          (3 : ℝ) ^ (s' * (((P.scale : ℤ) : ℝ) - (((Q : TriadicCube d).scale : ℤ) : ℝ))))) ≤
        6 * (d : ℝ) * liftGeomFactor s' * A *
          (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) * cubeVolume P := by
    intro u
    rw [← Finset.mul_sum]
    have himg : ∀ R ∈ u.image (fun Q : maximalCubes V => (Q : TriadicCube d)),
        MaximalCubeIn V R := by
      intro R hR
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hR
      exact Q.2
    have hinj : Set.InjOn (fun Q : maximalCubes V => (Q : TriadicCube d))
        (u : Set (maximalCubes V)) := fun _ _ _ _ h => Subtype.ext h
    have hpack : (∑ Q ∈ u, cubeVolume (Q : TriadicCube d) *
        (3 : ℝ) ^ (s' * (((P.scale : ℤ) : ℝ) - (((Q : TriadicCube d).scale : ℤ) : ℝ)))) ≤
        6 * (d : ℝ) * liftGeomFactor s' * cubeVolume P := by
      rw [← Finset.sum_image (f := fun R : TriadicCube d =>
        cubeVolume R * (3 : ℝ) ^ (s' * (((P.scale : ℤ) : ℝ) - ((R.scale : ℤ) : ℝ)))) hinj]
      exact finset_sum_maximalCubes_weight_le w P hs1 _ himg
    have hstep := mul_le_mul_of_nonneg_left hpack hAw
    refine hstep.trans (le_of_eq ?_)
    ring
  have hnnmaj : (0 : maximalCubes V → ℝ) ≤ fun Q : maximalCubes V =>
      A * (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) *
        (cubeVolume (Q : TriadicCube d) *
          (3 : ℝ) ^ (s' * (((P.scale : ℤ) : ℝ) - (((Q : TriadicCube d).scale : ℤ) : ℝ)))) := by
    intro Q
    exact mul_nonneg hAw (mul_nonneg (cubeVolume_pos _).le (three_rpow_nonneg _))
  have hsummableMaj : Summable fun Q : maximalCubes V =>
      A * (3 : ℝ) ^ (-(s' * ((P.scale : ℤ) : ℝ))) *
        (cubeVolume (Q : TriadicCube d) *
          (3 : ℝ) ^ (s' * (((P.scale : ℤ) : ℝ) - (((Q : TriadicCube d).scale : ℤ) : ℝ)))) :=
    summable_of_sum_le hnnmaj hfin
  exact (Summable.tsum_le_tsum hterm hsummable hsummableMaj).trans
    (hsummableMaj.tsum_le_of_sum_le hfin)

end Average

/-! ## 3. The box carrier -/

section Box

variable [NeZero d]

omit [NeZero d] in
private theorem cubeCenter_originCube (n : ℤ) : cubeCenter (originCube d n) = (0 : Vec d) := by
  funext i
  simp [cubeCenter, originCube]

omit [NeZero d] in
private theorem cubeRadius_originCube (n : ℤ) : cubeRadius (originCube d n) = boxRadius n := by
  rw [cubeRadius, cubeScaleFactor_originCube, boxRadius_def, ← Real.rpow_intCast (3 : ℝ) n]
  ring

omit [NeZero d] in
private theorem translateSet_ball_zero (x : Vec d) (r : ℝ) :
    translateSet x (Metric.ball (0 : Vec d) r) = Metric.ball x r := by
  ext y
  rw [mem_translateSet_iff_sub_mem, Metric.mem_ball, Metric.mem_ball, dist_zero_right,
    dist_eq_norm]

omit [NeZero d] in
private theorem cubeVolume_originCube_eq (n : ℤ) :
    cubeVolume (originCube d n) = ((3 : ℝ) ^ (n : ℝ)) ^ d := by
  rw [cubeVolume_eq_scaleFactor_pow, cubeScaleFactor_originCube, ← Real.rpow_intCast (3 : ℝ) n]

omit [NeZero d] in
/-- **The scale-`n` box centred at `x` is the off-grid cube of shape `□_n`.** -/
theorem offGridCube_originCube_eq_ball (n : ℤ) (x : Vec d) :
    offGridCube x (originCube d n) = Metric.ball x (boxRadius n) := by
  rw [offGridCube, ← ball_cubeCenter_eq_openCubeSet, cubeCenter_originCube,
    cubeRadius_originCube, translateSet_ball_zero]

private theorem setIntegral_boxSet_eq_offGridCube (n : ℤ) (x : Vec d) (f : Vec d → ℝ) :
    ∫ y in boxSet n x, f y = ∫ y in offGridCube x (originCube d n), f y := by
  have : Nontrivial (Vec d) := by
    have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
    infer_instance
  have hae : boxSet n x =ᵐ[volume] offGridCube x (originCube d n) := by
    rw [offGridCube_originCube_eq_ball, boxSet_def]
    refine MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩
    · rw [Metric.closedBall_sdiff_ball]
      exact MeasureTheory.Measure.addHaar_sphere volume x (boxRadius n)
    · rw [Set.sdiff_eq_empty.2 Metric.ball_subset_closedBall]
      simp
  exact MeasureTheory.setIntegral_congr_set hae

/-- **The grid-to-translate estimate at the box carrier, scalar form.** -/
theorem abs_boxAverage_le_of_gridGauge {n : ℤ} {s' A : ℝ} (hs1 : s' < 1) (hA : 0 ≤ A)
    {f : Vec d → ℝ} (hf : Integrable f volume)
    (hgrid : ∀ Q : TriadicCube d, Q.scale ≤ n →
      |cubeAverage Q f| ≤ A * (3 : ℝ) ^ (-(s' * ((Q.scale : ℤ) : ℝ)))) (x : Vec d) :
    |boxAverage n x f| ≤
      6 * (d : ℝ) * liftGeomFactor s' * A * (3 : ℝ) ^ (-(s' * (n : ℝ))) := by
  have hvol : (0 : ℝ) < cubeVolume (originCube d n) := cubeVolume_pos _
  have hmain := abs_setIntegral_offGridCube_le x (originCube d n) hs1 hA hf hgrid
  have hscale : ((originCube d n).scale : ℤ) = n := rfl
  rw [hscale] at hmain
  rw [boxAverage_eq_inv_mul_integral, setIntegral_boxSet_eq_offGridCube,
    ← cubeVolume_originCube_eq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvol.le)]
  have hstep := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hvol.le)
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- **The grid-to-translate estimate at the box carrier, vector form.** -/
theorem norm_boxAverageVec_le_of_gridGauge {n : ℤ} {s' A : ℝ} (hs1 : s' < 1) (hA : 0 ≤ A)
    {F : Vec d → Vec d} (hF : ∀ i, Integrable (fun y => F y i) volume)
    (hgrid : ∀ Q : TriadicCube d, Q.scale ≤ n →
      ‖cubeAverageVec Q F‖ ≤ A * (3 : ℝ) ^ (-(s' * ((Q.scale : ℤ) : ℝ)))) (x : Vec d) :
    ‖boxAverageVec n x F‖ ≤
      6 * (d : ℝ) * liftGeomFactor s' * A * (3 : ℝ) ^ (-(s' * (n : ℝ))) := by
  have hC : (0 : ℝ) ≤ 6 * (d : ℝ) * liftGeomFactor s' * A * (3 : ℝ) ^ (-(s' * (n : ℝ))) := by
    have h1 : (0 : ℝ) ≤ liftGeomFactor s' := liftGeomFactor_nonneg hs1
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h6d : (0 : ℝ) ≤ 6 * (d : ℝ) := by linarith only [hd0]
    exact mul_nonneg (mul_nonneg (mul_nonneg h6d h1) hA) (three_rpow_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hC).2 ?_
  intro i
  rw [Real.norm_eq_abs, boxAverageVec_apply]
  refine abs_boxAverage_le_of_gridGauge hs1 hA (hF i) ?_ x
  intro Q hQ
  have hcoord : |cubeAverage Q fun y => F y i| ≤ ‖cubeAverageVec Q F‖ := by
    have := norm_le_pi_norm (cubeAverageVec Q F) i
    rwa [Real.norm_eq_abs, cubeAverageVec] at this
  exact hcoord.trans (hgrid Q hQ)

/-- **THE GRID-TO-TRANSLATE EXTENSION.**

A multiscale negative gauge of order `-s'` on the PRINTED triadic grid — every
grid cube of every scale — is the translate-uniform `UniformBoxGaugeBound` at
the dimensional cost `6 d · liftGeomFactor s'`. For `s' ≤ 1/2` the geometric
factor is at most `3`, so the cost is at most `18 d`.

This is the item left open above; the source hypothesis may therefore be
transcribed at the printed grid carrier and consumed at the translate carrier
without any harvest. -/
theorem uniformBoxGaugeBound_of_gridGauge (m : ℤ) {s' A : ℝ} (hs1 : s' < 1) (hA : 0 ≤ A)
    {F : Vec d → Vec d} (hF : ∀ i, Integrable (fun y => F y i) volume)
    (hgrid : ∀ Q : TriadicCube d, Q.scale ≤ m →
      ‖cubeAverageVec Q F‖ ≤ A * (3 : ℝ) ^ (-(s' * ((Q.scale : ℤ) : ℝ)))) :
    UniformBoxGaugeBound m s' (6 * (d : ℝ) * liftGeomFactor s' * A) F := by
  intro n hn x
  have hmain := norm_boxAverageVec_le_of_gridGauge (n := n) hs1 hA hF
    (fun Q hQ => hgrid Q (hQ.trans hn)) x
  refine hmain.trans (le_of_eq ?_)
  rw [show -(s' * (n : ℝ)) = -((n : ℝ) * s') by ring]

/-! ## 4. From the PRINTED descendants to the whole grid -/

omit [NeZero d] in
/-- **The printed carrier feeds the whole-grid hypothesis.**

The printed sum of the negative Besov seminorm definition runs over `3^k ℤ^d ∩
□_m`, i.e. over the triadic descendants of `□_m`;
`uniformBoxGaugeBound_of_gridGauge` asks for every grid cube of scale `≤ m`.
The two agree for a field supported in `□_m`: a grid cube of scale `≤ m` either
shares a point with `□_m`, and is then a descendant of it (nested-or-disjoint),
or is disjoint from it, and then its average vanishes.

The support hypothesis is the `H¹₀` zero extension already present in the frame
— the Step-3 object is `∇(u-v)` with `u - v ∈ H¹₀(□_m)`. -/
theorem gridGauge_of_descendantBound (m : ℤ) {s' A : ℝ} (hA : 0 ≤ A) {F : Vec d → Vec d}
    (hzero : ∀ y, y ∉ cubeSet (originCube d m) → F y = 0)
    (hdesc : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth (originCube d m) j →
      ‖cubeAverageVec R F‖ ≤ A * (3 : ℝ) ^ (-(s' * ((R.scale : ℤ) : ℝ)))) :
    ∀ Q : TriadicCube d, Q.scale ≤ m →
      ‖cubeAverageVec Q F‖ ≤ A * (3 : ℝ) ^ (-(s' * ((Q.scale : ℤ) : ℝ))) := by
  intro Q hQ
  by_cases hdisj : Disjoint (cubeSet Q) (cubeSet (originCube d m))
  · have hvanish : cubeAverageVec Q F = 0 := by
      funext i
      have hint : ∫ y in cubeSet Q, F y i = 0 := by
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
        intro y hy
        have := hzero y (Set.disjoint_left.mp hdisj hy)
        rw [this]
        rfl
      rw [cubeAverageVec, cubeAverage, hint, mul_zero]
      rfl
    rw [hvanish, norm_zero]
    exact mul_nonneg hA (three_rpow_nonneg _)
  · rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨x, hxQ, hxm⟩ := hdisj
    obtain ⟨R, hR, hxR⟩ :=
      exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := originCube d m) (x := x)
        (n := (m - Q.scale).toNat) hxm
    have hRscale : R.scale = m - (((m - Q.scale).toNat : ℤ)) := by
      have := scale_eq_sub_of_mem_descendantsAtDepth hR
      simpa using! this
    have hQscale : Q.scale = m - (((m - Q.scale).toNat : ℤ)) := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hQR : Q = R := eq_of_scale_eq_of_mem_of_mem (by rw [hQscale, hRscale]) hxQ hxR
    rw [hQR]
    exact hdesc _ R hR

end Box

end

end Algsuperdiff.Section4.Provider.Homogenization
