/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilityGeometry
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Subadditivity

/-!
# OffGridStabilitySubadditivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Countable subadditivity of the response functional

> Then, by subadditivity and `(e.bound.one.cube.by.lambdas)`,
> `|σ_*^{-1}(U;a)| ≤ ∑_{n=-∞}^0 ∑_{z ∈ 𝒢_n(U)} (|□_n| / |U|) |σ_*^{-1}(z+□_n;a)|`

for an arbitrary domain `U ⊆ □_0` and the greedy family `𝒢_n(U)`.  That is a
**countably infinite** subadditivity over a family of cubes of unboundedly many
scales inside an arbitrary domain.

CoarseGraining's subadditivity surface stops strictly short of it.  Its public
form (`Ch02.ResponseSubadditivityAndScalingTheory.responseJ_subadditive`) is
indexed by a `Ch02.DomainPartition`, whose `triadic_realization` field *forces*

* a `Fintype` cell index, and
* cells enumerating `descendantsAtDepth root depth` for one root cube and one
  common depth — an equal-depth exact triadic partition of a **grid** cube.

Neither the countability nor the multi-scale family nor the off-grid parent can
be expressed there.  This module proves the missing inequality directly on
CoarseGraining's set-level `Homogenization.ResponseJ`, for an arbitrary
countable a.e. partition of an arbitrary open set, and then specialises it to
the maximal-cube family of `OffGridStabilityGeometry.lean`.

## The ingredients used, all public in CoarseGraining

* `Homogenization.responseJValueSet_nonempty`, `responseJValueSet_mem`;
* `Homogenization.scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn`;
* `Homogenization.AHarmonicFunction.restrictOfIsEllipticFieldOn` — restriction of
  an `a`-harmonic function to an open subset, which is what makes one admissible
  field for the big domain admissible for every cell;
* `Homogenization.le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn`;
* `Homogenization.IsEllipticFieldOn.mono`;
* Mathlib's `MeasureTheory.hasSum_integral_iUnion`.

The one genuinely new step is that the *exact* finite partition identity
CoarseGraining uses (`volumeAverage` over `descendantsAverage`) is replaced by
the countable `hasSum_integral_iUnion`, which needs only pairwise disjointness,
measurability and an a.e. cover.

## Main results

* `responseJ_le_tsum_of_countable_cover` — the countable subadditivity.
* `responseJ_offGridCube_le_tsum_maximalCubes` — the same across the maximal
  grid cubes of an off-grid cube, in the `∑ |Q|/|V|` normalization of the
  printed display.

## References

* ABK26, `l.lambdas.stability`.
* CoarseGraining, `Homogenization/CoarseGraining/Definitions.lean`
  (`ResponseJ`),
  `Homogenization/CoarseGraining/ResponseIdentities/Foundations/Ellipticity.lean`,
  `Homogenization//Harmonic.lean`,
  `Homogenization/Book/Ch02/Theorems/SubadditivityScalingDefinitions.lean` (the
  finite-partition ceiling this module lifts).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. Countable subadditivity of `ResponseJ` -/

/-- **Countable subadditivity of the response functional.**

If the open set `V` is covered, up to a null set, by countably many pairwise
disjoint open subsets `cell i`, then the response of `V` is at most the
`|cell i| / |V|`-weighted sum of any majorant of the responses of the cells.

This is the countable, multi-scale, off-grid replacement for CoarseGraining's
`DomainPartition`-indexed subadditivity, whose `triadic_realization` field
forces a finite equal-depth partition of a grid cube. -/
theorem responseJ_le_tsum_of_countable_cover {ι : Type} [Countable ι]
    {V : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ} {p q : Vec d}
    (hVopen : IsOpen V) (hVtop : volume V < ⊤) (hVpos : (volume V).toReal ≠ 0)
    (hEll : IsEllipticFieldOn lam Lam V a)
    (cell : ι → Set (Vec d)) (hopen : ∀ i, IsOpen (cell i))
    (hmeas : ∀ i, MeasurableSet (cell i)) (hsub : ∀ i, cell i ⊆ V)
    (hdisj : Pairwise (Function.onFun Disjoint cell))
    (hcelltop : ∀ i, volume (cell i) < ⊤) (hcellpos : ∀ i, (volume (cell i)).toReal ≠ 0)
    (hcover : volume (V \ ⋃ i, cell i) = 0)
    (B : ι → ℝ) (hB : ∀ i, ResponseJ (cell i) p q a ≤ B i)
    (hsummable : Summable fun i => (volume (cell i)).toReal * B i) :
    ResponseJ V p q a ≤ (volume V).toReal⁻¹ * ∑' i, (volume (cell i)).toReal * B i := by
  classical
  have : Fact (volume V < ⊤) := ⟨hVtop⟩
  have hVinvpos : (0 : ℝ) ≤ (volume V).toReal⁻¹ := by positivity
  have hae : V =ᵐ[volume] ⋃ i, cell i := by
    refine MeasureTheory.ae_eq_set.2 ⟨hcover, ?_⟩
    have hsub' : (⋃ i, cell i) \ V = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro x ⟨hxU, hxV⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxU
      exact hxV (hsub i hxi)
    rw [hsub']
    simp
  refine csSup_le (responseJValueSet_nonempty V p q a) ?_
  rintro m ⟨u, rfl⟩
  set f : Vec d → ℝ := scalarResponseIntegrand V a p q u with hf
  have hfint : IntegrableOn f V volume :=
    scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
  have hfintU : IntegrableOn f (⋃ i, cell i) volume :=
    (MeasureTheory.integrableOn_congr_set_ae hae).1 hfint
  have hsum : HasSum (fun i => ∫ x in cell i, f x ∂volume)
      (∫ x in ⋃ i, cell i, f x ∂volume) :=
    MeasureTheory.hasSum_integral_iUnion hmeas hdisj hfintU
  have hcellLe : ∀ i, ∫ x in cell i, f x ∂volume ≤ (volume (cell i)).toReal * B i := by
    intro i
    have : Fact (volume (cell i) < ⊤) := ⟨hcelltop i⟩
    have hEll_i : IsEllipticFieldOn lam Lam (cell i) a := hEll.mono (hmeas i) (hsub i)
    set ui : AHarmonicFunction a (cell i) :=
      u.restrictOfIsEllipticFieldOn hVopen (hopen i) (hsub i) hEll_i with hui
    have hcongr : f = scalarResponseIntegrand (cell i) a p q ui := by
      funext x
      simp only [hf, hui, scalarResponseIntegrand,
        AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn, H1Function.restrict]
    have hmem : volumeAverage (cell i) (scalarResponseIntegrand (cell i) a p q ui) ∈
        responseJValueSet (cell i) p q a := responseJValueSet_mem (cell i) p q a ui
    have hle : volumeAverage (cell i) f ≤ ResponseJ (cell i) p q a := by
      rw [hcongr]
      exact le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hEll_i
        (hcellpos i) p q hmem
    have hintEq : ∫ x in cell i, f x ∂volume =
        (volume (cell i)).toReal * volumeAverage (cell i) f := by
      rw [volumeAverage, ← mul_assoc, mul_inv_cancel₀ (hcellpos i), one_mul]
    rw [hintEq]
    have hvolnn : (0 : ℝ) ≤ (volume (cell i)).toReal := ENNReal.toReal_nonneg
    exact mul_le_mul_of_nonneg_left (hle.trans (hB i)) hvolnn
  have hsumLe : ∑' i, ∫ x in cell i, f x ∂volume ≤ ∑' i, (volume (cell i)).toReal * B i :=
    Summable.tsum_le_tsum hcellLe hsum.summable hsummable
  have hintV : ∫ x in V, f x ∂volume = ∑' i, ∫ x in cell i, f x ∂volume := by
    rw [MeasureTheory.setIntegral_congr_set hae]
    exact hsum.tsum_eq.symm
  rw [volumeAverage, hintV]
  exact mul_le_mul_of_nonneg_left hsumLe hVinvpos

/-! ## 2. The off-grid specialisation -/

variable [NeZero d]

/-- The open realizations of the maximal cubes cover the off-grid cube up to a
null set: the discarded set is the countable union of the cubes' boundaries. -/
theorem volume_offGridCube_diff_iUnion_openCubeSet (w : Vec d) (P : TriadicCube d) :
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
  refine measure_iUnion_null ?_
  intro Q
  exact volume_cubeBoundary_eq_zero _

/-- **The printed display, formalized.**

For an arbitrary real translate `w + □_k` of a triadic cube, the response of the
off-grid cube is at most the `|Q| / |w + □_k|`-weighted sum of any majorant of
the responses of its maximal grid subcubes.  This is
`|σ_*^{-1}(U)| ≤ ∑_n ∑_{z ∈ 𝒢_n(U)} (|□_n|/|U|) |σ_*^{-1}(z+□_n)|` at the level
of the response functional itself.

`B` and its two obligations are conditional A, per the disclosure in the module
docstring. -/
theorem responseJ_offGridCube_le_tsum_maximalCubes {w : Vec d} {P : TriadicCube d}
    {a : CoeffField d} {lam Lam : ℝ} {p q : Vec d}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) a)
    (B : TriadicCube d → ℝ)
    (hB : ∀ Q : maximalCubes (offGridCube w P),
      ResponseJ (openCubeSet (Q : TriadicCube d)) p q a ≤ B (Q : TriadicCube d))
    (hsummable : Summable fun Q : maximalCubes (offGridCube w P) =>
      cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d)) :
    ResponseJ (offGridCube w P) p q a ≤
      (cubeVolume P)⁻¹ *
        ∑' Q : maximalCubes (offGridCube w P),
          cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d) := by
  classical
  have hopenCube : ∀ R : TriadicCube d, IsOpen (openCubeSet R) := by
    intro R
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have hVtop : volume (offGridCube w P) < ⊤ :=
    lt_of_le_of_ne le_top (volume_offGridCube_ne_top w P)
  have hVreal : (volume (offGridCube w P)).toReal = cubeVolume P :=
    volume_offGridCube_toReal w P
  have hVpos : (volume (offGridCube w P)).toReal ≠ 0 := by
    rw [hVreal]
    exact (cubeVolume_pos P).ne'
  have hcellreal : ∀ Q : maximalCubes (offGridCube w P),
      (volume (openCubeSet (Q : TriadicCube d))).toReal = cubeVolume (Q : TriadicCube d) :=
    fun Q => volume_openCubeSet_toReal _
  have key := responseJ_le_tsum_of_countable_cover (ι := maximalCubes (offGridCube w P))
    (V := offGridCube w P) (a := a) (lam := lam) (Lam := Lam) (p := p) (q := q)
    (isOpen_offGridCube w P) hVtop hVpos hEll
    (fun Q => openCubeSet (Q : TriadicCube d))
    (fun Q => hopenCube _)
    (fun Q => measurableSet_openCubeSet _)
    (fun Q => by
      refine subset_trans (openCubeSet_subset_cubeSet _) ?_
      exact Q.2.1)
    (by
      intro Q R hne
      refine Disjoint.mono (openCubeSet_subset_cubeSet _) (openCubeSet_subset_cubeSet _) ?_
      exact disjoint_cubeSet_of_maximalCubeIn Q.2 R.2 (fun h => hne (Subtype.ext h)))
    (fun Q => lt_of_le_of_ne le_top (volume_openCubeSet_lt_top _).ne)
    (fun Q => by
      rw [hcellreal Q]
      exact (cubeVolume_pos _).ne')
    (volume_offGridCube_diff_iUnion_openCubeSet w P)
    (fun Q => B Q) hB
    (by
      refine hsummable.congr ?_
      intro Q
      rw [hcellreal Q])
  have hrw : (∑' Q : maximalCubes (offGridCube w P),
      (volume (openCubeSet (Q : TriadicCube d))).toReal * B (Q : TriadicCube d)) =
      ∑' Q : maximalCubes (offGridCube w P),
        cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d) := by
    refine tsum_congr ?_
    intro Q
    rw [hcellreal Q]
  rw [hVreal, hrw] at key
  exact key

end

end Algsuperdiff.Section4.Provider.ExcessDecay
