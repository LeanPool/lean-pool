/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryOdd
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionAssembly

/-!
# OneStepOddValue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The value-level odd pinning of the boundary competitor

`OneStepBoundaryOdd` runs the boundary branch through the odd class under the
*pointwise everywhere* hypothesis `oddExtend x m k V = V` on the competitor.
The proved one-met-face transfer
(`OddReflectionAssembly.isWeaklyHarmonicOn_reflectedWindow_of_meets{Upper,Lower}Face`)
pins only the **gradient** of the reflected `H¹` datum, and Weyl's lemma
(`OneStepSchauderComposeBoundary.exists_classicalCompetitor_reflectedWindow`)
returns a classical competitor only up to a null set.  This module closes that
interface gap.

## Three observations

* **Oddness is a reflection identity, not a fold identity.**  In the one-met-face
  regime the fold `windowFold` acts only in the met coordinate, where it is the
  identity on the window side and the face reflection `coordFaceReflection a i`
  beyond it, with the matching sign.  Hence *any* `O` with
  `O ∘ coordFaceReflection a i = -O` satisfies `oddExtend x m k O = O` off the
  interface hyperplane `{yᵢ = a}` — no membership hypothesis at all
  (`oddExtend_eq_self_of_faceOdd_upper`).  The interface is Lebesgue-null, so the
  identity holds almost everywhere.

* **Almost-everywhere suffices.**  `normalizedL2On` is an integral, so it is an
  almost-everywhere invariant (`normalizedL2On_congr_ae`); the odd bridge
  therefore runs verbatim from `oddExtend x m k O =ᵐ O` and `V =ᵐ O + c₀`.

* **The additive constant is free.**  The gradient pinning determines the value of
  the reflected `H¹` datum only up to an additive constant (two `H¹` functions
  with the same weak gradient on a connected open set differ by a constant), and
  a constant is *not* in the odd class.  It does not have to be: a constant is an
  admissible affine competitor, so the whole chain runs with `V =ᵐ O + c₀` and the
  odd affine datum read at the shifted intercept `c - c₀`.  Taking `c₀ = 0`
  recovers `OneStepBoundaryOdd` verbatim.

## What is delivered

`affineExcessRaw_reflectedWindow_le_odd_ae` and
`exists_gradientHolder_boundary_odd_ae` — the almost-everywhere twins's odd
bridge and boundary producer — together with the pointwise atom
`oddExtend_eq_self_of_faceOdd_upper` and its lower-face twin, and the
face-oddness of the one-face odd extension `oddFaceExtend` (which is exactly
the value-level shape of the object whose gradient the proved transfer pins).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `normalizedL2On` is an almost-everywhere invariant -/

/-- The volume-normalized `L²` seminorm only sees the almost-everywhere class of
its argument: it is a set integral.  No measurability and no finiteness of the
window is needed. -/
theorem normalizedL2On_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) :
    normalizedL2On W f = normalizedL2On W g := by
  have hint : ∫ y in W, f y ^ 2 ∂volume = ∫ y in W, g y ^ 2 ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  simp only [normalizedL2On, HCPolySupport.volumeAverage, hint]

/-- The affine distance, unfolded to the seminorm of the affine residual. -/
theorem affineDistOn_eq_normalizedL2On (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) :
    affineDistOn W u c g = normalizedL2On W (fun y => u y - affineEval c g y) := rfl

/-- The affine distance is an almost-everywhere invariant. -/
theorem affineDistOn_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) (c : ℝ) (A : Vec d) :
    affineDistOn W f c A = affineDistOn W g c A := by
  refine normalizedL2On_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-! ## 2. Face oddness implies the fold identity -/

/-- **The interface atom, upper face.**  In the one-met-face regime the partial
odd extension `oddExtend` fixes every function which is odd about the met face,
off the interface hyperplane.  The met face supplies the fold in its own
coordinate; the unmet coordinates are untouched. -/
theorem oddExtend_eq_self_of_faceOdd_upper {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    {O : Vec d → ℝ}
    (hO : ∀ z, O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z)
    {y : Vec d} (hne : y i ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    oddExtend x m k O y = O y := by
  have hsign : windowFoldSign x m k y = foldSignCoord x m k i (y i) := by
    rw [windowFoldSign]
    refine Finset.prod_eq_single i (fun j _ hji => ?_) (fun h => ?_)
    · exact foldSignCoord_of_unmet (hother j hji).1 (hother j hji).2 (y j)
    · exact absurd (Finset.mem_univ i) h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hfold : windowFold x m k y = y := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [windowFold_apply, foldCoord_of_meetsUpperFace hup,
          min_eq_left (by linarith only [hlt])]
      · exact foldCoord_of_unmet (hother j hj).1 (hother j hj).2 (y j)
    rw [oddExtend_apply, hfold, hsign, foldSignCoord_of_meetsUpperFace hup,
      ite_eq_right (not_lt.2 hlt.le), one_mul]
  · have hfold : windowFold x m k y
        = coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [windowFold_apply, foldCoord_of_meetsUpperFace hup,
          min_eq_right (by linarith only [hgt]), coordFaceReflection_apply, ite_eq_left rfl]
        ring
      · rw [windowFold_apply, foldCoord_of_unmet (hother j hj).1 (hother j hj).2 (y j),
          coordFaceReflection_apply, ite_eq_right hj]
    rw [oddExtend_apply, hfold, hsign, foldSignCoord_of_meetsUpperFace hup,
      ite_eq_left hgt, hO y]
    ring

/-- **The interface is null.**  The pointwise atom therefore holds almost
everywhere, upper face. -/
theorem oddExtend_ae_eq_self_of_faceOdd_upper {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    {O : Vec d → ℝ}
    (hO : ∀ z, O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z) :
    oddExtend x m k O =ᵐ[volume] O := by
  refine MeasureTheory.ae_iff.2 (measure_mono_null ?_
    (volume_coordLevel_eq_zero i ((1 / 2 : ℝ) * (3 : ℝ) ^ m)))
  intro y hy
  by_contra hne
  exact hy (oddExtend_eq_self_of_faceOdd_upper hup hother hO hne)

/-! ## 3. The odd bridge, almost everywhere -/

/-- **The odd bridge, almost-everywhere form.**  For a competitor which agrees
almost everywhere on the doubled window with `O + c₀`, where `O` is fixed by the
partial odd extension almost everywhere, and an affine datum whose *shifted*
intercept `c - c₀` lies in the odd class, the excess minimum on the doubled
window is at most `2^d` times the affine distance on `U₂`.

With `c₀ = 0` and a pointwise-odd `V` this is
the pointwise odd-class excess bound on the doubled window. -/
theorem affineExcessRaw_reflectedWindow_le_odd_ae {m k : ℤ} {x : Vec d} (hkm : k < m)
    {V O : Vec d → ℝ} {c₀ : ℝ}
    (hVO : V =ᵐ[volume.restrict (reflectedWindow x m k)] fun y => O y + c₀)
    (hOodd : oddExtend x m k O =ᵐ[volume.restrict (reflectedWindow x m k)] O)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m k (c - c₀) A)
    (hRpos : 0 < (volume (reflectedWindow x m k)).toReal)
    (hUpos : 0 < (volume (truncatedWindow x m k)).toReal)
    (hOR : MemLp O 2 (volume.restrict (reflectedWindow x m k))) :
    affineExcessRaw (reflectedWindow x m k) V
      ≤ 2 ^ d * affineDistOn (truncatedWindow x m k) V (c - vecDot A x) A := by
  set aff : Vec d → ℝ := affineEval (c - c₀ - vecDot A x) A with haffdef
  have haffLift : aff = affineLift x (c - c₀) A := by
    rw [haffdef]
    exact affineEval_eq_affineLift x (c - c₀) A
  set f : Vec d → ℝ := fun y => O y - aff y with hfdef
  -- the shifted affine datum is fixed by the odd extension
  have hoddaff : oddExtend x m k aff = aff := by
    rw [haffLift]
    exact oddExtend_affineLift hodd
  -- `f` is fixed by the odd extension almost everywhere on the doubled window
  have hfodd : oddExtend x m k f =ᵐ[volume.restrict (reflectedWindow x m k)] f := by
    have hsub : oddExtend x m k f = fun y => oddExtend x m k O y - aff y := by
      rw [hfdef, oddExtend_sub, hoddaff]
    rw [hsub]
    filter_upwards [hOodd] with y hy
    rw [hy]
  -- the competitor's affine residual is `f`, almost everywhere on both windows
  have hVf : (fun y => V y - affineEval (c - vecDot A x) A y)
      =ᵐ[volume.restrict (reflectedWindow x m k)] f := by
    filter_upwards [hVO] with y hy
    show V y - affineEval (c - vecDot A x) A y = O y - aff y
    rw [hy, haffdef]
    simp only [affineEval]
    ring
  have hVfU : (fun y => V y - affineEval (c - vecDot A x) A y)
      =ᵐ[volume.restrict (truncatedWindow x m k)] f :=
    hVf.filter_mono (MeasureTheory.ae_mono
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m k) le_rfl))
  -- the `L²` data
  have hfR : MemLp f 2 (volume.restrict (reflectedWindow x m k)) := by
    rw [hfdef, haffdef]
    exact hOR.sub (memLp_affineEval_reflectedWindow x m k (c - c₀ - vecDot A x) A)
  have hfU : MemLp f 2 (volume.restrict (truncatedWindow x m k)) :=
    hfR.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m k) le_rfl)
  have hoddfR : MemLp (oddExtend x m k f) 2 (volume.restrict (reflectedWindow x m k)) :=
    hfR.ae_eq hfodd.symm
  have hkey := normalizedL2On_oddExtend_le x hkm f hRpos hUpos hoddfR hfU
  have hbridge : normalizedL2On (reflectedWindow x m k) f
      ≤ 2 ^ d * normalizedL2On (truncatedWindow x m k) f := by
    rw [normalizedL2On_congr_ae hfodd.symm]
    exact hkey
  calc affineExcessRaw (reflectedWindow x m k) V
      ≤ affineDistOn (reflectedWindow x m k) V (c - vecDot A x) A :=
        affineExcessRaw_le_affineDistOn _ _ _ _
    _ = normalizedL2On (reflectedWindow x m k) f := normalizedL2On_congr_ae hVf
    _ ≤ 2 ^ d * normalizedL2On (truncatedWindow x m k) f := hbridge
    _ = 2 ^ d * affineDistOn (truncatedWindow x m k) V (c - vecDot A x) A := by
        rw [affineDistOn_eq_normalizedL2On, normalizedL2On_congr_ae hVfU]

/-! ## 4. The boundary producer, almost everywhere -/

/-- **The Schauder gradient-Hölder estimate, boundary branch — the producer from an
almost-everywhere odd competitor.**

The almost-everywhere twin of
the pointwise odd-class producer: the competitor is only
required to agree almost everywhere on the doubled window with `O + c₀` for an
almost-everywhere odd `O`, which is exactly what Weyl's lemma delivers off the
reflected `H¹` datum. -/
theorem exists_gradientHolder_boundary_odd_ae [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    {V O : Vec d → ℝ} {c₀ : ℝ}
    (hVO : V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] fun y => O y + c₀)
    (hOodd : oddExtend x m (n - 2) O
      =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] O)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) (c - c₀) A)
    (hharm : HarmonicOnNhd (V ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2)))) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField V p i) (truncatedWindow x m (n - 3)) volume) ∧
      HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
      HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
      K ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m (n - 2)) V
          + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
  have hintsq : ∀ (c' : ℝ) (g' : Vec d),
      IntegrableOn (fun y => (V y - affineEval c' g' y) ^ 2)
        (reflectedWindow x m (n - 2)) volume :=
    fun c' g' => integrableOn_sub_affineEval_sq_reflectedWindow x hVR c' g'
  obtain ⟨K, hK, hint, hgrad, hhol, hraw⟩ :=
    exists_gradientHolder_boundary_raw hx hmn hharm hintsq
  refine ⟨K, hK, hint, hgrad, hhol, le_trans hraw ?_⟩
  have hRpos : 0 < (volume (reflectedWindow x m (n - 2))).toReal :=
    volume_toReal_reflectedWindow_pos x hx (by omega)
  have hUpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have : IsFiniteMeasure (volume.restrict (reflectedWindow x m (n - 2))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top (volume_reflectedWindow_ne_top x m (n - 2))
  have hOR : MemLp O 2 (volume.restrict (reflectedWindow x m (n - 2))) := by
    refine (hVR.sub (memLp_const c₀)).ae_eq ?_
    filter_upwards [hVO] with y hy
    simp only [Pi.sub_apply]
    rw [hy]
    ring
  have hbridge := affineExcessRaw_reflectedWindow_le_odd_ae (k := n - 2) hmn hVO hOodd
    hodd hRpos hUpos hOR
  have hdist : affineDistOn (truncatedWindow x m (n - 2)) V (c - vecDot A x) A
      = affineExcessRaw (truncatedWindow x m (n - 2)) V + oddClassDefect x m n V c A := by
    rw [oddClassDefect]
    ring
  rw [hdist] at hbridge
  have hscale : (0 : ℝ) < (3 : ℝ) ^ (-(n - 2)) := zpow_pos (by norm_num) _
  have hnormz : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V
      ≤ affineExcess (truncatedWindow x m (n - 2)) V := by
    rw [affineExcess]
    exact mul_le_mul_of_nonneg_right
      (rpow_volume_truncatedWindow_bounds hd x hx (by omega)).1
      (affineExcessRaw_nonneg _ _)
  have hkappa : (0 : ℝ) ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) :=
    mul_nonneg (boundarySchauderConst_nonneg d)
      (Real.rpow_nonneg (zpow_pos (by norm_num) (-n)).le _)
  have hstep : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (reflectedWindow x m (n - 2)) V
      ≤ 2 ^ d * affineExcess (truncatedWindow x m (n - 2)) V
        + 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
    have h1 := mul_le_mul_of_nonneg_left hbridge hscale.le
    have h2 : (3 : ℝ) ^ (-(n - 2)) * (2 ^ d * (affineExcessRaw (truncatedWindow x m (n - 2)) V
          + oddClassDefect x m n V c A))
        = 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V)
          + 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by ring
    rw [h2] at h1
    have h3 : (2 : ℝ) ^ d
          * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V)
        ≤ 2 ^ d * affineExcess (truncatedWindow x m (n - 2)) V :=
      mul_le_mul_of_nonneg_left hnormz (pow_nonneg (by norm_num) d)
    linarith only [h1, h3]
  calc boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (reflectedWindow x m (n - 2)) V)
      ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * (2 ^ d * affineExcess (truncatedWindow x m (n - 2)) V
            + 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A)) :=
        mul_le_mul_of_nonneg_left hstep hkappa
    _ = boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * affineExcess (truncatedWindow x m (n - 2)) V
        + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
        rw [boundaryOddSchauderConst]
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
