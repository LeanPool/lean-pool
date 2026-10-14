/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeMesh
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationOscillationBridge

/-!
# LocalizationFluctuationEighthMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cell eighth-moment envelope of the oscillation cell

`LocalizationFluctuationGammaFold.gridFourthMoment_mesoCubeGrid_le_interior_add_of_eighthMoment`
closes the boundary remainder against an **eighth**-moment grid average of the
same per-cell quantity, and
`LocalizationFluctuationGammaFold.exists_gamma_threshold_mesh_boundary` then
puts that remainder below `gamma^100`.  What the consumer still owes is the
*spatial* half of that envelope: a pointwise (in the sample) bound of the
eighth power of the oscillation cell of `e.nablaw.oscillations` by the cell
average of `|u|^8`, whose grid average the mesh tiling identity of
`LocalizationGrid` turns into the single quantity `fint_{cu_K} |u|^8` that
`e.nablaw.in.L.eight` controls.

This module proves that spatial half.  Two elementary steps do the work, at the
constant `1` in both.

* **Variance is below the second moment.**  `meanSquareOscillationVecOn` centres
  the field at its own window average; dropping the centring costs nothing:
  `volumeAverage_sub_volumeAverage_sq_le`.  This replaces the manuscript's
  implicit triangle inequality and avoids its `2^7`.
* **Jensen twice.**  `(fint g)^4 <= fint g^4` for `g = |u|^2 >= 0`, by two
  applications of Cauchy--Schwarz against the constant `1`
  (`sq_volumeAverage_le_volumeAverage_sq`).  This is the same normalized
  Cauchy--Schwarz `LocalizationEnvelopeMesh` uses at one level, restated on a
  general set of finite positive volume so it can be iterated.

`meshOscillationCell_pow_eight_le_volumeAverage` is the composed statement, and
`volumeAverage_vecNormSq_pow_four_eq_cubeEuclideanLpNorm_eight_pow_eight` is the
dictionary that turns its right-hand side into the eighth power of the
volume-normalized Euclidean `L^8` norm -- verbatim the left-hand side of
`Corrector.FreshShellL8.exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow`.

## Binders

`hsc` -- the cell is read at its own scale, which only *names* `n`; and the
integrability families, which are the standing spatial integrability of the
moments being formed (all four follow from the `L^8` membership of `|u|` on the
cube, which is what `e.nablaw.in.L.eight` supplies).  They are conditional A
obligations discharged by the caller.  No smallness, no moment, no
measurability in the sample, and nothing about the corrector, the coefficient
field or the sample space occurs.

## Scope

There is no `sorry`.

## References

* ABK26, `e.nablaw.oscillations`, `e.lower.bound.oscillations`,
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Cauchy--Schwarz against the constant, on a general window -/

/-- Cauchy--Schwarz against `1` on a set of finite positive volume:
`(int_V g)^2 <= |V| int_V g^2`.

on the volume data and the two integrabilities. -/
theorem sq_setIntegral_le_volume_mul_setIntegral_sq' {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {g : Vec d → ℝ}
    (hg : IntegrableOn g V volume) (hg2 : IntegrableOn (fun x => g x ^ 2) V volume) :
    (∫ x in V, g x ∂volume) ^ 2 ≤
      (volume V).toReal * ∫ x in V, g x ^ 2 ∂volume := by
  exact sq_setIntegral_le_volume_mul_setIntegral_sq hfin hpos hg hg2

/-- **Normalized Cauchy--Schwarz on a general window.**  The square of the window
average is below the window average of the square; the constant is `1`.  Stated
on a general set so that it can be iterated, which is what the eighth moment
needs. -/
theorem sq_volumeAverage_le_volumeAverage_sq {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {g : Vec d → ℝ}
    (hg : IntegrableOn g V volume) (hg2 : IntegrableOn (fun x => g x ^ 2) V volume) :
    (volumeAverage V g) ^ 2 ≤ volumeAverage V (fun x => g x ^ 2) := by
  have hcs := sq_setIntegral_le_volume_mul_setIntegral_sq' hfin hpos hg hg2
  change ((volume V).toReal⁻¹ * ∫ x in V, g x ∂volume) ^ 2 ≤
    (volume V).toReal⁻¹ * ∫ x in V, g x ^ 2 ∂volume
  rw [mul_pow]
  calc ((volume V).toReal⁻¹) ^ 2 * (∫ x in V, g x ∂volume) ^ 2
      ≤ ((volume V).toReal⁻¹) ^ 2 *
          ((volume V).toReal * ∫ x in V, g x ^ 2 ∂volume) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (volume V).toReal⁻¹ * ∫ x in V, g x ^ 2 ∂volume := by field_simp

/-- **Variance is below the second moment.**  Dropping the centring in
`meanSquareOscillationVecOn` costs nothing. -/
theorem volumeAverage_sub_volumeAverage_sq_le {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {g : Vec d → ℝ}
    (hg : IntegrableOn g V volume) (hg2 : IntegrableOn (fun x => g x ^ 2) V volume) :
    volumeAverage V (fun x => (g x - volumeAverage V g) ^ 2) ≤
      volumeAverage V (fun x => g x ^ 2) := by
  set m : ℝ := (volume V).toReal with hmdef
  set I : ℝ := ∫ x in V, g x ∂volume with hIdef
  set J : ℝ := ∫ x in V, g x ^ 2 ∂volume with hJdef
  have hmne : m ≠ 0 := ne_of_gt hpos
  have ht : volumeAverage V g = m⁻¹ * I := rfl
  set t : ℝ := m⁻¹ * I with htdef
  have hconst : IntegrableOn (fun _ : Vec d => t ^ 2) V volume := integrableOn_const hfin
  have hexp : (fun x => (g x - t) ^ 2)
      = fun x => g x ^ 2 + (-(2 * t) * g x + t ^ 2) := by
    funext x
    ring
  have hint2 : IntegrableOn (fun x => -(2 * t) * g x + t ^ 2) V volume :=
    (hg.const_mul (-(2 * t))).add hconst
  have hcalc : ∫ x in V, (g x - t) ^ 2 ∂volume = J + (-(2 * t) * I + t ^ 2 * m) := by
    rw [hexp, integral_add hg2 hint2, integral_add (hg.const_mul (-(2 * t))) hconst,
      integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul]
    ring
  have hgoal : volumeAverage V (fun x => (g x - t) ^ 2) = m⁻¹ * J - t ^ 2 := by
    change m⁻¹ * ∫ x in V, (g x - t) ^ 2 ∂volume = m⁻¹ * J - t ^ 2
    rw [hcalc, htdef]
    field_simp
    ring
  rw [ht, hgoal]
  have hsq : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  change m⁻¹ * J - t ^ 2 ≤ m⁻¹ * J
  linarith

/-! ## The oscillation cell against the window energy -/

/-- **The mean-square oscillation is below the mean-square size.**  Componentwise
`volumeAverage_sub_volumeAverage_sq_le`, summed over the coordinates.

on the volume data and the coordinate integrabilities. -/
theorem meanSquareOscillationVecOn_le_volumeAverage_vecNormSq {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) (u : Vec d → Vec d)
    (hcoord : ∀ k : Fin d, IntegrableOn (fun x => u x k) V volume)
    (hcoordsq : ∀ k : Fin d, IntegrableOn (fun x => (u x k) ^ 2) V volume) :
    Book.Ch01.meanSquareOscillationVecOn V u ≤
      volumeAverage V (fun x => vecNormSq (u x)) := by
  classical
  have hterm : ∀ k : Fin d,
      Book.Ch01.meanSquareDeviationOn V (fun x => u x k) (volumeAverageVec V u k) ≤
        volumeAverage V (fun x => (u x k) ^ 2) := by
    intro k
    have hk : volumeAverageVec V u k = volumeAverage V (fun x => u x k) := rfl
    rw [Book.Ch01.meanSquareDeviationOn, hk]
    exact volumeAverage_sub_volumeAverage_sq_le hfin hpos (hcoord k) (hcoordsq k)
  have hsum : ∑ k : Fin d, volumeAverage V (fun x => (u x k) ^ 2) =
      volumeAverage V (fun x => vecNormSq (u x)) := by
    unfold volumeAverage vecNormSq vecDot
    rw [← Finset.mul_sum]
    congr 1
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun k _ => by simpa [pow_two] using! (hcoordsq k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  calc Book.Ch01.meanSquareOscillationVecOn V u
      = ∑ k : Fin d,
          Book.Ch01.meanSquareDeviationOn V (fun x => u x k) (volumeAverageVec V u k) := rfl
    _ ≤ ∑ k : Fin d, volumeAverage V (fun x => (u x k) ^ 2) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = volumeAverage V (fun x => vecNormSq (u x)) := hsum

/-! ## The volume data of an open triadic cube -/

/-- Unconditional: an open triadic cube has finite volume. -/
theorem volume_openCubeSet_ne_top' (R : TriadicCube d) : volume (openCubeSet R) ≠ ⊤ := by
  rw [← openCubeAtScale_triadicCubeShift_eq_openCubeSet R]
  exact Corrector.volume_openCubeAtScale_ne_top _ _

/-- Unconditional: an open triadic cube has positive volume. -/
theorem volume_openCubeSet_toReal_pos' (R : TriadicCube d) :
    0 < (volume (openCubeSet R)).toReal := by
  rw [← openCubeAtScale_triadicCubeShift_eq_openCubeSet R]
  exact Corrector.volume_openCubeAtScale_toReal_pos _ _

/-! ## The eighth-moment envelope of the oscillation cell -/

/-- **The pointwise Jensen step of the eighth-moment envelope.**  At the cell's
own scale the eighth power of the oscillation cell of `e.nablaw.oscillations` is
below the cell average of `|u|^8`; the constant is `1`.

on the identification `hsc` of the cell's scale and on the five integrability
families -- all consequences of the `L^8` membership of `|u|` on the cube,
which is what `e.nablaw.in.L.eight` supplies.  The volume data of the open cube
is discharged internally. -/
theorem meshOscillationCell_pow_eight_le_volumeAverage {n : ℤ} (R : TriadicCube d)
    (hsc : R.scale = n) (u : Vec d → Vec d)
    (hcoord : ∀ k : Fin d, IntegrableOn (fun x => u x k) (openCubeSet R) volume)
    (hcoordsq : ∀ k : Fin d, IntegrableOn (fun x => (u x k) ^ 2) (openCubeSet R) volume)
    (hsq : IntegrableOn (fun x => vecNormSq (u x)) (openCubeSet R) volume)
    (hfour : IntegrableOn (fun x => vecNormSq (u x) ^ 2) (openCubeSet R) volume)
    (height : IntegrableOn (fun x => (vecNormSq (u x) ^ 2) ^ 2) (openCubeSet R) volume) :
    meshOscillationCell n u R ^ (8 : ℕ) ≤
      volumeAverage (openCubeSet R) (fun x => vecNormSq (u x) ^ (4 : ℕ)) := by
  have hfin : volume (openCubeSet R) ≠ ⊤ := volume_openCubeSet_ne_top' R
  have hpos : 0 < (volume (openCubeSet R)).toReal := volume_openCubeSet_toReal_pos' R
  set V : Set (Vec d) := openCubeSet R with hV
  have hwin : openCubeAtScale (triadicCubeShift R) n = V := by
    rw [hV, ← hsc]
    exact openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have hoscnn : (0 : ℝ) ≤ Book.Ch01.meanSquareOscillationVecOn V u := by
    have hterm : ∀ k : Fin d,
        (0 : ℝ) ≤
          Book.Ch01.meanSquareDeviationOn V (fun x => u x k) (volumeAverageVec V u k) := by
      intro k
      rw [Book.Ch01.meanSquareDeviationOn]
      exact volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
        fun _ _ => sq_nonneg _
    have hexpand : Book.Ch01.meanSquareOscillationVecOn V u =
        ∑ k : Fin d,
          Book.Ch01.meanSquareDeviationOn V (fun x => u x k) (volumeAverageVec V u k) := rfl
    rw [hexpand]
    exact Finset.sum_nonneg fun k _ => hterm k
  have hpow : meshOscillationCell n u R ^ (8 : ℕ) =
      (Book.Ch01.meanSquareOscillationVecOn V u) ^ (4 : ℕ) := by
    rw [meshOscillationCell, hwin,
      show Real.sqrt (Book.Ch01.meanSquareOscillationVecOn V u) ^ (8 : ℕ) =
        ((Real.sqrt (Book.Ch01.meanSquareOscillationVecOn V u)) ^ 2) ^ (4 : ℕ) by ring,
      Real.sq_sqrt hoscnn]
  have hosc := meanSquareOscillationVecOn_le_volumeAverage_vecNormSq hfin hpos u hcoord
    hcoordsq
  have hgnn : (0 : ℝ) ≤ volumeAverage V (fun x => vecNormSq (u x)) :=
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      fun _ _ => vecNormSq_nonneg _
  have hstep1 : (Book.Ch01.meanSquareOscillationVecOn V u) ^ (4 : ℕ) ≤
      (volumeAverage V (fun x => vecNormSq (u x))) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hoscnn hosc 4
  have hcs1 : (volumeAverage V (fun x => vecNormSq (u x))) ^ 2 ≤
      volumeAverage V (fun x => vecNormSq (u x) ^ 2) :=
    sq_volumeAverage_le_volumeAverage_sq hfin hpos hsq hfour
  have hcs2 : (volumeAverage V (fun x => vecNormSq (u x) ^ 2)) ^ 2 ≤
      volumeAverage V (fun x => (vecNormSq (u x) ^ 2) ^ 2) :=
    sq_volumeAverage_le_volumeAverage_sq hfin hpos hfour height
  have hmid : (0 : ℝ) ≤ volumeAverage V (fun x => vecNormSq (u x) ^ 2) :=
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      fun _ _ => sq_nonneg _
  have hchain : (volumeAverage V (fun x => vecNormSq (u x))) ^ (4 : ℕ) ≤
      volumeAverage V (fun x => (vecNormSq (u x) ^ 2) ^ 2) := by
    calc (volumeAverage V (fun x => vecNormSq (u x))) ^ (4 : ℕ)
        = ((volumeAverage V (fun x => vecNormSq (u x))) ^ 2) ^ 2 := by ring
      _ ≤ (volumeAverage V (fun x => vecNormSq (u x) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hcs1 2
      _ ≤ volumeAverage V (fun x => (vecNormSq (u x) ^ 2) ^ 2) := hcs2
  have hfun : (fun x => (vecNormSq (u x) ^ 2) ^ 2) =
      fun x => vecNormSq (u x) ^ (4 : ℕ) := by
    funext x
    ring
  rw [hpow, ← hfun]
  exact le_trans hstep1 hchain

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
