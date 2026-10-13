/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBound

/-!
# OneStepEvenBoundFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `(★)`: the even part of the affine minimizer is priced by the excess

This module closes's residue.  For `V` classically harmonic on the doubled
window `R = reflectedWindow x m (n-2)` and **odd about the met face** `{yᵢ =
a}`, `a = (1/2)·3^m`, and `(c, A)` an affine minimizer of `V` on `U₂ =
truncatedWindow x m (n-2)`,

```text
  ‖even part of ℓ*‖_{L²(U₂)} ≤ C(d) · affineExcessRaw U₂ V .                (★)
```

Composed with's reduction `oddClassDefect_oddPart_le_evenPart`, `(★)` says that
the boundary branch's odd-class defect is priced by the **excess itself**: the
producer's second leg folds into its first, and no `[∇h]` leg enters through
the odd class.

## The two steps

1. **The slab comparison** (`normalizedL2On_evenAffinePart_le_of_hessian_bound`).
   Integrating the two-point Taylor estimate of `OneStepEvenBound` over the core
   slab of depth `delta`, and using that an affine function with vanishing
   `i`-slope keeps half of its `L²(U₂)` size on the transversally halved slab
   (`OneStepEvenBoundBox.normalizedL2On_coordBox_affineEval_half_le` — the
   reverse-Chebyshev step), gives

   ```text
     (1/2) N ≤ 3 ((3^{n-2}/delta)^d)^{1/2} E + 3 M delta² ,
   ```

   with `N = ‖e‖_{L²(U₂)}`, `E = ‖V - ℓ*‖_{L²(U₂)}` and `M` any bound for the
   Hessian of `V - ℓ*` on the Taylor box.  The two `f`-terms cost only the volume
   ratio because the deep comparison point is a **translate** of the slab, of the
   same volume, still inside `U₂`.

2. **The choice of `delta`** (`exists_evenAffinePart_le_affineExcessRaw`).  The
   interior Hessian estimate at the doubled window
   (`OneStepEvenBoundHessian.exists_hessian_normalizedL2On_bound`) gives
   `M ≤ C₁ 3^{-2(n-2)} ‖V - ℓ*‖_{L²(R)}`, and the odd bridge of
   `OneStepEvenBoundOdd` gives `‖V - ℓ*‖_{L²(R)} ≤ (2^d + 1)(E + N)` — note the
   even part's `L²(R)` and `L²(U₂)` sizes are *equal*, since it has vanishing
   `i`-slope and the two boxes differ only in the `i`-edge.  Taking
   `delta = t·3^{n-2}` with

   ```text
     t = min (1/16) (1 / (1 + 24 K)) ,   K = C₁ (2^d + 1) ,
   ```

   makes `3 M delta² ≤ (1/8)(E + N)`, and `(★)` closes at
   `C(d) = 8 ((1/t)^d)^{1/2} + 1/3` with no case split.

The constant is coefficient-free but not explicit as a closed form: `C₁` is the
constant of the transplanted interior Hessian estimate, itself produced
existentially.  This is the same convention `schauderConst`/`boundarySchauderConst`
already follow.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The core slab, the deep slab and the translation between them -/

/-- The `i`-th coordinate of the normal displacement `delta·eᵢ`. -/
theorem smul_basisVec_apply (delta : ℝ) (i j : Fin d) :
    (delta • (basisVec i : Vec d)) j = if j = i then delta else 0 := by
  show delta * (basisVec i : Vec d) j = _
  rw [HCPolySupport.basisVec_apply]
  split_ifs <;> ring

/-- **The deep slab is the translate of the core slab.** -/
theorem image_sub_slab (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) :
    (fun z => z - delta • (basisVec i : Vec d)) '' coordBox (slabLo x m k i delta)
        (slabHi x m k i)
      = coordBox (deepLo x m k i delta) (deepHi x m k i delta) := by
  rw [image_sub_coordBox]
  have h1 : (fun j => slabLo x m k i delta j - (delta • (basisVec i : Vec d)) j)
      = deepLo x m k i delta := by
    funext j
    rw [smul_basisVec_apply]
    by_cases hj : j = i
    · subst hj
      rw [slabLo_self, deepLo_self, ite_eq_left rfl]
      ring
    · rw [slabLo_of_ne hj, deepLo_of_ne hj, ite_eq_right hj]
      ring
  have h2 : (fun j => slabHi x m k i j - (delta • (basisVec i : Vec d)) j)
      = deepHi x m k i delta := by
    funext j
    rw [smul_basisVec_apply]
    by_cases hj : j = i
    · subst hj
      rw [slabHi_self, deepHi_self, ite_eq_left rfl]
    · rw [slabHi_of_ne hj, deepHi_of_ne hj, ite_eq_right hj]
      ring
  rw [h1, h2]

/-- **The deep slab's volume from below.**  Every edge is at least `delta`. -/
theorem volume_toReal_coordBox_deep_ge {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    delta ^ d ≤ (volume (coordBox (deepLo x m k i delta) (deepHi x m k i delta))).toReal := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [volume_coordBox_toReal (fun j => (deepLo_lt_deepHi hdelta j).le)]
  have hstep : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      delta ≤ deepHi x m k i delta j - deepLo x m k i delta j := by
    intro j _
    by_cases hj : j = i
    · subst hj
      rw [deepLo_self, deepHi_self]
      linarith only [hdelta]
    · rw [deepLo_of_ne hj, deepHi_of_ne hj]
      linarith only [hdelta16, hdelta]
  calc delta ^ d = ∏ _j : Fin d, delta := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ j : Fin d, (deepHi x m k i delta j - deepLo x m k i delta j) :=
        Finset.prod_le_prod₀ (fun _ _ => hdelta.le) hstep

/-! ## 2. The slab comparison -/

/-- **The slab comparison.**  The even part of the affine minimizer is priced on
the near-face slab by the affine residual and the Hessian remainder. -/
theorem normalizedL2On_evenAffinePart_le_of_hessian_bound [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) {i : Fin d}
    (hup : MeetsUpperFace x m (n - 2) i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j)
    {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))))
    {c : ℝ} {A : Vec d} {delta M : ℝ} (hdelta : 0 < delta)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ (n - 2)) (hM : 0 ≤ M)
    (hharm : ∀ z ∈ coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta),
      HarmonicAt ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc z))
    (hMbound : ∀ z ∈ coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta),
      ‖fderiv ℝ (fderiv ℝ ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M) :
    (1 / 2 : ℝ) * normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A)
      ≤ 3 * Real.sqrt (((3 : ℝ) ^ (n - 2) / delta) ^ d)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
        + 3 * (M * delta ^ 2) := by
  classical
  have hw : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  set f : Vec d → ℝ := fun y => V y - affineEval (c - vecDot A x) A y with hfdef
  set e : Vec d → ℝ := evenAffinePart x m i c A with hedef
  set v0 : Vec d := delta • (basisVec i : Vec d) with hv0def
  set P : Set (Vec d) :=
    coordBox (slabLo x m (n - 2) i delta) (slabHi x m (n - 2) i) with hPdef
  set D : Set (Vec d) :=
    coordBox (deepLo x m (n - 2) i delta) (deepHi x m (n - 2) i delta) with hDdef
  -- the geometry
  have hPU : P ⊆ truncatedWindow x m (n - 2) :=
    coordBox_slab_subset_truncatedWindow hx hmn hup hother hdelta16
  have hDU : D ⊆ truncatedWindow x m (n - 2) :=
    coordBox_deep_subset_truncatedWindow hx hmn hup hother hdelta hdelta16
  have hUR : truncatedWindow x m (n - 2) ⊆ reflectedWindow x m (n - 2) :=
    truncatedWindow_subset_reflectedWindow x m (n - 2)
  have himg : (fun z => z - v0) '' P = D := image_sub_slab x m (n - 2) i delta
  -- the volumes
  have hUvol : (volume (truncatedWindow x m (n - 2))).toReal ≤ ((3 : ℝ) ^ (n - 2)) ^ d :=
    (volume_toReal_truncatedWindow_bounds x hx (by omega)).2
  have hUpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hPvol : delta ^ d ≤ (volume P).toReal := volume_toReal_coordBox_slab_ge hdelta hdelta16
  have hDvol : delta ^ d ≤ (volume D).toReal := volume_toReal_coordBox_deep_ge hdelta hdelta16
  have hdd : (0 : ℝ) < delta ^ d := by positivity
  have hPpos : 0 < (volume P).toReal := lt_of_lt_of_le hdd hPvol
  have hDpos : 0 < (volume D).toReal := lt_of_lt_of_le hdd hDvol
  -- the `L²` data
  have hfR : MemLp f 2 (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hfU : MemLp f 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hfR.mono_measure (Measure.restrict_mono hUR le_rfl)
  have hfP : MemLp f 2 (volume.restrict P) :=
    hfU.mono_measure (Measure.restrict_mono hPU le_rfl)
  have hfD : MemLp f 2 (volume.restrict D) :=
    hfU.mono_measure (Measure.restrict_mono hDU le_rfl)
  have heP : MemLp e 2 (volume.restrict P) := by
    rw [hedef, evenAffinePart]
    exact (memLp_affineEval_truncatedWindow x m (n - 2) _ _).mono_measure
      (Measure.restrict_mono hPU le_rfl)
  have : IsFiniteMeasure (volume.restrict P) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top (volume_coordBox_ne_top _ _)
  have hmp : MeasurePreserving (fun z : Vec d => z - v0) (volume.restrict P)
      (volume.restrict D) := by
    rw [← himg]
    exact (measurePreserving_sub_right (volume : Measure (Vec d)) v0).restrict_image_emb
      (measurableEmbedding_subRight v0) P
  have hftP : MemLp (fun y => f (y - v0)) 2 (volume.restrict P) :=
    hfD.comp_measurePreserving hmp
  -- the dominating function
  set g : Vec d → ℝ := fun y => 2 * |f y| + (|f (y - v0)| + 3 * (M * delta ^ 2)) with hgdef
  have hgmem : MemLp g 2 (volume.restrict P) := by
    rw [hgdef]
    exact (hfP.abs.const_mul 2).add (hftP.abs.add (memLp_const _))
  have hdom : normalizedL2On P e ≤ normalizedL2On P g := by
    refine normalizedL2On_mono_of_abs_le (measurableSet_coordBox _ _) heP.integrable_sq
      hgmem.integrable_sq ?_
    intro y hy
    have hyD0 : y - v0 ∈ D := by
      rw [← himg]
      exact ⟨y, hy, rfl⟩
    have hyD : y - v0 ∈ coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta) :=
      coordBox_deep_subset_taylor hdelta hyD0
    have h := abs_evenAffinePart_le_pointwise (n := n) hVodd hdelta hM hharm hMbound hy hyD
    rw [hgdef]
    show |e y| ≤ 2 * |f y| + (|f (y - v0)| + 3 * (M * delta ^ 2))
    have habs : |f (y - v0)| = |V (y - v0) - affineEval (c - vecDot A x) A (y - v0)| := rfl
    have habs2 : |f y| = |V y - affineEval (c - vecDot A x) A y| := rfl
    rw [habs, habs2]
    linarith only [h]
  -- the three seminorms
  have hg1 : normalizedL2On P g
      ≤ 2 * normalizedL2On P f + (normalizedL2On D f + 3 * (M * delta ^ 2)) := by
    have hsplit : normalizedL2On P g
        ≤ normalizedL2On P (fun y => 2 * |f y|)
          + normalizedL2On P (fun y => |f (y - v0)| + 3 * (M * delta ^ 2)) := by
      rw [hgdef]
      exact normalizedL2On_add_le (hfP.abs.const_mul 2) (hftP.abs.add (memLp_const _))
    have hsplit2 : normalizedL2On P (fun y => |f (y - v0)| + 3 * (M * delta ^ 2))
        ≤ normalizedL2On P (fun y => |f (y - v0)|)
          + normalizedL2On P (fun _ : Vec d => 3 * (M * delta ^ 2)) :=
      normalizedL2On_add_le hftP.abs (memLp_const _)
    have hA : normalizedL2On P (fun y => 2 * |f y|) = 2 * normalizedL2On P f := by
      rw [normalizedL2On_const_mul, normalizedL2On_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hB : normalizedL2On P (fun y => |f (y - v0)|) = normalizedL2On D f := by
      rw [normalizedL2On_abs, normalizedL2On_comp_sub_right, himg]
    have hC : normalizedL2On P (fun _ : Vec d => 3 * (M * delta ^ 2))
        = 3 * (M * delta ^ 2) := by
      rw [normalizedL2On_const_of_toReal_pos hPpos, abs_of_nonneg (by positivity)]
    rw [hA] at hsplit
    rw [hB, hC] at hsplit2
    linarith only [hsplit, hsplit2]
  -- the volume-ratio transfers
  have hratio : ∀ {W : Set (Vec d)}, W ⊆ truncatedWindow x m (n - 2) →
      delta ^ d ≤ (volume W).toReal → 0 < (volume W).toReal →
      normalizedL2On W f
        ≤ Real.sqrt ((((3 : ℝ) ^ (n - 2)) / delta) ^ d)
            * normalizedL2On (truncatedWindow x m (n - 2)) f := by
    intro W hWU hWvol hWpos
    refine le_trans (normalizedL2On_le_of_subset hWU hUpos hWpos hfU.integrable_sq) ?_
    refine mul_le_mul_of_nonneg_right ?_ (normalizedL2On_nonneg _ _)
    refine Real.sqrt_le_sqrt ?_
    rw [div_pow]
    calc (volume (truncatedWindow x m (n - 2))).toReal / (volume W).toReal
        ≤ ((3 : ℝ) ^ (n - 2)) ^ d / (volume W).toReal :=
          div_le_div_of_nonneg_right hUvol hWpos.le
      _ ≤ ((3 : ℝ) ^ (n - 2)) ^ d / delta ^ d :=
          div_le_div_of_nonneg_left (by positivity) hdd hWvol
  have hPtrans := hratio hPU hPvol hPpos
  have hDtrans := hratio hDU hDvol hDpos
  -- the reverse-Chebyshev step
  have hhalf : (1 / 2 : ℝ) * normalizedL2On (truncatedWindow x m (n - 2)) e
      ≤ normalizedL2On P e := by
    rw [hedef, evenAffinePart, truncatedWindow_eq_coordBox, hPdef]
    refine normalizedL2On_coordBox_affineEval_half_le
      (windowLo_lt_windowHi hx hmn hup hother) (slabLo_lt_slabHi hdelta)
      (evenAffineSlope_apply_self i A) ?_ ?_
    · intro j hj
      rw [slabLo_of_ne hj, slabHi_of_ne hj, windowLo_eq_of_ne hother hj,
        windowHi_eq_of_ne hother hj]
      ring
    · intro j hj
      rw [slabLo_of_ne hj, slabHi_of_ne hj, windowLo_eq_of_ne hother hj,
        windowHi_eq_of_ne hother hj]
      linarith only []
  linarith only [hhalf, hdom, hg1, hPtrans, hDtrans]

/-! ## 3. `(★)` -/

/-- **`(★)`, the even-part bound.**  For a competitor odd about the met face and
harmonic on the doubled window, the even part of an affine minimizer on `U₂` is
bounded by a dimensional constant times the excess itself.

Composed with's `oddClassDefect_oddPart_le_evenPart`, this prices the boundary
branch's odd-class defect by the excess: the producer's datum leg folds into
its excess leg. -/
theorem exists_evenAffinePart_le_affineExcessRaw (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i : Fin d) (V : Vec d → ℝ) (c : ℝ)
      (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m →
      MeetsUpperFace x m (n - 2) i →
      (∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j) →
      (∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A)
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  classical
  obtain ⟨CH, hCH0, hCH⟩ := exists_hessian_normalizedL2On_bound d
  set Kp : ℝ := CH * 16 * Real.sqrt ((8 : ℝ) ^ d) with hKpdef
  have hKp0 : 0 ≤ Kp := by
    rw [hKpdef]
    exact mul_nonneg (mul_nonneg hCH0 (by norm_num)) (Real.sqrt_nonneg _)
  set K : ℝ := Kp * ((2 : ℝ) ^ d + 1) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg hKp0 (by positivity)
  have hden : (0 : ℝ) < 1 + 24 * K := by linarith only [hK0]
  set tt : ℝ := min (1 / 16) (1 / (1 + 24 * K)) with httdef
  have htt0 : 0 < tt := by
    rw [httdef]
    exact lt_min (by norm_num) (by positivity)
  have htt16 : tt ≤ 1 / 16 := min_le_left _ _
  have httb : tt ≤ 1 / (1 + 24 * K) := min_le_right _ _
  have htt1 : tt ≤ 1 := by linarith only [htt16]
  have httK : 3 * K * tt ^ 2 ≤ 1 / 8 := by
    have hsq : tt ^ 2 ≤ tt := by
      have h := mul_le_mul_of_nonneg_left htt1 htt0.le
      calc tt ^ 2 = tt * tt := by ring
        _ ≤ tt * 1 := h
        _ = tt := by ring
    have h3 : 3 * K * tt ^ 2 ≤ 3 * K * tt :=
      mul_le_mul_of_nonneg_left hsq (by linarith only [hK0])
    have h4 : 3 * K * tt ≤ 3 * K * (1 / (1 + 24 * K)) :=
      mul_le_mul_of_nonneg_left httb (by linarith only [hK0])
    have h5 : 3 * K * (1 / (1 + 24 * K)) ≤ 1 / 8 := by
      rw [mul_one_div, div_le_iff₀ hden]
      linarith only [hK0]
    linarith only [h3, h4, h5]
  refine ⟨8 * Real.sqrt ((1 / tt) ^ d) + 1 / 3, by positivity, ?_⟩
  intro m n x i V c A hx hmn hup hother hVodd hharm hVR hmin
  have hw : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  set delta : ℝ := tt * (3 : ℝ) ^ (n - 2) with hdeltadef
  have hdelta : 0 < delta := mul_pos htt0 hw
  have hdelta16 : 16 * delta ≤ (3 : ℝ) ^ (n - 2) := by
    have h1 : 16 * tt - 1 ≤ 0 := by linarith only [htt16]
    have h2 := mul_le_mul_of_nonneg_right h1 hw.le
    rw [hdeltadef]
    linarith only [h2]
  -- harmonicity of the affine residual
  have hfharmR : HarmonicOnNhd
      ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) :=
    harmonicOnNhd_sub_vec_affine hharm (c - vecDot A x) A
  have hTR : coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta)
      ⊆ reflectedWindow x m (n - 2) :=
    coordBox_taylor_subset_reflectedWindow hx hmn hup hother hdelta16
  have hharmT : ∀ z ∈ coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta),
      HarmonicAt ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc z) :=
    fun z hz => hfharmR (toEuc z) ⟨z, hTR hz, rfl⟩
  -- the `L²` data of the residual
  have hfR : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hfsqR : IntegrableOn (fun y => (V y - affineEval (c - vecDot A x) A y) ^ 2)
      (reflectedWindow x m (n - 2)) volume := hfR.integrable_sq
  -- the Hessian bound
  have hquarter : (0 : ℝ) < (3 : ℝ) ^ (n - 2) / 4 := by linarith only [hw]
  set M : ℝ := CH * ((3 : ℝ) ^ (n - 2) / 4)⁻¹ * ((3 : ℝ) ^ (n - 2) / 4)⁻¹
      * Real.sqrt ((volume (reflectedWindow x m (n - 2))).toReal
          / ((3 : ℝ) ^ (n - 2) / 4) ^ d)
      * normalizedL2On (reflectedWindow x m (n - 2))
          (fun y => V y - affineEval (c - vecDot A x) A y) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCH0 (by positivity))
      (by positivity)) (Real.sqrt_nonneg _)) (normalizedL2On_nonneg _ _)
  have hMbound : ∀ z ∈ coordBox (taylorLo x m (n - 2) i delta)
      (taylorHi x m (n - 2) i delta),
      ‖fderiv ℝ (fderiv ℝ ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M := by
    intro z hz
    exact hCH (reflectedWindow x m (n - 2))
      (fun y => V y - affineEval (c - vecDot A x) A y) z ((3 : ℝ) ^ (n - 2) / 4)
      (volume_reflectedWindow_ne_top x m (n - 2))
      (volume_toReal_reflectedWindow_pos x hx (by omega)) hfharmR hfsqR hquarter
      (metricBall_subset_reflectedWindow_of_mem_taylor hx hmn hup hother hdelta16 hz)
  -- the slab comparison
  have hslab := normalizedL2On_evenAffinePart_le_of_hessian_bound hx hmn hup hother hVodd
    hVR hdelta hdelta16 hM0 hharmT hMbound
  have hwd : (3 : ℝ) ^ (n - 2) / delta = 1 / tt := by
    rw [hdeltadef]
    field_simp
  rw [hwd] at hslab
  -- the even part costs the same on both windows
  have hRe : normalizedL2On (reflectedWindow x m (n - 2)) (evenAffinePart x m i c A)
      = normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A) := by
    rw [evenAffinePart, truncatedWindow_eq_coordBox, reflectedWindow]
    exact normalizedL2On_coordBox_affineEval_congr_of_slope_zero
      (windowLo_lt_windowHi hx hmn hup hother)
      (reflectedLo_lt_reflectedHi hx hmn hup hother)
      (evenAffineSlope_apply_self i A)
      (fun j hj => ⟨reflectedLo_eq hmn hup hother j, reflectedHi_eq_of_ne hother hj⟩)
  have hodd := normalizedL2On_reflectedWindow_sub_affineEval_le hx hmn hup hother hVodd hVR c A
  rw [hRe] at hodd
  -- the excess identification
  have hEeq : normalizedL2On (truncatedWindow x m (n - 2))
      (fun y => V y - affineEval (c - vecDot A x) A y)
      = affineExcessRaw (truncatedWindow x m (n - 2)) V := hmin
  -- abbreviate
  set E : ℝ := normalizedL2On (truncatedWindow x m (n - 2))
    (fun y => V y - affineEval (c - vecDot A x) A y) with hEdef
  set N : ℝ := normalizedL2On (truncatedWindow x m (n - 2))
    (evenAffinePart x m i c A) with hNdef
  set nfR : ℝ := normalizedL2On (reflectedWindow x m (n - 2))
    (fun y => V y - affineEval (c - vecDot A x) A y) with hnfRdef
  set S : ℝ := Real.sqrt ((1 / tt) ^ d) with hSdef
  have hE0 : 0 ≤ E := normalizedL2On_nonneg _ _
  have hN0 : 0 ≤ N := normalizedL2On_nonneg _ _
  have hEN0 : 0 ≤ E + N := by linarith only [hE0, hN0]
  -- the odd bridge, collected
  have hnfRle : nfR ≤ ((2 : ℝ) ^ d + 1) * (E + N) := by
    have hNle : N ≤ E + N := by linarith only [hE0]
    calc nfR ≤ (2 : ℝ) ^ d * (E + N) + N := hodd
      _ ≤ (2 : ℝ) ^ d * (E + N) + (E + N) := by linarith only [hNle]
      _ = ((2 : ℝ) ^ d + 1) * (E + N) := by ring
  -- the Hessian remainder is absorbed
  have hMle : M ≤ Kp * ((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹ * nfR := by
    have hratio : Real.sqrt ((volume (reflectedWindow x m (n - 2))).toReal
        / ((3 : ℝ) ^ (n - 2) / 4) ^ d) ≤ Real.sqrt ((8 : ℝ) ^ d) := by
      refine Real.sqrt_le_sqrt ?_
      have hnum : (volume (reflectedWindow x m (n - 2))).toReal
          ≤ (2 * (3 : ℝ) ^ (n - 2)) ^ d :=
        volume_toReal_reflectedWindow_le x hx (by omega) hmn
      have hpos : (0 : ℝ) < ((3 : ℝ) ^ (n - 2) / 4) ^ d := by positivity
      have hquot : (2 * (3 : ℝ) ^ (n - 2)) ^ d / ((3 : ℝ) ^ (n - 2) / 4) ^ d
          = (8 : ℝ) ^ d := by
        rw [← div_pow]
        congr 1
        field_simp
        ring
      calc (volume (reflectedWindow x m (n - 2))).toReal / ((3 : ℝ) ^ (n - 2) / 4) ^ d
          ≤ (2 * (3 : ℝ) ^ (n - 2)) ^ d / ((3 : ℝ) ^ (n - 2) / 4) ^ d :=
            div_le_div_of_nonneg_right hnum hpos.le
        _ = (8 : ℝ) ^ d := hquot
    have hcoef : CH * ((3 : ℝ) ^ (n - 2) / 4)⁻¹ * ((3 : ℝ) ^ (n - 2) / 4)⁻¹
        = CH * 16 * ((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹ := by
      field_simp
      ring
    rw [hMdef, hcoef, hKpdef]
    have hcnn : (0 : ℝ) ≤ CH * 16 * ((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹ := by
      have h1 : (0 : ℝ) ≤ ((3 : ℝ) ^ (n - 2))⁻¹ := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hCH0 (by norm_num)) h1) h1
    calc CH * 16 * ((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹
          * Real.sqrt ((volume (reflectedWindow x m (n - 2))).toReal
              / ((3 : ℝ) ^ (n - 2) / 4) ^ d) * nfR
        ≤ CH * 16 * ((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹
            * Real.sqrt ((8 : ℝ) ^ d) * nfR := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hcnn) ?_
          rw [hnfRdef]
          exact normalizedL2On_nonneg _ _
      _ = CH * 16 * Real.sqrt ((8 : ℝ) ^ d) * ((3 : ℝ) ^ (n - 2))⁻¹
            * ((3 : ℝ) ^ (n - 2))⁻¹ * nfR := by ring
  have hdw : delta ^ 2 * (((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹) = tt ^ 2 := by
    rw [hdeltadef]
    field_simp
  have hnfR0 : 0 ≤ nfR := by
    rw [hnfRdef]
    exact normalizedL2On_nonneg _ _
  have hMdelta : 3 * (M * delta ^ 2) ≤ 1 / 8 * (E + N) := by
    have h1 : M * delta ^ 2 ≤ Kp * nfR * tt ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hMle (by positivity : (0 : ℝ) ≤ delta ^ 2)
      calc M * delta ^ 2
          ≤ Kp * ((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹ * nfR * delta ^ 2 := h
        _ = Kp * nfR * (delta ^ 2
            * (((3 : ℝ) ^ (n - 2))⁻¹ * ((3 : ℝ) ^ (n - 2))⁻¹)) := by ring
        _ = Kp * nfR * tt ^ 2 := by rw [hdw]
    have h2 : Kp * nfR * tt ^ 2 ≤ Kp * (((2 : ℝ) ^ d + 1) * (E + N)) * tt ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnfRle hKp0) (sq_nonneg tt)
    have h3 : Kp * (((2 : ℝ) ^ d + 1) * (E + N)) * tt ^ 2 = K * tt ^ 2 * (E + N) := by
      rw [hKdef]; ring
    have h4 : 3 * K * tt ^ 2 * (E + N) ≤ 1 / 8 * (E + N) :=
      mul_le_mul_of_nonneg_right httK hEN0
    have h5 : 3 * (M * delta ^ 2) ≤ 3 * (K * tt ^ 2 * (E + N)) := by
      linarith only [h1, h2, h3]
    linarith only [h4, h5]
  -- assembly
  rw [← hEeq]
  have hslab' : 1 / 2 * N ≤ 3 * (S * E) + 3 * (M * delta ^ 2) := by
    calc 1 / 2 * N ≤ 3 * S * E + 3 * (M * delta ^ 2) := hslab
      _ = 3 * (S * E) + 3 * (M * delta ^ 2) := by ring
  have hgoal : (8 * S + 1 / 3) * E = 8 * (S * E) + 1 / 3 * E := by ring
  rw [hgoal]
  linarith only [hslab', hMdelta, hE0, hN0]

/-! ## 4. The odd-class defect, priced by the excess -/

/-- **'s residue, discharged.**  Composing `(★)` with's reduction
`oddClassDefect_oddPart_le_evenPart`, the odd-class defect at the normal part
of an affine minimizer is priced by the excess itself.  No `[∇h]` leg enters
here: under face-oddness the datum has already been subtracted. -/
theorem exists_oddClassDefect_le_affineExcessRaw (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i : Fin d) (V : Vec d → ℝ) (c : ℝ)
      (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m →
      MeetsUpperFace x m (n - 2) i →
      (∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j) →
      (∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      oddClassDefect x m n V (oddAffineIntercept x m i A) (oddAffineSlope i A)
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  obtain ⟨C, hC0, hC⟩ := exists_evenAffinePart_le_affineExcessRaw d
  refine ⟨C, hC0, ?_⟩
  intro m n x i V c A hx hmn hup hother hVodd hharm hVR hmin
  have hVU : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hVR.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m (n - 2)) le_rfl)
  exact le_trans (oddClassDefect_oddPart_le_evenPart hVU hmin)
    (hC m n x i V c A hx hmn hup hother hVodd hharm hVR hmin)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
