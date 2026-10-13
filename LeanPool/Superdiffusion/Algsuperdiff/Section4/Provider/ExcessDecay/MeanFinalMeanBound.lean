/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanFinalCore

/-!
# MeanFinalMeanBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `(A)`: the flush-cube mean bound

```text
  |β| ≤ C · ‖W − β‖_{L²(K)}
```

for a function `W` **odd** about the face hyperplane `{yᵢ = a}` that the cube
`K` shares with the boundary, and **classically harmonic** on a doubled window
`D ⊇ K`.  Applied with `β = ⨍_K W` this is exactly

```text
  |⨍_K W| ≤ C(d) · ‖W − (W)_K‖_{L²(K)} ,
```

the statement that a `Δ`-harmonic function vanishing on a face of `K` cannot be
close to a nonzero constant; the general-`β` form is what the composition
actually uses.

## The proof, in three moves

1. **The pointwise near-face elimination** (`MeanFinalPointwise`): at every
   point `y` of a thin slab `S` under the face, the reflection identity plus two
   second-order Taylor steps eliminate the unknown normal derivative and give
   `|β| ≤ 2|G y| + |G(y − w·eᵢ)| + 3Mw²` with `G = W − β`.
2. **The slab average**: `normalizedL2On_mono_of_abs_le` and Minkowski turn
   that into `|β| ≤ 2‖G‖_{L²(S)} + ‖G‖_{L²(S − w·eᵢ)} + 3Mw²`, and both
   seminorms transfer to `K` at the volume ratio `(|K|/|S|)^{1/2}`.
3. **The absorption**: `M` is the interior Hessian bound of
   `exists_hessian_normalizedL2On_bound` on `D`, so `3Mw²` carries the
   *quadratically small* factor `w²`; the doubled-window transfer of
   `MeanFinalCore` returns `‖G‖_{L²(D)}` to `2‖G‖_{L²(K)} + 3|β|`, and the
   room hypothesis `9·CH·r⁻¹·r⁻¹·RD·w² ≤ 1/2` absorbs the `|β|` that comes back.

The geometry is left abstract — four sets `S ⊆ K ⊆ D`, `S ⊆ T ⊆ D` with the
inclusions each move uses — so that the same statement serves an upper and a
lower flush face of `MeanControlWindowCube`: the sign of the face lives
entirely in the **signed** depth `w`, and every hypothesis below is sign free.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2 (boundary cubes).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec coordFaceReflection basisVec volumeAverage)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. A translated window has the same volume -/

/-- Translating a window is a measure-preserving relabelling. -/
theorem image_sub_eq_preimage_add' (S : Set (Vec d)) (v : Vec d) :
    (fun z => z - v) '' S = (fun z => z + v) ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show x - v + v ∈ S
    rwa [sub_add_cancel]
  · intro hy
    refine ⟨y + v, hy, ?_⟩
    show y + v - v = y
    abel

/-- The volume of a translated window. -/
theorem volume_image_sub (S : Set (Vec d)) (v : Vec d) :
    volume ((fun z => z - v) '' S) = volume S := by
  rw [image_sub_eq_preimage_add' S v, measure_preimage_add_right]

/-! ## 2. The slab average -/

/-- **The slab average of the pointwise near-face bound.**

If a constant `β` is dominated pointwise on `S` by `2|G| + |G(· − v)| + Mw`,
then it is dominated by the corresponding `L²(S)` seminorms. -/
theorem abs_le_slab_of_pointwise {i : Fin d} {w : ℝ} {S : Set (Vec d)}
    {G : Vec d → ℝ} {beta Mw : ℝ}
    (hSm : MeasurableSet S) (hSpos : 0 < (volume S).toReal) (hStop : volume S ≠ ⊤)
    (hGS : MemLp G 2 (volume.restrict S))
    (hGpush : MemLp (fun y => G (y - w • (basisVec i : Vec d))) 2 (volume.restrict S))
    (hMw : 0 ≤ Mw)
    (hpt : ∀ y ∈ S, |beta| ≤ 2 * |G y| + |G (y - w • (basisVec i : Vec d))| + Mw) :
    |beta| ≤ 2 * normalizedL2On S G
      + normalizedL2On ((fun z => z - w • (basisVec i : Vec d)) '' S) G + Mw := by
  classical
  have : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hStop
  set v0 : Vec d := w • (basisVec i : Vec d) with hv0def
  set g : Vec d → ℝ := fun y => 2 * |G y| + (|G (y - v0)| + Mw) with hgdef
  have hgmem : MemLp g 2 (volume.restrict S) := by
    rw [hgdef]
    exact (hGS.abs.const_mul 2).add (hGpush.abs.add (memLp_const _))
  have hconstmem : MemLp (fun _ : Vec d => beta) 2 (volume.restrict S) := memLp_const _
  have hdom : normalizedL2On S (fun _ : Vec d => beta) ≤ normalizedL2On S g := by
    refine normalizedL2On_mono_of_abs_le hSm hconstmem.integrable_sq hgmem.integrable_sq ?_
    intro y hy
    have h := hpt y hy
    show |beta| ≤ 2 * |G y| + (|G (y - v0)| + Mw)
    linarith only [h]
  rw [normalizedL2On_const_of_toReal_pos hSpos] at hdom
  have hsplit : normalizedL2On S g
      ≤ normalizedL2On S (fun y => 2 * |G y|)
        + normalizedL2On S (fun y => |G (y - v0)| + Mw) := by
    rw [hgdef]
    exact normalizedL2On_add_le (hGS.abs.const_mul 2) (hGpush.abs.add (memLp_const _))
  have hsplit2 : normalizedL2On S (fun y => |G (y - v0)| + Mw)
      ≤ normalizedL2On S (fun y => |G (y - v0)|)
        + normalizedL2On S (fun _ : Vec d => Mw) :=
    normalizedL2On_add_le hGpush.abs (memLp_const _)
  have hA : normalizedL2On S (fun y => 2 * |G y|) = 2 * normalizedL2On S G := by
    rw [normalizedL2On_const_mul, normalizedL2On_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hB : normalizedL2On S (fun y => |G (y - v0)|)
      = normalizedL2On ((fun z => z - v0) '' S) G := by
    rw [normalizedL2On_abs, normalizedL2On_comp_sub_right]
  have hC : normalizedL2On S (fun _ : Vec d => Mw) = Mw := by
    rw [normalizedL2On_const_of_toReal_pos hSpos, abs_of_nonneg hMw]
  rw [hA] at hsplit
  rw [hB, hC] at hsplit2
  linarith only [hdom, hsplit, hsplit2]

/-! ## 3. `(A)` -/

/-- **`(A)`, the flush-cube mean bound.**

Let `W` be odd about the face hyperplane `{yᵢ = a}`, square integrable on a
doubled window `D`, and let `G = W − β` be classically harmonic on `D`.  Let
`K ⊆ D` be the cube, `S ⊆ K` a near-face slab whose translate by `w·eᵢ` also
lies in `K`, and `T` a convex Taylor set containing `S`, its reflection and its
translate, with a uniform ball of radius `r` inside `D` at each of its points.
If `D` is covered — up to the face hyperplane — by `K` and the reflection of
`K`, then

```text
  |β| ≤ (6·RK + 12·CH·r⁻¹·r⁻¹·RD·w²) · ‖W − β‖_{L²(K)} ,
```

where bounds `(|K|/|S|)^{1/2}` bounds `(|D|/rᵈ)^{1/2}` is the dimensional
constant of the interior Hessian estimate — provided the absorption has room,
`9··r⁻¹·r⁻¹··w² ≤ 1/2`. -/
theorem exists_abs_le_normalizedL2On_of_faceOdd (d : ℕ) [NeZero d] :
    ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ (i : Fin d) (a w r : ℝ) (K D S T : Set (Vec d)) (W : Vec d → ℝ)
        (beta RK RD : ℝ),
        (∀ z, W (coordFaceReflection a i z) = -W z) →
        MemLp W 2 (volume.restrict D) →
        HarmonicOnNhd ((fun y => W y - beta) ∘
            (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
          ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' D) →
        Convex ℝ T → T ⊆ D → S ⊆ K → K ⊆ D →
        (fun z => z - w • (basisVec i : Vec d)) '' S ⊆ K →
        (∀ y ∈ S, y ∈ T ∧ coordFaceReflection a i y ∈ T ∧
          y - w • (basisVec i : Vec d) ∈ T ∧
          0 < (a - y i) / w ∧ (a - y i) / w ≤ 1) →
        (∀ z ∈ T, Metric.ball z r ⊆ D) → 0 < r →
        (∀ y ∈ D, y ∈ K ∨ coordFaceReflection a i y ∈ K ∨ y i = a) →
        MeasurableSet S → MeasurableSet K → MeasurableSet D →
        volume D ≠ ⊤ →
        0 < (volume S).toReal → 0 < (volume K).toReal → 0 < (volume D).toReal →
        (volume K).toReal ≤ (volume D).toReal →
        Real.sqrt ((volume K).toReal / (volume S).toReal) ≤ RK →
        Real.sqrt ((volume D).toReal / r ^ d) ≤ RD → 0 ≤ RD →
        9 * (CH * r⁻¹ * r⁻¹ * RD * w ^ 2) ≤ 1 / 2 →
        |beta| ≤ (6 * RK + 12 * (CH * r⁻¹ * r⁻¹ * RD * w ^ 2)) *
          normalizedL2On K (fun y => W y - beta) := by
  classical
  obtain ⟨CH, hCH0, hCH⟩ := exists_hessian_normalizedL2On_bound d
  refine ⟨CH, hCH0, ?_⟩
  intro i a w r K D S T W beta RK RD hodd hWD hharm hTconv hTD hSK hKD hpushK
    hSmem hball hr hDsplit hSm hKm hDm hDtop hSpos hKpos hDpos hKleD hRK hRD hRD0 hroom
  set G : Vec d → ℝ := fun y => W y - beta with hGdef
  set v0 : Vec d := w • (basisVec i : Vec d) with hv0def
  set osc : ℝ := normalizedL2On K G with hoscdef
  set nD : ℝ := normalizedL2On D G with hnDdef
  set q : ℝ := CH * r⁻¹ * r⁻¹ * RD * w ^ 2 with hqdef
  have : IsFiniteMeasure (volume.restrict D) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hDtop
  have hSD : S ⊆ D := hSK.trans hKD
  have hpushD : (fun z => z - v0) '' S ⊆ D := hpushK.trans hKD
  have hGD : MemLp G 2 (volume.restrict D) := hWD.sub (memLp_const beta)
  have hintDG : IntegrableOn (fun y => G y ^ 2) D volume := hGD.integrable_sq
  have hintKG : IntegrableOn (fun y => G y ^ 2) K volume := hintDG.mono_set hKD
  have hGS : MemLp G 2 (volume.restrict S) :=
    hGD.mono_measure (Measure.restrict_mono hSD le_rfl)
  have hGimg : MemLp G 2 (volume.restrict ((fun z => z - v0) '' S)) :=
    hGD.mono_measure (Measure.restrict_mono hpushD le_rfl)
  have hStop : volume S ≠ ⊤ := ne_top_of_le_ne_top hDtop (measure_mono hSD)
  have hmp : MeasurePreserving (fun z : Vec d => z - v0) (volume.restrict S)
      (volume.restrict ((fun z => z - v0) '' S)) :=
    (measurePreserving_sub_right (volume : Measure (Vec d)) v0).restrict_image_emb
      (measurableEmbedding_subRight v0) S
  have hGpush : MemLp (fun y => G (y - v0)) 2 (volume.restrict S) :=
    hGimg.comp_measurePreserving hmp
  have hosc0 : 0 ≤ osc := normalizedL2On_nonneg K G
  have hnD0 : 0 ≤ nD := normalizedL2On_nonneg D G
  -- the Hessian bound on the Taylor set
  set M : ℝ := CH * r⁻¹ * r⁻¹ * RD * nD with hMdef
  have hcoef0 : 0 ≤ CH * r⁻¹ * r⁻¹ :=
    mul_nonneg (mul_nonneg hCH0 (inv_nonneg.mpr hr.le)) (inv_nonneg.mpr hr.le)
  have hharm' : ∀ z ∈ T, HarmonicAt (G ∘
      (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc z) := by
    intro z hz
    exact hharm (toEuc z) (Set.mem_image_of_mem _ (hTD hz))
  have hMb : ∀ z ∈ T, ‖fderiv ℝ (fderiv ℝ (G ∘
      (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M := by
    intro z hz
    have hcore := hCH D G z r hDtop hDpos hharm hintDG hr (hball z hz)
    refine hcore.trans ?_
    rw [hMdef]
    have hstep : CH * r⁻¹ * r⁻¹ * Real.sqrt ((volume D).toReal / r ^ d)
        ≤ CH * r⁻¹ * r⁻¹ * RD := mul_le_mul_of_nonneg_left hRD hcoef0
    exact mul_le_mul_of_nonneg_right hstep hnD0
  -- the pointwise bound on the slab
  have hpt : ∀ y ∈ S, |beta| ≤ 2 * |G y| + |G (y - v0)| + 3 * M * w ^ 2 := by
    intro y hy
    obtain ⟨hyT, hrT, hpT, hd0, hd1⟩ := hSmem y hy
    have hrefl : G (coordFaceReflection a i y) + G y = -2 * beta := by
      have h := hodd y
      show (W (coordFaceReflection a i y) - beta) + (W y - beta) = -2 * beta
      rw [h]
      ring
    exact abs_le_pointwise_of_reflectionIdentity hTconv hharm' hMb hyT hrT hpT hrefl
      hd0 hd1
  -- the slab average
  have hMwnn : 0 ≤ 3 * M * w ^ 2 := by
    have hM0 : 0 ≤ M := by
      rw [hMdef]
      exact mul_nonneg (mul_nonneg hcoef0 hRD0) hnD0
    have hw2 : (0 : ℝ) ≤ w ^ 2 := sq_nonneg w
    have h1 : 0 ≤ 3 * M := by linarith only [hM0]
    exact mul_nonneg h1 hw2
  have hslab := abs_le_slab_of_pointwise (i := i) (w := w) hSm hSpos hStop hGS hGpush
    hMwnn hpt
  -- the two volume-ratio transfers
  have hSratio : normalizedL2On S G ≤ RK * osc := by
    have h1 := normalizedL2On_le_of_subset hSK hKpos hSpos hintKG
    exact h1.trans (mul_le_mul_of_nonneg_right hRK hosc0)
  have hpushvol : (volume ((fun z => z - v0) '' S)).toReal = (volume S).toReal := by
    rw [volume_image_sub]
  have hpushpos : 0 < (volume ((fun z => z - v0) '' S)).toReal := by
    rw [hpushvol]; exact hSpos
  have hPratio : normalizedL2On ((fun z => z - v0) '' S) G ≤ RK * osc := by
    have h1 := normalizedL2On_le_of_subset hpushK hKpos hpushpos hintKG
    rw [hpushvol] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hRK hosc0)
  -- the doubled-window transfer
  have hdb : nD ≤ 2 * osc + 3 * |beta| :=
    normalizedL2On_doubled_le hodd hKm hDm hKD hDsplit hKpos hDpos hKleD hDtop hGD
  -- the absorption
  have hq0 : 0 ≤ q := by
    rw [hqdef]
    exact mul_nonneg (mul_nonneg hcoef0 hRD0) (sq_nonneg w)
  have hMq : 3 * M * w ^ 2 = 3 * (q * nD) := by
    rw [hMdef, hqdef]; ring
  have hkey : |beta| ≤ 3 * (RK * osc) + 3 * (q * nD) := by
    rw [hMq] at hslab
    linarith only [hslab, hSratio, hPratio]
  have hmul : q * nD ≤ q * (2 * osc + 3 * |beta|) := mul_le_mul_of_nonneg_left hdb hq0
  have hroom' : 3 * (q * (3 * |beta|)) ≤ (1 / 2) * |beta| := by
    have h := mul_le_mul_of_nonneg_right hroom (abs_nonneg beta)
    calc 3 * (q * (3 * |beta|)) = 9 * q * |beta| := by ring
      _ ≤ (1 / 2) * |beta| := h
  have hexpand : q * (2 * osc + 3 * |beta|) = 2 * (q * osc) + q * (3 * |beta|) := by ring
  have hgoal : (6 * RK + 12 * q) * osc = 6 * (RK * osc) + 12 * (q * osc) := by ring
  rw [hgoal]
  linarith only [hkey, hmul, hroom', hexpand]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
