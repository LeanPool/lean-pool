/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerTaylor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerMoments

/-!
# OneStepOddClassCorner

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The corner pricing of the odd-class defect

's residue (2).  At two met faces the odd affine class collapses to `{0}`
(`affineLift_eq_zero_of_two_met`), so the odd-class defect of the boundary
producer degenerates to `‖V‖_{L²(U₂)} − E_raw(U₂,V)` and the proved one-face
pricing `(★)` does not apply.  This module proves the corner pricing:

```text
  ‖V‖_{L²(U₂)} ≤ C(d) · E_raw(U₂, V)                                (★★)
```

for `V` classically harmonic on the doubled window, odd under **every**
met-face reflection, at a window meeting the upper faces of two distinct
coordinates `i ≠ j` (the remaining met set arbitrary); and hence

```text
  oddClassDefect x m n V 0 0 ≤ C(d) · E_raw(U₂, V) ,
```

the exact leg shape the proved K-package consumers carry at the corner datum
`(c, A) = (0, 0)` — the only member of the collapsed class.

## The mechanism

Let `ℓ*` be an affine minimizer and `f = V − ℓ*`, `E = ‖f‖_{L²(U₂)}`,
`P = ‖ℓ*‖_{L²(U₂)}`.  With `evenᵢ`/`evenⱼ` the even parts of `ℓ*` at the two
faces and `e_{ij}` the doubly even part (`= evenⱼ` of the affine `evenᵢ`),

```text
  ℓ* = evenᵢ + evenⱼ − e_{ij} ,
```

and each of the three parts is priced on a window-hugging near-face slab by
the two-point Taylor elimination (`abs_evenAffinePart_le_pointwise_of_mem`):
the single-face applications at `i` and at `j` against the residual `f`, and
the doubly even part at the face `j` against the residual `V − evenᵢ` **on
the corner slab**, where the leftover normal ramp `oddᵢ = ℓ* − evenᵢ` is
pointwise at most `|Aᵢ|·delta` and hence `O(t)`-small against
`P + ‖evenᵢ‖` by the box-moment lower bound.  The Hessian remainders are
`O(t²)·‖f‖_{L²(R)}`, and `‖f‖_{L²(R)}` folds back to `(E + P)` by the
full-met-set odd fold and the affine moment comparison.  Choosing the depth
fraction `t = t(d)` small absorbs every `P`-feedback at coefficient `< 1`,
closing `P ≤ C(d)·E`.

## Scope (disclosed)

The two active faces are met **upper** faces, matching every proved convention
of the one-face chain (`evenAffinePart`, the slab geometry, `(★)` itself are
stated at upper faces).  Lower and mixed corners require either the mechanical
lower-face twins of those atoms or a coordinate-negation transport; neither is
built here, and the composed corner consumption must supply the upper-upper
configuration or its transported image.  The met-face oddness binders are the
**global pointwise** identities, exactly as in the proved `(★)` and one-face
producer.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The slab estimate, box-generic -/

/-- **The near-face slab estimate**, box-generic: the `L²` size of the even
part on the slab is priced by the residual on the slab, on its inward
translate, and the Hessian remainder. -/
theorem normalizedL2On_evenAffinePart_slab_le {m : ℤ} {x : Vec d} {face : Fin d}
    {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) face z) = -V z)
    {c' : ℝ} {A' : Vec d} {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 ≤ M)
    {loP hiP loT hiT : Fin d → ℝ}
    (hPpos : 0 < (volume (coordBox loP hiP)).toReal)
    (hharmT : ∀ z ∈ coordBox loT hiT,
      HarmonicAt ((fun y => V y - affineEval (c' - vecDot A' x) A' y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc z))
    (hMT : ∀ z ∈ coordBox loT hiT,
      ‖fderiv ℝ (fderiv ℝ ((fun y => V y - affineEval (c' - vecDot A' x) A' y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M)
    (hPT : coordBox loP hiP ⊆ coordBox loT hiT)
    (hrT : ∀ y ∈ coordBox loP hiP,
      coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) face y ∈ coordBox loT hiT)
    (hpT : ∀ y ∈ coordBox loP hiP,
      y - delta • (basisVec face : Vec d) ∈ coordBox loT hiT)
    (hdepth : ∀ y ∈ coordBox loP hiP,
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y face
        ∧ y face < (1 / 2 : ℝ) * (3 : ℝ) ^ m)
    (hfP : MemLp (fun y => V y - affineEval (c' - vecDot A' x) A' y) 2
      (volume.restrict (coordBox loP hiP)))
    (hfD : MemLp (fun y => V y - affineEval (c' - vecDot A' x) A' y) 2
      (volume.restrict (coordBox
        (fun l => loP l - (delta • (basisVec face : Vec d)) l)
        (fun l => hiP l - (delta • (basisVec face : Vec d)) l)))) :
    normalizedL2On (coordBox loP hiP) (evenAffinePart x m face c' A')
      ≤ 2 * normalizedL2On (coordBox loP hiP)
            (fun y => V y - affineEval (c' - vecDot A' x) A' y)
        + normalizedL2On (coordBox
            (fun l => loP l - (delta • (basisVec face : Vec d)) l)
            (fun l => hiP l - (delta • (basisVec face : Vec d)) l))
            (fun y => V y - affineEval (c' - vecDot A' x) A' y)
        + 3 * (M * delta ^ 2) := by
  classical
  set f : Vec d → ℝ := fun y => V y - affineEval (c' - vecDot A' x) A' y with hfdef
  set v0 : Vec d := delta • (basisVec face : Vec d) with hv0def
  set P : Set (Vec d) := coordBox loP hiP with hPdef
  set D : Set (Vec d) := coordBox (fun l => loP l - v0 l) (fun l => hiP l - v0 l)
    with hDdef
  have himg : (fun z => z - v0) '' P = D := by
    rw [hPdef, hDdef, image_sub_coordBox]
  have heP : MemLp (evenAffinePart x m face c' A') 2 (volume.restrict P) := by
    rw [evenAffinePart]
    exact memLp_affineEval_coordBox loP hiP _ _
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
  set g : Vec d → ℝ := fun y => 2 * |f y| + (|f (y - v0)| + 3 * (M * delta ^ 2))
    with hgdef
  have hgmem : MemLp g 2 (volume.restrict P) := by
    rw [hgdef]
    exact (hfP.abs.const_mul 2).add (hftP.abs.add (memLp_const _))
  have hdom : normalizedL2On P (evenAffinePart x m face c' A')
      ≤ normalizedL2On P g := by
    refine normalizedL2On_mono_of_abs_le (measurableSet_coordBox _ _)
      heP.integrable_sq hgmem.integrable_sq ?_
    intro y hy
    have hyd := hdepth y hy
    have h := abs_evenAffinePart_le_pointwise_of_mem hVodd hdelta hM
      (convex_coordBox loT hiT) hharmT hMT (hPT hy) (hrT y hy) (hpT y hy)
      hyd.1 hyd.2
    rw [hgdef]
    change |evenAffinePart x m face c' A' y|
        ≤ 2 * |f y| + (|f (y - v0)| + 3 * (M * delta ^ 2))
    have habs : |f (y - v0)| = |V (y - v0) - affineEval (c' - vecDot A' x) A' (y - v0)| :=
      rfl
    have habs2 : |f y| = |V y - affineEval (c' - vecDot A' x) A' y| := rfl
    rw [habs, habs2]
    linarith only [h]
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
  linarith only [hdom, hg1]

/-! ## 2. Transfer helpers -/

/-- The subset transfer with an explicit ratio bound. -/
theorem transfer_le {U' B : Set (Vec d)} {f : Vec d → ℝ} {ρ : ℝ}
    (hsub : B ⊆ U') (hU'pos : 0 < (volume U').toReal)
    (hBpos : 0 < (volume B).toReal)
    (hint : IntegrableOn (fun y => f y ^ 2) U' volume)
    (hratio : (volume U').toReal / (volume B).toReal ≤ ρ) :
    normalizedL2On B f ≤ Real.sqrt ρ * normalizedL2On U' f := by
  refine le_trans (normalizedL2On_le_of_subset hsub hU'pos hBpos hint) ?_
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hratio)
    (normalizedL2On_nonneg _ _)

/-- The volume-ratio bound `|U|/|B| ≤ (1/t)^d` for a slab of edge `≥ delta`. -/
theorem ratio_le_inv_t_pow {a b A w tt delta : ℝ}
    (ha0 : 0 ≤ a) (haA : a ≤ w ^ d) (hb : delta ^ d ≤ b)
    (hw : 0 < w) (htt : 0 < tt) (hdel : delta = tt * w) (hab : a = A) :
    A / b ≤ (1 / tt) ^ d := by
  have hδpos : (0 : ℝ) < delta := by
    rw [hdel]
    positivity
  have hδd : (0 : ℝ) < delta ^ d := by positivity
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le hδd hb
  have h1 : A / b ≤ A / delta ^ d := by
    rw [← hab]
    exact div_le_div_of_nonneg_left ha0 hδd hb
  have h2 : A / delta ^ d ≤ w ^ d / delta ^ d := by
    rw [← hab]
    exact div_le_div_of_nonneg_right haA hδd.le
  have h3 : w ^ d / delta ^ d = (1 / tt) ^ d := by
    rw [← div_pow]
    congr 1
    rw [hdel]
    field_simp
  calc A / b ≤ A / delta ^ d := h1
    _ ≤ w ^ d / delta ^ d := h2
    _ = (1 / tt) ^ d := h3

/-! ## 3. The Hessian value on a Taylor set -/

/-- **The Hessian value.**  For `F` harmonic on the doubled window and a set whose
points carry sup-balls of radius `3^k/16` inside it, there is a Hessian bound
`M` on the set with `M·delta² ≤·256·√(32^d)·t²·‖F‖_{L²(R)}` at `delta =
t·3^k`. -/
theorem exists_hessian_value {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) {tt delta : ℝ}
    (htt0 : 0 < tt) (hdel : delta = tt * (3 : ℝ) ^ k)
    {Tbox : Set (Vec d)}
    (hballs : ∀ z ∈ Tbox, Metric.ball z ((3 : ℝ) ^ k / 16) ⊆ reflectedWindow x m k)
    {F : Vec d → ℝ}
    (hFR : MemLp F 2 (volume.restrict (reflectedWindow x m k)))
    (hFharm : HarmonicOnNhd (F ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k))
    {CH : ℝ} (hCH0 : 0 ≤ CH)
    (hCH : ∀ (W : Set (Vec d)) (V : Vec d → ℝ) (p : Vec d) (r : ℝ),
      volume W ≠ ⊤ → 0 < (volume W).toReal →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' W) →
      IntegrableOn (fun y => V y ^ 2) W volume →
      0 < r → Metric.ball p r ⊆ W →
      ‖fderiv ℝ (fderiv ℝ (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)))
          (toEuc p)‖
        ≤ CH * r⁻¹ * r⁻¹ * Real.sqrt ((volume W).toReal / r ^ d)
            * normalizedL2On W V) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ z ∈ Tbox, ‖fderiv ℝ (fderiv ℝ
          (F ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M) ∧
      M * delta ^ 2 ≤ CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
        * normalizedL2On (reflectedWindow x m k) F := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hr : (0 : ℝ) < (3 : ℝ) ^ k / 16 := by linarith only [hw]
  have hRpos : 0 < (volume (reflectedWindow x m k)).toReal :=
    volume_toReal_reflectedWindow_pos x hx (by omega)
  set M : ℝ := CH * ((3 : ℝ) ^ k / 16)⁻¹ * ((3 : ℝ) ^ k / 16)⁻¹
      * Real.sqrt ((volume (reflectedWindow x m k)).toReal / ((3 : ℝ) ^ k / 16) ^ d)
      * normalizedL2On (reflectedWindow x m k) F with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCH0 (by positivity))
      (by positivity)) (Real.sqrt_nonneg _)) (normalizedL2On_nonneg _ _)
  refine ⟨M, hM0, ?_, ?_⟩
  · intro z hz
    exact hCH (reflectedWindow x m k) F z ((3 : ℝ) ^ k / 16)
      (volume_reflectedWindow_ne_top x m k) hRpos hFharm hFR.integrable_sq hr
      (hballs z hz)
  · have hratio : Real.sqrt ((volume (reflectedWindow x m k)).toReal
        / ((3 : ℝ) ^ k / 16) ^ d) ≤ Real.sqrt ((32 : ℝ) ^ d) := by
      refine Real.sqrt_le_sqrt ?_
      have hnum : (volume (reflectedWindow x m k)).toReal ≤ (2 * (3 : ℝ) ^ k) ^ d :=
        volume_toReal_reflectedWindow_le x hx (by omega) hkm
      have hpos : (0 : ℝ) < ((3 : ℝ) ^ k / 16) ^ d := by positivity
      have hquot : (2 * (3 : ℝ) ^ k) ^ d / ((3 : ℝ) ^ k / 16) ^ d = (32 : ℝ) ^ d := by
        rw [← div_pow]
        congr 1
        field_simp
        ring
      calc (volume (reflectedWindow x m k)).toReal / ((3 : ℝ) ^ k / 16) ^ d
          ≤ (2 * (3 : ℝ) ^ k) ^ d / ((3 : ℝ) ^ k / 16) ^ d :=
            div_le_div_of_nonneg_right hnum hpos.le
        _ = (32 : ℝ) ^ d := hquot
    have hinv : ((3 : ℝ) ^ k / 16)⁻¹ = 16 * ((3 : ℝ) ^ k)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have hdw : delta ^ 2 * (((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹) = tt ^ 2 := by
      rw [hdel]
      field_simp
    have hN0 : 0 ≤ normalizedL2On (reflectedWindow x m k) F :=
      normalizedL2On_nonneg _ _
    have hMle : M ≤ CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * ((3 : ℝ) ^ k)⁻¹
        * ((3 : ℝ) ^ k)⁻¹ * normalizedL2On (reflectedWindow x m k) F := by
      rw [hMdef, hinv]
      have hcnn : (0 : ℝ) ≤ CH * (16 * ((3 : ℝ) ^ k)⁻¹) * (16 * ((3 : ℝ) ^ k)⁻¹) := by
        positivity
      calc CH * (16 * ((3 : ℝ) ^ k)⁻¹) * (16 * ((3 : ℝ) ^ k)⁻¹)
            * Real.sqrt ((volume (reflectedWindow x m k)).toReal
                / ((3 : ℝ) ^ k / 16) ^ d)
            * normalizedL2On (reflectedWindow x m k) F
          ≤ CH * (16 * ((3 : ℝ) ^ k)⁻¹) * (16 * ((3 : ℝ) ^ k)⁻¹)
              * Real.sqrt ((32 : ℝ) ^ d)
              * normalizedL2On (reflectedWindow x m k) F := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hratio hcnn) hN0
        _ = CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * ((3 : ℝ) ^ k)⁻¹
              * ((3 : ℝ) ^ k)⁻¹ * normalizedL2On (reflectedWindow x m k) F := by
            ring
    have h := mul_le_mul_of_nonneg_right hMle (sq_nonneg delta)
    calc M * delta ^ 2
        ≤ CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹
            * normalizedL2On (reflectedWindow x m k) F * delta ^ 2 := h
      _ = CH * 256 * Real.sqrt ((32 : ℝ) ^ d)
            * (delta ^ 2 * (((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹))
            * normalizedL2On (reflectedWindow x m k) F := by ring
      _ = CH * 256 * Real.sqrt ((32 : ℝ) ^ d) * tt ^ 2
            * normalizedL2On (reflectedWindow x m k) F := by rw [hdw]

/-! ## 4. Small instantiation helpers -/

/-- The controlled comparison of the window against a window-hugging slab:
`κ = 4`, active coordinates carried by zero slopes. -/
theorem moment_transfer_window_le {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    {loP hiP : Fin d → ℝ} (hltP : ∀ l, loP l < hiP l) {c' : ℝ} {g' : Vec d}
    (hcases : ∀ l, g' l = 0 ∨
      (loP l = hugLo x m k l ∧ hiP l = hugHi x m k l)) :
    normalizedL2On (truncatedWindow x m k) (affineEval c' g')
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2)
          * normalizedL2On (coordBox loP hiP) (affineEval c' g') := by
  have hltW : ∀ l, windowLo x m k l < windowHi x m k l :=
    windowLo_lt_windowHi_of_mem hx hkm
  have hctrl : ∀ l, g' l = 0 ∨ ((windowHi x m k l - windowLo x m k l
        ≤ 4 * (hiP l - loP l)) ∧
      |boxCenter (windowLo x m k) (windowHi x m k) l - boxCenter loP hiP l|
        ≤ 4 * (hiP l - loP l)) := by
    intro l
    rcases hcases l with hg | ⟨hlo, hhi⟩
    · exact Or.inl hg
    · refine Or.inr ?_
      have hedge0 : 0 ≤ windowHi x m k l - windowLo x m k l := by
        linarith only [hltW l]
      have hsub : hiP l - loP l = (windowHi x m k l - windowLo x m k l) / 2 := by
        rw [hlo, hhi, hugHi_sub_hugLo]
      constructor
      · rw [hsub]
        linarith only [hedge0]
      · have hcen : boxCenter (windowLo x m k) (windowHi x m k) l
            - boxCenter loP hiP l = 0 := by
          rw [boxCenter_apply, boxCenter_apply, hlo, hhi]
          have h := hugLo_add_hugHi (x := x) m k l
          linarith only [h]
        rw [hcen, abs_zero, hsub]
        linarith only [hedge0]
  have h := normalizedL2On_coordBox_affineEval_le_of_controlled hltW hltP
    (κ := 4) (c := c') (g := g') hctrl
  rwa [show coordBox (windowLo x m k) (windowHi x m k) = truncatedWindow x m k from
    (truncatedWindow_eq_coordBox x m k).symm] at h

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
