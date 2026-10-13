/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanFinalMeanBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanControlWindowCube

/-!
# SealMeanCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `(A)` at a cube: the flush-face mean bound with a dimension-only constant

`MeanFinalMeanBound.exists_abs_le_normalizedL2On_of_faceOdd` proves the mean
bound `(A)` for an **abstract** near-face geometry: four sets `S ⊆ K ⊆ D`, `S ⊆
T ⊆ D`, a signed depth `w`, a ball radius `r`, and two volume ratios, subject
to a list of inclusions and an absorption room hypothesis.  This module
instantiates that statement at the geometry the composition actually has — a
**cube with a flush face** — and discharges *every* geometric side condition,
leaving a clean statement

```text
  |β| ≤ C(d) · ‖W − β‖_{L²(K)} ,     K = sealCube c L ,
```

for `W` odd about the face hyperplane `{yᵢ = c i + σ·L/2}` (`σ = ±1`) and
`W − β` classically harmonic on the doubled cube `sealDouble c L i σ`.  The
constant depends on the dimension only: neither the centre `c`, nor the side
`L > 0`, nor the coordinate `i`, nor the sign `σ` occurs in it.

## The choice of parameters

With the dimensional constant of `exists_abs_le_normalizedL2On_of_faceOdd`,

```text
  r = L/8 ,   λ = (16 + 1152·CH·4ᵈ)⁻¹ ,   w = σ·(λL) ,   RK = √(λ⁻¹ᵈ) ,  RD = 4ᵈ ,
  C(d) = 6·√(λ⁻¹ᵈ) + 12·(64·CH·4ᵈ·λ²)   ( ≤ 6·√(λ⁻¹ᵈ) + 1 ) .
```

The two ratios are the crude volume bounds `|K| ≤ Lᵈ`, `|S| ≥ (λL)ᵈ`, `|D| ≤
(2L)ᵈ`, `rᵈ = (L/8)ᵈ`.  The room hypothesis is `CH·r⁻¹·r⁻¹·RD·w² = 64·CH·4ᵈ·λ²` with
`9·(64·CH·4ᵈ·λ²) ≤ 1/2`, i.e. `1152·CH·4ᵈ·λ² ≤ 1`, which holds because `1152·CH·4ᵈ ≤
(16 + 1152·CH·4ᵈ)² = λ⁻²` for every `CH·4ᵈ ≥ 0` (the degenerate value `CH·4ᵈ = 0` makes
the left side vanish).  All six windows are open coordinate boxes that are
cubes transversally to `i` with a prescribed `i`-edge; they are packaged as
`axisBox`, whose small A (inclusion, reflection, translation, sup-ball, two
volume bounds) is what makes the two sign branches short.

## Naming: the relation to `SealCaccioppoliGeometry`

That module fixes the parent scale at `n + 2` and exports `flushSubCentre
z m n i σ` in `Algsuperdiff.Section4.Provider.ExcessDecay`.  Everything named
`flushSub…` here carries the `seal` prefix (`sealFlushSubCentre z m k n i sg`,
with the parent scale `k` a free index) so that a consumer may open both
namespaces; the bodies are written in the same `if`-normal form, so
`sealFlushSubCentre z m (n+2) n i σ = flushSubCentre z m n i σ` holds by `rfl`.
The bridge is not stated here: this module does not import that one.

## What is not done here

Nothing analytic: no Taylor step, no Hessian estimate, no harmonicity is proved.
The single analytic input is the abstract `(A)` of `MeanFinalMeanBound`; the
square integrability of `W` on the doubled cube and the classical harmonicity of
`W − β` there remain hypotheses of every statement below.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2 (boundary cubes).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec coordFaceReflection basisVec openCubeSet originCube
  coordFaceReflection_apply_self coordFaceReflection_apply_ne)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Axis boxes

An `axisBox` is the open box which is a cube of half-side `b` about `c` in every
coordinate except `i`, and has the prescribed edge `(p, q)` in the coordinate
`i`.  All six windows of the instantiation are of this shape. -/

/-- The lower corner of the box with `i`-edge `(p, q)` and transversal half-side `b`. -/
def axisLo (c : Vec d) (i : Fin d) (p b : ℝ) : Fin d → ℝ :=
  fun j => if j = i then p else c j - b

/-- The upper corner of the box with `i`-edge `(p, q)` and transversal half-side `b`. -/
def axisHi (c : Vec d) (i : Fin d) (q b : ℝ) : Fin d → ℝ :=
  fun j => if j = i then q else c j + b

/-- The open box with `i`-edge `(p, q)` and transversal half-side `b` about `c`. -/
def axisBox (c : Vec d) (i : Fin d) (p q b : ℝ) : Set (Vec d) :=
  coordBox (axisLo c i p b) (axisHi c i q b)

theorem axisLo_self {c : Vec d} {i : Fin d} {p b : ℝ} : axisLo c i p b i = p := ite_eq_left rfl

theorem axisLo_of_ne {c : Vec d} {i j : Fin d} {p b : ℝ} (hji : j ≠ i) :
    axisLo c i p b j = c j - b := ite_eq_right hji

theorem axisHi_self {c : Vec d} {i : Fin d} {q b : ℝ} : axisHi c i q b i = q := ite_eq_left rfl

theorem axisHi_of_ne {c : Vec d} {i j : Fin d} {q b : ℝ} (hji : j ≠ i) :
    axisHi c i q b j = c j + b := ite_eq_right hji

theorem mem_axisBox_iff {c : Vec d} {i : Fin d} {p q b : ℝ} {y : Vec d} :
    y ∈ axisBox c i p q b ↔
      (p < y i ∧ y i < q) ∧ ∀ j, j ≠ i → c j - b < y j ∧ y j < c j + b := by
  rw [axisBox, mem_coordBox_iff]
  constructor
  · intro hy
    refine ⟨?_, fun j hji => ?_⟩
    · have h := hy i
      rwa [axisLo_self, axisHi_self] at h
    · have h := hy j
      rwa [axisLo_of_ne hji, axisHi_of_ne hji] at h
  · rintro ⟨hmet, hother⟩ j
    by_cases hji : j = i
    · subst hji
      rw [axisLo_self, axisHi_self]
      exact hmet
    · rw [axisLo_of_ne hji, axisHi_of_ne hji]
      exact hother j hji

theorem convex_axisBox (c : Vec d) (i : Fin d) (p q b : ℝ) :
    Convex ℝ (axisBox c i p q b) :=
  convex_coordBox _ _

theorem measurableSet_axisBox (c : Vec d) (i : Fin d) (p q b : ℝ) :
    MeasurableSet (axisBox c i p q b) :=
  measurableSet_coordBox _ _

theorem volume_axisBox_ne_top (c : Vec d) (i : Fin d) (p q b : ℝ) :
    volume (axisBox c i p q b) ≠ ⊤ :=
  volume_coordBox_ne_top _ _

/-- Widening the `i`-edge and the transversal half-side enlarges the box. -/
theorem axisBox_subset_axisBox {c : Vec d} {i : Fin d} {p q b p' q' b' : ℝ}
    (hp : p' ≤ p) (hq : q ≤ q') (hb : b ≤ b') :
    axisBox c i p q b ⊆ axisBox c i p' q' b' := by
  intro y hy
  rw [mem_axisBox_iff] at hy ⊢
  refine ⟨⟨lt_of_le_of_lt hp hy.1.1, lt_of_lt_of_le hy.1.2 hq⟩, fun j hji => ?_⟩
  obtain ⟨h1, h2⟩ := hy.2 j hji
  exact ⟨by linarith only [h1, hb], by linarith only [h2, hb]⟩

/-! ### Translating in the `i` direction -/

theorem sub_smul_basisVec_apply_self (y : Vec d) (w : ℝ) (i : Fin d) :
    (y - w • (basisVec i : Vec d)) i = y i - w := by
  simp

theorem sub_smul_basisVec_apply_of_ne (y : Vec d) (w : ℝ) {i j : Fin d} (hji : j ≠ i) :
    (y - w • (basisVec i : Vec d)) j = y j := by
  simp [hji]

theorem sub_smul_basisVec_mem_axisBox {c : Vec d} {i : Fin d} {p q b p' q' b' w : ℝ}
    {y : Vec d} (hy : y ∈ axisBox c i p q b)
    (hp : p' ≤ p - w) (hq : q - w ≤ q') (hb : b ≤ b') :
    y - w • (basisVec i : Vec d) ∈ axisBox c i p' q' b' := by
  rw [mem_axisBox_iff] at hy ⊢
  refine ⟨?_, fun j hji => ?_⟩
  · rw [sub_smul_basisVec_apply_self]
    exact ⟨by linarith only [hy.1.1, hp], by linarith only [hy.1.2, hq]⟩
  · rw [sub_smul_basisVec_apply_of_ne y w hji]
    obtain ⟨h1, h2⟩ := hy.2 j hji
    exact ⟨by linarith only [h1, hb], by linarith only [h2, hb]⟩

theorem image_sub_smul_axisBox_subset {c : Vec d} {i : Fin d} {p q b p' q' b' w : ℝ}
    (hp : p' ≤ p - w) (hq : q - w ≤ q') (hb : b ≤ b') :
    (fun z => z - w • (basisVec i : Vec d)) '' axisBox c i p q b
      ⊆ axisBox c i p' q' b' := by
  rintro _ ⟨y, hy, rfl⟩
  exact sub_smul_basisVec_mem_axisBox hy hp hq hb

/-! ### Reflecting about a hyperplane transversal to `i` -/

theorem coordFaceReflection_mem_axisBox {c : Vec d} {i : Fin d} {p q b p' q' b' a : ℝ}
    {y : Vec d} (hy : y ∈ axisBox c i p q b)
    (hp : p' ≤ 2 * a - q) (hq : 2 * a - p ≤ q') (hb : b ≤ b') :
    coordFaceReflection a i y ∈ axisBox c i p' q' b' := by
  rw [mem_axisBox_iff] at hy ⊢
  refine ⟨?_, fun j hji => ?_⟩
  · rw [coordFaceReflection_apply_self]
    exact ⟨by linarith only [hy.1.2, hp], by linarith only [hy.1.1, hq]⟩
  · rw [coordFaceReflection_apply_ne a i j y hji]
    obtain ⟨h1, h2⟩ := hy.2 j hji
    exact ⟨by linarith only [h1, hb], by linarith only [h2, hb]⟩

/-! ### The sup-ball family -/

theorem metricBall_subset_axisBox {c : Vec d} {i : Fin d} {p q b p' q' b' r : ℝ}
    (hr : 0 < r) {z : Vec d} (hz : z ∈ axisBox c i p q b)
    (hp : p' ≤ p - r) (hq : q + r ≤ q') (hb : b + r ≤ b') :
    Metric.ball z r ⊆ axisBox c i p' q' b' := by
  intro y hy
  rw [Metric.mem_ball, dist_pi_lt_iff hr] at hy
  rw [mem_axisBox_iff] at hz
  rw [mem_axisBox_iff]
  have habs : ∀ j, |y j - z j| < r := by
    intro j
    have h := hy j
    rwa [Real.dist_eq] at h
  refine ⟨?_, fun j hji => ?_⟩
  · have h := abs_lt.1 (habs i)
    exact ⟨by linarith only [h.1, hz.1.1, hp], by linarith only [h.2, hz.1.2, hq]⟩
  · have h := abs_lt.1 (habs j)
    obtain ⟨h1, h2⟩ := hz.2 j hji
    exact ⟨by linarith only [h.1, h1, hb], by linarith only [h.2, h2, hb]⟩

/-! ### Two crude volume bounds -/

/-- Lower-bounding every edge of an axis box by the same number. -/
theorem pow_le_volume_toReal_axisBox {c : Vec d} {i : Fin d} {p q b e : ℝ}
    (he : 0 ≤ e) (hmet : e ≤ q - p) (hb : e ≤ 2 * b) :
    e ^ d ≤ (volume (axisBox c i p q b)).toReal := by
  have hle : ∀ j, axisLo c i p b j ≤ axisHi c i q b j := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [axisLo_self, axisHi_self]
      linarith only [hmet, he]
    · rw [axisLo_of_ne hji, axisHi_of_ne hji]
      linarith only [hb, he]
  rw [axisBox, volume_coordBox_toReal hle]
  have hedge : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      e ≤ axisHi c i q b j - axisLo c i p b j := by
    intro j _
    by_cases hji : j = i
    · subst hji
      rw [axisLo_self, axisHi_self]
      linarith only [hmet]
    · rw [axisLo_of_ne hji, axisHi_of_ne hji]
      linarith only [hb]
  have hconst : ∏ _j : Fin d, e = e ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc e ^ d = ∏ _j : Fin d, e := hconst.symm
    _ ≤ ∏ j : Fin d, (axisHi c i q b j - axisLo c i p b j) :=
        Finset.prod_le_prod₀ (fun j _ => he) hedge

/-- Upper-bounding every edge of an axis box by the same number. -/
theorem volume_toReal_axisBox_le_pow {c : Vec d} {i : Fin d} {p q b e : ℝ}
    (hpq : p ≤ q) (hb0 : 0 ≤ b) (hmet : q - p ≤ e) (hb : 2 * b ≤ e) :
    (volume (axisBox c i p q b)).toReal ≤ e ^ d := by
  have hle : ∀ j, axisLo c i p b j ≤ axisHi c i q b j := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [axisLo_self, axisHi_self]
      exact hpq
    · rw [axisLo_of_ne hji, axisHi_of_ne hji]
      linarith only [hb0]
  rw [axisBox, volume_coordBox_toReal hle]
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      (0 : ℝ) ≤ axisHi c i q b j - axisLo c i p b j := by
    intro j _
    linarith only [hle j]
  have hedge : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      axisHi c i q b j - axisLo c i p b j ≤ e := by
    intro j _
    by_cases hji : j = i
    · subst hji
      rw [axisLo_self, axisHi_self]
      exact hmet
    · rw [axisLo_of_ne hji, axisHi_of_ne hji]
      linarith only [hb]
  calc ∏ j : Fin d, (axisHi c i q b j - axisLo c i p b j) ≤ ∏ _j : Fin d, e :=
        Finset.prod_le_prod₀ hnn hedge
    _ = e ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## 2. The cube and the cube doubled across a face -/

/-- The cube of centre `c` and side `L`. -/
def sealCube (c : Vec d) (L : ℝ) : Set (Vec d) :=
  coordBox (fun j => c j - L / 2) (fun j => c j + L / 2)

/-- The cube of centre `c` and side `L`, doubled across its `σeᵢ` face (`σ = ±1`). -/
def sealDouble (c : Vec d) (L : ℝ) (i : Fin d) (sg : ℝ) : Set (Vec d) :=
  coordBox (fun j => if j = i then c j - L / 2 - (1 - sg) / 2 * L else c j - L / 2)
    (fun j => if j = i then c j + L / 2 + (1 + sg) / 2 * L else c j + L / 2)

theorem mem_sealCube_iff {c : Vec d} {L : ℝ} {y : Vec d} :
    y ∈ sealCube c L ↔ ∀ j, c j - L / 2 < y j ∧ y j < c j + L / 2 :=
  mem_coordBox_iff

theorem sealCube_eq_axisBox (c : Vec d) (L : ℝ) (i : Fin d) :
    sealCube c L = axisBox c i (c i - L / 2) (c i + L / 2) (L / 2) := by
  have hlo : (fun j => c j - L / 2) = axisLo c i (c i - L / 2) (L / 2) := by
    funext j
    show c j - L / 2 = axisLo c i (c i - L / 2) (L / 2) j
    by_cases hji : j = i
    · subst hji
      rw [axisLo_self]
    · rw [axisLo_of_ne hji]
  have hhi : (fun j => c j + L / 2) = axisHi c i (c i + L / 2) (L / 2) := by
    funext j
    show c j + L / 2 = axisHi c i (c i + L / 2) (L / 2) j
    by_cases hji : j = i
    · subst hji
      rw [axisHi_self]
    · rw [axisHi_of_ne hji]
  rw [sealCube, axisBox, hlo, hhi]

theorem sealDouble_eq_axisBox (c : Vec d) (L : ℝ) (i : Fin d) {sg : ℝ}
    (hsg : sg = 1 ∨ sg = -1) :
    sealDouble c L i sg
      = axisBox c i (c i + sg * (L / 2) - L) (c i + sg * (L / 2) + L) (L / 2) := by
  have hlo : (fun j => if j = i then c j - L / 2 - (1 - sg) / 2 * L else c j - L / 2)
      = axisLo c i (c i + sg * (L / 2) - L) (L / 2) := by
    funext j
    show (if j = i then c j - L / 2 - (1 - sg) / 2 * L else c j - L / 2)
      = axisLo c i (c i + sg * (L / 2) - L) (L / 2) j
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl, axisLo_self]
      rcases hsg with rfl | rfl <;> ring
    · rw [ite_eq_right hji, axisLo_of_ne hji]
  have hhi : (fun j => if j = i then c j + L / 2 + (1 + sg) / 2 * L else c j + L / 2)
      = axisHi c i (c i + sg * (L / 2) + L) (L / 2) := by
    funext j
    show (if j = i then c j + L / 2 + (1 + sg) / 2 * L else c j + L / 2)
      = axisHi c i (c i + sg * (L / 2) + L) (L / 2) j
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl, axisHi_self]
      rcases hsg with rfl | rfl <;> ring
    · rw [ite_eq_right hji, axisHi_of_ne hji]
  rw [sealDouble, axisBox, hlo, hhi]

/-! ## 3. The two volume ratios and the absorption coefficient -/

/-- The slab ratio `√(|K|/|S|)` is bounded by the dimension-only `√(λ⁻¹ᵈ)`. -/
theorem sqrt_volume_slab_ratio_le {vK vS L lam : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hK : vK ≤ L ^ d) (hS : (lam * L) ^ d ≤ vS) :
    Real.sqrt (vK / vS) ≤ Real.sqrt (lam⁻¹ ^ d) := by
  have hlLd : (0 : ℝ) < (lam * L) ^ d := pow_pos (mul_pos hlam hL) d
  have hSpos : 0 < vS := lt_of_lt_of_le hlLd hS
  have hkey : lam⁻¹ ^ d * (lam * L) ^ d = L ^ d := by
    rw [← mul_pow, inv_mul_cancel_left₀ (ne_of_gt hlam)]
  have h2 : lam⁻¹ ^ d * (lam * L) ^ d ≤ lam⁻¹ ^ d * vS :=
    mul_le_mul_of_nonneg_left hS (pow_nonneg (inv_nonneg.mpr hlam.le) d)
  rw [hkey] at h2
  have h4 : vK / vS ≤ lam⁻¹ ^ d :=
    (div_le_iff₀ hSpos).mpr (by linarith only [hK, h2])
  exact Real.sqrt_le_sqrt h4

/-- The Hessian ratio `√(|D|/rᵈ)` is bounded by the dimension-only `4ᵈ`. -/
theorem sqrt_volume_ball_ratio_le {vD L : ℝ} (hL : 0 < L)
    (hD : vD ≤ (2 * L) ^ d) :
    Real.sqrt (vD / (L / 8) ^ d) ≤ (4 : ℝ) ^ d := by
  have hrd : (0 : ℝ) < (L / 8) ^ d := pow_pos (by linarith only [hL]) d
  have hkey : (16 : ℝ) ^ d * (L / 8) ^ d = (2 * L) ^ d := by
    rw [← mul_pow]
    congr 1
    ring
  have h1 : vD / (L / 8) ^ d ≤ (16 : ℝ) ^ d := by
    rw [div_le_iff₀ hrd, hkey]
    exact hD
  have h4 : ((4 : ℝ) ^ d) ^ 2 = (16 : ℝ) ^ d := by
    rw [← pow_mul, mul_comm d 2, pow_mul]
    norm_num
  have h2 : Real.sqrt ((16 : ℝ) ^ d) = (4 : ℝ) ^ d := by
    rw [← h4, Real.sqrt_sq (pow_nonneg (by norm_num) d)]
  rw [← h2]
  exact Real.sqrt_le_sqrt h1

/-- The absorption coefficient at `r = L/8`, with the ratio bound `4ᵈ` and `w² = (λL)²`.
-/
theorem coef_eq_of_sq {CH L lam w : ℝ} (hL0 : L ≠ 0) (hw : w ^ 2 = (lam * L) ^ 2) :
    CH * (L / 8)⁻¹ * (L / 8)⁻¹ * (4 : ℝ) ^ d * w ^ 2
      = 64 * (CH * (4 : ℝ) ^ d) * lam ^ 2 := by
  rw [hw, inv_div]
  field_simp
  ring

/-! ## 4. `(A)` at a cube with a flush face -/

/-- The five slab memberships consumed at the **upper** flush face `{yᵢ = cᵢ + L/2}`.

Stated separately so that the five-component anonymous constructor is elaborated
in a five-hypothesis context rather than inside the main assembly. -/
private theorem sealSlabMem_upper {c : Vec d} {i : Fin d} {L hs : ℝ} (hhs0 : 0 < hs) :
    ∀ y ∈ axisBox c i (c i + L / 2 - hs) (c i + L / 2) (L / 4),
      y ∈ axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4) ∧
      coordFaceReflection (c i + L / 2) i y
        ∈ axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4) ∧
      y - hs • (basisVec i : Vec d)
        ∈ axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4) ∧
      0 < (c i + L / 2 - y i) / hs ∧ (c i + L / 2 - y i) / hs ≤ 1 := by
  intro y hy
  have hy' := mem_axisBox_iff.mp hy
  refine ⟨axisBox_subset_axisBox (by linarith only [hhs0]) (by linarith only [hhs0])
      (le_refl _) hy, ?_, ?_, ?_, ?_⟩
  · exact coordFaceReflection_mem_axisBox hy (by linarith only [hhs0])
      (by linarith only []) (le_refl _)
  · exact sub_smul_basisVec_mem_axisBox hy (by linarith only [])
      (by linarith only [hhs0]) (le_refl _)
  · exact div_pos (by linarith only [hy'.1.2]) hhs0
  · exact (div_le_one hhs0).mpr (by linarith only [hy'.1.1])

/-- The five slab memberships consumed at the **lower** flush face `{yᵢ = cᵢ − L/2}`,
the mirror image of `sealSlabMem_upper` with the inward step `-hs`. -/
private theorem sealSlabMem_lower {c : Vec d} {i : Fin d} {L hs : ℝ} (hhs0 : 0 < hs) :
    ∀ y ∈ axisBox c i (c i - L / 2) (c i - L / 2 + hs) (L / 4),
      y ∈ axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4) ∧
      coordFaceReflection (c i - L / 2) i y
        ∈ axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4) ∧
      y - (-hs) • (basisVec i : Vec d)
        ∈ axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4) ∧
      0 < (c i - L / 2 - y i) / (-hs) ∧ (c i - L / 2 - y i) / (-hs) ≤ 1 := by
  intro y hy
  have hy' := mem_axisBox_iff.mp hy
  have hdiv : (c i - L / 2 - y i) / (-hs) = (y i - (c i - L / 2)) / hs := by
    rw [show c i - L / 2 - y i = -(y i - (c i - L / 2)) from by ring, neg_div_neg_eq]
  refine ⟨axisBox_subset_axisBox (by linarith only [hhs0]) (by linarith only [hhs0])
      (le_refl _) hy, ?_, ?_, ?_, ?_⟩
  · exact coordFaceReflection_mem_axisBox hy (by linarith only [])
      (by linarith only [hhs0]) (le_refl _)
  · exact sub_smul_basisVec_mem_axisBox hy (by linarith only [hhs0])
      (by linarith only []) (le_refl _)
  · rw [hdiv]
    exact div_pos (by linarith only [hy'.1.1]) hhs0
  · rw [hdiv]
    exact (div_le_one hhs0).mpr (by linarith only [hy'.1.2])

/-- **`(A)` at a flush cube.**

Let `K = sealCube c L` be the cube of centre `c` and side `L > 0`, let `σ = ±1`
and let `a = cᵢ + σ·L/2` be the level of its `σeᵢ` face.  If `W` is odd about
`{yᵢ = a}`, square integrable on the doubled cube `D = sealDouble c L i σ`, and
`W − β` is classically harmonic on `D`, then

```text
  |β| ≤ C(d) · ‖W − β‖_{L²(K)}
```

with a constant that depends on the dimension alone.  Taking `β = ⨍_K W` gives
the flush-cube mean bound; the general-`β` form is what the composition uses. -/
theorem exists_abs_le_normalizedL2On_sealCube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : Fin d) (sg L : ℝ) (c : Vec d) (W : Vec d → ℝ) (beta : ℝ),
        (sg = 1 ∨ sg = -1) → 0 < L →
        (∀ z, W (coordFaceReflection (c i + sg * (L / 2)) i z) = -W z) →
        MemLp W 2 (volume.restrict (sealDouble c L i sg)) →
        HarmonicOnNhd ((fun y => W y - beta) ∘
            (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
          ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' sealDouble c L i sg) →
        |beta| ≤ C * normalizedL2On (sealCube c L) (fun y => W y - beta) := by
  classical
  obtain ⟨CH, hCH0, hCH⟩ := exists_abs_le_normalizedL2On_of_faceOdd d
  have hP0 : (0 : ℝ) ≤ CH * (4 : ℝ) ^ d := mul_nonneg hCH0 (pow_nonneg (by norm_num) d)
  have hQpos : (0 : ℝ) < 16 + 1152 * (CH * (4 : ℝ) ^ d) := by linarith only [hP0]
  obtain ⟨lam, hlamdef⟩ : ∃ t : ℝ, t = (16 + 1152 * (CH * (4 : ℝ) ^ d))⁻¹ := ⟨_, rfl⟩
  have hlampos : 0 < lam := by
    rw [hlamdef]
    exact inv_pos.mpr hQpos
  have hprod : lam * (16 + 1152 * (CH * (4 : ℝ) ^ d)) = 1 := by
    rw [hlamdef]
    exact inv_mul_cancel₀ (ne_of_gt hQpos)
  have hlam16 : 16 * lam ≤ 1 := by
    have hnn : 0 ≤ lam * (1152 * (CH * (4 : ℝ) ^ d)) :=
      mul_nonneg hlampos.le (by linarith only [hP0])
    have hexp : lam * (16 + 1152 * (CH * (4 : ℝ) ^ d))
        = 16 * lam + lam * (1152 * (CH * (4 : ℝ) ^ d)) := by ring
    linarith only [hprod, hnn, hexp]
  have hroom : 1152 * (CH * (4 : ℝ) ^ d) * lam ^ 2 ≤ 1 := by
    have hsq : lam ^ 2 * (16 + 1152 * (CH * (4 : ℝ) ^ d)) ^ 2 = 1 := by
      have hh : lam ^ 2 * (16 + 1152 * (CH * (4 : ℝ) ^ d)) ^ 2
          = (lam * (16 + 1152 * (CH * (4 : ℝ) ^ d))) ^ 2 := by ring
      rw [hh, hprod, one_pow]
    have hcmp : 1152 * (CH * (4 : ℝ) ^ d) ≤ (16 + 1152 * (CH * (4 : ℝ) ^ d)) ^ 2 := by
      have hsq0 : (0 : ℝ) ≤ (1152 * (CH * (4 : ℝ) ^ d)) ^ 2 := sq_nonneg _
      have hexp : (16 + 1152 * (CH * (4 : ℝ) ^ d)) ^ 2
          = 256 + 32 * (1152 * (CH * (4 : ℝ) ^ d))
            + (1152 * (CH * (4 : ℝ) ^ d)) ^ 2 := by ring
      linarith only [hsq0, hP0, hexp]
    have hmul := mul_le_mul_of_nonneg_right hcmp (sq_nonneg lam)
    have heq : (16 + 1152 * (CH * (4 : ℝ) ^ d)) ^ 2 * lam ^ 2 = 1 := by
      rw [mul_comm]
      exact hsq
    linarith only [hmul, heq]
  refine ⟨6 * Real.sqrt (lam⁻¹ ^ d) + 12 * (64 * (CH * (4 : ℝ) ^ d) * lam ^ 2), ?_, ?_⟩
  · have h1 : 0 ≤ Real.sqrt (lam⁻¹ ^ d) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ 64 * (CH * (4 : ℝ) ^ d) * lam ^ 2 :=
      mul_nonneg (by linarith only [hP0]) (sq_nonneg lam)
    linarith only [h1, h2]
  intro i sg L c W beta hsg hL hodd hWD hharm
  have hL0 : L ≠ 0 := ne_of_gt hL
  obtain ⟨hs, hhsdef⟩ : ∃ t : ℝ, t = lam * L := ⟨_, rfl⟩
  have hhs0 : 0 < hs := by
    rw [hhsdef]
    exact mul_pos hlampos hL
  have h16hs : 16 * hs ≤ L := by
    have h := mul_le_mul_of_nonneg_right hlam16 hL.le
    rw [hhsdef]
    calc 16 * (lam * L) = 16 * lam * L := by ring
      _ ≤ 1 * L := h
      _ = L := one_mul L
  have hLd : (0 : ℝ) < L ^ d := pow_pos hL d
  have hhsd : (0 : ℝ) < hs ^ d := pow_pos hhs0 d
  rcases hsg with rfl | rfl
  · -- the upper face `{yᵢ = cᵢ + L/2}`
    rw [show c i + (1 : ℝ) * (L / 2) = c i + L / 2 from by ring] at hodd
    have hDeq : sealDouble c L i 1
        = axisBox c i (c i - L / 2) (c i + 3 * L / 2) (L / 2) := by
      rw [sealDouble_eq_axisBox c L i (Or.inl rfl),
        show c i + (1 : ℝ) * (L / 2) - L = c i - L / 2 from by ring,
        show c i + (1 : ℝ) * (L / 2) + L = c i + 3 * L / 2 from by ring]
    rw [hDeq] at hWD hharm
    rw [sealCube_eq_axisBox c L i]
    have hKlo : L ^ d
        ≤ (volume (axisBox c i (c i - L / 2) (c i + L / 2) (L / 2))).toReal :=
      pow_le_volume_toReal_axisBox hL.le (by linarith only []) (by linarith only [])
    have hKhi : (volume (axisBox c i (c i - L / 2) (c i + L / 2) (L / 2))).toReal
        ≤ L ^ d :=
      volume_toReal_axisBox_le_pow (by linarith only [hL]) (by linarith only [hL])
        (by linarith only []) (by linarith only [])
    have hDlo : L ^ d
        ≤ (volume (axisBox c i (c i - L / 2) (c i + 3 * L / 2) (L / 2))).toReal :=
      pow_le_volume_toReal_axisBox hL.le (by linarith only [hL]) (by linarith only [])
    have hDhi : (volume (axisBox c i (c i - L / 2) (c i + 3 * L / 2) (L / 2))).toReal
        ≤ (2 * L) ^ d :=
      volume_toReal_axisBox_le_pow (by linarith only [hL]) (by linarith only [hL])
        (by linarith only []) (by linarith only [hL])
    have hSlo : hs ^ d
        ≤ (volume (axisBox c i (c i + L / 2 - hs) (c i + L / 2) (L / 4))).toReal :=
      pow_le_volume_toReal_axisBox hhs0.le (by linarith only [])
        (by linarith only [h16hs, hL])
    have hSlo' : (lam * L) ^ d
        ≤ (volume (axisBox c i (c i + L / 2 - hs) (c i + L / 2) (L / 4))).toReal := by
      rw [← hhsdef]
      exact hSlo
    have hSmem : ∀ y ∈ axisBox c i (c i + L / 2 - hs) (c i + L / 2) (L / 4),
        y ∈ axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4) ∧
        coordFaceReflection (c i + L / 2) i y
          ∈ axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4) ∧
        y - hs • (basisVec i : Vec d)
          ∈ axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4) ∧
        0 < (c i + L / 2 - y i) / hs ∧ (c i + L / 2 - y i) / hs ≤ 1 :=
      sealSlabMem_upper hhs0
    have hballs : ∀ z ∈ axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4),
        Metric.ball z (L / 8) ⊆ axisBox c i (c i - L / 2) (c i + 3 * L / 2) (L / 2) := by
      intro z hz
      exact metricBall_subset_axisBox (by linarith only [hL]) hz
        (by linarith only [h16hs, hhs0, hL]) (by linarith only [h16hs, hhs0, hL])
        (by linarith only [hL])
    have hDsplit : ∀ y ∈ axisBox c i (c i - L / 2) (c i + 3 * L / 2) (L / 2),
        y ∈ axisBox c i (c i - L / 2) (c i + L / 2) (L / 2) ∨
        coordFaceReflection (c i + L / 2) i y
          ∈ axisBox c i (c i - L / 2) (c i + L / 2) (L / 2) ∨
        y i = c i + L / 2 := by
      intro y hy
      have hy' := mem_axisBox_iff.mp hy
      rcases lt_trichotomy (y i) (c i + L / 2) with hlt | heq | hgt
      · exact Or.inl (mem_axisBox_iff.mpr ⟨⟨hy'.1.1, hlt⟩, hy'.2⟩)
      · exact Or.inr (Or.inr heq)
      · refine Or.inr (Or.inl (mem_axisBox_iff.mpr ⟨⟨?_, ?_⟩, fun j hji => ?_⟩))
        · rw [coordFaceReflection_apply_self]
          linarith only [hy'.1.2]
        · rw [coordFaceReflection_apply_self]
          linarith only [hgt]
        · rw [coordFaceReflection_apply_ne _ i j y hji]
          exact hy'.2 j hji
    have hcoef : CH * (L / 8)⁻¹ * (L / 8)⁻¹ * (4 : ℝ) ^ d * hs ^ 2
        = 64 * (CH * (4 : ℝ) ^ d) * lam ^ 2 :=
      coef_eq_of_sq hL0 (by rw [hhsdef])
    have hroom' : 9 * (CH * (L / 8)⁻¹ * (L / 8)⁻¹ * (4 : ℝ) ^ d * hs ^ 2) ≤ 1 / 2 := by
      rw [hcoef]
      linarith only [hroom]
    have hmain := hCH i (c i + L / 2) hs (L / 8)
      (axisBox c i (c i - L / 2) (c i + L / 2) (L / 2))
      (axisBox c i (c i - L / 2) (c i + 3 * L / 2) (L / 2))
      (axisBox c i (c i + L / 2 - hs) (c i + L / 2) (L / 4))
      (axisBox c i (c i + L / 2 - 2 * hs) (c i + L / 2 + hs) (L / 4))
      W beta (Real.sqrt (lam⁻¹ ^ d)) ((4 : ℝ) ^ d)
      hodd hWD hharm (convex_axisBox _ _ _ _ _)
      (axisBox_subset_axisBox (by linarith only [h16hs, hhs0])
        (by linarith only [h16hs, hhs0]) (by linarith only [hL]))
      (axisBox_subset_axisBox (by linarith only [h16hs, hhs0]) (by linarith only [])
        (by linarith only [hL]))
      (axisBox_subset_axisBox (by linarith only []) (by linarith only [hL])
        (by linarith only []))
      (image_sub_smul_axisBox_subset (by linarith only [h16hs, hhs0])
        (by linarith only [hhs0]) (by linarith only [hL]))
      hSmem hballs (by linarith only [hL]) hDsplit
      (measurableSet_axisBox _ _ _ _ _) (measurableSet_axisBox _ _ _ _ _)
      (measurableSet_axisBox _ _ _ _ _) (volume_axisBox_ne_top _ _ _ _ _)
      (by linarith only [hSlo, hhsd]) (by linarith only [hKlo, hLd])
      (by linarith only [hDlo, hLd]) (by linarith only [hKhi, hDlo])
      (sqrt_volume_slab_ratio_le hL hlampos hKhi hSlo')
      (sqrt_volume_ball_ratio_le hL hDhi)
      (pow_nonneg (by norm_num) d) hroom'
    rw [hcoef] at hmain
    exact hmain
  · -- the lower face `{yᵢ = cᵢ − L/2}`
    rw [show c i + (-1 : ℝ) * (L / 2) = c i - L / 2 from by ring] at hodd
    have hDeq : sealDouble c L i (-1)
        = axisBox c i (c i - 3 * L / 2) (c i + L / 2) (L / 2) := by
      rw [sealDouble_eq_axisBox c L i (Or.inr rfl),
        show c i + (-1 : ℝ) * (L / 2) - L = c i - 3 * L / 2 from by ring,
        show c i + (-1 : ℝ) * (L / 2) + L = c i + L / 2 from by ring]
    rw [hDeq] at hWD hharm
    rw [sealCube_eq_axisBox c L i]
    have hKlo : L ^ d
        ≤ (volume (axisBox c i (c i - L / 2) (c i + L / 2) (L / 2))).toReal :=
      pow_le_volume_toReal_axisBox hL.le (by linarith only []) (by linarith only [])
    have hKhi : (volume (axisBox c i (c i - L / 2) (c i + L / 2) (L / 2))).toReal
        ≤ L ^ d :=
      volume_toReal_axisBox_le_pow (by linarith only [hL]) (by linarith only [hL])
        (by linarith only []) (by linarith only [])
    have hDlo : L ^ d
        ≤ (volume (axisBox c i (c i - 3 * L / 2) (c i + L / 2) (L / 2))).toReal :=
      pow_le_volume_toReal_axisBox hL.le (by linarith only [hL]) (by linarith only [])
    have hDhi : (volume (axisBox c i (c i - 3 * L / 2) (c i + L / 2) (L / 2))).toReal
        ≤ (2 * L) ^ d :=
      volume_toReal_axisBox_le_pow (by linarith only [hL]) (by linarith only [hL])
        (by linarith only []) (by linarith only [hL])
    have hSlo : hs ^ d
        ≤ (volume (axisBox c i (c i - L / 2) (c i - L / 2 + hs) (L / 4))).toReal :=
      pow_le_volume_toReal_axisBox hhs0.le (by linarith only [])
        (by linarith only [h16hs, hL])
    have hSlo' : (lam * L) ^ d
        ≤ (volume (axisBox c i (c i - L / 2) (c i - L / 2 + hs) (L / 4))).toReal := by
      rw [← hhsdef]
      exact hSlo
    have hSmem : ∀ y ∈ axisBox c i (c i - L / 2) (c i - L / 2 + hs) (L / 4),
        y ∈ axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4) ∧
        coordFaceReflection (c i - L / 2) i y
          ∈ axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4) ∧
        y - (-hs) • (basisVec i : Vec d)
          ∈ axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4) ∧
        0 < (c i - L / 2 - y i) / (-hs) ∧ (c i - L / 2 - y i) / (-hs) ≤ 1 :=
      sealSlabMem_lower hhs0
    have hballs : ∀ z ∈ axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4),
        Metric.ball z (L / 8) ⊆ axisBox c i (c i - 3 * L / 2) (c i + L / 2) (L / 2) := by
      intro z hz
      exact metricBall_subset_axisBox (by linarith only [hL]) hz
        (by linarith only [h16hs, hhs0, hL]) (by linarith only [h16hs, hhs0, hL])
        (by linarith only [hL])
    have hDsplit : ∀ y ∈ axisBox c i (c i - 3 * L / 2) (c i + L / 2) (L / 2),
        y ∈ axisBox c i (c i - L / 2) (c i + L / 2) (L / 2) ∨
        coordFaceReflection (c i - L / 2) i y
          ∈ axisBox c i (c i - L / 2) (c i + L / 2) (L / 2) ∨
        y i = c i - L / 2 := by
      intro y hy
      have hy' := mem_axisBox_iff.mp hy
      rcases lt_trichotomy (y i) (c i - L / 2) with hlt | heq | hgt
      · refine Or.inr (Or.inl (mem_axisBox_iff.mpr ⟨⟨?_, ?_⟩, fun j hji => ?_⟩))
        · rw [coordFaceReflection_apply_self]
          linarith only [hlt]
        · rw [coordFaceReflection_apply_self]
          linarith only [hy'.1.1]
        · rw [coordFaceReflection_apply_ne _ i j y hji]
          exact hy'.2 j hji
      · exact Or.inr (Or.inr heq)
      · exact Or.inl (mem_axisBox_iff.mpr ⟨⟨hgt, hy'.1.2⟩, hy'.2⟩)
    have hcoef : CH * (L / 8)⁻¹ * (L / 8)⁻¹ * (4 : ℝ) ^ d * (-hs) ^ 2
        = 64 * (CH * (4 : ℝ) ^ d) * lam ^ 2 :=
      coef_eq_of_sq hL0 (by rw [hhsdef]; ring)
    have hroom' : 9 * (CH * (L / 8)⁻¹ * (L / 8)⁻¹ * (4 : ℝ) ^ d * (-hs) ^ 2) ≤ 1 / 2 := by
      rw [hcoef]
      linarith only [hroom]
    have hmain := hCH i (c i - L / 2) (-hs) (L / 8)
      (axisBox c i (c i - L / 2) (c i + L / 2) (L / 2))
      (axisBox c i (c i - 3 * L / 2) (c i + L / 2) (L / 2))
      (axisBox c i (c i - L / 2) (c i - L / 2 + hs) (L / 4))
      (axisBox c i (c i - L / 2 - hs) (c i - L / 2 + 2 * hs) (L / 4))
      W beta (Real.sqrt (lam⁻¹ ^ d)) ((4 : ℝ) ^ d)
      hodd hWD hharm (convex_axisBox _ _ _ _ _)
      (axisBox_subset_axisBox (by linarith only [h16hs, hhs0])
        (by linarith only [h16hs, hhs0]) (by linarith only [hL]))
      (axisBox_subset_axisBox (by linarith only []) (by linarith only [h16hs, hhs0])
        (by linarith only [hL]))
      (axisBox_subset_axisBox (by linarith only [hL]) (by linarith only [])
        (by linarith only []))
      (image_sub_smul_axisBox_subset (by linarith only [hhs0])
        (by linarith only [h16hs, hhs0]) (by linarith only [hL]))
      hSmem hballs (by linarith only [hL]) hDsplit
      (measurableSet_axisBox _ _ _ _ _) (measurableSet_axisBox _ _ _ _ _)
      (measurableSet_axisBox _ _ _ _ _) (volume_axisBox_ne_top _ _ _ _ _)
      (by linarith only [hSlo, hhsd]) (by linarith only [hKlo, hLd])
      (by linarith only [hDlo, hLd]) (by linarith only [hKhi, hDlo])
      (sqrt_volume_slab_ratio_le hL hlampos hKhi hSlo')
      (sqrt_volume_ball_ratio_le hL hDhi)
      (pow_nonneg (by norm_num) d) hroom'
    rw [hcoef] at hmain
    exact hmain

/-! ## 5. The flush cube of the well-placed clamp -/

/-- A translated open triadic cube **is** a `sealCube`. -/
theorem image_add_eq_sealCube (c : Vec d) (j : ℤ) :
    (fun y => c + y) '' openCubeSet (originCube d j) = sealCube c ((3 : ℝ) ^ j) := by
  ext y
  rw [mem_image_add_openCubeSet_coord_iff, mem_sealCube_iff]
  constructor
  · intro hy k
    obtain ⟨h1, h2⟩ := hy k
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro hy k
    obtain ⟨h1, h2⟩ := hy k
    exact ⟨by linarith only [h1], by linarith only [h2]⟩

/-- The centre of the flush **sub**-cube of side `3ⁿ` sharing the `σeᵢ` face of the
well-placed cube of side `3ᵏ`.

The body is written in the `if`-normal form of
`SealCaccioppoliGeometry.flushSubCentre`, so that at `k = n + 2` the two
definitions are the *same term*; see the module docstring. -/
def sealFlushSubCentre (z : Vec d) (m k n : ℤ) (i : Fin d) (sg : ℝ) : Vec d :=
  fun r => wellPlacedCentre z m k r +
    (if r = i then sg * (((3 : ℝ) ^ k - (3 : ℝ) ^ n) / 2) else 0)

theorem sealFlushSubCentre_apply (z : Vec d) (m k n : ℤ) (i : Fin d) (sg : ℝ)
    (r : Fin d) :
    sealFlushSubCentre z m k n i sg r = wellPlacedCentre z m k r +
      (if r = i then sg * (((3 : ℝ) ^ k - (3 : ℝ) ^ n) / 2) else 0) := rfl

theorem sealFlushSubCentre_apply_self (z : Vec d) (m k n : ℤ) (i : Fin d) (sg : ℝ) :
    sealFlushSubCentre z m k n i sg i
      = wellPlacedCentre z m k i + sg * (((3 : ℝ) ^ k - (3 : ℝ) ^ n) / 2) := by
  rw [sealFlushSubCentre_apply, ite_eq_left (rfl : i = i)]

/-- **The flush face sits in the frontier hyperplane.**

On the boundary branch the `σeᵢ` face of the well-placed cube of side `3ᵏ` lies
exactly in `{σ yᵢ = ½·3ᵐ}`, and so does the `σeᵢ` face of the concentric-in-`σeᵢ`
sub-cube of side `3ⁿ` centred at `sealFlushSubCentre z m k n i σ`. -/
theorem sealFlushSubCentre_faceLevel {m k n : ℤ} (hkm : k ≤ m) {z : Vec d} {i : Fin d}
    {sg : ℝ} (hsg : sg = 1 ∨ sg = -1) (hover : wellPlacedHalfGap m k < sg * z i) :
    sealFlushSubCentre z m k n i sg i + sg * ((3 : ℝ) ^ n / 2)
      = sg * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  have hflush := wellPlacedCentre_flush hkm hsg hover
  rw [wellPlacedHalfGap] at hflush
  rw [sealFlushSubCentre_apply_self]
  rcases hsg with rfl | rfl
  · simp only [one_mul] at hflush ⊢
    linarith only [hflush]
  · simp only [neg_mul, one_mul] at hflush ⊢
    linarith only [hflush]

/-- **`(A)` at the flush sub-cube of the boundary branch.**

At the boundary branch of the covering — the overhang `wellPlacedHalfGap m k <
σ·zᵢ` — the cube of side `3ⁿ` centred at `sealFlushSubCentre z m k n i σ` has its
`σeᵢ` face exactly in the frontier hyperplane `{σ yᵢ = ½·3ᵐ}`, so the flush-cube
mean bound applies there verbatim, with the same dimension-only constant.  The
scale-`k` well-placed cube itself is the case `n = k`. -/
theorem exists_abs_le_normalizedL2On_sealFlushSubCube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m k n : ℤ) (z : Vec d) (i : Fin d) (sg : ℝ) (W : Vec d → ℝ) (beta : ℝ),
        k ≤ m → (sg = 1 ∨ sg = -1) → wellPlacedHalfGap m k < sg * z i →
        (∀ y, W (coordFaceReflection (sg * ((1 / 2 : ℝ) * (3 : ℝ) ^ m)) i y) = -W y) →
        MemLp W 2 (volume.restrict
          (sealDouble (sealFlushSubCentre z m k n i sg) ((3 : ℝ) ^ n) i sg)) →
        HarmonicOnNhd ((fun y => W y - beta) ∘
            (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
          ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
            sealDouble (sealFlushSubCentre z m k n i sg) ((3 : ℝ) ^ n) i sg) →
        |beta| ≤ C * normalizedL2On
          ((fun y => sealFlushSubCentre z m k n i sg + y) '' openCubeSet (originCube d n))
          (fun y => W y - beta) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_normalizedL2On_sealCube d
  refine ⟨C, hC0, ?_⟩
  intro m k n z i sg W beta hkm hsg hover hodd hWD hharm
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hodd' : ∀ y, W (coordFaceReflection
      (sealFlushSubCentre z m k n i sg i + sg * ((3 : ℝ) ^ n / 2)) i y) = -W y := by
    rw [sealFlushSubCentre_faceLevel hkm hsg hover]
    exact hodd
  rw [image_add_eq_sealCube]
  exact hC i sg ((3 : ℝ) ^ n) (sealFlushSubCentre z m k n i sg) W beta hsg h3 hodd' hWD hharm

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
