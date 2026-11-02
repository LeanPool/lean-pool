/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumSplit

/-!
# OneStepBoundaryHonest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary one-step contraction at the manuscript competitor `v − ℓ_h − v₁`

The proved boundary endpoint
at the met set
asks the met-face oddness and the classical harmonicity of the **harmonic
replacement `v` itself**; but `v = h` on the met portion of `∂□_m`, so that
clause forces `v` to vanish there
(`Regularity.StepFourBoundaryJoin.oddCompetitor_eq_zero_on_metUpperFace`): the
proved branch is the `[∇h] = 0` specialization, and indeed it calls the
one-step at `K_h := 0`.

Here the odd-class binders are asked of the manuscript's **shifted** competitor

```text
  V_odd = v − ℓ_h − v₁
```

— the object whose zero trace on the met faces the chain actually produces
(the split datum's localized zero trace) — while the
`L²` comparison binder stays on `u − v`, the anchor's own object.  The datum
enters through the **already existing** `K_h` slot of
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox`, at the printed
`K_h ≍ [∇h]_{C^{0,1/2}(U_2)}`.

## What is *not* claimed

No boundary Schauder estimate for `∇v` itself is proved or assumed: the
`C^{1,1/2}` data lives on `V_odd`, and `v₁` is never differentiated.  This is
the honest reading ("subtract a controlled extension first"); the printed
sentence `[∇v]_{C^{0,1/2}(U_3)} ≤^{-n/2}E(v,U_2) + C[∇h]` is *reproduced at the
level of the excess conclusion*, not re-derived as a gradient-seminorm
statement.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The excess is invariant under subtracting an affine function -/

/-- Affine functions add. -/
theorem affineEval_add (c c' : ℝ) (g g' : Vec d) (y : Vec d) :
    affineEval c g y + affineEval c' g' y = affineEval (c + c') (g + g') y := by
  have hdot : vecDot (g + g') y = vecDot g y + vecDot g' y := by
    simp only [vecDot, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [affineEval, hdot]
  ring

/-- **The competitor set is unchanged by an affine shift.**  Subtracting a fixed
affine function permutes the affine competitors, so it moves no distance. -/
theorem affineDistSet_sub_affineEval (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) :
    affineDistSet W (fun y => u y - affineEval c g y) = affineDistSet W u := by
  ext r
  constructor
  · rintro ⟨⟨c', g'⟩, rfl⟩
    refine ⟨(c + c', g + g'), ?_⟩
    change affineDistOn W u (c + c') (g + g')
      = affineDistOn W (fun y => u y - affineEval c g y) c' g'
    simp only [affineDistOn]
    congr 1
    funext y
    rw [← affineEval_add]
    ring
  · rintro ⟨⟨c', g'⟩, rfl⟩
    refine ⟨(c' - c, g' - g), ?_⟩
    change affineDistOn W (fun y => u y - affineEval c g y) (c' - c) (g' - g)
      = affineDistOn W u c' g'
    simp only [affineDistOn]
    congr 1
    funext y
    have hc : c + (c' - c) = c' := by ring
    have hg : g + (g' - g) = g' := by abel
    have hadd : affineEval c g y + affineEval (c' - c) (g' - g) y = affineEval c' g' y := by
      rw [affineEval_add, hc, hg]
    linarith only [hadd]

/-- The raw excess is invariant under an affine shift. -/
theorem affineExcessRaw_sub_affineEval (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) :
    affineExcessRaw W (fun y => u y - affineEval c g y) = affineExcessRaw W u := by
  simp only [affineExcessRaw, affineDistSet_sub_affineEval]

/-- The excess is invariant under an affine shift. -/
theorem affineExcess_sub_affineEval (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) :
    affineExcess W (fun y => u y - affineEval c g y) = affineExcess W u := by
  simp only [affineExcess, affineExcessRaw_sub_affineEval]

/-- **The affine shift is excess-free.**  `E(u − ℓ_h, W) = E(u, W)`: the
manuscript's datum subtraction costs no constant at all. -/
theorem affineExcess_sub_affineLift (W : Set (Vec d)) (x : Vec d) (c : ℝ)
    (A : Vec d) (u : Vec d → ℝ) :
    affineExcess W (fun y => u y - affineLift x c A y) = affineExcess W u := by
  rw [affineLift_eq_affineEval]
  exact affineExcess_sub_affineEval W u _ _

/-! ## 2. The `L²` price of an almost-everywhere bounded corrector -/

/-- **`L^∞ → L²` at an almost-everywhere bound.**  The corrector's bound is
delivered a.e. by `OneStepDatumSplit.exists_datumCorrector`, so the pointwise
version of this step is not available. -/
theorem normalizedL2On_le_of_ae_abs_le {W : Set (Vec d)} (hWpos : 0 < volume W)
    (hWtop : volume W ≠ ⊤) {f : Vec d → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : MemLp f 2 (volume.restrict W))
    (hbd : ∀ᵐ y ∂(volume.restrict W), |f y| ≤ R) :
    normalizedL2On W f ≤ R := by
  refine normalizedL2On_le_of_sq_le hR ?_
  have hVpos : 0 < (volume W).toReal := ENNReal.toReal_pos hWpos.ne' hWtop
  have hint1 : IntegrableOn (fun y => f y ^ 2) W volume := hf.integrable_sq
  have hint2 : IntegrableOn (fun _ : Vec d => R ^ 2) W volume := integrableOn_const hWtop
  have hle : (∫ y in W, f y ^ 2) ≤ ∫ _y in W, R ^ 2 := by
    refine setIntegral_mono_ae_restrict hint1 hint2 ?_
    filter_upwards [hbd] with y hy
    obtain ⟨hl, hr⟩ := abs_le.1 hy
    exact sq_le_sq' hl hr
  have hconst : (∫ _y in W, R ^ 2) = (volume W).toReal * R ^ 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul]
  rw [hconst] at hle
  change (volume W).toReal⁻¹ * ∫ y in W, f y ^ 2 ≤ R ^ 2
  have hmul := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hVpos.le)
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hVpos), one_mul] at hmul
  exact hmul

/-! ## 3. The datum leg's constant, and the exact propagation identity -/

/-- The constant of the boundary datum leg:
`triangleRemainderConst d C k · 3^{-5} · (3^k)^{1/2}`. -/
def boundaryDatumLegConst (d : ℕ) (Csch : ℝ) (k : ℕ) : ℝ :=
  triangleRemainderConst d Csch k * (1 / 243 : ℝ) * ((3 : ℝ) ^ (k : ℤ)) ^ (1 / 2 : ℝ)

theorem boundaryDatumLegConst_nonneg (d : ℕ) {Csch : ℝ} (hCsch : 0 ≤ Csch) (k : ℕ) :
    0 ≤ boundaryDatumLegConst d Csch k := by
  have h1 : (0 : ℝ) ≤ triangleRemainderConst d Csch k :=
    triangleRemainderConst_nonneg d hCsch k
  have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ (k : ℤ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (zpow_pos (by norm_num) _).le _
  exact mul_nonneg (mul_nonneg h1 (by norm_num)) h2

/-- **The propagation is exact.**  The corrector's `L²` price, carried at the
remainder weight `triangleRemainderConst d C k · 3^{-n}`, *is* the printed
`K_h`-leg `C_t · (3^{n-k})^{1/2} · K_h'` at `K_h' = boundaryDatumLegConst d C k
· K_h`.  No inequality, no slack. -/
theorem triangleRemainder_mul_datumResidual (d : ℕ) (Csch : ℝ) (k : ℕ) (n : ℤ)
    (Kh : ℝ) :
    triangleRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * datumResidualBound d n Kh)
      = taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
          * (boundaryDatumLegConst d Csch k * Kh) := by
  have hsplit : ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ (k : ℤ)) ^ (1 / 2 : ℝ)
      = ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (zpow_pos (by norm_num) _).le (zpow_pos (by norm_num) _).le,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      show n - (k : ℤ) + (k : ℤ) = n by ring]
  have h3 : (3 : ℝ) ^ (-3 : ℝ) = 1 / 27 := by
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have h2 : (2 : ℝ) ^ (-(3 / 2) : ℝ) = ((1 : ℝ) / 2) ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_neg (by norm_num), show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num)]
  have hkey : taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
        * (boundaryDatumLegConst d Csch k * Kh)
      = taylorContractionConst d * (1 / 243 : ℝ) * triangleRemainderConst d Csch k * Kh
          * (((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ (k : ℤ)) ^ (1 / 2 : ℝ)) := by
    simp only [boundaryDatumLegConst]
    ring
  rw [hkey, hsplit, datumResidualBound_zpow_mul, h3, h2]
  simp only [taylorContractionConst]
  ring

/-! ## 3b. The join's folding device, with the datum leg carried -/

/-- The datum leg's constant is nondecreasing in the Schauder constant. -/
theorem boundaryDatumLegConst_mono (d : ℕ) {Csch Csch' : ℝ} (hCsch : Csch ≤ Csch')
    (k : ℕ) :
    boundaryDatumLegConst d Csch k ≤ boundaryDatumLegConst d Csch' k := by
  have hT : triangleRemainderConst d Csch k ≤ triangleRemainderConst d Csch' k := by
    simp only [triangleRemainderConst]
    have := mul_le_mul_of_nonneg_left hCsch
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) (taylorContractionConst_nonneg d))
    linarith only [this]
  have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ (k : ℤ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (zpow_pos (by norm_num) _).le _
  simp only [boundaryDatumLegConst]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hT (by norm_num)) h2

/-- **The one-step conclusion's constant monotonicity with the printed datum
leg carried.**  The join raises both branches to `max (schauderWindowConst d) C_b`;
this is the three-leg version of that move, so the boundary branch's datum leg
travels with it. -/
theorem oneStepConclusionKh_mono (d : ℕ) {Csch Csch' : ℝ} (hCsch : Csch ≤ Csch')
    {k : ℕ} {n : ℤ} {Ek E0 R Kh : ℝ} (hE0 : 0 ≤ E0) (hR : 0 ≤ R) (hKh : 0 ≤ Kh)
    (h : Ek ≤ taylorContractionConst d * Csch * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0
          + triangleRemainderConst d Csch k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R))
          + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
            * (boundaryDatumLegConst d Csch k * Kh)) :
    Ek ≤ taylorContractionConst d * Csch' * windowRatioConst d 2
          * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0
        + triangleRemainderConst d Csch' k
          * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
          * (boundaryDatumLegConst d Csch' k * Kh) := by
  have hcontr : taylorContractionConst d * Csch * windowRatioConst d 2
        * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0
      ≤ taylorContractionConst d * Csch' * windowRatioConst d 2
        * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0 := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ (windowRatioConst_nonneg d 2))
      (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)) hE0
    exact mul_le_mul_of_nonneg_left hCsch (taylorContractionConst_nonneg d)
  have hrem : triangleRemainderConst d Csch k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R))
      ≤ triangleRemainderConst d Csch' k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R)) := by
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (zpow_pos (by norm_num) (-n)).le
        (mul_nonneg (Real.sqrt_nonneg _) hR))
    simp only [triangleRemainderConst]
    have := mul_le_mul_of_nonneg_left hCsch
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) (taylorContractionConst_nonneg d))
    linarith only [this]
  have hTnn : (0 : ℝ) ≤ taylorContractionConst d
      * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) :=
    mul_nonneg (taylorContractionConst_nonneg d)
      (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)
  have h3 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (boundaryDatumLegConst_mono d hCsch k) hKh) hTnn
  exact h.trans (add_le_add (add_le_add hcontr hrem) h3)

/-! ## 4. The deterministic core -/

/-- **The one-step contraction at the manuscript competitor, deterministic
form.**

The `C^{1,1/2}` data is asked of `V_odd = v − ℓ_h − v₁` on `U_3`, the `L²`
comparison of `u − v` on `U_2`, and the corrector only through its `L^∞` bound.
The `K_h` leg comes out in the printed shape.  No probability, no good event. -/
theorem excessDecay_oneStep_boundary_datumSplit_core (hd : d ≠ 0) {m n : ℤ}
    {k : ℕ} (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m))
    (hnm : n - 1 ≤ m) {u v v₁ V : Vec d → ℝ} {cl : ℝ} {Al : Vec d} {Kh Csch : ℝ}
    (hKh : 0 ≤ Kh) (hCsch : 0 ≤ Csch)
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (hVU : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2))))
    (hVae : V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))]
      (fun y => v y - affineLift x cl Al y - v₁ y))
    (hv₁ : ∀ᵐ y ∂(volume.restrict (truncatedWindow x m (n - 2))),
      |v₁ y| ≤ datumResidualBound d n Kh)
    {K : ℝ} (hK : 0 ≤ K)
    (hint : ∀ i, IntegrableOn (fun p => gradField V p i)
      (truncatedWindow x m (n - 3)) volume)
    (hgrad : HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V))
    (hhol : HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K
      (gradField V))
    (hschauder : K ≤ Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
      * affineExcess (truncatedWindow x m (n - 2)) V)
    {D : ℝ}
    (hD : normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y) ≤ D) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * Csch * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
            * (boundaryDatumLegConst d Csch k * Kh) := by
  have hmeas2 : MeasurableSet (truncatedWindow x m (n - 2)) :=
    measurableSet_truncatedWindow x m (n - 2)
  have hsub32 : truncatedWindow x m (n - 3) ⊆ truncatedWindow x m (n - 2) :=
    truncatedWindow_mono x m (by omega)
  have hsub20 : truncatedWindow x m (n - 2) ⊆ truncatedWindow x m n :=
    truncatedWindow_mono x m (by omega)
  -- the localized competitor: `V` cut off to `U_2`, where all four windows live
  have hWmem : MemLp (Set.indicator (truncatedWindow x m (n - 2)) V) 2
      (volume.restrict (truncatedWindow x m n)) :=
    ((memLp_indicator_iff_restrict hmeas2).2 hVU).restrict _
  have hWeq : Set.EqOn (Set.indicator (truncatedWindow x m (n - 2)) V) V
      (truncatedWindow x m (n - 2)) :=
    fun y hy => Set.indicator_of_mem hy _
  have hgradW : HasGradientOn (truncatedWindow x m (n - 3))
      (Set.indicator (truncatedWindow x m (n - 2)) V) (gradField V) := by
    intro y hy
    exact (hgrad y hy).congr' (fun p hp => hWeq (hsub32 hp)) hy
  have hexcW : affineExcess (truncatedWindow x m (n - 2))
      (Set.indicator (truncatedWindow x m (n - 2)) V)
      = affineExcess (truncatedWindow x m (n - 2)) V :=
    affineExcess_congr_eqOn hmeas2 hWeq
  have hschW : K ≤ Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
      * affineExcess (truncatedWindow x m (n - 2))
          (Set.indicator (truncatedWindow x m (n - 2)) V) + 0 := by
    rw [hexcW, add_zero]
    exact hschauder
  -- the affine-shifted datum
  have hUmem : MemLp (fun y => u y - affineLift x cl Al y) 2
      (volume.restrict (truncatedWindow x m n)) := by
    rw [affineLift_eq_affineEval]
    exact hu.sub (memLp_affineEval_truncatedWindow x _ _)
  have htri := excessDecay_oneStep_triangle_of_schauder hd hk hx hnm hUmem hWmem hK
    hCsch hint hgradW hhol hschW
  rw [affineExcess_sub_affineLift, affineExcess_sub_affineLift] at htri
  simp only [mul_zero, add_zero] at htri
  -- the corrector's `L²` price on `U_2`
  have hv2 : MemLp v 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset hsub20 hv
  have hu2 : MemLp u 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset hsub20 hu
  have hcorr : MemLp v₁ 2 (volume.restrict (truncatedWindow x m (n - 2))) := by
    have haff : MemLp (affineLift x cl Al) 2
        (volume.restrict (truncatedWindow x m (n - 2))) := by
      rw [affineLift_eq_affineEval]
      exact memLp_affineEval_truncatedWindow x _ _
    have h := (hv2.sub haff).sub hVU
    refine h.ae_eq ?_
    filter_upwards [hVae] with y hy
    change v y - affineLift x cl Al y - V y = v₁ y
    rw [hy]
    ring
  have hRnn : (0 : ℝ) ≤ datumResidualBound d n Kh := datumResidualBound_nonneg d n hKh
  have hcorrL2 : normalizedL2On (truncatedWindow x m (n - 2)) v₁
      ≤ datumResidualBound d n Kh :=
    normalizedL2On_le_of_ae_abs_le (volume_truncatedWindow_pos (n - 2) hx)
      (ne_of_lt (volume_truncatedWindow_lt_top x m (n - 2))) hRnn hcorr hv₁
  have hL2ae : (fun y => (u y - affineLift x cl Al y)
        - Set.indicator (truncatedWindow x m (n - 2)) V y)
      =ᵐ[volume.restrict (truncatedWindow x m (n - 2))]
        (fun y => (u y - v y) + v₁ y) := by
    filter_upwards [ae_eq_restrict_of_eqOn hmeas2 hWeq, hVae] with y h1 h2
    show (u y - affineLift x cl Al y)
      - Set.indicator (truncatedWindow x m (n - 2)) V y = (u y - v y) + v₁ y
    rw [h1, h2]
    ring
  have hL2 : normalizedL2On (truncatedWindow x m (n - 2))
      (fun y => (u y - affineLift x cl Al y)
        - Set.indicator (truncatedWindow x m (n - 2)) V y)
      ≤ D + datumResidualBound d n Kh := by
    rw [normalizedL2On_congr_ae hL2ae]
    exact (normalizedL2On_add_le (hu2.sub hv2) hcorr).trans (add_le_add hD hcorrL2)
  -- the extra leg proves in the printed `K_h` slot
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hstep : triangleRemainderConst d Csch k
        * ((3 : ℝ) ^ (-n)
          * normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => (u y - affineLift x cl Al y)
                - Set.indicator (truncatedWindow x m (n - 2)) V y))
      ≤ triangleRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
            * (boundaryDatumLegConst d Csch k * Kh) := by
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hL2 h3npos.le)
      (triangleRemainderConst_nonneg d hCsch k)
    have h2 : triangleRemainderConst d Csch k
          * ((3 : ℝ) ^ (-n) * (D + datumResidualBound d n Kh))
        = triangleRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
          + triangleRemainderConst d Csch k
              * ((3 : ℝ) ^ (-n) * datumResidualBound d n Kh) := by ring
    rw [h2, triangleRemainder_mul_datumResidual] at h1
    exact h1
  linarith only [htri, hstep]

/-! ## 5. The re-cut boundary one-step -/

/-- **The re-cut boundary one-step contraction at the manuscript
competitor `V_odd = v − ℓ_h − v₁`, with the printed `K_h` leg.**

The sibling of the proved boundary endpoint at the met set
in which the odd-class binders `_hupv`/`_hlowv`/`_hharmclass` are asked of the
**shifted** competitor — the object the chain's zero-trace supplier actually
produces — while `_hharm` stays on `u − v`.  The conclusion is
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox`'s display at
`K_h := boundaryDatumLegConst d C k * K_h`, where `K_h` is the corrector's own
`L^∞` scale, i.e. the printed `[∇h]_{C^{0,1/2}(U_2)}`. -/
theorem excessDecay_oneStep_boundary_metSet_datumSplit (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n : ℤ} {k : ℕ} (_hk : 3 ≤ k) {M : ABKModel d} {s : ℝ}
      (hs : 0 < s) (_hs1 : s ≤ 1) {delta : ℝ} (_hdelta1 : delta ≤ 1) {x z : Vec d}
      {i : Fin d} (_hx : x ∈ openCubeSet (originCube d m)) (_hnm : n - 1 ≤ m)
      (_hmn : n - 2 < m)
      (_hmet : MeetsUpperFace x m (n - 2) i ∨ MeetsLowerFace x m (n - 2) i)
      {u v v₁ V : Vec d → ℝ} {cl : ℝ} {Al : Vec d} {Kh : ℝ} (_hKh : 0 ≤ Kh)
      (_hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
      (_hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
      (_hvR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))))
      (_huv : MemLp (fun y => u y - v y) 2
        (volume.restrict (movedReplacementCube x m n)))
      (_hVae : V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))]
        (fun y => v y - affineLift x cl Al y - v₁ y))
      (_hv₁ : ∀ᵐ y ∂(volume.restrict (truncatedWindow x m (n - 2))),
        |v₁ y| ≤ datumResidualBound d n Kh)
      (_hupv : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
      (_hlowv : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
      (_hharmclass : HarmonicOnNhd
        (V ∘ (Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          reflectedWindow x m (n - 2)))
      {omega : Cutoff.CutoffSample d}
      (_hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta))
      {B : ℝ≥0∞} (_hB : B ≠ ⊤)
      (_hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B),
      affineExcess (truncatedWindow x m (n - (k : ℤ))) u
        ≤ taylorContractionConst d * C * windowRatioConst d 2
              * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m n) u
          + triangleRemainderConst d C k
              * ((3 : ℝ) ^ (-n)
                * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
          + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
              * (boundaryDatumLegConst d C k * Kh) := by
  obtain ⟨C, hC0, hC⟩ := Schauder.exists_gradientHolder_boundary_metSet d hd
  refine ⟨C, hC0, ?_⟩
  intro m n k hk M s hs hs1 delta hdelta1 x z i hx hnm hmn hmet u v v₁ V cl Al Kh hKh hu
    hv hvR huv hVae hv₁ hupv hlowv hharmclass omega hmem B hB hharm
  have hVU : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hvR.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m (n - 2)) le_rfl)
  obtain ⟨c, A, hmin⟩ :=
    Schauder.exists_isAffineMinimizer_shifted_truncatedWindow hx (by omega) hVU
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    hC m n x i V c A hx hmn hmet hupv hlowv hharmclass hvR hmin
  -- the anchor's `L²` comparison, transferred to `U_2`
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta := by positivity
  have heple : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have hnorm := le_of_indicator_goodEventAt_le hep0 heple hmem hharm
  have hDmoved : normalizedL2On (movedReplacementCube x m n) (fun y => u y - v y)
      ≤ B.toReal :=
    normalizedL2On_le_toReal_of_eLpNorm_le (volume_movedReplacementCube_pos x m n)
      (volume_movedReplacementCube_ne_top x m n) huv hB hnorm
  have hD : normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y)
      ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal :=
    (normalizedL2On_truncatedWindow_le_movedReplacementCube hx (by omega) huv).trans
      (mul_le_mul_of_nonneg_left hDmoved (Real.sqrt_nonneg _))
  exact excessDecay_oneStep_boundary_datumSplit_core hd hk hx hnm hKh hC0 hu hv hVU hVae
    hv₁ hK hint hgrad hhol hschauder hD

end

end Algsuperdiff.Section4.Provider.ExcessDecay
