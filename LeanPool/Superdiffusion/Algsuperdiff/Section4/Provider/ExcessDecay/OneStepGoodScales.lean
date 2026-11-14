/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.GoodEventCaps

/-!
# OneStepGoodScales

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The good-event cap and the transport of the harmonic-approximation conclusion

Two more ingredients of `l.excess.decay.good.scales`, both proved outright:

* **the good-event cap**: `ae_errorRepresentative_le_goodEventDeltaSlot` is the
  printed `𝓔_{s/8,∞,2}(z+□_j; a_L − (κ_L−κ_j)_{z+□_j}, σ_j) · 1_𝒢 ≤ C s
  δ^{1/2}` at the smallness parameter `ε = (s/8) δ^{1/2}`, obtained from the
  proved generic-`ε` annular cap.  **This is the leg that produces the
  `s^{-1/2}δ^{1/2}` summand of the printed contraction factor.**
* the **carrier transport** of the harmonic-approximation anchor's left-hand
  side: the anchor bounds `‖u−v‖` in `ℝ≥0∞` on the *full moved cube*
  `y + □_{n-2}`, while the triangle assembly reads `‖u−v‖_{L²(U_2)}` in `ℝ`.
  `normalizedL2On_truncatedWindow_le_movedReplacementCube` and
  `normalizedL2On_le_toReal_of_eLpNorm_le` do the two halves, and
  `le_of_indicator_goodEventAt_le` removes the indicator after the
  `ε`-monotonicity of the good event.

## The `ε`-monotonicity bridge

The harmonic lemma carries the indicator at one `ε` slot while the excess-decay
display carries it at `ε = (s/8)δ^{1/2}`, and the source never states the
inclusion between the two events.  It is proved here
(`GoodEvents.goodEventAt_mono_ep`: the event *grows* with `ε`), and
`le_of_indicator_goodEventAt_le` is its consumption: a bound valid on the
*larger* event `𝒢(·; s/8, 1/2)` is valid pathwise on the *smaller* event
`𝒢(·; s/8, (s/8)δ^{1/2})`, which is the event the cap is available on.  The
side condition `(s/8)δ^{1/2} ≤ 1/2` is discharged from `s ≤ 1`, `δ ≤ 1`.

## Two deviations from the printed statement, both inherited

1. **The `s`-range.**  The printed lemma assumes `s ∈ [8γ, 1/2]`.  The cap here
   assumes `s ∈ [64γ, 1]` — the range at which the proved annular cap's slot
   `s/8` lies in its own `[8γ, 1/4]`.  The printed range *fails* on `[8γ, 64γ)`
   (`s/8 ≥ 8γ` is false there); the floor `64γ` is what replaces it, and it is
   also the floor the frozen harmonic anchor carries.
2. **The `γ`-smallness hypothesis.**  `p.mathcalE.annular.decomp` additionally
   requires `γ|log γ|² ≤ (s/8)^{3/2} c⋆² ε`, which
   `l.excess.decay.good.scales` does not list among its hypotheses.  It is
   carried here as an explicit hypothesis at the instance `ε =
   (s/8)δ^{1/2}`; note it is *stronger* than the `ε = 1/2` instance the
   harmonic anchor carries, by the factor `(s/4)δ^{1/2}`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The moved replacement cube -/

/-- The harmonic replacement's domain at the development's window choice: the full
cube `y + □_{n-2}` with `y = wellPlacedCentre x m (n-2)` (see
`OneStepWindows.image_add_wellPlacedCentre_subset_windowChoice`). -/
def movedReplacementCube (x : Vec d) (m n : ℤ) : Set (Vec d) :=
  (fun y => wellPlacedCentre x m (n - 2) + y) '' openCubeSet (originCube d (n - 2))

theorem volume_toReal_movedReplacementCube (x : Vec d) (m n : ℤ) :
    (volume (movedReplacementCube x m n)).toReal = ((3 : ℝ) ^ (n - 2)) ^ d := by
  rw [movedReplacementCube, volume_image_add, volume_toReal_openCubeSet_originCube]

theorem volume_movedReplacementCube_ne_top (x : Vec d) (m n : ℤ) :
    volume (movedReplacementCube x m n) ≠ ⊤ := by
  rw [movedReplacementCube, volume_image_add]
  exact volume_openCubeSet_originCube_ne_top d (n - 2)

theorem volume_movedReplacementCube_pos (x : Vec d) (m n : ℤ) :
    0 < volume (movedReplacementCube x m n) := by
  refine pos_iff_ne_zero.mpr ?_
  intro hzero
  have hreal := volume_toReal_movedReplacementCube x m n
  rw [hzero, ENNReal.toReal_zero] at hreal
  have hpos : (0 : ℝ) < ((3 : ℝ) ^ (n - 2)) ^ d := by positivity
  linarith only [hpos, hreal]

/-- **The window transfer.**  The anchor's `L²` norm lives on the full moved
cube; the assembly reads it on `U_2 = (x+□_{n-2}) ∩ □_m ⊆ y+□_{n-2}`.  The cost
is the volume ratio `3^{2d}` (the truncated window's own aspect ratio). -/
theorem normalizedL2On_truncatedWindow_le_movedReplacementCube {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 2 ≤ m) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (movedReplacementCube x m n))) :
    normalizedL2On (truncatedWindow x m (n - 2)) f
      ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d)
        * normalizedL2On (movedReplacementCube x m n) f := by
  have hkm : n - 2 - 1 ≤ m := by omega
  have hsub : truncatedWindow x m (n - 2) ⊆ movedReplacementCube x m n :=
    truncatedWindow_subset_image_add_windowChoice x hnm
  have hW : 0 < (volume (movedReplacementCube x m n)).toReal := by
    rw [volume_toReal_movedReplacementCube]
    positivity
  have hW' : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx hkm
  have hint : IntegrableOn (fun p => f p ^ 2) (movedReplacementCube x m n) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  refine (normalizedL2On_le_of_subset hsub hW hW' hint).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (normalizedL2On_nonneg _ _)
  refine Real.sqrt_le_sqrt ?_
  have hlo : ((3 : ℝ) ^ (n - 2 - 2)) ^ d ≤ (volume (truncatedWindow x m (n - 2))).toReal :=
    (volume_toReal_truncatedWindow_bounds x hx hkm).1
  have hlopos : (0 : ℝ) < ((3 : ℝ) ^ (n - 2 - 2)) ^ d := by positivity
  have hquot : ((3 : ℝ) ^ (n - 2)) ^ d / ((3 : ℝ) ^ (n - 2 - 2)) ^ d = ((3 : ℝ) ^ (2 : ℤ)) ^ d := by
    rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0),
      show n - 2 - (n - 2 - 2) = (2 : ℤ) by ring]
  rw [volume_toReal_movedReplacementCube, ← hquot, div_le_div_iff₀ hW' hlopos]
  exact mul_le_mul_of_nonneg_left hlo (by positivity)

/-! ## 2. The `ℝ≥0∞ → ℝ` bridge -/

/-- The anchor's left-hand side is an `eLpNorm` against the normalized volume
measure; `normalizedL2On` is its `toReal`. -/
theorem normalizedL2On_le_toReal_of_eLpNorm_le {W : Set (Vec d)} (hW0 : 0 < volume W)
    (hWtop : volume W ≠ ⊤) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict W))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (h : eLpNorm f 2 (Support.normalizedVolumeMeasureOn W) ≤ B) :
    normalizedL2On W f ≤ B.toReal := by
  rw [normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn hW0 hWtop hf]
  exact ENNReal.toReal_mono hB h

/-! ## 3. The `ε`-monotonicity bridge -/

/-- **Removing the anchor's indicator on the smaller event.**

The good event grows with `ε`, so a bound stated with the indicator of
`𝒢(j,z; t, 1/2)` holds pathwise at every `ω` of `𝒢(j,z; t, ε)` for `ε ≤ 1/2` ---
in particular at `ε = (s/8)δ^{1/2}`, the slot the excess-decay display and the
good-event cap are written at. -/
theorem le_of_indicator_goodEventAt_le {M : ABKModel d} {Ccg : ℝ} {j : ℤ} {z : Vec d}
    {t : {t : ℝ // 0 < t}} {ep : ℝ} (hep0 : 0 ≤ ep) (heple : ep ≤ 1 / 2)
    {F : Cutoff.CutoffSample d → ℝ≥0∞} {B : ℝ≥0∞} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg j z t ep)
    (h : Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg j z t (1 / 2)) F omega
      ≤ B) :
    F omega ≤ B := by
  have hsub := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M Ccg j z t
    hep0 heple
  rwa [Set.indicator_of_mem (hsub hmem)] at h

/-! ## 4. The good-event cap at the `δ^{1/2}`-graded slot -/

/-- **The good-event cap.**

```text
  𝓔_{s/8,∞,2}(z+□_j; a_L − (κ_L−κ_j)_{z+□_j}, σ_j) · 1_{𝒢(j,z; s/8, (s/8)δ^{1/2})}
      ≤ C s δ^{1/2} .
```

Exactly the printed `C s δ^{1/2}` (the proved cap gives `C·ε` at `ε =
(s/8)δ^{1/2}`, and `C(s/8)δ^{1/2} ≤ C s δ^{1/2}`).  See deviations 1--2 of the
module docstring for the two inherited hypotheses. -/
theorem ae_errorRepresentative_le_goodEventDeltaSlot (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ s : ℝ, s ∈ Set.Icc (64 * M.gamma) 1 → ∀ hs : 0 < s,
          ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) 1 →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  (s / 8 * Real.sqrt delta) →
              ∀ (j : ℤ) (z : Vec d),
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                      (Support.cgEllipLowerConstant d) j z ⟨s / 8, by linarith only [hs]⟩
                      (s / 8 * Real.sqrt delta) →
                    ∀ L : ℤ, j ≤ L →
                      Support.fluxCorrectedErrorRepresentative M L j
                          ⟨s / 8, by linarith only [hs]⟩
                          (Cutoff.translateCutoffSample z omega) ≤ C * s * Real.sqrt delta := by
  obtain ⟨C, hC0, hC⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  refine ⟨C, hC0, ?_⟩
  intro M hreg s hsrange hs delta hdelta hsmall j z
  have hsqrtpos : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta.1
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta.2
  have hep : s / 8 * Real.sqrt delta ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) := by
    refine ⟨by positivity, ?_⟩
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hsrange.2]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtpos.le (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have hslot : ((⟨s / 8, by linarith only [hs]⟩ : {t : ℝ // 0 < t}) : ℝ)
      ∈ Set.Icc (8 * M.gamma) (1 / 4 : ℝ) := annularSlot_mem_Icc M.gamma s hsrange
  have hmain := hC M hreg ⟨s / 8, by linarith only [hs]⟩ hslot
    (s / 8 * Real.sqrt delta) hep hsmall j z
  filter_upwards [hmain] with omega homega
  intro hmem L hL
  refine (homega hmem L hL).trans ?_
  have h8 : s / 8 ≤ s := by linarith only [hs]
  calc C * (s / 8 * Real.sqrt delta) = C * (s / 8) * Real.sqrt delta := by ring
    _ ≤ C * s * Real.sqrt delta :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hC0.le) hsqrtpos.le

/-! ## 5. The assembly, fed by an `L²` bound on the moved cube -/

/-- **The triangle assembly composed with the harmonic-approximation transport.**

The `‖u-v‖` leg of `excessDecay_oneStep_triangle_of_schauder` is fed by any bound
`D` on the anchor's own object --- the normalized `L²` norm of `u - v` on the
full moved cube `y+□_{n-2}` --- paying only the transfer constant
`√((3^2)^d) = 3^d`. -/
theorem excessDecay_oneStep_of_movedCubeBound (hd : d ≠ 0) {m n : ℤ} {k : ℕ}
    (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (huv : MemLp (fun y => u y - v y) 2 (volume.restrict (movedReplacementCube x m n)))
    {Gv : Vec d → Vec d} {K Kh Csch D : ℝ} (hK : 0 ≤ K) (hCsch : 0 ≤ Csch)
    (hint : ∀ i, IntegrableOn (fun p => Gv p i) (truncatedWindow x m (n - 3)) volume)
    (hgrad : HasGradientOn (truncatedWindow x m (n - 3)) v Gv)
    (hhol : HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K Gv)
    (hschauder : K ≤ Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * affineExcess (truncatedWindow x m (n - 2)) v + Kh)
    (hD : normalizedL2On (movedReplacementCube x m n) (fun y => u y - v y) ≤ D) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * Csch * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d Csch k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * D))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
  have hmain := excessDecay_oneStep_triangle_of_schauder hd hk hx hnm hu hv hK hCsch hint
    hgrad hhol hschauder
  refine hmain.trans ?_
  have htrans : normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y)
      ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * D := by
    refine (normalizedL2On_truncatedWindow_le_movedReplacementCube hx (by omega) huv).trans ?_
    exact mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg _)
  have hstep : triangleRemainderConst d Csch k
        * ((3 : ℝ) ^ (-n)
          * normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y))
      ≤ triangleRemainderConst d Csch k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * D)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left htrans (zpow_pos (by norm_num) (-n)).le)
      (triangleRemainderConst_nonneg d hCsch k)
  exact add_le_add (add_le_add le_rfl hstep) le_rfl

end

end Algsuperdiff.Section4.Provider.ExcessDecay
