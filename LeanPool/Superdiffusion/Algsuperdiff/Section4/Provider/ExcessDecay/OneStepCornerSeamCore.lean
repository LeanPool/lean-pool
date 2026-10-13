/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerProducer

/-!
# OneStepCornerSeamCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The a.e. seam of the boundary branch: a globally met-face-odd representative

The odd-class apparatus of the boundary branch (`OneStepEvenBoundFinal`'s `(★)`
and `OneStepOddClassCornerFinal`'s `(★★)`) consumes the **global pointwise**
oddness binders

```text
  ∀ z : Vec d,  V (r_l z) = − V z          (r_l the reflection in a met face)
```

while the competitor the chain actually produces is a Weyl representative `V`,
which is only *almost everywhere* equal to the pointwise-odd `H¹` datum `w`
delivered by the reflection chain
(`OneStepPartialReflection.exists_h1_oddReflection_reflectedWindow`).  This
module closes that seam in two steps.

## Step 1: a.e. oddness becomes pointwise oddness *on the doubled window*

The doubled window `R = reflectedWindow x m k` is open and invariant under
every met-face reflection (`mem_reflectedWindow_coordFaceReflection_iff`), a
Weyl representative is continuous on it (`continuousOn_of_harmonicOnNhd`), and
the reflection is measure preserving; so `V ∘ r_l` and `−V` are two functions
continuous on the open set `R` which agree a.e. there, hence agree pointwise
there (`MeasureTheory.Measure.eqOn_open_of_ae_eq`).

## Step 2: the piecewise globally odd representative

Pointwise oddness *on `R`* is still not the binder `(★)`/`(★★)` want.  But `R`
is reflection invariant, so the **piecewise** function

```text
  W := fun y => if y ∈ R then V y else O y
```

is odd about every met face *globally*: inside `R` the oddness is Step 1's, and
outside `R` it is the a.e. datum's own pointwise oddness — the two cases never
mix, precisely because `r_l` maps `R` onto `R` and its complement onto its
complement.  And `W = V` on `R`, so every quantity the odd-class apparatus reads
(`normalizedL2On`, `affineDistOn`, `affineExcessRaw`, `oddClassDefect`,
classical harmonicity on `R`, `MemLp` on `R`, the affine-minimizer datum on
`U₂ ⊆ R`) is unchanged.  No symmetrization, no reflection-group average and no
new analytic input is needed.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ## 1. Classical harmonicity is an `EqOn` invariant on an open set -/

/-- **Harmonicity transfers along an equality on an open set.**  Both sides are
germs at each point of the set, and the set is open, so the germs agree. -/
theorem harmonicOnNhd_congr_eqOn {S : Set (Vec d)} (hS : IsOpen S) {V W : Vec d → ℝ}
    (h : Set.EqOn W V S)
    (hV : HarmonicOnNhd (V ∘ (toEuc.symm : 𝔼 → Vec d)) ((toEuc : Vec d → 𝔼) '' S)) :
    HarmonicOnNhd (W ∘ (toEuc.symm : 𝔼 → Vec d)) ((toEuc : Vec d → 𝔼) '' S) := by
  have hopen : IsOpen ((toEuc : Vec d → 𝔼) '' S) :=
    (toEuc : Vec d ≃L[ℝ] 𝔼).toHomeomorph.isOpenMap _ hS
  have hgerm : ∀ e ∈ (toEuc : Vec d → 𝔼) '' S,
      (W ∘ (toEuc.symm : 𝔼 → Vec d)) =ᶠ[nhds e] (V ∘ (toEuc.symm : 𝔼 → Vec d)) := by
    intro e he
    refine Filter.eventually_of_mem (hopen.mem_nhds he) ?_
    rintro w ⟨p, hp, rfl⟩
    change W (toEuc.symm (toEuc p)) = V (toEuc.symm (toEuc p))
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact h hp
  rintro e ⟨y, hy, rfl⟩
  have hmem : (toEuc : Vec d → 𝔼) y ∈ (toEuc : Vec d → 𝔼) '' S := ⟨y, hy, rfl⟩
  have hVe := hV _ hmem
  refine ⟨hVe.1.congr_of_eventuallyEq (hgerm _ hmem), ?_⟩
  have hlap := laplacian_congr_nhds (hgerm _ hmem)
  filter_upwards [hVe.2, hlap] with e he hl
  rw [Pi.zero_apply] at he ⊢
  rw [hl, he]

/-! ## 2. From an almost-everywhere odd datum to oddness on the doubled window -/

/-- **The upper-face seam.**  A function continuous on the doubled window and
almost everywhere equal there to a globally odd datum is *pointwise* odd about
the met upper face at every point of the doubled window. -/
theorem eqOn_faceOdd_upper_of_ae_eq {x : Vec d} {m k : ℤ} (hkm : k < m) {i : Fin d}
    (hup : MeetsUpperFace x m k i) {V O : Vec d → ℝ}
    (hVcont : ContinuousOn V (reflectedWindow x m k))
    (hae : V =ᵐ[volume.restrict (reflectedWindow x m k)] O)
    (hOodd : ∀ z : Vec d,
      O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z) :
    ∀ y ∈ reflectedWindow x m k,
      V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y := by
  have hiff := mem_reflectedWindow_coordFaceReflection_iff hkm hup
  have hpre : coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i ⁻¹'
      reflectedWindow x m k = reflectedWindow x m k := by
    ext y
    exact hiff y
  have hmp : MeasurePreserving (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i)
      (volume.restrict (reflectedWindow x m k))
      (volume.restrict (reflectedWindow x m k)) := by
    have h := (HCPolySupport.measurePreserving_coordFaceReflection (d := d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i).restrict_preimage
      (isOpen_reflectedWindow x m k).measurableSet
    rwa [hpre] at h
  have hae2 : (fun y => V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      =ᵐ[volume.restrict (reflectedWindow x m k)]
      (fun y => O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)) :=
    hae.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
  have hae3 : (fun y => V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      =ᵐ[volume.restrict (reflectedWindow x m k)] (fun y => -V y) := by
    filter_upwards [hae2, hae] with y h2 h3
    rw [h2, hOodd y, h3]
  have hVrcont : ContinuousOn
      (fun y => V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      (reflectedWindow x m k) := by
    refine ContinuousOn.comp hVcont
      (HCPolySupport.contDiff_coordFaceReflection _ i).continuous.continuousOn ?_
    intro y hy
    exact (hiff y).mpr hy
  have heq := Measure.eqOn_open_of_ae_eq hae3 (isOpen_reflectedWindow x m k)
    hVrcont hVcont.neg
  exact fun y hy => heq hy

/-- **The lower-face seam**, the twin of `eqOn_faceOdd_upper_of_ae_eq`. -/
theorem eqOn_faceOdd_lower_of_ae_eq {x : Vec d} {m k : ℤ} (hkm : k < m) {i : Fin d}
    (hlow : MeetsLowerFace x m k i) {V O : Vec d → ℝ}
    (hVcont : ContinuousOn V (reflectedWindow x m k))
    (hae : V =ᵐ[volume.restrict (reflectedWindow x m k)] O)
    (hOodd : ∀ z : Vec d,
      O (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z) :
    ∀ y ∈ reflectedWindow x m k,
      V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y := by
  have hiff := mem_reflectedWindow_coordFaceReflection_iff_lower hkm hlow
  have hpre : coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i ⁻¹'
      reflectedWindow x m k = reflectedWindow x m k := by
    ext y
    exact hiff y
  have hmp : MeasurePreserving (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i)
      (volume.restrict (reflectedWindow x m k))
      (volume.restrict (reflectedWindow x m k)) := by
    have h := (HCPolySupport.measurePreserving_coordFaceReflection (d := d)
      (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i).restrict_preimage
      (isOpen_reflectedWindow x m k).measurableSet
    rwa [hpre] at h
  have hae2 : (fun y => V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      =ᵐ[volume.restrict (reflectedWindow x m k)]
      (fun y => O (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)) :=
    hae.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
  have hae3 : (fun y => V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      =ᵐ[volume.restrict (reflectedWindow x m k)] (fun y => -V y) := by
    filter_upwards [hae2, hae] with y h2 h3
    rw [h2, hOodd y, h3]
  have hVrcont : ContinuousOn
      (fun y => V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      (reflectedWindow x m k) := by
    refine ContinuousOn.comp hVcont
      (HCPolySupport.contDiff_coordFaceReflection _ i).continuous.continuousOn ?_
    intro y hy
    exact (hiff y).mpr hy
  have heq := Measure.eqOn_open_of_ae_eq hae3 (isOpen_reflectedWindow x m k)
    hVrcont hVcont.neg
  exact fun y hy => heq hy

/-! ## 3. The piecewise globally odd representative -/

/-- **The seam, closed.**  From a representative `V` odd about every met face
*at the points of the doubled window* and an a.e. datum `O` odd about every met
face *globally*, the piecewise function `W = V` on the doubled window, `= O` off
it, is odd about every met face globally and agrees with `V` on the doubled
window.

The proof is the reflection invariance of the doubled window: a met-face
reflection maps the window onto itself and its complement onto its complement,
so the two branches of the `if` never mix. -/
theorem exists_faceOdd_forall_eqOn_reflectedWindow {x : Vec d} {m k : ℤ} (hkm : k < m)
    {V O : Vec d → ℝ}
    (hupV : ∀ i : Fin d, MeetsUpperFace x m k i → ∀ y ∈ reflectedWindow x m k,
      V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y)
    (hlowV : ∀ i : Fin d, MeetsLowerFace x m k i → ∀ y ∈ reflectedWindow x m k,
      V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y)
    (hupO : ∀ i : Fin d, MeetsUpperFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z)
    (hlowO : ∀ i : Fin d, MeetsLowerFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z) :
    ∃ W : Vec d → ℝ,
      (∀ i : Fin d, MeetsUpperFace x m k i → ∀ z : Vec d,
        W (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -W z) ∧
      (∀ i : Fin d, MeetsLowerFace x m k i → ∀ z : Vec d,
        W (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -W z) ∧
      Set.EqOn W V (reflectedWindow x m k) := by
  classical
  refine ⟨fun y => if y ∈ reflectedWindow x m k then V y else O y, ?_, ?_, ?_⟩
  · intro i hup z
    dsimp only
    have hiff := mem_reflectedWindow_coordFaceReflection_iff hkm hup z
    by_cases hz : z ∈ reflectedWindow x m k
    · rw [ite_eq_left (hiff.mpr hz), ite_eq_left hz]
      exact hupV i hup z hz
    · rw [ite_eq_right (fun h => hz (hiff.mp h)), ite_eq_right hz]
      exact hupO i hup z
  · intro i hlow z
    dsimp only
    have hiff := mem_reflectedWindow_coordFaceReflection_iff_lower hkm hlow z
    by_cases hz : z ∈ reflectedWindow x m k
    · rw [ite_eq_left (hiff.mpr hz), ite_eq_left hz]
      exact hlowV i hlow z hz
    · rw [ite_eq_right (fun h => hz (hiff.mp h)), ite_eq_right hz]
      exact hlowO i hlow z
  · intro y hy
    change (if y ∈ reflectedWindow x m k then V y else O y) = V y
    rw [ite_eq_left hy]

/-! ## 4. The consumers transported along the `EqOn` -/

/-- `oddClassDefect` only sees the almost-everywhere class of its argument on
the window. -/
theorem oddClassDefect_congr_ae {x : Vec d} {m n : ℤ} {V W : Vec d → ℝ}
    (h : W =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] V) (c : ℝ) (A : Vec d) :
    oddClassDefect x m n W c A = oddClassDefect x m n V c A := by
  rw [oddClassDefect, oddClassDefect, affineDistOn_congr_ae h, affineExcessRaw_congr_ae h]

/-- `IsAffineMinimizer` on the window is an almost-everywhere invariant. -/
theorem isAffineMinimizer_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) (c : ℝ) (A : Vec d) :
    IsAffineMinimizer W f c A ↔ IsAffineMinimizer W g c A := by
  rw [IsAffineMinimizer, IsAffineMinimizer, affineDistOn_congr_ae h,
    affineExcessRaw_congr_ae h]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
