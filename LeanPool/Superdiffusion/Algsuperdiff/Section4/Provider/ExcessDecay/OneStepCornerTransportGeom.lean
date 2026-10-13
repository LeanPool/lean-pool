/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow

/-!
# OneStepCornerTransportGeom

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Coordinate-negation transport of the §4.3 boundary-window geometry

The domain cube `□_m` is origin-symmetric, so the involution

```text
  σ := σ_i := coordFaceReflection (0 : ℝ) i
```

which negates the `i`-th coordinate and fixes every other one, maps `□_m` onto
itself.  Consequently it carries the truncated window `(x + □_k) ∩ □_m` onto
`(σ x + □_k) ∩ □_m` — equivalently, the window centred at `σ x` is the
`σ`-preimage of the window centred at `x` — and it exchanges the upper and the
lower `i`-face of `∂□_m` while fixing the met/unmet status of every other face.

This is exactly what lets the proved **upper-face-only** odd-class apparatus of
`OddReflectionWindow` be read at every met configuration: a lower `i`-face
configuration at `x` is an upper `i`-face configuration at `σ x`, and the two
window geometries are related by the single change of variables `σ`.

Concretely the module transports, one by one, every piece of the
`OddReflectionWindow` geometry across `σ`:

```text
  MeetsUpperFace (σ x) m k i ↔ MeetsLowerFace x m k i      (faces swap at `i`)
  MeetsUpperFace (σ x) m k l ↔ MeetsUpperFace x m k l      (l ≠ i: unchanged)
  windowLo   (σ x) m k i = -windowHi   x m k i
  windowHi   (σ x) m k i = -windowLo   x m k i
  reflectedLo (σ x) m k i = -reflectedHi x m k i
  reflectedHi (σ x) m k i = -reflectedLo x m k i
  truncatedWindow  (σ x) m k = σ ⁻¹' truncatedWindow  x m k
  reflectedWindow  (σ x) m k = σ ⁻¹' reflectedWindow  x m k
```

Since `σ` is an involution (`coordFaceReflection_involutive`) the preimage form
is also the image form; the preimage form is the one the change-of-variables
consumers want.

## References

* ABK26, `l.excess.decay.good.scales`; the odd-reflection step replaced.
* CoarseGraining
  `Homogenization.Sobolev.Foundations.CubeReflection.Reflections`
  (`coordFaceReflection`, `coordFaceReflection_involutive`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport (Vec openCubeSet originCube coordFaceReflection)

noncomputable section

variable {d : ℕ}

/-! ## 1. The coordinate-negation involution -/

private theorem coordFaceReflection_zero_self_apply (i : Fin d) (y : Vec d) :
    coordFaceReflection (0 : ℝ) i y i = -(y i) := by
  rw [HCPolySupport.coordFaceReflection_apply_self]
  ring

private theorem coordFaceReflection_zero_apply_ne {i l : Fin d} (hli : l ≠ i)
    (y : Vec d) : coordFaceReflection (0 : ℝ) i y l = y l :=
  HCPolySupport.coordFaceReflection_apply_ne (0 : ℝ) i l y hli

/-- The domain cube `□_m` is origin-symmetric, hence `σ_i`-invariant. -/
theorem mem_openCubeSet_coordFaceReflection_zero_iff {m : ℤ} (i : Fin d)
    (y : Vec d) :
    coordFaceReflection (0 : ℝ) i y ∈ openCubeSet (originCube d m)
      ↔ y ∈ openCubeSet (originCube d m) := by
  simp only [HCPolySupport.mem_openCubeSet_originCube_iff]
  constructor
  · intro h l
    have hl := h l
    by_cases hli : l = i
    · rw [hli] at hl ⊢
      rw [coordFaceReflection_zero_self_apply] at hl
      exact ⟨by linarith only [hl.2], by linarith only [hl.1]⟩
    · rwa [coordFaceReflection_zero_apply_ne hli] at hl
  · intro h l
    have hl := h l
    by_cases hli : l = i
    · rw [hli] at hl ⊢
      rw [coordFaceReflection_zero_self_apply]
      exact ⟨by linarith only [hl.2], by linarith only [hl.1]⟩
    · rwa [coordFaceReflection_zero_apply_ne hli]

/-! ## 2. The met faces: the `i`-faces swap, the others are fixed -/

/-- Negating the `i`-th coordinate turns the lower `i`-face into the upper
one. -/
theorem meetsUpperFace_coordFaceReflection_zero_self {x : Vec d} {m k : ℤ}
    (i : Fin d) :
    MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m k i
      ↔ MeetsLowerFace x m k i := by
  unfold MeetsUpperFace MeetsLowerFace
  rw [coordFaceReflection_zero_self_apply]
  constructor <;> intro h <;> linarith only [h]

/-- Negating the `i`-th coordinate turns the upper `i`-face into the lower
one. -/
theorem meetsLowerFace_coordFaceReflection_zero_self {x : Vec d} {m k : ℤ}
    (i : Fin d) :
    MeetsLowerFace (coordFaceReflection (0 : ℝ) i x) m k i
      ↔ MeetsUpperFace x m k i := by
  unfold MeetsUpperFace MeetsLowerFace
  rw [coordFaceReflection_zero_self_apply]
  constructor <;> intro h <;> linarith only [h]

theorem meetsUpperFace_coordFaceReflection_zero_ne {x : Vec d} {m k : ℤ}
    {i l : Fin d} (hli : l ≠ i) :
    MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m k l
      ↔ MeetsUpperFace x m k l := by
  unfold MeetsUpperFace
  rw [coordFaceReflection_zero_apply_ne hli]

theorem meetsLowerFace_coordFaceReflection_zero_ne {x : Vec d} {m k : ℤ}
    {i l : Fin d} (hli : l ≠ i) :
    MeetsLowerFace (coordFaceReflection (0 : ℝ) i x) m k l
      ↔ MeetsLowerFace x m k l := by
  unfold MeetsLowerFace
  rw [coordFaceReflection_zero_apply_ne hli]

/-! ## 3. The window endpoints -/

theorem windowLo_coordFaceReflection_zero_self (x : Vec d) (m k : ℤ)
    (i : Fin d) :
    windowLo (coordFaceReflection (0 : ℝ) i x) m k i = -windowHi x m k i := by
  by_cases h : MeetsLowerFace (coordFaceReflection (0 : ℝ) i x) m k i
  · have hup : MeetsUpperFace x m k i :=
      (meetsLowerFace_coordFaceReflection_zero_self i).mp h
    rw [windowLo_of_meetsLowerFace h, windowHi_of_meetsUpperFace hup]
    ring
  · have hup : ¬ MeetsUpperFace x m k i := fun hc =>
      h ((meetsLowerFace_coordFaceReflection_zero_self i).mpr hc)
    rw [windowLo_of_not_meetsLowerFace h, windowHi_of_not_meetsUpperFace hup,
      coordFaceReflection_zero_self_apply]
    ring

theorem windowHi_coordFaceReflection_zero_self (x : Vec d) (m k : ℤ)
    (i : Fin d) :
    windowHi (coordFaceReflection (0 : ℝ) i x) m k i = -windowLo x m k i := by
  by_cases h : MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m k i
  · have hlo : MeetsLowerFace x m k i :=
      (meetsUpperFace_coordFaceReflection_zero_self i).mp h
    rw [windowHi_of_meetsUpperFace h, windowLo_of_meetsLowerFace hlo]
    ring
  · have hlo : ¬ MeetsLowerFace x m k i := fun hc =>
      h ((meetsUpperFace_coordFaceReflection_zero_self i).mpr hc)
    rw [windowHi_of_not_meetsUpperFace h, windowLo_of_not_meetsLowerFace hlo,
      coordFaceReflection_zero_self_apply]
    ring

theorem windowLo_coordFaceReflection_zero_ne {x : Vec d} {m k : ℤ}
    {i l : Fin d} (hli : l ≠ i) :
    windowLo (coordFaceReflection (0 : ℝ) i x) m k l = windowLo x m k l := by
  unfold windowLo
  rw [coordFaceReflection_zero_apply_ne hli]

theorem windowHi_coordFaceReflection_zero_ne {x : Vec d} {m k : ℤ}
    {i l : Fin d} (hli : l ≠ i) :
    windowHi (coordFaceReflection (0 : ℝ) i x) m k l = windowHi x m k l := by
  unfold windowHi
  rw [coordFaceReflection_zero_apply_ne hli]

/-! ## 4. The reflected-window endpoints -/

theorem reflectedLo_coordFaceReflection_zero_self (x : Vec d) (m k : ℤ)
    (i : Fin d) :
    reflectedLo (coordFaceReflection (0 : ℝ) i x) m k i =
      -reflectedHi x m k i := by
  by_cases h : MeetsLowerFace (coordFaceReflection (0 : ℝ) i x) m k i
  · have hup : MeetsUpperFace x m k i :=
      (meetsLowerFace_coordFaceReflection_zero_self i).mp h
    rw [reflectedLo_of_meetsLowerFace h, reflectedHi_of_meetsUpperFace hup,
      windowHi_coordFaceReflection_zero_self]
    ring
  · have hup : ¬ MeetsUpperFace x m k i := fun hc =>
      h ((meetsLowerFace_coordFaceReflection_zero_self i).mpr hc)
    rw [reflectedLo_of_not_meetsLowerFace h,
      reflectedHi_of_not_meetsUpperFace hup,
      windowLo_coordFaceReflection_zero_self]

theorem reflectedHi_coordFaceReflection_zero_self (x : Vec d) (m k : ℤ)
    (i : Fin d) :
    reflectedHi (coordFaceReflection (0 : ℝ) i x) m k i =
      -reflectedLo x m k i := by
  by_cases h : MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m k i
  · have hlo : MeetsLowerFace x m k i :=
      (meetsUpperFace_coordFaceReflection_zero_self i).mp h
    rw [reflectedHi_of_meetsUpperFace h, reflectedLo_of_meetsLowerFace hlo,
      windowLo_coordFaceReflection_zero_self]
    ring
  · have hlo : ¬ MeetsLowerFace x m k i := fun hc =>
      h ((meetsUpperFace_coordFaceReflection_zero_self i).mpr hc)
    rw [reflectedHi_of_not_meetsUpperFace h,
      reflectedLo_of_not_meetsLowerFace hlo,
      windowHi_coordFaceReflection_zero_self]

theorem reflectedLo_coordFaceReflection_zero_ne {x : Vec d} {m k : ℤ}
    {i l : Fin d} (hli : l ≠ i) :
    reflectedLo (coordFaceReflection (0 : ℝ) i x) m k l =
      reflectedLo x m k l := by
  by_cases h : MeetsLowerFace (coordFaceReflection (0 : ℝ) i x) m k l
  · have hlo : MeetsLowerFace x m k l :=
      (meetsLowerFace_coordFaceReflection_zero_ne hli).mp h
    rw [reflectedLo_of_meetsLowerFace h, reflectedLo_of_meetsLowerFace hlo,
      windowHi_coordFaceReflection_zero_ne hli]
  · have hlo : ¬ MeetsLowerFace x m k l := fun hc =>
      h ((meetsLowerFace_coordFaceReflection_zero_ne hli).mpr hc)
    rw [reflectedLo_of_not_meetsLowerFace h,
      reflectedLo_of_not_meetsLowerFace hlo,
      windowLo_coordFaceReflection_zero_ne hli]

theorem reflectedHi_coordFaceReflection_zero_ne {x : Vec d} {m k : ℤ}
    {i l : Fin d} (hli : l ≠ i) :
    reflectedHi (coordFaceReflection (0 : ℝ) i x) m k l =
      reflectedHi x m k l := by
  by_cases h : MeetsUpperFace (coordFaceReflection (0 : ℝ) i x) m k l
  · have hup : MeetsUpperFace x m k l :=
      (meetsUpperFace_coordFaceReflection_zero_ne hli).mp h
    rw [reflectedHi_of_meetsUpperFace h, reflectedHi_of_meetsUpperFace hup,
      windowLo_coordFaceReflection_zero_ne hli]
  · have hup : ¬ MeetsUpperFace x m k l := fun hc =>
      h ((meetsUpperFace_coordFaceReflection_zero_ne hli).mpr hc)
    rw [reflectedHi_of_not_meetsUpperFace h,
      reflectedHi_of_not_meetsUpperFace hup,
      windowHi_coordFaceReflection_zero_ne hli]

/-! ## 5. The two window identities -/

/-- The generic transport of a coordinate box under the coordinate negation
`σ_i`: negating the `i`-th edge and fixing all the others turns the box into
the `σ_i`-preimage of the untransported one. -/
private theorem coordBox_coordFaceReflection_zero (lo hi lo' hi' : Fin d → ℝ)
    (i : Fin d) (hlo : lo i = -hi' i) (hhi : hi i = -lo' i)
    (hlo' : ∀ l, l ≠ i → lo l = lo' l) (hhi' : ∀ l, l ≠ i → hi l = hi' l) :
    coordBox lo hi = coordFaceReflection (0 : ℝ) i ⁻¹' coordBox lo' hi' := by
  ext y
  simp only [Set.mem_preimage, mem_coordBox_iff]
  constructor
  · intro h l
    have hl := h l
    by_cases hli : l = i
    · rw [hli] at hl ⊢
      rw [hlo, hhi] at hl
      rw [coordFaceReflection_zero_self_apply]
      exact ⟨by linarith only [hl.2], by linarith only [hl.1]⟩
    · rw [hlo' l hli, hhi' l hli] at hl
      rwa [coordFaceReflection_zero_apply_ne hli]
  · intro h l
    have hl := h l
    by_cases hli : l = i
    · rw [hli] at hl ⊢
      rw [coordFaceReflection_zero_self_apply] at hl
      rw [hlo, hhi]
      exact ⟨by linarith only [hl.2], by linarith only [hl.1]⟩
    · rw [coordFaceReflection_zero_apply_ne hli] at hl
      rwa [hlo' l hli, hhi' l hli]

/-- **The truncated window transports.**  The window centred at `σ_i x` is the
`σ_i`-preimage of the window centred at `x`; equivalently (as `σ_i` is an
involution) its `σ_i`-image. -/
theorem truncatedWindow_coordFaceReflection_zero (x : Vec d) (m k : ℤ)
    (i : Fin d) :
    truncatedWindow (coordFaceReflection (0 : ℝ) i x) m k
      = coordFaceReflection (0 : ℝ) i ⁻¹' truncatedWindow x m k := by
  simp only [truncatedWindow_eq_coordBox]
  exact coordBox_coordFaceReflection_zero _ _ _ _ i
    (windowLo_coordFaceReflection_zero_self x m k i)
    (windowHi_coordFaceReflection_zero_self x m k i)
    (fun _ hl => windowLo_coordFaceReflection_zero_ne hl)
    (fun _ hl => windowHi_coordFaceReflection_zero_ne hl)

/-- **The partially reflected window transports.**  This is the statement that
lets the upper-face-only odd-class apparatus be read at a lower-face
configuration, by the change of variables `σ_i`. -/
theorem reflectedWindow_coordFaceReflection_zero (x : Vec d) (m k : ℤ)
    (i : Fin d) :
    reflectedWindow (coordFaceReflection (0 : ℝ) i x) m k
      = coordFaceReflection (0 : ℝ) i ⁻¹' reflectedWindow x m k := by
  unfold reflectedWindow
  exact coordBox_coordFaceReflection_zero _ _ _ _ i
    (reflectedLo_coordFaceReflection_zero_self x m k i)
    (reflectedHi_coordFaceReflection_zero_self x m k i)
    (fun _ hl => reflectedLo_coordFaceReflection_zero_ne hl)
    (fun _ hl => reflectedHi_coordFaceReflection_zero_ne hl)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
