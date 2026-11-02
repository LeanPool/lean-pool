/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitLift

/-!
# OddReflectionMap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The partial odd reflection operator, and the odd affine class

## The fold and its sign

Each met face contributes one coordinate reflection, and by
`not_meetsLowerFace_of_meetsUpperFace` a coordinate meets at most one face, so
the whole group action is realized by a single *coordinatewise fold*

```text
  foldCoord i t = min t (3^m - t)     if the upper i-face is met,
                = max t (-3^m - t)    if the lower i-face is met,
                = t                   otherwise,
```

with the matching odd sign `foldSignCoord i t = ±1` (negative exactly on the
reflected side), and `windowFoldSign y = ∏ᵢ foldSignCoord i (y i)`.

`oddExtend f` is `y ↦ windowFoldSign y · f (windowFold y)`, and `oddExtendGrad G`
carries the extra per-coordinate sign that the chain rule produces.

## The odd affine class `𝕃_odd(V)`

`IsOddAffineData x m k c A` says the affine function `ℓ(y) = c + A·(y-x)`
vanishes on every hyperplane containing a met face — the paper's
`𝕃_odd(V)`.  Two structural facts are proved:

* if the `i`-face is met then `A j = 0` for every `j ≠ i`
  (`slope_eq_zero_of_ne_of_meets`), so at one met face the class is the single
  line `ℝ·(y_i - a_i)`;
* if two *different* coordinates meet a face then `ℓ ≡ 0`
  (`affineLift_eq_zero_of_two_met`) — at an edge or corner of `□_m` the class
  `𝕃_odd(V)` collapses to `{0}`.

`oddExtend_affineLift` is the paper's "if `ℓ ∈ 𝕃_odd(V)`, then `ℓ` is odd under
each of these reflections": the odd extension of such an `ℓ` is `ℓ` itself, so
the extension of `v₀ - ℓ` is the odd extension of `v₀ - ℓ`.

## What is not done here

No `H¹` statement, no weak harmonicity, no measure-theoretic change of
variables.

## References

* CoarseGraining
  `Homogenization.Sobolev.Foundations.CubeDirichletH2.OddReflection` (the
  all-faces construction adapted here) and
  `Homogenization.Sobolev.Foundations.CubeReflection.Reflections`
  (`coordFaceReflection`, the one-face affine map).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. The coordinatewise fold and its sign -/

/-- The fold of one coordinate into the window's side of the met face. -/
def foldCoord (x : Vec d) (m k : ℤ) (i : Fin d) (t : ℝ) : ℝ :=
  if (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ x i + (1 / 2 : ℝ) * (3 : ℝ) ^ k then
    min t ((3 : ℝ) ^ m - t)
  else if x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m then
    max t (-(3 : ℝ) ^ m - t)
  else t

/-- The odd sign attached to one coordinate: `-1` exactly on the reflected
side of a met face. -/
def foldSignCoord (x : Vec d) (m k : ℤ) (i : Fin d) (t : ℝ) : ℝ :=
  if (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ x i + (1 / 2 : ℝ) * (3 : ℝ) ^ k then
    (if (1 / 2 : ℝ) * (3 : ℝ) ^ m < t then -1 else 1)
  else if x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m then
    (if t < -(1 / 2 : ℝ) * (3 : ℝ) ^ m then -1 else 1)
  else 1

theorem foldCoord_of_meetsUpperFace {x : Vec d} {m k : ℤ} {i : Fin d}
    (h : MeetsUpperFace x m k i) (t : ℝ) :
    foldCoord x m k i t = min t ((3 : ℝ) ^ m - t) :=
  ite_eq_left h

theorem foldCoord_of_meetsLowerFace {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : ¬ MeetsUpperFace x m k i) (h : MeetsLowerFace x m k i) (t : ℝ) :
    foldCoord x m k i t = max t (-(3 : ℝ) ^ m - t) := by
  have h1 : ¬ ((1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ x i + (1 / 2 : ℝ) * (3 : ℝ) ^ k) := hup
  have h2 : x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m := h
  rw [foldCoord, ite_eq_right h1, ite_eq_left h2]

theorem foldCoord_of_unmet {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : ¬ MeetsUpperFace x m k i) (hlow : ¬ MeetsLowerFace x m k i) (t : ℝ) :
    foldCoord x m k i t = t := by
  have h1 : ¬ ((1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ x i + (1 / 2 : ℝ) * (3 : ℝ) ^ k) := hup
  have h2 : ¬ (x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m) := hlow
  rw [foldCoord, ite_eq_right h1, ite_eq_right h2]

theorem foldSignCoord_of_meetsUpperFace {x : Vec d} {m k : ℤ} {i : Fin d}
    (h : MeetsUpperFace x m k i) (t : ℝ) :
    foldSignCoord x m k i t =
      (if (1 / 2 : ℝ) * (3 : ℝ) ^ m < t then -1 else 1) :=
  ite_eq_left h

theorem foldSignCoord_of_meetsLowerFace {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : ¬ MeetsUpperFace x m k i) (h : MeetsLowerFace x m k i) (t : ℝ) :
    foldSignCoord x m k i t =
      (if t < -(1 / 2 : ℝ) * (3 : ℝ) ^ m then -1 else 1) := by
  have h1 : ¬ ((1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ x i + (1 / 2 : ℝ) * (3 : ℝ) ^ k) := hup
  have h2 : x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m := h
  rw [foldSignCoord, ite_eq_right h1, ite_eq_left h2]

theorem foldSignCoord_of_unmet {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : ¬ MeetsUpperFace x m k i) (hlow : ¬ MeetsLowerFace x m k i) (t : ℝ) :
    foldSignCoord x m k i t = 1 := by
  have h1 : ¬ ((1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ x i + (1 / 2 : ℝ) * (3 : ℝ) ^ k) := hup
  have h2 : ¬ (x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m) := hlow
  rw [foldSignCoord, ite_eq_right h1, ite_eq_right h2]

/-! ## 2. The fold, the global sign, and the odd extension -/

/-- The coordinatewise fold of `Vec d` onto the window's side of every met
face: the composite of the reflections in the met faces, applied to whichever
of the `2^{#S}` cells the point lies in. -/
def windowFold (x : Vec d) (m k : ℤ) : Vec d → Vec d :=
  fun y i => foldCoord x m k i (y i)

/-- The global odd sign: `(-1)^{#\{i : y \text{ is beyond the met } i\text{-face}\}}`. -/
def windowFoldSign (x : Vec d) (m k : ℤ) (y : Vec d) : ℝ :=
  ∏ i : Fin d, foldSignCoord x m k i (y i)

@[simp] theorem windowFold_apply (x : Vec d) (m k : ℤ) (y : Vec d) (i : Fin d) :
    windowFold x m k y i = foldCoord x m k i (y i) :=
  rfl

theorem abs_foldSignCoord (x : Vec d) (m k : ℤ) (i : Fin d) (t : ℝ) :
    |foldSignCoord x m k i t| = 1 := by
  by_cases hup : MeetsUpperFace x m k i
  · rw [foldSignCoord_of_meetsUpperFace hup]
    split_ifs <;> norm_num
  · by_cases hlow : MeetsLowerFace x m k i
    · rw [foldSignCoord_of_meetsLowerFace hup hlow]
      split_ifs <;> norm_num
    · rw [foldSignCoord_of_unmet hup hlow]
      norm_num

theorem abs_windowFoldSign (x : Vec d) (m k : ℤ) (y : Vec d) :
    |windowFoldSign x m k y| = 1 := by
  rw [windowFoldSign, Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => abs_foldSignCoord x m k i (y i)

/-- **The partial odd reflection of a scalar.** -/
def oddExtend (x : Vec d) (m k : ℤ) (f : Vec d → ℝ) : Vec d → ℝ :=
  fun y => windowFoldSign x m k y * f (windowFold x m k y)

/-- **The partial odd reflection of a gradient field.**  The chain rule for the
coordinate fold contributes the extra per-coordinate sign. -/
def oddExtendGrad (x : Vec d) (m k : ℤ) (G : Vec d → Vec d) : Vec d → Vec d :=
  fun y i =>
    windowFoldSign x m k y * foldSignCoord x m k i (y i) *
      G (windowFold x m k y) i

@[simp] theorem oddExtend_apply (x : Vec d) (m k : ℤ) (f : Vec d → ℝ) (y : Vec d) :
    oddExtend x m k f y = windowFoldSign x m k y * f (windowFold x m k y) :=
  rfl

@[simp] theorem oddExtendGrad_apply (x : Vec d) (m k : ℤ) (G : Vec d → Vec d)
    (y : Vec d) (i : Fin d) :
    oddExtendGrad x m k G y i =
      windowFoldSign x m k y * foldSignCoord x m k i (y i) *
        G (windowFold x m k y) i :=
  rfl

theorem oddExtend_sub (x : Vec d) (m k : ℤ) (f g : Vec d → ℝ) :
    oddExtend x m k (fun y => f y - g y) =
      fun y => oddExtend x m k f y - oddExtend x m k g y := by
  funext y
  simp only [oddExtend_apply]
  ring

theorem abs_oddExtend (x : Vec d) (m k : ℤ) (f : Vec d → ℝ) (y : Vec d) :
    |oddExtend x m k f y| = |f (windowFold x m k y)| := by
  rw [oddExtend_apply, abs_mul, abs_windowFoldSign, one_mul]

/-! ## 4. The fold maps the reflected window onto the window -/

/-- **The fold is onto the window, off the interfaces.**  Every point of the
partially reflected window that avoids the reflection hyperplanes is carried
into the window itself by `windowFold`.  (The excluded set is a finite union of
hyperplanes, hence Lebesgue-null; the null set is what the downstream change of
variables discards.) -/
theorem windowFold_mem_truncatedWindow {x : Vec d} {m k : ℤ} {y : Vec d}
    (hkm : k < m) (hy : y ∈ reflectedWindow x m k)
    (hup : ∀ i, MeetsUpperFace x m k i → y i ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m)
    (hlow : ∀ i, MeetsLowerFace x m k i → y i ≠ -(1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    windowFold x m k y ∈ truncatedWindow x m k := by
  rw [mem_reflectedWindow_iff] at hy
  rw [truncatedWindow_eq_coordBox, mem_coordBox_iff]
  intro i
  have h1 := (hy i).1
  have h2 := (hy i).2
  by_cases hu : MeetsUpperFace x m k i
  · have hl : ¬ MeetsLowerFace x m k i :=
      not_meetsLowerFace_of_meetsUpperFace hkm hu
    rw [reflectedLo_of_not_meetsLowerFace hl] at h1
    rw [reflectedHi_of_meetsUpperFace hu] at h2
    have hne := hup i hu
    have hhi : windowHi x m k i = (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
      windowHi_of_meetsUpperFace hu
    rw [windowFold_apply, foldCoord_of_meetsUpperFace hu, hhi]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left (by linarith only [hlt])]
      exact ⟨h1, hlt⟩
    · rw [min_eq_right (by linarith only [hgt])]
      exact ⟨by linarith only [h2], by linarith only [hgt]⟩
  · by_cases hl : MeetsLowerFace x m k i
    · rw [reflectedLo_of_meetsLowerFace hl] at h1
      rw [reflectedHi_of_not_meetsUpperFace hu] at h2
      have hne := hlow i hl
      have hlo : windowLo x m k i = -(1 / 2 : ℝ) * (3 : ℝ) ^ m :=
        windowLo_of_meetsLowerFace hl
      rw [windowFold_apply, foldCoord_of_meetsLowerFace hu hl, hlo]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [max_eq_right (by linarith only [hlt])]
        exact ⟨by linarith only [hlt], by linarith only [h1]⟩
      · rw [max_eq_left (by linarith only [hgt])]
        exact ⟨hgt, h2⟩
    · rw [reflectedLo_of_not_meetsLowerFace hl] at h1
      rw [reflectedHi_of_not_meetsUpperFace hu] at h2
      rw [windowFold_apply, foldCoord_of_unmet hu hl]
      exact ⟨h1, h2⟩

/-! ## 5. The odd affine class `𝕃_odd(V)` -/

/-- **The odd affine class** of the paper's `e.v0.hessian`: the affine
functions `ℓ(y) = c + A·(y-x)` that vanish on every hyperplane containing a
face of `∂□_m` meeting the closure of the window. -/
def IsOddAffineData (x : Vec d) (m k : ℤ) (c : ℝ) (A : Vec d) : Prop :=
  (∀ i : Fin d, MeetsUpperFace x m k i →
      ∀ y : Vec d, y i = (1 / 2 : ℝ) * (3 : ℝ) ^ m → affineLift x c A y = 0) ∧
    ∀ i : Fin d, MeetsLowerFace x m k i →
      ∀ y : Vec d, y i = -(1 / 2 : ℝ) * (3 : ℝ) ^ m → affineLift x c A y = 0

/-- In the interior regime — no face met — the odd class is all of `𝕃`. -/
theorem isOddAffineData_of_no_met_face {x : Vec d} {m k : ℤ} (c : ℝ) (A : Vec d)
    (hup : ∀ i, ¬ MeetsUpperFace x m k i)
    (hlow : ∀ i, ¬ MeetsLowerFace x m k i) :
    IsOddAffineData x m k c A :=
  ⟨fun i hi _ _ => absurd hi (hup i), fun i hi _ _ => absurd hi (hlow i)⟩

/-- The affine lift's increment, coordinate by coordinate. -/
private theorem affineLift_sub_affineLift (x : Vec d) (c : ℝ) (A : Vec d)
    (y z : Vec d) :
    affineLift x c A y - affineLift x c A z = ∑ i : Fin d, A i * (y i - z i) := by
  simp only [affineLift, vecDot, Pi.sub_apply]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A met face pins an odd affine function to zero on a whole hyperplane. -/
private theorem exists_face_coord_vanishing {x : Vec d} {m k : ℤ} {c : ℝ}
    {A : Vec d} (hodd : IsOddAffineData x m k c A) {i : Fin d}
    (hi : MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i) :
    ∃ a : ℝ, ∀ w : Vec d, w i = a → affineLift x c A w = 0 := by
  classical
  by_cases hu : MeetsUpperFace x m k i
  · exact ⟨(1 / 2 : ℝ) * (3 : ℝ) ^ m, fun w hw => hodd.1 i hu w hw⟩
  · exact ⟨-(1 / 2 : ℝ) * (3 : ℝ) ^ m,
      fun w hw => hodd.2 i (hi.resolve_left hu) w hw⟩

/-- **The tangential slopes vanish.**  If the `i`-face is met then every
coordinate `j ≠ i` of the slope of an odd affine function is zero, so at a
single met face `𝕃_odd(V)` is the one-dimensional space `ℝ·(y_i - a_i)`. -/
theorem slope_eq_zero_of_ne_of_meets {x : Vec d} {m k : ℤ} {c : ℝ} {A : Vec d}
    (hodd : IsOddAffineData x m k c A) {i : Fin d}
    (hi : MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i) {j : Fin d}
    (hji : j ≠ i) : A j = 0 := by
  classical
  obtain ⟨a, hvanish⟩ := exists_face_coord_vanishing hodd hi
  set y : Vec d := fun l => if l = i then a else 0 with hydef
  set z : Vec d := fun l => if l = i then a else if l = j then 1 else 0 with hzdef
  have hyi : y i = a := by rw [hydef]; simp
  have hzi : z i = a := by rw [hzdef]; simp
  have hzj : z j = 1 := by rw [hzdef]; simp [hji]
  have hyj : y j = 0 := by rw [hydef]; simp [hji]
  have hsum : ∑ l : Fin d, A l * (z l - y l) = A j * (z j - y j) := by
    refine Finset.sum_eq_single j (fun l _ hlj => ?_) (fun h => ?_)
    · have hzl : z l = y l := by
        rw [hzdef, hydef]
        by_cases hli : l = i <;> simp [hli, hlj]
      rw [hzl, sub_self, mul_zero]
    · exact absurd (Finset.mem_univ j) h
  have hd := affineLift_sub_affineLift x c A z y
  rw [hvanish z hzi, hvanish y hyi, hsum, hzj, hyj] at hd
  linarith only [hd]

/-- **At an edge or corner the odd class collapses.**  If two *different*
coordinates each meet a face of `∂□_m`, the only odd affine function is `0`. -/
theorem affineLift_eq_zero_of_two_met {x : Vec d} {m k : ℤ} {c : ℝ} {A : Vec d}
    (hodd : IsOddAffineData x m k c A) {i j : Fin d} (hij : i ≠ j)
    (hi : MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i)
    (hj : MeetsUpperFace x m k j ∨ MeetsLowerFace x m k j) :
    affineLift x c A = fun _ => 0 := by
  classical
  have hA : ∀ l : Fin d, A l = 0 := by
    intro l
    by_cases hli : l = i
    · subst hli
      exact slope_eq_zero_of_ne_of_meets hodd hj hij
    · exact slope_eq_zero_of_ne_of_meets hodd hi hli
  have hconst : ∀ w : Vec d, affineLift x c A w = c := by
    intro w
    have hz : vecDot A (w - x) = 0 := by
      rw [vecDot]
      exact Finset.sum_eq_zero fun l _ => by rw [hA l, zero_mul]
    rw [affineLift, hz, add_zero]
  obtain ⟨a, hvanish⟩ := exists_face_coord_vanishing hodd hi
  set w : Vec d := fun l => if l = i then a else 0 with hwdef
  have hwi : w i = a := by rw [hwdef]; simp
  have hw : affineLift x c A w = 0 := hvanish w hwi
  rw [hconst w] at hw
  funext y
  rw [hconst y, hw]

/-! ## 6. Odd affine functions are fixed by the odd extension -/

/-- The one-met-face core: the only data used about the fold is that in the met
coordinate it is either the identity with sign `+1` or the reflection through
`a` with sign `-1`. -/
private theorem oddExtend_affineLift_single {x : Vec d} {m k : ℤ} {c : ℝ}
    {A : Vec d} {i : Fin d} (a : ℝ)
    (hvanish : ∀ w : Vec d, w i = a → affineLift x c A w = 0)
    (hother : ∀ j : Fin d, j ≠ i →
      ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hfold : ∀ t : ℝ,
      (foldCoord x m k i t = t ∧ foldSignCoord x m k i t = 1) ∨
        (foldCoord x m k i t = 2 * a - t ∧ foldSignCoord x m k i t = -1))
    (y : Vec d) :
    oddExtend x m k (affineLift x c A) y = affineLift x c A y := by
  classical
  have hfoldj : ∀ j : Fin d, j ≠ i → windowFold x m k y j = y j := fun j hji =>
    foldCoord_of_unmet (hother j hji).1 (hother j hji).2 (y j)
  have hsign : windowFoldSign x m k y = foldSignCoord x m k i (y i) := by
    rw [windowFoldSign]
    refine Finset.prod_eq_single i (fun j _ hji => ?_) (fun h => ?_)
    · exact foldSignCoord_of_unmet (hother j hji).1 (hother j hji).2 (y j)
    · exact absurd (Finset.mem_univ i) h
  rcases hfold (y i) with ⟨hid, hs⟩ | ⟨href, hs⟩
  · have hy : windowFold x m k y = y := by
      funext j
      by_cases hji : j = i
      · subst hji
        exact hid
      · exact hfoldj j hji
    rw [oddExtend_apply, hy, hsign, hs, one_mul]
  · have hsum : ∑ j : Fin d, A j * (windowFold x m k y j - y j) =
        A i * (windowFold x m k y i - y i) := by
      refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => ?_)
      · rw [hfoldj j hji, sub_self, mul_zero]
      · exact absurd (Finset.mem_univ i) h
    have hdiff := affineLift_sub_affineLift x c A (windowFold x m k y) y
    rw [hsum, show windowFold x m k y i = 2 * a - y i from href] at hdiff
    set w : Vec d := fun l => if l = i then a else y l with hwdef
    have hwi : w i = a := by rw [hwdef]; simp
    have hwsum : ∑ j : Fin d, A j * (y j - w j) = A i * (y i - w i) := by
      refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => ?_)
      · have hwj : w j = y j := by rw [hwdef]; simp [hji]
        rw [hwj, sub_self, mul_zero]
      · exact absurd (Finset.mem_univ i) h
    have hwd := affineLift_sub_affineLift x c A y w
    rw [hvanish w hwi, hwsum, hwi, sub_zero] at hwd
    have hexp1 : affineLift x c A (windowFold x m k y) - affineLift x c A y =
        2 * (A i * a) - 2 * (A i * y i) := by
      rw [hdiff]; ring
    have hexp2 : affineLift x c A y = A i * y i - A i * a := by
      rw [hwd]; ring
    rw [oddExtend_apply, hsign, hs]
    linarith only [hexp1, hexp2]

/-- **The oddness step.**  An affine function in `𝕃_odd(V)` is odd
under every met-face reflection, hence is its own partial odd extension.
Consequently the odd extension of `v₀ - ℓ` is the odd extension of `v₀` minus
`ℓ`, which is what the free parameter `ℓ` of `e.v0.hessian` is for. -/
theorem oddExtend_affineLift {x : Vec d} {m k : ℤ} {c : ℝ} {A : Vec d}
    (hodd : IsOddAffineData x m k c A) :
    oddExtend x m k (affineLift x c A) = affineLift x c A := by
  classical
  funext y
  by_cases hS : ∃ i : Fin d, MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i
  · obtain ⟨i, hi⟩ := hS
    by_cases hS2 : ∃ j : Fin d, j ≠ i ∧
        (MeetsUpperFace x m k j ∨ MeetsLowerFace x m k j)
    · obtain ⟨j, hji, hj⟩ := hS2
      rw [affineLift_eq_zero_of_two_met hodd (Ne.symm hji) hi hj]
      simp only [oddExtend_apply, mul_zero]
    · have hother : ∀ j : Fin d, j ≠ i →
          ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j := fun j hji =>
        ⟨fun h => hS2 ⟨j, hji, Or.inl h⟩, fun h => hS2 ⟨j, hji, Or.inr h⟩⟩
      by_cases hu : MeetsUpperFace x m k i
      · refine oddExtend_affineLift_single ((1 / 2 : ℝ) * (3 : ℝ) ^ m)
          (fun w hw => hodd.1 i hu w hw) hother (fun t => ?_) y
        by_cases ht : (1 / 2 : ℝ) * (3 : ℝ) ^ m < t
        · refine Or.inr ⟨?_, ?_⟩
          · rw [foldCoord_of_meetsUpperFace hu,
              min_eq_right (by linarith only [ht])]
            ring
          · rw [foldSignCoord_of_meetsUpperFace hu, ite_eq_left ht]
        · push Not at ht
          refine Or.inl ⟨?_, ?_⟩
          · rw [foldCoord_of_meetsUpperFace hu,
              min_eq_left (by linarith only [ht])]
          · rw [foldSignCoord_of_meetsUpperFace hu, ite_eq_right (not_lt.mpr ht)]
      · have hl : MeetsLowerFace x m k i := hi.resolve_left hu
        refine oddExtend_affineLift_single (-(1 / 2 : ℝ) * (3 : ℝ) ^ m)
          (fun w hw => hodd.2 i hl w hw) hother (fun t => ?_) y
        by_cases ht : t < -(1 / 2 : ℝ) * (3 : ℝ) ^ m
        · refine Or.inr ⟨?_, ?_⟩
          · rw [foldCoord_of_meetsLowerFace hu hl,
              max_eq_right (by linarith only [ht])]
            ring
          · rw [foldSignCoord_of_meetsLowerFace hu hl, ite_eq_left ht]
        · push Not at ht
          refine Or.inl ⟨?_, ?_⟩
          · rw [foldCoord_of_meetsLowerFace hu hl,
              max_eq_left (by linarith only [ht])]
          · rw [foldSignCoord_of_meetsLowerFace hu hl, ite_eq_right (not_lt.mpr ht)]
  · have hother : ∀ j : Fin d,
        ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j := fun j =>
      ⟨fun h => hS ⟨j, Or.inl h⟩, fun h => hS ⟨j, Or.inr h⟩⟩
    have hfold : windowFold x m k y = y := funext fun j =>
      foldCoord_of_unmet (hother j).1 (hother j).2 (y j)
    have hsign : windowFoldSign x m k y = 1 :=
      Finset.prod_eq_one fun j _ =>
        foldSignCoord_of_unmet (hother j).1 (hother j).2 (y j)
    rw [oddExtend_apply, hfold, hsign, one_mul]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
