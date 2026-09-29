/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Basic

/-!
# Rounding Predicates

Semantic specifications for directed, toward-zero, and nearest rounding.  They are independent of
any radix or concrete format: a predicate `F : ℝ → Prop` identifies the representable values, and
the point predicates characterize the required output among those values.

These definitions correspond to Flocq's `Rnd_DN_pt`, `Rnd_UP_pt`, `Rnd_ZR_pt`, and `Rnd_N_pt`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- `f` is the greatest `F`-value no larger than `x`. -/
def RoundDownPoint (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ f ≤ x ∧ ∀ g, F g → g ≤ x → g ≤ f

/-- `f` is the least `F`-value no smaller than `x`. -/
def RoundUpPoint (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ x ≤ f ∧ ∀ g, F g → x ≤ g → f ≤ g

/-- A downward rounding point is a greatest element of the representable lower bounds. -/
theorem roundDownPoint_iff_isGreatest (F : ℝ → Prop) (x f : ℝ) :
    RoundDownPoint F x f ↔ IsGreatest {g | F g ∧ g ≤ x} f := by
  constructor
  · rintro ⟨hf, hfx, hgreatest⟩
    exact ⟨⟨hf, hfx⟩, fun _ hg => hgreatest _ hg.1 hg.2⟩
  · rintro ⟨⟨hf, hfx⟩, hgreatest⟩
    exact ⟨hf, hfx, fun _ hg hgx => hgreatest ⟨hg, hgx⟩⟩

/-- An upward rounding point is a least element of the representable upper bounds. -/
theorem roundUpPoint_iff_isLeast (F : ℝ → Prop) (x f : ℝ) :
    RoundUpPoint F x f ↔ IsLeast {g | F g ∧ x ≤ g} f := by
  constructor
  · rintro ⟨hf, hxf, hleast⟩
    exact ⟨⟨hf, hxf⟩, fun _ hg => hleast _ hg.1 hg.2⟩
  · rintro ⟨⟨hf, hxf⟩, hleast⟩
    exact ⟨hf, hxf, fun _ hg hxg => hleast ⟨hg, hxg⟩⟩

/-- Directed down on nonnegative inputs and directed up on nonpositive inputs. -/
def RoundTowardZeroPoint (F : ℝ → Prop) (x f : ℝ) : Prop :=
  (0 ≤ x → RoundDownPoint F x f) ∧ (x ≤ 0 → RoundUpPoint F x f)

/-- `f` is an `F`-value at least as close to `x` as every other representable value. -/
def RoundNearestPoint (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ ∀ g, F g → abs (f - x) ≤ abs (g - x)

/-- A rounding function rounds downward with respect to `F` at every input. -/
def RoundDown (F : ℝ → Prop) (round : ℝ → ℝ) : Prop :=
  ∀ x, RoundDownPoint F x (round x)

/-- A rounding function rounds upward with respect to `F` at every input. -/
def RoundUp (F : ℝ → Prop) (round : ℝ → ℝ) : Prop :=
  ∀ x, RoundUpPoint F x (round x)

/-- A rounding function rounds toward zero with respect to `F` at every input. -/
def RoundTowardZero (F : ℝ → Prop) (round : ℝ → ℝ) : Prop :=
  ∀ x, RoundTowardZeroPoint F x (round x)

/-- A rounding function rounds to a nearest `F`-value at every input. -/
def RoundNearest (F : ℝ → Prop) (round : ℝ → ℝ) : Prop :=
  ∀ x, RoundNearestPoint F x (round x)

/-- A downward rounding point is unique. -/
theorem roundDownPoint_unique {F : ℝ → Prop} {x f g : ℝ}
    (hf : RoundDownPoint F x f) (hg : RoundDownPoint F x g) : f = g :=
  ((roundDownPoint_iff_isGreatest F x f).mp hf).unique
    ((roundDownPoint_iff_isGreatest F x g).mp hg)

/-- An upward rounding point is unique. -/
theorem roundUpPoint_unique {F : ℝ → Prop} {x f g : ℝ}
    (hf : RoundUpPoint F x f) (hg : RoundUpPoint F x g) : f = g :=
  ((roundUpPoint_iff_isLeast F x f).mp hf).unique
    ((roundUpPoint_iff_isLeast F x g).mp hg)

/-- A representable value is its own downward rounding point. -/
theorem roundDownPoint_refl {F : ℝ → Prop} {x : ℝ} (hx : F x) :
    RoundDownPoint F x x := by
  exact ⟨hx, le_rfl, fun _ _ hg => hg⟩

/-- A representable value is its own upward rounding point. -/
theorem roundUpPoint_refl {F : ℝ → Prop} {x : ℝ} (hx : F x) :
    RoundUpPoint F x x := by
  exact ⟨hx, le_rfl, fun _ _ hg => hg⟩

/-- Negation turns a downward point into an upward point for a symmetric format. -/
theorem roundUpPoint_neg {F : ℝ → Prop}
    (hneg : ∀ x, F x → F (-x)) {x f : ℝ} (hf : RoundDownPoint F x f) :
    RoundUpPoint F (-x) (-f) := by
  refine ⟨hneg f hf.1, neg_le_neg hf.2.1, ?_⟩
  intro g hg hxg
  have hng : F (-g) := hneg g hg
  have hngx : -g ≤ x := by simpa using neg_le_neg hxg
  simpa using neg_le_neg (hf.2.2 (-g) hng hngx)

/-- Negation turns an upward point into a downward point for a symmetric format. -/
theorem roundDownPoint_neg {F : ℝ → Prop}
    (hneg : ∀ x, F x → F (-x)) {x f : ℝ} (hf : RoundUpPoint F x f) :
    RoundDownPoint F (-x) (-f) := by
  refine ⟨hneg f hf.1, neg_le_neg hf.2.1, ?_⟩
  intro g hg hgx
  have hng : F (-g) := hneg g hg
  have hxng : x ≤ -g := by simpa using neg_le_neg hgx
  simpa using neg_le_neg (hf.2.2 (-g) hng hxng)

/-- Any representable value lies below the downward point or above the upward point. -/
theorem roundDownUpPoint_split {F : ℝ → Prop} {x d u f : ℝ}
    (hd : RoundDownPoint F x d) (hu : RoundUpPoint F x u) (hf : F f) :
    f ≤ d ∨ u ≤ f := by
  rcases le_total f x with hfx | hxf
  · exact Or.inl (hd.2.2 f hf hfx)
  · exact Or.inr (hu.2.2 f hf hxf)

/--
A representable value no farther than both directed neighbors is globally nearest.  Every other
representable value lies outside the interval between those neighbors.
-/
theorem roundNearestPoint_of_down_up {F : ℝ → Prop} {x d u f : ℝ}
    (hd : RoundDownPoint F x d) (hu : RoundUpPoint F x u)
    (hf : F f) (hfd : abs (f - x) ≤ abs (d - x))
    (hfu : abs (f - x) ≤ abs (u - x)) : RoundNearestPoint F x f := by
  refine ⟨hf, ?_⟩
  intro g hg
  rcases roundDownUpPoint_split hd hu hg with hgd | hug
  · calc
      abs (f - x) ≤ abs (d - x) := hfd
      _ = x - d := by simpa [neg_sub] using abs_of_nonpos (sub_nonpos.mpr hd.2.1)
      _ ≤ x - g := sub_le_sub_left hgd x
      _ = abs (g - x) := by
        simpa [neg_sub] using
          (abs_of_nonpos (sub_nonpos.mpr (hgd.trans hd.2.1))).symm
  · calc
      abs (f - x) ≤ abs (u - x) := hfu
      _ = u - x := abs_of_nonneg (sub_nonneg.mpr hu.2.1)
      _ ≤ g - x := sub_le_sub_right hug x
      _ = abs (g - x) := (abs_of_nonneg (sub_nonneg.mpr (hu.2.1.trans hug))).symm

end FloatLib.Floats.Formats.Flocq
