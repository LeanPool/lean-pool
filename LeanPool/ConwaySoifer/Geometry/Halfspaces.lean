/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Rays
import Mathlib.Tactic

/-!
Necessary outward-normal conditions for genuine full ray endpoints and strict
forbidden points. These are geometric implications, not assumptions encoded in
a certificate. The finite index set may include redundant halfspaces.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

noncomputable section
namespace ConwaySoifer

private theorem finite_positive_lower_bound {ι : Type*} [Finite ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  classical
  let _ := Fintype.ofFinite ι
  have hfin : ∀ S : Finset ι, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε ≤ f i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨ε, hε, hle⟩ := ih
      refine ⟨min (f i) ε, lt_min (hf i) hε, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (hle j hj)
  obtain ⟨ε, hε, hle⟩ := hfin Finset.univ
  exact ⟨ε, hε, fun i => hle i (Finset.mem_univ i)⟩

/-- A finite intersection of closed linear halfspaces. -/
structure HalfspaceSystem (ι : Type*) where
  /-- The linear functional defining each closed halfspace. -/
  normal : ι → Point →ₗ[ℝ] ℝ
  /-- The upper bound for each defining functional. -/
  offset : ι → ℝ

/-- The closed intersection of the system's linear halfspaces. -/
def HalfspaceSystem.carrier {ι : Type*} (H : HalfspaceSystem ι) : Set Point :=
  {p | ∀ i, H.normal i p ≤ H.offset i}

@[simp] theorem HalfspaceSystem.normal_linePoint {ι : Type*}
    (H : HalfspaceSystem ι) (i : ι) (p d : Point) (t : ℝ) :
    H.normal i (linePoint p d t) = H.normal i p + t * H.normal i d := by
  simp [linePoint]

/-- If every positive displacement leaves the intersection, some active facet
has strictly positive derivative in that direction. Finiteness is essential. -/
theorem HalfspaceSystem.active_of_exit {ι : Type*} [Finite ι]
    (H : HalfspaceSystem ι) {p d : Point} (hp : p ∈ H.carrier)
    (hexit : ∀ ε : ℝ, 0 < ε → linePoint p d ε ∉ H.carrier) :
    ∃ i, 0 < H.normal i d ∧ H.normal i p = H.offset i := by
  classical
  by_contra hbad
  have hslack : ∀ i, 0 < H.normal i d → H.normal i p < H.offset i := by
    intro i hi
    apply lt_of_le_of_ne (hp i)
    intro he
    exact hbad ⟨i, hi, he⟩
  let step : ι → ℝ := fun i =>
    if 0 < H.normal i d then (H.offset i - H.normal i p) / H.normal i d else 1
  have hstep : ∀ i, 0 < step i := by
    intro i
    dsimp [step]
    split_ifs with hi
    · exact div_pos (sub_pos.mpr (hslack i hi)) hi
    · norm_num
  obtain ⟨ε, hε, hle⟩ := finite_positive_lower_bound step hstep
  apply hexit ε hε
  intro i
  rw [H.normal_linePoint]
  by_cases hi : 0 < H.normal i d
  · have hbound := hle i
    dsimp [step] at hbound
    rw [ite_eq_left hi] at hbound
    have hmul := (le_div_iff₀ hi).mp hbound
    linarith
  · have hmul : ε * H.normal i d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hε.le (le_of_not_gt hi)
    linarith [hp i]

/-- A violated halfspace at a positive point on a ray from an included anchor
necessarily has a strictly positive outward derivative on that ray. -/
theorem HalfspaceSystem.violated_of_forbidden {ι : Type*}
    (H : HalfspaceSystem ι) {v d : Point} (hv : v ∈ H.carrier)
    {t : ℝ} (ht : 0 < t) (hout : linePoint v d t ∉ H.carrier) :
    ∃ i, 0 < H.normal i d ∧ H.offset i < H.normal i (linePoint v d t) := by
  classical
  change ¬ ∀ i, H.normal i (linePoint v d t) ≤ H.offset i at hout
  push Not at hout
  obtain ⟨i, hi⟩ := hout
  refine ⟨i, ?_, hi⟩
  rw [H.normal_linePoint] at hi
  by_contra hn
  have hmul : t * H.normal i d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hn)
  linarith [hv i]

/-- Exact ray endpoints supply a supporting normal for every mandatory point. -/
theorem rayLen_has_supporting_normal {ι : Type*} [Finite ι]
    (T : EquilateralTriangle) (H : HalfspaceSystem ι)
    (hrep : T.carrier = H.carrier) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) :
    ∃ i, 0 < H.normal i d ∧
      H.normal i (linePoint v d (rayLen T v d)) = H.offset i ∧
      ∀ q ∈ T.carrier,
        H.normal i q ≤ H.normal i (linePoint v d (rayLen T v d)) := by
  have hp : linePoint v d (rayLen T v d) ∈ H.carrier := by
    rw [← hrep]
    exact rayLen_endpoint_mem T hv hd
  have hexit : ∀ ε : ℝ, 0 < ε →
      linePoint (linePoint v d (rayLen T v d)) d ε ∉ H.carrier := by
    intro ε hε
    have he : linePoint (linePoint v d (rayLen T v d)) d ε =
        linePoint v d (rayLen T v d + ε) := by
      simp [linePoint, add_smul, add_assoc]
    rw [he, ← hrep]
    exact not_mem_after_rayLen T hv hd (by linarith)
  obtain ⟨i, hi, he⟩ := H.active_of_exit hp hexit
  refine ⟨i, hi, he, ?_⟩
  intro q hq
  rw [he]
  exact (hrep ▸ hq) i

/-- A forbidden positive ray point supplies the strict support inequality used
by the contact-sensitive finite certificates. -/
theorem forbidden_ray_has_strict_support {ι : Type*}
    (T : EquilateralTriangle) (H : HalfspaceSystem ι)
    (hrep : T.carrier = H.carrier) {v d : Point} (hv : v ∈ T.carrier)
    {t : ℝ} (ht : 0 < t) (hout : linePoint v d t ∉ T.carrier) :
    ∃ i, 0 < H.normal i d ∧
      ∀ q ∈ T.carrier, H.normal i q < H.normal i (linePoint v d t) := by
  have hv' : v ∈ H.carrier := hrep ▸ hv
  have hout' : linePoint v d t ∉ H.carrier := by
    rwa [← hrep]
  obtain ⟨i, hi, hviol⟩ := H.violated_of_forbidden hv' ht hout'
  exact ⟨i, hi, fun q hq => lt_of_le_of_lt ((hrep ▸ hq) i) hviol⟩

end ConwaySoifer
