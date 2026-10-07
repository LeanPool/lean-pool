/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Halfspaces
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
A filled nondegenerate triangle is exactly an intersection of three explicit
halfspaces. In particular, endpoint and forbidden-point support conditions are
proved for the actual convex-hull datatype, rather than a surrogate polygon.
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
open scoped BigOperators
namespace ConwaySoifer

/-- The coordinate determinant of two planar vectors. -/
def cross (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The real linear functional with the given coordinate coefficients. -/
def linearForm (n : Point) : Point →ₗ[ℝ] ℝ where
  toFun p := n.1 * p.1 + n.2 * p.2
  map_add' := by
    intro p q; dsimp; ring
  map_smul' := by
    intro a p; dsimp; ring

@[simp] theorem linearForm_apply (n p : Point) :
    linearForm n p = n.1 * p.1 + n.2 * p.2 := rfl

@[simp] theorem cross_self (p : Point) : cross p p = 0 := by
  dsimp [cross]; ring
@[simp] theorem cross_zero_left (p : Point) : cross (0, 0) p = 0 := by
  simp [cross]
@[simp] theorem cross_zero_right (p : Point) : cross p (0, 0) = 0 := by
  simp [cross]

/-- The oriented doubled coordinate area of three vertices. -/
def triangleDet (a b c : Point) : ℝ := cross (b-a) (c-a)

/-- The barycentric coefficient of the second vertex relative to the first. -/
def baryFirst (a b c p : Point) : ℝ := cross (p-a) (c-a) / triangleDet a b c
/-- The barycentric coefficient of the third vertex relative to the first. -/
def barySecond (a b c p : Point) : ℝ := cross (b-a) (p-a) / triangleDet a b c

/-- The three outward normals, with orientation corrected by the determinant. -/
def triangleNormals (a b c : Point) : Fin 3 → Point :=
  let u := b-a
  let v := c-a
  let δ := triangleDet a b c
  ![(-v.2 / δ, v.1 / δ), (u.2 / δ, -u.1 / δ),
    ((v.2-u.2) / δ, (u.1-v.1) / δ)]

/-- The three closed halfspaces determined by an oriented triangle. -/
def triangleHalfspaces (a b c : Point) : HalfspaceSystem (Fin 3) where
  normal i := linearForm (triangleNormals a b c i)
  offset i := linearForm (triangleNormals a b c i) a + if i = 2 then 1 else 0

theorem HalfspaceSystem.convex_carrier {ι : Type*} (H : HalfspaceSystem ι) :
    Convex ℝ H.carrier := by
  intro p hp q hq a b ha hb hab i
  change H.normal i (a • p + b • q) ≤ H.offset i
  rw [map_add, map_smul, map_smul]
  change a * H.normal i p + b * H.normal i q ≤ H.offset i
  have h₁ := mul_le_mul_of_nonneg_left (hp i) ha
  have h₂ := mul_le_mul_of_nonneg_left (hq i) hb
  calc
    _ ≤ a * H.offset i + b * H.offset i := add_le_add h₁ h₂
    _ = H.offset i := by
      rw [← add_mul, hab, one_mul]

theorem triangleHalfspaces_iff (a b c p : Point) :
    p ∈ (triangleHalfspaces a b c).carrier ↔
      0 ≤ baryFirst a b c p ∧ 0 ≤ barySecond a b c p ∧
        baryFirst a b c p + barySecond a b c p ≤ 1 := by
  have h₀ : (triangleHalfspaces a b c).normal 0 p -
      (triangleHalfspaces a b c).offset 0 = -baryFirst a b c p := by
    simp only [triangleHalfspaces, linearForm_apply]
    dsimp [triangleNormals, baryFirst, cross]
    ring
  have h₁ : (triangleHalfspaces a b c).normal 1 p -
      (triangleHalfspaces a b c).offset 1 = -barySecond a b c p := by
    simp only [triangleHalfspaces, linearForm_apply]
    dsimp [triangleNormals, barySecond, cross]
    ring
  have h₂ : (triangleHalfspaces a b c).normal 2 p -
      (triangleHalfspaces a b c).offset 2 =
        baryFirst a b c p + barySecond a b c p - 1 := by
    simp only [triangleHalfspaces, linearForm_apply]
    dsimp [triangleNormals, baryFirst, barySecond, cross]
    ring
  constructor
  · intro hp
    have hp₀ := hp 0
    have hp₁ := hp 1
    have hp₂ := hp 2
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨hp₀, hp₁, hp₂⟩ i
    fin_cases i
    · change (triangleHalfspaces a b c).normal 0 p ≤ (triangleHalfspaces a b c).offset 0
      linarith
    · change (triangleHalfspaces a b c).normal 1 p ≤ (triangleHalfspaces a b c).offset 1
      linarith
    · change (triangleHalfspaces a b c).normal 2 p ≤ (triangleHalfspaces a b c).offset 2
      linarith

@[simp] theorem baryFirst_self (a b c : Point) : baryFirst a b c a = 0 := by
  simp [baryFirst, cross]
@[simp] theorem barySecond_self (a b c : Point) : barySecond a b c a = 0 := by
  simp [barySecond, cross]
@[simp] theorem baryFirst_second (a b c : Point) (h : triangleDet a b c ≠ 0) :
    baryFirst a b c b = 1 := div_self h
@[simp] theorem barySecond_second (a b c : Point) : barySecond a b c b = 0 := by
  simp [barySecond]
@[simp] theorem baryFirst_third (a b c : Point) : baryFirst a b c c = 0 := by
  simp [baryFirst]
@[simp] theorem barySecond_third (a b c : Point) (h : triangleDet a b c ≠ 0) :
    barySecond a b c c = 1 := div_self h

theorem bary_expansion (a b c p : Point) (h : triangleDet a b c ≠ 0) :
    p = (1-baryFirst a b c p-barySecond a b c p) • a +
      baryFirst a b c p • b + barySecond a b c p • c := by
  apply Prod.ext <;>
    dsimp only [baryFirst, barySecond, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp [h] <;>
    dsimp [triangleDet, cross] <;> ring

theorem convex_three_mem {S : Set Point} (hS : Convex ℝ S)
    {a b c : Point} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    (1-u-v) • a + u • b + v • c ∈ S := by
  let w : Fin 3 → ℝ := ![1-u-v, u, v]
  let z : Fin 3 → Point := ![a, b, c]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i hi
    fin_cases i <;> dsimp [w] <;> linarith
  have hsum : ∑ i : Fin 3, w i = 1 := by
    simp [w, Fin.sum_univ_succ]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ S := by
    intro i hi
    fin_cases i <;> simp [z, ha, hb, hc]
  have hm := hS.sum_mem hw hsum hz
  simpa [w, z, Fin.sum_univ_succ, add_assoc] using hm

/-- No equilateral assumption is needed for the geometric representation. -/
theorem triangleHalfspaces_eq_convexHull (a b c : Point)
    (h : triangleDet a b c ≠ 0) :
    (triangleHalfspaces a b c).carrier =
      convexHull ℝ (Set.range (![a, b, c] : Fin 3 → Point)) := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨hu, hv, huv⟩ := (triangleHalfspaces_iff a b c p).mp hp
    have ha : a ∈ convexHull ℝ (Set.range (![a, b, c] : Fin 3 → Point)) :=
      subset_convexHull ℝ _ ⟨0, rfl⟩
    have hb : b ∈ convexHull ℝ (Set.range (![a, b, c] : Fin 3 → Point)) :=
      subset_convexHull ℝ _ ⟨1, rfl⟩
    have hc : c ∈ convexHull ℝ (Set.range (![a, b, c] : Fin 3 → Point)) :=
      subset_convexHull ℝ _ ⟨2, rfl⟩
    rw [bary_expansion a b c p h]
    exact convex_three_mem (convex_convexHull ℝ _) ha hb hc hu hv huv
  · apply convexHull_min ?_ (HalfspaceSystem.convex_carrier _)
    rintro _ ⟨i, rfl⟩
    apply (triangleHalfspaces_iff _ _ _ _).mpr
    fin_cases i <;> simp [h]

theorem triangleDet_sq_identity (a b c : Point) :
    3 * triangleDet a b c ^ 2 =
      4 * sqDist b a * sqDist c a - (sqDist b a + sqDist c a - sqDist b c) ^ 2 := by
  dsimp [triangleDet, cross, sqDist]
  ring

theorem EquilateralTriangle.det_sq (T : EquilateralTriangle) :
    triangleDet (T.vertices 0) (T.vertices 1) (T.vertices 2) ^ 2 = T.side ^ 4 := by
  have h := triangleDet_sq_identity (T.vertices 0) (T.vertices 1) (T.vertices 2)
  rw [T.equilateral 1 0 (by decide), T.equilateral 2 0 (by decide),
    T.equilateral 1 2 (by decide)] at h
  nlinarith

theorem EquilateralTriangle.det_ne_zero (T : EquilateralTriangle) (hs : 0 < T.side) :
    triangleDet (T.vertices 0) (T.vertices 1) (T.vertices 2) ≠ 0 := by
  intro hz
  have h := T.det_sq
  rw [hz] at h
  have hp := pow_pos hs 4
  nlinarith

/-- The halfspace system induced by the triangle's three vertices. -/
def EquilateralTriangle.halfspaces (T : EquilateralTriangle) : HalfspaceSystem (Fin 3) :=
  triangleHalfspaces (T.vertices 0) (T.vertices 1) (T.vertices 2)

theorem EquilateralTriangle.carrier_eq_halfspaces (T : EquilateralTriangle)
    (hs : 0 < T.side) : T.carrier = T.halfspaces.carrier := by
  unfold EquilateralTriangle.halfspaces
  rw [triangleHalfspaces_eq_convexHull _ _ _ (T.det_ne_zero hs)]
  have hv : (![T.vertices 0, T.vertices 1, T.vertices 2] : Fin 3 → Point) = T.vertices := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rfl

theorem EquilateralTriangle.full_endpoint_support (T : EquilateralTriangle)
    (hs : 0 < T.side) {v d : Point} (hv : v ∈ T.carrier)
    (hd : sqDist d (0, 0) = 1) :
    ∃ i : Fin 3, 0 < T.halfspaces.normal i d ∧
      T.halfspaces.normal i (linePoint v d (rayLen T v d)) = T.halfspaces.offset i ∧
      ∀ q ∈ T.carrier, T.halfspaces.normal i q ≤
        T.halfspaces.normal i (linePoint v d (rayLen T v d)) :=
  rayLen_has_supporting_normal T T.halfspaces (T.carrier_eq_halfspaces hs) hv hd

theorem EquilateralTriangle.forbidden_support (T : EquilateralTriangle)
    (hs : 0 < T.side) {v d : Point} (hv : v ∈ T.carrier)
    {t : ℝ} (ht : 0 < t) (hout : linePoint v d t ∉ T.carrier) :
    ∃ i : Fin 3, 0 < T.halfspaces.normal i d ∧
      ∀ q ∈ T.carrier, T.halfspaces.normal i q < T.halfspaces.normal i (linePoint v d t) :=
  forbidden_ray_has_strict_support T T.halfspaces (T.carrier_eq_halfspaces hs) hv ht hout

end ConwaySoifer
