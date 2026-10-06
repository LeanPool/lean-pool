/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Diameter
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-!
Full ray sections of the actual closed filled triangles. The transfer theorem
uses the cover of an open segment, not merely a finite witness assignment.
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
open Set
namespace ConwaySoifer

theorem sqDist_eq_zero_iff (p q : Point) : sqDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    have h₁ : (p.1-q.1) = 0 := by
      dsimp [sqDist] at h
      nlinarith [sq_nonneg (2*(p.1-q.1)+(p.2-q.2)), sq_nonneg (p.2-q.2),
        sq_nonneg ((p.1-q.1)+2*(p.2-q.2))]
    have h₂ : (p.2-q.2) = 0 := by
      dsimp [sqDist] at h
      rw [h₁] at h
      nlinarith [sq_nonneg (p.2-q.2)]
    exact Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂)
  · rintro rfl
    simp [sqDist]

theorem EquilateralTriangle.convex_carrier (T : EquilateralTriangle) :
    Convex ℝ T.carrier := convex_convexHull ℝ _

theorem EquilateralTriangle.isCompact_carrier (T : EquilateralTriangle) :
    IsCompact T.carrier := (Set.finite_range T.vertices).isCompact_convexHull ℝ

theorem EquilateralTriangle.isClosed_carrier (T : EquilateralTriangle) :
    IsClosed T.carrier := T.isCompact_carrier.isClosed

theorem EquilateralTriangle.vertex_mem_carrier (T : EquilateralTriangle) (i : Fin 3) :
    T.vertices i ∈ T.carrier := subset_convexHull ℝ _ (Set.mem_range_self i)

/-- The point at a real parameter along a ray from a specified base point. -/
def linePoint (v d : Point) (t : ℝ) : Point := v + t • d

theorem continuous_linePoint (v d : Point) : Continuous (linePoint v d) := by
  unfold linePoint
  fun_prop

@[simp] theorem linePoint_zero (v d : Point) : linePoint v d 0 = v := by
  simp [linePoint]

theorem sqDist_linePoint (v d : Point) (t : ℝ) :
    sqDist (linePoint v d t) v = t ^ 2 * sqDist d (0, 0) := by
  rcases v with ⟨v₁, v₂⟩
  rcases d with ⟨d₁, d₂⟩
  dsimp [linePoint, sqDist]
  ring

theorem linePoint_between {S : Set Point} (hS : Convex ℝ S) {v d : Point}
    (hv : v ∈ S) {u t : ℝ} (hu : linePoint v d u ∈ S)
    (ht : 0 ≤ t) (htu : t ≤ u) : linePoint v d t ∈ S := by
  by_cases ht0 : t = 0
  · simpa [ht0] using hv
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hup : 0 < u := lt_of_lt_of_le htp htu
  have htu' : t/u ≤ 1 := (div_le_one hup).mpr htu
  have hmem := hS hv hu (sub_nonneg.mpr htu') (div_nonneg ht hup.le)
    (show 1-t/u+t/u = 1 by ring)
  convert hmem using 1
  rcases v with ⟨v₁, v₂⟩
  rcases d with ⟨d₁, d₂⟩
  apply Prod.ext <;> dsimp [linePoint] <;> field_simp <;> ring

/-- All nonnegative parameters, without truncation or a guessed endpoint. -/
def rayParams (T : EquilateralTriangle) (v d : Point) : Set ℝ :=
  {t | 0 ≤ t ∧ linePoint v d t ∈ T.carrier}

/-- The supremum of the nonnegative parameters whose ray point belongs to the triangle. -/
def rayLen (T : EquilateralTriangle) (v d : Point) : ℝ := sSup (rayParams T v d)

theorem rayParams_nonempty (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) : (rayParams T v d).Nonempty :=
  ⟨0, le_rfl, by simpa using hv⟩

theorem rayParams_le_side (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1)
    {t : ℝ} (ht : t ∈ rayParams T v d) : t ≤ T.side := by
  obtain ⟨ht0, htmem⟩ := ht
  have hdist := T.sqDist_le htmem hv
  rw [sqDist_linePoint, hd, mul_one] at hdist
  nlinarith [T.side_nonneg]

theorem rayParams_bddAbove (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) : BddAbove (rayParams T v d) :=
  ⟨T.side, fun _ ht => rayParams_le_side T hv hd ht⟩

theorem isClosed_rayParams (T : EquilateralTriangle) (v d : Point) :
    IsClosed (rayParams T v d) :=
  isClosed_Ici.inter (T.isClosed_carrier.preimage (continuous_linePoint v d))

theorem rayLen_mem (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) :
    rayLen T v d ∈ rayParams T v d :=
  (isClosed_rayParams T v d).csSup_mem (rayParams_nonempty T hv)
    (rayParams_bddAbove T hv hd)

theorem rayLen_nonneg (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) : 0 ≤ rayLen T v d :=
  (rayLen_mem T hv hd).1

theorem rayLen_le_side (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) : rayLen T v d ≤ T.side :=
  rayParams_le_side T hv hd (rayLen_mem T hv hd)

theorem rayLen_endpoint_mem (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) :
    linePoint v d (rayLen T v d) ∈ T.carrier := (rayLen_mem T hv hd).2

theorem linePoint_mem_iff_le_rayLen (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) {t : ℝ} (ht : 0 ≤ t) :
    linePoint v d t ∈ T.carrier ↔ t ≤ rayLen T v d := by
  constructor
  · intro hm
    exact le_csSup (rayParams_bddAbove T hv hd) ⟨ht, hm⟩
  · intro hle
    exact linePoint_between T.convex_carrier hv (rayLen_endpoint_mem T hv hd) ht hle

theorem not_mem_after_rayLen (T : EquilateralTriangle) {v d : Point}
    (hv : v ∈ T.carrier) (hd : sqDist d (0, 0) = 1) {t : ℝ}
    (ht : rayLen T v d < t) : linePoint v d t ∉ T.carrier := by
  intro hmem
  have ht0 : 0 ≤ t := le_trans (rayLen_nonneg T hv hd) ht.le
  exact (not_le_of_gt ht) ((linePoint_mem_iff_le_rayLen T hv hd ht0).mp hmem)

/-- The union of all triangles except a specified owner is still closed. -/
def otherCarriers (T : Configuration) (i : Fin 10) : Set Point :=
  ⋃ j : {j : Fin 10 // j ≠ i}, (T j).carrier

theorem isClosed_otherCarriers (T : Configuration) (i : Fin 10) :
    IsClosed (otherCarriers T i) :=
  isClosed_iUnion_of_finite (fun j => (T j).isClosed_carrier)

theorem mem_otherCarriers (T : Configuration) (i : Fin 10) (p : Point) :
    p ∈ otherCarriers T i ↔ ∃ j, j ≠ i ∧ p ∈ (T j).carrier := by
  simp only [otherCarriers, Set.mem_iUnion, Subtype.exists, exists_prop]

/-- A real open segment covered by a finite closed union transfers to its endpoint. -/
theorem closed_cover_endpoint {S : Set Point} (hS : IsClosed S) {f : ℝ → Point}
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hcover : ∀ t ∈ Set.Ioo a b, f t ∈ S) : f a ∈ S := by
  have hsub : Set.Ioo a b ⊆ f ⁻¹' S := hcover
  have hcl : closure (Set.Ioo a b) ⊆ f ⁻¹' S :=
    closure_minimal hsub (hS.preimage hf)
  have ha : a ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  exact hcl ha

/-- Uses coverage immediately after the full endpoint. -/
theorem rayLen_transfers (T : Configuration) (hc : Covers T) (i : Fin 10)
    {v d : Point} (hv : v ∈ (T i).carrier) (hd : sqDist d (0, 0) = 1)
    {b : ℝ} (hb : rayLen (T i) v d < b)
    (hseg : ∀ t ∈ Set.Icc 0 b, linePoint v d t ∈ target) :
    ∃ j, j ≠ i ∧ linePoint v d (rayLen (T i) v d) ∈ (T j).carrier := by
  apply (mem_otherCarriers T i _).mp
  apply closed_cover_endpoint (isClosed_otherCarriers T i) (continuous_linePoint v d) hb
  intro t ht
  have ht0 := le_trans (rayLen_nonneg (T i) hv hd) ht.1.le
  obtain ⟨j, hj⟩ := hc _ (hseg t ⟨ht0, ht.2.le⟩)
  have hji : j ≠ i := by
    intro he
    rw [he] at hj
    exact not_mem_after_rayLen (T i) hv hd ht.1 hj
  exact (mem_otherCarriers T i _).mpr ⟨j, hji, hj⟩

/-- Unique ownership forces a strictly positive section. -/
theorem rayLen_pos_of_unique_owner (T : Configuration) (hc : Covers T) (i : Fin 10)
    {v d : Point} (hv : v ∈ (T i).carrier) (hd : sqDist d (0, 0) = 1)
    (hunique : ∀ j, j ≠ i → v ∉ (T j).carrier)
    {b : ℝ} (hb : 0 < b) (hseg : ∀ t ∈ Set.Icc 0 b, linePoint v d t ∈ target) :
    0 < rayLen (T i) v d := by
  let U : Set ℝ := (linePoint v d) ⁻¹' (otherCarriers T i)ᶜ
  have hU : IsOpen U :=
    (isClosed_otherCarriers T i).isOpen_compl.preimage (continuous_linePoint v d)
  have h0 : (0 : ℝ) ∈ U := by
    change linePoint v d 0 ∉ otherCarriers T i
    rw [linePoint_zero]
    rintro h
    obtain ⟨j, hji, hj⟩ := (mem_otherCarriers T i v).mp h
    exact hunique j hji hj
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  let t : ℝ := min (ε/2) (b/2)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htb : t ≤ b := le_trans (min_le_right _ _) (by linarith)
  have htU : t ∈ U := hball (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg ht.le] using
      htε)
  obtain ⟨j, hj⟩ := hc _ (hseg t ⟨ht.le, htb⟩)
  have hji : j = i := by
    by_contra hn
    exact htU ((mem_otherCarriers T i _).mpr ⟨j, hn, hj⟩)
  subst j
  exact lt_of_lt_of_le ht ((linePoint_mem_iff_le_rayLen (T i) hv hd ht.le).mp hj)

end ConwaySoifer
