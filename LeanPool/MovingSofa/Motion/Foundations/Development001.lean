/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001


public import LeanPool.MovingSofa.Geometry.Foundations.Development003

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Order.IntermediateValue
/-!
# Moving sofa: related mathematical developments

* `Motion.Basic`.
* `Motion.CommonSubset`.
* `Motion.Compactness`.
* `Motion.Rotation`.
* `Motion.AngleLift`.
* `Motion.RotationAngleCalculation`.
* `Motion.SupportingHallways`.
* `Motion.Translation`.
* `Motion.StandardPosition`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Basic
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- A paper motion permits an initial translation and preserves orientation at every time. -/
def IsPaperMotion (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point) : Prop :=
  IsConnected s ∧ IsClosed s ∧ Continuous m ∧
    (∃ q : Point, ∀ p, m 0 p = p + q) ∧
    (∀ t, ∃ a : Real.Angle, ∀ p, m t p = rotationMap a p + m t 0) ∧
    m 0 '' s ⊆ horizontalHallway ∧
    (∀ t, m t '' s ⊆ hallway) ∧ m 1 '' s ⊆ verticalHallway

/-- Movability in the paper's translation-invariant convention. -/
def IsPaperMovingSofa (s : Set Point) : Prop :=
  ∃ m, IsPaperMotion s m

/-- Clockwise rotation angle of a particular admissible lifted motion witness. -/
def HasRotationAngle (s : Set Point) (ω : ℝ) : Prop :=
  ∃ (m : I → Point ≃ᵃⁱ[ℝ] Point), IsPaperMotion s m ∧
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ α 1 = -ω ∧
      ∀ t p, m t p = rotationMap (α t : Real.Angle) p + m t 0

/-- Standard position for a compact moving sofa with the specified rotation angle. -/
def IsStandardPosition (s : Set Point) (ω : ℝ) : Prop :=
  IsCompact s ∧ HasRotationAngle s ω ∧ 0 < ω ∧ ω ≤ Real.pi / 2 ∧
    supportValue s (ω : Real.Angle) = 1 ∧
    supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1

/-- The cap set constructed from all supporting outer quadrants. -/
def capOfSofa (s : Set Point) (ω : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    ⋂ t ∈ Set.Icc 0 ω, (rotatingHallwayParts s (t : Real.Angle)).outerQuadrant

/-- The intersection of supporting hallways used for monotonization. -/
def monotonization (s : Set Point) (ω : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩ ⋂ t ∈ Set.Icc 0 ω, supportingHallway s (t : Real.Angle)

/-- A monotone sofa is the monotonization of a sofa in standard position. -/
def IsMonotoneSofa (s : Set Point) : Prop :=
  ∃ (s₀ : Set Point) (ω : ℝ), IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω

/-- The finite-angle outer approximation to a cap. -/
def angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) : Set Point :=
  (stripParallelogram Θ.angle).1 ∩
    ⋂ t ∈ Θ.directions, (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).outerQuadrant

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Common Subset
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem HasRotationAngle.exists_translated_rotated_hallway {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) {t : ℝ} (ht : t ∈ Set.Icc 0 ω) :
    ∃ v : Point, s ⊆ (fun p ↦ rotationMap (t : Real.Angle) p + v) '' hallway := by
  obtain ⟨m, hm, α, hα, hα0, hα1, hmotion⟩ := hs
  obtain ⟨_, _, _, _, _, _, hhallway, _⟩ := hm
  obtain ⟨τ, hτ⟩ := mem_range_of_exists_le_of_exists_ge (c := -t) hα
    ⟨1, by rw [hα1]; linarith [ht.2]⟩ ⟨0, by rw [hα0]; linarith [ht.1]⟩
  refine ⟨-rotationMap (t : Real.Angle) (m τ 0), ?_⟩
  intro p hp
  refine ⟨m τ p, hhallway τ ⟨p, hp, rfl⟩, ?_⟩
  rw [hmotion τ p, hτ]
  simp only [rotationMap, Real.Angle.coe_neg, map_add,
    ← EuclideanGeometry.o.rotation_symm, LinearIsometryEquiv.apply_symm_apply,
    add_neg_cancel_right]

theorem HasRotationAngle.exists_translated_horizontal_strip {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    ∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).1 := by
  obtain ⟨m, hm, _⟩ := hs
  obtain ⟨_, _, _, ⟨v, hv⟩, _, hstart, _, _⟩ := hm
  refine ⟨-v, ?_⟩
  intro p hp
  have hmem := hstart ⟨p, hp, rfl⟩
  obtain ⟨x, y, hxy, heq⟩ := hmem
  refine ⟨p + v, ?_, by simp⟩
  change 0 ≤ (p + v) 1 ∧ (p + v) 1 ≤ 1
  rw [← hv p, ← heq]
  exact ⟨hxy.2.1, hxy.2.2⟩

theorem HasRotationAngle.exists_translated_vertical_strip {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    ∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).2.2 := by
  obtain ⟨m, hm, α, _, _, hα1, hmotion⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, hend⟩ := hm
  refine ⟨-rotationMap (ω : Real.Angle) (m 1 0), ?_⟩
  intro p hp
  have hmem := hend ⟨p, hp, rfl⟩
  obtain ⟨x, y, hxy, heq⟩ := hmem
  refine ⟨rotationMap (ω : Real.Angle) (m 1 p), ?_, ?_⟩
  · refine ⟨m 1 p, ?_, rfl⟩
    change 0 ≤ (m 1 p) 0 ∧ (m 1 p) 0 ≤ 1
    rw [← heq]
    exact ⟨hxy.1, hxy.2.1⟩
  · rw [hmotion 1 p, hα1]
    simp only [rotationMap, Real.Angle.coe_neg, map_add,
      ← EuclideanGeometry.o.rotation_symm, LinearIsometryEquiv.apply_symm_apply,
      add_neg_cancel_right]

private theorem isBounded_of_oblique_bounds (s : Set Point) (a c d A B : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hy : ∀ p ∈ s, a ≤ p 1 ∧ p 1 ≤ a + 1)
    (hx : ∀ p ∈ s, c * p 0 + d * p 1 ≤ A ∧ -d * p 0 + c * p 1 ≤ B) :
    Bornology.IsBounded s := by
  let l := (c * a - B) / d
  let u := (A - d * a) / c
  let M := |l| + |u|
  let N := |a| + |a + 1|
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + N, ?_⟩
  intro p hp
  obtain ⟨hy0, hy1⟩ := hy p hp
  obtain ⟨hx0, hx1⟩ := hx p hp
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hu : p 0 ≤ u := by
    apply (le_div_iff₀ hc).2
    nlinarith
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN : 0 ≤ N := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hxabs : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self u, abs_nonneg l, abs_nonneg u]
  have hyabs : |p 1| ≤ N := by
    apply abs_le.mpr
    dsimp [N]
    constructor <;> linarith [neg_abs_le a, le_abs_self (a + 1),
      abs_nonneg a, abs_nonneg (a + 1)]
  have hx2 := pow_le_pow_left₀ (abs_nonneg (p 0)) hxabs 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg (p 1)) hyabs 2
  have hnorm := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hnorm hx2 hy2
  nlinarith [mul_nonneg hM hN, norm_nonneg p]

theorem HasRotationAngle.isCompact {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) : IsCompact s := by
  obtain ⟨v, hv⟩ := hs.exists_translated_horizontal_strip
  have ht : ω / 2 ∈ Set.Icc 0 ω := ⟨by linarith [hω.1], by linarith [hω.1]⟩
  obtain ⟨w, hw⟩ := hs.exists_translated_rotated_hallway ht
  have hc : 0 < Real.cos (ω / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hω.1, Real.pi_pos], by linarith [hω.2, Real.pi_pos]⟩
  have hd : 0 < Real.sin (ω / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hω.1]) (by linarith [hω.2, Real.pi_pos])
  have hb : Bornology.IsBounded s := isBounded_of_oblique_bounds s (v 1)
      (Real.cos (ω / 2)) (Real.sin (ω / 2))
      (1 + inner ℝ w (normalVector ((ω / 2 : ℝ) : Real.Angle)))
      (1 + inner ℝ w (tangentVector ((ω / 2 : ℝ) : Real.Angle))) hc hd
      (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := hv hp
        change 0 ≤ q 1 ∧ q 1 ≤ 1 at hq
        change v 1 ≤ q 1 + v 1 ∧ q 1 + v 1 ≤ v 1 + 1
        constructor <;> linarith [hq.1, hq.2])
      (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := hw hp
        have hq01 : q 0 ≤ 1 ∧ q 1 ≤ 1 := by
          rcases hq with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
          · exact ⟨h.1, h.2.2⟩
          · exact ⟨h.2.1, h.2.2⟩
        obtain ⟨hq0, hq1⟩ := hq01
        have hn : inner ℝ (rotationMap ((ω / 2 : ℝ) : Real.Angle) q + w)
            (normalVector ((ω / 2 : ℝ) : Real.Angle)) ≤
              1 + inner ℝ w (normalVector ((ω / 2 : ℝ) : Real.Angle)) := by
          rw [inner_add_left, inner_rotationMap_normalVector]
          linarith
        have ht : inner ℝ (rotationMap ((ω / 2 : ℝ) : Real.Angle) q + w)
            (tangentVector ((ω / 2 : ℝ) : Real.Angle)) ≤
              1 + inner ℝ w (tangentVector ((ω / 2 : ℝ) : Real.Angle)) := by
          rw [inner_add_left, inner_rotationMap_tangentVector]
          linarith
        simpa [normalVector, tangentVector, frame, PiLp.inner_apply,
          Fin.sum_univ_two, Real.inner_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
          mul_comm] using And.intro hn ht)
  obtain ⟨m, hm, _⟩ := hs
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hm.2.1, hb⟩

private theorem width_le_of_forall_mem_Icc {s : Set Point} (hne : s.Nonempty)
    (f : Point → ℝ) (a b : ℝ) (h : ∀ p ∈ s, a ≤ f p ∧ f p ≤ b) :
    sSup (f '' s) - sInf (f '' s) ≤ b - a := by
  have hu : sSup (f '' s) ≤ b := csSup_le (hne.image f) (by
    rintro _ ⟨p, hp, rfl⟩
    exact (h p hp).2)
  have hl : a ≤ sInf (f '' s) := le_csInf (hne.image f) (by
    rintro _ ⟨p, hp, rfl⟩
    exact (h p hp).1)
  linarith

theorem HasRotationAngle.horizontal_width_le {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    sSup ((fun p : Point ↦ p 1) '' s) - sInf ((fun p : Point ↦ p 1) '' s) ≤ 1 := by
  obtain ⟨v, hv⟩ := hs.exists_translated_horizontal_strip
  obtain ⟨m, hm, _⟩ := hs
  have hb := width_le_of_forall_mem_Icc hm.1.nonempty (fun p ↦ p 1) (v 1) (v 1 + 1)
    (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := hv hp
      change 0 ≤ q 1 ∧ q 1 ≤ 1 at hq
      change v 1 ≤ q 1 + v 1 ∧ q 1 + v 1 ≤ v 1 + 1
      constructor <;> linarith [hq.1, hq.2])
  simpa using hb

theorem HasRotationAngle.normal_width_le {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    sSup ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) -
      sInf ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) ≤ 1 := by
  obtain ⟨v, hv⟩ := hs.exists_translated_vertical_strip
  obtain ⟨m, hm, _⟩ := hs
  have hb := width_le_of_forall_mem_Icc hm.1.nonempty
    (fun p ↦ inner ℝ p (normalVector (ω : Real.Angle)))
    (inner ℝ v (normalVector (ω : Real.Angle)))
    (inner ℝ v (normalVector (ω : Real.Angle)) + 1) (by
      intro p hp
      obtain ⟨q, ⟨r, hr, rfl⟩, rfl⟩ := hv hp
      change 0 ≤ r 0 ∧ r 0 ≤ 1 at hr
      rw [inner_add_left, inner_rotationMap_normalVector]
      constructor <;> linarith [hr.1, hr.2])
  simpa using hb

private theorem subset_Icc_of_width_le_of_csSup_eq {s : Set ℝ}
    (hbelow : BddBelow s) (habove : BddAbove s)
    (hwidth : sSup s - sInf s ≤ 1) (hsup : sSup s = 1) : s ⊆ Set.Icc 0 1 := by
  intro x hx
  have hl := csInf_le hbelow hx
  have hu := le_csSup habove hx
  rw [hsup] at hwidth hu
  exact ⟨by linarith, hu⟩

theorem IsStandardPosition.subset_strips {s : Set Point} {ω : ℝ}
    (hs : IsStandardPosition s ω) : s ⊆ (strips ω).1 ∩ (strips ω).2.2 := by
  obtain ⟨hcompact, hmotion, _, _, hnormal, hvertical⟩ := hs
  have hcy : IsCompact ((fun p : Point ↦ p 1) '' s) := hcompact.image (by fun_prop)
  have hcn : IsCompact ((fun p : Point ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) :=
    hcompact.image (by fun_prop)
  have hsupy : sSup ((fun p : Point ↦ p 1) '' s) = 1 := by
    simpa [supportValue, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hvertical
  have hy := subset_Icc_of_width_le_of_csSup_eq hcy.bddBelow hcy.bddAbove
    hmotion.horizontal_width_le hsupy
  have hn := subset_Icc_of_width_le_of_csSup_eq hcn.bddBelow hcn.bddAbove
    hmotion.normal_width_le hnormal
  intro p hp
  refine ⟨hy ⟨p, hp, rfl⟩, ?_⟩
  obtain ⟨q, rfl⟩ := (EuclideanGeometry.o.rotation (ω : Real.Angle)).surjective p
  refine ⟨q, ?_, rfl⟩
  have hb := hn ⟨rotationMap (ω : Real.Angle) q, hp, rfl⟩
  change 0 ≤ q 0 ∧ q 0 ≤ 1
  simpa only [Set.mem_Icc, inner_rotationMap_normalVector] using hb

theorem movingSofa_commonSubset (s : Set Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) :
    IsCompact s ∧
    (∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).1) ∧
    (∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).2.2) ∧
    (∀ t ∈ Set.Icc 0 ω, ∃ v : Point,
      s ⊆ (fun p ↦ rotationMap (t : Real.Angle) p + v) '' hallway) ∧
    (sSup ((fun p : Point ↦ p 1) '' s) - sInf ((fun p : Point ↦ p 1) '' s) ≤ 1) ∧
    (sSup ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) -
      sInf ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) ≤ 1) ∧
    (IsStandardPosition s ω → s ⊆ (strips ω).1 ∩ (strips ω).2.2) := by
  exact ⟨hs.isCompact hω, hs.exists_translated_horizontal_strip,
    hs.exists_translated_vertical_strip, fun _ ht ↦ hs.exists_translated_rotated_hallway ht,
    hs.horizontal_width_le, hs.normal_width_le, fun hstd ↦ hstd.subset_strips⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Compactness
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped unitInterval

namespace MovingSofa

private theorem abs_le_of_affine_coordinate {a b c x y z : ℝ}
    (ha : a ≠ 0) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (heq : z = a * x + b * y + c) :
    |x| ≤ (1 + |b| + |c|) / |a| := by
  have hmul : |a| * |x| ≤ 1 + |b| + |c| := by
    calc
      |a| * |x| = |z - (b * y + c)| := by rw [← abs_mul]; congr 1; linarith
      _ ≤ |z| + |b * y + c| := abs_sub _ _
      _ ≤ 1 + (|b| * |y| + |c|) := by
        grw [hz, abs_add_le, abs_mul]
      _ ≤ 1 + |b| + |c| := by nlinarith [abs_nonneg b]
  exact (le_div_iff₀ (abs_pos.mpr ha)).mpr (by nlinarith)

private theorem norm_le_of_coordinate_bounds {p : Point} {C : ℝ}
    (hC : 0 ≤ C) (hx : |p 0| ≤ C) (hy : |p 1| ≤ 1) : ‖p‖ ≤ C + 1 := by
  have hn : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p
  have hx2 := sq_le_sq₀ (abs_nonneg (p 0)) hC |>.mpr hx
  have hy2 := sq_le_sq₀ (abs_nonneg (p 1)) (by positivity : (0 : ℝ) ≤ 1) |>.mpr hy
  rw [sq_abs] at hx2 hy2
  nlinarith [norm_nonneg p]

private theorem affineIsometry_coordinate (e : Point ≃ᵃⁱ[ℝ] Point) (p : Point) (i : Fin 2) :
    e p i = (e.linearIsometryEquiv !₂[1, 0]) i * p 0 +
      (e.linearIsometryEquiv !₂[0, 1]) i * p 1 + e 0 i := by
  have hp : p = p 0 • !₂[1, 0] + p 1 • !₂[0, 1] := by
    ext j
    fin_cases j <;> simp
  have he := e.map_vadd (0 : Point) p
  change e (p + 0) = e.linearIsometryEquiv p + e 0 at he
  rw [add_zero] at he
  rw [he, hp, map_add, map_smul, map_smul]
  simp [mul_comm]

private theorem isBounded_affine_strip (e : Point ≃ᵃⁱ[ℝ] Point) (i : Fin 2)
    (hi : (e.linearIsometryEquiv !₂[1, 0]) i ≠ 0) :
    Bornology.IsBounded {p : Point | |p 1| ≤ 1 ∧ |e p i| ≤ 1} := by
  let C := (1 + |(e.linearIsometryEquiv !₂[0, 1]) i| + |e 0 i|) /
    |(e.linearIsometryEquiv !₂[1, 0]) i|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C + 1, fun p hp ↦ ?_⟩
  apply norm_le_of_coordinate_bounds hC _ hp.1
  exact abs_le_of_affine_coordinate hi hp.1 hp.2 (affineIsometry_coordinate e p i)

private theorem abs_snd_le_one_of_mem_horizontal {p : Point}
    (hp : p ∈ horizontalHallway) : |p 1| ≤ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hp
  simpa using
    (abs_le.mpr ⟨by linarith [hxy.2.1], hxy.2.2⟩ : |y| ≤ 1)

private theorem abs_fst_le_one_of_mem_vertical {p : Point}
    (hp : p ∈ verticalHallway) : |p 0| ≤ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hp
  simpa using
    (abs_le.mpr ⟨by linarith [hxy.1], hxy.2.1⟩ : |x| ≤ 1)

private theorem isBounded_of_mixed_direction (s : Set Point)
    (m : I → Point ≃ᵃⁱ[ℝ] Point) (h : IsMovingSofa s m) (t : I)
    (h0 : ((m t).linearIsometryEquiv !₂[1, 0]) 0 ≠ 0)
    (h1 : ((m t).linearIsometryEquiv !₂[1, 0]) 1 ≠ 0) : Bornology.IsBounded s := by
  apply ((isBounded_affine_strip (m t) 0 h0).union
    (isBounded_affine_strip (m t) 1 h1)).subset
  intro p hp
  have hy := abs_snd_le_one_of_mem_horizontal (h.initial hp)
  rcases h.subset_hallway t ⟨p, hp, rfl⟩ with hhor | hvert
  · exact Or.inr ⟨hy, abs_snd_le_one_of_mem_horizontal hhor⟩
  · exact Or.inl ⟨hy, abs_fst_le_one_of_mem_vertical hvert⟩

/-- A set admitting a canonical hallway motion is bounded. -/
theorem IsMovingSofa.isBounded {s : Set Point}
    {m : I → Point ≃ᵃⁱ[ℝ] Point} (h : IsMovingSofa s m) : Bornology.IsBounded s := by
  let d : I → Point := fun t ↦ (m t).linearIsometryEquiv !₂[1, 0]
  have hd : Continuous d := by
    have he (t : I) : d t = m t !₂[1, 0] - m t 0 := by
      have he := (m t).map_vadd (0 : Point) !₂[1, 0]
      change m t (!₂[1, 0] + 0) = d t + m t 0 at he
      rw [add_zero] at he
      exact eq_sub_iff_add_eq.mpr he.symm
    simp_rw [show d = (fun t ↦ m t !₂[1, 0] - m t 0) from funext he]
    have hm : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
      continuous_induced_dom.comp h.continuous
    exact (hm.eval_const _).sub (hm.eval_const _)
  have hnorm (t : I) : (d t 0) ^ 2 + (d t 1) ^ 2 = 1 := by
    have hn : ‖d t‖ = 1 := by
      dsimp [d]
      rw [(m t).linearIsometryEquiv.norm_map]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have hs := EuclideanSpace.real_norm_sq_eq (d t)
    simpa [hn, Fin.sum_univ_two] using hs.symm
  by_cases hmix : ∃ t, d t 0 ≠ 0 ∧ d t 1 ≠ 0
  · obtain ⟨t, h0, h1⟩ := hmix
    exact isBounded_of_mixed_direction s m h t h0 h1
  have hmem (t : I) : d t 0 ∈ ({-1, 0, 1} : Set ℝ) := by
    by_cases h0 : d t 0 = 0
    · simp [h0]
    have h1 : d t 1 = 0 := by
      by_contra hn
      exact hmix ⟨t, h0, hn⟩
    have hs : (d t 0) ^ 2 = (1 : ℝ) ^ 2 := by simpa [h1] using hnorm t
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hs) with he | he <;> simp [he]
  have hc : Continuous (fun t ↦ d t 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.comp hd
  have hconst (t : I) : d t 0 = d 0 0 :=
    isPreconnected_univ.constant_of_mapsTo
      (((finite_singleton (1 : ℝ)).insert 0).insert (-1)).isDiscrete
      hc.continuousOn (fun t _ ↦ hmem t) (mem_univ t) (mem_univ 0)
  have hd0 : d 0 0 = 1 := by simp only [d, h.zero]; rfl
  have hdir : ((m 1).linearIsometryEquiv !₂[1, 0]) 0 ≠ 0 := by
    change d 1 0 ≠ 0
    rw [hconst, hd0]
    norm_num
  apply (isBounded_affine_strip (m 1) 0 hdir).subset
  intro p hp
  exact ⟨abs_snd_le_one_of_mem_horizontal (h.initial hp),
    abs_fst_le_one_of_mem_vertical (h.final ⟨p, hp, rfl⟩)⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Rotation
-/

@[expose] public section

noncomputable section

open Set
open scoped unitInterval

namespace MovingSofa

/-- The linear part of a continuous rigid motion varies continuously on each vector. -/
theorem continuous_motion_linear_apply (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (x : Point) :
    Continuous (fun t ↦ (m t).linearIsometryEquiv x) := by
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  have he (t : I) : (m t).linearIsometryEquiv x = m t x - m t 0 := by
    have he := (m t).map_vadd (0 : Point) x
    change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at he
    rw [add_zero] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  simp_rw [he]
  exact (hmc.eval_const x).sub (hmc.eval_const 0)

/-- The linear parts of an identity-starting continuous rigid motion have positive determinant. -/
theorem motion_linear_det_pos (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    0 < LinearMap.det (m t).linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  let L : I → Point →L[ℝ] Point := fun t ↦ (m t).linearIsometryEquiv.toContinuousLinearEquiv
  have hL : Continuous L := continuous_clm_apply.mpr
    (continuous_motion_linear_apply m hm)
  have hdet : Continuous (fun t ↦ (L t).det) := ContinuousLinearMap.continuous_det.comp hL
  have hne (u : I) : (L u).det ≠ 0 := (m u).linearIsometryEquiv.toLinearEquiv.isUnit_det'.ne_zero
  have hL0 : L 0 = ContinuousLinearMap.id ℝ Point := by
    ext x
    simp only [L, hzero]
    rfl
  have hzero' : (L 0).det = 1 := by rw [hL0]; simp [ContinuousLinearMap.det]
  change 0 < (L t).det
  by_contra hneg
  have hle : (L t).det ≤ 0 := le_of_not_gt hneg
  obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hdet ⟨hle, by rw [hzero']; norm_num⟩
  exact hne u hu

/-- Each placement of an identity-starting continuous rigid motion is a rotation and translation. -/
theorem exists_motion_rotation (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    ∃ θ : Real.Angle, ∀ x, m t x = rotationMap θ x + m t 0 := by
  obtain ⟨θ, hθ⟩ := EuclideanGeometry.o.exists_linearIsometryEquiv_eq_of_det_pos
    (motion_linear_det_pos m hm hzero t)
  refine ⟨θ, fun x ↦ ?_⟩
  have he := (m t).map_vadd (0 : Point) x
  change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at he
  simpa only [add_zero, hθ, rotationMap] using he

/-- Translation followed by a varying rotation depends continuously on both parameters. -/
theorem continuous_vaddConst_trans_rotation :
    Continuous (fun q : Real.Angle × Point ↦ ((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv)) := by
  rw [continuous_induced_rng]
  apply ContinuousAffineMap.continuous_rng
  · intro p
    change Continuous (fun q : Real.Angle × Point ↦
      (EuclideanGeometry.o.rotation q.1) (p + q.2))
    simp only [Orientation.rotation_apply]
    exact ((Real.Angle.continuous_cos.comp continuous_fst).smul
      (continuous_const.add continuous_snd)).add
      ((Real.Angle.continuous_sin.comp continuous_fst).smul
        (EuclideanGeometry.o.rightAngleRotation.continuous.comp
          (continuous_const.add continuous_snd)))
  · have heq : (fun q : Real.Angle × Point ↦
        (((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation
          q.1).toAffineIsometryEquiv)).toAffineIsometry.toContinuousAffineMap.contLinear) =
        (fun q : Real.Angle × Point ↦
          q.1.cos • ContinuousLinearMap.id ℝ Point +
          q.1.sin • EuclideanGeometry.o.rightAngleRotation.toContinuousLinearMap) := by
      funext q
      apply ContinuousLinearMap.ext
      intro p
      change (EuclideanGeometry.o.rotation q.1) p = _
      exact EuclideanGeometry.o.rotation_apply q.1 p
    change Continuous (fun q : Real.Angle × Point ↦
      (((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation
          q.1).toAffineIsometryEquiv)).toAffineIsometry.toContinuousAffineMap.contLinear)
    rw [heq]
    exact ((Real.Angle.continuous_cos.comp continuous_fst).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp continuous_fst).smul continuous_const)

/-- A continuously varying rotation about the origin followed by a continuously varying
translation is a continuous family of rigid motions. -/
theorem continuous_rotation_trans_vaddConst {X : Type*} [TopologicalSpace X]
    {θ : X → Real.Angle} {c : X → Point} (hθ : Continuous θ) (hc : Continuous c) :
    Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ (c x))) := by
  rw [continuous_induced_rng]
  apply ContinuousAffineMap.continuous_rng
  · intro p
    change Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)) p + c x)
    simp only [Orientation.rotation_apply]
    exact (((Real.Angle.continuous_cos.comp hθ).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp hθ).smul continuous_const)).add hc
  · have heq : (fun x ↦
        ((EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
          (AffineIsometryEquiv.vaddConst ℝ
            (c x))).toAffineIsometry.toContinuousAffineMap.contLinear) =
        (fun x ↦ (θ x).cos • ContinuousLinearMap.id ℝ Point +
            (θ x).sin • EuclideanGeometry.o.rightAngleRotation.toContinuousLinearMap) := by
      funext x
      apply ContinuousLinearMap.ext
      intro p
      change (EuclideanGeometry.o.rotation (θ x)) p = _
      exact EuclideanGeometry.o.rotation_apply (θ x) p
    change Continuous (fun x ↦
      ((EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
        (AffineIsometryEquiv.vaddConst ℝ
          (c x))).toAffineIsometry.toContinuousAffineMap.contLinear)
    rw [heq]
    exact ((Real.Angle.continuous_cos.comp hθ).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp hθ).smul continuous_const)

/-- Planar area is invariant under rotation about the origin, with no measurability
hypothesis on the set. -/
theorem area_image_rotationMap (α : Real.Angle) (S : Set Point) :
    ClassicalResults.area (rotationMap α '' S) = ClassicalResults.area S := by
  have himg : rotationMap α '' S = (EuclideanGeometry.o.rotation α).symm ⁻¹' S := by
    ext p
    simp only [rotationMap, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨_, h, (EuclideanGeometry.o.rotation α).apply_symm_apply p⟩
  change (MeasureTheory.volume (rotationMap α '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [himg]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving (EuclideanGeometry.o.rotation α).symm
    (E := Point) (F := Point)).measure_preimage_emb
    ((EuclideanGeometry.o.rotation α).symm.toHomeomorph.measurableEmbedding) S

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Angle Lift
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- An identity-starting continuous rigid motion has a normalized continuous real angle lift. -/
theorem exists_continuous_motion_angle_lift (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) :
    ∃ (α : I → ℝ) (p : I → Point), Continuous α ∧ Continuous p ∧
      α 0 = 0 ∧ p 0 = 0 ∧ ∀ t x, m t x = rotationMap (α t : Real.Angle) x + p t := by
  let e : Point := !₂[1, 0]
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun p : Point ↦ p 0) h
    norm_num [e] at this
  let θ : I → Real.Angle := fun t ↦ EuclideanGeometry.o.oangle e
    ((m t).linearIsometryEquiv e)
  have hθ : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : (m t).linearIsometryEquiv e ≠ 0 := by
      exact (m t).linearIsometryEquiv.map_ne_zero_iff.mpr he
    have ha : ContinuousAt (fun z : Point × Point ↦ EuclideanGeometry.o.oangle z.1 z.2)
        (e, (m t).linearIsometryEquiv e) :=
      EuclideanGeometry.o.continuousAt_oangle he hne
    have hp : ContinuousAt (fun u : I ↦ (e, (m u).linearIsometryEquiv e)) t :=
      continuousAt_const.prodMk (continuous_motion_linear_apply m hm e).continuousAt
    exact ContinuousAt.comp (f := fun u : I ↦ (e, (m u).linearIsometryEquiv e))
      (x := t) ha hp
  have hθ0 : θ 0 = 0 := by
    have h0 : (m 0).linearIsometryEquiv e = e := by rw [hzero]; rfl
    simp [θ, h0]
  have hrot (t : I) : (m t).linearIsometryEquiv = EuclideanGeometry.o.rotation (θ t) := by
    obtain ⟨u, hu⟩ := EuclideanGeometry.o.exists_linearIsometryEquiv_eq_of_det_pos
      (motion_linear_det_pos m hm hzero t)
    have ht : θ t = u := by
      dsimp [θ]
      rw [hu, EuclideanGeometry.o.oangle_rotation_self_right he]
    rw [ht, hu]
  obtain ⟨α, hα, hα0, hαθ⟩ := Real.Angle.exists_continuous_lift_zero θ hθ hθ0
  have hp : Continuous (fun t ↦ m t (0 : Point)) := by
    have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
      continuous_induced_dom.comp hm
    exact hmc.eval_const 0
  refine ⟨α, fun t ↦ m t 0, hα, hp, hα0, ?_, ?_⟩
  · change m 0 0 = 0
    rw [hzero]
    rfl
  · intro t x
    have hx := (m t).map_vadd (0 : Point) x
    change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at hx
    simpa only [add_zero, hrot t, hαθ t, rotationMap] using hx

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Rotation Angle Calculation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The rotation-angle interval from `arccos(5/11)` up to, but excluding, `π/2`. -/
abbrev RotationCalculationAngle := Set.Ico (Real.arccos (5 / 11 : ℝ)) (Real.pi / 2)

/-- The piecewise lower cutoff on the auxiliary distance used in the rotation estimate. -/
def rotationCalculationMinimum (ω : RotationCalculationAngle) : ℝ :=
  if ω.val < Real.arctan (11 / 5 : ℝ) then 5 / 4 else 11 / 10

/-- Auxiliary radii and points determined by an admissible rotation angle and distance. -/
def rotationCalculationValues (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val)) :
    ℝ × ℝ × Point × Point :=
  let r := 1 - d.val * (Real.cos ω.val / Real.sin ω.val)
  let g := Real.sqrt (1 - r ^ 2)
  let o := (stripParallelogram ω.val).2.2
  (r, g, o - tangentVector 0 + d.val • normalVector 0, o - g • normalVector 0)

theorem rotationCalculation_convex (d : ℝ) (hd : 1 ≤ d) :
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2))
      (fun t ↦ (1 - d * (Real.cos t / Real.sin t)) ^ 2) ∧
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2))
      (fun t ↦ Real.cos t ^ 2) := by
  let D := Set.Icc (Real.pi / 4) (Real.pi / 2)
  have hsin (t : ℝ) (ht : t ∈ D) : Real.sin t ≠ 0 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < Real.pi / 4) ht.1
    have htpi : t < Real.pi := lt_of_le_of_lt ht.2 (by linarith)
    exact (Real.sin_pos_of_pos_of_lt_pi ht0 htpi).ne'
  have hfirst (t : ℝ) (ht : t ∈ D) : HasDerivAt
      (fun s ↦ (1 - d * (Real.cos s / Real.sin s)) ^ 2)
      (2 * d * (1 - d * (Real.cos t / Real.sin t)) / Real.sin t ^ 2) t := by
    have htrig : -(Real.sin t * Real.sin t) - Real.cos t * Real.cos t = -1 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    convert (((hasDerivAt_const t 1).sub
      ((hasDerivAt_const t d).mul ((Real.hasDerivAt_cos t).div
        (Real.hasDerivAt_sin t) (hsin t ht)))).pow 2) using 1
    all_goals simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply]
    all_goals norm_num
    all_goals simp only [htrig]
    all_goals field_simp [hsin t ht]
  have hsecond (t : ℝ) (ht : t ∈ D) : HasDerivAt
      (fun s ↦ 2 * d * (1 - d * (Real.cos s / Real.sin s)) / Real.sin s ^ 2)
      (2 * d / Real.sin t ^ 4 *
        (d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t)) t := by
    have hs := hsin t ht
    have htrig : -(Real.sin t * Real.sin t) - Real.cos t * Real.cos t = -1 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    convert (((hasDerivAt_const t (2 * d)).mul
      ((hasDerivAt_const t 1).sub
        ((hasDerivAt_const t d).mul ((Real.hasDerivAt_cos t).div
          (Real.hasDerivAt_sin t) hs)))).div
      ((Real.hasDerivAt_sin t).pow 2) (pow_ne_zero 2 hs)) using 1
    all_goals simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
    all_goals norm_num
    all_goals simp only [htrig]
    all_goals field_simp [hs]
    all_goals ring
  constructor
  · apply convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun t ↦ 2 * d * (1 - d * (Real.cos t / Real.sin t)) / Real.sin t ^ 2)
      (f'' := fun t ↦ 2 * d / Real.sin t ^ 4 *
        (d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t)) (convex_Icc _ _)
    · fun_prop
    · intro t ht
      exact (hfirst t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact (hsecond t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have hc : 2 * Real.sin t * Real.cos t ≤ 1 := by
        nlinarith [sq_nonneg (Real.sin t - Real.cos t), Real.sin_sq_add_cos_sq t]
      have : 0 ≤ d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t := by
        nlinarith [sq_nonneg (Real.cos t)]
      positivity
  · apply convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun t ↦ -2 * Real.sin t * Real.cos t)
      (f'' := fun t ↦ -2 * Real.cos (2 * t)) (convex_Icc _ _)
    · fun_prop
    · intro t ht
      convert ((Real.hasDerivAt_cos t).mul (Real.hasDerivAt_cos t)).hasDerivWithinAt using 1 <;>
        first | funext s; simp [Pi.mul_apply]; ring | ring
    · intro t ht
      convert (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).const_mul (-2))
        |>.hasDerivWithinAt using 1 <;>
          first | funext s; simp [Pi.mul_apply]; ring |
            rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq t]; ring
    · intro t ht
      have htD := interior_subset ht
      change t ∈ Set.Icc (Real.pi / 4) (Real.pi / 2) at htD
      have h1 : Real.pi / 2 ≤ 2 * t := by
        calc
          Real.pi / 2 = 2 * (Real.pi / 4) := by ring
          _ ≤ 2 * t := mul_le_mul_of_nonneg_left htD.1 (by norm_num)
      have h2 : 2 * t ≤ Real.pi + Real.pi / 2 := by
        calc
          2 * t ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left htD.2 (by norm_num)
          _ ≤ Real.pi + Real.pi / 2 := by linarith [Real.pi_pos]
      exact mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2)

private def rotationBound (d t : ℝ) : ℝ :=
  (1 - d * (Real.cos t / Real.sin t)) ^ 2 + 4 * Real.cos t ^ 2

private theorem rotationBound_convex (d : ℝ) (hd : 1 ≤ d) :
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2)) (rotationBound d) := by
  obtain ⟨h₁, h₂⟩ := rotationCalculation_convex d hd
  exact h₁.add (h₂.smul (by norm_num : (0 : ℝ) ≤ 4))

private theorem rotationBound_arccos :
    rotationBound (5 / 4) (Real.arccos (5 / 11)) < 1 := by
  have hs : Real.sin (Real.arccos (5 / 11)) = Real.sqrt 96 / 11 := by
    rw [Real.sin_arccos]
    norm_num
  have hsq : Real.sqrt 96 ^ 2 = 96 := Real.sq_sqrt (by norm_num)
  have hlo : 97 / 10 < Real.sqrt 96 := by
    nlinarith [Real.sqrt_nonneg 96]
  have hhi : Real.sqrt 96 < 49 / 5 := by
    nlinarith [Real.sqrt_nonneg 96]
  unfold rotationBound
  rw [Real.cos_arccos (by norm_num) (by norm_num), hs]
  have hpos : 0 < Real.sqrt 96 := by positivity
  field_simp
  nlinarith

private theorem rotationBound_arctan_left :
    rotationBound (5 / 4) (Real.arctan (11 / 5)) < 1 := by
  unfold rotationBound
  rw [Real.cos_arctan, Real.sin_arctan]
  norm_num
  have hs : Real.sqrt (146 : ℝ) ^ 2 = 146 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (146 : ℝ) := by positivity
  field_simp
  nlinarith

private theorem rotationBound_arctan_right :
    rotationBound (11 / 10) (Real.arctan (11 / 5)) < 1 := by
  unfold rotationBound
  rw [Real.cos_arctan, Real.sin_arctan]
  norm_num
  have hs : Real.sqrt (146 : ℝ) ^ 2 = 146 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (146 : ℝ) := by positivity
  field_simp
  nlinarith

private theorem rotationBound_pi_div_two (d : ℝ) : rotationBound d (Real.pi / 2) = 1 := by
  simp [rotationBound]

/-- The three landmark angles of the rotation calculation are strictly ordered:
`π / 4 < arccos (5 / 11) < arctan (11 / 5) < π / 2`. -/
theorem rotationCalculation_angle_bounds :
    Real.pi / 4 < Real.arccos (5 / 11 : ℝ) ∧
    Real.arccos (5 / 11 : ℝ) < Real.arctan (11 / 5 : ℝ) ∧
    Real.arctan (11 / 5 : ℝ) < Real.pi / 2 := by
  have ha : Real.arccos (5 / 11 : ℝ) = Real.arctan (Real.sqrt 96 / 5) := by
    rw [Real.arccos_eq_arctan (by norm_num)]
    norm_num
    ring
  have hs : Real.sqrt 96 ^ 2 = 96 := Real.sq_sqrt (by norm_num)
  have hpos := Real.sqrt_nonneg 96
  refine ⟨?_, ?_, Real.arctan_lt_pi_div_two _⟩
  · rw [ha, ← Real.arctan_one]
    apply Real.arctan_strictMono
    nlinarith
  · rw [ha]
    apply Real.arctan_strictMono
    nlinarith

private theorem rotationBound_lt_one (ω : RotationCalculationAngle) :
    rotationBound (rotationCalculationMinimum ω) ω.val < 1 := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hdom₁ : Set.Icc (Real.arccos (5 / 11 : ℝ)) (Real.arctan (11 / 5 : ℝ)) ⊆
      Set.Icc (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    exact ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hdom₂ : Set.Icc (Real.arctan (11 / 5 : ℝ)) (Real.pi / 2) ⊆
      Set.Icc (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    exact ⟨(ha.le.trans hab.le).trans ht.1, ht.2⟩
  unfold rotationCalculationMinimum
  split_ifs with h
  · exact ConvexOn.lt_on_Ico_of_lt_of_le
      ((rotationBound_convex (5 / 4) (by norm_num)).subset hdom₁ (convex_Icc _ _))
      rotationBound_arccos rotationBound_arctan_left.le ω.property.1 h
  · exact ConvexOn.lt_on_Ico_of_lt_of_le
      ((rotationBound_convex (11 / 10) (by norm_num)).subset hdom₂ (convex_Icc _ _))
      rotationBound_arctan_right (rotationBound_pi_div_two _).le (le_of_not_gt h) ω.property.2

private theorem rotationCalculation_sin_bound (ω : RotationCalculationAngle) :
    1 < rotationCalculationMinimum ω * Real.sin ω.val := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hsinmono := Real.strictMonoOn_sin.monotoneOn
  unfold rotationCalculationMinimum
  split_ifs with h
  · have hs := hsinmono
      (show Real.arccos (5 / 11 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
      (show ω.val ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [ω.property.1, ω.property.2, Real.pi_pos]) ω.property.1
    rw [Real.sin_arccos] at hs
    norm_num at hs
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 96)
    have hp := Real.sqrt_nonneg 96
    have : 44 / 5 < Real.sqrt 96 := by nlinarith
    nlinarith
  · have hs := hsinmono
      (show Real.arctan (11 / 5 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
      (show ω.val ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [ω.property.1, ω.property.2, Real.pi_pos]) (le_of_not_gt h)
    rw [Real.sin_arctan] at hs
    norm_num at hs
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 146)
    have hp : 0 < Real.sqrt 146 := by positivity
    have hupper : Real.sqrt 146 < 121 / 10 := by nlinarith
    have hbase : 10 / 11 < 11 / Real.sqrt 146 := (lt_div_iff₀ hp).2 (by nlinarith)
    nlinarith

private theorem rotationCalculation_g_bound (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val))
    (hr : 0 ≤ (rotationCalculationValues ω d).1) :
    2 * Real.cos ω.val < (rotationCalculationValues ω d).2.1 := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hw0 : 0 < ω.val := by linarith [ω.property.1, Real.pi_pos]
  have hsin : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hcos : 0 < Real.cos ω.val := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    ω.property.2⟩
  have hcot : 0 ≤ Real.cos ω.val / Real.sin ω.val := le_of_lt (div_pos hcos hsin)
  have hmin : 0 ≤ rotationCalculationMinimum ω := by
    unfold rotationCalculationMinimum
    split_ifs <;> norm_num
  have hdd := mul_le_mul_of_nonneg_right d.property.1 hcot
  change 0 ≤ 1 - d.val * (Real.cos ω.val / Real.sin ω.val) at hr
  have hf := rotationBound_lt_one ω
  unfold rotationBound at hf
  have hrle : 1 - d.val * (Real.cos ω.val / Real.sin ω.val) ≤
      1 - rotationCalculationMinimum ω * (Real.cos ω.val / Real.sin ω.val) := by linarith
  have hr0 : 0 ≤ 1 - rotationCalculationMinimum ω * (Real.cos ω.val / Real.sin ω.val) := by linarith
  have hsquares := sq_le_sq₀ hr hr0 |>.2 hrle
  have hrad : 0 ≤ 1 - (1 - d.val * (Real.cos ω.val / Real.sin ω.val)) ^ 2 := by nlinarith
    [sq_nonneg (Real.cos ω.val)]
  have hsqrt := Real.sq_sqrt hrad
  have hnonneg := Real.sqrt_nonneg (1 - (1 - d.val * (Real.cos ω.val / Real.sin ω.val)) ^ 2)
  change 2 * Real.cos ω.val < Real.sqrt _
  nlinarith

theorem rotationCalculation_inequalities (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val))
    (hr : 0 ≤ (rotationCalculationValues ω d).1) :
    1 < inner ℝ
      ((rotationCalculationValues ω d).2.2.1 -
        ((stripParallelogram ω.val).2.2 - tangentVector 0))
      (normalVector ((Real.pi / 2 - ω.val : ℝ) : Real.Angle)) ∧
    1 < inner ℝ
      ((rotationCalculationValues ω d).2.2.2 -
        ((stripParallelogram ω.val).2.2 - normalVector (ω.val : Real.Angle)))
      (tangentVector ((Real.pi / 2 - ω.val : ℝ) : Real.Angle)) := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hw0 : 0 < ω.val := by linarith [ω.property.1, Real.pi_pos]
  have hsin : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hcos : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hg := rotationCalculation_g_bound ω d hr
  have hd := mul_le_mul_of_nonneg_right d.property.1 hsin.le
  have hds := rotationCalculation_sin_bound ω
  constructor
  · simp [rotationCalculationValues, inner_smul_left,
      normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
    linarith
  · have hvec : (rotationCalculationValues ω d).2.2.2 -
        ((stripParallelogram ω.val).2.2 - normalVector (ω.val : Real.Angle)) =
        normalVector (ω.val : Real.Angle) - (rotationCalculationValues ω d).2.1 • normalVector 0
          := by
      simp only [rotationCalculationValues]
      abel
    rw [hvec]
    simp only [inner_sub_left, inner_smul_left]
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
    have hm := mul_lt_mul_of_pos_right hg hcos
    nlinarith [Real.sin_sq_add_cos_sq ω.val]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Supporting Hallways
-/

@[expose] public section

noncomputable section
open Set
open scoped unitInterval
namespace MovingSofa

/-- The supporting placement regarded as an affine isometry equivalence. -/
def supportingPlacementEquiv (s : Set Point) (t : Real.Angle) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (EuclideanGeometry.o.rotation t).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ
      ((supportValue s t - 1) • normalVector t +
       (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t))

theorem supportingPlacementEquiv_apply (s : Set Point) (t : Real.Angle) (p : Point) :
    supportingPlacementEquiv s t p = supportingPlacement s t p := by
  simp [supportingPlacementEquiv, supportingPlacement, rotationMap, add_assoc]

private def supportCorner (s : Set Point) (t : Real.Angle) : Point :=
  (supportValue s t - 1) • normalVector t +
    (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t

private theorem continuous_supportCorner_real (s : Set Point)
    (hs : s.Nonempty) (hc : IsCompact s) :
    Continuous (fun t : ℝ ↦ supportCorner s (t : Real.Angle)) := by
  have hh := (compactSet_support_continuity s s hs hc hs hc).2.2.1
  have hn := continuous_normalVector_real
  have hv : Continuous (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
    have h := hn.comp (continuous_id.add (continuous_const (y := Real.pi / 2)))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, Real.Angle.coe_add,
      normalVector_add_pi_div_two] using h
  exact (((hh.comp Real.Angle.continuous_coe).sub continuous_const).smul hn).add
    (((hh.comp (Real.Angle.continuous_coe.add continuous_const)).sub continuous_const).smul hv)

private theorem supportingPlacementEquiv_symm_apply (s : Set Point) (t : Real.Angle)
    (p : Point) :
    (supportingPlacementEquiv s t).symm p =
      ((AffineIsometryEquiv.vaddConst ℝ (-supportCorner s t)).trans
        (EuclideanGeometry.o.rotation (-t)).toAffineIsometryEquiv) p := by
  change (EuclideanGeometry.o.rotation t).symm (p - supportCorner s t) =
    (EuclideanGeometry.o.rotation (-t)) (p + -supportCorner s t)
  simp only [Orientation.rotation_symm_apply, Orientation.rotation_apply,
    Real.Angle.cos_neg, Real.Angle.sin_neg, neg_smul, sub_eq_add_neg]

private theorem continuous_inverse_supportingPlacement (s : Set Point)
    (hs : s.Nonempty) (hc : IsCompact s) :
    Continuous (fun t : ℝ ↦ (supportingPlacementEquiv s (t : Real.Angle)).symm) := by
  have h := continuous_vaddConst_trans_rotation.comp
    (Real.Angle.continuous_coe.neg.prodMk (continuous_supportCorner_real s hs hc).neg)
  apply h.congr
  intro t
  apply AffineIsometryEquiv.ext
  intro p
  exact (supportingPlacementEquiv_symm_apply s (t : Real.Angle) p).symm

private theorem inverse_supportingPlacement_coordinates (s : Set Point)
    (t : Real.Angle) (p : Point) :
    ((supportingPlacementEquiv s t).symm p) 0 =
      inner ℝ p (normalVector t) - supportValue s t + 1 ∧
    ((supportingPlacementEquiv s t).symm p) 1 =
      inner ℝ p (tangentVector t) -
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) + 1 := by
  have hn := inner_supportingPlacement_normalVector s t ((supportingPlacementEquiv s t).symm p)
  have ht := inner_supportingPlacement_tangentVector s t ((supportingPlacementEquiv s t).symm p)
  rw [← supportingPlacementEquiv_apply, AffineIsometryEquiv.apply_symm_apply] at hn ht
  constructor <;> linarith

private theorem inverse_supportingPlacement_mem_hallway (s : Set Point)
    (t : Real.Angle) {p : Point} (hp : p ∈ supportingHallway s t) :
    (supportingPlacementEquiv s t).symm p ∈ hallway := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← supportingPlacementEquiv_apply, AffineIsometryEquiv.symm_apply_apply]
  exact hq

private theorem hallway_coordinates_le {p : Point} (hp : p ∈ hallway) :
    p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  rcases hp with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
  · exact ⟨h.1, h.2.2⟩
  · exact ⟨h.2.1, h.2.2⟩

/-- A closed connected subset of the supporting-hallway intersection inherits its
clockwise hallway motion from the reference compact set. -/
theorem hasRotationAngle_of_subset_supportingHallways (s S : Set Point) (ω : ℝ)
    (hsne : s.Nonempty) (hscompact : IsCompact s) (hω : 0 ≤ ω)
    (hsω : supportValue s (ω : Real.Angle) = 1)
    (hsπ : supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1)
    (hSconn : IsConnected S) (hSclosed : IsClosed S)
    (hSsub : S ⊆ monotonization s ω) : HasRotationAngle S ω := by
  let m : I → Point ≃ᵃⁱ[ℝ] Point := fun r ↦
    (supportingPlacementEquiv s ((ω * (r : ℝ) : ℝ) : Real.Angle)).symm
  have hθ (r : I) : ω * (r : ℝ) ∈ Icc (0 : ℝ) ω := by
    exact ⟨mul_nonneg hω r.2.1,
      (mul_le_mul_of_nonneg_left r.2.2 hω).trans_eq (mul_one ω)⟩
  have hall (r : I) : m r '' S ⊆ hallway := by
    rintro p ⟨q, hq, rfl⟩
    apply inverse_supportingPlacement_mem_hallway
    exact mem_iInter.mp (mem_iInter.mp (hSsub hq).2 (ω * (r : ℝ))) (hθ r)
  have hrot (r : I) (p : Point) :
      m r p = rotationMap ((-ω * (r : ℝ) : ℝ) : Real.Angle) p + m r 0 := by
    dsimp [m]
    rw [supportingPlacementEquiv_symm_apply, supportingPlacementEquiv_symm_apply]
    change rotationMap (-((ω * (r : ℝ) : ℝ) : Real.Angle))
      (p + -supportCorner s _) = _
    rw [show ((-ω * (r : ℝ) : ℝ) : Real.Angle) =
      -((ω * (r : ℝ) : ℝ) : Real.Angle) by rw [neg_mul, Real.Angle.coe_neg]]
    simp [rotationMap, map_add]
  refine ⟨m, ?_, (fun r ↦ -ω * (r : ℝ)), by fun_prop, by simp, by simp, hrot⟩
  refine ⟨hSconn,
    hSclosed,
    (continuous_inverse_supportingPlacement s hsne hscompact).comp
      (continuous_const.mul continuous_subtype_val), ?_, ?_, ?_, hall, ?_⟩
  · refine ⟨-supportCorner s 0, ?_⟩
    intro p
    simp [m, supportingPlacementEquiv_symm_apply,
      Orientation.rotation_zero]
  · intro r
    exact ⟨((-ω * (r : ℝ) : ℝ) : Real.Angle), hrot r⟩
  · rintro p ⟨q, hq, rfl⟩
    apply mem_horizontalHallway_of_coordinates
    · exact (hallway_coordinates_le (hall 0 ⟨q, hq, rfl⟩)).1
    · have hc := (inverse_supportingPlacement_coordinates s 0 q).2
      have hqP := (mem_stripParallelogram_iff ω q).mp (hSsub hq).1
      have hy : (m 0 q) 1 = q 1 := by
        simpa [m, hsπ, tangentVector, frame, PiLp.inner_apply,
          Fin.sum_univ_two] using hc
      rw [hy]
      exact hqP.1
  · rintro p ⟨q, hq, rfl⟩
    apply mem_verticalHallway_of_coordinates
    · have hc := (inverse_supportingPlacement_coordinates s (ω : Real.Angle) q).1
      have hqP := (mem_stripParallelogram_iff ω q).mp (hSsub hq).1
      have hx : (m 1 q) 0 = inner ℝ q (normalVector (ω : Real.Angle)) := by
        simpa [m, hsω] using hc
      rw [hx]
      exact hqP.2
    · exact (hallway_coordinates_le (hall 1 ⟨q, hq, rfl⟩)).2

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Translation
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private def translatedMotion (v : Point) (m : I → Point ≃ᵃⁱ[ℝ] Point) (t : I) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (AffineIsometryEquiv.vaddConst ℝ (-v)).trans (m t)

private theorem continuous_translatedMotion (v : Point)
    (m : I → Point ≃ᵃⁱ[ℝ] Point) (hm : Continuous m) :
    Continuous (translatedMotion v m) := by
  rw [continuous_induced_rng]
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  apply (ContinuousAffineMap.continuous_comp_right
    (AffineIsometryEquiv.vaddConst ℝ (-v)).toAffineIsometry.toContinuousAffineMap).comp
      hmc |>.congr
  intro t
  rfl

/-- Translating a sofa preserves each admitted rotation angle. -/
theorem hasRotationAngle_image_add (s : Set Point) (v : Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) :
    HasRotationAngle ((fun p ↦ p + v) '' s) ω := by
  obtain ⟨m, hm, α, hα, hα0, hα1, hmotion⟩ := hs
  refine ⟨translatedMotion v m, ?_, α, hα, hα0, hα1, ?_⟩
  · obtain ⟨hconn, hclosed, hcont, ⟨q, hq⟩, hrot, hini, hall, hfinal⟩ := hm
    refine ⟨hconn.image _ (by fun_prop), ?_, continuous_translatedMotion v m hcont,
      ⟨q - v, ?_⟩, ?_, ?_, ?_, ?_⟩
    · change IsClosed ((AffineIsometryEquiv.vaddConst ℝ v) '' s)
      exact (AffineIsometryEquiv.vaddConst ℝ v).toHomeomorph.isClosedMap s hclosed
    · intro p
      change m 0 (p - v) = p + (q - v)
      rw [hq]
      abel
    · intro t
      obtain ⟨a, ha⟩ := hrot t
      refine ⟨a, fun p ↦ ?_⟩
      change m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p) =
        rotationMap a p + m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)
      rw [ha ((AffineIsometryEquiv.vaddConst ℝ (-v)) p),
        ha ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)]
      have hvp : (AffineIsometryEquiv.vaddConst ℝ (-v)) p = p - v := by rfl
      have hv0 : (AffineIsometryEquiv.vaddConst ℝ (-v)) 0 = -v := by simp
      rw [hvp, hv0]
      simp only [rotationMap, map_sub, map_neg]
      abel
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hini ⟨y, hy, by simp [translatedMotion]⟩
    · intro t
      rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact hall t ⟨y, hy, by simp [translatedMotion]⟩
    · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact hfinal ⟨y, hy, by simp [translatedMotion]⟩
  · intro t p
    change m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p) =
      rotationMap (α t : Real.Angle) p +
        m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)
    rw [hmotion t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p),
      hmotion t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)]
    have hvp : (AffineIsometryEquiv.vaddConst ℝ (-v)) p = p - v := by rfl
    have hv0 : (AffineIsometryEquiv.vaddConst ℝ (-v)) 0 = -v := by simp
    rw [hvp, hv0]
    simp only [rotationMap, map_sub, map_neg]
    abel

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Standard Position
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem exists_standardPosition_translation (s : Set Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) :
    (∃ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω) ∧
    (∀ v w : Point,
      IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      IsStandardPosition ((fun p ↦ p + w) '' s) ω →
      (ω < Real.pi / 2 → v = w) ∧ (ω = Real.pi / 2 → v 1 = w 1)) ∧
    (∀ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      ω = Real.pi / 2 → ∀ a : ℝ,
        IsStandardPosition ((fun p ↦ p + (v + a • normalVector 0)) '' s) ω) ∧
    (∀ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      (fun p ↦ p + v) '' s ⊆ (stripParallelogram ω).1) := by
  have hc : IsCompact s := hs.isCompact hω
  have hne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs
    exact hm.1.nonempty
  have hadd (v : Point) (t : Real.Angle) :
      supportValue ((fun p ↦ p + v) '' s) t =
        supportValue s t + inner ℝ v (normalVector t) :=
    supportValue_image_add_of_isCompact hc hne v t
  have hcos (hlt : ω < Real.pi / 2) : Real.cos ω ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hω.1, Real.pi_pos], hlt⟩).ne'
  constructor
  · rcases lt_or_eq_of_le hω.2 with hlt | rfl
    · let v : Point := !₂[
          (1 - supportValue s (ω : Real.Angle) -
            (1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)) * Real.sin ω) /
              Real.cos ω,
          1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)]
      refine ⟨v, hc.image (by fun_prop), hasRotationAngle_image_add s v ω hs,
        hω.1, hω.2, ?_, ?_⟩
      · rw [hadd]
        simp only [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
          Real.Angle.cos_coe, Real.Angle.sin_coe, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        field_simp [hcos hlt]
        ring
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    · let v : Point := !₂[0,
          1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)]
      refine ⟨v, hc.image (by fun_prop),
        hasRotationAngle_image_add s v (Real.pi / 2) hs, hω.1, hω.2, ?_, ?_⟩
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  · constructor
    · intro v w hv hw
      have hvω := hv.2.2.2.2.1
      have hvπ := hv.2.2.2.2.2
      have hwω := hw.2.2.2.2.1
      have hwπ := hw.2.2.2.2.2
      rw [hadd] at hvω hvπ hwω hwπ
      constructor
      · intro hlt
        have hy : v 1 = w 1 := by
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ hwπ
          linarith
        apply PiLp.ext
        intro i
        fin_cases i
        · have hcω := hcos hlt
          change v 0 = w 0
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvω hwω
          rw [hy] at hvω
          apply mul_left_cancel₀ hcω
          linarith [hvω, hwω]
        · exact hy
      · intro _
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ hwπ
        linarith
    · constructor
      · intro v hv hωeq a
        subst ω
        have hvπ := hv.2.2.2.2.2
        rw [hadd] at hvπ
        refine ⟨hc.image (by fun_prop),
          hasRotationAngle_image_add s (v + a • normalVector 0) (Real.pi / 2) hs,
          hω.1, hω.2, ?_, ?_⟩
        · rw [hadd]
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ ⊢
          linarith
        · rw [hadd]
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ ⊢
          linarith
      · intro v hv
        exact hv.subset_strips

end MovingSofa

end

end

end
