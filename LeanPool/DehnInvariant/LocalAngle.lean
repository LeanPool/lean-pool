/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.Polytope
public import LeanPool.DehnInvariant.TensorInvariant
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026), part B: the Dehn invariant of a
set, defined
from the set alone (no list of edges is given as input).

At a point `x` of `P` the directions that stay in `P` form a cone `tcone P x`. The directions `v`
with both
`v` and `-v` in the cone span `linSpace`. The point is an *edge point* when that span is a line
`K`; the
dihedral angle there is the angle of the cone inside the plane perpendicular to `K`, measured as
2π × (area of the cone inside the unit disc) / (area of the unit disc).  `dehnSet P` adds, over
all angle classes
`θ` in ℝ/ℚπ, (the length of the set of edge points with angle class `θ`) ⊗ `θ`; length is the
1-dimensional
Hausdorff measure.

Proved here: the angle is exactly additive when the cone is cut by a plane through the edge
(`wedgeAngle_split`), a cone that contains a full line of the perpendicular plane has angle 0, π
or 2π
(`wedgeAngle_mem_ratPi_of_line`), and the resulting rule for the angle class at a point
(`theta_cut`).
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The cone of directions that stay in `P` near the point `x` of `P` (empty when `x ∉ P`). -/
def tcone (P : Set E) (x : E) : Set E := {v | x ∈ P ∧ ∃ t : ℝ, 0 < t ∧ x + t • v ∈ P}

/-- The span of the directions `v` of a cone for which `-v` is in the cone too. -/
def linSpace (T : Set E) : Submodule ℝ E := Submodule.span ℝ {v | v ∈ T ∧ -v ∈ T}

/-- The part of the cone `T` inside the open unit disc of the space perpendicular to `K`. -/
def wedgeSet (T : Set E) (K : Submodule ℝ E) : Set Kᗮ := {w | (w : E) ∈ T ∧ ‖w‖ < 1}

/-- The angle of the cone `T` around the line `K`: 2π × area(T ∩ unit disc of Kᗮ) / area(unit disc
of Kᗮ). -/
noncomputable def wedgeAngle (T : Set E) (K : Submodule ℝ E) : ℝ :=
  2 * Real.pi * ((volume (wedgeSet T K)).toReal / (volume (Metric.ball (0 : Kᗮ) 1)).toReal)

/-- The angle class in ℝ/ℚπ of a cone: its angle around `linSpace` when that is a line, else 0. -/
noncomputable def theta (T : Set E) : Angle :=
  if finrank ℝ (linSpace T) = 1 then Submodule.Quotient.mk (wedgeAngle T (linSpace T)) else 0

/-- The dihedral angle class of the set `P` at the point `x` (0 unless `x` is an edge point). -/
noncomputable def edgeAngle (P : Set E) (x : E) : Angle := theta (tcone P x)

/-- **The Dehn invariant of a set**, in ℝ ⊗[ℚ] (ℝ/ℚπ): Σ over angle classes θ of length{edge
points with class θ} ⊗ θ. -/
noncomputable def dehnSet (P : Set E) : DehnSpace :=
  ∑ᶠ θ : Angle, (μH[1] {x | edgeAngle P x = θ}).toReal ⊗ₜ[ℚ] θ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linSpace_eq_of {T : Set E} {M : Submodule ℝ E} (h : ∀ v, (v ∈ T ∧ -v ∈ T) ↔ v ∈ M) :
    linSpace T = M := by
  unfold linSpace
  have h1 : {v | v ∈ T ∧ -v ∈ T} = (M : Set E) := Set.ext h
  rw [h1, Submodule.span_eq]

lemma theta_empty : theta (∅ : Set E) = 0 := by
  have h : linSpace (∅ : Set E) = ⊥ := by simp [linSpace]
  unfold theta
  rw [h, ite_eq_right]
  simp

lemma edgeAngle_of_notMem {P : Set E} {x : E} (hx : x ∉ P) : edgeAngle P x = 0 := by
  have h : tcone P x = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]; intro v hv; exact hx hv.1
  unfold edgeAngle; rw [h, theta_empty]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma wedgeSet_subset_ball (T : Set E) (K : Submodule ℝ E) : wedgeSet T K ⊆ Metric.ball (0 : Kᗮ)
    1 := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right]; exact hw.2

lemma wedge_vol_ne_top (T : Set E) (K : Submodule ℝ E) : volume (wedgeSet T K) ≠ ⊤ :=
  ((measure_mono (wedgeSet_subset_ball T K)).trans_lt measure_ball_lt_top).ne

/-- **Angles add.** A plane through the line `K` (normal `c ⟂ K`) cuts the cone in two; the two
angles add up
to the angle of the cone, exactly. -/
lemma wedgeAngle_split (T : Set E) (K : Submodule ℝ E) {c : E} (hc : c ≠ 0) (hcK : c ∈ Kᗮ) :
    wedgeAngle T K = wedgeAngle (T ∩ {v | ⟪c, v⟫ ≤ 0}) K + wedgeAngle (T ∩ {v | ⟪-c, v⟫ ≤ 0})
        K := by
  unfold wedgeAngle
  set S := wedgeSet T K with hS
  let Hle : Set Kᗮ := {w | ⟪c, (w : E)⟫ ≤ 0}
  have hHle : MeasurableSet Hle := (isClosed_le (by fun_prop) continuous_const).measurableSet
  let N : Submodule ℝ Kᗮ := (ℝ ∙ (⟨c, hcK⟩ : Kᗮ))ᗮ
  have hN : N ≠ ⊤ := by
    intro h
    have h1 : (⟨c, hcK⟩ : Kᗮ) ∈ N := by rw [h]; trivial
    have h2 : ⟪(⟨c, hcK⟩ : Kᗮ), (⟨c, hcK⟩ : Kᗮ)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 h1
    have h3 : (⟨c, hcK⟩ : Kᗮ) = 0 := inner_self_eq_zero.1 h2
    exact hc (congrArg Subtype.val h3)
  have hN0 : volume (N : Set Kᗮ) = 0 := Measure.addHaar_submodule volume N hN
  have e1 : wedgeSet (T ∩ {v | ⟪c, v⟫ ≤ 0}) K = S ∩ Hle := by
    ext w; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have h1 := measure_inter_add_sdiff (μ := volume) S hHle
  have e2 : volume (wedgeSet (T ∩ {v | ⟪-c, v⟫ ≤ 0}) K) = volume (S \ Hle) := by
    apply le_antisymm
    · calc volume (wedgeSet (T ∩ {v | ⟪-c, v⟫ ≤ 0}) K) ≤ volume ((S \ Hle) ∪ (N : Set Kᗮ)) := by
            apply measure_mono
            rintro w ⟨⟨hw1, hw2⟩, hw3⟩
            have hw2' : ⟪-c, (w : E)⟫ ≤ 0 := hw2
            rw [inner_neg_left] at hw2'
            by_cases h0 : ⟪c, (w : E)⟫ = 0
            · right
              exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 h0
            · left
              refine ⟨⟨hw1, hw3⟩, fun hle => h0 (le_antisymm hle (by linarith))⟩
        _ ≤ volume (S \ Hle) + volume (N : Set Kᗮ) := measure_union_le _ _
        _ = volume (S \ Hle) := by rw [hN0, add_zero]
    · apply measure_mono
      rintro w ⟨⟨hw1, hw3⟩, hw2⟩
      have hw2' : ¬ ⟪c, (w : E)⟫ ≤ 0 := hw2
      refine ⟨⟨hw1, ?_⟩, hw3⟩
      change ⟪-c, (w : E)⟫ ≤ 0
      rw [inner_neg_left]; linarith
  have f1 : volume (S ∩ Hle) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (wedge_vol_ne_top T K).lt_top).ne
  have f2 : volume (S \ Hle) ≠ ⊤ :=
    ((measure_mono sdiff_subset).trans_lt (wedge_vol_ne_top T K).lt_top).ne
  rw [e1, e2, ← h1, ENNReal.toReal_add f1 f2]
  ring

/-- **A cone that contains a whole line of the perpendicular plane has angle 0, π or 2π.**
(A point inside a face, or inside the solid: the new edge made there by a cut gets two angles that
sum to π or 2π.) -/
lemma wedgeAngle_mem_ratPi_of_line [Fact (finrank ℝ E = 3)] {T : Set E} {K : Submodule ℝ E}
    (hK : finrank ℝ K = 1)
    (hadd : ∀ v ∈ T, ∀ w ∈ T, v + w ∈ T) (hsmul : ∀ v ∈ T, ∀ s : ℝ, 0 < s → s • v ∈ T)
    {w0 : E} (hw0 : w0 ≠ 0) (hw0K : w0 ∈ Kᗮ) (hw0T : w0 ∈ T) (hw0T' : -w0 ∈ T) :
    wedgeAngle T K ∈ ratPi := by
  classical
  rw [mem_ratPi_iff]
  unfold wedgeAngle
  have hE : finrank ℝ E = 3 := Fact.out
  have hV : finrank ℝ Kᗮ = 1 + 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal K
    omega
  have : Fact (finrank ℝ Kᗮ = 1 + 1) := ⟨hV⟩
  set W0 : Kᗮ := ⟨w0, hw0K⟩ with hW0def
  have hW0 : W0 ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
  have hf1 : finrank ℝ (ℝ ∙ W0)ᗮ = 1 := Submodule.finrank_orthogonal_span_singleton hW0
  obtain ⟨n, hnmem, hn0⟩ : ∃ n ∈ (ℝ ∙ W0)ᗮ, n ≠ 0 := by
    apply (Submodule.ne_bot_iff _).1
    intro h
    rw [h] at hf1
    simp at hf1
  have hnW : ⟪W0, n⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hnmem
  have hf2 : finrank ℝ (ℝ ∙ n)ᗮ = 1 := Submodule.finrank_orthogonal_span_singleton hn0
  have hW0n : W0 ∈ (ℝ ∙ n)ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by rw [real_inner_comm]; exact hnW)
  have hline : ∀ v : Kᗮ, ⟪n, v⟫ = 0 → ∃ t : ℝ, t • W0 = v := by
    intro v hv
    have hv' : v ∈ (ℝ ∙ n)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.2 hv
    have hne : (⟨W0, hW0n⟩ : (ℝ ∙ n)ᗮ) ≠ 0 := fun h => hW0 (congrArg Subtype.val h)
    obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_ne_zero' _ hne).1 hf2 ⟨v, hv'⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  have h0T : (0 : E) ∈ T := by
    have := hadd _ hw0T _ hw0T'
    rwa [add_neg_cancel] at this
  have hlineT : ∀ t : ℝ, t • w0 ∈ T := by
    intro t
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have := hsmul _ hw0T' (-t) (by linarith)
      rwa [smul_neg, neg_smul, neg_neg] at this
    · rw [ht, zero_smul]; exact h0T
    · exact hsmul _ hw0T t ht
  have claimA : ∀ v0 : Kᗮ, (v0 : E) ∈ T → ∀ v : Kᗮ, 0 < ⟪n, v⟫ / ⟪n, v0⟫ → (v : E) ∈ T := by
    intro v0 hv0 v hpos
    have hne : ⟪n, v0⟫ ≠ 0 := by
      intro h; rw [h, div_zero] at hpos; exact lt_irrefl _ hpos
    obtain ⟨t, ht⟩ := hline (v - (⟪n, v⟫ / ⟪n, v0⟫) • v0) (by
      rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hne, sub_self])
    have h1 : v = (⟪n, v⟫ / ⟪n, v0⟫) • v0 + t • W0 := by rw [ht]; abel
    have hv : (v : E) = (⟪n, v⟫ / ⟪n, v0⟫) • (v0 : E) + t • w0 := by
      calc (v : E) = (((⟪n, v⟫ / ⟪n, v0⟫) • v0 + t • W0 : Kᗮ) : E) := congrArg Subtype.val h1
        _ = (⟪n, v⟫ / ⟪n, v0⟫) • (v0 : E) + t • w0 := rfl
    rw [hv]
    exact hadd _ (hsmul _ hv0 _ hpos) _ (hlineT t)
  set S := wedgeSet T K with hS
  set B : Set Kᗮ := Metric.ball (0 : Kᗮ) 1 with hB
  let Hp : Set Kᗮ := {v | 0 < ⟪n, v⟫}
  let Hn : Set Kᗮ := {v | ⟪n, v⟫ < 0}
  have hHp : MeasurableSet Hp := (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hHn : MeasurableSet Hn := (isOpen_lt (by fun_prop) continuous_const).measurableSet
  let N : Submodule ℝ Kᗮ := (ℝ ∙ n)ᗮ
  have hN : volume (N : Set Kᗮ) = 0 := by
    apply Measure.addHaar_submodule
    intro h
    have h1 : n ∈ N := by rw [h]; trivial
    have h2 : ⟪n, n⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 h1
    exact hn0 (inner_self_eq_zero.1 h2)
  have hsplit : ∀ X : Set Kᗮ, volume X = volume (X ∩ Hp) + volume (X ∩ Hn) := by
    intro X
    have h1 := measure_inter_add_sdiff (μ := volume) X hHp
    have h2 := measure_inter_add_sdiff (μ := volume) (X \ Hp) hHn
    have h3 : volume ((X \ Hp) \ Hn) = 0 := by
      apply measure_mono_null _ hN
      intro v hv
      have a1 : ¬ 0 < ⟪n, v⟫ := hv.1.2
      have a2 : ¬ ⟪n, v⟫ < 0 := hv.2
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.2
        (le_antisymm (not_lt.1 a1) (not_lt.1 a2))
    have h4 : (X \ Hp) ∩ Hn = X ∩ Hn := by
      ext v; constructor
      · rintro ⟨⟨hx, -⟩, hn⟩; exact ⟨hx, hn⟩
      · rintro ⟨hx, hn⟩; exact ⟨⟨hx, fun hp => lt_asymm (show 0 < ⟪n, v⟫ from hp) (show ⟪n,
          v⟫ < 0 from hn)⟩, hn⟩
    rw [← h1, ← h2, h3, add_zero, h4]
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hsym : volume (B ∩ Hn) = volume (B ∩ Hp) := by
    have hmp := (LinearIsometryEquiv.neg ℝ (E := Kᗮ)).measurePreserving
    have h1 := hmp.measure_preimage (hBm.inter hHp).nullMeasurableSet
    rw [← h1]
    congr 1
    ext v
    have hb : (-v ∈ B) ↔ v ∈ B := by
      rw [hB, Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right, norm_neg]
    constructor
    · rintro ⟨h2, h3⟩
      refine ⟨hb.2 h2, ?_⟩
      change 0 < ⟪n, -v⟫
      rw [inner_neg_right]; have h3' : ⟪n, v⟫ < 0 := h3; linarith
    · rintro ⟨h2, h3⟩
      have h3' : 0 < ⟪n, -v⟫ := h3
      rw [inner_neg_right] at h3'
      exact ⟨hb.1 h2, show ⟪n, v⟫ < 0 by linarith⟩
  have hSB : S ⊆ B := wedgeSet_subset_ball T K
  have dp : S ∩ Hp = B ∩ Hp ∨ S ∩ Hp = ∅ := by
    by_cases h : ∃ v0 : Kᗮ, (v0 : E) ∈ T ∧ 0 < ⟪n, v0⟫
    · obtain ⟨v0, hv0, hpos⟩ := h
      left
      ext v; constructor
      · rintro ⟨hs, hp⟩; exact ⟨hSB hs, hp⟩
      · rintro ⟨hb, hp⟩
        refine ⟨⟨claimA v0 hv0 v (div_pos hp hpos), ?_⟩, hp⟩
        rw [hB, Metric.mem_ball, dist_zero_right] at hb; exact hb
    · right
      rw [Set.eq_empty_iff_forall_notMem]
      rintro v ⟨hs, hp⟩
      exact h ⟨v, hs.1, hp⟩
  have dn : S ∩ Hn = B ∩ Hn ∨ S ∩ Hn = ∅ := by
    by_cases h : ∃ v0 : Kᗮ, (v0 : E) ∈ T ∧ ⟪n, v0⟫ < 0
    · obtain ⟨v0, hv0, hneg⟩ := h
      left
      ext v; constructor
      · rintro ⟨hs, hp⟩; exact ⟨hSB hs, hp⟩
      · rintro ⟨hb, hp⟩
        refine ⟨⟨claimA v0 hv0 v (div_pos_of_neg_of_neg hp hneg), ?_⟩, hp⟩
        rw [hB, Metric.mem_ball, dist_zero_right] at hb; exact hb
    · right
      rw [Set.eq_empty_iff_forall_notMem]
      rintro v ⟨hs, hp⟩
      exact h ⟨v, hs.1, hp⟩
  have hBpos : 0 < volume B := Metric.measure_ball_pos volume _ one_pos
  have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hBsplit := hsplit B
  rw [hsym] at hBsplit
  have hSsplit := hsplit S
  have hfin : volume (B ∩ Hp) ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt hBfin.lt_top).ne
  have hfinn : volume (B ∩ Hn) ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt hBfin.lt_top).ne
  have hm : (volume B).toReal = (volume (B ∩ Hp)).toReal + (volume (B ∩ Hp)).toReal := by
    rw [← ENNReal.toReal_add hfin hfin, ← hBsplit]
  have hmpos : 0 < (volume B).toReal := ENNReal.toReal_pos hBpos.ne' hBfin
  have hSr : (volume S).toReal = (volume (S ∩ Hp)).toReal + (volume (S ∩ Hn)).toReal := by
    rw [← ENNReal.toReal_add, ← hSsplit]
    · exact ((measure_mono (inter_subset_left.trans hSB)).trans_lt hBfin.lt_top).ne
    · exact ((measure_mono (inter_subset_left.trans hSB)).trans_lt hBfin.lt_top).ne
  have hx : (volume (S ∩ Hp)).toReal = (volume (B ∩ Hp)).toReal ∨ (volume (S ∩ Hp)).toReal = 0 := by
    rcases dp with e | e
    · left; rw [e]
    · right; rw [e]; simp
  have hy : (volume (S ∩ Hn)).toReal = (volume (B ∩ Hp)).toReal ∨ (volume (S ∩ Hn)).toReal = 0 := by
    rcases dn with e | e
    · left; rw [e, hsym]
    · right; rw [e]; simp
  rw [hSr, hm]
  rw [hm] at hmpos
  generalize (volume (B ∩ Hp)).toReal = h at *
  have hh : 0 < h := by linarith
  rcases hx with ex | ex <;> rcases hy with ey | ey <;> rw [ex, ey]
  · refine ⟨2, ?_⟩
    rw [div_self (by positivity)]; push_cast; ring
  · refine ⟨1, ?_⟩
    have : (h + 0) / (h + h) = 1 / 2 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]; ring
    rw [this]; push_cast; ring
  · refine ⟨1, ?_⟩
    have : (0 + h) / (h + h) = 1 / 2 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]; ring
    rw [this]; push_cast; ring
  · refine ⟨0, ?_⟩
    simp

/-- **The angle class under a cut through the point.** `T` is the cone at a point, `L` its
lineality space;
cut the cone by the plane with normal `c` through the point. Unless the point is on an edge that
crosses the
plane (`L` a line not in the plane), the angle class is the sum of the angle classes of the two
parts. -/
lemma theta_cut [Fact (finrank ℝ E = 3)] {T : Set E} {L : Submodule ℝ E}
    (hL : ∀ v, (v ∈ T ∧ -v ∈ T) ↔ v ∈ L)
    (hadd : ∀ v ∈ T, ∀ w ∈ T, v + w ∈ T) (hsmul : ∀ v ∈ T, ∀ s : ℝ, 0 < s → s • v ∈ T)
    {c : E} (hc : c ≠ 0) (hexc : ¬ (finrank ℝ L = 1 ∧ ¬ L ≤ (ℝ ∙ c)ᗮ)) :
    theta T = theta (T ∩ {v | ⟪c, v⟫ ≤ 0}) + theta (T ∩ {v | ⟪-c, v⟫ ≤ 0}) := by
  have hLT : linSpace T = L := linSpace_eq_of hL
  have hLp : linSpace (T ∩ {v | ⟪c, v⟫ ≤ 0}) = L ⊓ (ℝ ∙ c)ᗮ := by
    apply linSpace_eq_of
    intro v
    rw [Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right, ← hL v]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have h2' : ⟪c, v⟫ ≤ 0 := h2
      have h4' : ⟪c, -v⟫ ≤ 0 := h4
      rw [inner_neg_right] at h4'
      exact ⟨⟨h1, h3⟩, by linarith⟩
    · rintro ⟨⟨h1, h3⟩, h0⟩
      refine ⟨⟨h1, ?_⟩, ⟨h3, ?_⟩⟩
      · change ⟪c, v⟫ ≤ 0
        rw [h0]
      · change ⟪c, -v⟫ ≤ 0
        rw [inner_neg_right, h0, neg_zero]
  have hLm : linSpace (T ∩ {v | ⟪-c, v⟫ ≤ 0}) = L ⊓ (ℝ ∙ c)ᗮ := by
    apply linSpace_eq_of
    intro v
    rw [Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right, ← hL v]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have h2' : ⟪-c, v⟫ ≤ 0 := h2
      have h4' : ⟪-c, -v⟫ ≤ 0 := h4
      rw [inner_neg_left] at h2'
      rw [inner_neg_left, inner_neg_right, neg_neg] at h4'
      exact ⟨⟨h1, h3⟩, by linarith⟩
    · rintro ⟨⟨h1, h3⟩, h0⟩
      refine ⟨⟨h1, ?_⟩, ⟨h3, ?_⟩⟩
      · change ⟪-c, v⟫ ≤ 0
        rw [inner_neg_left, h0, neg_zero]
      · change ⟪-c, -v⟫ ≤ 0
        rw [inner_neg_left, inner_neg_right, neg_neg, h0]
  unfold theta
  rw [hLT, hLp, hLm]
  by_cases hsub : L ≤ (ℝ ∙ c)ᗮ
  · rw [inf_eq_left.2 hsub]
    by_cases h1 : finrank ℝ L = 1
    · simp only [ite_eq_left h1]
      rw [← Submodule.Quotient.mk_add]
      have hcL : c ∈ Lᗮ := by
        rw [Submodule.mem_orthogonal']
        intro u hu
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hsub hu)
      rw [wedgeAngle_split T L hc hcL]
    · simp only [ite_eq_right h1, add_zero]
  · have h1 : finrank ℝ L ≠ 1 := fun h => hexc ⟨h, hsub⟩
    rw [ite_eq_right h1]
    by_cases h2 : finrank ℝ ↥(L ⊓ (ℝ ∙ c)ᗮ) = 1
    · simp only [ite_eq_left h2]
      rw [← Submodule.Quotient.mk_add]
      symm
      rw [Submodule.Quotient.mk_eq_zero]
      have hcL : c ∈ (L ⊓ (ℝ ∙ c)ᗮ)ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro u hu
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hu.2
      rw [← wedgeAngle_split T _ hc hcL]
      obtain ⟨v1, hv1L, hv1c⟩ : ∃ v1 ∈ L, ⟪c, v1⟫ ≠ 0 := by
        by_contra hno
        push Not at hno
        exact hsub fun v hv => Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hno v hv)
      obtain ⟨u, hu0, hspan⟩ := finrank_eq_one_iff'.1 h2
      have huL : (u : E) ∈ L := u.2.1
      have huc : ⟪c, (u : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 u.2.2
      have hu0' : (u : E) ≠ 0 := fun h => hu0 (Subtype.ext h)
      have huu : ⟪(u : E), (u : E)⟫ ≠ 0 := fun h => hu0' (inner_self_eq_zero.1 h)
      set w0 : E := v1 - (⟪(u : E), v1⟫ / ⟪(u : E), (u : E)⟫) • (u : E) with hw0def
      have hw0L : w0 ∈ L := L.sub_mem hv1L (L.smul_mem _ huL)
      have hw0c : ⟪c, w0⟫ = ⟪c, v1⟫ := by
        rw [hw0def, inner_sub_right, inner_smul_right, huc, mul_zero, sub_zero]
      have hw0 : w0 ≠ 0 := by
        intro h; rw [h, inner_zero_right] at hw0c; exact hv1c hw0c.symm
      have hw0K : w0 ∈ (L ⊓ (ℝ ∙ c)ᗮ)ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro z hz
        obtain ⟨t, ht⟩ := hspan ⟨z, hz⟩
        have hz' : z = t • (u : E) := (congrArg Subtype.val ht).symm
        rw [hz', inner_smul_right, hw0def, inner_sub_left, inner_smul_left]
        simp only [conj_trivial]
        rw [div_mul_cancel₀ _ huu, real_inner_comm, sub_self, mul_zero]
      have hw0T := (hL w0).2 hw0L
      exact wedgeAngle_mem_ratPi_of_line h2 hadd hsmul hw0 hw0K hw0T.1 hw0T.2
    · simp only [ite_eq_right h2, add_zero]

end DehnCanon.Library
