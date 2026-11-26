/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import Mathlib.Topology.Subpath
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Reading an entry curve as two paths

The definition on XII page 243 first follows the given curve and then
traverses a spoke. Splitting at its joining time gives the affine approach
path and an injective path whose range is the spoke closure. These lemmas
supply that parametrization step without choosing a different trace.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The affine parameter of a unit-interval path lies in its real interval. -/
theorem affine_approach_parameter_mem_Icc {h c : ℝ} (hh : h ≤ c) (t : unitInterval) :
    h + t.val * (c - h) ∈ Icc h c := by
  have hpos := sub_nonneg.mpr hh
  refine ⟨le_add_of_nonneg_right (mul_nonneg t.property.1 hpos), ?_⟩
  have hle := mul_le_of_le_one_left hpos t.property.2
  linarith

/-- Before the final time the affine parameter lies strictly before the endpoint. -/
theorem affine_approach_parameter_mem_Ico {h c : ℝ} (hh : h < c)
    {t : unitInterval} (ht : t < 1) : h + t.val * (c - h) ∈ Ico h c := by
  refine ⟨(affine_approach_parameter_mem_Icc hh.le t).1, ?_⟩
  have hlt := mul_lt_of_lt_one_left (sub_pos.mpr hh) ht
  linarith

/-- An approach in a region with a terminal boundary vertex gives a path in their union. -/
theorem exists_affine_approach_path {S : Type*} [TopologicalSpace S] {r : Set S} {v : S}
    {f : ℝ → S} {h c : ℝ} (hh : h < c) (hf : ContinuousOn f (Icc h c)) (hfc : f c = v)
    (hinside : ∀ q ∈ Ico h c, f q ∈ r) :
    ∃ F : Path (⟨f h, Or.inl (hinside h ⟨le_rfl, hh⟩)⟩ : (r ∪ {v} : Set S))
      ⟨v, Or.inr (mem_singleton v)⟩,
      (∀ t : unitInterval, (F t).val = f (h + t.val * (c - h))) ∧
      ∀ t : unitInterval, t < 1 → (F t).val ∈ r := by
  let m : unitInterval → ℝ := fun t => h + t.val * (c - h)
  have hm : Continuous m := by fun_prop
  have hmI : ∀ t, m t ∈ Icc h c := affine_approach_parameter_mem_Icc hh.le
  have hmR : ∀ t : unitInterval, t < 1 → f (m t) ∈ r :=
    fun t ht => hinside _ (affine_approach_parameter_mem_Ico hh ht)
  have hmem : ∀ t : unitInterval, f (m t) ∈ r ∪ {v} := by
    intro t
    rcases eq_or_lt_of_le t.2.2 with ht | ht
    · have ht1 : t = 1 := Subtype.ext ht
      exact Or.inr (by simp [m, ht1, hfc])
    · exact Or.inl (hmR t ht)
  let F : Path (⟨f h, Or.inl (hinside h ⟨le_rfl, hh⟩)⟩ : (r ∪ {v} : Set S))
      ⟨v, Or.inr (mem_singleton v)⟩ := {
    toFun := fun t => ⟨f (m t), hmem t⟩
    continuous_toFun := (hf.comp_continuous hm hmI).subtype_mk _
    source' := Subtype.ext (by simp [m])
    target' := Subtype.ext (by simpa only [m, Icc.coe_one, one_mul, add_sub_cancel] using hfc) }
  exact ⟨F, fun _ => rfl, hmR⟩

/-- A terminal subpath has the same affine parametrization starting at the chosen time. -/
theorem affine_approach_subpath_apply {S X : Type*} [TopologicalSpace X] {a b : X}
    (F : Path a b) {j : X → S} {f : ℝ → S} {h₀ c : ℝ}
    (hF : ∀ t : unitInterval, j (F t) = f (h₀ + t.val * (c - h₀))) (s t : unitInterval) :
    let h := h₀ + s.val * (c - h₀)
    j ((F.subpath s 1) t) = f (h + t.val * (c - h)) := by
  change j (F (Icc.convexComb s 1 t)) = _
  rw [hF]
  congr 1
  simp only [Icc.coe_convexComb, Icc.coe_one]
  ring

private theorem convexComb_tail_image_Ioo {s : unitInterval} (hs : s < 1) :
    Icc.convexComb s 1 '' Ioo (0 : unitInterval) 1 = Ioo s 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    change s < Icc.convexComb s 1 t ∧ Icc.convexComb s 1 t < 1
    have hs' : (s : ℝ) < 1 := hs
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : (t : ℝ) < 1 := ht.2
    constructor
    · change (s : ℝ) < (1 - t.val) * s.val + t.val * 1
      nlinarith
    · change (1 - t.val) * s.val + t.val * 1 < 1
      nlinarith
  · intro hu
    have hs' : (s : ℝ) < 1 := hs
    have hu0 : (s : ℝ) < u := hu.1
    have hu1 : (u : ℝ) < 1 := hu.2
    let x : ℝ := ((u : ℝ) - s) / (1 - s)
    have hx0 : 0 < x := div_pos (sub_pos.mpr hu0) (sub_pos.mpr hs')
    have hx1 : x < 1 := (div_lt_one (sub_pos.mpr hs')).mpr (by linarith)
    refine ⟨⟨x, hx0.le, hx1.le⟩, ⟨hx0, hx1⟩, ?_⟩
    apply Subtype.ext
    change (1 - x) * s + x * 1 = u
    dsimp only [x]
    field_simp [ne_of_gt (sub_pos.mpr hs')]
    ring

/-- Splitting at the entry curve's joining time gives the prescribed
approach, now parametrized on the full unit interval. -/
theorem entry_subpath_prefix {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    (j : X → S) {a b : X} (P : Path a b) (ξ : Curve S)
    (hP : ∀ t, j (P t) = ξ t) {f : ℝ → S} {h c : ℝ} {s : unitInterval}
    (hs : 0 < s)
    (hfirst : ∀ t : unitInterval, t ≤ s → ξ t = f (h + t.val / s.val * (c - h))) :
    ∀ t : unitInterval, j ((P.subpath 0 s) t) = f (h + t.val * (c - h)) := by
  intro t
  change j (P (Icc.convexComb 0 s t)) = _
  rw [hP, hfirst]
  · congr 1
    have hs' : (s : ℝ) ≠ 0 := ne_of_gt hs
    change h + ((1 - t.val) * 0 + t.val * s.val) / s.val * (c - h) = _
    field_simp [hs']
    ring
  · change (1 - t.val) * 0 + t.val * s.val ≤ s.val
    simp only [mul_zero, zero_add]
    exact mul_le_of_le_one_left s.property.1 t.property.2

/-- The interior of the terminal subpath is exactly the edge in the
entry-curve definition. -/
theorem entry_subpath_interior {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    (j : X → S) {a b : X} (P : Path a b) (ξ : Curve S)
    (hP : ∀ t, j (P t) = ξ t) {s : unitInterval} (hs : s < 1)
    {e : Set S} (himage : ξ '' Ioo s 1 = e) :
    (fun t => j ((P.subpath s 1) t)) '' Ioo (0 : unitInterval) 1 = e := by
  calc
    _ = ξ '' (Icc.convexComb s 1 '' Ioo (0 : unitInterval) 1) := by
      rw [Set.image_image]
      congr 1
      funext t
      exact hP _
    _ = e := by rw [convexComb_tail_image_Ioo hs, himage]

/-- The range of a continuous path is the closure of its interior image.
The endpoint images follow by continuity, and compactness closes the range. -/
theorem path_range_eq_closure_interior {S : Type*} [TopologicalSpace S] [T2Space S]
    {a b : S} (P : Path a b) :
    range P = closure (P '' Ioo (0 : unitInterval) 1) := by
  apply subset_antisymm
  · have hpre : IsClosed {t : unitInterval | P t ∈ closure (P '' Ioo (0 : unitInterval) 1)} :=
      isClosed_closure.preimage P.continuous
    have hsub : Ioo (0 : unitInterval) 1 ⊆ {t | P t ∈ closure (P '' Ioo (0 : unitInterval) 1)} :=
      fun t ht => subset_closure (mem_image_of_mem P ht)
    have hcl := closure_minimal hsub hpre
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)] at hcl
    rintro x ⟨t, rfl⟩
    exact hcl ⟨t.property.1, t.property.2⟩
  · exact closure_minimal (image_subset_range _ _) (isCompact_range P.continuous).isClosed

/-- An injective interior extends to an injective parametrization of an
arc when its two distinct endpoint values are outside the interior image. -/
theorem injective_of_injective_interior {S : Type*} (q : unitInterval → S)
    (hinj : InjOn q (Ioo (0 : unitInterval) 1))
    (h0 : q 0 ∉ q '' Ioo (0 : unitInterval) 1)
    (h1 : q 1 ∉ q '' Ioo (0 : unitInterval) 1) (hne : q 0 ≠ q 1) :
    Function.Injective q := by
  have eq0 : ∀ t, q t = q 0 → t = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · exact ht0
    by_cases ht1 : t = 1
    · exact (hne (ht1 ▸ ht).symm).elim
    exact (h0 ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
      lt_of_le_of_ne t.property.2 ht1⟩, ht⟩).elim
  have eq1 : ∀ t, q t = q 1 → t = 1 := by
    intro t ht
    by_cases ht1 : t = 1
    · exact ht1
    by_cases ht0 : t = 0
    · exact (hne (ht0 ▸ ht)).elim
    exact (h1 ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
      lt_of_le_of_ne t.property.2 ht1⟩, ht⟩).elim
  intro s t hst
  by_cases hs0 : s = 0
  · subst s
    exact (eq0 t hst.symm).symm
  by_cases hs1 : s = 1
  · subst s
    exact (eq1 t hst.symm).symm
  by_cases ht0 : t = 0
  · subst t
    exact eq0 s hst
  by_cases ht1 : t = 1
  · subst t
    exact eq1 s hst
  exact hinj ⟨unitInterval.pos_iff_ne_zero.mpr hs0, lt_of_le_of_ne s.property.2 hs1⟩
    ⟨unitInterval.pos_iff_ne_zero.mpr ht0, lt_of_le_of_ne t.property.2 ht1⟩ hst

/-- The terminal piece of an entry curve is an injective spoke path,
including its two endpoints. -/
theorem entry_terminal_injective {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    (j : X → S) {a b : X} (P : Path a b) (ξ : Curve S)
    (hP : ∀ t, j (P t) = ξ t) {s : unitInterval} (hs : s < 1)
    {e : Set S} (himage : ξ '' Ioo s 1 = e) (hinj : InjOn ξ (Ioo s 1))
    (h0 : j (P s) ∉ e) (h1 : j (P 1) ∉ e) (hne : j (P s) ≠ j (P 1)) :
    Function.Injective (fun t => j ((P.subpath s 1) t)) := by
  let q : unitInterval → S := fun t => j ((P.subpath s 1) t)
  have hqi : q '' Ioo (0 : unitInterval) 1 = e := entry_subpath_interior j P ξ hP hs himage
  apply injective_of_injective_interior q
  · intro u hu v hv heq
    have hmem : ∀ t ∈ Ioo (0 : unitInterval) 1, Icc.convexComb s 1 t ∈ Ioo s 1 := by
      intro t ht
      rw [← convexComb_tail_image_Ioo hs]
      exact mem_image_of_mem _ ht
    have hξeq : ξ (Icc.convexComb s 1 u) = ξ (Icc.convexComb s 1 v) := by
      rw [← hP, ← hP]
      exact heq
    have hparams := congrArg Subtype.val (hinj (hmem u hu) (hmem v hv) hξeq)
    simp only [Icc.coe_convexComb, Icc.coe_one] at hparams
    apply Subtype.ext
    have hs' : (s : ℝ) < 1 := hs
    nlinarith
  · rw [hqi]
    change j ((P.subpath s 1) 0) ∉ e
    rw [(P.subpath s 1).source]
    exact h0
  · rw [hqi]
    change j ((P.subpath s 1) 1) ∉ e
    rw [(P.subpath s 1).target]
    exact h1
  · change j ((P.subpath s 1) 0) ≠ j ((P.subpath s 1) 1)
    rw [(P.subpath s 1).source, (P.subpath s 1).target]
    exact hne

end GraphMinor.GM12
