/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryReduction
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonTriangleConstruction
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryRestoration
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonalSeparation
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Topology.Order.Compact

-- [TABLET NODE: P3861T1RealPolygonDomains]

/-!
# P3861T1RealPolygonDomains

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RealPolygonGeometry

open Set AffineMap

private theorem angle :
    (by
      classical
      exact
        ∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), (a ≠ b) → ((a ≠ c) → ((segment ℝ a b ∩
            segment ℝ a c ⊆ {a}) → (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s
            + t ≤ K * dist (lineMap a b s) (lineMap a c t)))) ) := by
  classical
  intro a b c hab hac hi
  have hpos : ∀ z ∈ Icc (0 : ℝ) 1,
      0 < ‖z • (b - a) - (1 - z) • (c - a)‖ := by
    intro z hz
    apply norm_pos_iff.mpr
    intro heq
    have heq' : z • (b - a) = (1 - z) • (c - a) := sub_eq_zero.mp heq
    have hm : lineMap a b z ∈ segment ℝ a b ∩ segment ℝ a c := by
      constructor
      · exact lineMap_mem_segment ℝ _ _ hz
      · have hh : lineMap a b z = lineMap a c (1 - z) := by
          simpa only [lineMap_apply, vsub_eq_sub, vadd_eq_add] using
            congrArg (fun x : ℝ × ℝ => x + a) heq'
        rw [hh]
        exact lineMap_mem_segment ℝ _ _ ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have ha : lineMap a b z = a := hi hm
    have hz0 : z = 0 := (lineMap_injective ℝ hab) (by simpa using ha)
    have hc0 : (1 - z) • (c - a) = 0 := by simpa [hz0] using heq'.symm
    have hz1 : z = 1 := by
      rcases smul_eq_zero.mp hc0 with hh | hh
      · linarith
      · exact False.elim (hac (sub_eq_zero.mp hh).symm)
    linarith
  obtain ⟨ε, hε, hmin⟩ := isCompact_Icc.exists_forall_le'
    (f := fun z : ℝ => ‖z • (b - a) - (1 - z) • (c - a)‖)
    (by fun_prop) hpos
  refine ⟨ε⁻¹, inv_nonneg.mpr hε.le, ?_⟩
  intro s hs t ht
  by_cases hst : s + t = 0
  · simp only [hst]
    exact mul_nonneg (inv_nonneg.mpr hε.le) dist_nonneg
  have hstpos : 0 < s + t := lt_of_le_of_ne (add_nonneg hs.1 ht.1) (Ne.symm hst)
  have hz : s / (s + t) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hstpos.le, (div_le_one hstpos).mpr (by linarith [ht.1])⟩
  have hscale :
      s • (b - a) - t • (c - a) =
        (s + t) • ((s / (s + t)) • (b - a) - (1 - s / (s + t)) • (c - a)) := by
    have h₁ : (s + t) * (s / (s + t)) = s := by field_simp
    have h₂ : (s + t) * (1 - s / (s + t)) = t := by field_simp; ring
    conv_rhs => rw [smul_sub, smul_smul, smul_smul]
    rw [h₁, h₂]
  have hd : dist (lineMap a b s) (lineMap a c t) =
      (s + t) * ‖(s / (s + t)) • (b - a) - (1 - s / (s + t)) • (c - a)‖ := by
    rw [dist_eq_norm]
    have hh : lineMap a b s - lineMap a c t = s • (b - a) - t • (c - a) := by
      simp only [lineMap_apply, vsub_eq_sub, vadd_eq_add]
      abel
    rw [hh, hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hstpos]
  rw [hd]
  calc
    s + t = ε⁻¹ * ((s + t) * ε) := by field_simp
    _ ≤ _ := by gcongr; exact hmin _ hz

private theorem shared :
    (by
      classical
      exact
        (∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), (a ≠ b) → ((a ≠ c) → ((segment ℝ a b ∩
            segment ℝ a c ⊆ {a}) → (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s
            + t ≤ K * dist (lineMap a b s) (lineMap a c t))))) → (∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀
            (c : ℝ × ℝ), (a ≠ b) → ((a ≠ c) → ((segment ℝ a b ∩ segment ℝ a c ⊆ {a}) → (∀ (f : (ℝ
            × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap
            (f a) (f b) s) (lineMap (f a) (f c) t) ≤ K * dist (lineMap a b s) (lineMap a c t)))))
            ) := by
  classical
  intro angle a b c hab hac hi f
  obtain ⟨A, hA, hbound⟩ := angle a b c hab hac hi
  let D := dist (f a) (f b) + dist (f a) (f c)
  have hD : 0 ≤ D := add_nonneg dist_nonneg dist_nonneg
  refine ⟨A * D, mul_nonneg hA hD, ?_⟩
  intro s hs t ht
  calc
    _ ≤ dist (lineMap (f a) (f b) s) (f a) +
        dist (f a) (lineMap (f a) (f c) t) := dist_triangle _ _ _
    _ = s * dist (f a) (f b) + t * dist (f a) (f c) := by
      rw [dist_lineMap_left, dist_left_lineMap]
      simp only [Real.norm_eq_abs, abs_of_nonneg hs.1, abs_of_nonneg ht.1]
    _ ≤ (s + t) * D := by
      dsimp [D]
      nlinarith [mul_nonneg hs.1 (dist_nonneg (x := f a) (y := f c)),
        mul_nonneg ht.1 (dist_nonneg (x := f a) (y := f b))]
    _ ≤ (A * dist (lineMap a b s) (lineMap a c t)) * D :=
      mul_le_mul_of_nonneg_right (hbound s hs t ht) hD
    _ = _ := by ring

private theorem same :
    (by
      classical
      exact
        ∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), (a ≠ b) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc
            (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f a) (f b) t)
            ≤ K * dist (lineMap a b s) (lineMap a b t)) ) := by
  classical
  intro a b hab f
  have hpos : 0 < dist a b := dist_pos.mpr hab
  refine ⟨dist (f a) (f b) / dist a b, div_nonneg dist_nonneg hpos.le, ?_⟩
  intro s hs t ht
  rw [dist_lineMap_lineMap, dist_lineMap_lineMap]
  exact le_of_eq (by field_simp)

private theorem separate :
    (by
      classical
      exact
        ∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), ∀ (d : ℝ × ℝ), (Disjoint (segment ℝ a b)
            (segment ℝ c d)) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈
            Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤ K * dist
            (lineMap a b s) (lineMap c d t)) ) := by
  classical
  intro a b c d hi f
  have hpos : ∀ z ∈ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      0 < dist (lineMap a b z.1) (lineMap c d z.2) := by
    intro z hz
    apply dist_pos.mpr
    intro h
    exact Set.disjoint_left.mp hi (lineMap_mem_segment ℝ _ _ hz.1)
      (h ▸ lineMap_mem_segment ℝ _ _ hz.2)
  obtain ⟨ε, hε, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_forall_le'
    (f := fun z : ℝ × ℝ => dist (lineMap a b z.1) (lineMap c d z.2))
    (by fun_prop) hpos
  let D := dist (f a) (f b) + dist (f a) (f c) + dist (f c) (f d)
  have hD : 0 ≤ D := add_nonneg (add_nonneg dist_nonneg dist_nonneg) dist_nonneg
  refine ⟨D / ε, div_nonneg hD hε.le, ?_⟩
  intro s hs t ht
  have hbound : dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤ D := by
    calc
      _ ≤ dist (lineMap (f a) (f b) s) (f a) + dist (f a) (f c) +
          dist (f c) (lineMap (f c) (f d) t) := dist_triangle4 _ _ _ _
      _ = s * dist (f a) (f b) + dist (f a) (f c) + t * dist (f c) (f d) := by
        rw [dist_lineMap_left, dist_left_lineMap]
        simp only [Real.norm_eq_abs, abs_of_nonneg hs.1, abs_of_nonneg ht.1]
      _ ≤ D := by
        dsimp [D]
        nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (dist_nonneg (x := f a) (y := f b)),
          mul_nonneg (sub_nonneg.mpr ht.2) (dist_nonneg (x := f c) (y := f d))]
  calc
    _ ≤ D := hbound
    _ = (D / ε) * ε := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmin (s, t) ⟨hs, ht⟩) (div_nonneg hD hε.le)

private theorem first :
    (by
      classical
      exact
        (∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), (a ≠ b) → ((a ≠ c) → ((segment ℝ a b ∩
            segment ℝ a c ⊆ {a}) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀
            t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f a) (f c) t) ≤ K * dist
            (lineMap a b s) (lineMap a c t))))) → ((∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), (a ≠ b) → (∀ (f
            : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist
            (lineMap (f a) (f b) s) (lineMap (f a) (f b) t) ≤ K * dist (lineMap a b s) (lineMap a
            b t))) → (∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), (a ≠ b) → ((a ≠ c) → ((∀ x ∈
            segment ℝ a b ∩ segment ℝ a c,
            (x = a ∨ x = b) ∧ (x = a ∨ x = c)) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc
                (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f a) (f c)
                t) ≤ K * dist (lineMap a b s) (lineMap a c t)))))) ) := by
  classical
  intro shared same a b c hab hac hi f
  by_cases hbc : b = c
  · subst c
    exact same a b hab f
  apply shared a b c hab hac ?_ f
  intro x hx
  rcases hi x hx with ⟨h₁, h₂⟩
  rcases h₁ with rfl | rfl
  · rfl
  · rcases h₂ with h | h
    · exact h
    · exact False.elim (hbc h)

private theorem reverse_left :
    (by
      classical
      exact
        ∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), ∀ (d : ℝ × ℝ), ∀ (f : (ℝ × ℝ) → ℝ), (∃ K :
            ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤
              K * dist (lineMap a b s) (lineMap c d t)) → (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1,
                  ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f b) (f a) s) (lineMap (f c) (f d) t) ≤ K *
                  dist (lineMap b a s) (lineMap c d t)) ) := by
  classical
  intro a b c d f h
  obtain ⟨K, hK, hb⟩ := h
  refine ⟨K, hK, fun s hs t ht => ?_⟩
  simpa only [lineMap_apply_one_sub] using
    hb (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ t ht

private theorem reverse_right :
    (by
      classical
      exact
        ∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), ∀ (d : ℝ × ℝ), ∀ (f : (ℝ × ℝ) → ℝ), (∃ K :
            ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤
              K * dist (lineMap a b s) (lineMap c d t)) → (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1,
                  ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f d) (f c) t) ≤ K *
                  dist (lineMap a b s) (lineMap d c t)) ) := by
  classical
  intro a b c d f h
  obtain ⟨K, hK, hb⟩ := h
  refine ⟨K, hK, fun s hs t ht => ?_⟩
  simpa only [lineMap_apply_one_sub] using
    hb s hs (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩

private theorem pair_bound :
    (by
      classical
      exact
        (∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), ∀ (d : ℝ × ℝ), (Disjoint (segment ℝ a b)
            (segment ℝ c d)) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈
            Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤ K * dist
            (lineMap a b s) (lineMap c d t))) → ((∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), (a
            ≠ b) → ((a ≠ c) → ((∀ x ∈ segment ℝ a b ∩ segment ℝ a c, (x = a ∨ x = b) ∧ (x = a ∨ x
            = c)) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ)
            1, dist (lineMap (f a) (f b) s) (lineMap (f a) (f c) t) ≤ K * dist (lineMap a b s)
            (lineMap a c t))))) → ((∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), ∀ (d : ℝ × ℝ), ∀
            (f : (ℝ × ℝ) → ℝ), (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist
            (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤ K * dist (lineMap a b s) (lineMap c
            d t)) → (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f
            b) (f a) s) (lineMap (f c) (f d) t) ≤ K * dist (lineMap b a s) (lineMap c d t))) →
            ((∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c : ℝ × ℝ), ∀ (d : ℝ × ℝ), ∀ (f : (ℝ × ℝ) → ℝ), (∃
            K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s)
            (lineMap (f c) (f d) t) ≤ K * dist (lineMap a b s) (lineMap c d t)) → (∃ K : ℝ, 0 ≤ K
            ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f
            d) (f c) t) ≤ K * dist (lineMap a b s) (lineMap d c t))) → (∀ (a : ℝ × ℝ), ∀ (b : ℝ ×
            ℝ), ∀ (c : ℝ × ℝ), ∀ (d : ℝ × ℝ), (a ≠ b) → ((c ≠ d) → ((∀ x ∈ segment ℝ a b ∩
            segment ℝ c d,
            (x = a ∨ x = b) ∧ (x = c ∨ x = d)) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc
                (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f c) (f d)
                t) ≤ K * dist (lineMap a b s) (lineMap c d t)))))))) ) := by
  classical
  intro separate first reverse_left reverse_right a b c d hab hcd hi f
  by_cases hac : a = c
  · subst c
    exact first a b d hab hcd hi f
  by_cases had : a = d
  · subst d
    apply reverse_right a b a c f
    apply first a b c hab hcd.symm
    intro x hx
    have hh := hi x (by simpa only [segment_symm ℝ a c] using hx)
    exact ⟨hh.1, hh.2.symm⟩
  by_cases hbc : b = c
  · subst c
    apply reverse_left b a b d f
    apply first b a d hab.symm hcd
    intro x hx
    have hh := hi x (by simpa only [segment_symm ℝ b a] using hx)
    exact ⟨hh.1.symm, hh.2⟩
  by_cases hbd : b = d
  · subst d
    apply reverse_left b a c b f
    apply reverse_right b a b c f
    apply first b a c hab.symm hcd.symm
    intro x hx
    have hh := hi x (by simpa only [segment_symm ℝ b a, segment_symm ℝ b c] using hx)
    exact ⟨hh.1.symm, hh.2.symm⟩
  apply separate a b c d ?_ f
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hi x ⟨hx, hy⟩ with ⟨h₁, h₂⟩
  rcases h₁ with rfl | rfl <;> rcases h₂ with h | h
  · exact hac h
  · exact had h
  · exact hbc h
  · exact hbd h

private theorem boundary_extension :
    (by
      classical
      exact
        (∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), (a ≠ b) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc
            (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f a) (f b) t)
            ≤ K * dist (lineMap a b s) (lineMap a b t))) → ((∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (c :
            ℝ × ℝ), ∀ (d : ℝ × ℝ), (a ≠ b) → ((c ≠ d) → ((∀ x ∈ segment ℝ a b ∩ segment ℝ c d, (x
            = a ∨ x = b) ∧ (x = c ∨ x = d)) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0
            : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤ K
            * dist (lineMap a b s) (lineMap c d t))))) → (∀ {n : ℕ}, ∀ (p : Fin (n + 3) → ℝ × ℝ),
            (Function.Injective p) → ((∀ i j : Fin (n + 3), i ≠ j →
            segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) =
              {x | (x = p i ∨ x = p (i + 1)) ∧ (x = p j ∨ x = p (j + 1))}) → (∀ (f : (ℝ × ℝ) →
                  ℝ), ∃ (K : NNReal) (g : (ℝ × ℝ) → ℝ), LipschitzWith K g ∧ ∀ i, ∀ (t : ℝ), t ∈
                  Icc (0 : ℝ) 1 → g (lineMap (p i) (p (i + 1)) t) = lineMap (f (p i)) (f (p (i +
                  1))) t)))) ) := by
  classical
  intro same pair_bound n p hi he f
  classical
  have hne : ∀ i : Fin (n + 3), p i ≠ p (i + 1) := by
    intro i hh
    simpa using (hi hh).symm
  have hb : ∀ i j : Fin (n + 3), ∃ K : ℝ, 0 ≤ K ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (lineMap (f (p i)) (f (p (i + 1))) s)
          (lineMap (f (p j)) (f (p (j + 1))) t) ≤
        K * dist (lineMap (p i) (p (i + 1)) s) (lineMap (p j) (p (j + 1)) t) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact same _ _ (hne i) f
    apply pair_bound _ _ _ _ (hne i) (hne j) ?_ f
    intro x hx
    simpa only [he i j hij, Set.mem_ofPred] using hx
  choose B hB hbound using hb
  let K : NNReal := ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hB i j))⟩
  have hBK : ∀ i j, B i j ≤ (K : ℝ) := by
    intro i j
    exact le_trans (Finset.single_le_sum (fun j _ => hB i j) (Finset.mem_univ j))
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hB i j)) (Finset.mem_univ i))
  let C := ⋃ i, segment ℝ (p i) (p (i + 1))
  have hrep : ∀ x ∈ C, ∃ i, ∃ t ∈ Icc (0 : ℝ) 1,
      lineMap (p i) (p (i + 1)) t = x := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨t, ht, heq⟩ := hi
    exact ⟨i, t, ht, heq⟩
  let g₀ : (ℝ × ℝ) → ℝ := fun x => if hx : x ∈ C then
    lineMap (f (p (hrep x hx).choose)) (f (p ((hrep x hx).choose + 1)))
      (hrep x hx).choose_spec.choose else 0
  have hg₀ : ∀ x ∈ C, ∃ i, ∃ t ∈ Icc (0 : ℝ) 1,
      lineMap (p i) (p (i + 1)) t = x ∧
      g₀ x = lineMap (f (p i)) (f (p (i + 1))) t := by
    intro x hx
    refine ⟨(hrep x hx).choose, (hrep x hx).choose_spec.choose,
      (hrep x hx).choose_spec.choose_spec.1,
      (hrep x hx).choose_spec.choose_spec.2, ?_⟩
    simp only [g₀, dite_eq_left hx]
  have hlip : LipschitzOnWith K g₀ C := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    obtain ⟨i, s, hs, rfl, hsval⟩ := hg₀ x hx
    obtain ⟨j, t, ht, rfl, htval⟩ := hg₀ y hy
    rw [hsval, htval]
    exact (hbound i j s hs t ht).trans (mul_le_mul_of_nonneg_right (hBK i j) dist_nonneg)
  obtain ⟨g, hg, hgeq⟩ := hlip.extend_real
  refine ⟨K, g, hg, ?_⟩
  intro i t ht
  have hx : lineMap (p i) (p (i + 1)) t ∈ C :=
    mem_iUnion.mpr ⟨i, lineMap_mem_segment ℝ _ _ ht⟩
  rw [← hgeq hx]
  obtain ⟨j, s, hs, heq, hval⟩ := hg₀ _ hx
  rw [hval]
  apply dist_le_zero.mp
  have hh := hbound j i s hs t ht
  rw [heq, dist_self, mul_zero] at hh
  exact hh

private theorem perturbation :
    (by
      classical
      exact
        ∀ (F : (ℝ × ℝ) → (ℝ × ℝ)), (LipschitzWith (1 / 2) F) → (∃ H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (∀ x, H
            x = x + F x) ∧ LipschitzWith (3 / 2) H ∧ AntilipschitzWith 2 H) ) := by
  classical
  intro F hF
  classical
  let h : (ℝ × ℝ) → (ℝ × ℝ) := fun x => x + F x
  have hlip : LipschitzWith (3 / 2) h := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh : dist (h x) (h y) ≤ dist x y + dist (F x) (F y) := dist_add_add_le _ _ _ _
    have hb := hF.dist_le_mul x y
    norm_num at hb ⊢
    linarith
  have hanti : AntilipschitzWith 2 h := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    have hh : dist x y ≤ dist (h x) (h y) + dist (F x) (F y) := by
      calc
        _ = dist (h x - F x) (h y - F y) := by simp only [h, add_sub_cancel_right]
        _ ≤ _ := dist_sub_sub_le _ _ _ _
    have hb := hF.dist_le_mul x y
    norm_num at hb ⊢
    linarith
  have hsurj : Function.Surjective h := by
    intro y
    let g : (ℝ × ℝ) → (ℝ × ℝ) := fun x => y - F x
    have hg : ContractingWith (1 / 2) g := by
      refine ⟨by norm_num, ?_⟩
      simpa only [zero_add] using (LipschitzWith.const y).sub hF
    refine ⟨hg.fixedPoint, ?_⟩
    have hfix : y - F (hg.fixedPoint) = hg.fixedPoint := hg.fixedPoint_isFixedPt
    exact eq_sub_iff_add_eq.mp hfix.symm
  let e := Equiv.ofBijective h ⟨hanti.injective, hsurj⟩
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := e.toHomeomorphOfIsInducing (hanti.isInducing hlip.continuous)
  exact ⟨H, fun _ => rfl, hlip, hanti⟩

private theorem rationalize :
    (by
      classical
      exact
        (∀ {n : ℕ}, ∀ (p : Fin (n + 3) → ℝ × ℝ), (Function.Injective p) → ((∀ i j : Fin (n + 3),
            i ≠ j → segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) = {x | (x = p i ∨ x
            = p (i + 1)) ∧ (x = p j ∨ x = p (j + 1))}) → (∀ (f : (ℝ × ℝ) → ℝ), ∃ (K : NNReal) (g
            : (ℝ × ℝ) → ℝ), LipschitzWith K g ∧ ∀ i, ∀ (t : ℝ), t ∈ Icc (0 : ℝ) 1 → g (lineMap (p
            i) (p (i + 1)) t) = lineMap (f (p i)) (f (p (i + 1))) t))) → ((∀ (F : (ℝ × ℝ) → (ℝ ×
            ℝ)), (LipschitzWith (1 / 2) F) → (∃ H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (∀ x, H x = x + F x) ∧
            LipschitzWith (3 / 2) H ∧ AntilipschitzWith 2 H)) → (∀ {n : ℕ}, ∀ (p : Fin (n + 3) →
            ℝ × ℝ), (Function.Injective p) → ((∀ i j : Fin (n + 3), i ≠ j →
            segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) =
              {x | (x = p i ∨ x = p (i + 1)) ∧ (x = p j ∨ x = p (j + 1))}) → (∃ (H : (ℝ × ℝ) ≃ₜ
                  (ℝ × ℝ)) (r : Fin (n + 3) → ℝ × ℝ), (∀ i, ∃ a b : ℚ, r i = ((a : ℝ), (b : ℝ)))
                  ∧ LipschitzWith (3 / 2) H ∧ AntilipschitzWith 2 H ∧ (∀ i, H (p i) = r i) ∧ (∀
                  i, H '' segment ℝ (p i) (p (i + 1)) = segment ℝ (r i) (r (i + 1))))))) ) := by
  classical
  intro boundary_extension perturbation n p hi he
  classical
  have hhats : ∀ k : Fin (n + 3), ∃ (K : NNReal) (g : (ℝ × ℝ) → ℝ),
      LipschitzWith K g ∧ ∀ i (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        g (lineMap (p i) (p (i + 1)) t) =
          lineMap (if i = k then 1 else 0 : ℝ) (if i + 1 = k then 1 else 0) t := by
    intro k
    simpa only [hi.eq_iff] using
      boundary_extension p hi he (fun x => if x = p k then (1 : ℝ) else 0)
  choose K g hg hval using hhats
  let S : ℝ := ∑ k, (K k : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
  let δ : ℝ := (2 * (S + 1))⁻¹
  have hδ : 0 < δ := inv_pos.mpr (by positivity)
  have hδS : δ * S ≤ (1 / 2 : ℝ) := by
    have hh : δ * (S + 1) = (1 / 2 : ℝ) := by
      dsimp [δ]
      field_simp
    nlinarith
  have hr : ∀ i : Fin (n + 3), ∃ a b : ℚ,
      ‖((a : ℝ), (b : ℝ)) - p i‖ ≤ δ := by
    intro i
    obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show (p i).1 - δ < (p i).1 + δ by linarith)
    obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show (p i).2 - δ < (p i).2 + δ by linarith)
    refine ⟨a, b, ?_⟩
    rw [Prod.norm_def, max_le_iff]
    constructor <;> change |(_ : ℝ) - _| ≤ δ <;> rw [abs_le] <;> constructor <;> linarith
  choose a b hr using hr
  let r : Fin (n + 3) → ℝ × ℝ := fun i => ((a i : ℝ), (b i : ℝ))
  let d := fun i => r i - p i
  let F : (ℝ × ℝ) → ℝ × ℝ := fun x => ∑ k, g k x • d k
  have hF : LipschitzWith (1 / 2) F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (F x) (F y) = ‖∑ k, (g k x - g k y) • d k‖ := by
        rw [dist_eq_norm]
        simp only [F, ← Finset.sum_sub_distrib, sub_smul]
      _ ≤ ∑ k, ‖(g k x - g k y) • d k‖ := norm_sum_le _ _
      _ ≤ ∑ k, ((K k : ℝ) * dist x y) * δ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_smul, ← dist_eq_norm]
        exact mul_le_mul ((hg k).dist_le_mul x y) (hr k)
          (norm_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)
      _ = (δ * S) * dist x y := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        dsimp [S]
        ring
      _ ≤ (1 / 2 : NNReal) * dist x y := by
        change _ ≤ (1 / 2 : ℝ) * dist x y
        exact mul_le_mul_of_nonneg_right hδS dist_nonneg
  obtain ⟨H, hH, hlip, hanti⟩ := perturbation F hF
  have hFedge : ∀ i (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      F (lineMap (p i) (p (i + 1)) t) = lineMap (d i) (d (i + 1)) t := by
    intro i t ht
    simp only [F]
    simp_rw [hval _ i t ht]
    simp only [lineMap_apply, vsub_eq_sub, vadd_eq_add]
    simp only [smul_eq_mul, mul_sub]
    simp only [sub_smul, add_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, ite_smul, zero_smul, smul_sub]
    simp [Finset.sum_ite_eq]
  have hHedge : ∀ i (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      H (lineMap (p i) (p (i + 1)) t) = lineMap (r i) (r (i + 1)) t := by
    intro i t ht
    rw [hH, hFedge i t ht]
    simp only [lineMap_apply, vsub_eq_sub, vadd_eq_add, d]
    module
  refine ⟨H, r, fun i => ⟨a i, b i, rfl⟩, hlip, hanti, ?_, ?_⟩
  · intro i
    simpa using hHedge i 0 ⟨le_rfl, zero_le_one⟩
  · intro i
    rw [segment_eq_image_lineMap, segment_eq_image_lineMap, ← Set.image_comp]
    apply Set.image_congr
    intro t ht
    exact hHedge i t ht

private theorem hrinj :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : Fin (n + 3) → Real × Real), (Function.Injective p) → (∀ (H : ℝ × ℝ ≃ₜ
            ℝ × ℝ), ∀ (r : Fin (n + (3 : ℕ)) → ℝ × ℝ), (∀ (i : Fin (n + (3 : ℕ))), (H : ℝ × ℝ → ℝ
            × ℝ) (p i) = r i) → (Function.Injective r)) ) := by
  classical
  intro n p hi H r hvert i j hh
  apply hi
  apply H.injective
  simpa only [hvert] using hh

private theorem hredge :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : Fin (n + 3) → Real × Real), (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n
            + (3 : ℕ))), i ≠ j → segment ℝ (p i) (p (i + (1 : Fin (n + (3 : ℕ))))) ∩ segment ℝ (p
            j) (p (j + (1 : Fin (n + (3 : ℕ))))) = {x : ℝ × ℝ | (x = p i ∨ x = p (i + (1 : Fin (n
            + (3 : ℕ))))) ∧ (x = p j ∨ x = p (j + (1 : Fin (n + (3 : ℕ)))))}) → (∀ (H : ℝ × ℝ ≃ₜ
            ℝ × ℝ), ∀ (r : Fin (n + (3 : ℕ)) → ℝ × ℝ), (∀ (i : Fin (n + (3 : ℕ))), (H : ℝ × ℝ → ℝ
            × ℝ) (p i) = r i) → ((∀ (i : Fin (n + (3 : ℕ))), (⇑H : ℝ × ℝ → ℝ × ℝ) '' segment ℝ (p
            i) (p (i + (1 : Fin (n + (3 : ℕ))))) = segment ℝ (r i) (r (i + (1 : Fin (n + (3 :
            ℕ)))))) → (∀ i j : Fin (n + 3), i ≠ j → segment ℝ (r i) (r (i + 1)) ∩ segment ℝ (r j)
            (r (j + 1)) = {x | (x = r i ∨ x = r (i + 1)) ∧ (x = r j ∨ x = r (j + 1))}))) ) := by
  classical
  intro n p he H r hvert hedge i j hij
  rw [← hedge i, ← hedge j, ← Set.image_inter H.injective, he i j hij]
  ext x
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    constructor
    · rcases hy₁ with rfl | rfl
      · exact Or.inl (hvert i)
      · exact Or.inr (hvert (i + 1))
    · rcases hy₂ with rfl | rfl
      · exact Or.inl (hvert j)
      · exact Or.inr (hvert (j + 1))
  · rintro ⟨hx₁, hx₂⟩
    refine ⟨H.symm x, ⟨?_, ?_⟩, H.apply_symm_apply x⟩
    · rcases hx₁ with h | h
      · exact Or.inl (by rw [h, ← hvert i, H.symm_apply_apply])
      · exact Or.inr (by rw [h, ← hvert (i + 1), H.symm_apply_apply])
    · rcases hx₂ with h | h
      · exact Or.inl (by rw [h, ← hvert j, H.symm_apply_apply])
      · exact Or.inr (by rw [h, ← hvert (j + 1), H.symm_apply_apply])

private theorem hcarrier :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : Fin (n + 3) → Real × Real), ∀ (H : ℝ × ℝ ≃ₜ ℝ × ℝ), ∀ (r : Fin (n +
            (3 : ℕ)) → ℝ × ℝ), ∀ (hr : ∀ (i : Fin (n + (3 : ℕ))), ∃ (a : ℚ) (b : ℚ), r i = ((↑a :
            ℝ), (↑b : ℝ))), (∀ (i : Fin (n + (3 : ℕ))), (⇑H : ℝ × ℝ → ℝ × ℝ) '' segment ℝ (p i)
            (p (i + (1 : Fin (n + (3 : ℕ))))) = segment ℝ (r i) (r (i + (1 : Fin (n + (3 :
            ℕ)))))) → (∀ (hrinj : Function.Injective r), ∀ (hredge : ∀ i j : Fin (n + 3), i ≠ j →
            segment ℝ (r i) (r (i + 1)) ∩ segment ℝ (r j) (r (j + 1)) = {x | (x = r i ∨ x = r (i
            + 1)) ∧ (x = r j ∨ x = r (j + 1))}),
        let q₀ : P3381T1PolygonBoundary n := ⟨r, hr, hrinj, hredge⟩
        ∀ (m : ℕ), ∀ (q : P3381T1PolygonBoundary m), (P3475T1BoundarySubdivision q q₀) → (H
            '' (⋃ i, segment ℝ (p i) (p (i + 1))) = ⋃ i, segment ℝ (q.vertex i) (q.vertex (i +
            1)))) ) := by
  classical
  intro n p H r hr hedge hrinj hredge q₀ m q s
  rw [Set.image_iUnion]
  simp_rw [hedge]
  exact s.carrier_eq

private theorem hpre :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : Fin (n + 3) → Real × Real), ∀ (H : ℝ × ℝ ≃ₜ ℝ × ℝ), ∀ (m : ℕ), ∀ (q :
            P3381T1PolygonBoundary m), (H '' (⋃ i, segment ℝ (p i) (p (i + 1))) = ⋃ i, segment
            ℝ (q.vertex i) (q.vertex (i + 1))) → (H ⁻¹' (⋃ i, segment ℝ (q.vertex i) (q.vertex (i
            + 1))) = ⋃ i, segment ℝ (p i) (p (i + 1))) ) := by
  classical
  intro n p H m q hcarrier
  rw [← hcarrier, Set.preimage_image_eq _ H.injective]

end RealPolygonGeometry

theorem P3861T1RealPolygonDomains {n : Nat}
    (p : Fin (n + 3) → Real × Real) (hi : Function.Injective p)
    (he : ∀ i j : Fin (n + 3), i ≠ j →
      segment Real (p i) (p (i + 1)) ∩ segment Real (p j) (p (j + 1)) =
        {x | (x = p i ∨ x = p (i + 1)) ∧
          (x = p j ∨ x = p (j + 1))}) :
    let C := ⋃ i, segment Real (p i) (p (i + 1))
    ∃ U V : Set (Real × Real),
      IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
      IsOpen V ∧ IsConnected V ∧ ¬ Bornology.IsBounded V ∧
      Disjoint U V ∧ U ∪ V = Cᶜ ∧
      frontier U = C ∧ frontier V = C := by
-- BODY
  exact (open Set AffineMap in by
    classical
    -- A positive angular bound also covers opposite collinear incident edges.
    have angle (a b c : ℝ × ℝ) (hab : a ≠ b) (hac : a ≠ c)
        (hi : segment ℝ a b ∩ segment ℝ a c ⊆ {a}) := RealPolygonGeometry.angle a b c hab hac hi
    have shared (a b c : ℝ × ℝ) (hab : a ≠ b) (hac : a ≠ c)
        (hi : segment ℝ a b ∩ segment ℝ a c ⊆ {a}) (f : (ℝ × ℝ) → ℝ) :=
            RealPolygonGeometry.shared angle a b c hab hac hi f
    have same (a b : ℝ × ℝ) (hab : a ≠ b) (f : (ℝ × ℝ) → ℝ) := RealPolygonGeometry.same a b hab f
    have separate (a b c d : ℝ × ℝ)
        (hi : Disjoint (segment ℝ a b) (segment ℝ c d)) (f : (ℝ × ℝ) → ℝ) :=
            RealPolygonGeometry.separate a b c d hi f
    have first (a b c : ℝ × ℝ) (hab : a ≠ b) (hac : a ≠ c)
        (hi : ∀ x ∈ segment ℝ a b ∩ segment ℝ a c,
          (x = a ∨ x = b) ∧ (x = a ∨ x = c)) (f : (ℝ × ℝ) → ℝ) := RealPolygonGeometry.first
              shared same a b c hab hac hi f
    have reverse_left (a b c d : ℝ × ℝ) (f : (ℝ × ℝ) → ℝ)
        (h : ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤
            K * dist (lineMap a b s) (lineMap c d t)) := RealPolygonGeometry.reverse_left a b c d
                f h
    have reverse_right (a b c d : ℝ × ℝ) (f : (ℝ × ℝ) → ℝ)
        (h : ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (lineMap (f a) (f b) s) (lineMap (f c) (f d) t) ≤
            K * dist (lineMap a b s) (lineMap c d t)) := RealPolygonGeometry.reverse_right a b c
                d f h
    have pair_bound (a b c d : ℝ × ℝ) (hab : a ≠ b) (hcd : c ≠ d)
        (hi : ∀ x ∈ segment ℝ a b ∩ segment ℝ c d,
          (x = a ∨ x = b) ∧ (x = c ∨ x = d)) (f : (ℝ × ℝ) → ℝ) := RealPolygonGeometry.pair_bound
              separate first reverse_left reverse_right a b c d hab hcd hi f
    -- Pairwise estimates make interpolation independent of the chosen edge.
    have boundary_extension {n : ℕ} (p : Fin (n + 3) → ℝ × ℝ)
        (hi : Function.Injective p)
        (he : ∀ i j : Fin (n + 3), i ≠ j →
          segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) =
            {x | (x = p i ∨ x = p (i + 1)) ∧ (x = p j ∨ x = p (j + 1))})
        (f : (ℝ × ℝ) → ℝ) := RealPolygonGeometry.boundary_extension same pair_bound (n := n) p hi
            he f
    -- The inverse is obtained by solving x = y - F x by contraction.
    have perturbation (F : (ℝ × ℝ) → (ℝ × ℝ)) (hF : LipschitzWith (1 / 2) F) :=
        RealPolygonGeometry.perturbation F hF
    -- Extend the vertex weights first, then choose sufficiently small displacements.
    have rationalize {n : ℕ} (p : Fin (n + 3) → ℝ × ℝ)
        (hi : Function.Injective p)
        (he : ∀ i j : Fin (n + 3), i ≠ j →
          segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) =
            {x | (x = p i ∨ x = p (i + 1)) ∧ (x = p j ∨ x = p (j + 1))}) :=
                RealPolygonGeometry.rationalize boundary_extension perturbation (n := n) p hi he
    dsimp only
    obtain ⟨H, r, hr, hlip, hanti, hvert, hedge⟩ := rationalize p hi he
    have hrinj := RealPolygonGeometry.hrinj n p hi H r hvert
    have hredge := RealPolygonGeometry.hredge n p he H r hvert hedge
    -- Reduction preserves the whole carrier, including straight subdivision vertices.
    let q₀ : P3381T1PolygonBoundary n := ⟨r, hr, hrinj, hredge⟩
    obtain ⟨m, q, ⟨s⟩, hcorner⟩ := P3475T1BoundaryReduction q₀
    obtain ⟨X, K, ⟨t⟩⟩ := P3475T1PolygonTriangleConstruction q hcorner
    obtain ⟨U, V, hoU, hcU, hbU, hoV, hcV, hbV, hd, hu, hfU, hfV, _⟩ :=
      P3475T1PolygonalSeparation q X K t
    have hcarrier := RealPolygonGeometry.hcarrier n p H r hr hedge hrinj hredge m q s
    have hpre : H ⁻¹' (⋃ i, segment ℝ (q.vertex i) (q.vertex (i + 1))) =
        ⋃ i, segment ℝ (p i) (p (i + 1)) := RealPolygonGeometry.hpre n p H m q hcarrier
    refine ⟨H ⁻¹' U, H ⁻¹' V, hoU.preimage H.continuous,
      H.isConnected_preimage.mpr hcU, hanti.isBounded_preimage hbU,
      hoV.preimage H.continuous, H.isConnected_preimage.mpr hcV, ?_,
      hd.preimage H, ?_, ?_, ?_⟩
    · intro hb
      apply hbV
      have hh := hlip.isBounded_image hb
      rwa [Set.image_preimage_eq _ H.surjective] at hh
    · rw [← Set.preimage_union, hu, Set.preimage_compl, hpre]
    · rw [← H.preimage_frontier, hfU, hpre]
    · rw [← H.preimage_frontier, hfV, hpre]
  )

end ApollonianSuperharmonic

end
