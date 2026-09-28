/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.Curves.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Curves.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import Mathlib.LinearAlgebra.AffineSpace.Independent
/-!
# Moving sofa: related mathematical developments

* `Convex.CurveCut`.
* `Convex.ArcCutArea`.
* `Convex.OuterCornerPath`.
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
# Convex / Curve Cut
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem normalVector_eq_positive_combo {a b t : ℝ}
    (hab : a < b) (hba : b < a + Real.pi) (_hat : a < t) (_htb : t < b) :
    normalVector (t : Real.Angle) =
      (Real.sin (b - t) / Real.sin (b - a)) • normalVector (a : Real.Angle) +
        (Real.sin (t - a) / Real.sin (b - a)) • normalVector (b : Real.Angle) := by
  have hs : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
  have hs' : Real.sin b * Real.cos a - Real.cos b * Real.sin a ≠ 0 := by
    simpa only [Real.sin_sub] using hs
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [normalVector, frame, Real.sin_sub] <;>
    field_simp [hs'] <;> ring

private theorem eq_supportingIntersection_of_mem_endpoint_faces
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (p : Point) (hpa : p ∈ exposedEdge K (a : Real.Angle))
    (hpb : p ∈ exposedEdge K (b : Real.Angle)) :
    supportingIntersection K a b = p := by
  let O := supportingIntersection K a b
  have hs : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
  have hna : inner ℝ (O - p) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, supportingIntersection_inner_left, hpa.2, sub_self]
  have hnb : inner ℝ (O - p) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, supportingIntersection_inner_right K a b hs, hpb.2, sub_self]
  have hrot := normalVector_add_real a (b - a)
  have htan : inner ℝ (O - p) (tangentVector (a : Real.Angle)) = 0 := by
    have := hnb
    rw [show normalVector (b : Real.Angle) =
      Real.cos (b - a) • normalVector (a : Real.Angle) +
        Real.sin (b - a) • tangentVector (a : Real.Angle) by
          simpa only [add_sub_cancel] using hrot,
      inner_add_right, inner_smul_right, inner_smul_right, hna] at this
    simp only [mul_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left hs
  change O = p
  rw [show O = p + (O - p) by abel,
    ← inner_normalVector_smul_add_inner_tangentVector_smul
      (O - p) (a : Real.Angle), hna, htan, zero_smul, zero_smul, add_zero, add_zero]

private theorem exposedEdge_eq_singleton_of_common_endpoint
    (K : ConvexBody Point) {a b t : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hat : a < t) (htb : t < b) (p : Point)
    (hpa : p ∈ exposedEdge K (a : Real.Angle))
    (hpb : p ∈ exposedEdge K (b : Real.Angle)) :
    exposedEdge K (t : Real.Angle) = {p} := by
  have hsa : 0 < Real.sin (b - t) / Real.sin (b - a) := div_pos
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith))
  have hsb : 0 < Real.sin (t - a) / Real.sin (b - a) := div_pos
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith))
  have hn := normalVector_eq_positive_combo hab hba hat htb
  have hpt : inner ℝ p (normalVector (t : Real.Angle)) = supportValue K t := by
    rw [hn, inner_add_right, inner_smul_right, inner_smul_right, hpa.2, hpb.2]
    apply le_antisymm
    · have hp_le := inner_le_supportValue K hpa.1 (t : Real.Angle)
      rw [hn, inner_add_right, inner_smul_right, inner_smul_right,
        hpa.2, hpb.2] at hp_le
      exact hp_le
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨z, hzK, rfl⟩
      change inner ℝ z (normalVector (t : Real.Angle)) ≤ _
      rw [hn, inner_add_right, inner_smul_right, inner_smul_right]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_le_supportValue K hzK _) hsa.le)
        (mul_le_mul_of_nonneg_left (inner_le_supportValue K hzK _) hsb.le)
  apply Set.Subset.antisymm
  · intro z hz
    have hza := inner_le_supportValue K hz.1 (a : Real.Angle)
    have hzb := inner_le_supportValue K hz.1 (b : Real.Angle)
    have hzt := hz.2
    change inner ℝ z (normalVector (t : Real.Angle)) = supportValue K t at hzt
    rw [← hpt, hn, inner_add_right, inner_smul_right, inner_smul_right] at hzt
    rw [inner_add_right, inner_smul_right, inner_smul_right, hpa.2, hpb.2] at hzt
    have hzea : inner ℝ z (normalVector (a : Real.Angle)) = supportValue K a := by
      by_contra hne
      have hlt := lt_of_le_of_ne hza hne
      nlinarith
    have hzeb : inner ℝ z (normalVector (b : Real.Angle)) = supportValue K b := by
      by_contra hne
      have hlt := lt_of_le_of_ne hzb hne
      nlinarith
    have hzpa : inner ℝ (z - p) (normalVector (a : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzea, hpa.2, sub_self]
    have hzpb : inner ℝ (z - p) (normalVector (b : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzeb, hpb.2, sub_self]
    have hs : Real.sin (b - a) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
    have htan : inner ℝ (z - p) (tangentVector (a : Real.Angle)) = 0 := by
      have hrot := normalVector_add_real a (b - a)
      rw [show normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) by
            simpa only [add_sub_cancel] using hrot,
        inner_add_right, inner_smul_right, inner_smul_right, hzpa] at hzpb
      simp only [mul_zero, zero_add] at hzpb
      exact (mul_eq_zero.mp hzpb).resolve_left hs
    have hzp : z = p := by
      rw [show z = p + (z - p) by abel,
        ← inner_normalVector_smul_add_inner_tangentVector_smul
          (z - p) (a : Real.Angle), hzpa, htan,
        zero_smul, zero_smul, add_zero, add_zero]
    simp [hzp]
  · intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hpa.1, hpt⟩

private theorem exists_cut_angle
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ t d : ℝ, a < t ∧ t < b ∧ 0 < d ∧
      (edgeVertices K (b : Real.Angle)).2 - (edgeVertices K (a : Real.Angle)).1 =
        d • tangentVector (t : Real.Angle) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨α, hα, hOa⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  obtain ⟨β, hβ, hOb⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  have hchord : Q - P = α • tangentVector (a : Real.Angle) +
      β • tangentVector (b : Real.Angle) := by
    change O = P + α • tangentVector (a : Real.Angle) at hOa
    change O = Q - β • tangentVector (b : Real.Angle) at hOb
    have hQO : Q = O + β • tangentVector (b : Real.Angle) := by
      rw [hOb]
      module
    rw [hQO, hOa]
    module
  let f : ℝ → ℝ := fun s ↦ inner ℝ (Q - P) (normalVector (s : Real.Angle))
  have hf : Continuous f := by
    dsimp only [f]
    rw [show (fun s : ℝ ↦ inner ℝ (Q - P) (normalVector (s : Real.Angle))) =
      fun s ↦ (Q - P) 0 * Real.cos s + (Q - P) 1 * Real.sin s by
        funext s
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        ring]
    fun_prop
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hfa : f a < 0 := by
    dsimp only [f]
    rw [hchord, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    have hid : -(Real.cos a * Real.sin b) + Real.sin a * Real.cos b =
        -Real.sin (b - a) := by rw [Real.sin_sub]; ring
    rw [hid]
    nlinarith
  have hfb : 0 < f b := by
    dsimp only [f]
    rw [hchord, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    have hid : -(Real.cos b * Real.sin a) + Real.sin b * Real.cos a =
        Real.sin (b - a) := by rw [Real.sin_sub]; ring
    rw [hid]
    nlinarith
  have hz : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨hfa.le, hfb.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab.le hf.continuousOn hz
  have hat : a < t := lt_of_le_of_ne ht.1 fun h ↦ by subst t; linarith
  have htb : t < b := lt_of_le_of_ne ht.2 fun h ↦ by subst t; linarith
  let d := inner ℝ (Q - P) (tangentVector (t : Real.Angle))
  have hdecomp : Q - P = d • tangentVector (t : Real.Angle) := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - P) (t : Real.Angle)]
    change inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 at hft
    rw [hft, zero_smul, zero_add]
  have hd : 0 < d := by
    have hqa : inner ℝ (Q - P) (normalVector (a : Real.Angle)) < 0 := hfa
    rw [hdecomp, real_inner_smul_left] at hqa
    have hsinat : 0 < Real.sin (t - a) :=
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
    have hinner : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (a : Real.Angle)) = -Real.sin (t - a) := by
      rw [real_inner_comm]
      have h := sin_sub_eq_neg_inner_normalVector_tangentVector
        (a : Real.Angle) (t : Real.Angle)
      change Real.sin (t - a) =
        -inner ℝ (normalVector (a : Real.Angle)) (tangentVector (t : Real.Angle)) at h
      have h' := h
      linarith
    rw [hinner] at hqa
    nlinarith
  exact ⟨t, d, hat, htb, hd, hdecomp⟩

private theorem mem_segment_of_mem_body_of_eq_cut_inner
    (K : ConvexBody Point) {a b t c d : ℝ} (hat : a < t) (htb : t < b)
    (hba : b < a + Real.pi)
    (P Q z : Point) (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle))
    (hPc : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hzc : inner ℝ z (normalVector (t : Real.Angle)) = c) (hzK : z ∈ K) :
    z ∈ segment ℝ P Q := by
  let r := inner ℝ (z - P) (tangentVector (t : Real.Angle))
  have hnormal : inner ℝ (z - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hzc, hPc, sub_self]
  have hzrepr : z = P + r • tangentVector (t : Real.Angle) := by
    rw [show z = P + (z - P) by abel,
      ← inner_normalVector_smul_add_inner_tangentVector_smul
        (z - P) (t : Real.Angle), hnormal, zero_smul, zero_add]
  have hza := inner_le_supportValue K hzK (a : Real.Angle)
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a := by
    rw [hP]
    exact (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hsinA : 0 < Real.sin (t - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
  have hta : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (a : Real.Angle)) = -Real.sin (t - a) := by
    rw [real_inner_comm]
    have h := sin_sub_eq_neg_inner_normalVector_tangentVector
      (a : Real.Angle) (t : Real.Angle)
    change Real.sin (t - a) =
      -inner ℝ (normalVector (a : Real.Angle)) (tangentVector (t : Real.Angle)) at h
    linarith
  have hr0 : 0 ≤ r := by
    rw [hzrepr, inner_add_left, real_inner_smul_left, hta, hPa] at hza
    nlinarith
  have hzb := inner_le_supportValue K hzK (b : Real.Angle)
  have hQb : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b := by
    rw [hQ]
    exact (edgeVertices_snd_mem K (b : Real.Angle)).2
  have hsinB : 0 < Real.sin (b - t) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith)
  have htbinner : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (b : Real.Angle)) = Real.sin (b - t) := by
    have h := sin_sub_eq_neg_inner_normalVector_tangentVector
      (b : Real.Angle) (t : Real.Angle)
    change Real.sin (t - b) =
      -inner ℝ (normalVector (b : Real.Angle)) (tangentVector (t : Real.Angle)) at h
    rw [real_inner_comm]
    rw [show t - b = -(b - t) by ring, Real.sin_neg] at h
    linarith
  have hQrepr : Q = P + d • tangentVector (t : Real.Angle) := by
    rw [show Q = P + (Q - P) by abel, hdir]
  have hrd : r ≤ d := by
    rw [hzrepr, inner_add_left, real_inner_smul_left, htbinner] at hzb
    have hQsupport := hQb
    rw [hQrepr, inner_add_left, real_inner_smul_left, htbinner] at hQsupport
    rw [← hQsupport] at hzb
    nlinarith
  rw [segment_eq_image']
  refine ⟨r / d, ⟨div_nonneg hr0 hd.le, (div_le_one hd).2 hrd⟩, ?_⟩
  rw [hdir]
  dsimp only
  rw [smul_smul]
  rw [div_mul_cancel₀ r hd.ne', hzrepr]

private theorem exposedEdge_subset_upper_cut
    (K : ConvexBody Point) {a b t c s : ℝ} (hat : a < t) (htb : t < b)
    (hba : b < a + Real.pi) (hs : s ∈ Set.Ioo a b)
    (P Q : Point) (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hPc : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQc : inner ℝ Q (normalVector (t : Real.Angle)) = c) :
    exposedEdge K (s : Real.Angle) ⊆ normalHalfPlane (t : Real.Angle) c true false := by
  intro z hz
  change c ≤ inner ℝ z (normalVector (t : Real.Angle))
  by_cases hst : s = t
  · subst s
    have hp_le := inner_le_supportValue K (edgeVertices_fst_mem K (a : Real.Angle)).1
      (t : Real.Angle)
    rw [← hP, hPc, ← hz.2] at hp_le
    exact hp_le
  rcases lt_or_gt_of_ne hst with hst | hts
  · have hn := normalVector_eq_positive_combo hat (by linarith) hs.1 hst
    have hA : 0 < Real.sin (t - s) / Real.sin (t - a) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hst) (by linarith [hba, hs.1]))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith))
    have hB : 0 < Real.sin (s - a) / Real.sin (t - a) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hs.1) (by linarith))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith))
    by_contra hnot
    have hzt : inner ℝ z (normalVector (t : Real.Angle)) < c := lt_of_not_ge hnot
    have hza := inner_le_supportValue K hz.1 (a : Real.Angle)
    have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a := by
      rw [hP]; exact (edgeVertices_fst_mem K _).2
    have hpK : P ∈ K := by rw [hP]; exact (edgeVertices_fst_mem K _).1
    have hp_le := inner_le_supportValue K hpK (s : Real.Angle)
    rw [← hz.2, hn, inner_add_right, inner_smul_right, inner_smul_right,
      inner_add_right, inner_smul_right, inner_smul_right, hPa, hPc] at hp_le
    nlinarith
  · have hn := normalVector_eq_positive_combo htb (by linarith) hts hs.2
    have hA : 0 < Real.sin (b - s) / Real.sin (b - t) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hs.2) (by linarith))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith))
    have hB : 0 < Real.sin (s - t) / Real.sin (b - t) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hts) (by linarith [hba, hat, hs.2]))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith))
    by_contra hnot
    have hzt : inner ℝ z (normalVector (t : Real.Angle)) < c := lt_of_not_ge hnot
    have hzb := inner_le_supportValue K hz.1 (b : Real.Angle)
    have hQb : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b := by
      rw [hQ]; exact (edgeVertices_snd_mem K _).2
    have hqK : Q ∈ K := by rw [hQ]; exact (edgeVertices_snd_mem K _).1
    have hq_le := inner_le_supportValue K hqK (s : Real.Angle)
    rw [← hz.2, hn, inner_add_right, inner_smul_right, inner_smul_right,
      inner_add_right, inner_smul_right, inner_smul_right, hQc, hQb] at hq_le
    nlinarith

private theorem not_collinear_of_inner_eq_eq_lt
    (P Q O n : Point) (hPQ : P ≠ Q)
    (hPQn : inner ℝ P n = inner ℝ Q n) (hO : inner ℝ P n < inner ℝ O n) :
    ¬Collinear ℝ ({P, Q, O} : Set Point) := by
  intro hcol
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd
    (k := ℝ) ({P, Q, O} : Set Point)).mp hcol
  obtain ⟨rP, hrP⟩ := hv P (by simp)
  obtain ⟨rQ, hrQ⟩ := hv Q (by simp)
  obtain ⟨rO, hrO⟩ := hv O (by simp)
  have hrne : rP ≠ rQ := by
    intro h
    apply hPQ
    rw [hrP, hrQ, h]
  have hvn : inner ℝ v n = 0 := by
    rw [hrP, hrQ, vadd_eq_add, vadd_eq_add, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left] at hPQn
    have : (rP - rQ) * inner ℝ v n = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hrne)
  rw [hrP, hrO, vadd_eq_add, vadd_eq_add, inner_add_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, hvn] at hO
  simp only [mul_zero, zero_add] at hO
  exact hO.false

private theorem exposedEdge_upper_cut_first (K K' : ConvexBody Point)
    (a b t c : ℝ) (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hsub : (K' : Set Point) ⊆ (K : Set Point))
    (hcut : ∀ z ∈ (K' : Set Point), c ≤ inner ℝ z (normalVector (t : Real.Angle)))
    (hPmem : (edgeVertices K (a : Real.Angle)).1 ∈ K')
    (hPc : inner ℝ (edgeVertices K (a : Real.Angle)).1
      (normalVector (t : Real.Angle)) = c) :
    exposedEdge K' (a : Real.Angle) =
      {(edgeVertices K (a : Real.Angle)).1} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (t - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
  have hsupport : supportValue K' (a : Real.Angle) = supportValue K (a : Real.Angle) := by
    apply le_antisymm
    · apply csSup_le (K'.nonempty.image _)
      rintro _ ⟨z, hz, rfl⟩
      exact inner_le_supportValue K (hsub hz) (a : Real.Angle)
    · rw [← (edgeVertices_fst_mem K (a : Real.Angle)).2]
      exact inner_le_supportValue K' hPmem (a : Real.Angle)
  apply Set.Subset.antisymm
  · intro z hz
    have hzKedge : z ∈ exposedEdge K (a : Real.Angle) := by
      refine ⟨hsub hz.1, ?_⟩
      change inner ℝ z (normalVector (a : Real.Angle)) = supportValue K a
      rw [← hsupport]
      exact hz.2
    have hnormal : inner ℝ (z - P) (normalVector (a : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzKedge.2]
      change supportValue K (a : Real.Angle) -
        inner ℝ (edgeVertices K (a : Real.Angle)).1
          (normalVector (a : Real.Angle)) = 0
      rw [(edgeVertices_fst_mem K (a : Real.Angle)).2, sub_self]
    have htangent : inner ℝ (z - P) (tangentVector (a : Real.Angle)) ≤ 0 := by
      rw [inner_sub_left, sub_nonpos]
      change inner ℝ z (tangentVector (a : Real.Angle)) ≤
        inner ℝ (edgeVertices K (a : Real.Angle)).1
          (tangentVector (a : Real.Angle))
      rw [inner_edgeVertices_fst_tangent]
      exact le_csSup ((isCompact_exposedEdge K (a : Real.Angle)).image
        (continuous_id.inner continuous_const) |>.bddAbove) ⟨z, hzKedge, rfl⟩
    have hcut : 0 ≤ inner ℝ (z - P) (normalVector (t : Real.Angle)) := by
      rw [inner_sub_left, hPc]
      exact sub_nonneg.mpr (hcut z hz.1)
    have hrotate : normalVector (t : Real.Angle) =
        Real.cos (t - a) • normalVector (a : Real.Angle) +
          Real.sin (t - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (t - a)
    rw [hrotate, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hcut
    have htangent0 : inner ℝ (z - P) (tangentVector (a : Real.Angle)) = 0 := by
      nlinarith
    have hzP : z = P := by
      rw [show z = P + (z - P) by abel,
        ← inner_normalVector_smul_add_inner_tangentVector_smul
          (z - P) (a : Real.Angle), hnormal, htangent0,
        zero_smul, zero_smul, add_zero, add_zero]
    simp [hzP, P]
  · rintro z rfl
    refine ⟨hPmem, ?_⟩
    change inner ℝ P (normalVector (a : Real.Angle)) = supportValue K' a
    rw [hsupport]
    exact (edgeVertices_fst_mem K (a : Real.Angle)).2

private theorem exposedEdge_upper_cut_last (K K' : ConvexBody Point)
    (a b t c : ℝ) (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hsub : (K' : Set Point) ⊆ (K : Set Point))
    (hcut : ∀ z ∈ (K' : Set Point), c ≤ inner ℝ z (normalVector (t : Real.Angle)))
    (hQmem : (edgeVertices K (b : Real.Angle)).2 ∈ K')
    (hQc : inner ℝ (edgeVertices K (b : Real.Angle)).2
      (normalVector (t : Real.Angle)) = c) :
    exposedEdge K' (b : Real.Angle) =
      {(edgeVertices K (b : Real.Angle)).2} := by
  let Q := (edgeVertices K (b : Real.Angle)).2
  have hsupport : supportValue K' (b : Real.Angle) = supportValue K (b : Real.Angle) := by
    apply le_antisymm
    · apply csSup_le (K'.nonempty.image _)
      rintro _ ⟨z, hz, rfl⟩
      exact inner_le_supportValue K (hsub hz) (b : Real.Angle)
    · rw [← (edgeVertices_snd_mem K (b : Real.Angle)).2]
      exact inner_le_supportValue K' hQmem (b : Real.Angle)
  apply Set.Subset.antisymm
  · intro z hz
    have hzKedge : z ∈ exposedEdge K (b : Real.Angle) := by
      refine ⟨hsub hz.1, ?_⟩
      change inner ℝ z (normalVector (b : Real.Angle)) = supportValue K b
      rw [← hsupport]
      exact hz.2
    have hnormal : inner ℝ (z - Q) (normalVector (b : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzKedge.2]
      change supportValue K (b : Real.Angle) -
        inner ℝ (edgeVertices K (b : Real.Angle)).2
          (normalVector (b : Real.Angle)) = 0
      rw [(edgeVertices_snd_mem K (b : Real.Angle)).2, sub_self]
    have htangent : 0 ≤ inner ℝ (z - Q) (tangentVector (b : Real.Angle)) := by
      rw [inner_sub_left, sub_nonneg]
      change inner ℝ (edgeVertices K (b : Real.Angle)).2
          (tangentVector (b : Real.Angle)) ≤
        inner ℝ z (tangentVector (b : Real.Angle))
      rw [inner_edgeVertices_snd_tangent]
      exact csInf_le ((isCompact_exposedEdge K (b : Real.Angle)).image
        (continuous_id.inner continuous_const) |>.bddBelow) ⟨z, hzKedge, rfl⟩
    have hcut : 0 ≤ inner ℝ (z - Q) (normalVector (t : Real.Angle)) := by
      rw [inner_sub_left, hQc]
      exact sub_nonneg.mpr (hcut z hz.1)
    have hrotate : normalVector (t : Real.Angle) =
        Real.cos (t - b) • normalVector (b : Real.Angle) +
          Real.sin (t - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (t - b)
    have hsinb : Real.sin (t - b) < 0 := by
      rw [show t - b = -(b - t) by ring, Real.sin_neg, neg_lt_zero]
      exact Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith)
    rw [hrotate, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hcut
    have htangent0 : inner ℝ (z - Q) (tangentVector (b : Real.Angle)) = 0 := by
      nlinarith
    have hzQ : z = Q := by
      rw [show z = Q + (z - Q) by abel,
        ← inner_normalVector_smul_add_inner_tangentVector_smul
          (z - Q) (b : Real.Angle), hnormal, htangent0,
        zero_smul, zero_smul, add_zero, add_zero]
    simp [hzQ, Q]
  · rintro z rfl
    refine ⟨hQmem, ?_⟩
    change inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K' b
    rw [hsupport]
    exact (edgeVertices_snd_mem K (b : Real.Angle)).2

theorem convexBoundaryArc_cut (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (P Q O : Point) (hP : P = (edgeVertices K a).1)
    (hQ : Q = (edgeVertices K b).2) (hO : O = supportingIntersection K a b) :
    (P = Q → O = P ∧ convexBoundaryArc K a b = {P}) ∧
    (P ≠ Q → ¬ Collinear ℝ ({P, Q, O} : Set Point) ∧
      ∃ (t c : ℝ) (K' : ConvexBody Point),
        a < t ∧ t < b ∧
        inner ℝ P (normalVector (t : Real.Angle)) = c ∧
        inner ℝ Q (normalVector (t : Real.Angle)) = c ∧
        c < inner ℝ O (normalVector (t : Real.Angle)) ∧
        (K' : Set Point) = (K : Set Point) ∩ normalHalfPlane t c true false ∧
        (∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P}) ∧
        (∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s) ∧
        (∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q}) ∧
        exposedEdge K' (t + Real.pi) = segment ℝ Q P) := by
  subst P
  subst Q
  subst O
  constructor
  · intro hPQ
    have hPa := edgeVertices_fst_mem K (a : Real.Angle)
    have hPb : (edgeVertices K (a : Real.Angle)).1 ∈ exposedEdge K (b : Real.Angle) := by
      rw [hPQ]
      exact edgeVertices_snd_mem K (b : Real.Angle)
    have hO := eq_supportingIntersection_of_mem_endpoint_faces K hab hba
      (edgeVertices K (a : Real.Angle)).1 hPa hPb
    refine ⟨hO, ?_⟩
    have hfaces : ∀ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle) =
        {(edgeVertices K (a : Real.Angle)).1} := by
      intro t ht
      exact exposedEdge_eq_singleton_of_common_endpoint K hab hba ht.1 ht.2 _ hPa hPb
    rw [convexBoundaryArc, hPQ]
    apply Set.Subset.antisymm
    · refine Set.union_subset (Set.union_subset (Set.Subset.rfl) ?_) Set.Subset.rfl
      exact Set.iUnion₂_subset fun t ht ↦ by simpa [← hPQ] using (hfaces t ht).le
    · exact Set.subset_union_left.trans Set.subset_union_left
  · intro hPQ
    let P := (edgeVertices K (a : Real.Angle)).1
    let Q := (edgeVertices K (b : Real.Angle)).2
    let O := supportingIntersection K a b
    obtain ⟨t, d, hat, htb, hd, hdir⟩ := exists_cut_angle K hab hba hPQ
    let c := inner ℝ P (normalVector (t : Real.Angle))
    have hPc : inner ℝ P (normalVector (t : Real.Angle)) = c := rfl
    have hQc : inner ℝ Q (normalVector (t : Real.Angle)) = c := by
      have hdiff : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
        rw [hdir, real_inner_smul_left, real_inner_comm,
          inner_normalVector_tangentVector, mul_zero]
      rw [inner_sub_left, hPc] at hdiff
      linarith
    have hPK : P ∈ K := edgeVertices_fst_mem K (a : Real.Angle) |>.1
    have hQK : Q ∈ K := edgeVertices_snd_mem K (b : Real.Angle) |>.1
    let K' : ConvexBody Point :=
      { carrier := (K : Set Point) ∩ normalHalfPlane (t : Real.Angle) c true false
        convex' := K.convex.inter (convex_normalHalfPlane _ _ true)
        isCompact' := K.isCompact.inter_right (isClosed_normalHalfPlane _ _ true)
        nonempty' := ⟨P, hPK, by change c ≤ _; exact hPc.ge⟩ }
    have hK' : (K' : Set Point) = (K : Set Point) ∩
        normalHalfPlane (t : Real.Angle) c true false := rfl
    obtain ⟨α, hα, hOa⟩ :=
      supportingIntersection_eq_fst_add_pos_tangent K hab hba hPQ
    have hsin : 0 < Real.sin (t - a) :=
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
    have hta : inner ℝ (tangentVector (a : Real.Angle))
        (normalVector (t : Real.Angle)) = Real.sin (t - a) := by
      have h := sin_sub_eq_neg_inner_normalVector_tangentVector
        (t : Real.Angle) (a : Real.Angle)
      change Real.sin (a - t) =
        -inner ℝ (normalVector (t : Real.Angle)) (tangentVector (a : Real.Angle)) at h
      rw [real_inner_comm, show a - t = -(t - a) by ring, Real.sin_neg] at h
      linarith
    have hcO : c < inner ℝ O (normalVector (t : Real.Angle)) := by
      change O = P + α • tangentVector (a : Real.Angle) at hOa
      rw [hOa, inner_add_left, real_inner_smul_left, hta, ← hPc]
      nlinarith
    have hncol : ¬Collinear ℝ ({P, Q, O} : Set Point) :=
      not_collinear_of_inner_eq_eq_lt P Q O (normalVector (t : Real.Angle))
        hPQ (hPc.trans hQc.symm) hcO
    have hPmem : P ∈ K' := ⟨hPK, by change c ≤ _; exact hPc.ge⟩
    have hQmem : Q ∈ K' := ⟨hQK, by change c ≤ _; exact hQc.ge⟩
    have hsupportTerminal :
        supportValue K' ((t + Real.pi : ℝ) : Real.Angle) = -c := by
      apply le_antisymm
      · apply csSup_le (K'.nonempty.image _)
        rintro _ ⟨z, hz, rfl⟩
        have hzcut := hz.2
        change c ≤ inner ℝ z (normalVector (t : Real.Angle)) at hzcut
        rw [normalVector_add_pi]
        change inner ℝ z (-normalVector (t : Real.Angle)) ≤ -c
        rw [inner_neg_right]
        linarith
      · have hp := inner_le_supportValue K' hPmem ((t + Real.pi : ℝ) : Real.Angle)
        rw [normalVector_add_pi, inner_neg_right, hPc] at hp
        exact hp
    have haFace := exposedEdge_upper_cut_first K K' a b t c hat htb hba
      (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.2) hPmem hPc
    have hbFace := exposedEdge_upper_cut_last K K' a b t c hat htb hba
      (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.2) hQmem hQc
    have hangleTerminal :
        ((t - Real.pi : ℝ) : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) := by
      rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      refine ⟨-1, ?_⟩
      norm_num
      ring
    have hPterminalPlus : P ∈ exposedEdge K' ((t + Real.pi : ℝ) : Real.Angle) := by
      refine ⟨hPmem, ?_⟩
      change inner ℝ P (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
        supportValue K' ((t + Real.pi : ℝ) : Real.Angle)
      rw [normalVector_add_pi, inner_neg_right, hsupportTerminal, hPc]
    have hQterminalPlus : Q ∈ exposedEdge K' ((t + Real.pi : ℝ) : Real.Angle) := by
      refine ⟨hQmem, ?_⟩
      change inner ℝ Q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
        supportValue K' ((t + Real.pi : ℝ) : Real.Angle)
      rw [normalVector_add_pi, inner_neg_right, hsupportTerminal, hQc]
    have hPterminalMinus : P ∈ exposedEdge K' ((t - Real.pi : ℝ) : Real.Angle) := by
      rw [hangleTerminal]
      exact hPterminalPlus
    refine ⟨hncol, t, c, K', hat, htb, hPc, hQc, hcO, hK', ?_, ?_, ?_, ?_⟩
    · intro s hs
      rcases eq_or_lt_of_le hs.2 with hsa | hsa
      · subst s
        exact haFace
      · exact exposedEdge_eq_singleton_of_common_endpoint K'
          (by linarith) (by linarith) hs.1 hsa P hPterminalMinus
          (by rw [haFace]; rfl)
    · intro s hs
      have hsub := exposedEdge_subset_upper_cut K hat htb hba hs P Q rfl rfl hPc hQc
      obtain ⟨z₀, hz₀⟩ := exposedEdge_nonempty K (s : Real.Angle)
      have hz₀K' : z₀ ∈ K' := ⟨hz₀.1, hsub hz₀⟩
      have hsupport : supportValue K' (s : Real.Angle) = supportValue K (s : Real.Angle) := by
        apply le_antisymm
        · apply csSup_le (K'.nonempty.image _)
          rintro _ ⟨z, hz, rfl⟩
          exact inner_le_supportValue K hz.1 (s : Real.Angle)
        · rw [← hz₀.2]
          exact inner_le_supportValue K' hz₀K' (s : Real.Angle)
      ext z
      constructor
      · intro hz
        refine ⟨hz.1.1, ?_⟩
        change inner ℝ z (normalVector (s : Real.Angle)) = supportValue K s
        rw [← hsupport]
        exact hz.2
      · intro hz
        refine ⟨⟨hz.1, hsub hz⟩, ?_⟩
        change inner ℝ z (normalVector (s : Real.Angle)) = supportValue K' s
        rw [hsupport]
        exact hz.2
    · intro s hs
      rcases eq_or_lt_of_le hs.1 with hbs | hbs
      · subst s
        exact hbFace
      · exact exposedEdge_eq_singleton_of_common_endpoint K'
          (by linarith) (by linarith) hbs hs.2 Q
          (by rw [hbFace]; rfl) hQterminalPlus
    · have hsupport := hsupportTerminal
      apply Set.Subset.antisymm
      · intro z hz
        have hzcut := hz.1.2
        change c ≤ inner ℝ z (normalVector (t : Real.Angle)) at hzcut
        have hzeq := hz.2
        change inner ℝ z (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
          supportValue K' ((t + Real.pi : ℝ) : Real.Angle) at hzeq
        rw [normalVector_add_pi, inner_neg_right, hsupport] at hzeq
        have hzc : inner ℝ z (normalVector (t : Real.Angle)) = c := by linarith
        rw [segment_symm ℝ]
        exact mem_segment_of_mem_body_of_eq_cut_inner K hat htb hba P Q z rfl rfl
          hd hdir hPc hzc hz.1.1
      · intro z hz
        have hzK : z ∈ K := K.convex.segment_subset hQK hPK hz
        have hzc : inner ℝ z (normalVector (t : Real.Angle)) = c := by
          have hlin := (convex_normalHalfPlane (t : Real.Angle) c true).segment_subset
            (show P ∈ normalHalfPlane (t : Real.Angle) c true false by
              change c ≤ _; exact hPc.ge)
            (show Q ∈ normalHalfPlane (t : Real.Angle) c true false by
              change c ≤ _; exact hQc.ge)
          have hzcut := hlin (show z ∈ segment ℝ P Q by simpa [segment_symm ℝ] using hz)
          rw [segment_eq_image'] at hz
          obtain ⟨u, hu, rfl⟩ := hz
          rw [inner_add_left, inner_smul_left, inner_sub_left, hPc, hQc]
          ring
        refine ⟨⟨hzK, by change c ≤ _; exact hzc.ge⟩, ?_⟩
        change inner ℝ z (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
          supportValue K' ((t + Real.pi : ℝ) : Real.Angle)
        rw [normalVector_add_pi, inner_neg_right, hsupport, hzc]

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
# Convex / Arc Cut Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Set

/-- A supporting chord of a convex-body frontier cuts off a rectifiable oriented arc, and the
closed signed area is the sum of the arc area and the oppositely oriented chord area. -/
theorem exists_rectifiableOrientedArc_of_cut_with_area
    (K : ConvexBody Point) {t c d α β : ℝ} {P Q : Point} {U : Set Point}
    {x : ContinuousBVPaths α β}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K : Set Point)) true x.val)
    (hPQ : P ≠ Q) (hbase : x.val ⟨α, le_rfl, hαβ.le⟩ ∉ segment ℝ P Q)
    (hfrontier : frontier (K : Set Point) = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A + segmentArea Q P := by
  let θ : Real.Angle := (t + Real.pi : ℝ)
  have hhalf : frontier (K : Set Point) ⊆ normalHalfPlane θ (-c) false false := by
    intro z hz
    have hzK : z ∈ K := K.isClosed.frontier_subset hz
    have hzle := inner_le_supportValue K hzK θ
    have hPterm : P ∈ exposedEdge K θ := by
      rw [show exposedEdge K θ = segment ℝ Q P by
        simpa only [θ, Real.Angle.coe_add] using hterminal]
      exact right_mem_segment ℝ Q P
    have hsupp : supportValue K θ = -c := by
      have h := hPterm.2
      change inner ℝ P (normalVector θ) = supportValue K θ at h
      change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = _ at h
      rw [normalVector_add_pi, inner_neg_right, hPt] at h
      linarith
    change inner ℝ z (normalVector θ) ≤ -c
    rwa [hsupp] at hzle
  have hQline : Q ∈ normalLine θ (-c) := by
    change inner ℝ Q (normalVector θ) = -c
    change inner ℝ Q (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hQt]
  have hdir' : P = Q + d • tangentVector θ := by
    have htangent : tangentVector θ = -tangentVector (t : Real.Angle) := by
      ext i
      fin_cases i <;> simp [θ, tangentVector, frame]
    rw [htangent]
    calc
      P = Q - (Q - P) := by module
      _ = Q - d • tangentVector (t : Real.Angle) := by rw [hdir]
      _ = Q + d • -tangentVector (t : Real.Angle) := by module
  exact exists_rectifiableOrientedArc_of_supportingChord_with_area
    hαβ hx P Q hPQ
    hbase hfrontier hinter θ (-c) hhalf hQline d hd hdir'

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
# The outer corner of a convex body as a path of bounded variation

The outer corner of the rotating supporting hallway of a convex body `K` is
`h_K(t) • u_t + h_K(t + π/2) • v_t`.  Support values are Lipschitz in the angle and bounded on a
compact interval, so this expression is a Lipschitz, hence continuous bounded-variation, path on
every compact interval of angles; and it is convex-linear in `K` because support values are.
These are the two hypotheses of Mamikon convexity for the middle summand of the sofa area.
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- The outer corner of a convex body traces a continuous path of bounded variation over every
compact interval of angles. -/
theorem exists_outerCornerBV (K : ConvexBody Point) (a b : ℝ) :
    ∃ γ : ContinuousBVPaths a b, ∀ s : Set.Icc a b,
      γ.val s = (rotatingHallwayParts (K : Set Point) ((s : ℝ) : Real.Angle)).outerCorner := by
  set C := sSup (norm '' (K : Set Point))
  have hC0 : 0 ≤ C := Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg p)
  have hlipn : ∀ x y : ℝ, |supportValue (K : Set Point) (x : Real.Angle) -
      supportValue (K : Set Point) (y : Real.Angle)| ≤ C * |x - y| :=
    abs_supportValue_sub_le_of_isCompact K.nonempty K.isCompact
  have hlipt : ∀ x y : ℝ,
      |supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K : Set Point) ((y + Real.pi / 2 : ℝ) : Real.Angle)| ≤ C * |x - y| := by
    intro x y
    simpa only [add_sub_add_right_eq_sub] using hlipn (x + Real.pi / 2) (y + Real.pi / 2)
  have hcont : Continuous fun x : ℝ ↦
      supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle) :=
    (continuous_supportValue_real K).comp (continuous_id.add_const _)
  obtain ⟨Mn, hMn⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    (continuous_supportValue_real K).continuousOn
  obtain ⟨Mt, hMt⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    hcont.continuousOn
  set M := max (max Mn Mt) 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMn' : ∀ x ∈ Set.Icc a b, |supportValue (K : Set Point) (x : Real.Angle)| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      (hMn x hx).trans ((le_max_left Mn Mt).trans (le_max_left _ 0))
  have hMt' : ∀ x ∈ Set.Icc a b,
      |supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle)| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      (hMt x hx).trans ((le_max_right Mn Mt).trans (le_max_left _ 0))
  exact ⟨continuousBVOfLipschitz _ (lipschitzOnWith_frameCombination
      (D := ⟨2 * (C + M), by linarith⟩) le_rfl hM0 hlipn hlipt hMn' hMt').to_restrict,
    fun s ↦ (outerCorner_eq_support_sum K (s : ℝ)).symm⟩

/-- The outer-corner paths of a convex body may be chosen convex-linearly in the body.  The
barycentric operation on paths is `bvPathCombination`, spelled out here because it is defined
downstream of this module. -/
theorem exists_outerCornerBV_convexLinear (a b : ℝ) :
    ∃ γ : ConvexBody Point → ContinuousBVPaths a b,
      (∀ (K : ConvexBody Point) (s : Set.Icc a b), (γ K).val s =
        (rotatingHallwayParts (K : Set Point) ((s : ℝ) : Real.Angle)).outerCorner) ∧
      IsConvexLinear convexBodyCombination
        (fun r x y ↦ (1 - (r : ℝ)) • x + (r : ℝ) • y) γ := by
  choose γ hγ using fun K : ConvexBody Point ↦ exists_outerCornerBV K a b
  refine ⟨γ, hγ, fun t K L ↦ Subtype.ext (funext fun s ↦ ?_)⟩
  show (γ (convexBodyCombination t K L)).val s =
    ((1 - (t : ℝ)) • (γ K).val + (t : ℝ) • (γ L).val) s
  rw [hγ, show ((1 - (t : ℝ)) • (γ K).val + (t : ℝ) • (γ L).val) s =
      (1 - (t : ℝ)) • (γ K).val s + (t : ℝ) • (γ L).val s from rfl, hγ, hγ]
  simp only [outerCorner_eq_support_sum, supportValue_convexBodyCombination]
  module

end MovingSofa

end

end

end
