/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Motion.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Geometry.ContactGeometry`.
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
# Geometry / Contact Geometry
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology unitInterval

namespace MovingSofa

private theorem inner_tangent_le_fst (K : ConvexBody Point) (t : Real.Angle)
    {p : Point} (hp : p ∈ exposedEdge K t) :
    inner ℝ p (tangentVector t) ≤ inner ℝ (edgeVertices K t).1 (tangentVector t) := by
  rw [inner_edgeVertices_fst_tangent]
  exact le_csSup ((isCompact_exposedEdge K t).image
    (continuous_id.inner continuous_const)).bddAbove ⟨p, hp, rfl⟩

private theorem snd_le_inner_tangent (K : ConvexBody Point) (t : Real.Angle)
    {p : Point} (hp : p ∈ exposedEdge K t) :
    inner ℝ (edgeVertices K t).2 (tangentVector t) ≤ inner ℝ p (tangentVector t) := by
  rw [inner_edgeVertices_snd_tangent]
  exact csInf_le ((isCompact_exposedEdge K t).image
    (continuous_id.inner continuous_const)).bddBelow ⟨p, hp, rfl⟩

private theorem fst_tangent_le_of_mem_exposedEdge_add (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤
      inner ℝ q (tangentVector (t : Real.Angle)) := by
  have hcomp := inner_le_supportValue K (edgeVertices_fst_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqnormal : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  rw [← hqnormal, normalVector_add_real] at hcomp
  simp only [inner_add_right, inner_smul_right] at hcomp
  have hpnormal : inner ℝ (edgeVertices K (t : Real.Angle)).1
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_fst_mem K (t : Real.Angle)).2
  rw [hpnormal] at hcomp
  have hqle := inner_le_supportValue K hq.1 (t : Real.Angle)
  have hsin := Real.sin_pos_of_pos_of_lt_pi hδ.1 (hδ.2.trans (by linarith [Real.pi_pos]))
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hδ.1], hδ.2⟩
  nlinarith

private theorem tendsto_facePoint_right (K : ConvexBody Point) (t : ℝ) (q : ℝ → Point)
    (hq : ∀ s : ℝ, q s ∈ exposedEdge K (s : Real.Angle)) :
    Tendsto q (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) := by
  apply K.isCompact.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun s ↦ (hq s).1)
  intro p hp hcluster
  obtain ⟨s, hqs, hs⟩ := hcluster.exists_seq_tendsto
  have hst : Tendsto s atTop (𝓝 t) := hs.mono_right nhdsWithin_le_nhds
  have hnormal := hqs.inner (𝕜 := ℝ) (continuous_normalVector_real.continuousAt.tendsto.comp hst)
  have hsupport := (continuous_supportValue_real K).continuousAt.tendsto.comp hst
  have hpnormal : inner ℝ p (normalVector (t : Real.Angle)) =
      supportValue K (t : Real.Angle) := by
    apply tendsto_nhds_unique hnormal
    exact hsupport.congr (fun n ↦ (hq (s n)).2.symm)
  have hpface : p ∈ exposedEdge K (t : Real.Angle) := ⟨hp, hpnormal⟩
  have hnear : ∀ᶠ n in atTop, s n ∈ Set.Ioo t (t + Real.pi / 2) :=
    hs.eventually (Ioo_mem_nhdsGT (by linarith [Real.pi_pos]))
  have hle : inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) := by
    apply ge_of_tendsto (hqs.inner tendsto_const_nhds)
    filter_upwards [hnear] with n hn
    have hn' : s n - t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [hn.1, hn.2]
    simpa only [add_sub_cancel, Function.comp_apply] using
      fst_tangent_le_of_mem_exposedEdge_add K t (s n - t) hn'
        (by simpa only [add_sub_cancel, Function.comp_apply] using hq (s n))
  have heq := le_antisymm (inner_tangent_le_fst K (t : Real.Angle) hpface) hle
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle), hpnormal, heq]
  rw [← (edgeVertices_fst_mem K (t : Real.Angle)).2]
  exact inner_normalVector_smul_add_inner_tangentVector_smul _ _

private theorem tangent_le_snd_of_mem_exposedEdge_add (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) := by
  have hcomp := inner_le_supportValue K (edgeVertices_snd_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqnormal : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  rw [← hqnormal, normalVector_add_real] at hcomp
  simp only [inner_add_right, inner_smul_right] at hcomp
  have hpnormal : inner ℝ (edgeVertices K (t : Real.Angle)).2
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_snd_mem K (t : Real.Angle)).2
  rw [hpnormal] at hcomp
  have hqle := inner_le_supportValue K hq.1 (t : Real.Angle)
  have hsin : Real.sin δ < 0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ.2] : 0 < -δ)
      (by linarith [Real.pi_pos, hδ.1] : -δ < Real.pi)
    simpa using h
  have hcos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨hδ.1, by linarith [Real.pi_pos, hδ.2]⟩
  nlinarith

private theorem tendsto_facePoint_left (K : ConvexBody Point) (t : ℝ) (q : ℝ → Point)
    (hq : ∀ s : ℝ, q s ∈ exposedEdge K (s : Real.Angle)) :
    Tendsto q (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  apply K.isCompact.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun s ↦ (hq s).1)
  intro p hp hcluster
  obtain ⟨s, hqs, hs⟩ := hcluster.exists_seq_tendsto
  have hst : Tendsto s atTop (𝓝 t) := hs.mono_right nhdsWithin_le_nhds
  have hnormal := hqs.inner (𝕜 := ℝ) (continuous_normalVector_real.continuousAt.tendsto.comp hst)
  have hsupport := (continuous_supportValue_real K).continuousAt.tendsto.comp hst
  have hpnormal : inner ℝ p (normalVector (t : Real.Angle)) =
      supportValue K (t : Real.Angle) := by
    apply tendsto_nhds_unique hnormal
    exact hsupport.congr (fun n ↦ (hq (s n)).2.symm)
  have hpface : p ∈ exposedEdge K (t : Real.Angle) := ⟨hp, hpnormal⟩
  have hnear : ∀ᶠ n in atTop, s n ∈ Set.Ioo (t - Real.pi / 2) t :=
    hs.eventually (Ioo_mem_nhdsLT (by linarith [Real.pi_pos]))
  have hle : inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) := by
    apply le_of_tendsto (hqs.inner tendsto_const_nhds)
    filter_upwards [hnear] with n hn
    have hn' : s n - t ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ) := by
      constructor <;> linarith [hn.1, hn.2]
    simpa only [add_sub_cancel, Function.comp_apply] using
      tangent_le_snd_of_mem_exposedEdge_add K t (s n - t) hn'
        (by simpa only [add_sub_cancel, Function.comp_apply] using hq (s n))
  have heq := le_antisymm hle (snd_le_inner_tangent K (t : Real.Angle) hpface)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle), hpnormal, heq]
  rw [← (edgeVertices_snd_mem K (t : Real.Angle)).2]
  exact inner_normalVector_smul_add_inner_tangentVector_smul _ _

private theorem intersection_tangent_bounds_right (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤
        (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ ∧
      (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ ≤
        inner ℝ q (tangentVector (t : Real.Angle)) := by
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ.1
    (by linarith [hδ.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos δ := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδ.1, Real.pi_pos], hδ.2⟩).le
  have hp := inner_le_supportValue K (edgeVertices_fst_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqn : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  have hpn : inner ℝ (edgeVertices K (t : Real.Angle)).1
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_fst_mem K (t : Real.Angle)).2
  rw [normalVector_add_real] at hp hqn
  simp only [inner_add_right, inner_smul_right] at hp hqn
  rw [hpn] at hp
  have hqle := mul_le_mul_of_nonneg_left (inner_le_supportValue K hq.1 (t : Real.Angle)) hc
  constructor
  · rw [le_div_iff₀ hs]
    linarith
  · rw [div_le_iff₀ hs]
    linarith

private theorem tendsto_supportingIntersection_right (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) := by
  let r (s : ℝ) := (supportValue K (s : Real.Angle) -
    supportValue K (t : Real.Angle) * Real.cos (s - t)) / Real.sin (s - t)
  have hr : Tendsto r (𝓝[>] t)
      (𝓝 (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)))) := by
    have hq := (tendsto_facePoint_right K t
      (fun s ↦ (edgeVertices K (s : Real.Angle)).1) (fun s ↦ edgeVertices_fst_mem K _)).inner
      (𝕜 := ℝ) (tendsto_const_nhds (x := tangentVector (t : Real.Angle)))
    have hbounds : ∀ᶠ s in 𝓝[>] t,
        inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤ r s ∧
        r s ≤ inner ℝ (edgeVertices K (s : Real.Angle)).1 (tangentVector (t : Real.Angle)) := by
      filter_upwards [Ioo_mem_nhdsGT (show t < t + Real.pi / 2 by linarith [Real.pi_pos])]
        with s hs
      have hδ : s - t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        constructor <;> linarith [hs.1, hs.2]
      simpa only [add_sub_cancel, r] using intersection_tangent_bounds_right K t (s - t) hδ
        (by simpa only [add_sub_cancel] using edgeVertices_fst_mem K (s : Real.Angle))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
      (hbounds.mono fun _ h ↦ h.1) (hbounds.mono fun _ h ↦ h.2)
  have hz := (tendsto_const_nhds
    (x := supportValue K (t : Real.Angle) • normalVector (t : Real.Angle))).add (hr.smul
    (tendsto_const_nhds (x := tangentVector (t : Real.Angle))))
  have hpnormal := (edgeVertices_fst_mem K (t : Real.Angle)).2
  change inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) =
    supportValue K (t : Real.Angle) at hpnormal
  have heq := inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K (t :
    Real.Angle)).1 (t : Real.Angle)
  rw [hpnormal] at heq
  simpa only [supportingIntersection, ← Real.Angle.coe_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe, heq, r] using hz

private theorem intersection_tangent_bounds_left (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ ≤
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) ∧
      inner ℝ q (tangentVector (t : Real.Angle)) ≤
        (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ := by
  have hs : Real.sin δ < 0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ.2] : 0 < -δ)
      (by linarith [hδ.1, Real.pi_pos] : -δ < Real.pi)
    simpa using h
  have hc : 0 ≤ Real.cos δ := (Real.cos_pos_of_mem_Ioo
    ⟨hδ.1, by linarith [hδ.2, Real.pi_pos]⟩).le
  have hp := inner_le_supportValue K (edgeVertices_snd_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqn : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  have hpn : inner ℝ (edgeVertices K (t : Real.Angle)).2
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_snd_mem K (t : Real.Angle)).2
  rw [normalVector_add_real] at hp hqn
  simp only [inner_add_right, inner_smul_right] at hp hqn
  rw [hpn] at hp
  have hqle := mul_le_mul_of_nonneg_left (inner_le_supportValue K hq.1 (t : Real.Angle)) hc
  constructor
  · rw [div_le_iff_of_neg hs]
    linarith
  · rw [le_div_iff_of_neg hs]
    linarith

private theorem tendsto_supportingIntersection_left_aux (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  let r (s : ℝ) := (supportValue K (s : Real.Angle) -
    supportValue K (t : Real.Angle) * Real.cos (s - t)) / Real.sin (s - t)
  have hr : Tendsto r (𝓝[<] t)
      (𝓝 (inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)))) := by
    have hq := (tendsto_facePoint_left K t
      (fun s ↦ (edgeVertices K (s : Real.Angle)).2) (fun s ↦ edgeVertices_snd_mem K _)).inner
      (𝕜 := ℝ) (tendsto_const_nhds (x := tangentVector (t : Real.Angle)))
    have hbounds : ∀ᶠ s in 𝓝[<] t,
        r s ≤ inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) ∧
        inner ℝ (edgeVertices K (s : Real.Angle)).2 (tangentVector (t : Real.Angle)) ≤ r s := by
      filter_upwards [Ioo_mem_nhdsLT (show t - Real.pi / 2 < t by linarith [Real.pi_pos])]
        with s hs
      have hδ : s - t ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ) := by
        constructor <;> linarith [hs.1, hs.2]
      simpa only [add_sub_cancel, r] using intersection_tangent_bounds_left K t (s - t) hδ
        (by simpa only [add_sub_cancel] using edgeVertices_snd_mem K (s : Real.Angle))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hq tendsto_const_nhds
      (hbounds.mono fun _ h ↦ h.2) (hbounds.mono fun _ h ↦ h.1)
  have hz := (tendsto_const_nhds
    (x := supportValue K (t : Real.Angle) • normalVector (t : Real.Angle))).add (hr.smul
    (tendsto_const_nhds (x := tangentVector (t : Real.Angle))))
  have hpnormal := (edgeVertices_snd_mem K (t : Real.Angle)).2
  change inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
    supportValue K (t : Real.Angle) at hpnormal
  have heq := inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K (t :
    Real.Angle)).2 (t : Real.Angle)
  rw [hpnormal] at heq
  simpa only [supportingIntersection, ← Real.Angle.coe_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe, heq, r] using hz

/-- Both face endpoints and the supporting intersections have the stated one-sided limits. -/
theorem contact_oneSided_limits (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1)
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) ∧
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).2)
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) ∧
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) ∧
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1)
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) ∧
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).2)
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) ∧
    Tendsto (fun s : ℝ ↦ supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  refine ⟨tendsto_facePoint_right K t _ (fun s ↦ edgeVertices_fst_mem K _),
    tendsto_facePoint_right K t _ (fun s ↦ edgeVertices_snd_mem K _),
    tendsto_supportingIntersection_right K t,
    tendsto_facePoint_left K t _ (fun s ↦ edgeVertices_fst_mem K _),
    tendsto_facePoint_left K t _ (fun s ↦ edgeVertices_snd_mem K _), ?_⟩
  apply (tendsto_supportingIntersection_left_aux K t).congr'
  filter_upwards [Ioo_mem_nhdsLT (show t - Real.pi / 2 < t by linarith [Real.pi_pos])]
    with s hs
  apply supportingIntersection_comm
  have hpos : 0 < Real.sin (t - s) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hs.2]) (by linarith [hs.1, Real.pi_pos])
  rw [show s - t = -(t - s) by ring, Real.sin_neg]
  exact neg_ne_zero.mpr hpos.ne'

end MovingSofa

end

end

end
