/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ZoomLimitEndpoint
public import LeanPool.CIVAxisymmetric.Zoom.OmegaLipschitz

/-!
# Uniform bounds of the rescaled potential vorticity at the moving axis points

Two of the three inputs of the compactness argument `eq:aniso:zoom:finite:compactness` in Step 2
of the proof of `prop:aniso:small`, at the moving axis points `(0, z_n)` of
`eq:aniso:zoom:finite:variables`: on every compact subset `K` of the open half-plane and every
compact set of times `J ⊆ (-∞, -1]`, the rescaled potential vorticities `Ω_n` are eventually
bounded by `2C` (`eq:aniso:zoom:finite:bound`) and eventually Lipschitz in space with a constant
independent of `n` (the first-derivative bounds obtained from
`eq:aniso:zoom:finite:identities` and `eq:aniso:zoom:derivatives`).
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- A compact set of zoomed points with `τ < 0` is eventually mapped into the unit cylinder by
the finite-axis zoom about the moving axis points `(0, zc n)`, `|zc n| ≤ ρ < 1`. -/
theorem eventually_forall_zoomPoint_mem_unitCylinder_moving {h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ) {lam : ℕ → ℝ}
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) (K : Set ((ℝ × ℝ) × ℝ))
    (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ n in atTop, ∀ p ∈ K, zoomPoint (lam n) h (zc n) p ∈ unitCylinder := by
  have hcz : ∀ n, (0 : ℝ) ^ 2 + zc n ^ 2 ≤ ρ ^ 2 := fun n => by
    have := sq_le_sq' (abs_le.mp (hzc n)).1 (abs_le.mp (hzc n)).2
    simpa using this
  have hall := eventually_mem_zoomPointRec_moving hh hρ0 hρ1 (by norm_num : (-1 : ℝ) < 0) hcz
    hlam_lim K hK hKt
  filter_upwards [hall] with n hn p hp
  have hq := hn p hp
  have heq : zoomPointRec (lam n) h 0 (zc n) p = zoomPoint (lam n) h (zc n) p := by
    unfold zoomPointRec zoomPoint; rw [zero_add]
  rw [heq] at hq
  exact ⟨hq.1, hq.2⟩

/-- Eventually `λ_n < 1`, hence `δ_n = λ_n^{2h} ≤ 1`. -/
theorem eventually_lam_lt_one_and_zoomDelta_le_one {h : ℝ} (hh0 : 0 ≤ h) {lam : ℕ → ℝ}
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    ∀ᶠ n in atTop, 0 < lam n ∧ lam n < 1 ∧ lam n ^ (2 * h) ≤ 1 := by
  have hlt : ∀ᶠ n in atTop, lam n < 1 :=
    (hlam_lim.mono_right nhdsWithin_le_nhds).eventually_lt_const (by norm_num)
  have hpos : ∀ᶠ n in atTop, 0 < lam n := hlam_lim.eventually self_mem_nhdsWithin
  filter_upwards [hlt, hpos] with n h1 h0
  exact ⟨h0, h1, Real.rpow_le_one h0.le h1.le (by linarith only [hh0])⟩

/-- `hbdd` for `Ω_n` at the moving axis points: eventually bounded by `2C` on
`K × J`, `K` compact in the open half-plane, `J ⊆ (-∞, -1]` compact. -/
theorem zoomOmega_eventually_bdd {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hC : 0 ≤ C) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    {lam : ℕ → ℝ} (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (J : Set ℝ) (hJ : IsCompact J)
    (hJt : ∀ τ ∈ J, τ ≤ -1) :
    ∀ᶠ n in atTop, ∀ y ∈ K, ∀ τ ∈ J, |zoomOmega (lam n) h (zc n) u (y, τ)| ≤ 2 * C := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  filter_upwards [eventually_forall_zoomPoint_mem_unitCylinder_moving hh hρ0 hρ1 hzc hlam_lim
      (K ×ˢ J) (hK.prod hJ) (fun p hp => by have := hJt p.2 hp.2; linarith only [this]),
    eventually_lam_lt_one_and_zoomDelta_le_one hh.1.le hlam_lim] with n hn hl y hy τ hτ
  exact abs_zoomOmega_le_two_mul_const hl.1 hb hu2 haxi (hn (y, τ) ⟨hy, hτ⟩) hC hl.2.2 hh.1 hh.2
    (hJt τ hτ)

/-- `hlip` for `Ω_n` at the moving axis points: on a compact `K` in the open half-plane and a
compact `J ⊆ (-∞, -1]`, eventually `Ω_n(·, τ)` is Lipschitz on `K` with one constant. -/
theorem zoomOmega_eventually_lipschitzOnWith {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    {lam : ℕ → ℝ} (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hKp : ∀ y ∈ K, 0 < y.1) (J : Set ℝ)
    (hJ : IsCompact J) (hJt : ∀ τ ∈ J, τ ≤ -1) :
    ∃ L : ℝ, ∀ᶠ n in atTop, ∀ τ ∈ J,
      LipschitzOnWith (Real.toNNReal L) (fun y => zoomOmega (lam n) h (zc n) u (y, τ)) K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, Eventually.of_forall fun n τ _ => by rw [hKe]; exact lipschitzOnWith_empty _ _⟩
  obtain ⟨y0, hy0K, hy0min⟩ := hK.exists_isMinOn hKne continuous_fst.continuousOn
  set ε : ℝ := y0.1 with hε
  have hεpos : 0 < ε := hKp y0 hy0K
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM y0 hy0K)
  set Rect : Set (ℝ × ℝ) := Icc ε (M + 1) ×ˢ Icc (-M) M with hRect
  have hKR : K ⊆ Rect := by
    intro y hy
    have hn := hM y hy
    have h1 : |y.1| ≤ M := le_trans (by rw [← Real.norm_eq_abs]; exact norm_fst_le y) hn
    have h2 : |y.2| ≤ M := le_trans (by rw [← Real.norm_eq_abs]; exact norm_snd_le y) hn
    exact ⟨⟨hy0min hy, by linarith only [(abs_le.mp h1).2]⟩, abs_le.mp h2⟩
  have hRc : IsCompact (Rect ×ˢ J) := (isCompact_Icc.prod isCompact_Icc).prod hJ
  refine ⟨2 * C * (2 / ε + 1 / ε ^ 2), ?_⟩
  filter_upwards [eventually_forall_zoomPoint_mem_unitCylinder_moving hh hρ0 hρ1 hzc hlam_lim
      (Rect ×ˢ J) hRc (fun p hp => by have := hJt p.2 hp.2; linarith only [this]),
    eventually_lam_lt_one_and_zoomDelta_le_one hh.1.le hlam_lim] with n hn hl τ hτ
  exact (lipschitzOnWith_zoomOmega hl.1 hb hu hC hh.1.le hh.2.le hl.2.2 hεpos le_rfl
    (hJt τ hτ) (fun y hy => hn (y, τ) ⟨hy, hτ⟩)).mono hKR

end CIV
