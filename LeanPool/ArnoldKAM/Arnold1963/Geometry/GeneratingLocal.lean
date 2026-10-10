/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingImplicit

/-!
Local analytic canonical branches of the generating equation. The neighborhood is open in
the ambient target space; the branch properties are conclusions of the construction.
-/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963

theorem generating_small_of_arnold {n : ℕ} (hn : 0 < n) {r : ℝ≥0} (hr : 0 < r)
    {M : ℝ} (hM : M < (r : ℝ) ^ 2 / (16 * n)) : M / r / r < 1 / 4 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (4 : ℝ) ≤ 16 * n := by linarith
  have hb : M < (r : ℝ) ^ 2 / 4 := hM.trans_le
    (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hd)
  apply (div_lt_iff₀ (show (0 : ℝ) < r from hr)).2
  apply (div_lt_iff₀ (show (0 : ℝ) < r from hr)).2
  nlinarith

/-- A local analytic inverse branch of the generating input map around a target point. -/
structure GeneratingLocalBranch {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (G U : Set (ComplexSpace n)) (r : ℝ≥0) (M : ℝ) (y : ComplexPhaseSpace n) where
  /-- The local inverse function for the generating input map. -/
  inverse : ComplexPhaseSpace n → ComplexPhaseSpace n
  /-- The open target neighborhood on which the inverse branch is analytic. -/
  neighborhood : Set (ComplexPhaseSpace n)
  isOpen_neighborhood : IsOpen neighborhood
  center_mem : y ∈ neighborhood
  analytic_inverse : AnalyticOnNhd ℂ inverse neighborhood
  implicit_eq : ∀ z ∈ neighborhood, generatingInput S (inverse z) = z
  source_mem : MapsTo inverse neighborhood (G ×ˢ U)
  analytic_transform : AnalyticOnNhd ℂ (generatingOutput S ∘ inverse) neighborhood
  canonical : CanonicalOn (generatingOutput S ∘ inverse) neighborhood
  mapsTo : MapsTo (generatingOutput S ∘ inverse) neighborhood (G ×ˢ U)
  derivative_lt_two : ∀ z ∈ neighborhood, ‖fderiv ℂ (generatingOutput S ∘ inverse) z‖ < 2
  displacement_center : ‖generatingOutput S (inverse y) - y‖ ≤ M / r
  root_in_ball : (inverse y).2 ∈ closedBall y.2 r

theorem exists_generatingLocalBranch {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {G U : Set (ComplexSpace n)} {r : ℝ≥0} {M : ℝ} {P Q : ComplexSpace n}
    (hr : 0 < r) (hS : AnalyticOnNhd ℂ S (G ×ˢ U))
    (hM : NormBoundOn S (G ×ˢ U) M) (hsmall : M / r / r < 1 / 4)
    (hP : P ∈ erosion G (r + r)) (hQ : Q ∈ erosion U ((r + r) + r)) :
    Nonempty (GeneratingLocalBranch S G U r M (P, Q)) := by
  have hsmall1 : M / r / r < 1 := lt_trans hsmall (by norm_num)
  obtain ⟨q, ⟨hq, he⟩, _⟩ := existsUnique_generating_root hr hS hM hsmall1 hP hQ
  have hx := generating_ball_buffer hP hQ hq
  have hAx := hS (P, q) (erosion_subset _ _ hx)
  have hF : generatingInput S (P, q) = (P, Q) := Prod.ext rfl he
  have hpB := norm_fderiv_pGradient_le hr hS hM hx
  have hqB := norm_fderiv_qGradient_le hr hS hM hx
  obtain ⟨g, hg, hgy, hright⟩ := exists_analytic_local_inverse
    (analyticAt_generatingInput hAx)
    ((norm_fderiv_generatingInput_sub_id_le hAx).trans_lt (hpB.trans_lt hsmall1))
  rw [hF] at hg hgy hright
  have hSg : AnalyticAt ℂ S (g (P, Q)) := by rw [hgy]; exact hAx
  have hB : AnalyticAt ℂ (generatingOutput S ∘ g) (P, Q) :=
    (analyticAt_generatingOutput hSg).comp hg
  have hder : ‖fderiv ℂ (generatingOutput S ∘ g) (P, Q)‖ < 2 :=
    (norm_fderiv_generating_branch_le hSg hg hright
      (by rw [hgy]; exact hpB.trans hsmall.le)
      (by rw [hgy]; exact hqB.trans hsmall.le)).trans_lt (by norm_num)
  have hbounds := generating_root_bounds hr hS hM hsmall1.le hP hQ hq he
  have hε : M / r ≤ (r : ℝ) := by
    simpa using (div_le_iff₀ (show (0 : ℝ) < r from hr)).mp hsmall1.le
  have hout : generatingOutput S (P, q) ∈ erosion (G ×ˢ U) r := by
    apply prod_mem_erosion
    · apply mem_erosion_of_dist_le hP
      have hb := norm_qGradient_le_div hr hS hM
        (erosion_antitone_radius _ (show r ≤ r + r from le_add_self) hx)
      simpa [generatingOutput, dist_eq_norm] using hb.trans hε
    · exact erosion_antitone_radius U (show r ≤ r + r from le_add_self)
        (mem_erosion_of_dist_le hQ hq)
  have hin_nhds : G ×ˢ U ∈ 𝓝 (g (P, Q)) := by
    rw [hgy]
    exact mem_of_superset (closedBall_mem_nhds _ (show (0 : ℝ) < r + r by positivity)) hx
  have hout_nhds : G ×ˢ U ∈ 𝓝 ((generatingOutput S ∘ g) (P, Q)) := by
    change G ×ˢ U ∈ 𝓝 (generatingOutput S (g (P, Q)))
    rw [hgy]
    exact mem_of_superset (closedBall_mem_nhds _ (show (0 : ℝ) < r from hr)) hout
  have hlocal : ∀ᶠ z in 𝓝 (P, Q),
      AnalyticAt ℂ g z ∧ generatingInput S (g z) = z ∧ g z ∈ G ×ˢ U ∧
      AnalyticAt ℂ (generatingOutput S ∘ g) z ∧
      CanonicalAt (generatingOutput S ∘ g) z ∧
      (generatingOutput S ∘ g) z ∈ G ×ˢ U ∧
      ‖fderiv ℂ (generatingOutput S ∘ g) z‖ < 2 := by
    filter_upwards [hg.eventually_analyticAt, hright, hright.eventually_nhds,
      hg.continuousAt hin_nhds, hB.eventually_analyticAt, hB.continuousAt hout_nhds,
      hB.fderiv.continuousAt.norm (gt_mem_nhds hder)] with z hgz hz hzloc hzin hBz hzout hd
    exact ⟨hgz, hz, hzin, hBz, canonicalAt_generating_branch (hS _ hzin) hgz hzloc, hzout, hd⟩
  obtain ⟨V, hV, hVo, hyV⟩ := _root_.eventually_nhds_iff.mp hlocal
  refine ⟨{
    inverse := g
    neighborhood := V
    isOpen_neighborhood := hVo
    center_mem := hyV
    analytic_inverse := fun z hz => (hV z hz).1
    implicit_eq := fun z hz => (hV z hz).2.1
    source_mem := fun z hz => (hV z hz).2.2.1
    analytic_transform := fun z hz => (hV z hz).2.2.2.1
    canonical := fun z hz => (hV z hz).2.2.2.2.1
    mapsTo := fun z hz => (hV z hz).2.2.2.2.2.1
    derivative_lt_two := fun z hz => (hV z hz).2.2.2.2.2.2
    displacement_center := ?_
    root_in_ball := ?_ }⟩
  · rw [hgy]; exact hbounds.1
  · rw [hgy]; exact hq

theorem AnalyticPhaseFunction.exists_generatingLocalBranch {n : ℕ}
    {G : Set (ComplexSpace n)} {ρ r : ℝ≥0} (S : AnalyticPhaseFunction n G ρ)
    (hr : 0 < r) (hsmall : S.uniformNorm / r / r < 1 / 4)
    {P Q : ComplexSpace n} (hP : P ∈ erosion G (r + r))
    (hQ : Q ∈ erosion (angleStrip n ρ) ((r + r) + r)) :
    Nonempty (GeneratingLocalBranch S.toFun G (angleStrip n ρ) r S.uniformNorm (P, Q)) :=
  KamProject.Arnold1963.exists_generatingLocalBranch hr S.analytic
    (S.norm_le_iff.mp le_rfl) hsmall hP hQ

theorem generatingLocalBranch_center_unique {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {G U : Set (ComplexSpace n)} {r : ℝ≥0} {M : ℝ} {P Q : ComplexSpace n}
    (hr : 0 < r) (hS : AnalyticOnNhd ℂ S (G ×ˢ U))
    (hM : NormBoundOn S (G ×ˢ U) M) (hsmall : M / r / r < 1)
    (hP : P ∈ erosion G (r + r)) (hQ : Q ∈ erosion U ((r + r) + r))
    (b c : GeneratingLocalBranch S G U r M (P, Q)) : b.inverse (P, Q) = c.inverse (P, Q) := by
  have hb := b.implicit_eq _ b.center_mem
  have hc := c.implicit_eq _ c.center_mem
  have hbp : (b.inverse (P, Q)).1 = P := congrArg Prod.fst hb
  have hcp : (c.inverse (P, Q)).1 = P := congrArg Prod.fst hc
  obtain ⟨q, hq, hu⟩ := existsUnique_generating_root hr hS hM hsmall hP hQ
  have heb : (b.inverse (P, Q)).2 + pGradient S (P, (b.inverse (P, Q)).2) = Q := by
    rw [show (P, (b.inverse (P, Q)).2) = b.inverse (P, Q) from Prod.ext hbp.symm rfl]
    exact congrArg Prod.snd hb
  have hec : (c.inverse (P, Q)).2 + pGradient S (P, (c.inverse (P, Q)).2) = Q := by
    rw [show (P, (c.inverse (P, Q)).2) = c.inverse (P, Q) from Prod.ext hcp.symm rfl]
    exact congrArg Prod.snd hc
  exact Prod.ext (hbp.trans hcp.symm)
    ((hu _ ⟨b.root_in_ball, heb⟩).trans (hu _ ⟨c.root_in_ball, hec⟩).symm)

namespace GeneratingLocalBranch
variable {n : ℕ} {S : ComplexPhaseSpace n → ℂ} {G U : Set (ComplexSpace n)}
  {r : ℝ≥0} {M : ℝ} {y : ComplexPhaseSpace n}

/-- The generating output map evaluated through the local inverse branch. -/
def transform (b : GeneratingLocalBranch S G U r M y) := generatingOutput S ∘ b.inverse

theorem equations (b : GeneratingLocalBranch S G U r M y) {z : ComplexPhaseSpace n}
    (hz : z ∈ b.neighborhood) :
    (b.transform z).1 = z.1 + qGradient S (z.1, (b.transform z).2) ∧
      z.2 = (b.transform z).2 + pGradient S (z.1, (b.transform z).2) := by
  have he := b.implicit_eq z hz
  have hp := congrArg (fun x : ComplexPhaseSpace n => x.1) he
  change (b.inverse z).1 = z.1 at hp
  have heq : b.inverse z = (z.1, (b.inverse z).2) := Prod.ext hp rfl
  constructor
  · change (b.inverse z).1 + qGradient S (b.inverse z) = _
    simp only [transform, Function.comp_apply, generatingOutput]
    rw [hp, heq]
  · change z.2 = (b.inverse z).2 + pGradient S (z.1, (b.inverse z).2)
    rw [← heq]
    exact (congrArg Prod.snd he).symm

end GeneratingLocalBranch

end KamProject.Arnold1963
