/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.PlurifinePullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshConvexCone

/-! Actual local real-PSH extensions for source plurifine domain compatibility. -/

@[expose] public section

namespace SGPT.PSH

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {n : ℕ}

/-- Actual real coercion commutes with the existing generic collar maximum. -/
theorem coe_gluedMax {U : Set (ComplexModel n)} (f b : ComplexModel n → ℝ) :
    (fun z ↦ ((SGPT.Foundations.Analysis.gluedMax U f b z : ℝ) : EReal)) =
      SGPT.Foundations.Analysis.gluedMax U (fun z ↦ (f z : EReal)) (fun z ↦ (b z : EReal)) := by
  classical
  funext z
  by_cases hz : z ∈ U
  · rw [gluedMax_eq_max hz, gluedMax_eq_max hz]
    rcases le_total (f z) (b z) with h | h
    · simp only [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
    · simp only [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h)]
  · simp only [SGPT.Foundations.Analysis.gluedMax, hz, ite_false]

/-- Reuse the genuine existing PSH collar theorem for actual real branches. -/
theorem real_gluedMax_plurisubharmonic {U U' : Set (ComplexModel n)}
    {f b : ComplexModel n → ℝ} (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hcollar : ∀ z ∈ U \ U', f z ≤ b z)
    (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) U)
    (hb : PlurisubharmonicOn (fun z ↦ (b z : EReal)) univ) :
    PlurisubharmonicOn (fun z ↦ ((SGPT.Foundations.Analysis.gluedMax U f b z : ℝ) : EReal))
      univ := by
  rw [coe_gluedMax]
  exact gluedMax_plurisubharmonic hU hclosure
    (fun z hz ↦ EReal.coe_le_coe_iff.mpr (hcollar z hz)) hf hb

/-- Genuine real USC follows from the actual finite real PSH values. -/
theorem real_upperSemicontinuousOn_of_psh {U : Set (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) U) :
    UpperSemicontinuousOn f U := by
  intro z hz a ha
  filter_upwards [hf.upperSemicontinuousOn z hz (a : EReal)
    (EReal.coe_lt_coe_iff.mpr ha)] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

/-- Genuine compact upper bounds, produced rather than assumed for extensions. -/
theorem exists_real_psh_compact_upper_bound {U K : Set (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) U)
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ C : ℝ, ∀ z ∈ K, f z ≤ C := by
  obtain ⟨C, hC⟩ := ((real_upperSemicontinuousOn_of_psh hf).mono hKU).bddAbove_of_isCompact hK
  exact ⟨C, fun z hz ↦ hC ⟨z, hz, rfl⟩⟩

/-- A genuine positive quadratic barrier in the actual shifted complex model. -/
theorem quadratic_barrier_plurisubharmonic (x : ComplexModel n) {q : ℝ}
    (hq : 0 < q) (c : ℝ) :
    PlurisubharmonicOn (fun z ↦ ((q * ‖z - x‖ ^ 2 + c : ℝ) : EReal)) univ := by
  have hn : PlurisubharmonicOn (fun z ↦ ((‖z - x‖ ^ 2 : ℝ) : EReal)) univ := by
    simpa only [ContinuousLinearMap.id_apply, Set.preimage_univ, neg_add_eq_sub] using
      ((discPshOn_norm_sq univ).plurisubharmonicOn isOpen_univ).comp_affine
        (ContinuousLinearMap.id ℂ (ComplexModel n)) (-x)
  have hc : PlurisubharmonicOn (fun _ : ComplexModel n ↦ (c : EReal)) univ :=
    fun z _ ↦ plurisubharmonicAt_const (c : EReal) (EReal.coe_ne_top c) z
  simpa only [EReal.coe_add, EReal.coe_mul] using (hn.const_mul hq).add hc

/-- A real local PSH superlevel has a genuine global PSH extension near each
of its points. The extension is manufactured using a quadratic collar. -/
theorem exists_real_psh_superlevel_extension {V : Set (ComplexModel n)}
    (hV : IsOpen V) {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) V)
    {x : ComplexModel n} (hx : x ∈ V) {a : ℝ} (ha : a < f x) :
    ∃ (g : ComplexModel n → ℝ) (N : Set (ComplexModel n)),
      PlurisubharmonicOn (fun z ↦ ((g z : ℝ) : EReal)) univ ∧
      g x = f x ∧ IsOpen N ∧ x ∈ N ∧ N ⊆ V ∧
      ∀ z ∈ N, a < g z → a < f z := by
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hx)
  obtain ⟨C, hC⟩ := exists_real_psh_compact_upper_bound hf (isCompact_closedBall x r) hrV
  let M : ℝ := max C a - a + 2
  have hM : 0 < M := by dsimp [M]; have := le_max_right C a; linarith
  have hhalf : 0 < r / 2 := by positivity
  let q : ℝ := M / (r / 2) ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqr : q * (r / 2) ^ 2 = M := by
    dsimp [q]
    exact div_mul_cancel₀ M (pow_ne_zero 2 hhalf.ne')
  let b : ComplexModel n → ℝ := fun z ↦ q * ‖z - x‖ ^ 2 + (a - 1)
  have hb : PlurisubharmonicOn (fun z ↦ (b z : EReal)) univ :=
    quadratic_barrier_plurisubharmonic x hq (a - 1)
  have hcollar : ∀ z ∈ ball x r \ ball x (r / 2), f z ≤ b z := by
    intro z hz
    have hn : r / 2 ≤ ‖z - x‖ := by
      simpa only [mem_ball, dist_eq_norm, not_lt] using hz.2
    have hsq : (r / 2) ^ 2 ≤ ‖z - x‖ ^ 2 := by
      nlinarith [norm_nonneg (z - x)]
    have hmul := mul_le_mul_of_nonneg_left hsq hq.le
    have hfc := hC z (ball_subset_closedBall hz.1)
    have hCc := le_max_left C a
    dsimp only [b]
    dsimp only [M] at hqr
    nlinarith
  have hclosure : closure (ball x (r / 2)) ⊆ ball x r :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  let g := SGPT.Foundations.Analysis.gluedMax (ball x r) f b
  have hg : PlurisubharmonicOn (fun z ↦ ((g z : ℝ) : EReal)) univ :=
    real_gluedMax_plurisubharmonic isOpen_ball hclosure hcollar
      (hf.mono (ball_subset_closedBall.trans hrV)) hb
  have hbx : b x = a - 1 := by simp [b]
  have hxball : x ∈ ball x r := mem_ball_self hr
  have hgx : g x = f x := by
    dsimp only [g]
    rw [SGPT.Foundations.Analysis.gluedMax_eq_max hxball]
    exact max_eq_left (by rw [hbx]; linarith)
  let N : Set (ComplexModel n) := ball x r ∩ {z | b z < a}
  have hbc : Continuous b := by dsimp [b]; fun_prop
  refine ⟨g, N, hg, hgx, isOpen_ball.inter (isOpen_lt hbc continuous_const),
    ⟨hxball, by change b x < a; rw [hbx]; linarith⟩,
    fun z hz ↦ hrV (ball_subset_closedBall hz.1), ?_⟩
  intro z hz hgz
  have hgzeq : g z = max (f z) (b z) :=
    SGPT.Foundations.Analysis.gluedMax_eq_max hz.1
  rw [hgzeq, lt_max_iff] at hgz
  exact hgz.resolve_right (not_lt.mpr hz.2.le)

/-- Every actual local real PSH strict superlevel is fine-open in the
independently defined topology of any containing open domain. -/
theorem isOpen_domainPlurifine_local_real_superlevel (Ω : Opens (ComplexModel n))
    {V : Set (ComplexModel n)} (hV : IsOpen V)
    {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) V) (a : ℝ) :
    IsOpen[domainPlurifineTopology Ω] {z : Ω | z.val ∈ V ∧ a < f z.val} := by
  let : TopologicalSpace Ω := domainPlurifineTopology Ω
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨g, N, hg, hgx, hN, hxN, hNV, hgf⟩ :=
    exists_real_psh_superlevel_extension hV hf hx.1 hx.2
  let T : Set Ω := (Subtype.val ⁻¹' N) ∩ {z : Ω | a < g z.val}
  have hTf : IsOpen T :=
    (SGPT.Foundations.Analysis.Pending.PlurifineEuclideanComparison.isOpen_euclidean hN).inter
      (SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.isOpen_realPsh_superlevel
        (hg.mono (subset_univ _)) a)
  refine ⟨T, ?_, hTf, hxN, ?_⟩
  · intro z hz
    exact ⟨hNV hz.1, hgf z.val hz.1 hz.2⟩
  · simpa only [mem_ofPred_eq, hgx] using hx.2

/-- Actual local real PSH sublevels are already ordinary open. -/
theorem isOpen_domainPlurifine_local_real_sublevel (Ω : Opens (ComplexModel n))
    {V : Set (ComplexModel n)} (hV : IsOpen V)
    {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) V) (a : ℝ) :
    IsOpen[domainPlurifineTopology Ω] {z : Ω | z.val ∈ V ∧ f z.val < a} := by
  obtain ⟨W, hW, hVW⟩ := upperSemicontinuousOn_iff_preimage_Iio.mp
    (real_upperSemicontinuousOn_of_psh hf) a
  have hO : IsOpen (V ∩ f ⁻¹' Iio a) := by rw [hVW]; exact hV.inter hW
  exact SGPT.Foundations.Analysis.Pending.PlurifineEuclideanComparison.isOpen_euclidean hO

/-- SGPT cor:pf_compatible: both independently defined domain topologies
agree with the actual subspace topology. No connectedness or nonemptiness
is needed for this stronger result. -/
theorem domainPlurifine_induced_eq {Ω₁ Ω₂ : Opens (ComplexModel n)}
    (h₁₂ : (Ω₁ : Set (ComplexModel n)) ⊆ Ω₂) :
    domainPlurifineTopology Ω₁ = induced (holomorphicDomainMap (F := id) h₁₂)
      (domainPlurifineTopology Ω₂) := by
  apply le_antisymm
  · exact continuous_iff_le_induced.mp
      (continuous_domainPlurifine_holomorphic differentiable_id.differentiableOn h₁₂)
  · apply (SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.topology_universal Ω₁
      (induced (holomorphicDomainMap (F := id) h₁₂) (domainPlurifineTopology Ω₂))).mpr
    intro f
    let : TopologicalSpace Ω₁ := induced (holomorphicDomainMap (F := id) h₁₂)
      (domainPlurifineTopology Ω₂)
    let : TopologicalSpace Ω₂ := domainPlurifineTopology Ω₂
    apply OrderTopology.continuous_iff.mpr
    intro a
    constructor
    · apply isOpen_induced_iff.mpr
      refine ⟨{z : Ω₂ | z.val ∈ (Ω₁ : Set (ComplexModel n)) ∧ a < f.val z.val},
        isOpen_domainPlurifine_local_real_superlevel Ω₂ Ω₁.isOpen f.property a, ?_⟩
      ext z
      change (z.val ∈ (Ω₁ : Set (ComplexModel n)) ∧ a < f.val z.val) ↔ a < f.val z.val
      exact and_iff_right z.property
    · apply isOpen_induced_iff.mpr
      refine ⟨{z : Ω₂ | z.val ∈ (Ω₁ : Set (ComplexModel n)) ∧ f.val z.val < a},
        isOpen_domainPlurifine_local_real_sublevel Ω₂ Ω₁.isOpen f.property a, ?_⟩
      ext z
      change (z.val ∈ (Ω₁ : Set (ComplexModel n)) ∧ f.val z.val < a) ↔ f.val z.val < a
      exact and_iff_right z.property

end SGPT.PSH
