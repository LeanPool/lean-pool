/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsOpen
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HolderGluing
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact gluing of good-point representatives

This file proves the compact-set and bad-point conclusions of
`lem:good-open-glue`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem goodPointVecNorm_sub_le_glue (a b : Vec3) :
    vec3EuclideanNorm (a - b) ≤ vec3EuclideanNorm a + vec3EuclideanNorm b := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- A point in the closed compact region which is not good satisfies the
lower bound in `eq:bad-point-lower-bound` at every admissible radius. -/
theorem goodPoint_badPoint_lower_bound_closed
    {ε₀ : ℝ} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {R : ℝ}
    (hz : vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
      z.2 ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hRpos : 0 < R)
    (hRdomain : goodPointPastCylinder z.1 z.2 R ⊆ goodPointDomain)
    (hnot : ¬ IsGoodPoint ε₀ u p z) :
    ENNReal.ofReal (R⁻¹ ^ 2) * goodPointEnergy u p z.1 z.2 R ≥
      ENNReal.ofReal (ε₀ / 8) := by
  by_contra hlarge
  have hsmall : ENNReal.ofReal (R⁻¹ ^ 2) * goodPointEnergy u p z.1 z.2 R <
      ENNReal.ofReal (ε₀ / 8) := lt_of_not_ge hlarge
  obtain ⟨r, hrpos, hrR, hsmallr⟩ :=
    exists_smaller_radius_preserving_goodPoint_smallness hRpos hsmall
  have hzclosed : z ∈ goodPointClosedTopDomain := by
    constructor
    · change vec3EuclideanNorm (z.1 - 0) < 1
      linarith only [hz.1]
    · constructor
      · linarith only [hz.2.1]
      · exact hz.2.2
  have hadmiss := goodPoint_smaller_radius_admissible
    hzclosed hRpos hrpos hrR hRdomain
  have hsubset : parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 R := by
    intro q hq
    rcases (mem_parabolicCylinder).mp hq with ⟨hqx, hqtlo, hqthi⟩
    have hlow : z.2 - R ^ 2 < z.2 - r ^ 2 := by
      nlinarith only [hrR, hrpos, hRpos]
    exact (mem_parabolicCylinder).mpr
      ⟨hqx.trans hrR, hlow.trans hqtlo, hqthi⟩
  have henergy : goodPointEnergy u p z.1 z.2 r ≤
      goodPointEnergy u p z.1 z.2 R := by
    unfold goodPointEnergy
    exact lintegral_mono_set hsubset
  have hsmallr' : ENNReal.ofReal (r⁻¹ ^ 2) *
      goodPointEnergy u p z.1 z.2 r < ENNReal.ofReal (ε₀ / 8) := by
    have hmul : ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p z.1 z.2 r ≤
        ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p z.1 z.2 R := by
      gcongr
    exact hmul.trans_lt hsmallr
  exact hnot ⟨hzclosed, r, hrpos, hadmiss.1, hadmiss.2, hsmallr'⟩

private theorem goodPoint_holder_patches_agree
    {U V U' V' : Set ParabolicPoint}
    {u f g : ParabolicPoint → Vec3} {γ C C' : ℝ}
    (hγ : 0 < γ) (hU : IsOpen U) (hU' : IsOpen U')
    (hUV : U ⊆ V) (hU'V' : U' ⊆ V')
    (hDense : V ∩ V' ⊆ closure (U ∩ U'))
    (hfU : ParabolicHolderVecNormLE U f γ C)
    (hgU' : ParabolicHolderVecNormLE U' g γ C')
    (hfV : ParabolicHolderVecNormLE V f γ C)
    (hgV' : ParabolicHolderVecNormLE V' g γ C')
    (hfu : f =ᵐ[volume.restrict U] u)
    (hgu : g =ᵐ[volume.restrict U'] u) :
    EqOn f g (V ∩ V') := by
  have hEq : EqOn f g (U ∩ U') :=
    CKN.Core.Endgame.holder_representatives_eqOn_overlap hU hU' hγ hγ
      (CKN.Core.Endgame.holder_on_of_norm hfU)
      (CKN.Core.Endgame.holder_on_of_norm hgU') hfu hgu
  apply Set.EqOn.of_subset_closure hEq
  · exact (CKN.Core.Endgame.holder_on_continuousOn hγ
      (CKN.Core.Endgame.holder_on_of_norm hfV)).mono inter_subset_left
  · exact (CKN.Core.Endgame.holder_on_continuousOn hγ
      (CKN.Core.Endgame.holder_on_of_norm hgV')).mono inter_subset_right
  · intro q hq
    exact ⟨hUV hq.1, hU'V' hq.2⟩
  · exact hDense

private theorem goodPoint_inner_region_subset_closedTop
    {K : Set ParabolicPoint}
    (hK : K ⊆ {z : ParabolicPoint |
      vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
        z.2 ∈ Icc (-(1 / 4 : ℝ)) 0}) :
    K ⊆ goodPointClosedTopDomain := by
  intro z hz
  rcases hK hz with ⟨hx, ht⟩
  constructor
  · change vec3EuclideanNorm (z.1 - 0) < 1
    linarith only [hx]
  · exact ⟨by linarith only [ht.1], ht.2⟩

private theorem goodPoint_domain_subset_closedTop :
    goodPointDomain ⊆ goodPointClosedTopDomain := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  exact ⟨hx, ⟨ht.1, le_of_lt ht.2⟩⟩

private theorem goodPoint_holder_norm_of_near_control
    {K : Set ParabolicPoint} {w : ParabolicPoint → Vec3}
    {γ B H δ : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hδ : 0 < δ)
    (hbound : ∀ x ∈ K, vec3EuclideanNorm (w x) ≤ B)
    (hnear : ∀ x ∈ K, ∀ y ∈ K, parabolicDist x y < δ →
      vec3EuclideanNorm (w x - w y) ≤ H * parabolicDist x y ^ γ) :
    ParabolicHolderVecNormLE K w γ (B + max H (2 * B / δ ^ γ)) := by
  refine ⟨B, max H (2 * B / δ ^ γ), hB,
    le_trans hH (le_max_left _ _), le_rfl, hbound, ?_⟩
  intro x hx y hy
  have hdistnonneg : 0 ≤ parabolicDist x y := by
    rw [← dist_eq_parabolicDist]
    exact dist_nonneg
  have hdpow : 0 ≤ parabolicDist x y ^ γ := Real.rpow_nonneg hdistnonneg _
  by_cases hclose : parabolicDist x y < δ
  · exact (hnear x hx y hy hclose).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hdpow)
  · have hfar : δ ≤ parabolicDist x y := le_of_not_gt hclose
    have hδpow : 0 < δ ^ γ := Real.rpow_pos_of_pos hδ _
    calc
      vec3EuclideanNorm (w x - w y) ≤
          vec3EuclideanNorm (w x) + vec3EuclideanNorm (w y) :=
        goodPointVecNorm_sub_le_glue _ _
      _ ≤ 2 * B := by linarith only [hbound x hx, hbound y hy]
      _ = (2 * B / δ ^ γ) * δ ^ γ := (div_mul_cancel₀ _ hδpow.ne').symm
      _ ≤ (2 * B / δ ^ γ) * parabolicDist x y ^ γ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hfar hγ.le)
          (div_nonneg (mul_nonneg (by norm_num) hB) hδpow.le)
      _ ≤ max H (2 * B / δ ^ γ) * parabolicDist x y ^ γ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hdpow

private theorem goodPoint_finite_cover_indices
    {α : Type*} {ι : Type*} {K : Set α} (t : Finset ι)
    (U : ι → Set α) (hcover : K ⊆ ⋃ i ∈ (t : Set ι), U i) :
    (∀ x ∈ K, ∃ i : {i // i ∈ t}, x ∈ U i) ∧
      (K.Nonempty → t.Nonempty) := by
  constructor
  · intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx) with ⟨i, hit, hxi⟩
    exact ⟨⟨i, hit⟩, hxi⟩
  · intro hK
    obtain ⟨x, hx⟩ := hK
    obtain ⟨i, hi⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact ⟨i, hi.1⟩

private theorem isOpen_subtype_union_preimage
    {α : Type*} [TopologicalSpace α] {ι : Type*} {S : Set α}
    (U : ι → Set α) (hU : ∀ i, IsOpen (U i)) :
    IsOpen {z : S | z.1 ∈ ⋃ i, U i} := by
  have hEq : {z : S | z.1 ∈ ⋃ i, U i} =
      ⋃ i, Subtype.val ⁻¹' U i := by
    ext z
    simp
  rw [hEq]
  exact isOpen_iUnion fun i => (hU i).preimage continuous_subtype_val


private theorem goodPoint_compact_representative
    {ε₀ γ₀ C₄ : ℝ} (hγ₀ : 0 < γ₀) (hC₄ : 0 ≤ C₄)
    (hTop : ∀ (x₀ : Vec3) (t₀ ρ r : ℝ)
      (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ),
      0 < r → r < ρ →
      IsSuitableWeakSolution (vec3Ball x₀ ρ) (Ioo (t₀ - ρ ^ 2) t₀) 3
        u Du p (fun _ => 0) →
      ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r <
        ENNReal.ofReal (ε₀ / 8) →
      ∃ w : ParabolicPoint → Vec3,
        w =ᵐ[volume.restrict (goodPointPastCylinder x₀ t₀ (r / 2))] u ∧
        (∀ z ∈ closure (goodPointPastCylinder x₀ t₀ (r / 2)),
          vec3EuclideanNorm (w z) ≤ 2 * C₄ * r⁻¹) ∧
        (∀ z ∈ closure (goodPointPastCylinder x₀ t₀ (r / 2)),
          ∀ z' ∈ closure (goodPointPastCylinder x₀ t₀ (r / 2)),
            vec3EuclideanNorm (w z - w z') ≤
              4 * C₄ * r⁻¹ * (8 * r⁻¹) ^ γ₀ * parabolicDist z z' ^ γ₀))
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0))
    {K : Set ParabolicPoint} (hK : IsCompact K)
    (hKregion : K ⊆ {z : ParabolicPoint |
      vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
        z.2 ∈ Icc (-(1 / 4 : ℝ)) 0})
    (hKgood : ∀ z ∈ K, IsGoodPoint ε₀ u p z) :
    ∃ N : Set ParabolicPoint, ∃ w : ParabolicPoint → Vec3,
      K ⊆ N ∧ N ⊆ goodPointClosedTopDomain ∧
      IsOpen {z : {q : ParabolicPoint // q ∈ goodPointClosedTopDomain} |
        z.1 ∈ N} ∧
      w =ᵐ[volume.restrict (N ∩ goodPointDomain)] u ∧
      ParabolicHolderVecOn K w γ₀ := by
  classical
  have hKdomain := goodPoint_inner_region_subset_closedTop hKregion
  by_cases hKempty : K = ∅
  · subst K
    have hHolder : ParabolicHolderVecNormLE (∅ : Set ParabolicPoint) u γ₀ 0 := by
      refine ⟨0, 0, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
      · intro z hz
        simp at hz
      · intro z hz z' hz'
        simp at hz
    refine ⟨goodPointClosedTopDomain, u, ?_, ?_, ?_, ?_, ?_⟩
    · exact empty_subset _
    · exact subset_rfl
    · simp
    · have hdomain : goodPointClosedTopDomain ∩ goodPointDomain = goodPointDomain := by
        ext z
        constructor
        · exact fun h => h.2
        · intro hz
          exact ⟨goodPoint_domain_subset_closedTop hz, hz⟩
      rw [hdomain]
    · exact CKN.Core.Endgame.holder_on_of_norm hHolder
  let patchIndex : Type := {z : ParabolicPoint // z ∈ K}
  choose δ Cpatch w hδpos hCpatch hwae hHolderPast hHolderTop using
    fun z : patchIndex =>
      goodPoint_local_holder_patch hC₄ hTop hSuitable
        (hKdomain z.2) (hKgood z.1 z.2)
  have hcover : K ⊆ ⋃ z : patchIndex, Metric.ball z.1 (δ z / 2) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩,
      Metric.mem_ball_self
        (div_pos (hδpos ⟨z, hz⟩) (by norm_num : (0 : ℝ) < 2))⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun z : patchIndex => Metric.ball z.1 (δ z / 2))
    (fun _ => Metric.isOpen_ball) hcover
  have hcoverIndices := goodPoint_finite_cover_indices t
    (fun z => Metric.ball z.1.1 (δ z / 2)) ht
  have hhalfcover := hcoverIndices.1
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  have htn : t.Nonempty := hcoverIndices.2 hKne
  let Ui : t → Set ParabolicPoint := fun i =>
    Metric.ball i.1.1 (δ i.1) ∩ goodPointDomain
  let Vi : t → Set ParabolicPoint := fun i =>
    Metric.ball i.1.1 (δ i.1) ∩ goodPointClosedTopDomain
  let N : Set ParabolicPoint := ⋃ i : t, Vi i
  have hUiOpen : ∀ i : t, IsOpen (Ui i) := by
    intro i
    change IsOpen (Metric.ball i.1.1 (δ i.1) ∩ goodPointDomain)
    refine Metric.isOpen_ball.inter ?_
    change IsOpen (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))
    exact isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo
  have hNsub : N ⊆ goodPointClosedTopDomain := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact hi.2
  have hKsubN : K ⊆ N := by
    intro x hx
    obtain ⟨i, hxi⟩ := hhalfcover x hx
    exact mem_iUnion.mpr ⟨i,
      ⟨Metric.ball_subset_ball (by linarith only [hδpos i.1]) hxi,
        hKdomain hx⟩⟩
  have hNopen : IsOpen {z : {q : ParabolicPoint //
      q ∈ goodPointClosedTopDomain} | z.1 ∈ N} := by
    simpa only [N, Vi] using isOpen_subtype_union_preimage
      (fun i : t => Metric.ball i.1.1 (δ i.1))
      (fun _ => Metric.isOpen_ball)
  have hNdomainEq : N ∩ goodPointDomain = ⋃ i : t, Ui i := by
    ext z
    constructor
    · rintro ⟨hzN, hzD⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hzN
      exact mem_iUnion.mpr ⟨i, ⟨hi.1, hzD⟩⟩
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact ⟨mem_iUnion.mpr ⟨i,
        ⟨hi.1, goodPoint_domain_subset_closedTop hi.2⟩⟩, hi.2⟩
  have hNdomain : N ∩ goodPointDomain ⊆ ⋃ i : t, Ui i := by
    rw [hNdomainEq]
  have hδglob : 0 < t.inf' htn (fun i => δ i / 2) := by
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact div_pos (hδpos i) (by norm_num : (0 : ℝ) < 2)
  let δglob : ℝ := t.inf' htn (fun i => δ i / 2)
  have hδglob' : 0 < δglob := by simpa only [δglob] using hδglob
  have hclose : ∀ x ∈ K, ∀ y ∈ K, parabolicDist x y < δglob →
      ∃ i : t, x ∈ Vi i ∧ y ∈ Vi i := by
    intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := hhalfcover x hx
    have hδile : δglob ≤ δ i.1 / 2 := by
      dsimp [δglob]
      exact Finset.inf'_le (s := t) (f := fun j => δ j / 2) i.2
    have hhalf : δ i.1 / 2 ≤ δ i.1 := by linarith only [hδpos i.1]
    have hxiFull : x ∈ Metric.ball i.1.1 (δ i.1) :=
      Metric.ball_subset_ball hhalf hxi
    have hdistyx : dist y x < δglob := by
      calc
        dist y x = dist x y := dist_comm _ _
        _ = parabolicDist x y := dist_eq_parabolicDist x y
        _ < δglob := hxy
    have hdistxc : dist x i.1.1 < δ i.1 / 2 := Metric.mem_ball.mp hxi
    have htri : dist y i.1.1 < δglob + δ i.1 / 2 :=
      (dist_triangle y x i.1.1).trans_lt (add_lt_add hdistyx hdistxc)
    have hyFull : y ∈ Metric.ball i.1.1 (δ i.1) := by
      apply Metric.mem_ball.mpr
      linarith only [htri, hδile, hδpos i.1]
    exact ⟨i, ⟨hxiFull, hKdomain hx⟩, ⟨hyFull, hKdomain hy⟩⟩
  have hAgree : ∀ i j : t, EqOn (w i.1) (w j.1) (Vi i ∩ Vi j) := by
    intro i j
    apply goodPoint_holder_patches_agree hγ₀ (hUiOpen i) (hUiOpen j)
      (by intro z hz; exact ⟨hz.1, goodPoint_domain_subset_closedTop hz.2⟩)
      (by intro z hz; exact ⟨hz.1, goodPoint_domain_subset_closedTop hz.2⟩)
      ?_ (hHolderPast i.1) (hHolderPast j.1)
      (hHolderTop i.1) (hHolderTop j.1) (hwae i.1) (hwae j.1)
    intro q hq
    apply (mem_closure_iff_nhds).2
    intro S hS
    let W := Metric.ball i.1.1 (δ i.1) ∩ Metric.ball j.1.1 (δ j.1)
    have hW : W ∈ 𝓝 q := by
      apply (Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds
      exact ⟨hq.1.1, hq.2.1⟩
    have hSW : S ∩ W ∈ 𝓝 q := Filter.inter_mem hS hW
    have hqclosure : q ∈ closure goodPointDomain :=
      goodPoint_closedTop_subset_closure_domain hq.1.2
    obtain ⟨a, ha⟩ := (mem_closure_iff_nhds.mp hqclosure)
      (S ∩ W) hSW
    rcases ha with ⟨⟨haS, haW⟩, haD⟩
    rcases haW with ⟨haI, haJ⟩
    exact ⟨a, ⟨haS, ⟨⟨haI, haD⟩, ⟨haJ, haD⟩⟩⟩⟩
  obtain ⟨g, hgEq, hgAE⟩ := CKN.Core.Endgame.exists_holder_gluing
    Ui (fun i => w i.1) hγ₀ hUiOpen
    (fun i => CKN.Core.Endgame.holder_on_of_norm (hHolderPast i.1))
    (fun i => hwae i.1)
  let wFinal : ParabolicPoint → Vec3 := fun q =>
    if hq : q ∈ N then
      if hqD : q ∈ goodPointDomain then g q
      else w (Classical.choose (mem_iUnion.mp
        (show q ∈ ⋃ i : t, Vi i from hq))).1 q
    else 0
  have hWlocal : ∀ i : t, EqOn wFinal (w i.1) (Vi i) := by
    intro i q hq
    have hqN : q ∈ N := mem_iUnion.mpr ⟨i, hq⟩
    by_cases hqD : q ∈ goodPointDomain
    · dsimp [wFinal]
      rw [dite_eq_left hqN, ite_eq_left hqD]
      exact hgEq i ⟨hq.1, hqD⟩
    · dsimp [wFinal]
      rw [dite_eq_left hqN, ite_eq_right hqD]
      exact hAgree (Classical.choose (mem_iUnion.mp
          (show q ∈ ⋃ j : t, Vi j from hqN))) i
        ⟨Classical.choose_spec (mem_iUnion.mp
          (show q ∈ ⋃ j : t, Vi j from hqN)), hq⟩
  have hWg : EqOn wFinal g (N ∩ goodPointDomain) := by
    intro q hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp (by rw [← hNdomainEq]; exact hq)
    have hqV : q ∈ Vi i := ⟨hi.1, goodPoint_domain_subset_closedTop hq.2⟩
    exact (hWlocal i hqV).trans (hgEq i hi).symm
  have hNdomainMeas : MeasurableSet (N ∩ goodPointDomain) := by
    rw [hNdomainEq]
    exact MeasurableSet.iUnion fun i => (hUiOpen i).measurableSet
  have hWAE : wFinal =ᵐ[volume.restrict (N ∩ goodPointDomain)] u := by
    have hWgAE : wFinal =ᵐ[volume.restrict (N ∩ goodPointDomain)] g :=
      (ae_restrict_mem hNdomainMeas).mono hWg
    exact hWgAE.trans
      (ae_restrict_of_ae_restrict_of_subset hNdomain hgAE)
  let Cmax : ℝ := t.sup' htn (fun i => Cpatch i)
  have hCmax : 0 ≤ Cmax := by
    obtain ⟨i, hi⟩ := htn
    dsimp [Cmax]
    exact (hCpatch i).trans
      (Finset.le_sup' (s := t) (f := fun j => Cpatch j) hi)
  have hCpatch_le : ∀ i : t, Cpatch i.1 ≤ Cmax := by
    intro i
    dsimp [Cmax]
    exact Finset.le_sup' (s := t) (f := fun j => Cpatch j) i.2
  have hsup : ∀ x ∈ K, vec3EuclideanNorm (wFinal x) ≤ Cmax := by
    intro x hx
    obtain ⟨i, hxi⟩ := hhalfcover x hx
    have hhalf : δ i.1 / 2 ≤ δ i.1 := by linarith only [hδpos i.1]
    have hxiFull : x ∈ Metric.ball i.1.1 (δ i.1) :=
      Metric.ball_subset_ball hhalf hxi
    have hxiV : x ∈ Vi i := ⟨hxiFull, hKdomain hx⟩
    rw [hWlocal i hxiV]
    obtain ⟨B, H, hB, hH, hBH, hbound, _⟩ := hHolderTop i.1
    exact (hbound x hxiV).trans
      (by linarith only [hH, hBH, hCpatch_le i])
  have hnearK : ∀ x ∈ K, ∀ y ∈ K, parabolicDist x y < δglob →
      vec3EuclideanNorm (wFinal x - wFinal y) ≤ Cmax * parabolicDist x y ^ γ₀ := by
    intro x hx y hy hnear
    obtain ⟨i, hxi, hyi⟩ := hclose x hx y hy hnear
    rw [hWlocal i hxi, hWlocal i hyi]
    obtain ⟨B, H, hB, hH, hBH, _, hsemi⟩ := hHolderTop i.1
    have hHmax : H ≤ Cmax := by linarith only [hB, hBH, hCpatch_le i]
    exact (hsemi x hxi y hyi).trans
      (mul_le_mul_of_nonneg_right hHmax
        (Real.rpow_nonneg (parabolicDist_nonneg x y) γ₀))
  have hHolderK := goodPoint_holder_norm_of_near_control
    hγ₀ hCmax hCmax hδglob' hsup hnearK
  refine ⟨N, wFinal, hKsubN, hNsub, hNopen, hWAE,
    CKN.Core.Endgame.holder_on_of_norm hHolderK⟩

/-- Good points are relatively open, and every compact subset of good points
has one representative which is Hölder on the entire compact set, including
its top-face points. The same constants also give the bad-point lower bound
in `eq:bad-point-lower-bound`. -/
theorem goodPoint_open_glue :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      (∀ {u : ParabolicPoint → Vec3}
          {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ},
        IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) 3
          u Du p (fun _ => 0) →
        IsOpen {z : {q : ParabolicPoint // q ∈ goodPointClosedTopDomain} |
          IsGoodPoint ε₀ u p z.1} ∧
        ∀ {K : Set ParabolicPoint}, IsCompact K →
          K ⊆ {z : ParabolicPoint |
            vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
              z.2 ∈ Icc (-(1 / 4 : ℝ)) 0} →
          (∀ z ∈ K, IsGoodPoint ε₀ u p z) →
          ∃ N : Set ParabolicPoint, ∃ w : ParabolicPoint → Vec3,
            K ⊆ N ∧ N ⊆ goodPointClosedTopDomain ∧
            IsOpen {z : {q : ParabolicPoint // q ∈ goodPointClosedTopDomain} |
              z.1 ∈ N} ∧
            w =ᵐ[volume.restrict (N ∩ goodPointDomain)] u ∧
            ParabolicHolderVecOn K w γ₀) ∧
      (∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
          {z : ParabolicPoint} {R : ℝ},
        vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 →
        z.2 ∈ Icc (-(1 / 4 : ℝ)) 0 →
        0 < R →
        goodPointPastCylinder z.1 z.2 R ⊆ goodPointDomain →
        ¬ IsGoodPoint ε₀ u p z →
        ENNReal.ofReal (R⁻¹ ^ 2) * goodPointEnergy u p z.1 z.2 R ≥
          ENNReal.ofReal (ε₀ / 8)) := by
  obtain ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, hTop⟩ :=
    epsilonRegularityL3_top
  refine ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, ?_, ?_⟩
  · intro u Du p hSuitable
    refine ⟨goodPoint_set_relative_open hSuitable, ?_⟩
    intro K hK hKregion hKgood
    exact goodPoint_compact_representative hγ₀ hC₄ hTop
      hSuitable hK hKregion hKgood
  · intro u p z R hx ht hRpos hRdomain hnot
    exact goodPoint_badPoint_lower_bound_closed ⟨hx, ht⟩ hRpos hRdomain hnot

end ESS
