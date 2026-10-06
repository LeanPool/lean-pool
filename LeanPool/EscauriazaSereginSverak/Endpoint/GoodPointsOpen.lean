/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsContinuity
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecNormLE
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Topology.Compactness.Compact

/-!
# Relative neighborhoods of good points

This file proves the openness and local representative parts of
`lem:good-open-glue`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem vec3EuclideanNorm_sub_triang_open (a b c : Vec3) :
    vec3EuclideanNorm (a - c) ≤
      vec3EuclideanNorm (a - b) + vec3EuclideanNorm (b - c) := by
  simp only [vec3EuclideanNorm_eq_l2]
  have h : WithLp.toLp 2 (a - c) =
      WithLp.toLp 2 (a - b) + WithLp.toLp 2 (b - c) := by
    rw [WithLp.toLp_sub, WithLp.toLp_sub, WithLp.toLp_sub]
    abel
  rw [h]
  exact norm_add_le _ _

private theorem closure_goodPointPastCylinder {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    closure (goodPointPastCylinder x t r) =
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} ×ˢ Icc (t - r ^ 2) t := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hlt : t - r ^ 2 < t := by linarith only [hr2]
  rw [show goodPointPastCylinder x t r =
      parabolicHomeomorph ⁻¹' (vec3Ball x r ×ˢ Ioo (t - r ^ 2) t) by
        rw [goodPointPastCylinder, parabolicHomeomorph_preimage],
    ← parabolicHomeomorph.preimage_closure]
  rw [closure_prod_eq, closure_vec3Ball hr, closure_Ioo hlt.ne,
    parabolicHomeomorph_preimage]

private theorem goodPointWitness_spatial_subset
    {z : ParabolicPoint} {R : ℝ}
    (hRpos : 0 < R)
    (hRdomain : goodPointPastCylinder z.1 z.2 R ⊆ goodPointDomain) :
    vec3Ball z.1 R ⊆ vec3Ball 0 1 := by
  intro y hy
  let s := z.2 - R ^ 2 / 2
  have hs : s ∈ Ioo (z.2 - R ^ 2) z.2 := by
    dsimp [s]
    constructor <;> nlinarith only [hRpos]
  have hx : ((y, s) : ParabolicPoint) ∈ goodPointPastCylinder z.1 z.2 R := by
    change y ∈ vec3Ball z.1 R ∧ s ∈ Ioo (z.2 - R ^ 2) z.2
    exact ⟨hy, hs⟩
  exact (hRdomain hx).1

private theorem goodPointWitness_lower_time
    {z : ParabolicPoint} {R : ℝ}
    (hRpos : 0 < R)
    (hRdomain : goodPointPastCylinder z.1 z.2 R ⊆ goodPointDomain) :
    -1 ≤ z.2 - R ^ 2 := by
  have hx : z.1 ∈ vec3Ball z.1 R := by
    simp [vec3Ball, vec3EuclideanNorm_zero, hRpos]
  have htime : Ioo (z.2 - R ^ 2) z.2 ⊆ Ioo (-1) 0 := by
    intro s hs
    have hq : ((z.1, s) : ParabolicPoint) ∈ goodPointPastCylinder z.1 z.2 R := by
      change z.1 ∈ vec3Ball z.1 R ∧ s ∈ Ioo (z.2 - R ^ 2) z.2
      exact ⟨hx, hs⟩
    exact (hRdomain hq).2
  have hends := (Set.Ioo_subset_Ioo_iff (by nlinarith only [hRpos])).mp htime
  exact hends.1

private theorem goodPoint_domain_spatial_ball_compact (x : Vec3) {r : ℝ} :
    IsCompact {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} := by
  let e : Vec3 → PiLp 2 (fun _ : Fin 3 => ℝ) := WithLp.toLp 2
  have hball : IsCompact (Metric.closedBall (e x) r) := isCompact_closedBall _ _
  have himage : IsCompact (WithLp.ofLp '' Metric.closedBall (e x) r) :=
    hball.image (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ))
  have heq : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} =
      WithLp.ofLp '' Metric.closedBall (e x) r := by
    ext y
    constructor
    · intro hy
      refine ⟨e y, ?_, WithLp.ofLp_toLp 2 y⟩
      change dist (e y) (e x) ≤ r
      rw [dist_eq_norm, ← WithLp.toLp_sub]
      change vec3EuclideanNorm (y - x) ≤ r at hy
      simpa only [vec3EuclideanNorm_eq_l2] using hy
    · rintro ⟨v, hv, hvy⟩
      have hy : WithLp.ofLp v = y := hvy
      subst y
      change vec3EuclideanNorm (WithLp.ofLp v - x) ≤ r
      have hvx : WithLp.toLp 2 (WithLp.ofLp v) = v := WithLp.toLp_ofLp 2 v
      change dist v (e x) ≤ r at hv
      rw [dist_eq_norm] at hv
      rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, hvx]
      exact hv
  rw [heq]
  exact himage

/-- The closed top domain lies in the closure of the open space-time domain.
This lets a relatively open intersection with the top face be tested from
below in time. -/
theorem goodPoint_closedTop_subset_closure_domain :
    goodPointClosedTopDomain ⊆ closure goodPointDomain := by
  intro z hz
  rw [show goodPointDomain =
      parabolicHomeomorph ⁻¹' (vec3Ball 0 1 ×ˢ Ioo (-1) 0) by
        rw [goodPointDomain, parabolicHomeomorph_preimage],
    ← parabolicHomeomorph.preimage_closure,
    closure_prod_eq, closure_vec3Ball (by norm_num : 0 < (1 : ℝ)),
    closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0), parabolicHomeomorph_preimage]
  rcases hz with ⟨hx, ht⟩
  refine ⟨?_, ?_⟩
  · change vec3EuclideanNorm (z.1 - 0) ≤ 1
    change vec3EuclideanNorm (z.1 - 0) < 1 at hx
    exact le_of_lt hx
  · exact ⟨le_of_lt ht.1, ht.2⟩

private theorem goodPoint_smallness_of_energy_le
    {ε : ℝ} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {x₁ x₂ : Vec3} {t₁ t₂ r₁ r₂ : ℝ}
    (hsmall : ENNReal.ofReal (r₁⁻¹ ^ 2) *
      goodPointEnergy u p x₂ t₂ r₂ < ENNReal.ofReal (ε / 8))
    (hsubset : parabolicCylinder x₁ t₁ r₁ ⊆ parabolicCylinder x₂ t₂ r₂) :
    ENNReal.ofReal (r₁⁻¹ ^ 2) * goodPointEnergy u p x₁ t₁ r₁ <
      ENNReal.ofReal (ε / 8) := by
  have hmono := goodPointEnergy_mono (u := u) (p := p) hsubset
  have hmul : ENNReal.ofReal (r₁⁻¹ ^ 2) * goodPointEnergy u p x₁ t₁ r₁ ≤
      ENNReal.ofReal (r₁⁻¹ ^ 2) * goodPointEnergy u p x₂ t₂ r₂ := by
    gcongr
  exact hmul.trans_lt hsmall

private theorem goodPoint_top_neighborhood_in_closure_past
    {z : ParabolicPoint} {r δ : ℝ}
    (hr : 0 < r) (hδ : δ = r / 4) (htop : z.2 = 0) :
    Metric.ball z δ ∩ goodPointClosedTopDomain ⊆
      closure (goodPointPastCylinder z.1 z.2 (r / 2)) := by
  intro q hq
  rcases hq with ⟨hball, hclosed⟩
  have hdist : parabolicDist q z < r / 4 := by
    simpa only [Metric.mem_ball, dist_eq_parabolicDist, hδ] using hball
  have hparts : vec3EuclideanNorm (q.1 - z.1) < r / 4 ∧
      Real.sqrt |q.2 - z.2| < r / 4 := by
    unfold parabolicDist at hdist
    exact max_lt_iff.mp hdist
  have hspace : vec3EuclideanNorm (q.1 - z.1) ≤ r / 2 := by
    exact le_of_lt (by nlinarith only [hparts.1, hr])
  have htimeabs : |q.2 - z.2| < (r / 4) ^ 2 :=
    (Real.sqrt_lt' (by positivity : 0 < r / 4)).mp hparts.2
  have hlow : z.2 - (r / 2) ^ 2 ≤ q.2 := by
    have hlow' := (abs_lt.mp htimeabs).1
    rw [htop, sub_zero] at hlow'
    rw [htop]
    nlinarith only [hlow', hr]
  have hhigh : q.2 ≤ z.2 := by rw [htop]; exact hclosed.2.2
  rw [closure_goodPointPastCylinder (by positivity : 0 < r / 2)]
  exact ⟨hspace, ⟨hlow, hhigh⟩⟩

private theorem goodPointFullCylinder_subset_of_top_near
    {z c : ParabolicPoint} {r R δ : ℝ}
    (hδ : 0 < δ) (hrδ : δ ≤ R - r)
    (hδt : δ ^ 2 ≤ R ^ 2 - r ^ 2)
    (hzTop : z.2 = 0) (hcTop : c.2 ≤ 0)
    (hd : parabolicDist c z < δ) :
    parabolicCylinder c.1 c.2 r ⊆ parabolicCylinder z.1 z.2 R := by
  have hparts : vec3EuclideanNorm (c.1 - z.1) < δ ∧
      Real.sqrt |c.2 - z.2| < δ := by
    unfold parabolicDist at hd
    exact max_lt_iff.mp hd
  have hrR : r ≤ R := by linarith only [hδ, hrδ]
  have hqsubset : parabolicCylinder c.1 c.2 r ⊆ parabolicCylinder z.1 z.2 R := by
    intro q hq
    rcases hq with ⟨hqx, hqtlo, hqthi⟩
    have hqxR : q.1 ∈ vec3Ball z.1 R := by
      calc
        vec3EuclideanNorm (q.1 - z.1) ≤
            vec3EuclideanNorm (q.1 - c.1) + vec3EuclideanNorm (c.1 - z.1) :=
          vec3EuclideanNorm_sub_triang_open _ _ _
        _ < r + δ := add_lt_add hqx hparts.1
        _ ≤ R := by linarith only [hδ, hrδ]
    have htimeabs : |c.2 - z.2| < δ ^ 2 :=
      (Real.sqrt_lt' hδ).mp hparts.2
    have hcloseLo : z.2 - δ ^ 2 < c.2 := by
      have := (abs_lt.mp htimeabs).1
      linarith only [this]
    have hmargin : δ ^ 2 + r ^ 2 ≤ R ^ 2 := by linarith only [hδt]
    have hlow : z.2 - R ^ 2 < q.2 := by
      linarith only [hqtlo, hcloseLo, hmargin]
    have htop : q.2 ≤ z.2 := by
      rw [hzTop]
      exact hqthi.trans hcTop
    exact ⟨hqxR, hlow, htop⟩
  exact hqsubset

private theorem suitable_on_goodPointPastCylinder
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {x : Vec3} {t ρ : ℝ}
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0))
    (hρpos : 0 < ρ)
    (hρdomain : goodPointPastCylinder x t ρ ⊆ goodPointDomain) :
    IsSuitableWeakSolution (vec3Ball x ρ) (Ioo (t - ρ ^ 2) t) 3
      u Du p (fun _ => 0) := by
  have hx : x ∈ vec3Ball x ρ := by
    simp [vec3Ball, vec3EuclideanNorm_zero, hρpos]
  have hΩsub : vec3Ball x ρ ⊆ vec3Ball 0 1 := by
    intro y hy
    let s := t - ρ ^ 2 / 2
    have hs : s ∈ Ioo (t - ρ ^ 2) t := by
      dsimp [s]
      constructor <;> nlinarith only [hρpos]
    have hq : ((y, s) : ParabolicPoint) ∈ goodPointPastCylinder x t ρ := by
      change y ∈ vec3Ball x ρ ∧ s ∈ Ioo (t - ρ ^ 2) t
      exact ⟨hy, hs⟩
    exact (hρdomain hq).1
  have hIsub : Ioo (t - ρ ^ 2) t ⊆ Ioo (-1) 0 := by
    intro s hs
    have hq : ((x, s) : ParabolicPoint) ∈ goodPointPastCylinder x t ρ := by
      change x ∈ vec3Ball x ρ ∧ s ∈ Ioo (t - ρ ^ 2) t
      exact ⟨hx, hs⟩
    exact (hρdomain hq).2
  exact isSuitableWeakSolution_restrict hSuitable
    (isOpen_vec3Ball _ _) isOpen_Ioo ordConnected_Ioo hΩsub hIsub

private theorem goodPoint_global_data
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0)) :
    IsSuitableWeakSolutionData (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0) :=
  (isSuitableWeakSolution_iff_integrable.mp hSuitable).toData

private theorem goodPointPastCylinder_subset_domain_of_top_near
    {z c : ParabolicPoint} {r R δ : ℝ}
    (hδ : 0 < δ) (hrδ : δ ≤ R - r)
    (hδt : δ ^ 2 ≤ R ^ 2 - r ^ 2)
    (hzTop : z.2 = 0) (hcTop : c.2 ≤ 0)
    (hd : parabolicDist c z < δ)
    (hRdomain : goodPointPastCylinder z.1 z.2 R ⊆ goodPointDomain) :
    goodPointPastCylinder c.1 c.2 r ⊆ goodPointDomain := by
  have hparts : vec3EuclideanNorm (c.1 - z.1) < δ ∧
      Real.sqrt |c.2 - z.2| < δ := by
    unfold parabolicDist at hd
    exact max_lt_iff.mp hd
  have hqsubset : goodPointPastCylinder c.1 c.2 r ⊆
      goodPointPastCylinder z.1 z.2 R := by
    intro q hq
    rcases hq with ⟨hqx, hqt⟩
    have hqxR : q.1 ∈ vec3Ball z.1 R := by
      calc
        vec3EuclideanNorm (q.1 - z.1) ≤
            vec3EuclideanNorm (q.1 - c.1) + vec3EuclideanNorm (c.1 - z.1) :=
          vec3EuclideanNorm_sub_triang_open _ _ _
        _ < r + δ := add_lt_add hqx hparts.1
        _ ≤ R := by linarith only [hrδ]
    rcases hqt with ⟨hqtlo, hqthi⟩
    have hqtR : q.2 ∈ Ioo (z.2 - R ^ 2) z.2 := by
      have htimeabs : |c.2 - z.2| < δ ^ 2 :=
        (Real.sqrt_lt' (by linarith only [hδ])).mp hparts.2
      have hcloseLo : z.2 - δ ^ 2 < c.2 := by
        have := (abs_lt.mp htimeabs).1
        linarith only [this]
      have hlow : z.2 - R ^ 2 < q.2 := by
        have hmargin : δ ^ 2 + r ^ 2 ≤ R ^ 2 := by
          linarith only [hδt]
        linarith only [hqtlo, hcloseLo, hmargin]
      have htop : q.2 < z.2 := by
        rw [hzTop]
        exact hqthi.trans_le hcTop
      exact ⟨hlow, htop⟩
    exact ⟨hqxR, hqtR⟩
  intro q hq
  exact hRdomain (hqsubset hq)

private theorem goodPointInteriorCompact
    {z : ParabolicPoint} {R r : ℝ}
    (hzinterior : z.2 < 0)
    (hRpos : 0 < R) (hrpos : 0 < r) (hrR : r < R)
    (hRdomain : goodPointPastCylinder z.1 z.2 R ⊆ goodPointDomain) :
    ∃ M η δ : ℝ, ∃ K : Set ParabolicPoint,
      r < M ∧ M < R ∧ 0 < η ∧ 0 < δ ∧ IsCompact K ∧
      K ⊆ goodPointDomain ∧
      (∀ c, parabolicDist c z < δ → parabolicCylinder c.1 c.2 r ⊆ K) ∧
      (∀ c, parabolicDist c z < δ →
        goodPointPastCylinder c.1 c.2 M ⊆ goodPointDomain) := by
  let M : ℝ := (r + R) / 2
  have hrM : r < M := by dsimp [M]; linarith only [hrR]
  have hMR : M < R := by dsimp [M]; linarith only [hrR]
  have hMpos : 0 < M := lt_trans hrpos hrM
  have hR2M2 : M ^ 2 < R ^ 2 := by nlinarith only [hMpos, hMR, hRpos]
  have hneg : 0 < -z.2 := neg_pos.mpr hzinterior
  let η := min ((R ^ 2 - M ^ 2) / 2) ((-z.2) / 2)
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hηR : η < R ^ 2 - M ^ 2 := by
    dsimp [η]
    have hfirst : 0 < (R ^ 2 - M ^ 2) / 2 := by positivity
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith only [hfirst])
  have hηt : η < -z.2 := by
    dsimp [η]
    have hsecond : 0 < (-z.2) / 2 := by positivity
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith only [hsecond])
  let d := min (M - r) (min (R - M)
    (min (Real.sqrt η) (min (Real.sqrt (R ^ 2 - M ^ 2)) (Real.sqrt (-z.2)))))
  have hdpos : 0 < d := by dsimp [d]; positivity
  let δ := d / 2
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδd : δ < d := by dsimp [δ]; linarith only [hdpos]
  have hdM : d ≤ M - r := by dsimp [d]; exact min_le_left _ _
  have hdR : d ≤ R - M := by
    dsimp [d]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdη : d ≤ Real.sqrt η := by
    dsimp [d]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdRm : d ≤ Real.sqrt (R ^ 2 - M ^ 2) := by
    dsimp [d]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hdtime : d ≤ Real.sqrt (-z.2) := by
    dsimp [d]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hδM : δ < M - r := lt_of_lt_of_le hδd hdM
  have hδR : δ < R - M := lt_of_lt_of_le hδd hdR
  have hδη : δ < Real.sqrt η := lt_of_lt_of_le hδd hdη
  have hδRm : δ < Real.sqrt (R ^ 2 - M ^ 2) := lt_of_lt_of_le hδd hdRm
  have hδtime : δ < Real.sqrt (-z.2) := lt_of_lt_of_le hδd hdtime
  have hδsqη : δ ^ 2 < η := by
    have hs := Real.sq_sqrt hηpos.le
    have hδnn := le_of_lt hδpos
    nlinarith only [hδη, hs, hδnn]
  have hδsqRm : δ ^ 2 < R ^ 2 - M ^ 2 := by
    have hs := Real.sq_sqrt (le_of_lt (sub_pos.mpr hR2M2))
    have hδnn := le_of_lt hδpos
    nlinarith only [hδRm, hs, hδnn]
  have hδsqtime : δ ^ 2 < -z.2 := by
    have hs := Real.sq_sqrt (le_of_lt hneg)
    have hδnn := le_of_lt hδpos
    nlinarith only [hδtime, hs, hδnn]
  have hRspace := goodPointWitness_spatial_subset (z := z) hRpos hRdomain
  have hRlower := goodPointWitness_lower_time (z := z) hRpos hRdomain
  let B : Set Vec3 := {y | vec3EuclideanNorm (y - z.1) ≤ M}
  let K : Set ParabolicPoint := B ×ˢ Icc (z.2 - M ^ 2 - η) (z.2 + η)
  have hKcompact : IsCompact K := by
    change IsCompact (parabolicHomeomorph ⁻¹'
      (B ×ˢ Icc (z.2 - M ^ 2 - η) (z.2 + η)))
    apply parabolicHomeomorph.isCompact_preimage.mpr
    exact (goodPoint_domain_spatial_ball_compact z.1).prod
      (isCompact_Icc : IsCompact (Icc (z.2 - M ^ 2 - η) (z.2 + η)))
  have hKsub : K ⊆ goodPointDomain := by
    intro q hq
    rcases hq with ⟨hqspace, hqtime⟩
    have hspaceR : q.1 ∈ vec3Ball z.1 R := by
      change vec3EuclideanNorm (q.1 - z.1) < R
      exact lt_of_le_of_lt hqspace hMR
    have hspace : q.1 ∈ vec3Ball 0 1 := hRspace hspaceR
    have hlowR : z.2 - M ^ 2 - η > z.2 - R ^ 2 := by
      have hsum : M ^ 2 + η < R ^ 2 := by linarith only [hηR]
      linarith only [hsum]
    have hlow : -1 < q.2 := by
      have := hqtime.1
      linarith only [hRlower, hlowR, this]
    have htop : q.2 < 0 := by
      have hupper : z.2 + η < 0 := by linarith only [hηt]
      have := hqtime.2
      linarith only [hupper, this]
    exact ⟨hspace, ⟨hlow, htop⟩⟩
  have hnear : ∀ c, parabolicDist c z < δ →
      parabolicCylinder c.1 c.2 r ⊆ K := by
    intro c hcz q hq
    rcases hq with ⟨hqx, hqtlo, hqthi⟩
    have hparts : vec3EuclideanNorm (c.1 - z.1) < δ ∧
        Real.sqrt |c.2 - z.2| < δ := by
      unfold parabolicDist at hcz
      exact max_lt_iff.mp hcz
    have hqxM : vec3EuclideanNorm (q.1 - z.1) ≤ M := by
      exact le_of_lt (calc
        vec3EuclideanNorm (q.1 - z.1) ≤
            vec3EuclideanNorm (q.1 - c.1) + vec3EuclideanNorm (c.1 - z.1) :=
          vec3EuclideanNorm_sub_triang_open _ _ _
        _ < r + δ := add_lt_add hqx hparts.1
        _ < M := by linarith only [hδM])
    have htimeabs : |c.2 - z.2| < δ ^ 2 :=
      (Real.sqrt_lt' (by linarith only [hδpos])).mp hparts.2
    have hcloseLo : z.2 - δ ^ 2 < c.2 := by
      have := (abs_lt.mp htimeabs).1
      linarith only [this]
    have hcloseHi : c.2 < z.2 + δ ^ 2 := by
      have := (abs_lt.mp htimeabs).2
      linarith only [this]
    have hlow : z.2 - M ^ 2 - η ≤ q.2 := by
      have hrM2 : r ^ 2 < M ^ 2 := by nlinarith only [hrpos, hrM]
      have hmargin : δ ^ 2 + r ^ 2 < M ^ 2 + η := by
        linarith only [hδsqη, hrM2]
      linarith only [hqtlo, hcloseLo, hmargin]
    have htop : q.2 ≤ z.2 + η := by
      have hmargin : δ ^ 2 < η := hδsqη
      exact le_trans hqthi (le_of_lt (hcloseHi.trans (by linarith only [hmargin])))
    exact ⟨hqxM, ⟨hlow, htop⟩⟩
  have hlarge : ∀ c, parabolicDist c z < δ →
      goodPointPastCylinder c.1 c.2 M ⊆ goodPointDomain := by
    intro c hcz q hq
    rcases hq with ⟨hqx, hqt⟩
    have hparts : vec3EuclideanNorm (c.1 - z.1) < δ ∧
        Real.sqrt |c.2 - z.2| < δ := by
      unfold parabolicDist at hcz
      exact max_lt_iff.mp hcz
    have hqxR : q.1 ∈ vec3Ball z.1 R := by
      change vec3EuclideanNorm (q.1 - z.1) < R
      calc
        vec3EuclideanNorm (q.1 - z.1) ≤
            vec3EuclideanNorm (q.1 - c.1) + vec3EuclideanNorm (c.1 - z.1) :=
          vec3EuclideanNorm_sub_triang_open _ _ _
        _ < M + δ := add_lt_add hqx hparts.1
        _ < R := by linarith only [hδR]
    have htimeabs : |c.2 - z.2| < δ ^ 2 :=
      (Real.sqrt_lt' (by linarith only [hδpos])).mp hparts.2
    have hcloseLo : z.2 - δ ^ 2 < c.2 := by
      have := (abs_lt.mp htimeabs).1
      linarith only [this]
    have hcloseHi : c.2 < z.2 + δ ^ 2 := by
      have := (abs_lt.mp htimeabs).2
      linarith only [this]
    have hlower : -1 < q.2 := by
      have hmargin : δ ^ 2 + M ^ 2 < R ^ 2 + 0 := by
        linarith only [hδsqRm]
      have : z.2 - R ^ 2 < q.2 := by linarith only [hqt.1, hcloseLo, hmargin]
      linarith only [hRlower, this]
    have hupper : q.2 < 0 := by
      have hclose : c.2 < 0 := lt_trans hcloseHi (by linarith only [hδsqtime])
      exact lt_trans hqt.2 hclose
    exact ⟨hRspace hqxR, ⟨hlower, hupper⟩⟩
  exact ⟨M, η, δ, K, hrM, hMR, hηpos, hδpos, hKcompact, hKsub, hnear, hlarge⟩

private theorem goodPoint_top_ball_subset_past
    {z : ParabolicPoint} {r : ℝ} (hrpos : 0 < r) (htop : z.2 = 0) :
    Metric.ball z (r / 4) ∩ goodPointDomain ⊆
      goodPointPastCylinder z.1 z.2 (r / 2) := by
  intro q hq
  rcases hq with ⟨hball, hqD⟩
  have hdist : parabolicDist q z < r / 4 := by
    simpa only [Metric.mem_ball, dist_eq_parabolicDist] using hball
  have hparts : vec3EuclideanNorm (q.1 - z.1) < r / 4 ∧
      Real.sqrt |q.2 - z.2| < r / 4 := by
    unfold parabolicDist at hdist
    exact max_lt_iff.mp hdist
  have hspace : q.1 ∈ vec3Ball z.1 (r / 2) := by
    change vec3EuclideanNorm (q.1 - z.1) < r / 2
    linarith only [hparts.1, hrpos]
  have htimeabs : |q.2 - z.2| < (r / 4) ^ 2 :=
    (Real.sqrt_lt' (by positivity : (0 : ℝ) < r / 4)).mp hparts.2
  have htimeLower : z.2 - (r / 2) ^ 2 < q.2 := by
    have hlow := (abs_lt.mp htimeabs).1
    rw [htop] at hlow ⊢
    have hlow' : -(r / 4) ^ 2 < q.2 := by simpa using hlow
    nlinarith only [hlow', hrpos]
  have htimeUpper : q.2 < z.2 := by
    rw [htop]
    exact hqD.2.2
  exact ⟨hspace, ⟨htimeLower, htimeUpper⟩⟩

/-- A good point has a local representative with Hölder bounds on both the
open past and the closed top portion of its neighborhood. -/
theorem goodPoint_local_holder_patch
    {ε₀ γ₀ C₄ : ℝ}
    (hC₄ : 0 ≤ C₄)
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
    {z : ParabolicPoint} (hz : z ∈ goodPointClosedTopDomain)
    (hgood : IsGoodPoint ε₀ u p z) :
    ∃ δ Cpatch : ℝ, ∃ w : ParabolicPoint → Vec3,
      0 < δ ∧ 0 ≤ Cpatch ∧
      w =ᵐ[volume.restrict (Metric.ball z δ ∩ goodPointDomain)] u ∧
      ParabolicHolderVecNormLE (Metric.ball z δ ∩ goodPointDomain) w γ₀ Cpatch ∧
      ParabolicHolderVecNormLE (Metric.ball z δ ∩ goodPointClosedTopDomain)
        w γ₀ Cpatch := by
  rcases hgood with ⟨_, R, hRpos, hRdomain, _, hsmallR⟩
  obtain ⟨r, hrpos, hrR, hsmallR'⟩ :=
    exists_smaller_radius_preserving_goodPoint_smallness hRpos hsmallR
  have hrle : r ≤ R := le_of_lt hrR
  have hrsubset : parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 R :=
    parabolicCylinder_mono (le_of_lt hrpos) hrle
  have hsmallr : ENNReal.ofReal (r⁻¹ ^ 2) *
      goodPointEnergy u p z.1 z.2 r < ENNReal.ofReal (ε₀ / 8) :=
    goodPoint_smallness_of_energy_le hsmallR' hrsubset
  let ρ : ℝ := (r + R) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith only [hrR]
  have hρR : ρ < R := by dsimp [ρ]; linarith only [hrR]
  have hρpos : 0 < ρ := lt_trans hrpos hrρ
  have hdomρ := goodPoint_smaller_radius_admissible hz hRpos hρpos hρR hRdomain
  have hglobalData := goodPoint_global_data hSuitable
  let B : ℝ := 2 * C₄ * r⁻¹
  let H : ℝ := 4 * C₄ * r⁻¹ * (8 * r⁻¹) ^ γ₀
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 ≤ B + H := add_nonneg hB hH
  have htopCenter : z.2 = 0 ∨ z.2 < 0 := by
    rcases hz with ⟨_, hzt⟩
    rcases hzt with ⟨_, hzle⟩
    by_cases hzero : z.2 = 0
    · exact Or.inl hzero
    · exact Or.inr (lt_of_le_of_ne hzle hzero)
  rcases htopCenter with htop | hinterior
  · let δ : ℝ := r / 4
    have hδpos : 0 < δ := by dsimp [δ]; positivity
    have hUsub : Metric.ball z δ ∩ goodPointDomain ⊆
        goodPointPastCylinder z.1 z.2 (r / 2) := by
      simpa only [δ] using goodPoint_top_ball_subset_past hrpos htop
    have hSuitableρ := suitable_on_goodPointPastCylinder hSuitable hρpos hdomρ.1
    obtain ⟨w, hwae, hwbound, hwsemi⟩ :=
      hTop z.1 z.2 ρ r u Du p hrpos hrρ hSuitableρ hsmallr
    have hUae : w =ᵐ[volume.restrict (Metric.ball z δ ∩ goodPointDomain)] u :=
      ae_restrict_of_ae_restrict_of_subset hUsub hwae
    have hHolder : ParabolicHolderVecNormLE
        (Metric.ball z δ ∩ goodPointDomain) w γ₀ (B + H) := by
      refine ⟨B, H, hB, hH, le_rfl, ?_, ?_⟩
      · intro q hq
        exact (hwbound q (subset_closure (hUsub hq)))
      · intro q hq q' hq'
        exact hwsemi q (subset_closure (hUsub hq))
          q' (subset_closure (hUsub hq'))
    have hTopSub : Metric.ball z δ ∩ goodPointClosedTopDomain ⊆
        closure (goodPointPastCylinder z.1 z.2 (r / 2)) :=
      goodPoint_top_neighborhood_in_closure_past hrpos rfl htop
    have hHolderTop : ParabolicHolderVecNormLE
        (Metric.ball z δ ∩ goodPointClosedTopDomain) w γ₀ (B + H) := by
      refine ⟨B, H, hB, hH, le_rfl, ?_, ?_⟩
      · intro q hq
        exact hwbound q (hTopSub hq)
      · intro q hq q' hq'
        exact hwsemi q (hTopSub hq) q' (hTopSub hq')
    exact ⟨δ, B + H, w, hδpos, hC, hUae, hHolder, hHolderTop⟩
  · obtain ⟨M, η, δ₀, K, hrM, hMR, hηpos, hδ₀pos, hKcompact, hKdomain,
      hKnear, hMdomain⟩ := goodPointInteriorCompact hinterior hRpos hrpos hrR hRdomain
    have hEnergyCont := goodPointEnergy_continuousAt_of_compact
      hglobalData hKcompact hKdomain hδ₀pos hKnear
    let k : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 2)
    have hkfinite : k ≠ ⊤ := ENNReal.ofReal_ne_top
    have hkcont : ContinuousAt (fun e : ℝ≥0∞ => k * e)
        (goodPointEnergy u p z.1 z.2 r) :=
      (ENNReal.continuous_const_mul hkfinite).continuousAt
    have hScaled : Tendsto
        (fun c => k * goodPointEnergy u p c.1 c.2 r) (𝓝 z)
        (𝓝 (k * goodPointEnergy u p z.1 z.2 r)) :=
      hkcont.tendsto.comp hEnergyCont
    have hsmallEvent : ∀ᶠ c : ParabolicPoint in 𝓝 z,
        k * goodPointEnergy u p c.1 c.2 r < ENNReal.ofReal (ε₀ / 8) :=
      hScaled.eventually (isOpen_Iio.mem_nhds hsmallr)
    obtain ⟨dE, hdEpos, hdEball⟩ := Metric.eventually_nhds_iff.mp hsmallEvent
    let a := min dE (min (Real.sqrt (-z.2)) r)
    have hrootpos : 0 < Real.sqrt (-z.2) :=
      Real.sqrt_pos.2 (neg_pos.mpr hinterior)
    have hap : 0 < a := by
      dsimp [a]
      exact lt_min hdEpos (lt_min hrootpos hrpos)
    have haE : a ≤ dE := by dsimp [a]; exact min_le_left _ _
    have hat : a ≤ Real.sqrt (-z.2) := by
      dsimp [a]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have har : a ≤ r := by
      dsimp [a]
      exact (min_le_right _ _).trans (min_le_right _ _)
    let σ : ℝ := (a / 4) ^ 2
    have hσpos : 0 < σ := by dsimp [σ]; positivity
    have hσtop : σ < -z.2 := by
      have hs := Real.sq_sqrt (le_of_lt (neg_pos.mpr hinterior))
      have ha2 : a / 4 < Real.sqrt (-z.2) := by
        nlinarith only [hat, hap, hrootpos]
      dsimp [σ]
      have ha_nonneg : 0 ≤ a / 4 := by positivity
      nlinarith only [ha2, hs, ha_nonneg, hrootpos]
    have hσr : σ < r ^ 2 / 4 := by
      have hr2 : 0 < r := hrpos
      have ha2 : a / 4 < r / 2 := by nlinarith only [har, hr2, hap]
      dsimp [σ]
      have ha_nonneg : 0 ≤ a / 4 := by positivity
      have hrhalf_nonneg : 0 ≤ r / 2 := by positivity
      nlinarith only [ha2, hr2, ha_nonneg, hrhalf_nonneg]
    have hsqrtσ : Real.sqrt σ = a / 4 := by
      dsimp [σ]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have hshiftDist : parabolicDist (z.1, z.2 + σ) z < dE := by
      have hspace : vec3EuclideanNorm (z.1 - z.1) = 0 := by
        simp [vec3EuclideanNorm_zero]
      have htime : Real.sqrt |z.2 + σ - z.2| = a / 4 := by
        have hshift : z.2 + σ - z.2 = σ := by ring
        rw [hshift, abs_of_pos hσpos, hsqrtσ]
      unfold parabolicDist
      rw [hspace, htime]
      change max 0 (a / 4) < dE
      exact max_lt_iff.mpr ⟨by linarith only [hdEpos], by linarith only [haE, hap]⟩
    have hsmallShift : k * goodPointEnergy u p z.1 (z.2 + σ) r <
        ENNReal.ofReal (ε₀ / 8) := by
      exact hdEball (by simpa only [dist_eq_parabolicDist] using hshiftDist)
    have hRspace := goodPointWitness_spatial_subset (z := z) hRpos hRdomain
    have hRlower := goodPointWitness_lower_time (z := z) hRpos hRdomain
    have hMpos : 0 < M := lt_trans hrpos hrM
    have hshiftDomain : goodPointPastCylinder z.1 (z.2 + σ) M ⊆ goodPointDomain := by
      intro q hq
      rcases hq with ⟨hqx, hqt⟩
      have hspace : q.1 ∈ vec3Ball 0 1 := by
        have hqxR : q.1 ∈ vec3Ball z.1 R := by
          change vec3EuclideanNorm (q.1 - z.1) < R
          exact lt_of_lt_of_le hqx hMR.le
        exact hRspace hqxR
      have htime : q.2 ∈ Ioo (-1) 0 := by
        constructor
        · have hshiftLow : z.2 + σ - M ^ 2 > z.2 - R ^ 2 := by
            have hMRsq : M ^ 2 < R ^ 2 := by nlinarith only [hMpos, hMR, hRpos]
            linarith only [hσpos, hMRsq]
          linarith only [hqt.1, hshiftLow, hRlower]
        · have htop : z.2 + σ < 0 := by linarith only [hσtop]
          exact lt_trans hqt.2 htop
      exact ⟨hspace, htime⟩
    have hSuitableShift := suitable_on_goodPointPastCylinder hSuitable hMpos hshiftDomain
    obtain ⟨w, hwae, hwbound, hwsemi⟩ :=
      hTop z.1 (z.2 + σ) M r u Du p hrpos hrM hSuitableShift hsmallShift
    let P := goodPointPastCylinder z.1 (z.2 + σ) (r / 2)
    have hzP : z ∈ P := by
      change z.1 ∈ vec3Ball z.1 (r / 2) ∧
        z.2 ∈ Ioo (z.2 + σ - (r / 2) ^ 2) (z.2 + σ)
      constructor
      · simp [vec3Ball, vec3EuclideanNorm_zero, hrpos]
      · constructor
        · nlinarith only [hσr]
        · linarith only [hσpos]
    have hPopen : IsOpen P := by
      change IsOpen (spaceTimeSet (vec3Ball z.1 (r / 2))
        (Ioo (z.2 + σ - (r / 2) ^ 2) (z.2 + σ)))
      exact isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo
    obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp hPopen z hzP
    have hUsub : Metric.ball z δ ∩ goodPointDomain ⊆ P := by
      intro q hq
      exact hball hq.1
    have hUae : w =ᵐ[volume.restrict (Metric.ball z δ ∩ goodPointDomain)] u :=
      ae_restrict_of_ae_restrict_of_subset hUsub hwae
    have hHolder : ParabolicHolderVecNormLE
        (Metric.ball z δ ∩ goodPointDomain) w γ₀ (B + H) := by
      refine ⟨B, H, hB, hH, le_rfl, ?_, ?_⟩
      · intro q hq
        exact hwbound q (subset_closure (hUsub hq))
      · intro q hq q' hq'
        exact hwsemi q (subset_closure (hUsub hq))
          q' (subset_closure (hUsub hq'))
    have hHolderTop : ParabolicHolderVecNormLE
        (Metric.ball z δ ∩ goodPointClosedTopDomain) w γ₀ (B + H) := by
      refine ⟨B, H, hB, hH, le_rfl, ?_, ?_⟩
      · intro q hq
        exact hwbound q (subset_closure (hball hq.1))
      · intro q hq q' hq'
        exact hwsemi q (subset_closure (hball hq.1))
          q' (subset_closure (hball hq'.1))
    exact ⟨δ, B + H, w, hδpos, hC, hUae, hHolder, hHolderTop⟩

private theorem goodPoint_isLocallyOpen
    {ε₀ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0))
    {z : ParabolicPoint} (hz : z ∈ goodPointClosedTopDomain)
    (hgood : IsGoodPoint ε₀ u p z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ParabolicPoint,
      parabolicDist c z < δ → c ∈ goodPointClosedTopDomain →
      IsGoodPoint ε₀ u p c := by
  rcases hgood with ⟨_, R, hRpos, hRdomain, _, hsmallR⟩
  obtain ⟨r, hrpos, hrR, hsmallR'⟩ :=
    exists_smaller_radius_preserving_goodPoint_smallness hRpos hsmallR
  have hrsubset : parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 R :=
    parabolicCylinder_mono (le_of_lt hrpos) (le_of_lt hrR)
  have hsmallr : ENNReal.ofReal (r⁻¹ ^ 2) *
      goodPointEnergy u p z.1 z.2 r < ENNReal.ofReal (ε₀ / 8) :=
    goodPoint_smallness_of_energy_le hsmallR' hrsubset
  let M : ℝ := (r + R) / 2
  have hrM : r < M := by dsimp [M]; linarith only [hrR]
  have hMR : M < R := by dsimp [M]; linarith only [hrR]
  have hMpos : 0 < M := lt_trans hrpos hrM
  rcases hz with ⟨_, hzt⟩
  rcases hzt with ⟨_, hztle⟩
  by_cases htop : z.2 = 0
  · have hmargin : 0 < R ^ 2 - M ^ 2 := by
      nlinarith only [hMpos, hMR, hRpos]
    let d := min (R - M) (Real.sqrt (R ^ 2 - M ^ 2))
    have hdpos : 0 < d := by dsimp [d]; positivity
    let δ := d / 2
    have hδpos : 0 < δ := by dsimp [δ]; positivity
    have hδd : δ < d := by dsimp [δ]; linarith only [hdpos]
    have hdspace : d ≤ R - M := by dsimp [d]; exact min_le_left _ _
    have hdtime : d ≤ Real.sqrt (R ^ 2 - M ^ 2) := by
      dsimp [d]
      exact min_le_right _ _
    have hδM : δ ≤ R - M := le_of_lt (lt_of_lt_of_le hδd hdspace)
    have hδsq : δ ^ 2 ≤ R ^ 2 - M ^ 2 := by
      have hδsqrt : δ < Real.sqrt (R ^ 2 - M ^ 2) := lt_of_lt_of_le hδd hdtime
      have hs := Real.sq_sqrt (le_of_lt hmargin)
      nlinarith only [hδsqrt, hs, (show 0 ≤ δ from le_of_lt hδpos)]
    have hδr : δ ≤ R - r := by linarith only [hδM, hrM]
    have hδsqR : δ ^ 2 ≤ R ^ 2 - r ^ 2 := by
      have hMr : r ^ 2 ≤ M ^ 2 := by nlinarith only [hrpos, hrM]
      linarith only [hδsq, hMr]
    refine ⟨δ, hδpos, ?_⟩
    intro c hdist hc
    have hccandidate := hc
    rcases hc with ⟨_, hct⟩
    have hcTop : c.2 ≤ 0 := hct.2
    have hMdomain := goodPointPastCylinder_subset_domain_of_top_near
      hδpos hδM hδsq htop hcTop hdist hRdomain
    have hadmiss := goodPoint_smaller_radius_admissible hccandidate hMpos hrpos hrM hMdomain
    have hfull := goodPointFullCylinder_subset_of_top_near
      hδpos hδr hδsqR htop hcTop hdist
    have hsmallc := goodPoint_smallness_of_energy_le hsmallR' hfull
    exact ⟨hccandidate, r, hrpos, hadmiss.1, hadmiss.2, hsmallc⟩
  · have hinterior : z.2 < 0 := lt_of_le_of_ne hztle htop
    obtain ⟨M, η, δ₀, K, hrM', hMR', hηpos, hδ₀pos, hKcompact, hKdomain,
      hKnear, hMdomain⟩ := goodPointInteriorCompact hinterior
        hRpos hrpos hrR hRdomain
    have hglobalData := goodPoint_global_data hSuitable
    have hEnergyCont := goodPointEnergy_continuousAt_of_compact
      hglobalData hKcompact hKdomain hδ₀pos hKnear
    let k : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 2)
    have hkfinite : k ≠ ⊤ := ENNReal.ofReal_ne_top
    have hScaled : Tendsto
        (fun c => k * goodPointEnergy u p c.1 c.2 r) (𝓝 z)
        (𝓝 (k * goodPointEnergy u p z.1 z.2 r)) :=
      (ENNReal.continuous_const_mul hkfinite).continuousAt.tendsto.comp hEnergyCont
    have hsmallEvent : ∀ᶠ c : ParabolicPoint in 𝓝 z,
        k * goodPointEnergy u p c.1 c.2 r < ENNReal.ofReal (ε₀ / 8) :=
      hScaled.eventually (isOpen_Iio.mem_nhds hsmallr)
    obtain ⟨δE, hδEpos, hδEball⟩ := Metric.eventually_nhds_iff.mp hsmallEvent
    let δ := min δ₀ δE
    have hδpos : 0 < δ := by dsimp [δ]; positivity
    have hδ₀ : δ ≤ δ₀ := by dsimp [δ]; exact min_le_left _ _
    have hδE : δ ≤ δE := by dsimp [δ]; exact min_le_right _ _
    refine ⟨δ, hδpos, ?_⟩
    intro c hdist hc
    have hdom := hMdomain c (lt_of_lt_of_le hdist hδ₀)
    have hMpos : 0 < M := lt_trans hrpos hrM'
    have hadmiss := goodPoint_smaller_radius_admissible hc
      hMpos hrpos hrM' hdom
    have hsmallc : k * goodPointEnergy u p c.1 c.2 r < ENNReal.ofReal (ε₀ / 8) := by
      apply hδEball
      simpa only [Metric.mem_ball, dist_eq_parabolicDist] using
        (lt_of_lt_of_le hdist hδE)
    have hsmallc' : ENNReal.ofReal (r⁻¹ ^ 2) *
        goodPointEnergy u p c.1 c.2 r < ENNReal.ofReal (ε₀ / 8) := by
      simpa only [k] using hsmallc
    exact ⟨hc, r, hrpos, hadmiss.1, hadmiss.2, hsmallc'⟩

/-- Good points form a relatively open subset of the closed top domain. -/
theorem goodPoint_set_relative_open
    {ε₀ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0)) :
    IsOpen {z : {q : ParabolicPoint // q ∈ goodPointClosedTopDomain} |
      IsGoodPoint ε₀ u p z.1} := by
  rw [Metric.isOpen_iff]
  rintro ⟨z, hz⟩ hgood
  obtain ⟨δ, hδ, hnear⟩ := goodPoint_isLocallyOpen hSuitable hz hgood
  refine ⟨δ, hδ, ?_⟩
  intro c hc
  have hdist : parabolicDist c.1 z < δ := by
    have hd : dist c ⟨z, hz⟩ < δ := Metric.mem_ball.mp hc
    simpa only [Subtype.dist_eq, dist_eq_parabolicDist] using hd
  exact hnear c.1 hdist c.2

end ESS
