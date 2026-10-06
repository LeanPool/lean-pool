/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsDefinition
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsRescaled
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HolderGluing
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Epsilon regularity at a top face

This file proves the one-sided Hölder estimate of `lem:thmA-top` from the
rescaled form of CKN Theorem A.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem goodPoint_shifted_small
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {x₀ x : Vec3} {t₀ s r ε₀ : ℝ}
    (hr : 0 < r) (hε₀ : 0 < ε₀)
    (hshift : parabolicCylinder x (t₀ - s) (r / 2) ⊆
      parabolicCylinder x₀ t₀ r)
    (hsmall : ENNReal.ofReal (r⁻¹ ^ 2) *
      goodPointEnergy u p x₀ t₀ r < ENNReal.ofReal (ε₀ / 8)) :
    goodPointEnergy u p x (t₀ - s) (r / 2) *
      ENNReal.ofReal ((r / 2)⁻¹ ^ 2) < ENNReal.ofReal ε₀ := by
  have henergy := goodPointEnergy_mono (u := u) (p := p) hshift
  have hinv : (r / 2)⁻¹ ^ 2 = 4 * r⁻¹ ^ 2 := by
    field_simp
    ring
  have hweight : ENNReal.ofReal ((r / 2)⁻¹ ^ 2) =
      ENNReal.ofReal 4 * ENNReal.ofReal (r⁻¹ ^ 2) := by
    rw [hinv, ENNReal.ofReal_mul (by norm_num)]
  have hweighted : goodPointEnergy u p x (t₀ - s) (r / 2) *
      ENNReal.ofReal ((r / 2)⁻¹ ^ 2) ≤
      ENNReal.ofReal 4 *
        (ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r) := by
    rw [hweight]
    calc
      goodPointEnergy u p x (t₀ - s) (r / 2) *
          (ENNReal.ofReal 4 * ENNReal.ofReal (r⁻¹ ^ 2)) =
          ENNReal.ofReal 4 *
            (goodPointEnergy u p x (t₀ - s) (r / 2) *
              ENNReal.ofReal (r⁻¹ ^ 2)) := by ac_rfl
      _ ≤ ENNReal.ofReal 4 *
          (goodPointEnergy u p x₀ t₀ r * ENNReal.ofReal (r⁻¹ ^ 2)) := by
        have hbase := mul_le_mul_right henergy (ENNReal.ofReal (r⁻¹ ^ 2))
        have houter := mul_le_mul_right hbase (ENNReal.ofReal 4)
        calc
          _ = ENNReal.ofReal 4 *
              (ENNReal.ofReal (r⁻¹ ^ 2) *
                goodPointEnergy u p x (t₀ - s) (r / 2)) := by ac_rfl
          _ ≤ ENNReal.ofReal 4 *
              (ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r) := houter
          _ = _ := by ac_rfl
      _ = ENNReal.ofReal 4 *
          (ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r) := by ac_rfl
  calc
    goodPointEnergy u p x (t₀ - s) (r / 2) *
        ENNReal.ofReal ((r / 2)⁻¹ ^ 2) ≤
        ENNReal.ofReal 4 *
          (ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r) :=
      hweighted
    _ < ENNReal.ofReal 4 * ENNReal.ofReal (ε₀ / 8) :=
      ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal 4 ≠ 0)
        ENNReal.ofReal_ne_top hsmall
    _ = ENNReal.ofReal (ε₀ / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ < ENNReal.ofReal ε₀ := by
      rw [ENNReal.ofReal_lt_ofReal_iff hε₀]
      linarith only [hε₀]

/-- Centers for the top-time patches, with spatial and positive-time offsets bounded by `r`. -/
@[expose] def goodPointTopCenter (x₀ : Vec3) (r : ℝ) : Set ParabolicPoint :=
  {c | c.1 ∈ vec3Ball x₀ (r / 2) ∧ c.2 ∈ Ioo 0 (r ^ 2 / 4)}

/-- The backward parabolic cylinder used as the patch based at `c`. -/
@[expose] def goodPointTopPatch (t₀ r : ℝ) (c : ParabolicPoint) :
    Set ParabolicPoint :=
  goodPointPastCylinder c.1 (t₀ - c.2) (r / 4)

private theorem vec3EuclideanNorm_sub_le (v w : Vec3) :
    vec3EuclideanNorm (v - w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
  exact norm_sub_le _ _

private theorem vec3EuclideanNorm_add_le (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem goodPointTop_shift_cylinder_subset
    {x₀ x : Vec3} {t₀ r s : ℝ}
    (hc : (x, s) ∈ goodPointTopCenter x₀ r) :
    parabolicCylinder x (t₀ - s) (r / 2) ⊆ parabolicCylinder x₀ t₀ r := by
  rcases hc with ⟨hx, hs⟩
  rcases hs with ⟨hspos, hslt⟩
  intro z hz
  rcases (mem_parabolicCylinder).mp hz with ⟨hzx, hztlo, hzthi⟩
  change vec3EuclideanNorm (z.1 - x₀) < r ∧ t₀ - r ^ 2 < z.2 ∧ z.2 ≤ t₀
  refine ⟨?_, ?_, ?_⟩
  · calc
      vec3EuclideanNorm (z.1 - x₀) =
          vec3EuclideanNorm ((z.1 - x) + (x - x₀)) := by congr 1; abel
      _ ≤ vec3EuclideanNorm (z.1 - x) + vec3EuclideanNorm (x - x₀) :=
        vec3EuclideanNorm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add hzx hx
      _ = r := by ring
  · have hlow : t₀ - r ^ 2 < (t₀ - s) - (r / 2) ^ 2 := by
      nlinarith only [hslt, sq_nonneg r]
    exact hlow.trans hztlo
  · have htop : t₀ - s ≤ t₀ := by linarith only [hspos]
    exact hzthi.trans htop

private theorem goodPointTop_shift_closure_subset
    {x₀ x : Vec3} {t₀ ρ r s : ℝ}
    (hρ : r < ρ) (hr : 0 < r)
    (hc : (x, s) ∈ goodPointTopCenter x₀ r) :
    closure (parabolicCylinder x (t₀ - s) (r / 2)) ⊆
      spaceTimeSet (vec3Ball x₀ ρ) (Ioo (t₀ - ρ ^ 2) t₀) := by
  have hs : s ∈ Ioo 0 (r ^ 2 / 4) := hc.2
  have hrhalf : 0 < r / 2 := by positivity
  have hlow : t₀ - ρ ^ 2 < t₀ - s - (r / 2) ^ 2 := by
    have hρ2 : r ^ 2 < ρ ^ 2 := by nlinarith only [hρ, hr]
    nlinarith only [hρ2, hs.2]
  intro z hz
  rw [closure_parabolicCylinder hrhalf] at hz
  rcases hz with ⟨hzx, hzt⟩
  rcases hzt with ⟨hzlo, hzhi⟩
  have hx : vec3EuclideanNorm (x - x₀) < r / 2 := hc.1
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · have hnormlt : vec3EuclideanNorm (z.1 - x₀) < r := by
      calc
        vec3EuclideanNorm (z.1 - x₀) =
            vec3EuclideanNorm ((z.1 - x) + (x - x₀)) := by congr 1; abel
        _ ≤ vec3EuclideanNorm (z.1 - x) + vec3EuclideanNorm (x - x₀) :=
          vec3EuclideanNorm_add_le _ _
        _ ≤ r / 2 + vec3EuclideanNorm (x - x₀) := add_le_add_left hzx _
        _ < r / 2 + r / 2 := by linarith only [hx]
        _ = r := by ring
    exact hnormlt.trans hρ
  · exact hlow.trans_le hzlo
  · calc
      z.2 ≤ t₀ - s := hzhi
      _ < t₀ := by linarith only [hs.1]

private theorem vec3EuclideanNorm_sub_comm (v w : Vec3) :
    vec3EuclideanNorm (v - w) = vec3EuclideanNorm (w - v) := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, WithLp.toLp_sub,
    WithLp.toLp_sub, norm_sub_rev]

private theorem parabolicDist_comm (z z' : ParabolicPoint) :
    parabolicDist z z' = parabolicDist z' z := by
  rw [← dist_eq_parabolicDist, dist_comm, dist_eq_parabolicDist]

private theorem goodPointTop_pair_patch_ordered
    {x₀ : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    {later earlier : ParabolicPoint}
    (hlater : later ∈ goodPointPastCylinder x₀ t₀ (r / 2))
    (hearlier : earlier ∈ goodPointPastCylinder x₀ t₀ (r / 2))
    (horder : earlier.2 ≤ later.2)
    (hd : parabolicDist later earlier < r / 8) :
    ∃ c : ParabolicPoint, c ∈ goodPointTopCenter x₀ r ∧
      later ∈ goodPointTopPatch t₀ r c ∧ earlier ∈ goodPointTopPatch t₀ r c := by
  rcases hlater with ⟨hlaterx, hlaterT⟩
  rcases hlaterT with ⟨hlaterlo, hlatertop⟩
  rcases hearlier with ⟨hearlierx, hearlierT⟩
  rcases hearlierT with ⟨hearlierlo, hearliertop⟩
  have hdist := max_lt_iff.mp hd
  have hspace : vec3EuclideanNorm (later.1 - earlier.1) < r / 8 := hdist.1
  have htimeRoot : Real.sqrt |later.2 - earlier.2| < r / 8 := hdist.2
  have htime : |later.2 - earlier.2| < (r / 8) ^ 2 :=
    (Real.sqrt_lt' (by positivity : 0 < r / 8)).mp htimeRoot
  have htimeNonneg : 0 ≤ later.2 - earlier.2 := sub_nonneg.mpr horder
  rw [abs_of_nonneg htimeNonneg] at htime
  let a := t₀ - later.2
  let b := t₀ - earlier.2
  let m := min (a / 2) (r ^ 2 / 64)
  let s := a - m
  let c : ParabolicPoint := (later.1, s)
  have ha : 0 < a ∧ a < r ^ 2 / 4 := by
    dsimp [a]
    constructor <;> nlinarith only [hlaterlo, hlatertop]
  have hmpos : 0 < m := by
    dsimp [m]
    positivity
  have hmA : m ≤ a / 2 := min_le_left _ _
  have hmR : m ≤ r ^ 2 / 64 := min_le_right _ _
  have hspos : 0 < s := by dsimp [s]; nlinarith only [ha.1, hmA]
  have hslt : s < r ^ 2 / 4 := by dsimp [s]; nlinarith only [ha.2, hmpos]
  have hdiff : 0 ≤ b - a ∧ b - a < r ^ 2 / 64 := by
    constructor
    · dsimp [a, b]
      linarith only [horder]
    · dsimp [a, b]
      nlinarith only [htime]
  have hlater_patch : later ∈ goodPointTopPatch t₀ r c := by
    change later.1 ∈ vec3Ball later.1 (r / 4) ∧
      later.2 ∈ Ioo (t₀ - s - (r / 4) ^ 2) (t₀ - s)
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · simp [vec3Ball, vec3EuclideanNorm_zero, hr]
    · dsimp [a, s]
      have hmpos' : 0 < min ((t₀ - later.2) / 2) (r ^ 2 / 64) := by positivity
      have hmR' : min ((t₀ - later.2) / 2) (r ^ 2 / 64) < (r / 4) ^ 2 := by
        calc
          min ((t₀ - later.2) / 2) (r ^ 2 / 64) ≤ r ^ 2 / 64 := min_le_right _ _
          _ < (r / 4) ^ 2 := by nlinarith only [hr]
      nlinarith only [hmR']
    · dsimp [a, s]
      nlinarith only [hmpos]
  have hearlier_patch : earlier ∈ goodPointTopPatch t₀ r c := by
    change earlier.1 ∈ vec3Ball later.1 (r / 4) ∧
      earlier.2 ∈ Ioo (t₀ - s - (r / 4) ^ 2) (t₀ - s)
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · have hspace' : vec3EuclideanNorm (earlier.1 - later.1) < r / 4 := by
        rw [vec3EuclideanNorm_sub_comm]
        exact hspace.trans (by nlinarith only [hr])
      exact hspace'
    · dsimp [a, b, s]
      have hmR' : m ≤ (r / 4) ^ 2 := by
        calc
          m ≤ r ^ 2 / 64 := hmR
          _ ≤ (r / 4) ^ 2 := by nlinarith only [hr]
      have hrSq : 0 ≤ r ^ 2 := sq_nonneg r
      nlinarith only [hmR, hdiff.2, hrSq]
    · dsimp [a, b, s]
      have hba : a ≤ b := sub_nonneg.mp hdiff.1
      nlinarith only [hba, hmpos]
  refine ⟨c, ?_, hlater_patch, hearlier_patch⟩
  change later.1 ∈ vec3Ball x₀ (r / 2) ∧ s ∈ Ioo 0 (r ^ 2 / 4)
  exact ⟨hlaterx, ⟨hspos, hslt⟩⟩

private theorem goodPointTop_pair_patch
    {x₀ : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    {z z' : ParabolicPoint}
    (hz : z ∈ goodPointPastCylinder x₀ t₀ (r / 2))
    (hz' : z' ∈ goodPointPastCylinder x₀ t₀ (r / 2))
    (hd : parabolicDist z z' < r / 8) :
    ∃ c : ParabolicPoint, c ∈ goodPointTopCenter x₀ r ∧
      z ∈ goodPointTopPatch t₀ r c ∧ z' ∈ goodPointTopPatch t₀ r c := by
  rcases le_total z.2 z'.2 with hzz' | hz'z
  · obtain ⟨c, hc, hz'c, hzc⟩ := goodPointTop_pair_patch_ordered hr hz' hz hzz'
      ((parabolicDist_comm _ _).symm ▸ hd)
    exact ⟨c, hc, hzc, hz'c⟩
  · exact goodPointTop_pair_patch_ordered hr hz hz' hz'z hd

/-- The local Hölder seminorm bound at scale `r/2` with constant `C₄`. -/
@[expose] def goodPointTopLocalHolderBound (C₄ r γ : ℝ) : ℝ :=
  C₄ * ((r / 2)⁻¹ * ((r / 2)⁻¹) ^ γ)

/-- A uniform Hölder bound obtained by enlarging the local bound to scale `r`. -/
@[expose] def goodPointTopHolderBound (C₄ r γ : ℝ) : ℝ :=
  4 * C₄ * r⁻¹ * (8 * r⁻¹) ^ γ

private theorem goodPointTop_localHolderBound_le
    {C₄ r γ : ℝ} (hC₄ : 0 ≤ C₄) (hr : 0 < r) (hγ : 0 < γ) :
    goodPointTopLocalHolderBound C₄ r γ ≤ goodPointTopHolderBound C₄ r γ := by
  have hrinv : (r / 2)⁻¹ = 2 * r⁻¹ := by
    field_simp
  have hpow : (2 * r⁻¹) ^ γ ≤ (8 * r⁻¹) ^ γ := by
    apply Real.rpow_le_rpow (by positivity)
    · have hrinvpos : 0 < r⁻¹ := inv_pos.mpr hr
      nlinarith only [hrinvpos]
    · exact hγ.le
  rw [goodPointTopLocalHolderBound, goodPointTopHolderBound, hrinv]
  calc
    C₄ * (2 * r⁻¹ * (2 * r⁻¹) ^ γ) ≤
        C₄ * (2 * r⁻¹ * (8 * r⁻¹) ^ γ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (by positivity)) hC₄
    _ = 2 * C₄ * r⁻¹ * (8 * r⁻¹) ^ γ := by ring
    _ ≤ 4 * C₄ * r⁻¹ * (8 * r⁻¹) ^ γ := by
      have hcoef : 0 ≤ C₄ * r⁻¹ * (8 * r⁻¹) ^ γ := by positivity
      nlinarith only [hcoef]

private theorem goodPointPastCylinder_subset_topPatches
    {x₀ : Vec3} {t₀ r : ℝ} (hr : 0 < r) :
    goodPointPastCylinder x₀ t₀ (r / 2) ⊆
      ⋃ c ∈ goodPointTopCenter x₀ r, goodPointTopPatch t₀ r c := by
  intro z hz
  rcases hz with ⟨hzx, hzt⟩
  rcases hzt with ⟨hzlo, hztop⟩
  let a := t₀ - z.2
  let m := min (a / 2) (r ^ 2 / 64)
  let s := a - m
  have ha : 0 < a ∧ a < r ^ 2 / 4 := by
    dsimp [a]
    constructor <;> nlinarith only [hzlo, hztop, hr]
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hmA : m ≤ a / 2 := min_le_left _ _
  have hmR : m ≤ r ^ 2 / 64 := min_le_right _ _
  have hspos : 0 < s := by dsimp [s]; nlinarith only [ha.1, hmA]
  have hslt : s < r ^ 2 / 4 := by dsimp [s]; nlinarith only [ha.2, hmpos]
  let c : ParabolicPoint := (z.1, s)
  have hc : c ∈ goodPointTopCenter x₀ r := by
    change z.1 ∈ vec3Ball x₀ (r / 2) ∧ s ∈ Ioo 0 (r ^ 2 / 4)
    exact ⟨hzx, ⟨hspos, hslt⟩⟩
  have hpatch : z ∈ goodPointTopPatch t₀ r c := by
    change z.1 ∈ vec3Ball z.1 (r / 4) ∧
      z.2 ∈ Ioo (t₀ - s - (r / 4) ^ 2) (t₀ - s)
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · simp [vec3Ball, vec3EuclideanNorm_zero, hr]
    · dsimp [a, s]
      have hmR' : m < (r / 4) ^ 2 := by
        calc
          m ≤ r ^ 2 / 64 := hmR
          _ < (r / 4) ^ 2 := by nlinarith only [hr]
      nlinarith only [hmR']
    · dsimp [a, s]
      nlinarith only [hmpos]
  exact Set.mem_iUnion₂.mpr ⟨c, hc, hpatch⟩

private theorem goodPoint_holder_bound_of_dense
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {S : Set X} {F : X → Y} {K γ : ℝ}
    (hF : Continuous F) (hγ : 0 ≤ γ) (hdense : Dense S)
    (hbound : ∀ z ∈ S, ∀ z' ∈ S,
      dist (F z) (F z') ≤ K * dist z z' ^ γ) :
    ∀ z z', dist (F z) (F z') ≤ K * dist z z' ^ γ := by
  let A : Set (X × X) := {q | dist (F q.1) (F q.2) ≤ K * dist q.1 q.2 ^ γ}
  have hleft : Continuous (fun q : X × X => dist (F q.1) (F q.2)) :=
    (hF.comp continuous_fst).dist (hF.comp continuous_snd)
  have hd : Continuous (fun q : X × X => dist q.1 q.2) :=
    continuous_fst.dist continuous_snd
  have hright : Continuous (fun q : X × X => K * dist q.1 q.2 ^ γ) :=
    continuous_const.mul ((Real.continuous_rpow_const hγ).comp hd)
  have hclosed : IsClosed A := isClosed_le hleft hright
  have hsub : S ×ˢ S ⊆ A := by
    intro q hq
    exact hbound q.1 hq.1 q.2 hq.2
  have hclosure : closure (S ×ˢ S) ⊆ A := closure_minimal hsub hclosed
  intro z z'
  change (z, z') ∈ A
  apply hclosure
  rw [(hdense.prod hdense).closure_eq]
  trivial

private theorem goodPoint_holder_extend_closure
    {V : Set ParabolicPoint} {g : ParabolicPoint → Vec3}
    {B K γ : ℝ} (hVopen : IsOpen V) (hγ : 0 < γ) (hK : 0 ≤ K)
    (hbound : ∀ z ∈ V, vec3EuclideanNorm (g z) ≤ B)
    (hholder : ∀ z ∈ V, ∀ z' ∈ V,
      vec3EuclideanNorm (g z - g z') ≤ K * parabolicDist z z' ^ γ) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict V] g ∧
      (∀ z ∈ closure V, vec3EuclideanNorm (w z) ≤ B) ∧
      (∀ z ∈ closure V, ∀ z' ∈ closure V,
        vec3EuclideanNorm (w z - w z') ≤ K * parabolicDist z z' ^ γ) := by
  classical
  let closureV : Set ParabolicPoint := closure V
  let inc : V → closureV := inclusion subset_closure
  have hincUE : IsUniformEmbedding inc := isUniformEmbedding_set_inclusion subset_closure
  have hincDense : DenseRange inc :=
    (denseRange_inclusion_iff subset_closure).2 subset_rfl
  have hincDI := hincUE.isUniformInducing.isDenseInducing hincDense
  let f : V → WithLp 2 Vec3 := fun z => WithLp.toLp 2 (g z)
  let Knn : ℝ≥0 := ⟨K, hK⟩
  have hfHolder : HolderOnWith ⟨K, hK⟩ ⟨γ, hγ.le⟩ f univ := by
    intro z _ z' _
    have h := hholder z.1 z.2 z'.1 z'.2
    rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, ← dist_eq_norm,
      ← dist_eq_parabolicDist] at h
    have he := ENNReal.ofReal_le_ofReal h
    change edist (f z) (f z') ≤
      (Knn : ℝ≥0∞) * edist z z' ^ γ
    have hc : (Knn : ℝ≥0∞) = ENNReal.ofReal K :=
      ENNReal.ofReal_coe_nnreal.symm
    rw [hc, edist_dist, edist_dist,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hγ.le,
      ← ENNReal.ofReal_mul hK]
    exact he
  have hfUniformOn : UniformContinuousOn f univ := hfHolder.uniformContinuousOn hγ
  have hfUniform : UniformContinuous f := by
    simpa only [uniformContinuousOn_univ] using hfUniformOn
  let F : closureV → WithLp 2 Vec3 := hincDI.extend f
  have hFUniform : UniformContinuous F := by
    dsimp [F]
    exact uniformContinuous_uniformly_extend hincUE.isUniformInducing hincDense hfUniform
  have hF_eq : ∀ z : V, F (inc z) = f z := by
    intro z
    exact hincDI.extend_eq hfUniform.continuous z
  have hFbound : ∀ z : closureV, ‖F z‖ ≤ B := by
    intro z
    let Sbound : Set closureV := {x | ‖F x‖ ≤ B}
    have hSclosed : IsClosed Sbound :=
      isClosed_le (continuous_norm.comp hFUniform.continuous) continuous_const
    have hrange : Set.range inc ⊆ Sbound := by
      rintro x ⟨y, hxy⟩
      change inc y = x at hxy
      subst x
      change ‖F (inc y)‖ ≤ B
      rw [hF_eq y]
      simpa only [vec3EuclideanNorm_eq_l2] using hbound y.1 y.2
    have hclosure : closure (Set.range inc) ⊆ Sbound := closure_minimal hrange hSclosed
    have hz : z ∈ closure (Set.range inc) := by
      rw [hincDense.closure_range]
      trivial
    exact hclosure hz
  have hFholder : ∀ z z' : closureV,
      dist (F z) (F z') ≤ K * dist z z' ^ γ := by
    apply goodPoint_holder_bound_of_dense hFUniform.continuous hγ.le hincDense
    rintro q ⟨z, rfl⟩ q' ⟨z', rfl⟩
    have h := hholder z.1 z.2 z'.1 z'.2
    rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, ← dist_eq_norm,
      ← dist_eq_parabolicDist] at h
    rw [hF_eq z, hF_eq z']
    simpa only [f, Subtype.dist_eq] using h
  let w : ParabolicPoint → Vec3 := fun z =>
    if hz : z ∈ closureV then WithLp.ofLp (F ⟨z, hz⟩) else 0
  have hwbound : ∀ z ∈ closureV, vec3EuclideanNorm (w z) ≤ B := by
    intro z hz
    rw [vec3EuclideanNorm_eq_l2]
    simp only [w, dite_eq_left hz, WithLp.toLp_ofLp]
    exact hFbound ⟨z, hz⟩
  have hwholder : ∀ z ∈ closureV, ∀ z' ∈ closureV,
      vec3EuclideanNorm (w z - w z') ≤ K * parabolicDist z z' ^ γ := by
    intro z hz z' hz'
    have h := hFholder ⟨z, hz⟩ ⟨z', hz'⟩
    have hnorm : vec3EuclideanNorm (w z - w z') =
        dist (F ⟨z, hz⟩) (F ⟨z', hz'⟩) := by
      rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
      simp only [w, dite_eq_left hz, dite_eq_left hz', WithLp.toLp_ofLp]
      rw [dist_eq_norm]
    rw [hnorm]
    simpa only [Subtype.dist_eq, dist_eq_parabolicDist] using h
  have hwg : w =ᵐ[volume.restrict V] g := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    have hzC : z ∈ closureV := subset_closure hz
    simp only [w, dite_eq_left hzC]
    have heq := hF_eq ⟨z, hz⟩
    simpa [f, inc] using congrArg WithLp.ofLp heq
  exact ⟨w, hwg, hwbound, hwholder⟩

/-- Theorem A yields a Hölder representative up to the top face, as in
`lem:thmA-top`. -/
theorem epsilonRegularityL3_top :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (x₀ : Vec3) (t₀ ρ r : ℝ)
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
                goodPointTopHolderBound C₄ r γ₀ * parabolicDist z z' ^ γ₀) := by
  obtain ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄,
      hRescaled⟩ := epsilonRegularityL3_rescaled 3 (by norm_num)
  refine ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, ?_⟩
  intro x₀ t₀ ρ r u Du p hr hρ hSuitable hsmall
  let V := goodPointPastCylinder x₀ t₀ (r / 2)
  let Center := {c : ParabolicPoint // c ∈ goodPointTopCenter x₀ r}
  let patch : Center → Set ParabolicPoint :=
    fun c => goodPointTopPatch t₀ r c.1
  have hRpos : 0 < r / 2 := by positivity
  have hlocal : ∀ c : Center, ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (patch c)] u ∧
      ParabolicHolderVecOn (patch c) w γ₀ ∧
      (∀ z ∈ patch c, vec3EuclideanNorm (w z) ≤ 2 * C₄ * r⁻¹) ∧
      (∀ z ∈ patch c, ∀ z' ∈ patch c,
        vec3EuclideanNorm (w z - w z') ≤
          goodPointTopLocalHolderBound C₄ r γ₀ * parabolicDist z z' ^ γ₀) := by
    intro c
    rcases c.2 with ⟨hcx, hcs⟩
    have hshift : parabolicCylinder c.1.1 (t₀ - c.1.2) (r / 2) ⊆
        parabolicCylinder x₀ t₀ r := by
      exact goodPointTop_shift_cylinder_subset (x₀ := x₀) (x := c.1.1)
        (t₀ := t₀) (r := r) (s := c.1.2) ⟨hcx, hcs⟩
    have hclosure : closure (parabolicCylinder c.1.1 (t₀ - c.1.2) (r / 2)) ⊆
        spaceTimeSet (vec3Ball x₀ ρ) (Ioo (t₀ - ρ ^ 2) t₀) := by
      exact goodPointTop_shift_closure_subset hρ hr ⟨hcx, hcs⟩
    have hsmall' := goodPoint_shifted_small (u := u) (p := p) hr hε₀
      hshift hsmall
    obtain ⟨v, hvae, hvbound, hvsemi⟩ := hRescaled
      (vec3Ball x₀ ρ) (Ioo (t₀ - ρ ^ 2) t₀) u Du p
      hSuitable c.1.1 (t₀ - c.1.2) (r / 2) hRpos hclosure hsmall'
    have hquarter : r / 2 / 2 = r / 4 := by ring
    have hpatch : patch c ⊆ parabolicCylinder c.1.1 (t₀ - c.1.2) (r / 2 / 2) := by
      intro z hz
      have hz' : z ∈ parabolicCylinder c.1.1 (t₀ - c.1.2) (r / 4) := by
        rcases hz with ⟨hzx, hzt⟩
        rcases hzt with ⟨hzlo, hzhi⟩
        exact ⟨hzx, hzlo, le_of_lt hzhi⟩
      simpa only [hquarter] using hz'
    have hvAE : v =ᵐ[volume.restrict (patch c)] u :=
      ae_restrict_of_ae_restrict_of_subset hpatch hvae
    have hlocbound : ∀ z ∈ patch c, vec3EuclideanNorm (v z) ≤
        2 * C₄ * r⁻¹ := by
      intro z hz
      have hzclosed : z ∈ closure
          (parabolicCylinder c.1.1 (t₀ - c.1.2) (r / 2 / 2)) :=
        subset_closure (hpatch hz)
      have hscale : C₄ * (r / 2)⁻¹ = 2 * C₄ * r⁻¹ := by
        field_simp
      calc
        vec3EuclideanNorm (v z) ≤ C₄ * (r / 2)⁻¹ := hvbound z hzclosed
        _ = 2 * C₄ * r⁻¹ := hscale
    have hlocsemi : ∀ z ∈ patch c, ∀ z' ∈ patch c,
        vec3EuclideanNorm (v z - v z') ≤
          goodPointTopLocalHolderBound C₄ r γ₀ * parabolicDist z z' ^ γ₀ := by
      intro z hz z' hz'
      have hzc : z ∈ closure
          (parabolicCylinder c.1.1 (t₀ - c.1.2) (r / 2 / 2)) :=
        subset_closure (hpatch hz)
      have hz'c : z' ∈ closure
          (parabolicCylinder c.1.1 (t₀ - c.1.2) (r / 2 / 2)) :=
        subset_closure (hpatch hz')
      simpa only [hquarter, goodPointTopLocalHolderBound] using hvsemi z hzc z' hz'c
    have hlocHolder : ParabolicHolderVecOn (patch c) v γ₀ := by
      refine ⟨2 * C₄ * r⁻¹,
        goodPointTopLocalHolderBound C₄ r γ₀, ?_, ?_, hlocbound, hlocsemi⟩
      · positivity
      · unfold goodPointTopLocalHolderBound
        positivity
    exact ⟨v, hvAE, hlocHolder, hlocbound, hlocsemi⟩
  classical
  choose W hW using hlocal
  have hVopen : IsOpen V := by
    change IsOpen (spaceTimeSet (vec3Ball x₀ (r / 2)) (Ioo (t₀ - (r / 2) ^ 2) t₀))
    exact isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo
  have hpatchOpen : ∀ c : Center, IsOpen (patch c) := by
    intro c
    change IsOpen (spaceTimeSet (vec3Ball c.1.1 (r / 4))
      (Ioo (t₀ - c.1.2 - (r / 4) ^ 2) (t₀ - c.1.2)))
    exact isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo
  have hcover : V ⊆ ⋃ c : Center, patch c := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp
      (goodPointPastCylinder_subset_topPatches hr hz)
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hzc⟩
  have hVlind : IsLindelof V := HereditarilyLindelofSpace.isLindelof V
  obtain ⟨S, hS, hScov⟩ := hVlind.elim_countable_subcover patch hpatchOpen hcover
  let Index := {c : Center // c ∈ S}
  have hIndexCountable : Countable Index := hS.to_subtype
  let patches : Index → Set ParabolicPoint := fun i => patch i.1
  let reps : Index → ParabolicPoint → Vec3 := fun i => W i.1
  have hcoverS : V ⊆ ⋃ i : Index, patches i := by
    intro z hz
    rcases Set.mem_iUnion₂.mp (hScov hz) with ⟨c, hcS, hzc⟩
    exact Set.mem_iUnion.mpr ⟨⟨c, hcS⟩, hzc⟩
  have hglueOpen : ∀ i : Index, IsOpen (patches i) := by
    intro i
    exact hpatchOpen i.1
  have hglueHolder : ∀ i : Index, ParabolicHolderVecOn (patches i) (reps i) γ₀ := by
    intro i
    exact (hW i.1).2.1
  have hglueAE : ∀ i : Index,
      reps i =ᵐ[volume.restrict (patches i)] u := by
    intro i
    exact (hW i.1).1
  obtain ⟨g, hgEq, hgAE⟩ :=
    @CKN.Core.Endgame.exists_holder_gluing Index hIndexCountable patches reps u γ₀ hγ₀
      hglueOpen hglueHolder hglueAE
  have hgAEV : g =ᵐ[volume.restrict V] u :=
    ae_restrict_of_ae_restrict_of_subset hcoverS hgAE
  have hgEqAny : ∀ c : Center, ∀ z ∈ V, z ∈ patch c → g z = W c z := by
    intro c z hzV hzc
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hcoverS hzV)
    have hoverlap := CKN.Core.Endgame.holder_representatives_eqOn_overlap
      (hpatchOpen i.1) (hpatchOpen c) hγ₀ hγ₀
      (hW i.1).2.1 (hW c).2.1 (hW i.1).1 (hW c).1
    calc
      g z = W i.1 z := hgEq i hzi
      _ = W c z := hoverlap ⟨hzi, hzc⟩
  have hboundV : ∀ z ∈ V, vec3EuclideanNorm (g z) ≤ 2 * C₄ * r⁻¹ := by
    intro z hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hcoverS hz)
    rw [hgEq i hzi]
    exact (hW i.1).2.2.1 z hzi
  have hholderV : ∀ z ∈ V, ∀ z' ∈ V,
      vec3EuclideanNorm (g z - g z') ≤
        goodPointTopHolderBound C₄ r γ₀ * parabolicDist z z' ^ γ₀ := by
    intro z hz z' hz'
    by_cases hclose : parabolicDist z z' < r / 8
    · obtain ⟨c, hc, hzc, hz'c⟩ := goodPointTop_pair_patch hr hz hz' hclose
      let cc : Center := ⟨c, hc⟩
      have hlocalSemi := (hW cc).2.2.2 z hzc z' hz'c
      rw [hgEqAny cc z hz hzc, hgEqAny cc z' hz' hz'c]
      exact hlocalSemi.trans (mul_le_mul_of_nonneg_right
        (goodPointTop_localHolderBound_le hC₄ hr hγ₀)
        (Real.rpow_nonneg (by
          rw [← dist_eq_parabolicDist]
          exact dist_nonneg) _))
    · have hfar : r / 8 ≤ parabolicDist z z' := le_of_not_gt hclose
      have hd_nonneg : 0 ≤ parabolicDist z z' := by
        rw [← dist_eq_parabolicDist]
        exact dist_nonneg
      have hpow_nonneg : 0 ≤ parabolicDist z z' ^ γ₀ := Real.rpow_nonneg hd_nonneg _
      have hbase : 0 < r / 8 := by positivity
      have hpow_mono : (r / 8) ^ γ₀ ≤ parabolicDist z z' ^ γ₀ :=
        Real.rpow_le_rpow hbase.le hfar hγ₀.le
      have hpow_pos : 0 < (r / 8) ^ γ₀ := Real.rpow_pos_of_pos hbase _
      have hscale :
          goodPointTopHolderBound C₄ r γ₀ * (r / 8) ^ γ₀ = 4 * C₄ * r⁻¹ := by
        rw [goodPointTopHolderBound]
        have hinv : 8 * r⁻¹ = (r / 8)⁻¹ := by field_simp
        rw [hinv, Real.inv_rpow (by positivity)]
        field_simp
      calc
        vec3EuclideanNorm (g z - g z') ≤
            vec3EuclideanNorm (g z) + vec3EuclideanNorm (g z') :=
              vec3EuclideanNorm_sub_le _ _
        _ ≤ 4 * C₄ * r⁻¹ := by linarith only [hboundV z hz, hboundV z' hz']
        _ = goodPointTopHolderBound C₄ r γ₀ * (r / 8) ^ γ₀ := hscale.symm
        _ ≤ goodPointTopHolderBound C₄ r γ₀ * parabolicDist z z' ^ γ₀ := by
          exact mul_le_mul_of_nonneg_left hpow_mono (by
            unfold goodPointTopHolderBound
            positivity)
  have hKnonneg : 0 ≤ goodPointTopHolderBound C₄ r γ₀ := by
    unfold goodPointTopHolderBound
    positivity
  obtain ⟨w, hwg, hwbound, hwholder⟩ := goodPoint_holder_extend_closure
    hVopen hγ₀ hKnonneg hboundV hholderV
  refine ⟨w, hwg.trans hgAEV, ?_, ?_⟩
  · intro z hz
    exact hwbound z hz
  · intro z hz z' hz'
    exact hwholder z hz z' hz'

end ESS
