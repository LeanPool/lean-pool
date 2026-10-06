/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Topology.MetricSpace.Cover
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Bounded-overlap integral estimates

The finite summation estimate used for the collar terms in
`eq:bu-gaussian-collar` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN

open Metric

abbrev BUGaussianSpace := CKN.Foundation.Parabolic.L2Vec3

/-- The fixed-width spatial collar used in `eq:bu-gaussian-collar` (ESS). -/
@[expose]
def buGaussianShell (ρ : ℝ) : Set BUGaussianSpace :=
  {y | ρ - 1 < ‖y‖ ∧ ‖y‖ < ρ - 1 / 2}

private theorem le_dist_of_disjoint_half_radius {r : ℝ} {x y : BUGaussianSpace}
    (hdis : Disjoint (closedBall x (r / 2)) (closedBall y (r / 2))) :
    r ≤ dist x y := by
  by_contra hnot
  have hdist : dist x y < r := lt_of_not_ge hnot
  let m := midpoint ℝ x y
  have hm₁ : dist x m = dist x y / 2 := by
    dsimp [m]
    rw [dist_left_midpoint]
    norm_num
    ring
  have hm₂ : dist y m = dist x y / 2 := by
    dsimp [m]
    rw [dist_right_midpoint]
    norm_num
    ring
  have hball₁ : m ∈ closedBall x (r / 2) := by
    change dist m x ≤ r / 2
    rw [dist_comm, hm₁]
    linarith only [hdist]
  have hball₂ : m ∈ closedBall y (r / 2) := by
    change dist m y ≤ r / 2
    rw [dist_comm, hm₂]
    linarith only [hdist]
  exact (Set.disjoint_left.mp hdis) hball₁ hball₂

private theorem buGaussianShell_closure_bounds (ρ : ℝ) :
    IsCompact (closure (buGaussianShell ρ)) ∧
    closure (buGaussianShell ρ) ⊆ {y : BUGaussianSpace | ‖y‖ ≤ ρ - 1 / 2} := by
  let S := buGaussianShell ρ
  let K := closure S
  have hKball : K ⊆ closedBall (0 : BUGaussianSpace) ρ := by
    apply closure_minimal
    · intro x hx
      change dist x 0 ≤ ρ
      rw [dist_zero_right]
      change ‖x‖ ≤ ρ
      have hx' := hx.2
      nlinarith only [hx']
    · exact isClosed_closedBall
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : BUGaussianSpace) ρ).of_isClosed_subset
      isClosed_closure hKball
  have hKouter : K ⊆ {y : BUGaussianSpace | ‖y‖ ≤ ρ - 1 / 2} := by
    apply closure_minimal
    · intro x hx
      exact le_of_lt hx.2
    · exact isClosed_le continuous_norm continuous_const
  exact ⟨hKcompact, hKouter⟩

open Classical in
/-- A finite shell cover whose doubled balls stay inside the localization ball.
The overlap constant is Besicovitch.multiplicity squared and is independent of
`ρ` and `r`. -/
theorem exists_buGaussian_shell_cover (ρ r : ℝ)
    (hr : 0 < r) (hrle : r ≤ 1 / 16) :
    ∃ Y : Finset (Fin (Besicovitch.multiplicity BUGaussianSpace) × BUGaussianSpace),
      (∀ p ∈ Y, ‖p.2‖ ≤ ρ - 1 / 2) ∧
      (∀ y ∈ buGaussianShell ρ, ∃ p ∈ Y, dist y p.2 < r) ∧
      (∀ p ∈ Y, Metric.ball p.2 (2 * r) ⊆ Metric.ball 0 ρ) ∧
      (∀ z, (Y.filter fun p => dist z p.2 < 2 * r).card ≤
        Besicovitch.multiplicity BUGaussianSpace ^ 2) := by
  let S := buGaussianShell ρ
  let K := closure S
  obtain ⟨hKcompact, hKouter⟩ :=
    buGaussianShell_closure_bounds ρ
  obtain ⟨C, hCK, hCfinite, hCcover⟩ :=
    hKcompact.finite_cover_balls (div_pos hr (by norm_num : 0 < (2 : ℝ)))
  let CFin := hCfinite.toFinset
  let β := {y : BUGaussianSpace // y ∈ CFin}
  let p : Besicovitch.BallPackage β BUGaussianSpace :=
    { c := Subtype.val
      r := fun _ => r / 2
      rpos := fun _ => by positivity
      r_bound := r / 2
      r_le := fun _ => le_rfl }
  let M := Besicovitch.multiplicity BUGaussianSpace
  have hN :
      IsEmpty (Besicovitch.SatelliteConfig BUGaussianSpace M
        (Besicovitch.goodτ BUGaussianSpace)) := by
    simpa [M] using Besicovitch.isEmpty_satelliteConfig_multiplicity BUGaussianSpace
  obtain ⟨family, hdisj, hcover⟩ :=
    Besicovitch.exist_disjoint_covering_families
      (Besicovitch.one_lt_goodτ BUGaussianSpace) hN p
  have hcenterSep : ∀ i (b b' : β), b ∈ family i → b' ∈ family i → b ≠ b' →
      r ≤ dist (p.c b) (p.c b') := by
    intro i b b' hb hb' hne
    exact le_dist_of_disjoint_half_radius (hdisj i hb hb' hne)
  have hperColor (i : Fin M) (z : BUGaussianSpace) :
      (((Set.toFinite (family i)).toFinset.image (fun b => (i, p.c b))).filter
        fun q => dist z q.2 < 2 * r).card ≤ M := by
    let B : Finset β := (Set.toFinite (family i)).toFinset
    let Q : Finset (Fin M × BUGaussianSpace) := B.image (fun b => (i, p.c b))
    let F : Finset β := B.filter fun b => dist z (p.c b) < 2 * r
    have hfilter : Q.filter (fun q => dist z q.2 < 2 * r) =
        F.image (fun b => (i, p.c b)) := by
      ext q
      constructor
      · intro hq
        rcases Finset.mem_filter.mp hq with ⟨hq, hqdist⟩
        rcases Finset.mem_image.mp hq with ⟨b, hb, rfl⟩
        exact Finset.mem_image.mpr
          ⟨b, Finset.mem_filter.mpr ⟨hb, hqdist⟩, rfl⟩
      · intro hq
        rcases Finset.mem_image.mp hq with ⟨b, hb, rfl⟩
        rcases Finset.mem_filter.mp hb with ⟨hbB, hbDist⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨b, hbB, rfl⟩, hbDist⟩
    have himage : Function.Injective (fun b : β => (i, p.c b)) := by
      intro b b' h
      have hc : p.c b = p.c b' := congrArg Prod.snd h
      exact Subtype.val_injective hc
    rw [hfilter, Finset.card_image_of_injective _ himage]
    let G : Finset BUGaussianSpace := F.image (fun b => r⁻¹ • (p.c b - z))
    have hscale : Function.Injective (fun b : β => r⁻¹ • (p.c b - z)) := by
      intro b b' h
      have hsub : p.c b - z = p.c b' - z := by
        calc
          p.c b - z = r • (r⁻¹ • (p.c b - z)) := by simp [smul_smul, hr.ne']
          _ = r • (r⁻¹ • (p.c b' - z)) := congrArg (fun v : BUGaussianSpace => r • v) h
          _ = p.c b' - z := by simp [smul_smul, hr.ne']
      have hc : p.c b = p.c b' := sub_left_injective (b := z) hsub
      exact Subtype.val_injective hc
    have hGcard : G.card = F.card := by
      dsimp [G]
      exact Finset.card_image_of_injective _ hscale
    have hGnorm : ∀ v ∈ G, ‖v‖ ≤ 2 := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
      have hb' := (Finset.mem_filter.mp hb).2
      have hinv : 0 < r⁻¹ := inv_pos.mpr hr
      have hnorm : ‖p.c b - z‖ = dist z (p.c b) := by
        rw [dist_eq_norm, norm_sub_rev]
      have hinvnorm : ‖r⁻¹‖ = r⁻¹ := Real.norm_of_nonneg (le_of_lt hinv)
      rw [norm_smul, hinvnorm, hnorm]
      exact le_of_lt <| calc
        r⁻¹ * dist z (p.c b) < r⁻¹ * (2 * r) :=
          mul_lt_mul_of_pos_left hb' hinv
        _ = 2 := by field_simp
    have hGsep : ∀ c ∈ G, ∀ d ∈ G, c ≠ d → 1 ≤ ‖c - d‖ := by
      intro c hc d hd hne
      rcases Finset.mem_image.mp hc with ⟨b, hb, rfl⟩
      rcases Finset.mem_image.mp hd with ⟨b', hb', rfl⟩
      have hb'' := (Finset.mem_filter.mp hb).1
      have hb''' := (Finset.mem_filter.mp hb').1
      have hbb' : b ≠ b' := by
        intro heq
        apply hne
        rw [heq]
      have hdist := hcenterSep i b b'
        ((Set.Finite.mem_toFinset (Set.toFinite (family i))).mp hb'')
        ((Set.Finite.mem_toFinset (Set.toFinite (family i))).mp hb''') hbb'
      have hnorm :
          ‖(r⁻¹ • (p.c b - z)) - (r⁻¹ • (p.c b' - z))‖ =
            r⁻¹ * dist (p.c b) (p.c b') := by
        have halg : (r⁻¹ • (p.c b - z)) - (r⁻¹ • (p.c b' - z)) =
            r⁻¹ • (p.c b - p.c b') := by module
        have hinvnorm : ‖r⁻¹‖ = r⁻¹ :=
          Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hr))
        rw [halg, norm_smul, hinvnorm, ← dist_eq_norm]
      rw [hnorm]
      have hmul := mul_le_mul_of_nonneg_left hdist
        (le_of_lt (inv_pos.mpr hr))
      have hcancel : r⁻¹ * r = 1 := by field_simp
      calc
        1 = r⁻¹ * r := hcancel.symm
        _ ≤ r⁻¹ * dist (p.c b) (p.c b') := hmul
    have hbound : G.card ≤ M := Besicovitch.card_le_multiplicity hGnorm hGsep
    rw [hGcard] at hbound
    exact hbound
  let Y : Finset (Fin M × BUGaussianSpace) := Finset.univ.biUnion fun i =>
    ((Set.toFinite (family i)).toFinset.image fun b => (i, p.c b))
  have hmemY : ∀ i (b : β), b ∈ family i → (i, p.c b) ∈ Y := by
    intro i b hb
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨b, (Set.Finite.mem_toFinset (Set.toFinite (family i))).2 hb, rfl⟩
  have hYcenter : ∀ q ∈ Y, ‖q.2‖ ≤ ρ - 1 / 2 := by
    intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨i, -, hqi⟩
    rcases Finset.mem_image.mp hqi with ⟨b, hb, rfl⟩
    have hbC : (b : BUGaussianSpace) ∈ C :=
      (Set.Finite.mem_toFinset hCfinite).1 b.property
    exact hKouter (hCK hbC)
  have hShellCover : ∀ y ∈ S, ∃ q ∈ Y, dist y q.2 < r := by
    intro y hy
    have hyK : y ∈ K := subset_closure hy
    rcases Set.mem_iUnion.mp (hCcover hyK) with ⟨c, hc⟩
    rcases Set.mem_iUnion.mp hc with ⟨hcC, hcy⟩
    have hcFin : c ∈ CFin := (Set.Finite.mem_toFinset hCfinite).2 hcC
    let b : β := ⟨c, hcFin⟩
    have hbRange : p.c b ∈ Set.range p.c := ⟨b, rfl⟩
    rcases Set.mem_iUnion.mp (hcover hbRange) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨b', hb'⟩
    rcases Set.mem_iUnion.mp hb' with ⟨hb'fam, hball⟩
    have hleft : dist y c < r / 2 := by
      exact Metric.mem_ball.mp (by simpa [b, p] using hcy)
    have hright : dist c (p.c b') < r / 2 := by
      simpa [b, p] using Metric.mem_ball.mp hball
    let q : Fin M × BUGaussianSpace := (i, p.c b')
    have hqY : q ∈ Y := hmemY i b' hb'fam
    have htri : dist y (p.c b') ≤ dist y c + dist c (p.c b') :=
      dist_triangle y c (p.c b')
    refine ⟨q, hqY, ?_⟩
    dsimp [q]
    have hsum : dist y c + dist c (p.c b') < r := by
      linarith only [hleft, hright]
    exact lt_of_le_of_lt htri hsum
  have hOuterBall : ∀ q ∈ Y, Metric.ball q.2 (2 * r) ⊆ Metric.ball 0 ρ := by
    intro q hq y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hyq : dist y q.2 < 2 * r := by
      exact Metric.mem_ball.mp (by simpa [dist_comm] using hy)
    have htri : ‖y‖ ≤ dist y q.2 + ‖q.2‖ := by
      simpa [dist_zero_right] using (dist_triangle y q.2 0)
    have hrsmall : 2 * r ≤ 1 / 2 := by nlinarith only [hrle]
    have hsum : dist y q.2 + ‖q.2‖ < ρ := by
      linarith only [hyq, hYcenter q hq, hrsmall]
    exact lt_of_le_of_lt htri hsum
  have hmult : ∀ z, (Y.filter fun q => dist z q.2 < 2 * r).card ≤ M ^ 2 := by
    intro z
    let Q : Finset (Fin M × BUGaussianSpace) :=
      Y.filter fun q => dist z q.2 < 2 * r
    let Qᵢ (i : Fin M) :=
      ((Set.toFinite (family i)).toFinset.image fun b => (i, p.c b)).filter
        fun q => dist z q.2 < 2 * r
    have hsubset : Q ⊆ Finset.univ.biUnion Qᵢ := by
      intro q hq
      have hqY : q ∈ Y := (Finset.mem_filter.mp hq).1
      rcases Finset.mem_biUnion.mp hqY with ⟨i, -, hqi⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hqi, (Finset.mem_filter.mp hq).2⟩
    have hcard : Q.card ≤ (Finset.univ.biUnion Qᵢ).card :=
      Finset.card_le_card hsubset
    calc
      Q.card ≤ ∑ i ∈ Finset.univ, (Qᵢ i).card :=
        hcard.trans Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.univ, M := by
        apply Finset.sum_le_sum
        intro i hi
        exact hperColor i z
      _ = M ^ 2 := by simp [pow_two, Finset.sum_const]
  exact ⟨Y, hYcenter, hShellCover, hOuterBall, hmult⟩

/-- The closed transition annulus of the normalized Gaussian cutoff. -/
@[expose]
def buGaussianTransitionShell (ρ : ℝ) : Set BUGaussianSpace :=
  {y | 13 * ρ / 20 ≤ ‖y‖ ∧ ‖y‖ ≤ 3 * ρ / 4}

private theorem buGaussianTransitionShell_closure_bounds (ρ : ℝ) (hρ : 4 < ρ) :
    IsCompact (closure (buGaussianTransitionShell ρ)) ∧
    closure (buGaussianTransitionShell ρ) ⊆ {y : BUGaussianSpace | ‖y‖ ≤ 3 * ρ / 4} ∧
    closure (buGaussianTransitionShell ρ) ⊆ {y : BUGaussianSpace | 13 * ρ / 20 ≤ ‖y‖} := by
  let S := buGaussianTransitionShell ρ
  let K := closure S
  have hKball : K ⊆ closedBall (0 : BUGaussianSpace) ρ := by
    apply closure_minimal
    · intro x hx
      change dist x 0 ≤ ρ
      rw [dist_zero_right]
      change ‖x‖ ≤ ρ
      have hx' := hx.2
      nlinarith only [hx', hρ]
    · exact isClosed_closedBall
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : BUGaussianSpace) ρ).of_isClosed_subset
      isClosed_closure hKball
  have hKouter : K ⊆ {y : BUGaussianSpace | ‖y‖ ≤ 3 * ρ / 4} := by
    apply closure_minimal
    · intro x hx
      exact hx.2
    · exact isClosed_le continuous_norm continuous_const
  have hKinner : K ⊆ {y : BUGaussianSpace | 13 * ρ / 20 ≤ ‖y‖} := by
    apply closure_minimal
    · intro x hx
      exact hx.1
    · exact isClosed_le continuous_const continuous_norm
  exact ⟨hKcompact, hKouter, hKinner⟩

open Classical in
/-- A finite cover of the closed transition annulus for the Gaussian cutoff.
The overlap constant is Besicovitch.multiplicity squared. -/
theorem exists_buGaussian_transition_cover (ρ r : ℝ) (hρ : 4 < ρ)
    (hr : 0 < r) (hrle : r ≤ 1 / 16) :
    ∃ Y : Finset (Fin (Besicovitch.multiplicity BUGaussianSpace) × BUGaussianSpace),
      (∀ p ∈ Y, ‖p.2‖ ≤ ρ - 1 / 2) ∧
      (∀ p ∈ Y, 13 * ρ / 20 ≤ ‖p.2‖) ∧
      (∀ y ∈ buGaussianTransitionShell ρ, ∃ p ∈ Y, dist y p.2 < r) ∧
      (∀ p ∈ Y, Metric.ball p.2 (2 * r) ⊆ Metric.ball 0 ρ) ∧
      (∀ z, (Y.filter fun p => dist z p.2 < 2 * r).card ≤
        Besicovitch.multiplicity BUGaussianSpace ^ 2) := by
  let S := buGaussianTransitionShell ρ
  let K := closure S
  obtain ⟨hKcompact, hKouter, hKinner⟩ :=
    buGaussianTransitionShell_closure_bounds ρ hρ
  obtain ⟨C, hCK, hCfinite, hCcover⟩ :=
    hKcompact.finite_cover_balls (div_pos hr (by norm_num : 0 < (2 : ℝ)))
  let CFin := hCfinite.toFinset
  let β := {y : BUGaussianSpace // y ∈ CFin}
  let p : Besicovitch.BallPackage β BUGaussianSpace :=
    { c := Subtype.val
      r := fun _ => r / 2
      rpos := fun _ => by positivity
      r_bound := r / 2
      r_le := fun _ => le_rfl }
  let M := Besicovitch.multiplicity BUGaussianSpace
  have hN :
      IsEmpty (Besicovitch.SatelliteConfig BUGaussianSpace M
        (Besicovitch.goodτ BUGaussianSpace)) := by
    simpa [M] using Besicovitch.isEmpty_satelliteConfig_multiplicity BUGaussianSpace
  obtain ⟨family, hdisj, hcover⟩ :=
    Besicovitch.exist_disjoint_covering_families
      (Besicovitch.one_lt_goodτ BUGaussianSpace) hN p
  have hcenterSep : ∀ i (b b' : β), b ∈ family i → b' ∈ family i → b ≠ b' →
      r ≤ dist (p.c b) (p.c b') := by
    intro i b b' hb hb' hne
    exact le_dist_of_disjoint_half_radius (hdisj i hb hb' hne)
  have hperColor (i : Fin M) (z : BUGaussianSpace) :
      (((Set.toFinite (family i)).toFinset.image (fun b => (i, p.c b))).filter
        fun q => dist z q.2 < 2 * r).card ≤ M := by
    let B : Finset β := (Set.toFinite (family i)).toFinset
    let Q : Finset (Fin M × BUGaussianSpace) := B.image (fun b => (i, p.c b))
    let F : Finset β := B.filter fun b => dist z (p.c b) < 2 * r
    have hfilter : Q.filter (fun q => dist z q.2 < 2 * r) =
        F.image (fun b => (i, p.c b)) := by
      ext q
      constructor
      · intro hq
        rcases Finset.mem_filter.mp hq with ⟨hq, hqdist⟩
        rcases Finset.mem_image.mp hq with ⟨b, hb, rfl⟩
        exact Finset.mem_image.mpr
          ⟨b, Finset.mem_filter.mpr ⟨hb, hqdist⟩, rfl⟩
      · intro hq
        rcases Finset.mem_image.mp hq with ⟨b, hb, rfl⟩
        rcases Finset.mem_filter.mp hb with ⟨hbB, hbDist⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨b, hbB, rfl⟩, hbDist⟩
    have himage : Function.Injective (fun b : β => (i, p.c b)) := by
      intro b b' h
      have hc : p.c b = p.c b' := congrArg Prod.snd h
      exact Subtype.val_injective hc
    rw [hfilter, Finset.card_image_of_injective _ himage]
    let G : Finset BUGaussianSpace := F.image (fun b => r⁻¹ • (p.c b - z))
    have hscale : Function.Injective (fun b : β => r⁻¹ • (p.c b - z)) := by
      intro b b' h
      have hsub : p.c b - z = p.c b' - z := by
        calc
          p.c b - z = r • (r⁻¹ • (p.c b - z)) := by simp [smul_smul, hr.ne']
          _ = r • (r⁻¹ • (p.c b' - z)) := congrArg (fun v : BUGaussianSpace => r • v) h
          _ = p.c b' - z := by simp [smul_smul, hr.ne']
      have hc : p.c b = p.c b' := sub_left_injective (b := z) hsub
      exact Subtype.val_injective hc
    have hGcard : G.card = F.card := by
      dsimp [G]
      exact Finset.card_image_of_injective _ hscale
    have hGnorm : ∀ v ∈ G, ‖v‖ ≤ 2 := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
      have hb' := (Finset.mem_filter.mp hb).2
      have hinv : 0 < r⁻¹ := inv_pos.mpr hr
      have hnorm : ‖p.c b - z‖ = dist z (p.c b) := by
        rw [dist_eq_norm, norm_sub_rev]
      have hinvnorm : ‖r⁻¹‖ = r⁻¹ := Real.norm_of_nonneg (le_of_lt hinv)
      rw [norm_smul, hinvnorm, hnorm]
      exact le_of_lt <| calc
        r⁻¹ * dist z (p.c b) < r⁻¹ * (2 * r) :=
          mul_lt_mul_of_pos_left hb' hinv
        _ = 2 := by field_simp
    have hGsep : ∀ c ∈ G, ∀ d ∈ G, c ≠ d → 1 ≤ ‖c - d‖ := by
      intro c hc d hd hne
      rcases Finset.mem_image.mp hc with ⟨b, hb, rfl⟩
      rcases Finset.mem_image.mp hd with ⟨b', hb', rfl⟩
      have hb'' := (Finset.mem_filter.mp hb).1
      have hb''' := (Finset.mem_filter.mp hb').1
      have hbb' : b ≠ b' := by
        intro heq
        apply hne
        rw [heq]
      have hdist := hcenterSep i b b'
        ((Set.Finite.mem_toFinset (Set.toFinite (family i))).mp hb'')
        ((Set.Finite.mem_toFinset (Set.toFinite (family i))).mp hb''') hbb'
      have hnorm :
          ‖(r⁻¹ • (p.c b - z)) - (r⁻¹ • (p.c b' - z))‖ =
            r⁻¹ * dist (p.c b) (p.c b') := by
        have halg : (r⁻¹ • (p.c b - z)) - (r⁻¹ • (p.c b' - z)) =
            r⁻¹ • (p.c b - p.c b') := by module
        have hinvnorm : ‖r⁻¹‖ = r⁻¹ :=
          Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hr))
        rw [halg, norm_smul, hinvnorm, ← dist_eq_norm]
      rw [hnorm]
      have hmul := mul_le_mul_of_nonneg_left hdist
        (le_of_lt (inv_pos.mpr hr))
      have hcancel : r⁻¹ * r = 1 := by field_simp
      calc
        1 = r⁻¹ * r := hcancel.symm
        _ ≤ r⁻¹ * dist (p.c b) (p.c b') := hmul
    have hbound : G.card ≤ M := Besicovitch.card_le_multiplicity hGnorm hGsep
    rw [hGcard] at hbound
    exact hbound
  let Y : Finset (Fin M × BUGaussianSpace) := Finset.univ.biUnion fun i =>
    ((Set.toFinite (family i)).toFinset.image fun b => (i, p.c b))
  have hmemY : ∀ i (b : β), b ∈ family i → (i, p.c b) ∈ Y := by
    intro i b hb
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨b, (Set.Finite.mem_toFinset (Set.toFinite (family i))).2 hb, rfl⟩
  have hYcenter : ∀ q ∈ Y, ‖q.2‖ ≤ ρ - 1 / 2 := by
    intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨i, -, hqi⟩
    rcases Finset.mem_image.mp hqi with ⟨b, hb, rfl⟩
    have hbC : (b : BUGaussianSpace) ∈ C :=
      (Set.Finite.mem_toFinset hCfinite).1 b.property
    have hbound := hKouter (hCK hbC)
    have hnorm : ‖(i, p.c b).2‖ ≤ 3 * ρ / 4 := by simpa using hbound
    have hroom : 3 * ρ / 4 ≤ ρ - 1 / 2 := by nlinarith only [hρ]
    exact hnorm.trans hroom
  have hYinner : ∀ q ∈ Y, 13 * ρ / 20 ≤ ‖q.2‖ := by
    intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨i, -, hqi⟩
    rcases Finset.mem_image.mp hqi with ⟨b, hb, rfl⟩
    have hbC : (b : BUGaussianSpace) ∈ C :=
      (Set.Finite.mem_toFinset hCfinite).1 b.property
    have hbound := hKinner (hCK hbC)
    simpa using hbound
  have hShellCover : ∀ y ∈ S, ∃ q ∈ Y, dist y q.2 < r := by
    intro y hy
    have hyK : y ∈ K := subset_closure hy
    rcases Set.mem_iUnion.mp (hCcover hyK) with ⟨c, hc⟩
    rcases Set.mem_iUnion.mp hc with ⟨hcC, hcy⟩
    have hcFin : c ∈ CFin := (Set.Finite.mem_toFinset hCfinite).2 hcC
    let b : β := ⟨c, hcFin⟩
    have hbRange : p.c b ∈ Set.range p.c := ⟨b, rfl⟩
    rcases Set.mem_iUnion.mp (hcover hbRange) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨b', hb'⟩
    rcases Set.mem_iUnion.mp hb' with ⟨hb'fam, hball⟩
    have hleft : dist y c < r / 2 := by
      exact Metric.mem_ball.mp (by simpa [b, p] using hcy)
    have hright : dist c (p.c b') < r / 2 := by
      simpa [b, p] using Metric.mem_ball.mp hball
    let q : Fin M × BUGaussianSpace := (i, p.c b')
    have hqY : q ∈ Y := hmemY i b' hb'fam
    have htri : dist y (p.c b') ≤ dist y c + dist c (p.c b') :=
      dist_triangle y c (p.c b')
    refine ⟨q, hqY, ?_⟩
    dsimp [q]
    have hsum : dist y c + dist c (p.c b') < r := by
      linarith only [hleft, hright]
    exact lt_of_le_of_lt htri hsum
  have hOuterBall : ∀ q ∈ Y, Metric.ball q.2 (2 * r) ⊆ Metric.ball 0 ρ := by
    intro q hq y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hyq : dist y q.2 < 2 * r := by
      exact Metric.mem_ball.mp (by simpa [dist_comm] using hy)
    have htri : ‖y‖ ≤ dist y q.2 + ‖q.2‖ := by
      simpa [dist_zero_right] using (dist_triangle y q.2 0)
    have hrsmall : 2 * r ≤ 1 / 8 := by nlinarith only [hrle]
    have hroom : 3 * ρ / 4 + 1 / 8 < ρ := by nlinarith only [hρ]
    have hsum : dist y q.2 + ‖q.2‖ < ρ := by
      linarith only [hyq, hYcenter q hq, hrsmall, hroom]
    exact lt_of_le_of_lt htri hsum
  have hmult : ∀ z, (Y.filter fun q => dist z q.2 < 2 * r).card ≤ M ^ 2 := by
    intro z
    let Q : Finset (Fin M × BUGaussianSpace) :=
      Y.filter fun q => dist z q.2 < 2 * r
    let Qᵢ (i : Fin M) :=
      ((Set.toFinite (family i)).toFinset.image fun b => (i, p.c b)).filter
        fun q => dist z q.2 < 2 * r
    have hsubset : Q ⊆ Finset.univ.biUnion Qᵢ := by
      intro q hq
      have hqY : q ∈ Y := (Finset.mem_filter.mp hq).1
      rcases Finset.mem_biUnion.mp hqY with ⟨i, -, hqi⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hqi, (Finset.mem_filter.mp hq).2⟩
    have hcard : Q.card ≤ (Finset.univ.biUnion Qᵢ).card :=
      Finset.card_le_card hsubset
    calc
      Q.card ≤ ∑ i ∈ Finset.univ, (Qᵢ i).card :=
        hcard.trans Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.univ, M := by
        apply Finset.sum_le_sum
        intro i hi
        exact hperColor i z
      _ = M ^ 2 := by simp [pow_two, Finset.sum_const]
  exact ⟨Y, hYcenter, hYinner, hShellCover, hOuterBall, hmult⟩

open Classical in
/-- Spatial and temporal overlap bounds multiply for a finite grid of
product cells. -/
theorem lintegral_sum_le_of_product_multiplicity_bound
    {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) (I : Finset ι) (J : Finset κ)
    (U : ι → Set α) (V : κ → Set β) (N K : ℕ)
    (f : α × β → ℝ≥0∞) (hf : AEMeasurable f μ)
    (hU : ∀ i ∈ I, MeasurableSet (U i))
    (hV : ∀ j ∈ J, MeasurableSet (V j))
    (hspace : ∀ x, (∑ i ∈ I, if x ∈ U i then 1 else 0) ≤ N)
    (htime : ∀ t, (∑ j ∈ J, if t ∈ V j then 1 else 0) ≤ K) :
    (∑ p ∈ I.product J,
      ∫⁻ z in U p.1 ×ˢ V p.2, f z ∂μ) ≤
      ((K * N : ℕ) : ℝ≥0∞) * ∫⁻ z, f z ∂μ := by
  classical
  let W : ι × κ → Set (α × β) :=
    fun p => {z | z.1 ∈ U p.1 ∧ z.2 ∈ V p.2}
  have hW (p : ι × κ) (hp : p ∈ I.product J) : MeasurableSet (W p) := by
    rcases Finset.mem_product.mp hp with ⟨hi, hj⟩
    change MeasurableSet (U p.1 ×ˢ V p.2)
    exact (hU p.1 hi).prod (hV p.2 hj)
  have hmulRaw : ∀ z,
      (∑ p ∈ I.product J, if z ∈ W p then 1 else 0) ≤ K * N := by
    intro z
    have hcount :
        (∑ p ∈ I.product J, if z ∈ W p then 1 else 0) =
          (∑ i ∈ I, if z.1 ∈ U i then 1 else 0) *
            (∑ j ∈ J, if z.2 ∈ V j then 1 else 0) := by
      calc
        _ = ∑ p ∈ I.product J,
            (if z.1 ∈ U p.1 then 1 else 0) *
              (if z.2 ∈ V p.2 then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro p hp
                rcases Finset.mem_product.mp hp with ⟨_, _⟩
                by_cases hx : z.1 ∈ U p.1 <;>
                  by_cases ht : z.2 ∈ V p.2 <;>
                  simp [W, hx, ht]
        _ = ∑ i ∈ I, ∑ j ∈ J,
            (if z.1 ∈ U i then 1 else 0) *
              (if z.2 ∈ V j then 1 else 0) :=
                Finset.sum_product I J _
        _ = _ := (Finset.sum_mul_sum I J _ _).symm
    rw [hcount]
    calc
      _ ≤ N * K := Nat.mul_le_mul (hspace z.1) (htime z.2)
      _ = K * N := Nat.mul_comm _ _
  let P := I.product J
  let g : ι × κ → α × β → ℝ≥0∞ := fun p z => (W p).indicator f z
  have hg (p : ι × κ) (hp : p ∈ P) : AEMeasurable (g p) μ := by
    change AEMeasurable ((W p).indicator f) μ
    exact (aemeasurable_indicator_iff (hW p hp)).2 hf.restrict
  have hset (p : ι × κ) (hp : p ∈ P) :
      ∫⁻ z in W p, f z ∂μ = ∫⁻ z, g p z ∂μ := by
    rw [← lintegral_indicator (hW p hp)]
  calc
    (∑ p ∈ P, ∫⁻ z in W p, f z ∂μ) =
        ∑ p ∈ P, ∫⁻ z, g p z ∂μ := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hset p hp
    _ = ∫⁻ z, ∑ p ∈ P, g p z ∂μ :=
          (lintegral_finsetSum' P hg).symm
    _ ≤ ∫⁻ z, ((K * N : ℕ) : ℝ≥0∞) * f z ∂μ := by
          apply lintegral_mono
          intro z
          change (∑ p ∈ P, g p z) ≤ ((K * N : ℕ) : ℝ≥0∞) * f z
          have hsum :
              (∑ p ∈ P, g p z) =
                ((∑ p ∈ P, if z ∈ W p then 1 else 0 : ℕ) : ℝ≥0∞) * f z := by
            calc
              (∑ p ∈ P, g p z) =
                  ∑ p ∈ P, (if z ∈ W p then (1 : ℝ≥0∞) else 0) * f z := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    by_cases hz : z ∈ W p <;> simp [g, hz]
              _ = (∑ p ∈ P, if z ∈ W p then (1 : ℝ≥0∞) else 0) * f z := by
                    rw [Finset.sum_mul]
              _ = ((∑ p ∈ P, if z ∈ W p then (1 : ℕ) else 0 : ℕ) : ℝ≥0∞) * f z := by
                    congr 1
                    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
          rw [hsum]
          gcongr
          exact_mod_cast hmulRaw z
    _ = ((K * N : ℕ) : ℝ≥0∞) * ∫⁻ z, f z ∂μ :=
          lintegral_const_mul'' _ hf

open Classical in
/-- A real-valued nonnegative integrand obeys the same finite product
overlap estimate, in the Bochner-integral form used by `lem:caccioppoli`. -/
theorem integral_sum_le_of_product_multiplicity_bound
    {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) (I : Finset ι) (J : Finset κ)
    (U : ι → Set α) (V : κ → Set β) (N K : ℕ)
    (f : α × β → ℝ) (hf : Integrable f μ)
    (hfn : ∀ᵐ z ∂μ, 0 ≤ f z)
    (hU : ∀ i ∈ I, MeasurableSet (U i))
    (hV : ∀ j ∈ J, MeasurableSet (V j))
    (hspace : ∀ x, (∑ i ∈ I, if x ∈ U i then 1 else 0) ≤ N)
    (htime : ∀ t, (∑ j ∈ J, if t ∈ V j then 1 else 0) ≤ K) :
    (∑ p ∈ I.product J,
      ∫ z in U p.1 ×ˢ V p.2, f z ∂μ) ≤
      ((K * N : ℕ) : ℝ) * ∫ z, f z ∂μ := by
  classical
  let P := I.product J
  let W : ι × κ → Set (α × β) :=
    fun p => U p.1 ×ˢ V p.2
  have hW (p : ι × κ) (hp : p ∈ P) : MeasurableSet (W p) := by
    rcases Finset.mem_product.mp hp with ⟨hi, hj⟩
    change MeasurableSet (U p.1 ×ˢ V p.2)
    exact (hU p.1 hi).prod (hV p.2 hj)
  have hWInt (p : ι × κ) (hp : p ∈ P) : Integrable f (μ.restrict (W p)) :=
    hf.restrict
  have hWnonneg (p : ι × κ) (hp : p ∈ P) :
      ∀ᵐ z ∂(μ.restrict (W p)), 0 ≤ f z :=
    ae_restrict_of_ae hfn
  let fₑ : α × β → ℝ≥0∞ := fun z => ENNReal.ofReal (f z)
  have hfₑ : AEMeasurable fₑ μ := by
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      hf.aestronglyMeasurable.aemeasurable
  have hlin := lintegral_sum_le_of_product_multiplicity_bound
    μ I J U V N K fₑ hfₑ hU hV hspace htime
  have hleft : ENNReal.ofReal
      (∑ p ∈ P, ∫ z in W p, f z ∂μ) =
      ∑ p ∈ P, ∫⁻ z in W p, fₑ z ∂μ := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro p hp
      exact ofReal_integral_eq_lintegral_ofReal (hWInt p hp) (hWnonneg p hp)
    · intro p hp
      exact integral_nonneg_of_ae (hWnonneg p hp)
  have hglobal : ∫⁻ z, fₑ z ∂μ = ENNReal.ofReal (∫ z, f z ∂μ) := by
    exact (ofReal_integral_eq_lintegral_ofReal hf hfn).symm
  have htotalnonneg : 0 ≤ ∫ z, f z ∂μ := integral_nonneg_of_ae hfn
  have hright : ((K * N : ℕ) : ℝ≥0∞) * ∫⁻ z, fₑ z ∂μ =
      ENNReal.ofReal (((K * N : ℕ) : ℝ) * ∫ z, f z ∂μ) := by
    rw [hglobal]
    calc
      ((K * N : ℕ) : ℝ≥0∞) * ENNReal.ofReal (∫ z, f z ∂μ) =
          ENNReal.ofReal ((K * N : ℕ) : ℝ) *
            ENNReal.ofReal (∫ z, f z ∂μ) := by rw [ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (((K * N : ℕ) : ℝ) * ∫ z, f z ∂μ) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ((K * N : ℕ) : ℝ))]
  have hlin' : (∑ p ∈ P, ∫⁻ z in W p, fₑ z ∂μ) ≤
      ((K * N : ℕ) : ℝ≥0∞) * ∫⁻ z, fₑ z ∂μ := by
    simpa [P, W, Nat.cast_mul] using hlin
  have hEN : ENNReal.ofReal
      (∑ p ∈ P, ∫ z in W p, f z ∂μ) ≤
      ENNReal.ofReal (((K * N : ℕ) : ℝ) * ∫ z, f z ∂μ) := by
    calc
      _ = ∑ p ∈ P, ∫⁻ z in W p, fₑ z ∂μ := hleft
      _ ≤ ((K * N : ℕ) : ℝ≥0∞) * ∫⁻ z, fₑ z ∂μ := hlin'
      _ = _ := hright
  have hresultNonneg : 0 ≤ ((K * N : ℕ) : ℝ) * ∫ z, f z ∂μ :=
    mul_nonneg (Nat.cast_nonneg _) htotalnonneg
  exact (ENNReal.ofReal_le_ofReal_iff hresultNonneg).mp hEN

end CKN

end
