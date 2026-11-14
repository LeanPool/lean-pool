/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.GeodesicFlow
public import LeanPool.PlanarMidpoint.GreenContinuous
public import LeanPool.PlanarMidpoint.GeodesicDefinitions
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Canonical short geodesics by a Dirichlet contraction

A bounded Dirichlet Green operator and a sufficiently small local Lipschitz
constant produce a unique phase path in a closed ball about the constant
zero-velocity path. This supplies the local endpoint problem.
-/

@[expose] public section

open Set Metric
open scoped NNReal

namespace PlanarMidpoint

noncomputable section

section PathContraction

variable {T V W : Type*} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Continuous paths restricted to one complete closed sup-norm ball. -/
def BallPath (p : V) (r : ℝ) := closedBall (ContinuousMap.const T p) r

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem path_mem_ball {p : V} {r : ℝ} (y : BallPath (T := T) p r) (t : T) :
    y.1 t ∈ closedBall p r := by
  exact (ContinuousMap.dist_apply_le_dist t).trans y.2

/-- Composition is continuous because the path stays in the region where
its vector field is Lipschitz. -/
def composeBallPath {p : V} {r : ℝ} {F : V → W} {L : ℝ≥0}
    (hF : LipschitzOnWith L F (closedBall p r)) (y : BallPath (T := T) p r) : C(T, W) :=
  ⟨F ∘ y.1, hF.continuousOn.comp_continuous y.1.continuous (path_mem_ball y)⟩

omit [NormedSpace ℝ W] [NormedSpace ℝ V] [CompleteSpace V] in
private theorem composeBallPath_dist {p : V} {r : ℝ} {F : V → W} {L : ℝ≥0}
    (hF : LipschitzOnWith L F (closedBall p r)) (y z : BallPath (T := T) p r) :
    dist (composeBallPath hF y) (composeBallPath hF z) ≤ L * dist y z := by
  apply (ContinuousMap.dist_le (mul_nonneg L.coe_nonneg (dist_nonneg))).mpr
  intro t
  exact (hF.dist_le_mul (y.1 t) (path_mem_ball y t) (z.1 t) (path_mem_ball z t)).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist t) L.coe_nonneg)

omit [NormedSpace ℝ W] [NormedSpace ℝ V] [CompleteSpace V] in
private theorem composeBallPath_norm {p : V} {r : ℝ} (hr : 0 ≤ r)
    {F : V → W} {L : ℝ≥0} (hF : LipschitzOnWith L F (closedBall p r)) (hFp : F p = 0)
    (y : BallPath (T := T) p r) : ‖composeBallPath hF y‖ ≤ L * r := by
  apply (ContinuousMap.norm_le _ (mul_nonneg L.coe_nonneg hr)).mpr
  intro t
  have h := hF.dist_le_mul (y.1 t) (path_mem_ball y t) p (mem_closedBall_self hr)
  have h' : ‖F (y.1 t)‖ ≤ L * dist (y.1 t) p := by simpa [hFp] using h
  exact h'.trans (mul_le_mul_of_nonneg_left (path_mem_ball y t) L.coe_nonneg)

/-- Banach's theorem for the nonlinear Dirichlet equation in phase-path space. -/
theorem exists_unique_green_path
    (G : C(T, W) →L[ℝ] C(T, V)) (p : V) (r : ℝ) (hr : 0 ≤ r)
    (F : V → W) (L : ℝ≥0) (hF : LipschitzOnWith L F (closedBall p r))
    (hFp : F p = 0) (hsmall : ‖G‖ * (L : ℝ) ≤ 1 / 2)
    (a : C(T, V)) (ha : dist a (ContinuousMap.const T p) ≤ r / 2) :
    ∃! y : BallPath (T := T) p r, y.1 = a + G (composeBallPath hF y) := by
  have hmaps (y : BallPath (T := T) p r) :
      a + G (composeBallPath hF y) ∈ closedBall (ContinuousMap.const T p) r := by
    have hb := G.le_opNorm (composeBallPath hF y)
    have hc := composeBallPath_norm hr hF hFp y
    have hbound : ‖G (composeBallPath hF y)‖ ≤ r / 2 := by
      calc
        ‖G (composeBallPath hF y)‖ ≤ ‖G‖ * ‖composeBallPath hF y‖ := hb
        _ ≤ ‖G‖ * (L * r) := mul_le_mul_of_nonneg_left hc (norm_nonneg G)
        _ ≤ r / 2 := by nlinarith [mul_le_mul_of_nonneg_right hsmall hr]
    calc
      dist (a + G (composeBallPath hF y)) (ContinuousMap.const T p)
          ≤ dist (a + G (composeBallPath hF y)) a + dist a (ContinuousMap.const T p) :=
        dist_triangle _ _ _
      _ = ‖G (composeBallPath hF y)‖ + dist a (ContinuousMap.const T p) := by simp
      _ ≤ r := by linarith
  let f : BallPath (T := T) p r → BallPath (T := T) p r := fun y =>
    ⟨a + G (composeBallPath hF y), hmaps y⟩
  have hf : ContractingWith (1 / 2 : ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro y z
    change dist (a + G (composeBallPath hF y)) (a + G (composeBallPath hF z)) ≤
      ((1 / 2 : ℝ≥0) : ℝ) * dist y z
    rw [dist_add_left]
    calc
      dist (G (composeBallPath hF y)) (G (composeBallPath hF z))
          ≤ ‖G‖ * dist (composeBallPath hF y) (composeBallPath hF z) :=
              G.lipschitzWith.dist_le_mul _ _
      _ ≤ ‖G‖ * (L * dist y z) :=
        mul_le_mul_of_nonneg_left (composeBallPath_dist hF y z) (norm_nonneg G)
      _ ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist y z := by
        norm_num
        nlinarith [mul_le_mul_of_nonneg_right hsmall (dist_nonneg (x := y) (y := z))]
  let : Nonempty (BallPath (T := T) p r) := ⟨⟨ContinuousMap.const T p, mem_closedBall_self hr⟩⟩
  let : CompleteSpace (BallPath (T := T) p r) := isClosed_closedBall.completeSpace_coe
  refine ⟨hf.fixedPoint f, ?_, ?_⟩
  · exact (congrArg Subtype.val hf.fixedPoint_isFixedPt).symm
  · intro y hy
    apply hf.fixedPoint_unique
    apply Subtype.ext
    exact hy.symm

end PathContraction

/-- The position and velocity of the affine chord joining two endpoints. -/
def affinePhase (P Q : E) : PhasePath :=
  ⟨fun t => (P + (t : ℝ) • (Q - P), Q - P), by fun_prop⟩

theorem affinePhase_near (p P Q : E) {r : ℝ} (hr : 0 ≤ r)
    (hP : dist P p ≤ r / 8) (hQ : dist Q p ≤ r / 8) :
    dist (affinePhase P Q) (ContinuousMap.const UnitInterval (p, (0 : E))) ≤ r / 2 := by
  have hd : ‖Q - P‖ ≤ r / 4 := by
    calc
      ‖Q - P‖ = dist Q P := (dist_eq_norm Q P).symm
      _ ≤ dist Q p + dist p P := dist_triangle _ _ _
      _ ≤ r / 4 := by rw [dist_comm p P]; linarith
  apply (ContinuousMap.dist_le (by positivity : 0 ≤ r / 2)).mpr
  intro t
  change max (dist (P + (t : ℝ) • (Q - P)) p) (dist (Q - P) 0) ≤ r / 2
  apply max_le
  · calc
      dist (P + (t : ℝ) • (Q - P)) p
          ≤ dist (P + (t : ℝ) • (Q - P)) P + dist P p := dist_triangle _ _ _
      _ = (t : ℝ) * ‖Q - P‖ + dist P p := by
        simp [norm_smul, abs_of_nonneg t.property.1]
      _ ≤ r / 2 := by
        have ht := mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg (Q - P))
        nlinarith
  · simpa using hd.trans (by linarith : r / 4 ≤ r / 2)

/-- The affine endpoint chord plus the zero-endpoint Green correction. -/
def bvpPosition (P Q : E) (a : AccelerationPath) (t : ℝ) : E :=
  P + t • (Q - P) + greenPosition a t

/-- The endpoint secant plus the velocity of the Green correction. -/
def bvpVelocity (P Q : E) (a : AccelerationPath) (t : ℝ) : E :=
  Q - P + greenVelocity a t

@[simp] theorem bvpPosition_zero (P Q : E) (a : AccelerationPath) :
    bvpPosition P Q a 0 = P := by simp [bvpPosition]

@[simp] theorem bvpPosition_one (P Q : E) (a : AccelerationPath) :
    bvpPosition P Q a 1 = Q := by simp [bvpPosition]

theorem hasDerivAt_bvpPosition (P Q : E) (a : AccelerationPath) (t : ℝ) :
    HasDerivAt (bvpPosition P Q a) (bvpVelocity P Q a t) t := by
  unfold bvpPosition bvpVelocity
  simpa only [id_eq, zero_add, one_smul] using
    ((hasDerivAt_const t P).fun_add ((hasDerivAt_id t).smul_const (Q - P))).fun_add
      (hasDerivAt_greenPosition a t)

theorem hasDerivAt_bvpVelocity (P Q : E) (a : AccelerationPath) (t : ℝ) :
    HasDerivAt (bvpVelocity P Q a) (pathExtend a t) t := by
  unfold bvpVelocity
  simpa only [zero_add] using
    (hasDerivAt_const t (Q - P)).fun_add (hasDerivAt_greenVelocity a t)

/-- A fixed phase path produces an actual geodesic with the prescribed endpoints. -/
theorem fixed_green_isGeodesic (C : E → Coeff) (σ : ℝ) (p P Q : E) (r : ℝ)
    {L : ℝ≥0}
    (hF : LipschitzOnWith L (fun z : Phase => -σ • K (C z.1) z.2 z.2)
      (closedBall (p, (0 : E)) r))
    (y : BallPath (T := UnitInterval) (p, (0 : E)) r)
    (hy : y.1 = affinePhase P Q + greenOperator (composeBallPath hF y)) :
    IsGeodesicSegment C σ (bvpPosition P Q (composeBallPath hF y))
      (bvpVelocity P Q (composeBallPath hF y)) ∧
    ∀ t (ht : t ∈ UnitInterval),
      (bvpPosition P Q (composeBallPath hF y) t,
        bvpVelocity P Q (composeBallPath hF y) t) = y.1 ⟨t, ht⟩ := by
  have hpath (t : ℝ) (ht : t ∈ UnitInterval) :
      (bvpPosition P Q (composeBallPath hF y) t,
        bvpVelocity P Q (composeBallPath hF y) t) = y.1 ⟨t, ht⟩ := by
    simpa [affinePhase, bvpPosition, bvpVelocity, greenOperator_apply] using
      (congrArg (fun z : PhasePath => z ⟨t, ht⟩) hy).symm
  refine ⟨⟨fun t _ => hasDerivAt_bvpPosition P Q _ t, ?_⟩, hpath⟩
  intro t ht
  have hacc : pathExtend (composeBallPath hF y) t =
      -σ • K (C (bvpPosition P Q (composeBallPath hF y) t))
        (bvpVelocity P Q (composeBallPath hF y) t)
        (bvpVelocity P Q (composeBallPath hF y) t) := by
    rw [pathExtend_mem _ t ht]
    change - σ • K (C (y.1 ⟨t, ht⟩).1) (y.1 ⟨t, ht⟩).2 (y.1 ⟨t, ht⟩).2 = _
    rw [← hpath t ht]
  simpa only [hacc] using hasDerivAt_bvpVelocity P Q (composeBallPath hF y) t

/-- The phase path of an actual geodesic, restricted to the parameter interval. -/
def segmentPhasePath {C : E → Coeff} {σ : ℝ} {γ v : ℝ → E}
    (hg : IsGeodesicSegment C σ γ v) : PhasePath :=
  ⟨fun t => (γ t, v t),
    (continuousOn_iff_continuous_domRestrict.mp
      (show ContinuousOn γ UnitInterval from fun t ht => (hg.1 t
          ht).continuousAt.continuousWithinAt)).prodMk
    (continuousOn_iff_continuous_domRestrict.mp
      (show ContinuousOn v UnitInterval from fun t ht => (hg.2 t
          ht).continuousAt.continuousWithinAt))⟩

theorem short_path_mem {C : E → Coeff} {σ : ℝ} {p P Q : E} {r : ℝ}
    (hr : 0 ≤ r) {γ v : ℝ → E} (h : IsShortGeodesic C σ p r P Q γ v) :
    segmentPhasePath h.1 ∈ closedBall (ContinuousMap.const UnitInterval (p, (0 : E))) r := by
  apply (ContinuousMap.dist_le hr).mpr
  intro t
  change max (dist (γ t) p) (dist (v t) 0) ≤ r
  apply max_le
  · simpa only [dist_eq_norm] using (h.2.2.2 t t.property).1.le
  · simpa using (h.2.2.2 t t.property).2.le

/-- Every actual short geodesic satisfies the same Green fixed-point equation. -/
theorem actual_geodesic_is_fixed {C : E → Coeff} {σ : ℝ} {p P Q : E} {r : ℝ}
    (hr : 0 ≤ r) {L : ℝ≥0}
    (hF : LipschitzOnWith L (fun z : Phase => -σ • K (C z.1) z.2 z.2)
      (closedBall (p, (0 : E)) r))
    {γ v : ℝ → E} (h : IsShortGeodesic C σ p r P Q γ v) :
    let y : BallPath (T := UnitInterval) (p, (0 : E)) r :=
      ⟨segmentPhasePath h.1, short_path_mem hr h⟩
    y.1 = affinePhase P Q + greenOperator (composeBallPath hF y) := by
  let y : BallPath (T := UnitInterval) (p, (0 : E)) r :=
    ⟨segmentPhasePath h.1, short_path_mem hr h⟩
  let a := composeBallPath hF y
  let xdiff := fun t => γ t - bvpPosition P Q a t
  let vdiff := fun t => v t - bvpVelocity P Q a t
  have hx (t : ℝ) (ht : t ∈ UnitInterval) : HasDerivAt xdiff (vdiff t) t :=
    (h.1.1 t ht).fun_sub (hasDerivAt_bvpPosition P Q a t)
  have hv (t : ℝ) (ht : t ∈ UnitInterval) : HasDerivAt vdiff 0 t := by
    have he : pathExtend a t = -σ • K (C (γ t)) (v t) (v t) := by
      rw [pathExtend_mem a t ht]
      rfl
    simpa only [he, sub_self, vdiff, Pi.sub_apply] using (h.1.2 t ht).fun_sub
        (hasDerivAt_bvpVelocity P Q a t)
  have h0 : xdiff 0 = 0 := by simp [xdiff, h.2.1]
  have h1 : xdiff 1 = 0 := by simp [xdiff, h.2.2.1]
  have hpos (t : ℝ) (ht : t ∈ UnitInterval) : γ t = bvpPosition P Q a t := by
    exact sub_eq_zero.mp (dirichlet_unique xdiff vdiff hx hv h0 h1 t ht)
  have hvel (t : ℝ) (ht : t ∈ UnitInterval) : v t = bvpVelocity P Q a t := by
    have hb := dirichlet_velocity_bound xdiff vdiff (fun _ => (0 : E)) 0
      hx hv (by simp) h0 h1 t ht
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  change y.1 = _
  ext t : 1
  apply Prod.ext
  · change γ t = bvpPosition P Q a t
    exact hpos t t.property
  · change v t = bvpVelocity P Q a t
    exact hvel t t.property

/-- Every sufficiently close pair of endpoints has a unique short geodesic.
The permitted phase radius can be chosen below any prescribed positive size. -/
theorem exists_unique_short_geodesic {C : E → Coeff} {p : E}
    (hC : ContDiffAt ℝ 1 C p) (σ : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ r > (0 : ℝ), r ≤ η ∧ ∃ δ > (0 : ℝ), ∀ P Q,
      P ∈ ball p δ → Q ∈ ball p δ → ∃ γ v,
        IsShortGeodesic C σ p r P Q γ v ∧
        ∀ γ' v', IsShortGeodesic C σ p r P Q γ' v' →
          ∀ t ∈ UnitInterval, γ' t = γ t ∧ v' t = v t := by
  let F : Phase → E := fun z => -σ • K (C z.1) z.2 z.2
  have hFp : F (p, 0) = 0 := by apply vec_ext <;> simp [F, K]
  obtain ⟨S, hS, hLip⟩ := (hasStrictFDerivAt_acceleration_zero hC
      σ).exists_lipschitzOnWith_of_nnnorm_lt (1 / 4 : ℝ≥0) (by norm_num)
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
  let r := min (ε / 2) η
  have hr : 0 < r := lt_min (by positivity) hη
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrη : r ≤ η := min_le_right _ _
  have hFr : LipschitzOnWith (1 / 4 : ℝ≥0) F (closedBall (p, (0 : E)) r) :=
    hLip.mono (fun z hz => hεS (lt_of_le_of_lt hz hrε))
  refine ⟨r, hr, hrη, r / 16, by positivity, ?_⟩
  intro P Q hP hQ
  have ha : dist (affinePhase P Q) (ContinuousMap.const UnitInterval (p, (0 : E))) ≤ r / 4 := by
    have h := affinePhase_near p P Q (r := r / 2) (by positivity)
      (by change dist P p < r / 16 at hP; linarith)
      (by change dist Q p < r / 16 at hQ; linarith)
    linarith
  have hsmall : ‖greenOperator‖ * ((1 / 4 : ℝ≥0) : ℝ) ≤ 1 / 2 := by
    norm_num
    nlinarith [norm_greenOperator_le]
  obtain ⟨y, hy, huniq⟩ := exists_unique_green_path greenOperator (p, (0 : E)) r hr.le
    F (1 / 4) hFr hFp hsmall (affinePhase P Q) (ha.trans (by linarith))
  let a := composeBallPath hFr y
  let γ := bvpPosition P Q a
  let v := bvpVelocity P Q a
  obtain ⟨hgeom, hpath⟩ := fixed_green_isGeodesic C σ p P Q r hFr y hy
  have hGbound : ‖greenOperator a‖ ≤ r / 4 := by
    have hn := composeBallPath_norm hr.le hFr hFp y
    have hg := norm_greenPath_le a
    change ‖greenPath a‖ ≤ r / 4
    norm_num at hn
    exact hg.trans (by simpa [a, div_eq_mul_inv, mul_comm] using hn)
  have hnear : dist y.1 (ContinuousMap.const UnitInterval (p, (0 : E))) ≤ r / 2 := by
    rw [hy]
    calc
      dist (affinePhase P Q + greenOperator a) (ContinuousMap.const UnitInterval (p, (0 : E)))
          ≤ dist (affinePhase P Q + greenOperator a) (affinePhase P Q) + dist (affinePhase P Q)
              (ContinuousMap.const UnitInterval (p, (0 : E))) := dist_triangle _ _ _
      _ = ‖greenOperator a‖ + dist (affinePhase P Q) (ContinuousMap.const UnitInterval (p, (0 :
          E))) := by simp
      _ ≤ r / 2 := by linarith
  have hshort : IsShortGeodesic C σ p r P Q γ v := by
    refine ⟨hgeom, bvpPosition_zero P Q a, bvpPosition_one P Q a, ?_⟩
    intro t ht
    have hb := (ContinuousMap.dist_apply_le_dist (f := y.1)
      (g := ContinuousMap.const UnitInterval (p, (0 : E))) ⟨t, ht⟩).trans hnear
    rw [← hpath t ht] at hb
    change max (dist (γ t) p) (dist (v t) 0) ≤ r / 2 at hb
    have hb1 := (max_le_iff.mp hb).1
    have hb2 := (max_le_iff.mp hb).2
    constructor
    · rw [dist_eq_norm] at hb1
      linarith
    · rw [dist_zero_right] at hb2
      linarith
  refine ⟨γ, v, hshort, ?_⟩
  intro γ' v' hg' t ht
  let y' : BallPath (T := UnitInterval) (p, (0 : E)) r :=
    ⟨segmentPhasePath hg'.1, short_path_mem hr.le hg'⟩
  have hfix : y'.1 = affinePhase P Q + greenOperator (composeBallPath hFr y') :=
    actual_geodesic_is_fixed hr.le hFr hg'
  have he : y' = y := huniq y' hfix
  have heval := congrArg (fun z : BallPath (T := UnitInterval) (p, (0 : E)) r => z.1 ⟨t, ht⟩) he
  change (γ' t, v' t) = y.1 ⟨t, ht⟩ at heval
  rw [← hpath t ht] at heval
  exact ⟨congrArg Prod.fst heval, congrArg Prod.snd heval⟩

end
end PlanarMidpoint
