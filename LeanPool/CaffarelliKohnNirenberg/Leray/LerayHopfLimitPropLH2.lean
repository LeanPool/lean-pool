/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropSlice
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitWeakContinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Weak continuity of the Leray–Hopf limit

This is the weak-continuity clause (LH2) of `def:leray-hopf` in the proof of
`prop:leray-hopf-limit`. Every slice of the limit lies in the `L²` closure of
smooth, compactly supported, divergence-free fields. Pairings with such fields
are Lipschitz in time by the uniform modulus of `lem:reg-equicontinuity`, and
the uniform energy bound extends continuity to every `L²` field: the
component orthogonal to the solenoidal fields pairs to zero.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Continuity of the pairings on a spanning family extends to all tests when
the curve stays bounded in the closed span of the family. -/
theorem lerayHopfLimit_continuousOn_inner_of_mem_closure_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (T M : ℝ) (hM : 0 ≤ M) (v : ℝ → E)
    (hbound : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ M)
    (hmem : ∀ t ∈ Icc 0 T, v t ∈ (Submodule.span ℝ S).topologicalClosure)
    (hcont : ∀ s ∈ S, ContinuousOn (fun t => inner ℝ (v t) s) (Icc 0 T)) :
    ∀ W : E, ContinuousOn (fun t => inner ℝ (v t) W) (Icc 0 T) := by
  let K : Submodule ℝ E := (Submodule.span ℝ S).topologicalClosure
  have : CompleteSpace K :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ S)).completeSpace_coe
  let D : Submodule ℝ E := Submodule.span ℝ S ⊔ Kᗮ
  have hspan : ∀ y ∈ Submodule.span ℝ S,
      ContinuousOn (fun t => inner ℝ (v t) y) (Icc 0 T) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hcont x hx
    | zero => simpa only [inner_zero_right] using continuousOn_const
    | add x y _ _ hx hy =>
        have heq : (fun t => inner ℝ (v t) (x + y)) =
            fun t => inner ℝ (v t) x + inner ℝ (v t) y :=
          funext fun t => inner_add_right _ _ _
        rw [heq]
        exact hx.add hy
    | smul c x _ hx =>
        have heq : (fun t => inner ℝ (v t) (c • x)) = fun t => c * inner ℝ (v t) x :=
          funext fun t => real_inner_smul_right _ _ _
        rw [heq]
        exact continuousOn_const.mul hx
  have hD : Dense (D : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
    have h1 : K ≤ D.topologicalClosure :=
      Submodule.topologicalClosure_mono le_sup_left
    have h2 : Kᗮ ≤ D.topologicalClosure :=
      le_sup_right.trans (Submodule.le_topologicalClosure D)
    rw [← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := K)]
    exact sup_le h1 h2
  have hDcont : ∀ d ∈ (D : Set E), ContinuousOn (fun t => inner ℝ (v t) d) (Icc 0 T) := by
    intro d hd
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hd
    refine (hspan y hy).congr (fun t ht => ?_)
    change inner ℝ (v t) (y + z) = inner ℝ (v t) y
    rw [inner_add_right, Submodule.inner_right_of_mem_orthogonal (hmem t ht) hz, add_zero]
  exact continuousOn_inner_of_dense_tests hM v (D : Set E) hD hbound hDcont

/-- The Euclidean `L²` elements of smooth, compactly supported, divergence-free
coordinate fields. -/
@[expose]
def lerayHopfLimitSolenoidalTests : Set (Lp L2Vec3 2 (volume : Measure Vec3)) :=
  {y | ∃ wc : Fin 3 → Vec3 → ℝ, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i)) ∧
    (∀ i, HasCompactSupport (wc i)) ∧ (∀ x, ∑ i : Fin 3, spatialDeriv (wc i) i x = 0) ∧
    ∃ hw : MemLp (fun x i => wc i x) 2 volume,
      y = (lerayHopfLimit_toLp_memLp hw).toLp
        (fun x => (WithLp.toLp 2 (fun i => wc i x) : L2Vec3))}

/-- Every weakly divergence-free `L²` field lies in the closure of the smooth
compactly supported solenoidal tests. -/
theorem lerayHopfLimit_mem_closure_solenoidalTests
    {f : Vec3 → Vec3} (hf : IsWeakDivFreeL2 f) :
    (lerayHopfLimit_toLp_memLp hf.1).toLp (fun x => (WithLp.toLp 2 (f x) : L2Vec3)) ∈
      closure lerayHopfLimitSolenoidalTests := by
  obtain ⟨_, aSeq, hsmooth, hcpt, hdiv, hlim⟩ := weakDivFreeL2_isInJ hf
  have hcomp : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (fun x => aSeq k x i) :=
    fun k i => (contDiff_pi.mp (hsmooth k)) i
  have hcompc : ∀ k i, HasCompactSupport (fun x => aSeq k x i) :=
    fun k i => (hcpt k).comp_left (g := fun v : Vec3 => v i) rfl
  have hmemk : ∀ k, MemLp (aSeq k) 2 volume := fun k =>
    (hsmooth k).continuous.memLp_of_hasCompactSupport (hcpt k)
  let Y : ℕ → Lp L2Vec3 2 (volume : Measure Vec3) := fun k =>
    (lerayHopfLimit_toLp_memLp (hmemk k)).toLp (fun x => (WithLp.toLp 2 (aSeq k x) : L2Vec3))
  have hY : ∀ k, Y k ∈ lerayHopfLimitSolenoidalTests := by
    intro k
    exact ⟨fun i x => aSeq k x i, hcomp k, hcompc k, hdiv k, hmemk k, rfl⟩
  refine mem_closure_of_tendsto (f := Y) (b := atTop) ?_ (Filter.Eventually.of_forall hY)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ k, ‖Y k - (lerayHopfLimit_toLp_memLp hf.1).toLp
      (fun x => (WithLp.toLp 2 (f x) : L2Vec3))‖ =
      (eLpNorm (fun x => (WithLp.toLp 2 (aSeq k x) : L2Vec3) - WithLp.toLp 2 (f x))
        2 volume).toReal := by
    intro k
    change ‖(lerayHopfLimit_toLp_memLp (hmemk k)).toLp _ -
      (lerayHopfLimit_toLp_memLp hf.1).toLp _‖ = _
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  simp only [hnorm]
  have hle : ∀ k, eLpNorm (fun x => (WithLp.toLp 2 (aSeq k x) : L2Vec3) - WithLp.toLp 2 (f x))
      2 volume ≤ ENNReal.ofReal (Real.sqrt 3) *
        eLpNorm (fun x => aSeq k x - f x) 2 volume := by
    intro k
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((lerayHopfLimit_toLp_memLp (hmemk k)).sub
        (lerayHopfLimit_toLp_memLp hf.1)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_)) 2
    rw [Pi.sub_apply, ← WithLp.toLp_sub]
    calc ‖(WithLp.toLp 2 (aSeq k x - f x) : L2Vec3)‖
        = vec3EuclideanNorm (aSeq k x - f x) := (vec3EuclideanNorm_eq_l2 _).symm
      _ ≤ Real.sqrt 3 * ‖aSeq k x - f x‖ := vec3EuclideanNorm_le_sqrt_three_mul_norm _
  have hup : Tendsto (fun k => ENNReal.ofReal (Real.sqrt 3) *
      eLpNorm (fun x => aSeq k x - f x) 2 volume) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt 3)) hlim
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [mul_zero] using h
  have hlim' : Tendsto (fun k => eLpNorm
      (fun x => (WithLp.toLp 2 (aSeq k x) : L2Vec3) - WithLp.toLp 2 (f x)) 2 volume)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => bot_le) hle
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim'
  rw [ENNReal.toReal_zero] at h
  exact h

/-- A Lipschitz bound for approximating pairings passes to their pointwise
limits. -/
theorem lerayHopfLimit_limitPairing_lipschitz
    (P : ℕ → ℝ → ℝ) (Q : ℝ → ℝ) (K : ℝ)
    (hmod : ∀ n s t, 0 ≤ s → 0 ≤ t → |P n t - P n s| ≤ K * |t - s|)
    (hconv : ∀ t, 0 ≤ t → Tendsto (fun n => P n t) atTop (𝓝 (Q t))) :
    ∀ s t, 0 ≤ s → 0 ≤ t → |Q t - Q s| ≤ K * |t - s| := by
  intro s t hs ht
  have h := ((hconv t ht).sub (hconv s hs)).abs
  exact le_of_tendsto h (Filter.Eventually.of_forall (fun n => hmod n s t hs ht))

/-- The weak-continuity clause (LH2): if every slice is a weakly
divergence-free `L²` field with a uniform bound, and the pairings with smooth
compactly supported solenoidal fields are Lipschitz in time, then the pairing
with every `L²` field is continuous on `[0,T]`. -/
theorem lerayHopfLimit_weakContinuity
    (T : ℝ) (u : ParabolicPoint → Vec3) (M : ℝ) (hM : 0 ≤ M)
    (hdiv : ∀ t, 0 ≤ t → IsWeakDivFreeL2 (fun x => u (x, t)))
    (hnorm : ∀ t (ht : 0 ≤ t), ‖(lerayHopfLimit_toLp_memLp (hdiv t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3))‖ ≤ M)
    (hmod : ∀ wc : Fin 3 → Vec3 → ℝ, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i)) →
      (∀ i, HasCompactSupport (wc i)) → (∀ x, ∑ i : Fin 3, spatialDeriv (wc i) i x = 0) →
      ∃ K : ℝ, ∀ s t, 0 ≤ s → 0 ≤ t →
        |(∫ x, ∑ i : Fin 3, u (x, t) i * wc i x) -
          ∫ x, ∑ i : Fin 3, u (x, s) i * wc i x| ≤ K * |t - s|) :
    ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * w x i) (Icc 0 T) := by
  let v : ℝ → Lp L2Vec3 2 (volume : Measure Vec3) := fun t =>
    if ht : 0 ≤ t then (lerayHopfLimit_toLp_memLp (hdiv t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3)) else 0
  have hv : ∀ t (ht : 0 ≤ t), v t = (lerayHopfLimit_toLp_memLp (hdiv t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3)) := by
    intro t ht
    simp [v, ht]
  have hpair : ∀ t (ht : 0 ≤ t) (w : Vec3 → Vec3) (hw : MemLp w 2 volume),
      inner ℝ (v t) ((lerayHopfLimit_toLp_memLp hw).toLp
        (fun x => (WithLp.toLp 2 (w x) : L2Vec3))) =
        ∫ x, ∑ i : Fin 3, u (x, t) i * w x i := by
    intro t ht w hw
    rw [hv t ht]
    exact lerayHopfLimit_inner_toLp_eq (hdiv t ht).1 hw
  have hcont : ∀ s ∈ lerayHopfLimitSolenoidalTests,
      ContinuousOn (fun t => inner ℝ (v t) s) (Icc 0 T) := by
    rintro s ⟨wc, hwc, hwcc, hwdiv, hw, rfl⟩
    obtain ⟨K, hK⟩ := hmod wc hwc hwcc hwdiv
    have heq : EqOn (fun t => inner ℝ (v t) ((lerayHopfLimit_toLp_memLp hw).toLp
        (fun x => (WithLp.toLp 2 (fun i => wc i x) : L2Vec3))))
        (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * wc i x) (Icc 0 T) := by
      intro t ht
      exact hpair t ht.1 _ hw
    refine ContinuousOn.congr ?_ heq
    rw [Metric.continuousOn_iff]
    intro b hb e he
    refine ⟨e / (|K| + 1), by positivity, fun c hc hcb => ?_⟩
    rw [Real.dist_eq]
    have h := hK b c hb.1 hc.1
    have hKabs : K * |c - b| ≤ |K| * |c - b| :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
    have hcb' : |c - b| < e / (|K| + 1) := by rwa [Real.dist_eq] at hcb
    have hlt : |K| * |c - b| < e := by
      calc |K| * |c - b| ≤ (|K| + 1) * |c - b| :=
            mul_le_mul_of_nonneg_right (by linarith only) (abs_nonneg _)
        _ < (|K| + 1) * (e / (|K| + 1)) :=
            mul_lt_mul_of_pos_left hcb' (by positivity)
        _ = e := by field_simp
    linarith only [h, hKabs, hlt]
  have hmemS : ∀ t ∈ Icc 0 T,
      v t ∈ (Submodule.span ℝ lerayHopfLimitSolenoidalTests).topologicalClosure := by
    intro t ht
    rw [hv t ht.1]
    have h := lerayHopfLimit_mem_closure_solenoidalTests (hdiv t ht.1)
    exact closure_mono Submodule.subset_span h
  have hbound : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ M := by
    intro t ht
    rw [hv t ht.1]
    exact hnorm t ht.1
  intro w hw
  have h := lerayHopfLimit_continuousOn_inner_of_mem_closure_span
    lerayHopfLimitSolenoidalTests T M hM v hbound hmemS hcont
    ((lerayHopfLimit_toLp_memLp hw).toLp (fun x => (WithLp.toLp 2 (w x) : L2Vec3)))
  exact h.congr (fun t ht => (hpair t ht.1 w hw).symm)

end CKN.Leray

end
