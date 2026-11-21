/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Thm73
public import LeanPool.RupertMinimality.Minimality.BadViews

/-! # Perturb -/

@[expose] public section

namespace RupertMinimality

/-!
# Generic views: openness and density

* For a strictly convex counterclockwise polygon, a point is in the interior
  of the hull iff it is strictly left of every edge
  (`IsCcwPolygon.mem_interior_iff`).
* Strict convexity, strict interiority and cyclic unimodality persist under
  small continuous perturbations (`eventually_isCcwPolygon`,
  `eventually_mem_interior`, `eventually_isCyclicUnimodal`).
* Views avoiding finitely many great circles are dense
  (`exists_rotation_near_avoiding`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem inner_outNormal (a b w : ℝ²) : ⟪outNormal a b, w⟫ = -cross2 (b - a) w := by
  simp [outNormal, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- A normal at `p` to `S` is strictly negative towards interior points. -/
theorem inner_neg_of_mem_interior {S : Set ℝ²} {p q n : ℝ²} (hn0 : n ≠ 0)
    (hn : ∀ c ∈ S, ⟪n, c - p⟫ ≤ 0) (hq : q ∈ interior S) : ⟪n, q - p⟫ < 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hq
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  have hmem : q + (r / 2 / ‖n‖) • n ∈ S := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_mul_cancel₀ _ hnpos.ne']
    linarith))
  have := hn _ hmem
  rw [show q + (r / 2 / ‖n‖) • n - p = (q - p) + (r / 2 / ‖n‖) • n by abel, inner_add_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq] at this
  have : 0 < r / 2 / ‖n‖ * ‖n‖ ^ 2 := by positivity
  linarith

namespace IsCcwPolygon

variable {k : ℕ} {p : ZMod k → ℝ²}

/-- The hull lies (weakly) left of every edge. -/
theorem left_of_mem_convexHull (hp : IsCcwPolygon p) (i : ZMod k) {c : ℝ²}
    (hc : c ∈ convexHull ℝ (Set.range p)) : 0 ≤ cross2 (p (i + 1) - p i) (c - p i) := by
  have hconv : Convex ℝ {w : ℝ² | 0 ≤ cross2 (p (i + 1) - p i) (w - p i)} := by
    have : {w : ℝ² | 0 ≤ cross2 (p (i + 1) - p i) (w - p i)} =
        {w : ℝ² | ⟪outNormal (p i) (p (i + 1)), w⟫ ≤ ⟪outNormal (p i) (p (i + 1)), p i⟫} := by
      ext w
      simp only [Set.mem_ofPred_eq]
      rw [show ⟪outNormal (p i) (p (i + 1)), w⟫ = ⟪outNormal (p i) (p (i + 1)), w - p i⟫ +
        ⟪outNormal (p i) (p (i + 1)), p i⟫ by rw [← inner_add_right, sub_add_cancel],
        inner_outNormal]
      constructor <;> intro h <;> linarith
    rw [this]; exact convex_halfSpace_le (innerₛₗ ℝ _).isLinear _
  refine convexHull_min ?_ hconv hc
  rintro _ ⟨j, rfl⟩
  by_cases h1 : j = i
  · subst h1; simp [cross2]
  by_cases h2 : j = i + 1
  · subst h2; simp only [Set.mem_ofPred_eq, cross2_self, le_refl]
  exact (hp.2 i j h1 h2).le

theorem edge_ne_zero (hp : IsCcwPolygon p) (i : ZMod k) : p (i + 1) - p i ≠ 0 := by
  intro h
  have := hp.cross2_edge_pos i
  rw [h] at this; simp [cross2] at this

/-- Interior points are strictly left of every edge. -/
theorem left_of_mem_interior (hp : IsCcwPolygon p) (i : ZMod k) {q : ℝ²}
    (hq : q ∈ interior (convexHull ℝ (Set.range p))) :
    0 < cross2 (p (i + 1) - p i) (q - p i) := by
  have hn0 : outNormal (p i) (p (i + 1)) ≠ 0 := by
    intro h
    have := congrArg (fun w => ⟪w, outNormal (p i) (p (i + 1))⟫) h
    simp only [inner_outNormal, inner_zero_left] at this
    have e := hp.edge_ne_zero i
    apply e
    have h0 : cross2 (p (i + 1) - p i) (outNormal (p i) (p (i + 1))) =
        -‖p (i + 1) - p i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
      simp [outNormal, cross2]
      ring_nf
    rw [h0, neg_neg] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  have := inner_neg_of_mem_interior hn0 (fun c hc => by
    rw [inner_outNormal]; linarith [hp.left_of_mem_convexHull i hc]) hq
  rw [inner_outNormal] at this; linarith

/-- Points weakly left of every edge lie in the hull. -/
theorem mem_convexHull_of_left [NeZero k] (hp : IsCcwPolygon p) {q : ℝ²}
    (h : ∀ i, 0 ≤ cross2 (p (i + 1) - p i) (q - p i)) : q ∈ convexHull ℝ (Set.range p) := by
  by_contra hq
  have hC : IsCompact (convexHull ℝ (Set.range p)) :=
    (Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ _) hC (convex_singleton q) isClosed_singleton
    (Set.disjoint_singleton_right.mpr hq)
  have hfq : ∀ c ∈ convexHull ℝ (Set.range p), f c < f q := fun c hc =>
    (hfu c hc).trans (huv.trans (hfv q rfl))
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => f (p i)) ⟨0, mem_univ _⟩
  set n := (InnerProductSpace.toDual ℝ ℝ²).symm f with hndef
  have hnf : ∀ w, ⟪n, w⟫ = f w := fun w => by
    rw [hndef, InnerProductSpace.toDual_symm_apply]
  have hnN : n ∈ normalConeAt (convexHull ℝ (Set.range p)) (p m) := by
    intro c hc
    rw [inner_sub_right, hnf, hnf, sub_nonpos]
    have hconv : Convex ℝ {w : ℝ² | f w ≤ f (p m)} :=
      convex_halfSpace_le f.toLinearMap.isLinear _
    refine convexHull_min ?_ hconv hc
    rintro _ ⟨j, rfl⟩; exact hm j (mem_univ _)
  obtain ⟨a, b, ha, hb, hab⟩ := hp.normalCone_decomp m hnN
  have hpos : 0 < ⟪n, q - p m⟫ := by
    rw [inner_sub_right, hnf, hnf]; linarith [hfq (p m) (subset_convexHull ℝ _ ⟨m, rfl⟩)]
  rw [hab, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_outNormal,
    inner_outNormal] at hpos
  have h1 := h m
  have h2 := h (m - 1)
  rw [sub_add_cancel] at h2
  have h2' : cross2 (p m - p (m - 1)) (q - p m) = cross2 (p m - p (m - 1)) (q - p (m - 1)) := by
    rw [show q - p m = (q - p (m - 1)) - (p m - p (m - 1)) by abel, cross2_sub_right, cross2_self,
      sub_zero]
  rw [h2'] at hpos
  nlinarith [mul_nonneg ha h2, mul_nonneg hb h1]

/-- Points strictly left of every edge are interior. -/
theorem mem_interior_of_left [NeZero k] (hp : IsCcwPolygon p) {q : ℝ²}
    (h : ∀ i, 0 < cross2 (p (i + 1) - p i) (q - p i)) :
    q ∈ interior (convexHull ℝ (Set.range p)) := by
  have hopen : IsOpen {w : ℝ² | ∀ i, 0 < cross2 (p (i + 1) - p i) (w - p i)} := by
    rw [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
    simp only [cross2]; fun_prop
  exact interior_maximal (fun w hw => hp.mem_convexHull_of_left fun i => (hw i).le) hopen h

theorem mem_interior_iff [NeZero k] (hp : IsCcwPolygon p) {q : ℝ²} :
    q ∈ interior (convexHull ℝ (Set.range p)) ↔ ∀ i, 0 < cross2 (p (i + 1) - p i) (q - p i) :=
  ⟨fun hq i => hp.left_of_mem_interior i hq, hp.mem_interior_of_left⟩

end IsCcwPolygon

section Eventually

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

theorem continuousAt_cross2 {f g : X → ℝ²} (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) :
    ContinuousAt (fun x => cross2 (f x) (g x)) x₀ := by
  simp only [cross2]; fun_prop

theorem eventually_isCcwPolygon {k : ℕ} [NeZero k] {p : X → ZMod k → ℝ²}
    (hc : ∀ i, ContinuousAt (fun x => p x i) x₀) (h : IsCcwPolygon (p x₀)) :
    ∀ᶠ x in 𝓝 x₀, IsCcwPolygon (p x) := by
  have : ∀ i j : ZMod k, ∀ᶠ x in 𝓝 x₀, j ≠ i → j ≠ i + 1 →
      0 < cross2 (p x (i + 1) - p x i) (p x j - p x i) := by
    intro i j
    by_cases hj : j ≠ i ∧ j ≠ i + 1
    · have hcont : ContinuousAt (fun x => cross2 (p x (i + 1) - p x i) (p x j - p x i)) x₀ :=
        continuousAt_cross2 ((hc (i + 1)).sub (hc i)) ((hc j).sub (hc i))
      exact (hcont.eventually (lt_mem_nhds (h.2 i j hj.1 hj.2))).mono fun x hx _ _ => hx
    · exact Eventually.of_forall fun x h1 h2 => absurd ⟨h1, h2⟩ hj
  filter_upwards [eventually_all.2 fun i => eventually_all.2 (this i)] with x hx
  exact ⟨h.1, fun i j h1 h2 => hx i j h1 h2⟩

theorem eventually_left {k : ℕ} [NeZero k] {p : X → ZMod k → ℝ²} {q : X → ℝ²}
    (hc : ∀ i, ContinuousAt (fun x => p x i) x₀) (hq : ContinuousAt q x₀)
    (h : ∀ i, 0 < cross2 (p x₀ (i + 1) - p x₀ i) (q x₀ - p x₀ i)) :
    ∀ᶠ x in 𝓝 x₀, ∀ i, 0 < cross2 (p x (i + 1) - p x i) (q x - p x i) :=
  eventually_all.2 fun i =>
    (continuousAt_cross2 ((hc (i + 1)).sub (hc i)) (hq.sub (hc i))).eventually (lt_mem_nhds (h i))

theorem eventually_mem_interior {k : ℕ} [NeZero k] {p : X → ZMod k → ℝ²} {q : X → ℝ²}
    (hc : ∀ i, ContinuousAt (fun x => p x i) x₀) (hq : ContinuousAt q x₀)
    (hp : IsCcwPolygon (p x₀)) (h : q x₀ ∈ interior (convexHull ℝ (Set.range (p x₀)))) :
    ∀ᶠ x in 𝓝 x₀, q x ∈ interior (convexHull ℝ (Set.range (p x))) := by
  filter_upwards [eventually_isCcwPolygon hc hp, eventually_left hc hq (hp.mem_interior_iff.mp h)]
    with x hx hl
  exact hx.mem_interior_of_left hl

/-- A strict order between finitely many continuous values persists. -/
theorem eventually_lt_iff {k : ℕ} [NeZero k] {z : X → ZMod k → ℝ}
    (hc : ∀ i, ContinuousAt (fun x => z x i) x₀) (hinj : Function.Injective (z x₀)) :
    ∀ᶠ x in 𝓝 x₀, ∀ a b, z x a < z x b ↔ z x₀ a < z x₀ b := by
  have : ∀ a b : ZMod k, ∀ᶠ x in 𝓝 x₀, z x₀ a < z x₀ b → z x a < z x b := by
    intro a b
    by_cases hab : z x₀ a < z x₀ b
    · exact ((hc a).sub (hc b) |>.eventually (gt_mem_nhds (sub_neg.mpr hab))).mono
        fun x hx _ => sub_neg.mp hx
    · exact Eventually.of_forall fun x h => absurd h hab
  filter_upwards [eventually_all.2 fun a => eventually_all.2 (this a)] with x hx
  intro a b
  refine ⟨fun h => ?_, hx a b⟩
  by_contra h'
  rcases eq_or_ne a b with rfl | hne
  · exact lt_irrefl _ h
  · have := hx b a (lt_of_le_of_ne (not_lt.mp h') (hinj.ne hne.symm))
    linarith

theorem eventually_isCyclicUnimodal {k : ℕ} [NeZero k] {z : X → ZMod k → ℝ}
    (hc : ∀ i, ContinuousAt (fun x => z x i) x₀) (h : IsCyclicUnimodal (z x₀)) :
    ∀ᶠ x in 𝓝 x₀, IsCyclicUnimodal (z x) := by
  filter_upwards [eventually_lt_iff hc h.1] with x hx
  refine ⟨fun a b hab => ?_, ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne (h.1.ne hne) with h1 | h1
    · have := (hx a b).2 h1; rw [hab] at this; exact lt_irrefl _ this
    · have := (hx b a).2 h1; rw [hab] at this; exact lt_irrefl _ this
  · rw [← h.2]
    congr 1
    exact filter_congr fun i _ => by rw [hx, hx]

end Eventually

/-- Rotation about the y-axis with `cos = c`, `sin = s`. -/
def rotY (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![c, 0, s; 0, 1, 0; -s, 0, c]

theorem rotY_mem_SO3 {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rotY c s ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotY, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring_nf <;> linear_combination h
  · simp [rotY, Matrix.det_fin_three]; linear_combination h

theorem continuous_toEuclideanLin_apply (v : ℝ³) :
    Continuous fun R : Matrix (Fin 3) (Fin 3) ℝ => R.toEuclideanLin v := by
  simp only [Matrix.toLpLin_apply]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_mulVec continuous_const)

/-- The tilt `rotX t · rotY t` used to perturb views. -/
noncomputable def tilt (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rotX (Real.cos t) (Real.sin t) * rotY (Real.cos t) (Real.sin t)

theorem tilt_mem_SO3 (t : ℝ) : tilt t ∈ SO3 :=
  mul_mem (rotX_mem_SO3 (by rw [add_comm]; exact Real.sin_sq_add_cos_sq t))
    (rotY_mem_SO3 (by rw [add_comm]; exact Real.sin_sq_add_cos_sq t))

theorem continuous_tilt : Continuous tilt := by
  unfold tilt
  refine Continuous.mul ?_ ?_
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Real.continuous_sin
      | exact Real.continuous_cos
      | exact Real.continuous_sin.neg
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Real.continuous_sin
      | exact Real.continuous_cos
      | exact Real.continuous_sin.neg

theorem tilt_zero : tilt 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tilt, rotX, rotY, Matrix.mul_apply,
    Fin.sum_univ_three]

theorem tilt_apply_two (t : ℝ) (m : ℝ³) :
    ((tilt t).toEuclideanLin m) 2 =
      -(Real.cos t * Real.sin t) * m 0 + Real.sin t * m 1 + Real.cos t ^ 2 * m 2 := by
  have e0 : tilt t 2 0 = -(Real.cos t * Real.sin t) := by
    simp [tilt, rotX, rotY, Matrix.mul_apply, Fin.sum_univ_three]
  have e1 : tilt t 2 1 = Real.sin t := by
    simp [tilt, rotX, rotY, Matrix.mul_apply, Fin.sum_univ_three]
  have e2 : tilt t 2 2 = Real.cos t ^ 2 := by
    simp [tilt, rotX, rotY, Matrix.mul_apply, Fin.sum_univ_three]; ring
  rw [toEuclideanLin_two, e0, e1, e2]

/-- For `m ≠ 0`, the tilted depth of `m` is nonzero for small `t > 0`. -/
theorem eventually_tilt_ne_zero {m : ℝ³} (hm : m ≠ 0) :
    ∀ᶠ t in 𝓝[>] 0, ((tilt t).toEuclideanLin m) 2 ≠ 0 := by
  simp only [tilt_apply_two]
  have hcont : Continuous fun t : ℝ =>
      -(Real.cos t * Real.sin t) * m 0 + Real.sin t * m 1 + Real.cos t ^ 2 * m 2 := by fun_prop
  by_cases h2 : m 2 ≠ 0
  · exact (hcont.continuousAt.eventually_ne (by simpa using h2)).filter_mono nhdsWithin_le_nhds
  push Not at h2
  have hsin : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < Real.sin t ∧ Real.cos t < 1 := by
    filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with t ht
    exact ⟨Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2, by
      simpa using Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl ht.2.le ht.1⟩
  by_cases h10 : m 1 - m 0 ≠ 0
  · have hg : Continuous fun t : ℝ => m 1 - Real.cos t * m 0 := by fun_prop
    filter_upwards [hsin, (hg.continuousAt.eventually_ne (by simpa using h10)).filter_mono
      nhdsWithin_le_nhds] with t ht hg'
    rw [h2, mul_zero, add_zero, show -(Real.cos t * Real.sin t) * m 0 + Real.sin t * m 1 =
      Real.sin t * (m 1 - Real.cos t * m 0) by ring]
    exact mul_ne_zero ht.1.ne' hg'
  push Not at h10
  have h0 : m 0 ≠ 0 := by
    intro h0; apply hm; ext i; fin_cases i
    · exact h0
    · simp; linarith
    · exact h2
  filter_upwards [hsin] with t ht
  rw [h2, mul_zero, add_zero, show m 1 = m 0 by linarith,
    show -(Real.cos t * Real.sin t) * m 0 + Real.sin t * m 0 =
      Real.sin t * (1 - Real.cos t) * m 0 by ring]
  exact mul_ne_zero (mul_ne_zero ht.1.ne' (by linarith [ht.2])) h0

/-- **Density of generic views.**  Near any rotation there are rotations whose
view avoids the finitely many great circles `(R l) 2 = 0`, `l ∈ Λ`. -/
theorem exists_rotation_near_avoiding {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (hR₀ : R₀ ∈ SO3)
    (Λ : Finset ℝ³) (hΛ : ∀ l ∈ Λ, l ≠ 0) {U : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (hU : U ∈ 𝓝 R₀) : ∃ R ∈ U, R ∈ SO3 ∧ ∀ l ∈ Λ, (R.toEuclideanLin l) 2 ≠ 0 := by
  have hT : Tendsto (fun t => tilt t * R₀) (𝓝[>] 0) (𝓝 R₀) := by
    have : Continuous fun t => tilt t * R₀ := continuous_tilt.mul continuous_const
    have h := this.tendsto 0
    rw [tilt_zero, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ l ∈ Λ, ((tilt t * R₀).toEuclideanLin l) 2 ≠ 0 := by
    refine (eventually_all_finset Λ).2 fun l hl => ?_
    have hm : R₀.toEuclideanLin l ≠ 0 := fun h0 =>
      hΛ l hl ((so3Isometry hR₀).injective (by rw [so3Isometry_apply, h0, map_zero]))
    filter_upwards [eventually_tilt_ne_zero hm] with t ht
    have e : (tilt t * R₀).toEuclideanLin l = (tilt t).toEuclideanLin (R₀.toEuclideanLin l) := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rwa [e]
  obtain ⟨t, ht1, ht2⟩ := ((hT.eventually hU).and hall).exists
  exact ⟨_, ht1, mul_mem (tilt_mem_SO3 t) hR₀, ht2⟩

end Minimality

end RupertMinimality
