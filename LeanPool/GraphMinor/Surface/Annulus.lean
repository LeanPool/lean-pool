/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Cap

/-!
# The annulus between a round disc and an `O`-arc around it

Let `F` be an `O`-arc of the plane with the closed unit disc in its inside. The annulus theorem in
this
setting says that a homeomorphism from the disc of radius `2` onto the closed domain of `F` is the
identity on the unit disc (`exists_annulus`).

The two rays from `1` and from `-1` away from the origin, up to the first point of `F`, cut the part
between the unit circle and `F` into two closed domains with four sides each. The same holds for the
circle of radius `2` in place of `F`. By the Schoenflies theorem we may match the two pairs of
domains with any given matching of the four sides, and we paste the results.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

local notation "𝕀" => unitInterval

universe u

/-- A matching of two finite families of arcs of the plane that agree on where they meet. -/
theorem exists_bdMatch_of_family {ι : Type*} [Finite ι] {a a' : ι → 𝕀 → ℂ}
    (ha : ∀ i, IsArcMap (a i)) (ha' : ∀ i, IsArcMap (a' i))
    (h1 : ∀ i j s t, a i s = a j t → a' i s = a' j t)
    (h2 : ∀ i j s t, a' i s = a' j t → a i s = a j t) :
    ∃ h k : ℂ → ℂ, BdMatch (⋃ i, range (a i)) (⋃ i, range (a' i)) h k ∧
      ∀ i s, h (a i s) = a' i s := by
  classical
  have key : ∀ {a a' : ι → 𝕀 → ℂ}, (∀ i, IsArcMap (a i)) → (∀ i, IsArcMap (a' i)) →
      (∀ i j s t, a i s = a j t → a' i s = a' j t) →
      ∃ h : ℂ → ℂ, ContinuousOn h (⋃ i, range (a i)) ∧ ∀ i s, h (a i s) = a' i s := by
    intro a a' ha ha' h1
    let h : ℂ → ℂ := fun z => if hz : ∃ p : ι × 𝕀, a p.1 p.2 = z then a' hz.choose.1 hz.choose.2
      else 0
    have hv : ∀ i s, h (a i s) = a' i s := fun i s => by
      have hz : ∃ p : ι × 𝕀, a p.1 p.2 = a i s := ⟨(i, s), rfl⟩
      simp only [h, dite_eq_left hz]
      exact h1 _ _ _ _ hz.choose_spec
    refine ⟨h, ?_, hv⟩
    refine (locallyFinite_of_finite _).continuousOn_iUnion
      (fun i => (isCompact_range (ha i).1).isClosed) fun i => ?_
    obtain ⟨f, hl, hf⟩ := (ha i).exists_inv
    refine ((ha' i).1.comp_continuousOn hf).congr ?_
    rintro _ ⟨s, rfl⟩
    change h (a i s) = a' i (f (a i s))
    rw [hl, hv]
  obtain ⟨h, hc, hv⟩ := key ha ha' h1
  obtain ⟨k, kc, kv⟩ := key ha' ha h2
  refine ⟨h, k, ⟨?_, ?_, ?_, ?_, hc, kc⟩, hv⟩
  · rintro _ hz
    obtain ⟨i, s, rfl⟩ := mem_iUnion.mp hz
    rw [hv]
    exact mem_iUnion.mpr ⟨i, s, rfl⟩
  · rintro _ hz
    obtain ⟨i, s, rfl⟩ := mem_iUnion.mp hz
    rw [kv]
    exact mem_iUnion.mpr ⟨i, s, rfl⟩
  · rintro _ hz
    obtain ⟨i, s, rfl⟩ := mem_iUnion.mp hz
    rw [hv, kv]
  · rintro _ hz
    obtain ⟨i, s, rfl⟩ := mem_iUnion.mp hz
    show h (k (a' i s)) = _
    rw [kv, hv]

/-- Two closed domains on the two sides of a cut, mapped on two matching sides of another cut, paste
to a map of the closed domain. -/
theorem paste_cut {F F' : Set ℂ} {a b e a' b' e' : 𝕀 → ℂ} (c : IsCut F a b e)
  (c' : IsCut F' a' b' e')
    (J : IsJordanParts F) (J' : IsJordanParts F') {Θ₁ Θ₁' Θ₂ Θ₂' : ℂ → ℂ}
    (m₁ : BdMatch (closedInner (side a e)) (closedInner (side a' e')) Θ₁ Θ₁')
    (m₂ : BdMatch (closedInner (side b e)) (closedInner (side b' e')) Θ₂ Θ₂')
    (h₁ : EqOn Θ₁ Θ₂ (range e)) (he : Θ₁ '' range e = range e') :
    ∃ Θ Θ' : ℂ → ℂ, BdMatch (closedInner F) (closedInner F') Θ Θ' ∧
      EqOn Θ Θ₁ (closedInner (side a e)) ∧ EqOn Θ Θ₂ (closedInner (side b e)) := by
  classical
  obtain ⟨hu, -, -, hm, -, -⟩ := c.closedInner_facts J
  obtain ⟨hu', -, -, hm', -, -⟩ := c'.closedInner_facts J'
  obtain ⟨φ₁⟩ := c.oArc_side
  obtain ⟨φ₂⟩ := c.symm.oArc_side
  obtain ⟨φ₁'⟩ := c'.oArc_side
  obtain ⟨φ₂'⟩ := c'.symm.oArc_side
  have hcl : ∀ {G : Set ℂ}, Nonempty (Circle ≃ₜ G) → IsClosed (closedInner G) := fun hG => by
    obtain ⟨φ⟩ := hG
    exact (isJordanParts φ).isCompact_closure_inner.isClosed
  have hA := hcl ⟨φ₁⟩
  have hB := hcl ⟨φ₂⟩
  have hA' := hcl ⟨φ₁'⟩
  have hB' := hcl ⟨φ₂'⟩
  set A := closedInner (side a e)
  set B := closedInner (side b e)
  set A' := closedInner (side a' e')
  set B' := closedInner (side b' e')
  have heA : range e ⊆ A := fun z hz => subset_union_right (Or.inr hz : z ∈ side a e)
  have heB : range e ⊆ B := fun z hz => subset_union_right (Or.inr hz : z ∈ side b e)
  have heA' : range e' ⊆ A' := fun z hz => subset_union_right (Or.inr hz : z ∈ side a' e')
  -- the inverses agree on the cut
  have h₂e : Θ₂ '' range e = range e' := by
    rw [← he]
    exact (image_congr h₁).symm
  have hinv : EqOn Θ₁' Θ₂' (range e') := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := he.symm ▸ hz
    rw [m₁.leftInvOn (heA hw), h₁ hw, m₂.leftInvOn (heB hw)]
  let Θ : ℂ → ℂ := fun z => if z ∈ A then Θ₁ z else Θ₂ z
  let Θ' : ℂ → ℂ := fun z => if z ∈ A' then Θ₁' z else Θ₂' z
  have hΘA : EqOn Θ Θ₁ A := fun z hz => ite_eq_left hz
  have hΘB : EqOn Θ Θ₂ B := fun z hz => by
    by_cases h : z ∈ A
    · have : Θ z = Θ₁ z := ite_eq_left h
      rw [this]
      exact h₁ (hm ⟨h, hz⟩)
    · exact ite_eq_right h
  have hΘA' : EqOn Θ' Θ₁' A' := fun z hz => ite_eq_left hz
  have hΘB' : EqOn Θ' Θ₂' B' := fun z hz => by
    by_cases h : z ∈ A'
    · have : Θ' z = Θ₁' z := ite_eq_left h
      rw [this]
      exact hinv (hm' ⟨h, hz⟩)
    · exact ite_eq_right h
  have hc : ContinuousOn Θ (closedInner F) := by
    rw [← hu]
    exact ContinuousOn.union_of_isClosed ((m₁.2.2.2.2.1).congr hΘA) ((m₂.2.2.2.2.1).congr hΘB) hA hB
  have hc' : ContinuousOn Θ' (closedInner F') := by
    rw [← hu']
    exact ContinuousOn.union_of_isClosed ((m₁.2.2.2.2.2).congr hΘA') ((m₂.2.2.2.2.2).congr hΘB')
      hA' hB'
  refine ⟨Θ, Θ', ⟨?_, ?_, ?_, ?_, hc, hc'⟩, hΘA, hΘB⟩
  · rw [← hu, ← hu']
    rintro z (hz | hz)
    · rw [hΘA hz]
      exact .inl (m₁.1 hz)
    · rw [hΘB hz]
      exact .inr (m₂.1 hz)
  · rw [← hu, ← hu']
    rintro z (hz | hz)
    · rw [hΘA' hz]
      exact .inl (m₁.2.1 hz)
    · rw [hΘB' hz]
      exact .inr (m₂.2.1 hz)
  · rw [← hu]
    rintro z (hz | hz)
    · rw [hΘA hz, hΘA' (m₁.1 hz)]
      exact m₁.2.2.1 hz
    · rw [hΘB hz, hΘB' (m₂.1 hz)]
      exact m₂.2.2.1 hz
  · rw [← hu']
    rintro z (hz | hz)
    · show Θ (Θ' z) = z
      rw [hΘA' hz, hΘA (m₁.2.1 hz)]
      exact m₁.2.2.2.1 hz
    · show Θ (Θ' z) = z
      rw [hΘB' hz, hΘB (m₂.2.1 hz)]
      exact m₂.2.2.2.1 hz

/-- Four arcs that form an `O`-arc in the order `u`, `p`, `x`, `m`. -/
structure IsQuad (u p m x : 𝕀 → ℂ) : Prop where
  arc_u : IsArcMap u
  arc_p : IsArcMap p
  arc_m : IsArcMap m
  arc_x : IsArcMap x
  up0 : u 0 = p 0
  um0 : u 1 = m 0
  px0 : p 1 = x 0
  mx1 : m 1 = x 1
  up : ∀ s t, u s = p t → s = 0 ∧ t = 0
  um : ∀ s t, u s = m t → s = 1 ∧ t = 0
  pm : ∀ s t, p s ≠ m t
  px : ∀ s t, p s = x t → s = 1 ∧ t = 0
  mx : ∀ s t, m s = x t → s = 1 ∧ t = 1
  ux : ∀ s t, u s ≠ x t

/-- The union of the four arcs. -/
def quadSet (u p m x : 𝕀 → ℂ) : Set ℂ := range u ∪ range p ∪ range m ∪ range x

/-- Four sides are matched by a homeomorphism of their unions. -/
theorem exists_bdMatch_of_quads {u p m x u' p' m' x' : 𝕀 → ℂ} (Q : IsQuad u p m x)
    (Q' : IsQuad u' p' m' x') :
    ∃ h k : ℂ → ℂ, BdMatch (quadSet u p m x) (quadSet u' p' m' x') h k ∧ (∀ s, h (u s) = u' s) ∧
      (∀ s, h (p s) = p' s) ∧ (∀ s, h (m s) = m' s) ∧ ∀ s, h (x s) = x' s := by
  have key : ∀ {u p m x u' p' m' x' : 𝕀 → ℂ}, IsQuad u p m x → IsQuad u' p' m' x' →
      ∀ i j s t, ![u, p, m, x] i s = ![u, p, m, x] j t →
        ![u', p', m', x'] i s = ![u', p', m', x'] j t := by
    intro u p m x u' p' m' x' Q Q' i j s t he
    fin_cases i <;> fin_cases j <;>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
        Fin.reduceFinMk, Matrix.cons_val] at he ⊢
    · rw [Q.arc_u.2 he]
    · obtain ⟨rfl, rfl⟩ := Q.up s t he
      exact Q'.up0
    · obtain ⟨rfl, rfl⟩ := Q.um s t he
      exact Q'.um0
    · exact absurd he (Q.ux s t)
    · obtain ⟨rfl, rfl⟩ := Q.up t s he.symm
      exact Q'.up0.symm
    · rw [Q.arc_p.2 he]
    · exact absurd he (Q.pm s t)
    · obtain ⟨rfl, rfl⟩ := Q.px s t he
      exact Q'.px0
    · obtain ⟨rfl, rfl⟩ := Q.um t s he.symm
      exact Q'.um0.symm
    · exact absurd he.symm (Q.pm t s)
    · rw [Q.arc_m.2 he]
    · obtain ⟨rfl, rfl⟩ := Q.mx s t he
      exact Q'.mx1
    · exact absurd he.symm (Q.ux t s)
    · obtain ⟨rfl, rfl⟩ := Q.px t s he.symm
      exact Q'.px0.symm
    · obtain ⟨rfl, rfl⟩ := Q.mx t s he.symm
      exact Q'.mx1.symm
    · rw [Q.arc_x.2 he]
  have harc : ∀ {u p m x : 𝕀 → ℂ}, IsQuad u p m x → ∀ i, IsArcMap (![u, p, m, x] i) := by
    intro u p m x Q i
    fin_cases i
    · exact Q.arc_u
    · exact Q.arc_p
    · exact Q.arc_m
    · exact Q.arc_x
  have hset : ∀ {u p m x : 𝕀 → ℂ}, (⋃ i, range (![u, p, m, x] i)) = quadSet u p m x := by
    intro u p m x
    ext z
    simp only [mem_iUnion, quadSet, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact .inl (.inl (.inl hi))
      · exact .inl (.inl (.inr hi))
      · exact .inl (.inr hi)
      · exact .inr hi
    · rintro (((h | h) | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
  obtain ⟨h, k, hm, hv⟩ := exists_bdMatch_of_family (harc Q) (harc Q') (key Q Q') (key Q' Q)
  rw [hset, hset] at hm
  exact ⟨h, k, hm, hv 0, hv 1, hv 2, hv 3⟩

/-- The first point of `F` on a ray that starts in the inside. -/
theorem exists_first_hit {F : Set ℂ} (J : IsJordanParts F) (hFc : IsCompact F)
    (hsub : closedBall (0 : ℂ) 1 ⊆ inner F) {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ t : ℝ, 1 < t ∧ (t : ℂ) * u ∈ F ∧ ∀ s ∈ Ico 1 t, (s : ℂ) * u ∈ inner F := by
  let r : ℝ → ℂ := fun t => (t : ℂ) * u
  have hr : Continuous r := Complex.continuous_ofReal.mul continuous_const
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖r t‖ = t := fun t ht => by
    simp only [r, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have h1 : r 1 ∈ inner F := hsub (by simp [r, hu])
  have h1F : r 1 ∉ F := J.inner_subset_compl h1
  let A : Set ℝ := Ici 1 ∩ r ⁻¹' F
  have hAc : IsClosed A := isClosed_Ici.inter (hFc.isClosed.preimage hr)
  have hAne : A.Nonempty := by
    by_contra hcon
    have hdis : Disjoint (r '' Ici 1) F := Set.disjoint_left.mpr fun z hz hzF => by
      obtain ⟨t, ht, rfl⟩ := hz
      exact hcon ⟨t, ht, hzF⟩
    have hin := J.subset_inner (isPreconnected_Ici.image r hr.continuousOn) hdis
      ⟨r 1, ⟨1, self_mem_Ici, rfl⟩, h1⟩
    obtain ⟨M, hM⟩ := J.isCompact_closure_inner.isBounded.subset_closedBall (0 : ℂ)
    have h2 := hM (Or.inl (hin ⟨max 1 M + 1, by
      have := le_max_left 1 M
      change (1 : ℝ) ≤ _
      linarith, rfl⟩) : r (max 1 M + 1) ∈ inner F ∪ F)
    rw [mem_closedBall_zero_iff, hnorm _ (by have := le_max_left 1 M; linarith)] at h2
    have := le_max_right 1 M
    linarith
  have hbdd : BddBelow A := ⟨1, fun x hx => hx.1⟩
  have hmem := hAc.csInf_mem hAne hbdd
  set t := sInf A with ht
  have h1t : 1 < t := lt_of_le_of_ne hmem.1 fun he => h1F (he ▸ hmem.2)
  refine ⟨t, h1t, hmem.2, fun s hs => ?_⟩
  have hdis : Disjoint (r '' Ico 1 t) F := Set.disjoint_left.mpr fun z hz hzF => by
    obtain ⟨x, hx, rfl⟩ := hz
    have := csInf_le hbdd (⟨hx.1, hzF⟩ : x ∈ A)
    linarith [hx.2]
  exact J.subset_inner (isPreconnected_Ico.image r hr.continuousOn) hdis
    ⟨r 1, ⟨1, ⟨le_rfl, h1t⟩, rfl⟩, h1⟩ ⟨s, hs, rfl⟩

/-- The upper half of the unit circle. -/
noncomputable def upArc (s : 𝕀) : ℂ := cis' (Real.pi * s.1)

/-- The lower half of the unit circle. -/
noncomputable def loArc (s : 𝕀) : ℂ := cis' (-(Real.pi * s.1))

/-- A segment of the positive real axis from `1`. -/
noncomputable def rayP (t : ℝ) (s : 𝕀) : ℂ := ((1 + s.1 * (t - 1) : ℝ) : ℂ)

/-- A segment of the negative real axis from `-1`. -/
noncomputable def rayM (t : ℝ) (s : 𝕀) : ℂ := -((1 + s.1 * (t - 1) : ℝ) : ℂ)

theorem cis'_re (θ : ℝ) : (cis' θ).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

theorem cis'_im (θ : ℝ) : (cis' θ).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

theorem upArc_inj : Function.Injective upArc := fun s t he => by
  have h1 := congrArg Complex.re he
  simp only [upArc, cis'_re] at h1
  have hpi := Real.pi_pos
  have hs : Real.pi * s.1 ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg hpi.le s.2.1, by nlinarith [s.2.2]⟩
  have ht : Real.pi * t.1 ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg hpi.le t.2.1, by nlinarith [t.2.2]⟩
  have h2 := Real.injOn_cos hs ht h1
  exact Subtype.ext (mul_left_cancel₀ hpi.ne' h2)

theorem loArc_inj : Function.Injective loArc := fun s t he => by
  apply upArc_inj
  have h1 := congrArg Complex.re he
  have h2 := congrArg Complex.im he
  simp only [loArc, cis'_re, cis'_im, Real.cos_neg, Real.sin_neg] at h1 h2
  apply Complex.ext
  · simpa only [upArc, cis'_re] using h1
  · simpa only [upArc, cis'_im] using neg_injective h2

theorem isArcMap_upArc : IsArcMap upArc :=
  ⟨continuous_cis'.comp (continuous_const.mul continuous_subtype_val), upArc_inj⟩

theorem isArcMap_loArc : IsArcMap loArc :=
  ⟨continuous_cis'.comp (continuous_const.mul continuous_subtype_val).neg, loArc_inj⟩

theorem isArcMap_rayP {t : ℝ} (ht : 1 < t) : IsArcMap (rayP t) := by
  refine ⟨Complex.continuous_ofReal.comp (by fun_prop), fun s s' he => ?_⟩
  have h1 : 1 + s.1 * (t - 1) = 1 + s'.1 * (t - 1) := Complex.ofReal_injective he
  have h2 : s.1 * (t - 1) = s'.1 * (t - 1) := by linarith
  exact Subtype.ext (mul_right_cancel₀ (by linarith : t - 1 ≠ 0) h2)

theorem isArcMap_rayM {t : ℝ} (ht : 1 < t) : IsArcMap (rayM t) := by
  obtain ⟨h1, h2⟩ := isArcMap_rayP ht
  exact ⟨h1.neg, fun s s' he => h2 (neg_injective he)⟩

theorem norm_upArc (s : 𝕀) : ‖upArc s‖ = 1 := norm_cis' _

theorem norm_loArc (s : 𝕀) : ‖loArc s‖ = 1 := norm_cis' _

theorem norm_rayP {t : ℝ} (ht : 1 < t) (s : 𝕀) : ‖rayP t s‖ = 1 + s.1 * (t - 1) := by
  have : 0 ≤ s.1 * (t - 1) := mul_nonneg s.2.1 (by linarith)
  rw [rayP, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

theorem norm_rayM {t : ℝ} (ht : 1 < t) (s : 𝕀) : ‖rayM t s‖ = 1 + s.1 * (t - 1) := by
  rw [rayM, norm_neg]
  exact norm_rayP ht s

theorem eq_zero_of_norm_eq {t : ℝ} (ht : 1 < t) {s : 𝕀} (h : 1 + s.1 * (t - 1) = 1) : s = 0 := by
  have h1 : s.1 * (t - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Subtype.ext h2
  · linarith

@[simp] theorem upArc_zero : upArc 0 = 1 := by simp [upArc, cis']

@[simp] theorem loArc_zero : loArc 0 = 1 := by simp [loArc, cis']

@[simp] theorem upArc_one : upArc 1 = -1 := by simp [upArc, cis']

@[simp] theorem loArc_one : loArc 1 = -1 := by
  simp [loArc, cis', Complex.exp_neg]

@[simp] theorem rayP_zero (t : ℝ) : rayP t 0 = 1 := by simp [rayP]

@[simp] theorem rayM_zero (t : ℝ) : rayM t 0 = -1 := by simp [rayM]

@[simp] theorem rayP_one (t : ℝ) : rayP t 1 = t := by simp [rayP]

@[simp] theorem rayM_one (t : ℝ) : rayM t 1 = -(t : ℂ) := by simp [rayM]

/-- A quadrilateral from a half of the unit circle, the two rays and an arc outside. -/
theorem isQuad_of_halfCircle {u x : 𝕀 → ℂ} {tp tm : ℝ} (hu : IsArcMap u) (hx : IsArcMap x)
    (hn : ∀ s, ‖u s‖ = 1) (hu0 : u 0 = 1) (hu1 : u 1 = -1) (htp : 1 < tp) (htm : 1 < tm)
    (hx0 : x 0 = tp) (hx1 : x 1 = -(tm : ℂ)) (hxn : ∀ t, ‖x t‖ ≠ 1)
    (hp : ∀ s t, rayP tp s = x t → s = 1) (hm : ∀ s t, rayM tm s = x t → s = 1) :
    IsQuad u (rayP tp) (rayM tm) x := by
  refine ⟨hu, isArcMap_rayP htp, isArcMap_rayM htm, hx, by simp [hu0], by simp [hu1], by simp [hx0],
    by simp [hx1], fun s t he => ?_, fun s t he => ?_, fun s t he => ?_, fun s t he => ?_,
    fun s t he => ?_, fun s t he => ?_⟩
  · have h1 : 1 + t.1 * (tp - 1) = 1 := by
      rw [← norm_rayP htp, ← he, hn]
    have h2 := eq_zero_of_norm_eq htp h1
    subst h2
    rw [rayP_zero, ← hu0] at he
    exact ⟨hu.2 he, rfl⟩
  · have h1 : 1 + t.1 * (tm - 1) = 1 := by
      rw [← norm_rayM htm, ← he, hn]
    have h2 := eq_zero_of_norm_eq htm h1
    subst h2
    rw [rayM_zero, ← hu1] at he
    exact ⟨hu.2 he, rfl⟩
  · have h1 := congrArg Complex.re he
    simp only [rayP, rayM, Complex.ofReal_re, Complex.neg_re] at h1
    have h2 : 0 ≤ s.1 * (tp - 1) := mul_nonneg s.2.1 (by linarith)
    have h3 : 0 ≤ t.1 * (tm - 1) := mul_nonneg t.2.1 (by linarith)
    linarith
  · obtain rfl := hp s t he
    rw [rayP_one, ← hx0] at he
    exact ⟨rfl, hx.2 he.symm ▸ rfl⟩
  · obtain rfl := hm s t he
    rw [rayM_one, ← hx1] at he
    exact ⟨rfl, hx.2 he.symm ▸ rfl⟩
  · exact hxn t (he ▸ hn s)

/-- How the rays and the unit circle cut the domain of `F`. -/
structure AnnCut (F : Set ℂ) (p m a b e b₂ : 𝕀 → ℂ) : Prop where
  qa : IsQuad upArc p m a
  qb : IsQuad loArc p m b
  cut : IsCut F a b e
  range_e : range e = range p ∪ range upArc ∪ range m
  cut₂ : IsCut (side b e) upArc b₂ loArc
  range_b : range b₂ = range p ∪ range b ∪ range m

theorem range_upArc_union : range upArc ∪ range loArc = sphere 0 1 := by
  ext z
  constructor
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact mem_sphere_zero_iff_norm.mpr (norm_upArc s)
    · exact mem_sphere_zero_iff_norm.mpr (norm_loArc s)
  · intro hz
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hpi := Real.pi_pos
    have harg := Complex.norm_mul_exp_arg_mul_I z
    rw [hn] at harg
    simp only [Complex.ofReal_one, one_mul] at harg
    have h1 := Complex.neg_pi_lt_arg z
    have h2 := Complex.arg_le_pi z
    rcases le_total 0 (Complex.arg z) with h | h
    · left
      refine ⟨⟨Complex.arg z / Real.pi, div_nonneg h hpi.le, (div_le_one hpi).mpr h2⟩, ?_⟩
      change cis' (Real.pi * (Complex.arg z / Real.pi)) = z
      rw [mul_div_cancel₀ _ hpi.ne', cis', harg]
    · right
      refine ⟨⟨-Complex.arg z / Real.pi, div_nonneg (by linarith) hpi.le,
        (div_le_one hpi).mpr (by linarith)⟩, ?_⟩
      change cis' (-(Real.pi * (-Complex.arg z / Real.pi))) = z
      rw [mul_div_cancel₀ _ hpi.ne', neg_neg, cis', harg]

theorem exists_annCut {F : Set ℂ} (φ : Circle ≃ₜ F) (hsub : closedBall (0 : ℂ) 1 ⊆ inner F) :
    ∃ p m a b e b₂, AnnCut F p m a b e b₂ := by
  have J := isJordanParts φ
  have hFc : IsCompact F := isCompact_of_oArc φ
  obtain ⟨tp, htp, htpF, htpi⟩ := exists_first_hit J hFc hsub (u := 1) (by simp)
  obtain ⟨tm, htm, htmF, htmi⟩ := exists_first_hit J hFc hsub (u := -1) (by simp)
  simp only [mul_one, mul_neg] at htpF htpi htmF htmi
  have hpin : ∀ s : 𝕀, s ≠ 1 → rayP tp s ∈ inner F := fun s hs => by
    refine htpi _ ⟨?_, ?_⟩
    · have := mul_nonneg s.2.1 (by linarith : 0 ≤ tp - 1)
      linarith
    · have h1 : s.1 < 1 := lt_of_le_of_ne s.2.2 fun h => hs (Subtype.ext h)
      nlinarith
  have hmin : ∀ s : 𝕀, s ≠ 1 → rayM tm s ∈ inner F := fun s hs => by
    refine htmi _ ⟨?_, ?_⟩
    · have := mul_nonneg s.2.1 (by linarith : 0 ≤ tm - 1)
      linarith
    · have h1 : s.1 < 1 := lt_of_le_of_ne s.2.2 fun h => hs (Subtype.ext h)
      nlinarith
  have hup : ∀ s, upArc s ∈ inner F := fun s =>
    hsub (mem_closedBall_zero_iff.mpr (norm_upArc s).le)
  have hlo : ∀ s, loArc s ∈ inner F := fun s =>
    hsub (mem_closedBall_zero_iff.mpr (norm_loArc s).le)
  have hnF : ∀ {z : ℂ}, z ∈ F → ‖z‖ ≠ 1 := fun hz hn =>
    J.inner_subset_compl (hsub (mem_closedBall_zero_iff.mpr hn.le)) hz
  have hpF : ∀ s (z : ℂ), z ∈ F → rayP tp s = z → s = 1 := fun s z hz he => by
    by_contra hs
    exact J.inner_subset_compl (hpin s hs) (he ▸ hz)
  have hmF : ∀ s (z : ℂ), z ∈ F → rayM tm s = z → s = 1 := fun s z hz he => by
    by_contra hs
    exact J.inner_subset_compl (hmin s hs) (he ▸ hz)
  -- the three arcs of the chord
  let r : 𝕀 → ℂ := fun s => rayP tp (unitInterval.symm s)
  have hr : IsArcMap r := ⟨(isArcMap_rayP htp).1.comp unitInterval.continuous_symm,
    (isArcMap_rayP htp).2.comp unitInterval.symm_bijective.injective⟩
  have hrup : ∀ s t, r s = upArc t → s = 1 ∧ t = 0 := fun s t he => by
    have h1 : 1 + (unitInterval.symm s).1 * (tp - 1) = 1 := by
      rw [← norm_rayP htp, show rayP tp _ = r s from rfl, he, norm_upArc]
    have h2 := eq_zero_of_norm_eq htp h1
    have h3 : s = 1 := by
      have := congrArg unitInterval.symm h2
      simpa using this
    subst h3
    have h4 : r 1 = 1 := by simp [r]
    rw [h4] at he
    exact ⟨rfl, upArc_inj (he.symm.trans upArc_zero.symm)⟩
  obtain ⟨c₁, hc₁, hc₁r, hc₁0, hc₁1⟩ := exists_arc_join hr isArcMap_upArc (by simp [r]) hrup
  have hc₁m : ∀ s t, c₁ s = rayM tm t → s = 1 ∧ t = 0 := fun s t he => by
    have h1 : c₁ s ∈ range r ∪ range upArc := hc₁r ▸ ⟨s, rfl⟩
    rcases h1 with ⟨x, hx⟩ | ⟨x, hx⟩
    · exfalso
      have h2 := congrArg Complex.re (hx.trans he)
      simp only [r, rayP, rayM, Complex.ofReal_re, Complex.neg_re] at h2
      have h3 := mul_nonneg (unitInterval.symm x).2.1 (by linarith : 0 ≤ tp - 1)
      have h4 := mul_nonneg t.2.1 (by linarith : 0 ≤ tm - 1)
      linarith
    · have h1' : 1 + t.1 * (tm - 1) = 1 := by
        rw [← norm_rayM htm, ← he, ← hx, norm_upArc]
      have h2 := eq_zero_of_norm_eq htm h1'
      subst h2
      refine ⟨hc₁.2 ?_, rfl⟩
      rw [he, hc₁1]
      simp
  obtain ⟨e, he, her, he0, he1⟩ := exists_arc_join hc₁ (isArcMap_rayM htm) (by simp [hc₁1]) hc₁m
  have hrr : range r = range (rayP tp) := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨unitInterval.symm s, by simp [r]⟩
  have hrange_e : range e = range (rayP tp) ∪ range upArc ∪ range (rayM tm) := by
    rw [her, hc₁r, hrr]
  have he0' : e 0 = tp := by simp [he0, hc₁0, r]
  have he1' : e 1 = -(tm : ℂ) := by simp [he1]
  have hne : e 0 ≠ e 1 := by
    rw [he0', he1']
    intro h
    have h1 := congrArg Complex.re h
    simp at h1
    linarith
  have hin : ∀ t, t ≠ 0 → t ≠ 1 → e t ∈ inner F := by
    intro t h0 h1
    have hmem : e t ∈ range (rayP tp) ∪ range upArc ∪ range (rayM tm) := hrange_e ▸ ⟨t, rfl⟩
    rcases hmem with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
    · rw [← hs]
      refine hpin s fun h => h0 (he.2 ?_)
      rw [← hs, h, rayP_one, he0']
    · rw [← hs]
      exact hup s
    · rw [← hs]
      refine hmin s fun h => h1 (he.2 ?_)
      rw [← hs, h, rayM_one, he1']
  obtain ⟨a, b, c⟩ := exists_isCut φ he hne (he0' ▸ htpF) (he1' ▸ htmF) hin
  -- the lower half circle lies on one side
  let Lo : Set ℂ := (fun r : ℝ => cis' (-(Real.pi * r))) '' Ioo 0 1
  have hLoc : IsPreconnected Lo :=
    isPreconnected_Ioo.image _ (continuous_cis'.comp (by fun_prop)).continuousOn
  have hLolo : ∀ s : 𝕀, s ≠ 0 → s ≠ 1 → loArc s ∈ Lo := fun s h0 h1 =>
    ⟨s.1, ⟨lt_of_le_of_ne s.2.1 fun h => h0 (Subtype.ext h.symm),
      lt_of_le_of_ne s.2.2 fun h => h1 (Subtype.ext h)⟩, rfl⟩
  have hsinpos : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < Real.sin (Real.pi * r) := fun r hr =>
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hr.1) (by nlinarith [Real.pi_pos, hr.2])
  have hLoe : Disjoint Lo (range e) := Set.disjoint_left.mpr fun z hz hze => by
    obtain ⟨x, hx, rfl⟩ := hz
    have hs := hsinpos x hx
    have him : (cis' (-(Real.pi * x))).im < 0 := by
      rw [cis'_im, Real.sin_neg]
      linarith
    rw [hrange_e] at hze
    rcases hze with (⟨s, hs'⟩ | ⟨s, hs'⟩) | ⟨s, hs'⟩
    · replace hs' : rayP tp s = cis' (-(Real.pi * x)) := hs'
      rw [← hs'] at him
      simp [rayP] at him
    · replace hs' : upArc s = cis' (-(Real.pi * x)) := hs'
      rw [← hs', upArc, cis'_im] at him
      have := Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le s.2.1)
        (by nlinarith [s.2.2, Real.pi_pos] : Real.pi * s.1 ≤ Real.pi)
      linarith
    · replace hs' : rayM tm s = cis' (-(Real.pi * x)) := hs'
      rw [← hs'] at him
      simp [rayM] at him
  have hLoin : Lo ⊆ inner F \ range e := fun z hz => by
    refine ⟨?_, Set.disjoint_left.mp hLoe hz⟩
    obtain ⟨x, -, rfl⟩ := hz
    exact hsub (mem_closedBall_zero_iff.mpr (norm_cis' _).le)
  have T := c.isTheta J
  have hLosub : Lo ⊆ inner (side a e) ∪ inner (side b e) := by
    rw [← T.inner_sdiff]
    exact hLoin
  have hLone : Lo.Nonempty := ⟨_, 1 / 2, by norm_num, rfl⟩
  have hside : ∀ {a b : 𝕀 → ℂ}, IsCut F a b e → Lo ⊆ inner (side b e) →
      ∃ p m a b e b₂, AnnCut F p m a b e b₂ := by
    intro a b c hLo
    have hb₀ : b 0 = tp := by rw [c.b_zero, he0']
    have hb₁ : b 1 = -(tm : ℂ) := by rw [c.b_one, he1']
    have ha₀ : a 0 = tp := by rw [c.a_zero, he0']
    have ha₁ : a 1 = -(tm : ℂ) := by rw [c.a_one, he1']
    have qa : IsQuad upArc (rayP tp) (rayM tm) a := isQuad_of_halfCircle isArcMap_upArc c.arc_a
      norm_upArc upArc_zero upArc_one htp htm ha₀ ha₁ (fun t => hnF (c.a_mem t))
      (fun s t h => hpF s _ (c.a_mem t) h) fun s t h => hmF s _ (c.a_mem t) h
    have qb : IsQuad loArc (rayP tp) (rayM tm) b := isQuad_of_halfCircle isArcMap_loArc c.arc_b
      norm_loArc loArc_zero loArc_one htp htm hb₀ hb₁ (fun t => hnF (c.b_mem t))
      (fun s t h => hpF s _ (c.b_mem t) h) fun s t h => hmF s _ (c.b_mem t) h
    obtain ⟨j, hj, hjr, hj0, hj1⟩ := exists_arc_join (isArcMap_rayP htp) c.arc_b
      (by simp [hb₀]) qb.px
    let q : 𝕀 → ℂ := fun s => rayM tm (unitInterval.symm s)
    have hq : IsArcMap q := ⟨(isArcMap_rayM htm).1.comp unitInterval.continuous_symm,
      (isArcMap_rayM htm).2.comp unitInterval.symm_bijective.injective⟩
    have hqr : range q = range (rayM tm) := by
      ext z
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨unitInterval.symm s, by simp [q]⟩
    have hjq : ∀ s t, j s = q t → s = 1 ∧ t = 0 := fun s t hh => by
      have h1 : j s ∈ range (rayP tp) ∪ range b := hjr ▸ ⟨s, rfl⟩
      rcases h1 with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact absurd (hx.trans hh) (qb.pm x _)
      · have h2 := qb.mx (unitInterval.symm t) x (hh.symm.trans hx.symm)
        obtain ⟨h3, rfl⟩ := h2
        have h4 : t = 0 := by
          have := congrArg unitInterval.symm h3
          simpa using this
        refine ⟨hj.2 ?_, h4⟩
        rw [← hx, hj1]
    obtain ⟨b₂, hb₂, hb₂r, hb₂0, hb₂1⟩ := exists_arc_join hj hq (by simp [hj1, q, hb₁]) hjq
    have hb₂rr : range b₂ = range (rayP tp) ∪ range b ∪ range (rayM tm) := by
      rw [hb₂r, hjr, hqr]
    have hb₂0' : b₂ 0 = 1 := by simp [hb₂0, hj0]
    have hb₂1' : b₂ 1 = -1 := by simp [hb₂1, q]
    have hcut₂ : IsCut (side b e) upArc b₂ loArc := by
      refine ⟨isArcMap_upArc, hb₂, isArcMap_loArc, by simp, by simp, by simp [hb₂0'],
        by simp [hb₂1'], by simp; norm_num, ?_, ?_, ?_⟩
      · rw [side, hb₂rr, hrange_e]
        ext z
        simp only [mem_union]
        tauto
      · intro s t hh
        have h1 : b₂ t ∈ range (rayP tp) ∪ range b ∪ range (rayM tm) := hb₂rr ▸ ⟨t, rfl⟩
        rcases h1 with (⟨x, hx⟩ | ⟨x, hx⟩) | ⟨x, hx⟩
        · obtain ⟨h2, rfl⟩ := qa.up s x (hh.trans hx.symm)
          refine .inl ⟨h2, hb₂.2 ?_⟩
          rw [← hx, hb₂0']
          simp
        · exact absurd (by rw [hx, ← hh, norm_upArc]) (hnF (c.b_mem x))
        · obtain ⟨h2, rfl⟩ := qa.um s x (hh.trans hx.symm)
          refine .inr ⟨h2, hb₂.2 ?_⟩
          rw [← hx, hb₂1']
          simp
      · intro t h0 h1
        exact hLo (hLolo t h0 h1)
    exact ⟨_, _, a, b, e, b₂, qa, qb, c, hrange_e, hcut₂, hb₂rr⟩
  rcases hLoc.subset_or_subset T.parts₁.isOpen_inner T.parts₂.isOpen_inner T.disjoint_inner hLosub
    with h | h
  · exact hside c.symm h
  · exact hside c h

theorem closedInner_sphere_two :
    Nonempty (Circle ≃ₜ sphere (0 : ℂ) 2) ∧ closedInner (sphere (0 : ℂ) 2) = closedBall 0 2 := by
  have hd := isClosedDisc_of_convex (K := closedBall (0 : ℂ) 2) (convex_closedBall 0 2)
    (by rw [interior_closedBall _ (by norm_num)]; exact ⟨0, by simp⟩) isBounded_closedBall
    isClosed_closedBall
  rw [frontier_closedBall _ (by norm_num)] at hd
  have h1 : Nonempty (Circle ≃ₜ sphere (0 : ℂ) 2) := by
    have := hd.1.isOArc_discBd
    rwa [hd.2] at this
  exact ⟨h1, (eq_closedInner_of_discBd h1 hd.1 hd.2).symm⟩

/-- **The annulus theorem in the plane.** See the module docstring. -/
theorem exists_annulus {F : Set ℂ} (φ : Circle ≃ₜ F) (hsub : closedBall (0 : ℂ) 1 ⊆ inner F) :
    ∃ Θ Θ' : ℂ → ℂ, BdMatch (closedBall 0 2) (closedInner F) Θ Θ' ∧
      EqOn Θ id (closedBall 0 1) ∧ Θ '' sphere 0 2 = F := by
  obtain ⟨hF₀, hcl₀⟩ := closedInner_sphere_two
  obtain ⟨φ₀⟩ := id hF₀
  have hsub₀ : closedBall (0 : ℂ) 1 ⊆ inner (sphere 0 2) := by
    have h1 : inner (sphere (0 : ℂ) 2) = closedInner (sphere (0 : ℂ) 2) \ sphere 0 2 := by
      have := (isJordanParts φ₀).inner_subset_compl
      ext z
      constructor
      · exact fun hz => ⟨.inl hz, this hz⟩
      · rintro ⟨hz | hz, h2⟩
        · exact hz
        · exact absurd hz h2
    rw [h1, hcl₀]
    intro z hz
    have h2 := mem_closedBall_zero_iff.mp hz
    refine ⟨closedBall_subset_closedBall (by norm_num) hz, fun h3 => ?_⟩
    rw [mem_sphere_zero_iff_norm] at h3
    linarith
  obtain ⟨p, m, a, b, e, b₂, A⟩ := exists_annCut φ hsub
  obtain ⟨p₀, m₀, a₀, b₀, e₀, b₂₀, A₀⟩ := exists_annCut φ₀ hsub₀
  have J := isJordanParts φ
  have J₀ := isJordanParts φ₀
  -- sides
  have hsa : side a e = quadSet upArc p m a := by
    rw [side, A.range_e, quadSet]
    ext z
    simp only [mem_union]
    tauto
  have hsa₀ : side a₀ e₀ = quadSet upArc p₀ m₀ a₀ := by
    rw [side, A₀.range_e, quadSet]
    ext z
    simp only [mem_union]
    tauto
  have hsb : side b₂ loArc = quadSet loArc p m b := by
    rw [side, A.range_b, quadSet]
    ext z
    simp only [mem_union]
    tauto
  have hsb₀ : side b₂₀ loArc = quadSet loArc p₀ m₀ b₀ := by
    rw [side, A₀.range_b, quadSet]
    ext z
    simp only [mem_union]
    tauto
  have hsu : side upArc loArc = sphere 0 1 := range_upArc_union
  -- the part below
  obtain ⟨h₂, k₂, m₂, hu₂, hp₂, hm₂, hx₂⟩ := exists_bdMatch_of_quads A₀.qb A.qb
  have ho₂₀ : Nonempty (Circle ≃ₜ quadSet loArc p₀ m₀ b₀) := hsb₀ ▸ A₀.cut₂.symm.oArc_side
  have ho₂ : Nonempty (Circle ≃ₜ quadSet loArc p m b) := hsb ▸ A.cut₂.symm.oArc_side
  obtain ⟨ψ₂, χ₂, n₂, he₂⟩ := exists_bdMatch_closedInner ho₂₀ ho₂ m₂
  -- the part above
  obtain ⟨h₁, k₁, m₁, hu₁, hp₁, hm₁, hx₁⟩ := exists_bdMatch_of_quads A₀.qa A.qa
  have ho₁₀ : Nonempty (Circle ≃ₜ quadSet upArc p₀ m₀ a₀) := hsa₀ ▸ A₀.cut.oArc_side
  have ho₁ : Nonempty (Circle ≃ₜ quadSet upArc p m a) := hsa ▸ A.cut.oArc_side
  obtain ⟨ψ₁, χ₁, n₁, he₁⟩ := exists_bdMatch_closedInner ho₁₀ ho₁ m₁
  have hJ₂ : IsJordanParts (side b e) := by
    obtain ⟨φ'⟩ := A.cut.symm.oArc_side
    exact isJordanParts φ'
  have hJ₂₀ : IsJordanParts (side b₀ e₀) := by
    obtain ⟨φ'⟩ := A₀.cut.symm.oArc_side
    exact isJordanParts φ'
  have hbm : BdMatch (closedBall 0 1) (closedBall 0 1) id id :=
    ⟨mapsTo_id _, mapsTo_id _, fun _ _ => rfl, fun _ _ => rfl, continuousOn_id, continuousOn_id⟩
  have hid : BdMatch (closedInner (side upArc loArc)) (closedInner (side upArc loArc)) id id := by
    rw [hsu, closedInner_sphere]
    exact hbm
  have hlo₂ : ∀ s, loArc s ∈ quadSet loArc p₀ m₀ b₀ := fun s => .inl (.inl (.inl ⟨s, rfl⟩))
  have hψ₂lo : ∀ s, ψ₂ (loArc s) = loArc s := fun s => by rw [he₂ (hlo₂ s), hu₂]
  obtain ⟨Θ₃, Θ₃', n₃, hΘ₃a, hΘ₃b⟩ := paste_cut A₀.cut₂ A.cut₂ hJ₂₀ hJ₂ hid
    (by rw [hsb₀, hsb]; exact n₂)
    (by
      rintro _ ⟨s, rfl⟩
      exact (hψ₂lo s).symm)
    (by simp)
  have hsubin : ∀ {G : Set ℂ}, G ⊆ closedInner G := fun h => Or.inr h
  have hz₁ : ∀ z ∈ closedBall (0 : ℂ) 1, Θ₃ z = z := fun z hz => by
    have : z ∈ closedInner (side upArc loArc) := by
      rw [hsu, closedInner_sphere]
      exact hz
    exact hΘ₃a this
  have hp₃ : ∀ s, Θ₃ (p₀ s) = p s := fun s => by
    have h1 : p₀ s ∈ quadSet loArc p₀ m₀ b₀ := .inl (.inl (.inr ⟨s, rfl⟩))
    have h2 : p₀ s ∈ closedInner (side b₂₀ loArc) := by
      rw [hsb₀]
      exact hsubin h1
    rw [hΘ₃b h2, he₂ h1, hp₂]
  have hm₃ : ∀ s, Θ₃ (m₀ s) = m s := fun s => by
    have h1 : m₀ s ∈ quadSet loArc p₀ m₀ b₀ := .inl (.inr ⟨s, rfl⟩)
    have h2 : m₀ s ∈ closedInner (side b₂₀ loArc) := by
      rw [hsb₀]
      exact hsubin h1
    rw [hΘ₃b h2, he₂ h1, hm₂]
  have hb₃ : ∀ s, Θ₃ (b₀ s) = b s := fun s => by
    have h1 : b₀ s ∈ quadSet loArc p₀ m₀ b₀ := .inr ⟨s, rfl⟩
    have h2 : b₀ s ∈ closedInner (side b₂₀ loArc) := by
      rw [hsb₀]
      exact hsubin h1
    rw [hΘ₃b h2, he₂ h1, hx₂]
  have hq₁ : ∀ {z}, z ∈ range e₀ → z ∈ quadSet upArc p₀ m₀ a₀ := fun hz => by
    rw [← hsa₀]
    exact .inr hz
  obtain ⟨Θ, Θ', n, hΘa, hΘb⟩ := paste_cut A₀.cut A.cut J₀ J
    (by rw [hsa₀, hsa]; exact n₁) n₃
    (by
      intro z hz
      rw [A₀.range_e] at hz
      rw [he₁ (hq₁ (A₀.range_e ▸ hz))]
      rcases hz with (⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩
      · rw [hp₁, hp₃]
      · rw [hu₁, hz₁ _ (mem_closedBall_zero_iff.mpr (norm_upArc s).le)]
      · rw [hm₁, hm₃])
    (by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [he₁ (hq₁ hz), A.range_e]
        rw [A₀.range_e] at hz
        rcases hz with (⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩
        · rw [hp₁]
          exact .inl (.inl ⟨s, rfl⟩)
        · rw [hu₁]
          exact .inl (.inr ⟨s, rfl⟩)
        · rw [hm₁]
          exact .inr ⟨s, rfl⟩
      · intro hw
        rw [A.range_e] at hw
        rcases hw with (⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩
        · have h1 : p₀ s ∈ range e₀ := by
            rw [A₀.range_e]
            exact .inl (.inl ⟨s, rfl⟩)
          exact ⟨_, h1, by rw [he₁ (hq₁ h1), hp₁]⟩
        · have h1 : upArc s ∈ range e₀ := by
            rw [A₀.range_e]
            exact .inl (.inr ⟨s, rfl⟩)
          exact ⟨_, h1, by rw [he₁ (hq₁ h1), hu₁]⟩
        · have h1 : m₀ s ∈ range e₀ := by
            rw [A₀.range_e]
            exact .inr ⟨s, rfl⟩
          exact ⟨_, h1, by rw [he₁ (hq₁ h1), hm₁]⟩)
  rw [hcl₀] at n
  have hbin : ∀ z ∈ closedInner (side b₂₀ loArc) ∪ closedInner (side upArc loArc),
      z ∈ closedInner (side b₀ e₀) := fun z hz => by
    have := (A₀.cut₂.closedInner_facts hJ₂₀).1
    rw [← this, union_comm]
    exact hz
  refine ⟨Θ, Θ', n, fun z hz => ?_, ?_⟩
  · have h1 : z ∈ closedInner (side upArc loArc) := by
      rw [hsu, closedInner_sphere]
      exact hz
    rw [hΘb (hbin z (.inr h1)), hz₁ z hz]
    rfl
  · have ha₀ : ∀ s, Θ (a₀ s) = a s := fun s => by
      have h1 : a₀ s ∈ quadSet upArc p₀ m₀ a₀ := .inr ⟨s, rfl⟩
      have h2 : a₀ s ∈ closedInner (side a₀ e₀) := by
        rw [hsa₀]
        exact hsubin h1
      rw [hΘa h2, he₁ h1, hx₁]
    have hb₀ : ∀ s, Θ (b₀ s) = b s := fun s => by
      have h2 : b₀ s ∈ closedInner (side b₀ e₀) := hsubin (Or.inl ⟨s, rfl⟩)
      rw [hΘb h2, hb₃]
    rw [← A₀.cut.union, ← A.cut.union, image_union]
    congr 1
    · ext w
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨s, (ha₀ s).symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨_, ⟨s, rfl⟩, ha₀ s⟩
    · ext w
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨s, (hb₀ s).symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨_, ⟨s, rfl⟩, hb₀ s⟩

end GraphMinor.Surface
