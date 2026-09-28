/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Motion.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Sofa.Support`.
* `Sofa.Cap`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Sofa / Support
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem standardPosition_subset_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : s ⊆ monotonization s ω := by
  have hω : ω ∈ Set.Ioc 0 (Real.pi / 2) := ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hcommon := movingSofa_commonSubset s ω hs.2.1 hω
  have hs_ne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs.2.1
    exact hm.1.nonempty
  have hshape : s ⊆ (stripParallelogram ω).1 := by
    have htranslated :=
      (exists_standardPosition_translation s ω hs.2.1 hω).2.2.2 (0 : Point)
    have hstandard :
        IsStandardPosition ((fun p : Point ↦ p + (0 : Point)) '' s) ω := by
      simpa using hs
    simpa using htranslated hstandard
  rw [monotonization]
  intro p hp
  refine ⟨hshape hp, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  exact subset_supportingHallway s (t : Real.Angle) hs_ne hcommon.1
    (hcommon.2.2.2.1 t ht) hp

theorem standardPosition_subset_cap (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    s ⊆ monotonization s ω ∧ monotonization s ω ⊆ capOfSofa s ω := by
  refine ⟨standardPosition_subset_monotonization s ω hs, ?_⟩
  rw [monotonization, capOfSofa]
  rintro p ⟨hpP, hpL⟩
  refine ⟨hpP, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  apply supportingHallway_subset_outerQuadrant s (t : Real.Angle)
  exact Set.mem_iInter.1 (Set.mem_iInter.1 hpL t) ht

private theorem inner_le_supportValue_of_mem_capOfSofa {s : Set Point} {ω t : ℝ}
    (ht : t ∈ capUpperAngles ω) {p : Point} (hp : p ∈ capOfSofa s ω) :
    inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue s (t : Real.Angle) := by
  rcases ht with ht | ht
  · have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
    obtain ⟨q, hq, rfl⟩ := hq
    rw [inner_supportingPlacement_normalVector]
    change q 0 ≤ 1 ∧ q 1 ≤ 1 at hq
    linarith [hq.1]
  · have ht' : t - Real.pi / 2 ∈ Set.Icc 0 ω := by
      constructor <;> linarith [ht.1, ht.2]
    have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 (t - Real.pi / 2)) ht'
    obtain ⟨q, hq, rfl⟩ := hq
    have ha : (t : Real.Angle) = ((t - Real.pi / 2 : ℝ) : Real.Angle) +
        ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_add, sub_add_cancel]
    rw [ha, normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    change q 0 ≤ 1 ∧ q 1 ≤ 1 at hq
    linarith [hq.2]

theorem standardPosition_support_eq (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    (∀ t ∈ capUpperAngles ω,
      supportValue (monotonization s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) ∧
      supportValue (capOfSofa s ω) (t : Real.Angle) = supportValue s (t : Real.Angle)) ∧
    (∀ t ∈ Set.Icc 0 ω,
      supportingHallway (monotonization s ω) (t : Real.Angle) =
        supportingHallway s (t : Real.Angle) ∧
      supportingHallway (capOfSofa s ω) (t : Real.Angle) =
        supportingHallway s (t : Real.Angle)) := by
  have hs_ne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hnorm := hs.2.2.2.2.1
    simp [he, supportValue] at hnorm
  obtain ⟨hsm, hmc⟩ := standardPosition_subset_cap s ω hs
  have hsupport (t : ℝ) (ht : t ∈ capUpperAngles ω) :
      supportValue (monotonization s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) ∧
      supportValue (capOfSofa s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) := by
    have hc (p : Point) (hp : p ∈ capOfSofa s ω) :=
      inner_le_supportValue_of_mem_capOfSofa ht hp
    exact ⟨supportValue_eq_of_subset_of_inner_le hs_ne hsm _ (fun p hp ↦ hc p (hmc hp)),
      supportValue_eq_of_subset_of_inner_le hs_ne (hsm.trans hmc) _ hc⟩
  refine ⟨hsupport, ?_⟩
  intro t ht
  have ht' : t + Real.pi / 2 ∈ capUpperAngles ω :=
    Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h₀ := hsupport t (Or.inl ht)
  have h₁ := hsupport (t + Real.pi / 2) ht'
  simp only [Real.Angle.coe_add] at h₁
  constructor
  · unfold supportingHallway
    congr 1
    funext p
    simp only [supportingPlacement, h₀.1, h₁.1]
  · unfold supportingHallway
    congr 1
    funext p
    simp only [supportingPlacement, h₀.2, h₁.2]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Sofa / Cap
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem capOfSofa_halfPlaneRepresentation (s : Set Point) (ω : ℝ) (hω : 0 ≤ ω) :
    HasHalfPlaneRepresentation (capOfSofa s ω)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪ capLowerNormals ω) := by
  let U : Set (Real.Angle × ℝ) :=
    (fun t : ℝ ↦ ((t : Real.Angle), supportValue s (t : Real.Angle))) '' capUpperAngles ω
  let B : Set (Real.Angle × ℝ) :=
    {(((ω : ℝ) : Real.Angle), 1),
      (((Real.pi / 2 : ℝ) : Real.Angle), 1),
      (((ω + Real.pi : ℝ) : Real.Angle), 0),
      (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)}
  refine ⟨U ∪ B, ?_, ?_⟩
  · rintro c (hc | hc)
    · obtain ⟨t, ht, rfl⟩ := hc
      exact Or.inl ⟨t, ht, rfl⟩
    · rcases hc with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨ω, Or.inl ⟨hω, le_rfl⟩, rfl⟩
      · exact Or.inl ⟨Real.pi / 2, Or.inr ⟨le_rfl, le_add_of_nonneg_left hω⟩, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · ext p
    simp only [Set.mem_iInter]
    constructor
    · intro hp c hc
      rcases hc with hc | hc
      · obtain ⟨φ, hφ, rfl⟩ := hc
        change inner ℝ p (normalVector (φ : Real.Angle)) ≤ supportValue s _
        rcases hφ with hφ | hφ
        · have hout := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 φ) hφ
          rw [(rotatingHallwayParts_formulas s (φ : Real.Angle)).2.2.2.2.2.2.2.1]
            at hout
          exact hout.1
        · let t := φ - Real.pi / 2
          have ht : t ∈ Set.Icc 0 ω := by
            constructor <;> dsimp [t] <;> linarith [hφ.1, hφ.2]
          have hout := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
          rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
            at hout
          have hang : ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) =
              (φ : Real.Angle) := by
            rw [← Real.Angle.coe_add]
            congr 1
            dsimp [t]
            ring
          have hout' := hout.2
          change inner ℝ p (normalVector ((t : Real.Angle) +
            ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _ at hout'
          simpa [hang] using hout'
      · rcases hc with rfl | rfl | rfl | rfl
        · exact ((mem_stripParallelogram_iff ω p).1 hp.1).2.2
        · simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply,
            Fin.sum_univ_two] using ((mem_stripParallelogram_iff ω p).1 hp.1).1.2
        · change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤ 0
          rw [normalVector_add_pi, inner_neg_right]
          exact neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp.1).2.1
        · simpa [normalHalfPlane, inner_normalVector_three_pi_div_two] using
            neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp.1).1.1
    · intro hp
      have hupper (φ : ℝ) (hφ : φ ∈ capUpperAngles ω) :
          inner ℝ p (normalVector (φ : Real.Angle)) ≤ supportValue s (φ : Real.Angle) :=
        hp ((φ : Real.Angle), supportValue s (φ : Real.Angle))
          (Or.inl ⟨φ, hφ, rfl⟩)
      have hω' := hp (((ω : ℝ) : Real.Angle), 1) (Or.inr (Or.inl rfl))
      have hπ := hp (((Real.pi / 2 : ℝ) : Real.Angle), 1)
        (Or.inr (Or.inr (Or.inl rfl)))
      have hlowerω := hp (((ω + Real.pi : ℝ) : Real.Angle), 0)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have hlowerπ := hp (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      refine ⟨(mem_stripParallelogram_iff ω p).2 ?_, ?_⟩
      · change inner ℝ p (normalVector (ω : Real.Angle)) ≤ 1 at hω'
        change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 at hπ
        change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤ 0 at hlowerω
        change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0 at hlowerπ
        rw [normalVector_add_pi, inner_neg_right] at hlowerω
        rw [inner_normalVector_three_pi_div_two] at hlowerπ
        have hπ' : p 1 ≤ 1 := by
          simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hπ
        exact ⟨⟨by linarith, hπ'⟩, by linarith, hω'⟩
      · refine Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_
        rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
        refine ⟨hupper t (Or.inl ht), ?_⟩
        have hshift : t + Real.pi / 2 ∈ capUpperAngles ω :=
          Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        change inner ℝ p (normalVector ((t : Real.Angle) +
          ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _
        simpa only [Real.Angle.coe_add] using hupper (t + Real.pi / 2) hshift

private theorem isBounded_capOfSofa (s : Set Point) (ω : ℝ)
    (hω : 0 < ω) (hωπ : ω ≤ Real.pi / 2) : Bornology.IsBounded (capOfSofa s ω) := by
  let t := ω / 2
  let A := supportValue s (t : Real.Angle)
  let B := supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle)
  have ht : t ∈ Set.Icc 0 ω := by
    constructor <;> dsimp [t] <;> linarith
  have htI : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> dsimp [t] <;> linarith [Real.pi_pos]
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo htI
  have hsine : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (by dsimp [t]; linarith)
    (by dsimp [t]; linarith [Real.pi_pos])
  refine (isBounded_iff_forall_norm_le).2 ⟨|A / Real.cos t| +
    |B / Real.sin t| + 1, ?_⟩
  intro p hp
  have hstrip := (mem_stripParallelogram_iff ω p).1 hp.1
  have hout := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
  rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
    at hout
  have h₀ := hout.1
  have h₁ := hout.2
  change inner ℝ p (normalVector (t : Real.Angle)) ≤ A at h₀
  change inner ℝ p (normalVector ((t : Real.Angle) +
    ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ B at h₁
  rw [normalVector_add_pi_div_two] at h₁
  simp only [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.inner_apply, Real.Angle.cos_coe, Real.Angle.sin_coe, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h₀ h₁
  have hxhi : p 0 ≤ A / Real.cos t := (le_div_iff₀ hc).2 (by
    have := mul_nonneg hstrip.1.1 hsine.le
    nlinarith)
  have hxlo : -(B / Real.sin t) ≤ p 0 := by
    rw [← neg_div]
    apply (div_le_iff₀ hsine).2
    have := mul_nonneg hstrip.1.1 hc.le
    nlinarith
  have hxabs : |p 0| ≤ |A / Real.cos t| + |B / Real.sin t| := by
    rw [abs_le]
    constructor
    · calc
        -(|A / Real.cos t| + |B / Real.sin t|) ≤ -(B / Real.sin t) := by
          have hA := abs_nonneg (A / Real.cos t)
          have hB := le_abs_self (B / Real.sin t)
          linarith
        _ ≤ p 0 := hxlo
    · calc
        p 0 ≤ A / Real.cos t := hxhi
        _ ≤ |A / Real.cos t| + |B / Real.sin t| := by
          have hA := le_abs_self (A / Real.cos t)
          have hB := abs_nonneg (B / Real.sin t)
          linarith
  have hyabs : |p 1| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hstrip.1.1], hstrip.1.2⟩
  have hpdecomp : p = p 0 • (!₂[1, 0] : Point) + p 1 • !₂[0, 1] := by
    ext i
    fin_cases i <;> simp
  have he₀ : ‖(!₂[1, 0] : Point)‖ = 1 := by
    have h : (!₂[1, 0] : Point) = normalVector (0 : Real.Angle) := by
      ext i
      fin_cases i <;> simp [normalVector, frame]
    rw [h]
    exact norm_normalVector_real 0
  have he₁ : ‖(!₂[0, 1] : Point)‖ = 1 := by
    have h : (!₂[0, 1] : Point) = normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
      ext i
      fin_cases i <;> simp [normalVector, frame]
    rw [h]
    exact norm_normalVector_real (Real.pi / 2)
  rw [hpdecomp]
  calc
    ‖p 0 • (!₂[1, 0] : Point) + p 1 • !₂[0, 1]‖ ≤
        ‖p 0 • (!₂[1, 0] : Point)‖ + ‖p 1 • (!₂[0, 1] : Point)‖ := norm_add_le _ _
    _ = |p 0| + |p 1| := by simp [norm_smul, he₀, he₁]
    _ ≤ |A / Real.cos t| + |B / Real.sin t| + 1 := add_le_add hxabs hyabs

private theorem mem_capOfSofa_of_mem_strip_of_upper {s : Set Point} {ω : ℝ} {p : Point}
    (hp : p ∈ (stripParallelogram ω).1)
    (hupper : ∀ t ∈ capUpperAngles ω,
      inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue s (t : Real.Angle)) :
    p ∈ capOfSofa s ω := by
  refine ⟨hp, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
  refine ⟨hupper t (Or.inl ht), ?_⟩
  have hshift : t + Real.pi / 2 ∈ capUpperAngles ω :=
    Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  change inner ℝ p (normalVector ((t : Real.Angle) +
    ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _
  simpa only [Real.Angle.coe_add] using hupper (t + Real.pi / 2) hshift

private theorem supportValue_eq_zero_of_nonpos_of_attains_zero (K : ConvexBody Point)
    (a : Real.Angle) (hupper : ∀ p ∈ K, inner ℝ p (normalVector a) ≤ 0)
    {q : Point} (hq : q ∈ K) (hqzero : inner ℝ q (normalVector a) = 0) :
    supportValue K a = 0 := by
  apply le_antisymm
  · exact supportValue_le_of_subset_normalHalfPlane K a 0 hupper
  · simpa only [hqzero] using inner_le_supportValue K hq a

private theorem standardPosition_right_cap_lower_support (s : Set Point)
    (hs : IsStandardPosition s (Real.pi / 2)) (K : ConvexBody Point)
    (hK : (K : Set Point) = capOfSofa s (Real.pi / 2))
    (hs_ne : s.Nonempty) :
    supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨p, hp, hpeq⟩ := (hs.1.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (hs_ne.image
        (fun p ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
  have hpT : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue s _ at hpeq
    simpa only [hs.2.2.2.2.2] using hpeq
  let q := p - tangentVector (0 : Real.Angle)
  have hqy : q 1 = 0 := by
    have hpcoord : p 1 = 1 := by
      simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hpT
    simp [q, tangentVector, frame, hpcoord]
  have hqP : q ∈ (stripParallelogram (Real.pi / 2)).1 := by
    rw [mem_stripParallelogram_iff]
    have hqn : inner ℝ q
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
      simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hqy
    exact ⟨⟨by rw [hqy], by rw [hqy]; norm_num⟩,
      by rw [hqn], by rw [hqn]; norm_num⟩
  have hq : q ∈ capOfSofa s (Real.pi / 2) := by
    apply mem_capOfSofa_of_mem_strip_of_upper hqP
    intro u hu
    have hsu : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi
      (by rcases hu with hu | hu <;> linarith [hu.1])
      (by rcases hu with hu | hu <;> linarith [hu.2, Real.pi_pos])
    calc
      inner ℝ q (normalVector (u : Real.Angle)) =
          inner ℝ p (normalVector (u : Real.Angle)) - Real.sin u := by
            simp [q, tangentVector, normalVector, frame, PiLp.inner_apply,
              Fin.sum_univ_two]
            ring
      _ ≤ inner ℝ p (normalVector (u : Real.Angle)) := sub_le_self _ hsu
      _ ≤ supportValue s (u : Real.Angle) :=
        inner_le_supportValue_of_isCompact hs.1 hp _
  apply supportValue_eq_zero_of_nonpos_of_attains_zero K
  · intro z hz
    change z ∈ (K : Set Point) at hz
    rw [hK] at hz
    have hz0 := ((mem_stripParallelogram_iff (Real.pi / 2) z).1 hz.1).1.1
    simpa [inner_normalVector_three_pi_div_two] using neg_nonpos.mpr hz0
  · exact hK.symm ▸ hq
  · simpa [inner_normalVector_three_pi_div_two] using congrArg Neg.neg hqy

theorem standardPosition_cap (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    ∃ K : CapSpace ω, (K.val : Set Point) = capOfSofa s ω := by
  have hs_ne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs.2.1
    exact hm.1.nonempty
  have hω0 : 0 ≤ ω := hs.2.2.1.le
  obtain ⟨D, hDN, hC⟩ := capOfSofa_halfPlaneRepresentation s ω hω0
  have hclosed : IsClosed (capOfSofa s ω) := by
    rw [hC]
    exact isClosed_iInter fun c ↦ isClosed_iInter fun _ ↦
      isClosed_normalHalfPlane c.1 c.2 false
  have hconvex : Convex ℝ (capOfSofa s ω) := by
    rw [hC]
    exact convex_iInter fun c ↦ convex_iInter fun _ ↦
      convex_normalHalfPlane c.1 c.2 false
  have hscap : s ⊆ capOfSofa s ω :=
    let h := standardPosition_subset_cap s ω hs
    h.1.trans h.2
  have hne : (capOfSofa s ω).Nonempty := hs_ne.mono hscap
  let K : ConvexBody Point := {
    carrier := capOfSofa s ω
    convex' := hconvex
    isCompact' := Metric.isCompact_iff_isClosed_bounded.2
      ⟨hclosed, isBounded_capOfSofa s ω hs.2.2.1 hs.2.2.2.1⟩
    nonempty' := hne }
  have hsupport := (standardPosition_support_eq s ω hs).1
  have hKω : supportValue K (ω : Real.Angle) = 1 := by
    change supportValue (capOfSofa s ω) (ω : Real.Angle) = 1
    rw [(hsupport ω (Or.inl ⟨hω0, le_rfl⟩)).2, hs.2.2.2.2.1]
  have hKπ : supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    change supportValue (capOfSofa s ω) ((Real.pi / 2 : ℝ) : Real.Angle) = 1
    rw [(hsupport (Real.pi / 2) (Or.inr ⟨le_rfl,
      le_add_of_nonneg_left hω0⟩)).2, hs.2.2.2.2.2]
  by_cases hright : ω = Real.pi / 2
  · subst ω
    have hbottom := standardPosition_right_cap_lower_support s hs K rfl hs_ne
    have hsame : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    refine ⟨⟨K, hs.2.2.1, hs.2.2.2.1, hKω, hKπ, ?_, hbottom,
      ⟨D, hDN, ?_⟩⟩, rfl⟩
    · simpa [hsame] using hbottom
    · exact hC
  · have hlt : ω < Real.pi / 2 := lt_of_le_of_ne hs.2.2.2.1 hright
    let o := (stripParallelogram ω).2.2
    have hc : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hs.2.2.1, Real.pi_pos], hlt⟩
    obtain ⟨pω, hpω, hpωeq⟩ := (hs.1.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
        (hs_ne.image (fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))))
    obtain ⟨pT, hpT, hpTeq⟩ := (hs.1.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
        (hs_ne.image
          (fun p ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
    have hpω' : inner ℝ pω (normalVector (ω : Real.Angle)) = 1 := by
      change inner ℝ pω (normalVector (ω : Real.Angle)) = supportValue s _ at hpωeq
      simpa only [hs.2.2.2.2.1] using hpωeq
    have hpT' : inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
      change inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue s _ at hpTeq
      simpa only [hs.2.2.2.2.2] using hpTeq
    have hpωT : inner ℝ pω (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
      simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using
        ((mem_stripParallelogram_iff ω pω).1 (hscap hpω).1).1.2
    have hpTω : inner ℝ pT (normalVector (ω : Real.Angle)) ≤ 1 :=
      ((mem_stripParallelogram_iff ω pT).1
        (hscap hpT).1).2.2
    have hoω : inner ℝ o (normalVector (ω : Real.Angle)) = 1 := by
      have hgap : Real.tan (Real.pi / 4 - ω / 2) =
          (Real.cos ω)⁻¹ - Real.tan ω := by
        simpa [show Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 by ring]
          using Real.tan_pi_div_two_sub_div_two ω ⟨hω0, hlt⟩
      have htan := Real.tan_eq_sin_div_cos ω
      simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
      field_simp [hc.ne']
      ring
    have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
      simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
    have hou (u : ℝ) (hu : u ∈ capUpperAngles ω) :
        inner ℝ o (normalVector (u : Real.Angle)) ≤ supportValue s (u : Real.Angle) := by
      rcases hu with hu | hu
      · let c := Real.cos u / Real.cos ω
        let d := Real.sin (ω - u) / Real.cos ω
        have hd0 : 0 ≤ d := div_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hu.2)
            (by linarith [hu.1, hs.2.2.2.1, Real.pi_pos])) hc.le
        have hdecomp : normalVector (u : Real.Angle) =
            c • normalVector (ω : Real.Angle) -
              d • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
          ext i
          fin_cases i
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
            ring
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoω, hoT]
        apply (inner_le_supportValue_of_isCompact hs.1 hpω (u : Real.Angle)).trans'
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpω']
        simpa only [mul_one] using
          sub_le_sub_left (mul_le_mul_of_nonneg_left hpωT hd0) c
      · let c := Real.sin (u - ω) / Real.cos ω
        let d := -Real.cos u / Real.cos ω
        have hd0 : 0 ≤ d := div_nonneg
          (neg_nonneg.mpr (Real.cos_nonpos_of_pi_div_two_le_of_le hu.1
            (by linarith [hu.2, hs.2.2.2.1, Real.pi_pos]))) hc.le
        have hdecomp : normalVector (u : Real.Angle) =
            c • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) -
              d • normalVector (ω : Real.Angle) := by
          ext i
          fin_cases i
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
            ring
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoT, hoω]
        apply (inner_le_supportValue_of_isCompact hs.1 hpT (u : Real.Angle)).trans'
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpT']
        simpa only [mul_one] using
          sub_le_sub_left (mul_le_mul_of_nonneg_left hpTω hd0) c
    let q₀ := o - tangentVector (0 : Real.Angle)
    have hsinω0 : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω0
      (by linarith [hs.2.2.2.1, Real.pi_pos])
    have hsinω1 : Real.sin ω ≤ 1 := Real.sin_le_one ω
    have hq₀P : q₀ ∈ (stripParallelogram ω).1 := by
      rw [mem_stripParallelogram_iff]
      have hq₀y : q₀ 1 = 0 := by
        simp [q₀, o, stripParallelogram, tangentVector, frame]
      have hq₀n : inner ℝ q₀ (normalVector (ω : Real.Angle)) = 1 - Real.sin ω := by
        rw [inner_sub_left, hoω]
        simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      exact ⟨⟨by rw [hq₀y], by rw [hq₀y]; norm_num⟩,
        by rw [hq₀n]; exact sub_nonneg.mpr hsinω1,
        by rw [hq₀n]; linarith⟩
    have hq₀ : q₀ ∈ capOfSofa s ω := by
      apply mem_capOfSofa_of_mem_strip_of_upper hq₀P
      intro u hu
      have hsu : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi
        (by rcases hu with hu | hu <;> linarith [hu.1])
        (by rcases hu with hu | hu <;> linarith [hu.2, hs.2.2.2.1])
      calc
        inner ℝ q₀ (normalVector (u : Real.Angle)) =
            inner ℝ o (normalVector (u : Real.Angle)) - Real.sin u := by
              simp [q₀, tangentVector, normalVector, frame, PiLp.inner_apply,
                Fin.sum_univ_two]
              ring
        _ ≤ inner ℝ o (normalVector (u : Real.Angle)) := sub_le_self _ hsu
        _ ≤ supportValue s (u : Real.Angle) := hou u hu
    let qω := o - normalVector (ω : Real.Angle)
    have hqωP : qω ∈ (stripParallelogram ω).1 := by
      rw [mem_stripParallelogram_iff]
      have hqωn : inner ℝ qω (normalVector (ω : Real.Angle)) = 0 := by
        rw [inner_sub_left, hoω, inner_normalVector_self]
        norm_num
      have hqωy : qω 1 = 1 - Real.sin ω := by
        simp [qω, o, stripParallelogram, normalVector, frame]
      exact ⟨⟨by rw [hqωy]; linarith, by rw [hqωy]; linarith⟩,
        by rw [hqωn], by rw [hqωn]; norm_num⟩
    have hqω : qω ∈ capOfSofa s ω := by
      apply mem_capOfSofa_of_mem_strip_of_upper hqωP
      intro u hu
      have hcos : 0 ≤ Real.cos (ω - u) := Real.cos_nonneg_of_mem_Icc
        ⟨by rcases hu with hu | hu <;> linarith [hu.2, hs.2.2.2.1],
          by rcases hu with hu | hu <;> linarith [hu.1, hs.2.2.1]⟩
      calc
        inner ℝ qω (normalVector (u : Real.Angle)) =
            inner ℝ o (normalVector (u : Real.Angle)) - Real.cos (ω - u) := by
              simp [qω, inner_sub_left, inner_normalVector_normalVector]
        _ ≤ inner ℝ o (normalVector (u : Real.Angle)) := sub_le_self _ hcos
        _ ≤ supportValue s (u : Real.Angle) := hou u hu
    have hlowerT : supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
      apply supportValue_eq_zero_of_nonpos_of_attains_zero K
      · intro p hp
        change p ∈ capOfSofa s ω at hp
        have := ((mem_stripParallelogram_iff ω p).1 hp.1).1.1
        simpa [inner_normalVector_three_pi_div_two] using neg_nonpos.mpr this
      · exact hq₀
      · simp [q₀, o, stripParallelogram, inner_normalVector_three_pi_div_two,
          tangentVector, frame]
    have hlowerω : supportValue K ((ω + Real.pi : ℝ) : Real.Angle) = 0 := by
      apply supportValue_eq_zero_of_nonpos_of_attains_zero K
      · intro p hp
        change p ∈ capOfSofa s ω at hp
        rw [normalVector_add_pi, inner_neg_right]
        exact neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp.1).2.1
      · exact hqω
      · rw [normalVector_add_pi, inner_neg_right]
        have hqωn : inner ℝ qω (normalVector (ω : Real.Angle)) = 0 := by
          rw [inner_sub_left, hoω, inner_normalVector_self]
          norm_num
        rw [hqωn, neg_zero]
    exact ⟨⟨K, hs.2.2.1, hs.2.2.2.1, hKω, hKπ, hlowerω, hlowerT,
      ⟨D, hDN, hC⟩⟩, rfl⟩

theorem standardPosition_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) (K : CapSpace ω)
    (hK : (K.val : Set Point) = capOfSofa s ω) :
    monotonization s ω = (K.val : Set Point) \ capNiche K := by
  have hsupport := (standardPosition_support_eq s ω hs).1
  have hparts (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
      supportingHallway s (t : Real.Angle) =
        (rotatingHallwayParts s (t : Real.Angle)).outerQuadrant \
          innerQuadrant (K.val : Set Point) t := by
    obtain ⟨h, _⟩ := rotatingHallwayParts_formulas s (t : Real.Angle)
    have h₀ := (hsupport t (Or.inl ht)).2
    have ht' : t + Real.pi / 2 ∈ capUpperAngles ω :=
      Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h₁ := (hsupport (t + Real.pi / 2) ht').2
    simp only [Real.Angle.coe_add] at h₁
    rw [h, rotatingHallwayParts_innerQuadrant]
    simp only [innerQuadrant, hK, h₀, h₁, Real.Angle.coe_add]
  ext p
  constructor
  · intro hp
    have hpH (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
        p ∈ (rotatingHallwayParts s (t : Real.Angle)).outerQuadrant \
          innerQuadrant (K.val : Set Point) t := by
      rw [← hparts t ht]
      exact Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
    have hpK : p ∈ (K.val : Set Point) := by
      rw [hK]
      exact ⟨hp.1, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ (hpH t ht).1⟩
    refine ⟨hpK, ?_⟩
    rintro ⟨_, hN⟩
    obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hN
    exact (hpH t ⟨ht.1.le, ht.2.le⟩).2 hq
  · rintro ⟨hpK, hpN⟩
    have hpC : p ∈ capOfSofa s ω := hK ▸ hpK
    have hpF := K.subset_capFan hpK
    refine ⟨hpC.1, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
    rw [hparts t ht]
    refine ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hpC.2 t) ht, ?_⟩
    intro hq
    have ht0 : t ≠ 0 := by
      rintro rfl
      have h := hq.2
      change inner ℝ p (normalVector ((0 + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue K.val ((0 + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h
      rw [zero_add, K.property.2.2.2.1] at h
      have hf := hpF.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hf
      linarith
    have htω : t ≠ ω := by
      intro he
      subst t
      have h := hq.1
      change inner ℝ p (normalVector (ω : Real.Angle)) <
        supportValue K.val (ω : Real.Angle) - 1 at h
      rw [K.property.2.2.1] at h
      have hf := hpF.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hf
      linarith
    exact hpN ⟨hpF, Set.mem_iUnion₂.mpr
      ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htω⟩, hq⟩⟩

end MovingSofa

end

end

end
