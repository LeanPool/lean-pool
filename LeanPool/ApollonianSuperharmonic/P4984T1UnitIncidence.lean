/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4984T1RootGaps
public import LeanPool.ApollonianSuperharmonic.P4828T1Evaluate
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- [TABLET NODE: P4984T1UnitIncidence]

/-!
# P4984T1UnitIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace UnitIncidenceProof

private theorem hdistAt190 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), ∀ (p : ℂ), ((p.re - u.re)^2 + (p.im - u.im)^2 = 1) → ((p.im -
        u.im ≤ 1) → ((((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) = ⟨u.re, u.im + 2⟩) → (1
        ≤ ‖p - ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)‖))) := by
  classical
  intro a u p hsum hyone hupper
  have hs : Complex.normSq
      (p - ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)) =
      (p.re - u.re)^2 + (p.im - (u.im + 2))^2 := by
    rw [hupper]
    simp [Complex.normSq, Complex.sub_re, Complex.sub_im, pow_two]
  have hn : ‖p - ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)‖^2 =
      (p.re - u.re)^2 + (p.im - (u.im + 2))^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hs
  have hnn := norm_nonneg (p -
    ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex))
  nlinarith [hn, hsum, hyone]

private theorem hdistAt357 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), ∀ (p : ℂ), ((p.re - u.re)^2 + (p.im - u.im)^2 = 1) → ((-1 ≤
        p.im - u.im) → ((((1 + 2 * (a - ⟨0, 1⟩) : GaussianInt) : Complex) = ⟨u.re, u.im - 2⟩) →
        (1 ≤ ‖p - ((1 + 2 * (a - ⟨0, 1⟩) : GaussianInt) : Complex)‖))) := by
  classical
  intro a u p hsum hyminus hbelow
  have hs : Complex.normSq
      (p - ((1 + 2 * (a - ⟨0, 1⟩) : GaussianInt) : Complex)) =
      (p.re - u.re)^2 + (p.im - (u.im - 2))^2 := by
    rw [hbelow]
    simp [Complex.normSq, Complex.sub_re, Complex.sub_im, pow_two]
  have hn : ‖p - ((1 + 2 * (a - ⟨0, 1⟩) : GaussianInt) : Complex)‖^2 =
      (p.re - u.re)^2 + (p.im - (u.im - 2))^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hs
  have hnn := norm_nonneg (p -
    ((1 + 2 * (a - ⟨0, 1⟩) : GaussianInt) : Complex))
  nlinarith [hn, hsum, hyminus]

private theorem hQimage :
    ∀ (a : GaussianInt), ∀ (u : ℂ), (u = (GaussianInt.toComplex : GaussianInt → ℂ) ((1 :
        GaussianInt) + (2 : GaussianInt) * a)) → (
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    ((u : Complex) = ⟨2 * (a.re : Real) + 1, 2 * (a.im : Real)⟩) → (
    let γ (left upper : Bool) (t : Real) : Complex :=
      u + (if left then -(Real.sqrt (1 - t^2) : Real) else Real.sqrt (1 - t^2)) +
        ((if upper then t else -t : Real) : Complex) * Complex.I
    ∀ (left : Bool), ∀ (upper : Bool), Q left upper = γ left upper '' Set.Icc (0 : ℝ) (1 : ℝ)))
        := by
  classical
  intro a u huDef Q hu γ left upper
  apply Set.ext
  intro p
  change (‖p - u‖ = 1 ∧
    (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
    (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)) ↔
    ∃ t ∈ Set.Icc (0 : Real) 1, γ left upper t = p
  constructor
  · rintro ⟨hnorm, hx, hy⟩
    have hs : Complex.normSq (p - u) = 1 := by
      calc
        Complex.normSq (p - u) = ‖p - u‖^2 := Complex.normSq_eq_norm_sq _
        _ = 1 := by rw [hnorm]; norm_num
    change (p - u).re * (p - u).re + (p - u).im * (p - u).im = 1 at hs
    rw [Complex.sub_re, Complex.sub_im] at hs
    have hsum : (p.re - u.re)^2 + (p.im - u.im)^2 = 1 := by nlinarith [hs]
    let t : Real := if upper then p.im - u.im else u.im - p.im
    have ht0 : 0 ≤ t := by
      dsimp [t]
      cases upper <;> simp_all
    have ht1 : t ≤ 1 := by
      cases upper <;> dsimp [t] <;> nlinarith [hsum]
    have ht : t ∈ Set.Icc (0 : Real) 1 := ⟨ht0, ht1⟩
    have htSq : t^2 = (p.im - u.im)^2 := by
      cases upper <;> dsimp [t]; ring
    have hsqrt : Real.sqrt (1 - t^2) = |p.re - u.re| := by
      calc
        Real.sqrt (1 - t^2) = Real.sqrt ((p.re - u.re)^2) := by
          congr 1; nlinarith [hsum, htSq]
        _ = |p.re - u.re| := Real.sqrt_sq_eq_abs _
    have hx' : (if left then -(Real.sqrt (1 - t^2)) else Real.sqrt (1 - t^2)) =
        p.re - u.re := by
      cases left
      · simp only [Bool.false_eq_true, ↓reduceIte, sub_nonneg] at hx ⊢
        have hxrel : 0 ≤ p.re - u.re := by linarith [hx]
        rw [hsqrt, abs_of_nonneg hxrel]
      · simp only [↓reduceIte, tsub_le_iff_right, zero_add] at hx ⊢
        have hxrel : p.re - u.re ≤ 0 := by linarith [hx]
        rw [hsqrt, abs_of_nonpos hxrel]
        ring
    have hy' : (if upper then t else -t) = p.im - u.im := by
      cases upper <;> simp [t]
    refine ⟨t, ht, ?_⟩
    apply Complex.ext
    · simp [γ, hx']
    · simp [γ, hy']
  · rintro ⟨t, ht, rfl⟩
    have hq : 0 ≤ 1 - t^2 := by nlinarith [ht.1, ht.2]
    have hs : Real.sqrt (1 - t^2)^2 = 1 - t^2 := Real.sq_sqrt hq
    have hns : Complex.normSq (γ left upper t - u) = 1 := by
      have hsub : γ left upper t - u =
          (if left then -(Real.sqrt (1 - t^2) : Real) else Real.sqrt (1 - t^2)) +
            ((if upper then t else -t : Real) : Complex) * Complex.I := by
        dsimp [γ]
        ring
      cases left <;> cases upper <;>
        simp [hsub, Complex.normSq_apply] <;> nlinarith [hs]
    have hnorm' : ‖γ left upper t - u‖ = 1 := by
      have hsquare : ‖γ left upper t - u‖ ^ 2 = 1 := by
        simpa only [Complex.normSq_eq_norm_sq] using hns
      rcases sq_eq_one_iff.mp hsquare with hnorm' | hnorm'
      · exact hnorm'
      · have hn := norm_nonneg (γ left upper t - u)
        linarith
    have hre : (γ left upper t).re = u.re +
        (if left then -Real.sqrt (1 - t^2) else Real.sqrt (1 - t^2)) := by
      change (u + (if left then -(Real.sqrt (1 - t^2) : Real) else
        Real.sqrt (1 - t^2)) +
        ((if upper then t else -t : Real) : Complex) * Complex.I).re =
        u.re + (if left then -Real.sqrt (1 - t^2) else Real.sqrt (1 - t^2))
      rw [Complex.add_re, Complex.add_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.I_re, Complex.I_im]
      ring
    have him : (γ left upper t).im = u.im +
        (if upper then t else -t) := by
      change (u + (if left then -(Real.sqrt (1 - t^2) : Real) else
        Real.sqrt (1 - t^2)) +
        ((if upper then t else -t : Real) : Complex) * Complex.I).im =
        u.im + (if upper then t else -t)
      rw [Complex.add_im, Complex.add_im]
      simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    constructor
    · exact hnorm'
    constructor
    · cases left
      · change 0 ≤ (γ false upper t).re - u.re
        simp only [Bool.false_eq_true, ite_false] at hre ⊢
        rw [hre]
        have hsqrt : 0 ≤ Real.sqrt (1 - t^2) := Real.sqrt_nonneg _
        linarith
      · change (γ true upper t).re - u.re ≤ 0
        simp only [ite_true] at hre ⊢
        rw [hre]
        have hsqrt : 0 ≤ Real.sqrt (1 - t^2) := Real.sqrt_nonneg _
        linarith
    · cases upper
      · simp only [Bool.false_eq_true, ite_false] at him ⊢
        rw [him]
        linarith [ht.1]
      · simp only [ite_eq_left] at him ⊢
        rw [him]
        linarith [ht.1]

private theorem hQcover :
    ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    Metric.sphere u 1 = ⋃ i : Fin 4, Q (i = 0 ∨ i = 2) (i = 0 ∨ i = 1) := by
  classical
  intro u Q
  exact (by
      ext p
      simp only [Metric.mem_sphere, dist_eq_norm, Set.mem_iUnion]
      constructor
      · intro hsphere
        have hnorm : ‖p - u‖ = 1 := hsphere
        have hx : p.re - u.re ≤ 0 ∨ 0 ≤ p.re - u.re := le_total _ _
        have hy : 0 ≤ p.im - u.im ∨ p.im - u.im ≤ 0 := le_total _ _
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · refine ⟨0, ?_⟩
          change p ∈ Q true true
          change ‖p - u‖ = 1 ∧ p.re - u.re ≤ 0 ∧ 0 ≤ p.im - u.im
          exact ⟨hnorm, hx, hy⟩
        · refine ⟨2, ?_⟩
          change p ∈ Q true false
          change ‖p - u‖ = 1 ∧ p.re - u.re ≤ 0 ∧ p.im - u.im ≤ 0
          exact ⟨hnorm, hx, hy⟩
        · refine ⟨1, ?_⟩
          change p ∈ Q false true
          change ‖p - u‖ = 1 ∧ 0 ≤ p.re - u.re ∧ 0 ≤ p.im - u.im
          exact ⟨hnorm, hx, hy⟩
        · refine ⟨3, ?_⟩
          change p ∈ Q false false
          change ‖p - u‖ = 1 ∧ 0 ≤ p.re - u.re ∧ p.im - u.im ≤ 0
          exact ⟨hnorm, hx, hy⟩
      · rintro ⟨i, hp⟩
        have hpNorm : ‖p - u‖ = 1 := by
          change ‖p - u‖ = 1 ∧ _ ∧ _ at hp
          exact hp.1
        simpa [dist_eq_norm] using hpNorm
    )

private theorem hparent :
    ∀ (a : GaussianInt),
    let roots : Fin 4 → GaussianInt × Bool :=
      ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
    ∀ i : Fin 4, ∃ j : Fin 3, P4828T1Evaluate (roots i).1 (roots i).2 [] j.succ = (1, 1 + 2 *
        a) := by
  classical
  intro a roots i
  fin_cases i
  · refine ⟨0, ?_⟩
    change (P4828T1Root a false) 1 = _
    simp [P4828T1Root]
  · refine ⟨0, ?_⟩
    change (P4828T1Root a true) 1 = _
    simp [P4828T1Root]
  · refine ⟨2, ?_⟩
    change (P4828T1Root (a - ⟨0, 1⟩) false) 3 = _
    simp [P4828T1Root]
    ring
  · refine ⟨1, ?_⟩
    change (P4828T1Root (a - ⟨0, 1⟩) true) 2 = _
    simp [P4828T1Root]
    ring

private theorem hseedUnion :
    ∀ (a : GaussianInt), ∀ (u : ℂ),
    let seeds : Finset (GaussianInt × Bool × List (Fin 3)) :=
      {(a, false, []), (a, true, []),
        (a - ⟨0, 1⟩, false, []), (a - ⟨0, 1⟩, true, [])}
    let arc (ι : GaussianInt × Bool × List (Fin 3)) : Set Complex :=
      P4984T1ClosedGap (2 * (ι.1.re : Real))
        (P4828T1Evaluate ι.1 ι.2.1 ι.2.2) ∩ Metric.sphere u 1
    let roots : Fin 4 → GaussianInt × Bool :=
      ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
    let A (i : Fin 4) : Set Complex :=
      P4984T1ClosedGap (2 * ((roots i).1.re : Real))
        (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
    (arc (a, false, []) = A 0) → ((arc (a, true, []) = A 1) → ((arc (a - ⟨0, 1⟩, false, []) = A
        2) → ((arc (a - ⟨0, 1⟩, true, []) = A 3) → ((⋃ ι ∈ seeds, arc ι) = ⋃ i : Fin 4, A i))))
            := by
  classical
  intro a u seeds arc roots A hArc0 hArc1 hArc2 hArc3
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨ι, hι, hp⟩
    simp only [seeds, Finset.mem_insert, Finset.mem_singleton] at hι
    rcases hι with hι | hι | hι | hι
    · subst ι
      exact ⟨0, hArc0.symm ▸ hp⟩
    · subst ι
      exact ⟨1, hArc1.symm ▸ hp⟩
    · subst ι
      exact ⟨2, hArc2.symm ▸ hp⟩
    · subst ι
      exact ⟨3, hArc3.symm ▸ hp⟩
  · rintro ⟨i, hp⟩
    fin_cases i
    · refine ⟨(a, false, []), ?_, hArc0 ▸ hp⟩
      unfold seeds
      exact Finset.mem_insert.mpr (Or.inl rfl)
    · refine ⟨(a, true, []), ?_, hArc1 ▸ hp⟩
      unfold seeds
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
    · refine ⟨(a - ⟨0, 1⟩, false, []), ?_, hArc2 ▸ hp⟩
      unfold seeds
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))) )
    · refine ⟨(a - ⟨0, 1⟩, true, []), ?_, hArc3 ▸ hp⟩
      unfold seeds
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr rfl))))) )

end UnitIncidenceProof

namespace UnitIncidenceDetails

private theorem hu :
    ∀ (a : GaussianInt), ∀ (u : ℂ), (u = (GaussianInt.toComplex : GaussianInt → ℂ) ((1 :
        GaussianInt) + (2 : GaussianInt) * a)) → ((u : Complex) = ⟨2 * (a.re : Real) + 1, 2 *
        (a.im : Real)⟩) := by
  classical
  intro a u huDef
  rw [huDef]
  rw [GaussianInt.toComplex_def₂]
  apply Complex.ext <;> simp [Zsqrtd.re_add, Zsqrtd.re_mul,
    Zsqrtd.im_add, Zsqrtd.im_mul]; ring

private theorem hLAt468 :
    ∀ (a : GaussianInt), 2 * (GaussianInt.toComplex a).re = 2 * (a.re : Real) := by
  classical
  intro a
  calc
    _ = 2 * ((a.re : ℤ) : Real) := by rw [← GaussianInt.intCast_re]
    _ = _ := rfl

private theorem huReAt488 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), ((u : Complex) = ⟨2 * (a.re : Real) + 1, 2 * (a.im : Real)⟩)
        → (u.re = 2 * (GaussianInt.toComplex a).re + 1) := by
  classical
  intro a u hu
  rw [hu]
  simp [GaussianInt.intCast_re]

private theorem huImAt491 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), ((u : Complex) = ⟨2 * (a.re : Real) + 1, 2 * (a.im : Real)⟩)
        → (u.im = 2 * (GaussianInt.toComplex a).im) := by
  classical
  intro a u hu
  rw [hu]
  simp [GaussianInt.intCast_im]

private theorem hsumAt494 :
    ∀ (u : ℂ), ∀ (p : ℂ), (‖p - u‖ = (1 : ℝ)) → ((p.re - u.re)^2 + (p.im - u.im)^2 = 1) := by
  classical
  intro u p hnorm
  have hs : Complex.normSq (p - u) = 1 := by
    calc
      Complex.normSq (p - u) = ‖p - u‖^2 := Complex.normSq_eq_norm_sq _
      _ = 1 := by rw [hnorm]; norm_num
  change (p - u).re * (p - u).re + (p - u).im * (p - u).im = 1 at hs
  rw [Complex.sub_re, Complex.sub_im] at hs
  nlinarith [hs]

private theorem hupperAt503 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), ((u : Complex) = ⟨2 * (a.re : Real) + 1, 2 * (a.im : Real)⟩)
        → (((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) = ⟨u.re, u.im + 2⟩) := by
  classical
  intro a u hu
  rw [GaussianInt.toComplex_def₂]
  apply Complex.ext <;> simp [hu, Zsqrtd.re_add, Zsqrtd.re_mul,
    Zsqrtd.im_add, Zsqrtd.im_mul]; ring

private theorem hownAt528 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), (u = (GaussianInt.toComplex : GaussianInt → ℂ) ((1 :
        GaussianInt) + (2 : GaussianInt) * a)) → ((1 + GaussianInt.toComplex 2 *
        GaussianInt.toComplex a) = u) := by
  classical
  intro a u huDef
  rw [huDef]
  simp only [GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
    GaussianInt.toComplex_one]

private theorem hupper'At534 :
    ∀ (a : GaussianInt), (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a +
        GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) =
        GaussianInt.toComplex (1 + 2 * a + 2 * (⟨0, 1⟩ : GaussianInt)) := by
  classical
  intro a
  simp only [GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
    GaussianInt.toComplex_one]

private theorem hLzAt615 :
    ∀ (a : GaussianInt), 2 * (((a - ⟨0, 1⟩ : GaussianInt).re : ℤ) : Real) = 2 *
        (GaussianInt.toComplex a).re := by
  classical
  intro a
  rw [GaussianInt.intCast_re, GaussianInt.toComplex_sub, Complex.sub_re]
  simp

private theorem hbelowAt648 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), ((u : Complex) = ⟨2 * (a.re : Real) + 1, 2 * (a.im : Real)⟩)
        → (((1 + 2 * (a - ⟨0, 1⟩) : GaussianInt) : Complex) = ⟨u.re, u.im - 2⟩) := by
  classical
  intro a u hu
  rw [GaussianInt.toComplex_def₂]
  apply Complex.ext <;> simp [hu, Zsqrtd.re_add, Zsqrtd.re_mul,
    Zsqrtd.im_add, Zsqrtd.im_mul, Zsqrtd.re_sub, Zsqrtd.im_sub] <;> ring

private theorem hbelow'At673 :
    ∀ (a : GaussianInt), (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex (a - ⟨0, 1⟩ :
        GaussianInt)) = GaussianInt.toComplex (1 + 2 * (a - ⟨0, 1⟩)) := by
  classical
  intro a
  simp only [GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
    GaussianInt.toComplex_one]

private theorem hown'At681 :
    ∀ (a : GaussianInt), ∀ (u : ℂ), (u = (GaussianInt.toComplex : GaussianInt → ℂ) ((1 :
        GaussianInt) + (2 : GaussianInt) * a)) → ((1 + GaussianInt.toComplex 2 *
        GaussianInt.toComplex (a - ⟨0, 1⟩ : GaussianInt) + GaussianInt.toComplex 2 *
        GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) = u) := by
  classical
  intro a u huDef
  rw [huDef]
  simp only [GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
    GaussianInt.toComplex_one, GaussianInt.toComplex_sub]
  ring

private theorem hγcontinuous :
    ∀ (u : ℂ),
    let γ (left upper : Bool) (t : Real) : Complex :=
      u + (if left then -(Real.sqrt (1 - t^2) : Real) else Real.sqrt (1 - t^2)) +
        ((if upper then t else -t : Real) : Complex) * Complex.I
    ∀ (left : Bool), ∀ (upper : Bool), Continuous (γ left upper) := by
  classical
  intro u γ left upper
  cases left <;> cases upper <;> unfold γ <;>
    (try simp only [Bool.false_eq_true, ite_false, ite_true]) <;>
    fun_prop

private theorem hQpre :
    ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    let γ (left upper : Bool) (t : Real) : Complex :=
      u + (if left then -(Real.sqrt (1 - t^2) : Real) else Real.sqrt (1 - t^2)) +
        ((if upper then t else -t : Real) : Complex) * Complex.I
    (∀ (left : Bool), ∀ (upper : Bool), Continuous (γ left upper)) → ((∀ (left : Bool), ∀ (upper
        : Bool), Q left upper = γ left upper '' Set.Icc (0 : Real) 1) → (∀ (left : Bool), ∀
        (upper : Bool), IsPreconnected (Q left upper))) := by
  classical
  intro u Q γ hγcontinuous hQimage left upper
  rw [hQimage left upper]
  exact isPreconnected_Icc.image (γ left upper)
    (hγcontinuous left upper).continuousOn

private theorem hQclosed :
    ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    let γ (left upper : Bool) (t : Real) : Complex :=
      u + (if left then -(Real.sqrt (1 - t^2) : Real) else Real.sqrt (1 - t^2)) +
        ((if upper then t else -t : Real) : Complex) * Complex.I
    (∀ (left : Bool), ∀ (upper : Bool), Continuous (γ left upper)) → ((∀ (left : Bool), ∀ (upper
        : Bool), Q left upper = γ left upper '' Set.Icc (0 : Real) 1) → (∀ (left : Bool), ∀
        (upper : Bool), IsClosed (Q left upper))) := by
  classical
  intro u Q γ hγcontinuous hQimage left upper
  rw [hQimage left upper]
  exact (isCompact_Icc.image_of_continuousOn
    (hγcontinuous left upper).continuousOn).isClosed

private theorem hQnonempty :
    ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    let γ (left upper : Bool) (t : Real) : Complex :=
      u + (if left then -(Real.sqrt (1 - t^2) : Real) else Real.sqrt (1 - t^2)) +
        ((if upper then t else -t : Real) : Complex) * Complex.I
    (∀ (left : Bool), ∀ (upper : Bool), Q left upper = γ left upper '' Set.Icc (0 : Real) 1) → (∀
        (left : Bool), ∀ (upper : Bool), (Q left upper).Nonempty) := by
  classical
  intro u Q γ hQimage left upper
  rw [hQimage left upper]
  exact ⟨γ left upper 0, ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩⟩

private theorem hcover :
    ∀ (a : GaussianInt), ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    let roots : Fin 4 → GaussianInt × Bool :=
      ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
    let A (i : Fin 4) : Set Complex :=
      P4984T1ClosedGap (2 * ((roots i).1.re : Real))
        (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
    (∀ i : Fin 4, A i = Q (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)) → ((Metric.sphere u 1 = ⋃ i : Fin 4, Q
        (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)) → (Metric.sphere u 1 = ⋃ i : Fin 4, A i)) := by
  classical
  intro a u Q roots A hA hQcover
  rw [hQcover]
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hp⟩
    exact ⟨i, (hA i).symm ▸ hp⟩
  · rintro ⟨i, hp⟩
    exact ⟨i, (hA i) ▸ hp⟩

private theorem hclosed :
    ∀ (a : GaussianInt), ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    let roots : Fin 4 → GaussianInt × Bool :=
      ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
    let A (i : Fin 4) : Set Complex :=
      P4984T1ClosedGap (2 * ((roots i).1.re : Real))
        (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
    (∀ i : Fin 4, A i = Q (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)) → ((∀ (left : Bool), ∀ (upper : Bool),
        IsClosed (Q left upper)) → (∀ i : Fin 4, IsClosed (A i))) := by
  classical
  intro a u Q roots A hA hQclosed i
  rw [hA i]
  exact hQclosed (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)

private theorem hpre :
    ∀ (a : GaussianInt), ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    let roots : Fin 4 → GaussianInt × Bool :=
      ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
    let A (i : Fin 4) : Set Complex :=
      P4984T1ClosedGap (2 * ((roots i).1.re : Real))
        (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
    (∀ i : Fin 4, A i = Q (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)) → ((∀ (left : Bool), ∀ (upper : Bool),
        IsPreconnected (Q left upper)) → (∀ i : Fin 4, IsPreconnected (A i))) := by
  classical
  intro a u Q roots A hA hQpre i
  rw [hA i]
  exact hQpre (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)

private theorem hne :
    ∀ (a : GaussianInt), ∀ (u : ℂ),
    let Q (left upper : Bool) : Set Complex :=
      {p | ‖p - u‖ = 1 ∧
        (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
        (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
    let roots : Fin 4 → GaussianInt × Bool :=
      ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
    let A (i : Fin 4) : Set Complex :=
      P4984T1ClosedGap (2 * ((roots i).1.re : Real))
        (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
    (∀ i : Fin 4, A i = Q (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)) → ((∀ (left : Bool), ∀ (upper : Bool),
        (Q left upper).Nonempty) → (∀ i : Fin 4, (A i).Nonempty)) := by
  classical
  intro a u Q roots A hA hQnonempty i
  rw [hA i]
  exact hQnonempty (i = 0 ∨ i = 2) (i = 0 ∨ i = 1)

end UnitIncidenceDetails

namespace UnitRootQuadrants

private theorem upperLeftRootGap :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (u : ℂ), ∀ (huDef : u = (GaussianInt.toComplex : GaussianInt → ℂ)
            ((1 : GaussianInt) + (2 : GaussianInt) * a)), let Q (left upper : Bool) : Set Complex :=
          {p | ‖p - u‖ = 1 ∧
            (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
            (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
        let roots : Fin 4 → GaussianInt × Bool :=
          ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
        let A (i : Fin 4) : Set Complex :=
          P4984T1ClosedGap (2 * ((roots i).1.re : Real))
            (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
        (u = ⟨(2 : ℝ) * (↑a.re : ℝ) + (1 : ℝ), (2 : ℝ) * (↑a.im : ℝ)⟩) → (A (0 : Fin 4) = Q ((0 :
            Fin 4) = 0 ∨ (0 : Fin 4) = 2) ((0 : Fin 4) = 0 ∨ (0 : Fin 4) = 1))) := by
  classical
  intro a u huDef Q roots A hu
  simp only [Int.reduceNeg, GaussianInt.intCast_re, P4828T1Evaluate, List.foldl_nil,
      Fin.isValue, Matrix.cons_val_zero, Fin.reduceEq, or_false, decide_true, zero_ne_one, A,
      roots]
  have hL := UnitIncidenceDetails.hLAt468 a
  rw [hL]
  rw [P4984T1RootGaps.1 a]
  ext p
  simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im, map_add, map_one,
      map_mul, dist_eq_norm, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_sphere_iff_norm,
      tsub_le_iff_right, zero_add, sub_nonneg, ↓reduceIte, Q]
  constructor
  · rintro ⟨⟨hxl, hxr, hyl, hyr, _, _⟩, hnorm⟩
    refine ⟨hnorm, ?_, ?_⟩
    · rw [hu]
      change p.re ≤ 2 * (a.re : Real) + 1
      rw [← GaussianInt.intCast_re a] at hxl hxr
      nlinarith
    · rw [hu]
      change 2 * (a.im : Real) ≤ p.im
      rw [← GaussianInt.intCast_im a] at hyl hyr
      nlinarith
  · rintro ⟨hnorm, hright, hbottom⟩
    have huRe := UnitIncidenceDetails.huReAt488 a u hu
    have huIm := UnitIncidenceDetails.huImAt491
        a u hu
    have hsum := UnitIncidenceDetails.hsumAt494 u
        p hnorm
    have hyone : p.im - u.im ≤ 1 := by nlinarith [hsum]
    have hupper := UnitIncidenceDetails.hupperAt503 a u hu
    have hdist := UnitIncidenceProof.hdistAt190 a u p hsum hyone hupper
    refine ⟨?_, hnorm⟩
    change (2 * (GaussianInt.toComplex a).re ≤ p.re ∧
      p.re ≤ 2 * (GaussianInt.toComplex a).re + 1 ∧
      2 * (GaussianInt.toComplex a).im ≤ p.im ∧
      p.im ≤ 2 * (GaussianInt.toComplex a).im + 2 ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a)‖ ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a +
        GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt))‖)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        2 * (GaussianInt.toComplex a).re = u.re - 1 := by linarith [huRe]
        _ ≤ p.re := by nlinarith [hsum]
    · rw [← huRe]
      exact hright
    · rw [← huIm]
      exact hbottom
    · rw [← huIm]
      nlinarith [hyone]
    · have hown : (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a) = u :=
        UnitIncidenceDetails.hownAt528 a u huDef
      rw [hown]
      linarith [hnorm]
    · have hupper' : (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a +
          GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) =
          GaussianInt.toComplex (1 + 2 * a + 2 * (⟨0, 1⟩ : GaussianInt)) :=
              UnitIncidenceDetails.hupper'At534 a
      rw [hupper']
      exact hdist

private theorem upperRightRootGap :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (u : ℂ), ∀ (huDef : u = (GaussianInt.toComplex : GaussianInt → ℂ)
            ((1 : GaussianInt) + (2 : GaussianInt) * a)), let Q (left upper : Bool) : Set Complex :=
          {p | ‖p - u‖ = 1 ∧
            (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
            (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
        let roots : Fin 4 → GaussianInt × Bool :=
          ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
        let A (i : Fin 4) : Set Complex :=
          P4984T1ClosedGap (2 * ((roots i).1.re : Real))
            (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
        (u = ⟨(2 : ℝ) * (↑a.re : ℝ) + (1 : ℝ), (2 : ℝ) * (↑a.im : ℝ)⟩) → (A (1 : Fin 4) = Q ((1 :
            Fin 4) = 0 ∨ (1 : Fin 4) = 2) ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 1))) := by
  classical
  intro a u huDef Q roots A hu
  simp only [Int.reduceNeg, GaussianInt.intCast_re, P4828T1Evaluate, List.foldl_nil,
      Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, one_ne_zero, Fin.reduceEq,
      or_self, decide_false, or_true, decide_true, A, roots]
  have hL := UnitIncidenceDetails.hLAt468 a
  rw [hL]
  rw [P4984T1RootGaps.2.1 a]
  ext p
  simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im, map_add, map_one,
      map_mul, dist_eq_norm, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_sphere_iff_norm,
      tsub_le_iff_right, zero_add, sub_nonneg, Bool.false_eq_true, ↓reduceIte, Q]
  constructor
  · rintro ⟨⟨hxl, hxr, hyl, hyr, _, _⟩, hnorm⟩
    refine ⟨hnorm, ?_, ?_⟩
    · rw [hu]
      change 2 * (a.re : Real) + 1 ≤ p.re
      rw [← GaussianInt.intCast_re a] at hxl hxr
      linarith
    · rw [hu]
      change 2 * (a.im : Real) ≤ p.im
      rw [← GaussianInt.intCast_im a] at hyl hyr
      linarith
  · rintro ⟨hnorm, hright, hbottom⟩
    have huRe : u.re = 2 * (GaussianInt.toComplex a).re + 1 := by
      rw [hu]; simp [GaussianInt.intCast_re]
    have huIm : u.im = 2 * (GaussianInt.toComplex a).im := by
      rw [hu]; simp [GaussianInt.intCast_im]
    have hsum := UnitIncidenceDetails.hsumAt494 u
        p hnorm
    have hyone : p.im - u.im ≤ 1 := by nlinarith [hsum]
    have hupper := UnitIncidenceDetails.hupperAt503 a u hu
    have hdist := UnitIncidenceProof.hdistAt190 a u p hsum hyone hupper
    refine ⟨?_, hnorm⟩
    change (2 * (GaussianInt.toComplex a).re + 1 ≤ p.re ∧
      p.re ≤ 2 * (GaussianInt.toComplex a).re + 2 ∧
      2 * (GaussianInt.toComplex a).im ≤ p.im ∧
      p.im ≤ 2 * (GaussianInt.toComplex a).im + 2 ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a)‖ ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a +
        GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt))‖)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        2 * (GaussianInt.toComplex a).re + 1 = u.re := by linarith [huRe]
        _ ≤ p.re := by linarith [hright]
    · calc
        p.re ≤ u.re + 1 := by nlinarith [hsum]
        _ = 2 * (GaussianInt.toComplex a).re + 2 := by linarith [huRe]
    · rw [← huIm]
      exact hbottom
    · rw [← huIm]
      nlinarith [hyone]
    · have hown : (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a) = u :=
        UnitIncidenceDetails.hownAt528 a u huDef
      rw [hown]
      linarith [hnorm]
    · have hupper' : (1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a +
          GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) =
          GaussianInt.toComplex (1 + 2 * a + 2 * (⟨0, 1⟩ : GaussianInt)) :=
              UnitIncidenceDetails.hupper'At534 a
      rw [hupper']
      exact hdist

private theorem lowerLeftRootGap :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (u : ℂ), ∀ (huDef : u = (GaussianInt.toComplex : GaussianInt → ℂ)
            ((1 : GaussianInt) + (2 : GaussianInt) * a)), let Q (left upper : Bool) : Set Complex :=
          {p | ‖p - u‖ = 1 ∧
            (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
            (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
        let roots : Fin 4 → GaussianInt × Bool :=
          ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
        let A (i : Fin 4) : Set Complex :=
          P4984T1ClosedGap (2 * ((roots i).1.re : Real))
            (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
        (u = ⟨(2 : ℝ) * (↑a.re : ℝ) + (1 : ℝ), (2 : ℝ) * (↑a.im : ℝ)⟩) → (A (2 : Fin 4) = Q ((2 :
            Fin 4) = 0 ∨ (2 : Fin 4) = 2) ((2 : Fin 4) = 0 ∨ (2 : Fin 4) = 1))) := by
  classical
  intro a u huDef Q roots A hu
  simp only [Int.reduceNeg, GaussianInt.intCast_re, P4828T1Evaluate, List.foldl_nil,
      Fin.isValue, Matrix.cons_val, map_sub, Complex.sub_re, GaussianInt.re_toComplex,
      Int.cast_zero, sub_zero, Fin.reduceEq, or_true, decide_true, or_self, decide_false, A,
      roots]
  have hLz := UnitIncidenceDetails.hLzAt615 a
  rw [← hLz]
  rw [P4984T1RootGaps.1 (a - ⟨0, 1⟩)]
  ext p
  simp only [Int.reduceNeg, Zsqrtd.re_sub, sub_zero, GaussianInt.intCast_re, Zsqrtd.im_sub,
      Int.cast_sub, GaussianInt.intCast_im, Int.cast_one, map_add, map_one, map_mul, map_sub,
      dist_eq_norm, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_sphere_iff_norm,
      tsub_le_iff_right, zero_add, sub_nonneg, ↓reduceIte, Bool.false_eq_true, Q]
  constructor
  · rintro ⟨⟨hxl, hxr, hyl, hyr, _, _⟩, hnorm⟩
    refine ⟨hnorm, ?_, ?_⟩
    · rw [hu]
      change p.re ≤ 2 * (a.re : Real) + 1
      rw [← GaussianInt.intCast_re a] at hxl hxr
      linarith
    · rw [hu]
      change p.im ≤ 2 * (a.im : Real)
      rw [← GaussianInt.intCast_im a] at hyr
      nlinarith [hyr]
  · rintro ⟨hnorm, hright, hbottom⟩
    have huRe : u.re = 2 * (GaussianInt.toComplex a).re + 1 := by
      rw [hu]; simp [GaussianInt.intCast_re]
    have huIm : u.im = 2 * (GaussianInt.toComplex a).im := by
      rw [hu]; simp [GaussianInt.intCast_im]
    have hsum := UnitIncidenceDetails.hsumAt494 u
        p hnorm
    have hyminus : -1 ≤ p.im - u.im := by nlinarith [hsum]
    have hbelow := UnitIncidenceDetails.hbelowAt648 a u hu
    have hdist := UnitIncidenceProof.hdistAt357 a u p hsum hyminus hbelow
    refine ⟨?_, hnorm⟩
    change (2 * (GaussianInt.toComplex a).re ≤ p.re ∧
      p.re ≤ 2 * (GaussianInt.toComplex a).re + 1 ∧
      2 * ((GaussianInt.toComplex a).im - 1) ≤ p.im ∧
      p.im ≤ 2 * ((GaussianInt.toComplex a).im - 1) + 2 ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 *
        (GaussianInt.toComplex a - GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)))‖ ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 *
        (GaussianInt.toComplex a - GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) +
        GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt))‖)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        2 * (GaussianInt.toComplex a).re = u.re - 1 := by linarith [huRe]
        _ ≤ p.re := by nlinarith [hsum]
    · rw [← huRe]
      exact hright
    · nlinarith [hyminus, huIm]
    · nlinarith [hbottom, huIm]
    · have hbelow' : (1 + GaussianInt.toComplex 2 *
          GaussianInt.toComplex (a - ⟨0, 1⟩ : GaussianInt)) =
          GaussianInt.toComplex (1 + 2 * (a - ⟨0, 1⟩)) :=
              UnitIncidenceDetails.hbelow'At673 a
      rw [GaussianInt.toComplex_sub] at hbelow'
      rw [hbelow']
      exact hdist
    · have hown' : (1 + GaussianInt.toComplex 2 *
          GaussianInt.toComplex (a - ⟨0, 1⟩ : GaussianInt) +
          GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) = u :=
              UnitIncidenceDetails.hown'At681 a u huDef
      rw [GaussianInt.toComplex_sub] at hown'
      rw [hown']
      linarith [hnorm]

private theorem lowerRightRootGap :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (u : ℂ), ∀ (huDef : u = (GaussianInt.toComplex : GaussianInt → ℂ)
            ((1 : GaussianInt) + (2 : GaussianInt) * a)), let Q (left upper : Bool) : Set Complex :=
          {p | ‖p - u‖ = 1 ∧
            (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
            (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
        let roots : Fin 4 → GaussianInt × Bool :=
          ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
        let A (i : Fin 4) : Set Complex :=
          P4984T1ClosedGap (2 * ((roots i).1.re : Real))
            (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
        (u = ⟨(2 : ℝ) * (↑a.re : ℝ) + (1 : ℝ), (2 : ℝ) * (↑a.im : ℝ)⟩) → (A (3 : Fin 4) = Q ((3 :
            Fin 4) = 0 ∨ (3 : Fin 4) = 2) ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 1))) := by
  classical
  intro a u huDef Q roots A hu
  simp only [Int.reduceNeg, GaussianInt.intCast_re, P4828T1Evaluate, List.foldl_nil,
      Fin.isValue, Matrix.cons_val, map_sub, Complex.sub_re, GaussianInt.re_toComplex,
      Int.cast_zero, sub_zero, Fin.reduceEq, or_self, decide_false, A, roots]
  have hLz := UnitIncidenceDetails.hLzAt615 a
  rw [← hLz]
  rw [P4984T1RootGaps.2.1 (a - ⟨0, 1⟩)]
  ext p
  simp only [Int.reduceNeg, Zsqrtd.re_sub, sub_zero, GaussianInt.intCast_re, Zsqrtd.im_sub,
      Int.cast_sub, GaussianInt.intCast_im, Int.cast_one, map_add, map_one, map_mul, map_sub,
      dist_eq_norm, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_sphere_iff_norm,
      tsub_le_iff_right, zero_add, sub_nonneg, Bool.false_eq_true, ↓reduceIte, Q]
  constructor
  · rintro ⟨⟨hxl, hxr, hyl, hyr, _, _⟩, hnorm⟩
    refine ⟨hnorm, ?_, ?_⟩
    · rw [hu]
      change 2 * (a.re : Real) + 1 ≤ p.re
      rw [← GaussianInt.intCast_re a] at hxl hxr
      linarith
    · rw [hu]
      change p.im ≤ 2 * (a.im : Real)
      rw [← GaussianInt.intCast_im a] at hyr
      nlinarith [hyr]
  · rintro ⟨hnorm, hright, hbottom⟩
    have huRe : u.re = 2 * (GaussianInt.toComplex a).re + 1 := by
      rw [hu]; simp [GaussianInt.intCast_re]
    have huIm : u.im = 2 * (GaussianInt.toComplex a).im := by
      rw [hu]; simp [GaussianInt.intCast_im]
    have hsum := UnitIncidenceDetails.hsumAt494 u
        p hnorm
    have hyminus : -1 ≤ p.im - u.im := by nlinarith [hsum]
    have hbelow := UnitIncidenceDetails.hbelowAt648 a u hu
    have hdist := UnitIncidenceProof.hdistAt357 a u p hsum hyminus hbelow
    refine ⟨?_, hnorm⟩
    change (2 * (GaussianInt.toComplex a).re + 1 ≤ p.re ∧
      p.re ≤ 2 * (GaussianInt.toComplex a).re + 2 ∧
      2 * ((GaussianInt.toComplex a).im - 1) ≤ p.im ∧
      p.im ≤ 2 * ((GaussianInt.toComplex a).im - 1) + 2 ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 *
        (GaussianInt.toComplex a - GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)))‖ ∧
      1 ≤ ‖p - (1 + GaussianInt.toComplex 2 *
        (GaussianInt.toComplex a - GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) +
        GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt))‖)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        2 * (GaussianInt.toComplex a).re + 1 = u.re := by linarith [huRe]
        _ ≤ p.re := by linarith [hright]
    · calc
        p.re ≤ u.re + 1 := by nlinarith [hsum]
        _ = 2 * (GaussianInt.toComplex a).re + 2 := by linarith [huRe]
    · nlinarith [hyminus]
    · nlinarith [hbottom, huIm]
    · have hbelow' : (1 + GaussianInt.toComplex 2 *
          GaussianInt.toComplex (a - ⟨0, 1⟩ : GaussianInt)) =
          GaussianInt.toComplex (1 + 2 * (a - ⟨0, 1⟩)) :=
              UnitIncidenceDetails.hbelow'At673 a
      rw [GaussianInt.toComplex_sub] at hbelow'
      rw [hbelow']
      exact hdist
    · have hown' : (1 + GaussianInt.toComplex 2 *
          GaussianInt.toComplex (a - ⟨0, 1⟩ : GaussianInt) +
          GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) = u :=
              UnitIncidenceDetails.hown'At681 a u huDef
      rw [GaussianInt.toComplex_sub] at hown'
      rw [hown']
      linarith [hnorm]

end UnitRootQuadrants

theorem P4984T1UnitIncidence (a : GaussianInt) :
    let seeds : Finset (GaussianInt × Bool × List (Fin 3)) :=
      {(a, false, []), (a, true, []),
        (a - ⟨0, 1⟩, false, []), (a - ⟨0, 1⟩, true, [])}
    let arc (ι : GaussianInt × Bool × List (Fin 3)) :=
      P4984T1ClosedGap (2 * (ι.1.re : Real))
        (P4828T1Evaluate ι.1 ι.2.1 ι.2.2) ∩
          Metric.sphere ((1 + 2 * a : GaussianInt) : Complex) 1
    Metric.sphere ((1 + 2 * a : GaussianInt) : Complex) 1 =
        ⋃ ι ∈ seeds, arc ι ∧
      ∀ ι ∈ seeds,
        IsClosed (arc ι) ∧ IsPreconnected (arc ι) ∧ (arc ι).Nonempty ∧
        ∃ j : Fin 3,
          P4828T1Evaluate ι.1 ι.2.1 ι.2.2 j.succ = (1, 1 + 2 * a) := by
-- BODY
  exact (by
      classical
      set u : Complex := ((1 + 2 * a : GaussianInt) : Complex) with huDef
      clear_value u
      let seeds : Finset (GaussianInt × Bool × List (Fin 3)) :=
        {(a, false, []), (a, true, []),
          (a - ⟨0, 1⟩, false, []), (a - ⟨0, 1⟩, true, [])}
      let arc (ι : GaussianInt × Bool × List (Fin 3)) : Set Complex :=
        P4984T1ClosedGap (2 * (ι.1.re : Real))
          (P4828T1Evaluate ι.1 ι.2.1 ι.2.2) ∩ Metric.sphere u 1
      let Q (left upper : Bool) : Set Complex :=
        {p | ‖p - u‖ = 1 ∧
          (if left then p.re - u.re ≤ 0 else 0 ≤ p.re - u.re) ∧
          (if upper then 0 ≤ p.im - u.im else p.im - u.im ≤ 0)}
      let roots : Fin 4 → GaussianInt × Bool :=
        ![(a, false), (a, true), (a - ⟨0, 1⟩, false), (a - ⟨0, 1⟩, true)]
      let A (i : Fin 4) : Set Complex :=
        P4984T1ClosedGap (2 * ((roots i).1.re : Real))
          (P4828T1Evaluate (roots i).1 (roots i).2 []) ∩ Metric.sphere u 1
      have hu := UnitIncidenceDetails.hu a u huDef
      have hA : ∀ i : Fin 4, A i = Q (i = 0 ∨ i = 2) (i = 0 ∨ i = 1) := by
        intro i
        fin_cases i
        · exact UnitRootQuadrants.upperLeftRootGap a u huDef hu
        · exact UnitRootQuadrants.upperRightRootGap a u huDef hu
        · exact UnitRootQuadrants.lowerLeftRootGap a u huDef hu
        · exact UnitRootQuadrants.lowerRightRootGap a u huDef hu
      have hArc0 : arc (a, false, []) = A 0 := by
        simp [arc, A, roots, P4828T1Evaluate]
      have hArc1 : arc (a, true, []) = A 1 := by
        simp [arc, A, roots, P4828T1Evaluate]
      have hArc2 : arc (a - ⟨0, 1⟩, false, []) = A 2 := by
        simp [arc, A, roots, P4828T1Evaluate]
      have hArc3 : arc (a - ⟨0, 1⟩, true, []) = A 3 := by
        simp [arc, A, roots, P4828T1Evaluate]
      let γ (left upper : Bool) (t : Real) : Complex :=
        u + (if left then -(Real.sqrt (1 - t^2) : Real) else Real.sqrt (1 - t^2)) +
          ((if upper then t else -t : Real) : Complex) * Complex.I
      have hγcontinuous (left upper : Bool) := UnitIncidenceDetails.hγcontinuous u left upper
      have hQimage (left upper : Bool) := UnitIncidenceProof.hQimage a u huDef hu left upper
      have hclosed := UnitIncidenceDetails.hclosed a u hA (UnitIncidenceDetails.hQclosed u
          hγcontinuous hQimage)
      have hpre := UnitIncidenceDetails.hpre a u hA (UnitIncidenceDetails.hQpre u hγcontinuous
          hQimage)
      have hne := UnitIncidenceDetails.hne a u hA (UnitIncidenceDetails.hQnonempty u hQimage)
      have hparent := UnitIncidenceProof.hparent a
      constructor
      · change Metric.sphere u 1 = ⋃ ι ∈ seeds, arc ι
        rw [(UnitIncidenceDetails.hcover a u hA (UnitIncidenceProof.hQcover u))]
        exact (UnitIncidenceProof.hseedUnion a u hArc0 hArc1 hArc2 hArc3).symm
      · intro ι hι
        simp only [Finset.mem_insert, Finset.mem_singleton] at hι
        rcases hι with hι | hι | hι | hι
        · subst ι
          change IsClosed (arc (a, false, [])) ∧ IsPreconnected (arc (a, false, [])) ∧
            (arc (a, false, [])).Nonempty ∧
            ∃ j : Fin 3, P4828T1Evaluate a false [] j.succ = (1, 1 + 2 * a)
          rw [hArc0]
          exact ⟨hclosed 0, hpre 0, hne 0, by simpa [roots] using hparent 0⟩
        · subst ι
          change IsClosed (arc (a, true, [])) ∧ IsPreconnected (arc (a, true, [])) ∧
            (arc (a, true, [])).Nonempty ∧
            ∃ j : Fin 3, P4828T1Evaluate a true [] j.succ = (1, 1 + 2 * a)
          rw [hArc1]
          exact ⟨hclosed 1, hpre 1, hne 1, by simpa [roots] using hparent 1⟩
        · subst ι
          have hArc2' := hArc2
          simp only [arc] at hArc2'
          simp only []
          rw [hArc2']
          exact ⟨hclosed 2, hpre 2, hne 2, by simpa [roots] using hparent 2⟩
        · subst ι
          have hArc3' := hArc3
          simp only [arc] at hArc3'
          simp only []
          rw [hArc3']
          exact ⟨hclosed 3, hpre 3, hne 3, by simpa [roots] using hparent 3⟩
  )

end ApollonianSuperharmonic

end
