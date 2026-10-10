/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Periodic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
Analytic phase functions, conjugation compatibility, and the uniform norm. AnalyticOnNhd requires
a convergent power series in an ambient neighborhood at each domain point. Bounded continuous
restrictions supply the actual supremum norm, including on empty domains.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

section UniformNorm

variable {E F : Type*} [NormedAddCommGroup F]

/-- A nonnegative uniform norm bound on the specified set. -/
def NormBoundOn (f : E → F) (S : Set E) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ x ∈ S, ‖f x‖ ≤ M

theorem NormBoundOn.nonneg {f : E → F} {S : Set E} {M : ℝ}
    (h : NormBoundOn f S M) : 0 ≤ M := h.1

theorem NormBoundOn.norm_le {f : E → F} {S : Set E} {M : ℝ}
    (h : NormBoundOn f S M) {x : E} (hx : x ∈ S) : ‖f x‖ ≤ M := h.2 x hx

@[simp] theorem normBoundOn_empty (f : E → F) (M : ℝ) :
    NormBoundOn f ∅ M ↔ 0 ≤ M := by simp [NormBoundOn]

variable [TopologicalSpace E]

/-- Bounded continuous functions on a domain, with the domain's subspace topology. -/
abbrev BoundedOnDomain (S : Set E) := BoundedContinuousFunction ↥S F

/-- The supremum norm inherited from bounded continuous functions on the domain. -/
def supNorm {S : Set E} (f : BoundedOnDomain (F := F) S) : ℝ := ‖f‖

/-- Packaging a continuous function restricted to a set together with its uniform bound. -/
def boundedRestriction (f : E → F) (S : Set E) (hf : ContinuousOn f S)
    (M : ℝ) (hM : NormBoundOn f S M) : BoundedOnDomain (F := F) S :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : S => f x)
    hf.domRestrict M (fun x => hM.norm_le x.property)

@[simp] theorem boundedRestriction_apply (f : E → F) (S : Set E)
    (hf : ContinuousOn f S) (M : ℝ) (hM : NormBoundOn f S M) (x : S) :
    boundedRestriction f S hf M hM x = f x := rfl

theorem norm_apply_le_supNorm {S : Set E} (f : BoundedOnDomain (F := F) S) (x : S) :
    ‖f x‖ ≤ supNorm f := f.norm_coe_le_norm x

theorem supNorm_le_iff {S : Set E} (f : BoundedOnDomain (F := F) S)
    {M : ℝ} (hM : 0 ≤ M) : supNorm f ≤ M ↔ ∀ x : S, ‖f x‖ ≤ M :=
  BoundedContinuousFunction.norm_le hM

theorem supNorm_lt_iff {S : Set E} (f : BoundedOnDomain (F := F) S) (M : ℝ) :
    supNorm f < M ↔ ∃ C : ℝ, 0 ≤ C ∧ C < M ∧ ∀ x : S, ‖f x‖ ≤ C := by
  constructor
  · intro h
    exact ⟨supNorm f, norm_nonneg f, h, fun x => norm_apply_le_supNorm f x⟩
  · rintro ⟨C, hC, hCM, hf⟩
    exact lt_of_le_of_lt ((supNorm_le_iff f hC).2 hf) hCM

theorem supNorm_boundedRestriction_le (f : E → F) (S : Set E)
    (hf : ContinuousOn f S) {M : ℝ} (hM : NormBoundOn f S M) :
    supNorm (boundedRestriction f S hf M hM) ≤ M :=
  (supNorm_le_iff _ hM.nonneg).2 fun x => hM.norm_le x.property

end UniformNorm

theorem analyticOnNhd_iff_forall_analyticAt {n : ℕ} (f : ComplexPhaseSpace n → ℂ)
    (S : Set (ComplexPhaseSpace n)) :
    AnalyticOnNhd ℂ f S ↔ ∀ x ∈ S, AnalyticAt ℂ f x := Iff.rfl

theorem analyticOnNhd_iff_exists_open {n : ℕ} (f : ComplexPhaseSpace n → ℂ)
    (S : Set (ComplexPhaseSpace n)) :
    AnalyticOnNhd ℂ f S ↔
      ∃ U : Set (ComplexPhaseSpace n), IsOpen U ∧ S ⊆ U ∧ AnalyticOnNhd ℂ f U := by
  constructor
  · intro h
    exact ⟨{x | AnalyticAt ℂ f x}, isOpen_analyticAt ℂ f, h, fun _ hx => hx⟩
  · rintro ⟨U, _, hSU, hU⟩
    exact hU.mono hSU

/-- Compatibility of a phase function with complex conjugation on the specified set. -/
def ConjCompatibleOn {n : ℕ} (f : ComplexPhaseSpace n → ℂ)
    (S : Set (ComplexPhaseSpace n)) : Prop :=
  ∀ z ∈ S, f (conjPhase z) = star (f z)

/-- A bounded analytic phase function with angle periodicity and real compatibility. -/
structure AnalyticPhaseFunction (n : ℕ) (G : Set (ComplexSpace n)) (ρ : ℝ≥0) where
  /-- The underlying complex-valued function on action-angle phase space. -/
  toFun : ComplexPhaseSpace n → ℂ
  domain_conj : ConjInvariant G
  analytic : AnalyticOnNhd ℂ toFun (phaseDomain G ρ)
  periodic : AnglePeriodicOn G ρ toFun
  conj_compatible : ConjCompatibleOn toFun (phaseDomain G ρ)
  bounded : ∃ M : ℝ, NormBoundOn toFun (phaseDomain G ρ) M

/-- The bounded continuous restriction of an analytic phase function to its phase domain. -/
def AnalyticPhaseFunction.toBounded {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) :
    BoundedOnDomain (F := ℂ) (phaseDomain G ρ) :=
  boundedRestriction f.toFun (phaseDomain G ρ) f.analytic.continuousOn
    f.bounded.choose f.bounded.choose_spec

/-- The uniform norm of the phase function on its prescribed action-angle domain. -/
def AnalyticPhaseFunction.uniformNorm {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) : ℝ := supNorm f.toBounded

theorem AnalyticPhaseFunction.norm_le_iff {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (f : AnalyticPhaseFunction n G ρ) {M : ℝ} :
    f.uniformNorm ≤ M ↔ NormBoundOn f.toFun (phaseDomain G ρ) M := by
  constructor
  · intro h
    refine ⟨(norm_nonneg f.toBounded).trans h, ?_⟩
    intro x hx
    exact (norm_apply_le_supNorm f.toBounded ⟨x, hx⟩).trans h
  · intro h
    exact (supNorm_le_iff _ h.nonneg).2 fun x => h.norm_le x.property

theorem AnalyticPhaseFunction.real_value {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (f : AnalyticPhaseFunction n G ρ) (p q : RealSpace n)
    (hp : complexify p ∈ G) : (f.toFun (complexify p, complexify q)).im = 0 := by
  have h := f.conj_compatible (complexify p, complexify q)
    (show (complexify p, complexify q) ∈ phaseDomain G ρ from
      ⟨hp, complexify_mem_angleStrip q ρ⟩)
  apply Complex.conj_eq_iff_im.mp
  simpa [conjPhase] using h.symm

/-- A real constant packaged as an analytic phase function on a conjugation-invariant domain. -/
def AnalyticPhaseFunction.constReal {n : ℕ} (G : Set (ComplexSpace n)) (ρ : ℝ≥0)
    (hG : ConjInvariant G) (c : ℝ) : AnalyticPhaseFunction n G ρ where
  toFun := fun _ => (c : ℂ)
  domain_conj := hG
  analytic := analyticOnNhd_const
  periodic := by intro p hp q hq k; rfl
  conj_compatible := by intro z hz; simp
  bounded := ⟨‖(c : ℂ)‖, norm_nonneg _, fun _ _ => le_rfl⟩

theorem AnalyticPhaseFunction.uniformNorm_constReal {n : ℕ}
    (G : Set (ComplexSpace n)) (ρ : ℝ≥0) (hG : ConjInvariant G)
    (hne : G.Nonempty) (c : ℝ) :
    (AnalyticPhaseFunction.constReal G ρ hG c).uniformNorm = |c| := by
  apply le_antisymm
  · apply (AnalyticPhaseFunction.norm_le_iff _).2
    refine ⟨abs_nonneg c, ?_⟩
    intro x hx
    simp [AnalyticPhaseFunction.constReal, Complex.norm_real, Real.norm_eq_abs]
  · obtain ⟨p, hp⟩ := hne
    let x : phaseDomain G ρ := ⟨(p, complexify (0 : RealSpace n)),
      hp, complexify_mem_angleStrip 0 ρ⟩
    have h := norm_apply_le_supNorm
      (AnalyticPhaseFunction.constReal G ρ hG c).toBounded x
    simpa [AnalyticPhaseFunction.toBounded, boundedRestriction,
      AnalyticPhaseFunction.constReal, AnalyticPhaseFunction.uniformNorm,
      Complex.norm_real, Real.norm_eq_abs] using h

end KamProject.Arnold1963
