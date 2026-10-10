/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Functions

/-!
Restrictions, sums, differences, and uniform norm bounds for analytic phase functions.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963

theorem NormBoundOn.mono {E F : Type*} [NormedAddCommGroup F]
    {f : E → F} {S T : Set E} {M : ℝ} (h : NormBoundOn f S M) (hTS : T ⊆ S) :
    NormBoundOn f T M := ⟨h.nonneg, fun _ hx => h.norm_le (hTS hx)⟩

theorem NormBoundOn.add {E F : Type*} [NormedAddCommGroup F]
    {f g : E → F} {S : Set E} {M N : ℝ}
    (hf : NormBoundOn f S M) (hg : NormBoundOn g S N) :
    NormBoundOn (fun x => f x + g x) S (M + N) :=
  ⟨add_nonneg hf.nonneg hg.nonneg, fun _ hx =>
    (norm_add_le _ _).trans (add_le_add (hf.norm_le hx) (hg.norm_le hx))⟩

theorem NormBoundOn.sub {E F : Type*} [NormedAddCommGroup F]
    {f g : E → F} {S : Set E} {M N : ℝ}
    (hf : NormBoundOn f S M) (hg : NormBoundOn g S N) :
    NormBoundOn (fun x => f x - g x) S (M + N) :=
  ⟨add_nonneg hf.nonneg hg.nonneg, fun _ hx =>
    (norm_sub_le _ _).trans (add_le_add (hf.norm_le hx) (hg.norm_le hx))⟩

namespace AnalyticPhaseFunction
variable {n : ℕ} {G U : Set (ComplexSpace n)} {ρ σ : ℝ≥0}

/-- Restriction to a conjugation-invariant action subdomain and a narrower angle strip. -/
def restrict (f : AnalyticPhaseFunction n G ρ) (hUG : U ⊆ G)
    (hσρ : σ ≤ ρ) (hU : ConjInvariant U) : AnalyticPhaseFunction n U σ where
  toFun := f.toFun
  domain_conj := hU
  analytic := f.analytic.mono (Set.prod_mono hUG (angleStrip_mono hσρ))
  periodic := fun p hp q hq k => f.periodic p (hUG hp) q (angleStrip_mono hσρ hq) k
  conj_compatible := fun z hz => f.conj_compatible z ⟨hUG hz.1, angleStrip_mono hσρ hz.2⟩
  bounded := ⟨f.uniformNorm, ((f.norm_le_iff).mp le_rfl).mono
    (Set.prod_mono hUG (angleStrip_mono hσρ))⟩

theorem uniformNorm_restrict_le (f : AnalyticPhaseFunction n G ρ)
    (hUG : U ⊆ G) (hσρ : σ ≤ ρ) (hU : ConjInvariant U) :
    (f.restrict hUG hσρ hU).uniformNorm ≤ f.uniformNorm :=
  (norm_le_iff _).mpr (((f.norm_le_iff).mp le_rfl).mono
    (Set.prod_mono hUG (angleStrip_mono hσρ)))

/-- Addition of analytic phase functions on the same domain and strip. -/
def add (f g : AnalyticPhaseFunction n G ρ) : AnalyticPhaseFunction n G ρ where
  toFun := fun z => f.toFun z + g.toFun z
  domain_conj := f.domain_conj
  analytic := f.analytic.add g.analytic
  periodic := by intro p hp q hq k; dsimp only; rw [f.periodic p hp q hq k, g.periodic p hp q hq k]
  conj_compatible := by
    intro z hz
    dsimp only
    rw [f.conj_compatible z hz, g.conj_compatible z hz, star_add]
  bounded := ⟨_, ((f.norm_le_iff).mp le_rfl).add ((g.norm_le_iff).mp le_rfl)⟩

/-- Subtraction of analytic phase functions on the same domain and strip. -/
def sub (f g : AnalyticPhaseFunction n G ρ) : AnalyticPhaseFunction n G ρ where
  toFun := fun z => f.toFun z - g.toFun z
  domain_conj := f.domain_conj
  analytic := f.analytic.sub g.analytic
  periodic := by intro p hp q hq k; dsimp only; rw [f.periodic p hp q hq k, g.periodic p hp q hq k]
  conj_compatible := by
    intro z hz
    dsimp only
    rw [f.conj_compatible z hz, g.conj_compatible z hz, star_sub]
  bounded := ⟨_, ((f.norm_le_iff).mp le_rfl).sub ((g.norm_le_iff).mp le_rfl)⟩

theorem uniformNorm_add_le (f g : AnalyticPhaseFunction n G ρ) :
    (f.add g).uniformNorm ≤ f.uniformNorm + g.uniformNorm :=
  (norm_le_iff _).mpr (((f.norm_le_iff).mp le_rfl).add ((g.norm_le_iff).mp le_rfl))

theorem uniformNorm_sub_le (f g : AnalyticPhaseFunction n G ρ) :
    (f.sub g).uniformNorm ≤ f.uniformNorm + g.uniformNorm :=
  (norm_le_iff _).mpr (((f.norm_le_iff).mp le_rfl).sub ((g.norm_le_iff).mp le_rfl))

/-- Addition after restricting both functions to their common phase domain. -/
def addOnInter {H : Set (ComplexSpace n)} {τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ) :
    AnalyticPhaseFunction n (G ∩ H) (min ρ τ) :=
  let hI : ConjInvariant (G ∩ H) := fun p hp =>
    ⟨f.domain_conj p hp.1, g.domain_conj p hp.2⟩
  (f.restrict Set.inter_subset_left (min_le_left _ _) hI).add
    (g.restrict Set.inter_subset_right (min_le_right _ _) hI)

/-- Subtraction after restricting both functions to their common phase domain. -/
def subOnInter {H : Set (ComplexSpace n)} {τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ) :
    AnalyticPhaseFunction n (G ∩ H) (min ρ τ) :=
  let hI : ConjInvariant (G ∩ H) := fun p hp =>
    ⟨f.domain_conj p hp.1, g.domain_conj p hp.2⟩
  (f.restrict Set.inter_subset_left (min_le_left _ _) hI).sub
    (g.restrict Set.inter_subset_right (min_le_right _ _) hI)

@[simp] theorem addOnInter_toFun {H : Set (ComplexSpace n)} {τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ)
    (z : ComplexPhaseSpace n) : (f.addOnInter g).toFun z = f.toFun z + g.toFun z := rfl

@[simp] theorem subOnInter_toFun {H : Set (ComplexSpace n)} {τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ)
    (z : ComplexPhaseSpace n) : (f.subOnInter g).toFun z = f.toFun z - g.toFun z := rfl

theorem uniformNorm_addOnInter_le {H : Set (ComplexSpace n)} {τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ) :
    (f.addOnInter g).uniformNorm ≤ f.uniformNorm + g.uniformNorm :=
  (uniformNorm_add_le _ _).trans
    (add_le_add (f.uniformNorm_restrict_le _ _ _) (g.uniformNorm_restrict_le _ _ _))

theorem uniformNorm_subOnInter_le {H : Set (ComplexSpace n)} {τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ) :
    (f.subOnInter g).uniformNorm ≤ f.uniformNorm + g.uniformNorm :=
  (uniformNorm_sub_le _ _).trans
    (add_le_add (f.uniformNorm_restrict_le _ _ _) (g.uniformNorm_restrict_le _ _ _))

end AnalyticPhaseFunction
end KamProject.Arnold1963
