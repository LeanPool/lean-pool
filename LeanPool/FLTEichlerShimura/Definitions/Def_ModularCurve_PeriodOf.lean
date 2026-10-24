/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node ModularCurve_PeriodOf
(904c1b4e-c0ab-5de1-a189-92dd0af902d0) by Claude (2026-09-05).

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_CuspForm_Petersson
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_PeriodLattice
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_PeriodMapBundled

import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Periods, period lattice and Petersson product for general Γ

Definition: `ModularCurve_PeriodOf` (`904c1b4e-c0ab-5de1-a189-92dd0af902d0`), by Claude, 2026-09-05.

Fix a subgroup $\Gamma\le\mathrm{SL}_2(\mathbb Z)$. The first group of declarations sets up
integration of a weight-two cusp form along a straight segment in the upper half-plane: for
$\tau_0,\tau_1\in\mathfrak H$ and $f\in S_2(\Gamma)$ (Mathlib's `CuspForm Γ 2`),
[`ModularCurve.periodIntegrandOf`](../def/ModularCurve_PeriodOf.html#L21) is the function $t\mapsto
f\big((1-t)\tau_0+t\tau_1\big)(\tau_1-\tau_0)$, where the parameter is first clamped to $[0,1]$, so
the integrand is globally continuous, hence interval integrable, and is additive and $\mathbb
C$-homogeneous in $f$. Consequently $f\mapsto\int_0^1$ of this integrand is a $\mathbb C$-linear
functional [`ModularCurve.periodAlongOf Γ τ₀ τ₁`](../def/ModularCurve_PeriodOf.html#L42) on
$S_2(\Gamma)$, i.e. the functional $f\mapsto\int_{\tau_0}^{\tau_1}f(\tau)\,d\tau$ along the segment.
[`ModularCurve.periodOf Γ γ`](../def/ModularCurve_PeriodOf.html#L56) is this functional for the
segment from $i$ to $\gamma\cdot i$, and [`ModularCurve.periodLatticeOf
Γ`](../def/ModularCurve_PeriodOf.html#L65) is the $\mathbb Z$-submodule of the dual
$S_2(\Gamma)^\vee$ spanned by the range of $\gamma\mapsto\mathrm{periodOf}\,\Gamma\,\gamma$; each
$\mathrm{periodOf}\,\Gamma\,\gamma$ lies in it.

[`ModularCurve.HasEquivariantPrimitiveOf Γ f F`](../def/ModularCurve_PeriodOf.html#L71) is the
conjunction of four conditions on $F:\mathfrak H\to\mathbb C$: $F$ has complex derivative $f(\tau)$
at every $\tau$; $F\to 0$ as $\operatorname{Im}\tau\to\infty$; $F$ is an equivariant primitive in
the sense of [`ModularCurve.Period.IsEquivariantPrimitive`](../def/ModularCurve_PeriodMap.html#L12),
that is for each $\gamma\in\Gamma$ the difference $F(\gamma\cdot z)-F(z)$ is a constant independent
of $z$; and for every $\delta\in\mathrm{SL}_2(\mathbb Z)$ the function $w\mapsto F(\delta\cdot w)$
has a finite limit at $i\infty$. [`ModularCurve.periodMapOf Γ
f`](../def/ModularCurve_PeriodOf.html#L79) is the additive character
$\Gamma^{\mathrm{add}}\to\mathbb C$, $\gamma\mapsto F(\gamma\cdot i)-F(i)$, attached to a chosen
such $F$ when one exists, and $0$ otherwise; `periodMapOf_def` records that the value is realised by
some witness whenever one witness is given.

For an integer weight $k$, [`CuspForm.peterssonIntegrandOf Γ f
g`](../def/ModularCurve_PeriodOf.html#L112) is the (finitely supported) sum over the coset space
$\mathrm{SL}_2(\mathbb Z)/\Gamma$ of the pointwise Petersson densities `UpperHalfPlane.petersson k`
of the slash translates $f\mid_k q^{-1}$ and $g\mid_k q^{-1}$, taken at a chosen representative of
each coset, and [`CuspForm.peterssonOf Γ f g`](../def/ModularCurve_PeriodOf.html#L116) is its
integral over the standard fundamental domain `ModularGroup.fd` of $\mathrm{SL}_2(\mathbb Z)$ for
the restricted volume measure; no normalisation by the index is inserted. Four comparison lemmas
identify `periodAlongOf`, `periodOf`, `periodLatticeOf`, `HasEquivariantPrimitiveOf`, `periodMapOf`
and `peterssonOf` at $\Gamma=\Gamma_0(N)$ with the corresponding level-$N$ objects `periodAlong`,
`period`, `periodLattice`, `HasEquivariantPrimitive`, `periodMap` and `petersson`, these being the
same formulas written for a general subgroup.

**Relation to Mathlib.** Mathlib supplies the ambient notions used here — `CuspForm`, the weight-$k$
slash action, the pointwise Petersson density `UpperHalfPlane.petersson` and the fundamental domain
`ModularGroup.fd` — but not the period functionals, the period lattice, the notion of an equivariant
primitive or the globally integrated Petersson product; those are the project's own, and are given
here for an arbitrary subgroup of $\mathrm{SL}_2(\mathbb Z)$ alongside the project's
level-$\Gamma_0(N)$ versions.

**Where it is used.** The period lattice in the dual of $S_2(\Gamma_0(N))$ and the period map are
the analytic input to the Eichler–Shimura construction of the Hecke-stable lattice on which the
modular Galois representations are realised; the Petersson product serves as the pairing on spaces
of cusp forms. The comparison lemmas let statements formulated for a general subgroup be applied
verbatim at the levels $\Gamma_0(N)$ occurring in the level-lowering and modularity-lifting
arguments.

<!-- Generated by add_prove2me_provenance.py -->
-/

@[expose] public section publicSection

noncomputable section

open UpperHalfPlane Filter Topology

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Period

variable (Γ : Subgroup SL(2, ℤ))

def periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) (t : ℝ) : ℂ :=
  f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)

theorem continuous_periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    Continuous (periodIntegrandOf Γ τ₀ τ₁ f) :=
  ((f.holo'.continuous).comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const

theorem intervalIntegrable_periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) (a b : ℝ) :
    IntervalIntegrable (periodIntegrandOf Γ τ₀ τ₁ f) MeasureTheory.volume a b :=
  (continuous_periodIntegrandOf Γ τ₀ τ₁ f).intervalIntegrable a b

theorem periodIntegrandOf_add (τ₀ τ₁ : ℍ) (f g : CuspForm Γ 2) :
    periodIntegrandOf Γ τ₀ τ₁ (f + g) = periodIntegrandOf Γ τ₀ τ₁ f + periodIntegrandOf Γ τ₀ τ₁ g
      := by
  funext t
  simp [periodIntegrandOf, add_mul]

theorem periodIntegrandOf_smul (τ₀ τ₁ : ℍ) (c : ℂ) (f : CuspForm Γ 2) :
    periodIntegrandOf Γ τ₀ τ₁ (c • f) = fun t => c * periodIntegrandOf Γ τ₀ τ₁ f t := by
  funext t
  simp [periodIntegrandOf, mul_assoc]

def periodAlongOf (τ₀ τ₁ : ℍ) : Module.Dual ℂ (CuspForm Γ 2) where
  toFun f := ∫ t in (0 : ℝ)..1, periodIntegrandOf Γ τ₀ τ₁ f t
  map_add' f g := by
    rw [periodIntegrandOf_add]
    exact intervalIntegral.integral_add (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1)
      (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ g 0 1)
  map_smul' c f := by
    rw [periodIntegrandOf_smul, RingHom.id_apply, smul_eq_mul]
    exact intervalIntegral.integral_const_mul c _

theorem periodAlongOf_apply (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    periodAlongOf Γ τ₀ τ₁ f = ∫ t in (0 : ℝ)..1, f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) :=
  rfl

def periodOf (γ : Γ) : Module.Dual ℂ (CuspForm Γ 2) :=
  periodAlongOf Γ UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)

theorem periodOf_apply (γ : Γ) (f : CuspForm Γ 2) :
    periodOf Γ γ f =
      ∫ t in (0 : ℝ)..1, f (segmentPath UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) t) *
        ((((γ : SL(2, ℤ)) • UpperHalfPlane.I : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)) :=
  rfl

def periodLatticeOf : Submodule ℤ (Module.Dual ℂ (CuspForm Γ 2)) :=
  Submodule.span ℤ (Set.range (periodOf Γ))

theorem periodOf_mem_periodLatticeOf (γ : Γ) : periodOf Γ γ ∈ periodLatticeOf Γ :=
  Submodule.subset_span (Set.mem_range_self γ)

def HasEquivariantPrimitiveOf (f : CuspForm Γ 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    Period.IsEquivariantPrimitive Γ F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in
def periodMapOf (f : CuspForm Γ 2) : Additive Γ →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitiveOf Γ f F then h.choose_spec.2.2.1.periodHom else 0

theorem periodMapOf_def (f : CuspForm Γ 2) {F : ℍ → ℂ} (hF : HasEquivariantPrimitiveOf Γ f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitiveOf Γ f F₀), periodMapOf Γ f = h₀.2.2.1.periodHom
      := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitiveOf Γ f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dite_eq_left h⟩

theorem periodAlongOf_gamma0 (N : ℕ) (τ₀ τ₁ : ℍ) :
    periodAlongOf (CongruenceSubgroup.Gamma0 N) τ₀ τ₁ = periodAlong N τ₀ τ₁ := rfl

theorem periodOf_gamma0 (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    periodOf (CongruenceSubgroup.Gamma0 N) γ = period N γ := rfl

theorem periodLatticeOf_gamma0 (N : ℕ) :
    periodLatticeOf (CongruenceSubgroup.Gamma0 N) = periodLattice N := rfl

theorem hasEquivariantPrimitiveOf_gamma0_iff (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (F : ℍ → ℂ) : HasEquivariantPrimitiveOf (CongruenceSubgroup.Gamma0 N) f F ↔
      HasEquivariantPrimitive N f F := Iff.rfl

theorem periodMapOf_gamma0 (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodMapOf (CongruenceSubgroup.Gamma0 N) f = periodMap N f := rfl

end Period

end ModularCurve

namespace CuspForm

variable (Γ : Subgroup SL(2, ℤ)) {k : ℤ}

def peterssonIntegrandOf (f g : CuspForm Γ k) (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (⇑f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (⇑g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def peterssonOf (f g : CuspForm Γ k) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd) (peterssonIntegrandOf Γ f
    g)

theorem peterssonOf_def (f g : CuspForm Γ k) :
    peterssonOf Γ f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonIntegrandOf Γ f g) := rfl

theorem peterssonIntegrandOf_gamma0 {N : ℕ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    peterssonIntegrandOf (CongruenceSubgroup.Gamma0 N) f g = peterssonIntegrand f g := rfl

theorem peterssonOf_gamma0 {N : ℕ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    peterssonOf (CongruenceSubgroup.Gamma0 N) f g = petersson f g := rfl

end CuspForm

end

end publicSection
