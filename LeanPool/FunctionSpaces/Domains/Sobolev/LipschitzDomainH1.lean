/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley
public import LeanPool.FunctionSpaces.Domains.Traces.LipschitzBoundaryTrace
public import LeanPool.FunctionSpaces.Domains.Sobolev.SobolevRestrictionSpaces

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# `H^1` on bounded Lipschitz domains

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner product
space `V`, such as `ℝ^d`, with Lebesgue measure. The Sobolev space `H^1(Ω)` is the space of
restrictions of `H^1(V) = W^1_2(V)` (`Rd.BoundedLipschitzDomain.MemSobolevOn`): `f ∈ L_2(V)` lies
in `H^1(Ω)` if it agrees almost everywhere on `Ω` with some `F ∈ W^1_2(V)`; membership depends
only on the values of `f` on `Ω` (`Rd.BoundedLipschitzDomain.MemSobolevOn.congr_ae`). The open
set `Ω` has finite measure (`Rd.BoundedLipschitzDomain.isFiniteMeasure_volume_restrict`).

* **The intrinsic description** (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_modulusOn`):
  `f ∈ H^1(Ω)` iff `‖f‖_{L_2(Ω)} + ‖(2^k ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞`, for every order
  `r ≥ 2`, by `W^1_2(V) = B^1_{2,2}(V)` and the extension theorem for bounded Lipschitz domains.
  This quantity is at most `‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2}` for every `F` with `F = f`
  on `Ω` (`Rd.BoundedLipschitzDomain.modNormOn_le_modNorm_of_ae_eq`).
* **The Hilbert space** (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`):
  `f ∈ H^1(Ω)` iff its restriction to `Ω` is `u|_Ω` for some `u` in the Hilbert space `H^1(Ω)`
  of restrictions of Mathlib's `H^1(V)` (`Rd.RestrictionSpace`).
* **The weak gradient** (`Rd.BoundedLipschitzDomain.MemSobolevOn.memWeakSobolev`): every
  `f ∈ H^1(Ω)` lies in `W^1_2(Ω)`, so its weak derivatives on `Ω` exist and lie in `L_2(Ω)`.
  This direction holds by the definition through extensions; the converse is the extension
  theorem (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`).
* **The trace**: every `f ∈ H^1(Ω)` has a boundary trace in `B^{1/2}_{2,2}(Γ)`, unique almost
  everywhere on `Γ` (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memSobolevOn`,
  `Rd.BoundedLipschitzDomain.MemSobolevOn.isBoundaryTrace_unique`), and the boundary traces of the
  functions of `H^1(Ω)` are the functions of `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_memSobolevOn`). The extensions in the
  definition of the boundary trace are the `F ∈ W^1_2(V)` with `F = f` on `Ω`
  (`Rd.BoundedLipschitzDomain.isBoundaryTrace_iff_forall_memSobolev`), and `f` has the boundary
  trace `g` with a finite intrinsic norm iff `f ∈ H^1(Ω)` and `g` is its boundary trace
  (`Rd.BoundedLipschitzDomain.hasBoundaryTrace_iff_memSobolevOn`).
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The open set of a bounded Lipschitz domain, as an element of Mathlib's `Opens V`, the form
in which open sets carry distributions and weak derivatives. -/
def BoundedLipschitzDomain.toOpens (Ω : BoundedLipschitzDomain V) : Opens V :=
  ⟨Ω.carrier, Ω.isOpen⟩

/-- The points of `Ω.toOpens` are the points of `Ω`. -/
@[simp]
theorem BoundedLipschitzDomain.coe_toOpens (Ω : BoundedLipschitzDomain V) :
    (Ω.toOpens : Set V) = Ω.carrier :=
  rfl

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Lebesgue measure restricted to a bounded Lipschitz domain is finite, as the domain is
bounded. -/
instance BoundedLipschitzDomain.isFiniteMeasure_volume_restrict (Ω : BoundedLipschitzDomain V) :
    IsFiniteMeasure (volume.restrict (Ω.toOpens : Set V)) :=
  isFiniteMeasure_restrict.2 Ω.isBounded.measure_lt_top.ne

/-! ### The restriction space `H^1(Ω)` -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The Sobolev space `H^1(Ω)`** of a bounded Lipschitz domain, as the space of restrictions:
`f ∈ L_2(V)` lies in `H^1(Ω)` if `f = F` almost everywhere on `Ω` for some `F ∈ W^1_2(V)`, which is
Mathlib's `H^1(V)` (`Rd.memSobolev_one_iff`). Only the values of `f` on `Ω` matter
(`Rd.BoundedLipschitzDomain.MemSobolevOn.congr_ae`). By this definition every such `f` lies in
the Sobolev space `W^1_2(Ω)` of weak derivatives on `Ω`
(`Rd.BoundedLipschitzDomain.MemSobolevOn.memWeakSobolev`); the converse is the extension theorem
of Calderón and Stein (Stein 1970, Chapter VI;
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`). -/
def MemSobolevOn (f : Lp ℂ 2 (volume : Measure V)) : Prop :=
  ∃ F : Lp ℂ 2 (volume : Measure V), MemSobolev 1 F ∧
    (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f

variable {Ω}

/-- Every `f ∈ W^1_2(V)` lies in `H^1(Ω)`. -/
theorem memSobolevOn_of_memSobolev {f : Lp ℂ 2 (volume : Measure V)} (hf : MemSobolev 1 f) :
    Ω.MemSobolevOn f :=
  ⟨f, hf, Filter.EventuallyEq.rfl⟩

/-- The zero class lies in `H^1(Ω)`. -/
theorem zero_memSobolevOn : Ω.MemSobolevOn 0 :=
  memSobolevOn_of_memSobolev zero_memSobolev

/-- `H^1(Ω)` only sees `f` almost everywhere on `Ω`. -/
theorem MemSobolevOn.congr_ae {f f' : Lp ℂ 2 (volume : Measure V)} (hf : Ω.MemSobolevOn f)
    (h : (f : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f') : Ω.MemSobolevOn f' := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact ⟨F, hF, hFf.trans h⟩

/-- `H^1(Ω)` is closed under addition. -/
theorem MemSobolevOn.add {f f' : Lp ℂ 2 (volume : Measure V)} (hf : Ω.MemSobolevOn f)
    (hf' : Ω.MemSobolevOn f') : Ω.MemSobolevOn (f + f') := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨F', hF', hFf'⟩ := hf'
  have h1 : ⇑(F + F') =ᵐ[volume.restrict Ω.carrier] ⇑F + ⇑F' :=
    ae_restrict_of_ae (Lp.coeFn_add F F')
  have h2 : ⇑(f + f') =ᵐ[volume.restrict Ω.carrier] ⇑f + ⇑f' :=
    ae_restrict_of_ae (Lp.coeFn_add f f')
  exact ⟨F + F', hF.add hF', h1.trans ((hFf.add hFf').trans h2.symm)⟩

/-- `H^1(Ω)` is closed under multiplication by complex scalars. -/
theorem MemSobolevOn.smul {f : Lp ℂ 2 (volume : Measure V)} (hf : Ω.MemSobolevOn f) (c : ℂ) :
    Ω.MemSobolevOn (c • f) := by
  obtain ⟨F, hF, hFf⟩ := hf
  have h1 : ⇑(c • F) =ᵐ[volume.restrict Ω.carrier] c • ⇑F :=
    ae_restrict_of_ae (Lp.coeFn_smul c F)
  have h2 : ⇑(c • f) =ᵐ[volume.restrict Ω.carrier] c • ⇑f :=
    ae_restrict_of_ae (Lp.coeFn_smul c f)
  exact ⟨c • F, hF.smul c, h1.trans ((hFf.const_smul c).trans h2.symm)⟩

variable (Ω)

/-- **`H^1(Ω)` by restrictions of `B^1_{2,2}(V)`**: `f ∈ H^1(Ω)` iff `f` agrees on `Ω` with some
`F` in the approximation space `A^1_2` of the band-limited functions on `V`
(`Rd.memSobolev_one_iff_memApprox`). -/
theorem memSobolevOn_iff_exists_memApprox (f : Lp ℂ 2 (volume : Measure V)) :
    Ω.MemSobolevOn f ↔ ∃ F : Lp ℂ 2 (volume : Measure V),
      indicatorLp Ω.measurableSet F = indicatorLp Ω.measurableSet f ∧
        (bandScheme two_ne_top).MemApprox 1 2 F := by
  refine exists_congr fun F => ?_
  rw [memSobolev_one_iff_memApprox, indicatorLp_eq_iff_ae_eq_restrict, and_comm]

/-- **`H^1(Ω)` by intrinsic differences**: for every order `r ≥ 2`, `f ∈ L_2(V)` lies in `H^1(Ω)`
iff `‖f‖_{L_2(Ω)} + ‖(2^k ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞`, with the moduli of smoothness of `f`
inside `Ω`. This is the extension theorem for bounded Lipschitz domains
(`Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff`) at `p = q = 2`, `s = 1`. -/
theorem memSobolevOn_iff_modulusOn {r : ℕ} (hr : 2 ≤ r) (f : Lp ℂ 2 (volume : Measure V)) :
    Ω.MemSobolevOn f ↔ modNormOn Ω.measurableSet r 1 2 f < ∞ := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hr
  rw [memSobolevOn_iff_exists_memApprox,
    Ω.exists_memApprox_extension_iff two_ne_top one_pos hr' one_le_two f]

/-- **The intrinsic norm is at most the norm of every extension**: for every order `r` and all
`F, f ∈ L_2(V)` with `F = f` almost everywhere on `Ω`,
`‖f‖_{L_2(Ω)} + ‖(2^k ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_2} ≤ ‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2}`
(`Rd.modNormOn_le_modNorm_of_indicatorLp`). For `F ∈ W^1_2(V)` this bounds the intrinsic
quantity of `f ∈ H^1(Ω)` by the `B^1_{2,2}(V)` quantity of its extension `F`, with constant `1`. -/
theorem modNormOn_le_modNorm_of_ae_eq (r : ℕ) {F f : Lp ℂ 2 (volume : Measure V)}
    (hFf : (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f) :
    modNormOn Ω.measurableSet r 1 2 f ≤
      ‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 r F k) :=
  modNormOn_le_modNorm_of_indicatorLp Ω.measurableSet r 1 2
    ((indicatorLp_eq_iff_ae_eq_restrict _).2 hFf)

variable {Ω}

/-- **Extensions with finite Besov norm**: for every order `r ≥ 2`, every `f ∈ H^1(Ω)` agrees on
`Ω` with some `F ∈ L_2(V)` with `‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2} < ∞`. -/
theorem MemSobolevOn.exists_modNorm_lt_top {r : ℕ} (hr : 2 ≤ r)
    {f : Lp ℂ 2 (volume : Measure V)} (hf : Ω.MemSobolevOn f) :
    ∃ F : Lp ℂ 2 (volume : Measure V),
      indicatorLp Ω.measurableSet F = indicatorLp Ω.measurableSet f ∧
        ‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 r F k) < ∞ := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact ⟨F, (indicatorLp_eq_iff_ae_eq_restrict _).2 hFf, (memSobolev_one_iff_modulus hr F).1 hF⟩

/-! ### The weak gradient -/

/-- **Functions of `H^1(Ω)` are weakly differentiable on `Ω`**: every `f ∈ H^1(Ω)` lies in the
Sobolev space `W^1_2(Ω)`, that is, `f ∈ L_2(Ω)` and every weak derivative `∂_v f` exists on `Ω`
and lies in `L_2(Ω)`. The extension `F ∈ W^1_2(V)` has these weak derivatives on `V`; they restrict
to `Ω` (`Rd.MemWeakSobolev.mono_set`), and `F = f` on `Ω`. -/
theorem MemSobolevOn.memWeakSobolev {f : Lp ℂ 2 (volume : Measure V)} (hf : Ω.MemSobolevOn f) :
    MemWeakSobolev Ω.toOpens 1 2 f := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact (MemWeakSobolev.mono_set hF le_top).congr_ae hFf

/-! ### The trace -/

variable (Ω)

/-- **Boundary traces of `H^1` functions**: for `L = 2`, `σ = 1` and `q = 2`, the functions `F` in
the definition of a boundary trace (`Rd.BoundedLipschitzDomain.IsBoundaryTrace`) are the
`F ∈ W^1_2(V)` with `F = f` almost everywhere on `Ω` (`Rd.memSobolev_one_iff_modulus` with
`r = 2`): `g` is the boundary trace of `f` iff `Tr_Γ F = g` almost everywhere on `Γ` for every such
`F`. -/
theorem isBoundaryTrace_iff_forall_memSobolev (ψ : Ω.BoundaryPartition)
    (f : Lp ℂ 2 (volume : Measure V)) (g : V → ℂ) :
    Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g ↔ ∀ F : Lp ℂ 2 (volume : Measure V), MemSobolev 1 F →
      (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f →
        Ω.boundaryTrace ψ two_ne_top 2 F =ᶠ[Ω.aeBoundary] g := by
  unfold IsBoundaryTrace
  refine forall_congr' fun F => ?_
  rw [memSobolev_one_iff_modulus le_rfl F, indicatorLp_eq_iff_ae_eq_restrict]
  exact ⟨fun h hF hFf => h hFf hF, fun h hFf hF => h hF hFf⟩

/-- **Boundary traces of `H^1` functions with a finite intrinsic norm**: for `L = 2`, `σ = 1` and
`q = 2`, `f` has the boundary trace `g` (`Rd.BoundedLipschitzDomain.HasBoundaryTrace`) iff
`f ∈ H^1(Ω)` and `g` is the boundary trace of `f`, since the finite intrinsic norm describes
`H^1(Ω)` (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_modulusOn` with `r = 2`). -/
theorem hasBoundaryTrace_iff_memSobolevOn (ψ : Ω.BoundaryPartition)
    (f : Lp ℂ 2 (volume : Measure V)) (g : V → ℂ) :
    Ω.HasBoundaryTrace ψ two_ne_top 2 1 2 f g ↔
      Ω.MemSobolevOn f ∧ Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g := by
  rw [hasBoundaryTrace_iff, Ω.memSobolevOn_iff_modulusOn le_rfl f]

/-- **The trace space of `H^1(Ω)`**: for every resolution of unity `ψ` on the boundary `Γ`, a
function `g` on `Γ` lies in `B^{1/2}_{2,2}(Γ)` iff it is the boundary trace of some `f ∈ H^1(Ω)`.
This is the trace space of bounded Lipschitz domains
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`) at `p = q = 2`,
`s = 1/2`, where `s + 1/p = 1`, with the intrinsic description of `H^1(Ω)`. -/
theorem memBoundaryBesov_iff_exists_memSobolevOn (ψ : Ω.BoundaryPartition) (g : V → ℂ) :
    Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g ↔ ∃ f : Lp ℂ 2 (volume : Measure V),
      Ω.MemSobolevOn f ∧ Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g := by
  have hσ : (1 / 2 : ℝ) + 1 / (2 : ℝ≥0∞).toReal = 1 := by norm_num
  rw [Ω.memBoundaryBesov_iff_exists_isBoundaryTrace ψ two_ne_top le_rfl (s := 1 / 2)
    (by norm_num) (by norm_num) one_le_two g, hσ]
  exact exists_congr fun f => and_congr_left' (Ω.memSobolevOn_iff_modulusOn le_rfl f).symm

variable {Ω}

/-- **The boundary trace of a function of `H^1(Ω)`**: for every resolution of unity `ψ` on the
boundary `Γ`, every `f ∈ H^1(Ω)` has a boundary trace `g ∈ B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_modNormOn_lt_top` at `p = q = 2`,
`s = 1/2`, where `s + 1/p = 1`, with the intrinsic description of `H^1(Ω)`). -/
theorem exists_isBoundaryTrace_of_memSobolevOn (ψ : Ω.BoundaryPartition)
    {f : Lp ℂ 2 (volume : Measure V)} (hf : Ω.MemSobolevOn f) :
    ∃ g : V → ℂ, Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g ∧
      Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g := by
  have hσ : (1 / 2 : ℝ) + 1 / (2 : ℝ≥0∞).toReal = 1 := by norm_num
  obtain ⟨g, hg, hfg⟩ := Ω.exists_isBoundaryTrace_of_modNormOn_lt_top ψ two_ne_top le_rfl
    (s := 1 / 2) (by norm_num) (by norm_num) one_le_two
    (by rw [hσ]; exact (Ω.memSobolevOn_iff_modulusOn le_rfl f).1 hf)
  rw [hσ] at hfg
  exact ⟨g, hg, hfg⟩

/-- **Every function of `B^{1/2}_{2,2}(Γ)` is the boundary trace of a function of `H^1(Ω)`**: for
every resolution of unity `ψ` on `Γ` and every `g ∈ B^{1/2}_{2,2}(Γ)` there is `f ∈ H^1(Ω)` with
boundary trace `g` (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_memSobolevOn`). -/
theorem exists_memSobolevOn_of_memBoundaryBesov (ψ : Ω.BoundaryPartition) {g : V → ℂ}
    (hg : Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g) :
    ∃ f : Lp ℂ 2 (volume : Measure V), Ω.MemSobolevOn f ∧
      Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g :=
  (Ω.memBoundaryBesov_iff_exists_memSobolevOn ψ g).1 hg

/-- **The boundary trace of a function of `H^1(Ω)` is unique** up to null sets of the boundary:
for every resolution of unity `ψ` on `Γ`, two boundary traces `g`, `g'` of `f ∈ H^1(Ω)` agree
almost everywhere on `Γ` (`Rd.BoundedLipschitzDomain.IsBoundaryTrace.unique` with the intrinsic
description of `H^1(Ω)`). -/
theorem MemSobolevOn.isBoundaryTrace_unique (ψ : Ω.BoundaryPartition)
    {f : Lp ℂ 2 (volume : Measure V)} (hf : Ω.MemSobolevOn f) {g g' : V → ℂ}
    (hg : Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g)
    (hg' : Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g') : g =ᶠ[Ω.aeBoundary] g' :=
  hg.unique one_pos (by norm_num) one_le_two ((Ω.memSobolevOn_iff_modulusOn le_rfl f).1 hf) hg'

open scoped BesselPotentialSpace in
/-- **The predicate and the type agree**: for a bounded Lipschitz domain `Ω`, `f ∈ L_2(V)` lies
in `H^1(Ω)` in the sense of `Rd.BoundedLipschitzDomain.MemSobolevOn` iff its restriction to `Ω`
is `u|_Ω` for some `u` in the Hilbert space `H^1(Ω)`. -/
theorem memSobolevOn_iff_exists_restrictL2 (Ω : BoundedLipschitzDomain V)
    (f : Lp ℂ 2 (volume : Measure V)) :
    Ω.MemSobolevOn f ↔ ∃ u : RestrictionSpace 1 Ω.toOpens,
      restrictL2 Ω.toOpens u = LpToLpRestrictCLM V ℂ ℂ volume 2 Ω.carrier f := by
  constructor
  · rintro ⟨F, hF, hFf⟩
    have hS := (memSobolev_one_iff F).1 hF
    have hU : toL2 hS.toBesselPotentialSpace = F :=
      toL2_eq_of_toDistr_eq _ hS.toBesselPotentialSpace_toDistr.symm
    refine ⟨restrictProj 1 Ω.toOpens hS.toBesselPotentialSpace, ?_⟩
    rw [restrictL2_restrictProj, hU]
    exact Lp.ext ((LpToLpRestrictCLM_coeFn ℂ _ _).trans
      (hFf.trans (LpToLpRestrictCLM_coeFn ℂ _ _).symm))
  · rintro ⟨u, hu⟩
    refine ⟨toL2 (u : H^{1}(V)), memSobolev_toL2 _, ?_⟩
    exact (restrictL2_eq_iff_ae_eq u f).1 hu

end BoundedLipschitzDomain

end Rd
