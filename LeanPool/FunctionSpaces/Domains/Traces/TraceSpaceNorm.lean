/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.SurfaceMeasure
public import LeanPool.FunctionSpaces.Domains.Traces.BoundaryBesovNorm

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The norm of the trace space of a bounded Lipschitz domain

Let `Ω` be a bounded Lipschitz domain with boundary `Γ`, `H^1(Ω)` its Sobolev space, and
`H^{1/2}(Γ)` the trace space, the orthogonal complement of the trace kernel in `H^1(Ω)`
(`Rd.BoundedLipschitzDomain.TraceSpace`). For `U ∈ H^1(V)` with `L_2` function `ι U`, `Tr_Γ ι U`
is its boundary trace.

* **The least extension norm** (`Rd.BoundedLipschitzDomain.enorm_eq_iInf`): the norm of
  `t ∈ H^{1/2}(Γ)` is the least `H^1(V)` norm of a function with the boundary trace of `t`, the
  quotient norm of `γ(H^1(Ω))`, which McLean, Theorem 3.37, shows to be equivalent to his chart
  norm of `H^{1/2}(Γ)`. The restriction to `Ω` keeps the boundary trace
  (`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`) and does not increase the norm.
* **The norm equivalence** (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`): for every
  resolution of unity `ψ` there is `C < ∞` with `‖t‖ ≤ C ‖τ t‖_{B^{1/2}_{2,2}(Γ)}` and
  `‖τ t‖_{B^{1/2}_{2,2}(Γ)} ≤ C ‖t‖` for the quasi-norm by chart pieces
  (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`): the trace bound for `p = q = L = 2`,
  `s = 1/2`, with `H^1(V) ⊆ B^1_{2,2}(V)` (`Rd.modNorm_two_le_norm`), and the bounded extension
  with the bound of `H^1(V)` by `B^1_{2,2}(V)` (`Rd.enorm_le_modNorm_two`). Every
  `g ∈ B^{1/2}_{2,2}(Γ)` has a preimage under the trace of norm at most `C ‖g‖`
  (`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov_le`).
* **The range** of `τ : H^{1/2}(Γ) → L_2(Γ)` is `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`).
* **The Banach space `B^{1/2}_{2,2}(Γ)`** (`Rd.BoundedLipschitzDomain.BoundaryBesovHalf`): the
  functions of `L_2(Γ)` in `B^{1/2}_{2,2}(Γ)`, for the canonical resolution of unity, with the
  quasi-norm by chart pieces, a norm here; `τ` is an isomorphism of `H^{1/2}(Γ)` onto it
  (`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesovHalf`), so it is complete. The trace
  `H^1(Ω) → B^{1/2}_{2,2}(Γ)` has a bounded linear right inverse, as in McLean's Theorem 3.37
  (`Rd.BoundedLipschitzDomain.traceRightInverse`).
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped ENNReal BesselPotentialSpace

open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : BoundedLipschitzDomain V)

/-! ### The norm of the trace space as a least extension norm -/

/-- **The restriction to `Ω` keeps the boundary trace**: for every resolution of unity `ψ` and
`U ∈ H^1(V)`, `Tr_Γ ι(U|_Ω) = Tr_Γ ι U` almost everywhere on `Γ`, since `U - U|_Ω` vanishes on `Ω`
(`Rd.sub_restrictProj_mem`, `Rd.mem_vanishOn_one_iff`) and the boundary trace depends only on the
function on `Ω` (`Rd.BoundedLipschitzDomain.boundaryTrace_congr`). -/
theorem boundaryTrace_restrictProj (ψ : Ω.BoundaryPartition) (U : H^{1}(V)) :
    Ω.boundaryTrace ψ two_ne_top 2
        (toL2 ((restrictProj 1 Ω.toOpens U : Ω.SobolevOne) : H^{1}(V))) =ᶠ[Ω.aeBoundary]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) := by
  have h := (mem_vanishOn_one_iff _).1 (sub_restrictProj_mem (s := 1) (Ω := Ω.toOpens) U)
  rw [Ω.coe_toOpens] at h
  replace h := (ae_restrict_iff' Ω.measurableSet).1 h
  refine Ω.boundaryTrace_congr ψ two_ne_top one_le_two (s := 1 / 2) (by norm_num) (by norm_num)
    one_le_two (modNorm_toL2_lt_top _) (modNorm_toL2_lt_top U) ?_
  filter_upwards [h, Lp.coeFn_sub (toL2 U)
    (toL2 ((restrictProj 1 Ω.toOpens U : Ω.SobolevOne) : H^{1}(V)))] with x hx hsub hxΩ
  have hx' := hx hxΩ
  rw [map_sub, hsub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx'
  exact hx'.symm

/-- The trace of the restriction to `Ω` has norm at most that of `U ∈ H^1(V)`:
`‖γ(U|_Ω)‖ ≤ ‖U|_Ω‖ ≤ ‖U‖` (`Rd.BoundedLipschitzDomain.norm_trace_apply_le`,
`Rd.norm_restrictProj_apply_le`). -/
theorem enorm_trace_restrictProj_le (U : H^{1}(V)) :
    ‖Ω.trace (restrictProj 1 Ω.toOpens U)‖ₑ ≤ ‖U‖ₑ :=
  eNorm_le_iff_norm_le.2 ((Ω.norm_trace_apply_le _).trans (norm_restrictProj_apply_le U))

/-- **Functions with the boundary trace of `t` restrict to extensions of `t`**: for every
resolution of unity `ψ`, if `Tr_Γ ι U = Tr_Γ ι(E t)` almost everywhere on `Γ`, then `γ(U|_Ω) = t`
(`Rd.BoundedLipschitzDomain.trace_eq_iff`, `Rd.BoundedLipschitzDomain.trace_extend`). -/
theorem trace_restrictProj_eq (ψ : Ω.BoundaryPartition) {U : H^{1}(V)} {t : Ω.TraceSpace}
    (h : Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) =ᶠ[Ω.aeBoundary]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)))) :
    Ω.trace (restrictProj 1 Ω.toOpens U) = t :=
  ((Ω.trace_eq_iff ψ _ _).2 ((Ω.boundaryTrace_restrictProj ψ U).trans h)).trans (Ω.trace_extend t)

/-- `‖t‖ ≤ ‖U‖` for every `U ∈ H^1(V)` with the boundary trace of `t ∈ H^{1/2}(Γ)`, for every
resolution of unity (`Rd.BoundedLipschitzDomain.trace_restrictProj_eq`). -/
theorem enorm_le_of_boundaryTrace_eventuallyEq (ψ : Ω.BoundaryPartition) {U : H^{1}(V)}
    {t : Ω.TraceSpace}
    (h : Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) =ᶠ[Ω.aeBoundary]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)))) :
    ‖t‖ₑ ≤ ‖U‖ₑ := by
  rw [← Ω.trace_restrictProj_eq ψ h]
  exact Ω.enorm_trace_restrictProj_le U

/-- **The norm of `H^{1/2}(Γ)` is the least extension norm** (the quotient norm of `γ(H^1(Ω))`,
which McLean, Theorem 3.37, shows to be equivalent to his chart norm of `H^{1/2}(Γ)`): for every
resolution of unity `ψ` and `t ∈ H^{1/2}(Γ)`,
`‖t‖ = inf {‖U‖ : U ∈ H^1(V), Tr_Γ ι U = Tr_Γ ι(E t) almost everywhere on Γ}`. Here `H^{1/2}(Γ)`
is defined by orthogonality; the infimum is attained at `U = E t`. -/
theorem enorm_eq_iInf (ψ : Ω.BoundaryPartition) (t : Ω.TraceSpace) :
    ‖t‖ₑ = ⨅ (U : H^{1}(V)) (_ : Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) =ᶠ[Ω.aeBoundary]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)))), ‖U‖ₑ :=
  le_antisymm (le_iInf₂ fun _ hU => Ω.enorm_le_of_boundaryTrace_eventuallyEq ψ hU)
    ((iInf₂_le ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)) EventuallyEq.rfl).trans_eq rfl)

/-! ### The norm equivalence with `B^{1/2}_{2,2}(Γ)` -/

/-- **The boundary trace of `H^1(V)` is bounded into `B^{1/2}_{2,2}(Γ)`**: for every resolution of
unity `ψ` there is `C < ∞` with `‖Tr_Γ ι U‖_{B^{1/2}_{2,2}(Γ)} ≤ C ‖U‖` for every `U ∈ H^1(V)`:
the trace bound (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le` at
`p = q = L = 2`, `s = 1/2`) and `H^1(V) ⊆ B^1_{2,2}(V)` (`Rd.modNorm_two_le_norm`). -/
theorem exists_boundaryBesovNorm_toL2_le (ψ : Ω.BoundaryPartition) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : H^{1}(V),
      Ω.boundaryBesovNorm 2 ψ (1 / 2) 2 (Ω.boundaryTrace ψ two_ne_top 2 (toL2 U)) ≤ C * ‖U‖ₑ := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_boundaryBesovNorm_boundaryTrace_le ψ two_ne_top (L := 2)
    (s := 1 / 2) (by norm_num) (by norm_num) (by norm_num) one_le_two
  refine ⟨C * sobolevOneBesovConst V, ENNReal.mul_ne_top hC sobolevOneBesovConst_ne_top,
    fun U => ?_⟩
  have hσ : (1 / 2 : ℝ) + 1 / (2 : ℝ≥0∞).toReal = 1 := by norm_num
  have h := hle (toL2 U) (modNorm_toL2_lt_top U)
  rw [hσ] at h
  rw [mul_assoc]
  exact h.trans (mul_le_mul' le_rfl (modNorm_two_le_norm U))

/-- **The trace of `H^{1/2}(Γ)` is bounded into `B^{1/2}_{2,2}(Γ)`**: for every resolution of
unity `ψ` there is `C < ∞` with `‖Tr_Γ ι(E t)‖_{B^{1/2}_{2,2}(Γ)} ≤ C ‖t‖` for every
`t ∈ H^{1/2}(Γ)` (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_toL2_le`, `‖E t‖ = ‖t‖`). -/
theorem exists_boundaryBesovNorm_extend_le (ψ : Ω.BoundaryPartition) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : Ω.TraceSpace, Ω.boundaryBesovNorm 2 ψ (1 / 2) 2
      (Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)))) ≤
        C * ‖t‖ₑ := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_boundaryBesovNorm_toL2_le ψ
  exact ⟨C, hC, fun t => hle _⟩

/-- **A bounded extension from `B^{1/2}_{2,2}(Γ)` into `H^1(V)`**: for every resolution of unity
`ψ` there is `C < ∞` such that every `g ∈ B^{1/2}_{2,2}(Γ)` is `Tr_Γ ι U` almost everywhere on `Γ`
for some `U ∈ H^1(V)` with `‖U‖ ≤ C ‖g‖_{B^{1/2}_{2,2}(Γ)}`: the bounded extension
(`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le` at `p = q = L = 2`, `s = 1/2`) gives
`F ∈ B^1_{2,2}(V)`, which is the `L_2` function of some `U ∈ H^1(V)`
(`Rd.memSobolev_one_iff_modulus`, `Rd.exists_toL2_eq_of_memSobolev`) with
`‖U‖ ≤ Rd.sobolevOneInvConst V ‖F‖_{B^1_{2,2}}` (`Rd.enorm_le_modNorm_two`). -/
theorem exists_toL2_boundaryTrace_eq_le (ψ : Ω.BoundaryPartition) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g →
      ∃ U : H^{1}(V), ‖U‖ₑ ≤ C * Ω.boundaryBesovNorm 2 ψ (1 / 2) 2 g ∧
        Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) =ᶠ[Ω.aeBoundary] g := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_boundaryTrace_eq_le ψ two_ne_top le_rfl (s := 1 / 2)
    (by norm_num) (by norm_num) one_le_two
  refine ⟨sobolevOneInvConst V * C, ENNReal.mul_ne_top sobolevOneInvConst_ne_top hC,
    fun g hg => ?_⟩
  obtain ⟨F, hFle, hFg⟩ := hle g hg
  have hσ : (1 / 2 : ℝ) + 1 / (2 : ℝ≥0∞).toReal = 1 := by norm_num
  rw [hσ] at hFle
  have hF := hFle.trans_lt (ENNReal.mul_lt_top hC.lt_top
    ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg))
  obtain ⟨U, rfl⟩ := exists_toL2_eq_of_memSobolev ((memSobolev_one_iff_modulus le_rfl F).2 hF)
  refine ⟨U, ?_, hFg⟩
  rw [mul_assoc]
  exact (enorm_le_modNorm_two U).trans (mul_le_mul' le_rfl hFle)

/-- **Bounded preimages under the trace**: for every resolution of unity `ψ` there is `C < ∞`
such that every `g ∈ B^{1/2}_{2,2}(Γ)` is `Tr_Γ ι(E t)` almost everywhere on `Γ` for some
`t ∈ H^{1/2}(Γ)` with `‖t‖ ≤ C ‖g‖_{B^{1/2}_{2,2}(Γ)}`; `t = γ(U|_Ω)` for the `U` of
`Rd.BoundedLipschitzDomain.exists_toL2_boundaryTrace_eq_le`. By uniqueness
(`Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`) `t` is determined by `g`; the
linear right inverse is `Rd.BoundedLipschitzDomain.traceRightInverse`. -/
theorem exists_traceSpace_of_memBoundaryBesov_le (ψ : Ω.BoundaryPartition) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g →
      ∃ t : Ω.TraceSpace, Ω.boundaryTrace ψ two_ne_top 2
          (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V))) =ᶠ[Ω.aeBoundary] g ∧
        ‖t‖ₑ ≤ C * Ω.boundaryBesovNorm 2 ψ (1 / 2) 2 g := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_toL2_boundaryTrace_eq_le ψ
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨U, hU, hUg⟩ := hle g hg
  exact ⟨Ω.trace (restrictProj 1 Ω.toOpens U), (Ω.boundaryTrace_extend_trace ψ _).trans
    ((Ω.boundaryTrace_restrictProj ψ U).trans hUg), (Ω.enorm_trace_restrictProj_le U).trans hU⟩

/-- **The norm of `H^{1/2}(Γ)` is bounded by the norm of the boundary trace**: for every
resolution of unity `ψ` there is `C < ∞` with `‖t‖ ≤ C ‖Tr_Γ ι(E t)‖_{B^{1/2}_{2,2}(Γ)}` for every
`t ∈ H^{1/2}(Γ)`: the bounded preimage
(`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov_le`) is `t`, since elements
of the trace space are determined by their boundary traces
(`Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`). -/
theorem exists_enorm_le_boundaryBesovNorm_extend (ψ : Ω.BoundaryPartition) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : Ω.TraceSpace, ‖t‖ₑ ≤ C * Ω.boundaryBesovNorm 2 ψ (1 / 2) 2
      (Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)))) := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_traceSpace_of_memBoundaryBesov_le ψ
  refine ⟨C, hC, fun t => ?_⟩
  obtain ⟨t', ht', hle'⟩ := hle _ (Ω.memBoundaryBesov_extend ψ t)
  rwa [(Ω.boundaryTrace_extend_eventuallyEq_iff ψ t' t).1 ht'] at hle'

/-- **`H^{1/2}(Γ)` and `B^{1/2}_{2,2}(Γ)` have equivalent norms**. The comparison uses the
Sobolev trace space, in the setting of McLean, Theorem 3.37, and the Besov trace-space
characterization with `p = q = 2`. Schneider–Vybíral, Theorem 4.11, treats domains of dimension
at least two. The characterization used here also covers dimension one.
For every resolution of unity `ψ` there is
`C < ∞` with `‖t‖ ≤ C ‖τ t‖_{B^{1/2}_{2,2}(Γ)}` and `‖τ t‖_{B^{1/2}_{2,2}(Γ)} ≤ C ‖t‖`
for every `t ∈ H^{1/2}(Γ)`, with the trace `τ : H^{1/2}(Γ) → L_2(Γ)`
(`Rd.BoundedLipschitzDomain.traceL2`). -/
theorem exists_traceL2_norm_equiv (ψ : Ω.BoundaryPartition) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : Ω.TraceSpace,
      ‖t‖ₑ ≤ C * Ω.boundaryBesovNorm 2 ψ (1 / 2) 2 (Ω.traceL2 t) ∧
        Ω.boundaryBesovNorm 2 ψ (1 / 2) 2 (Ω.traceL2 t) ≤ C * ‖t‖ₑ := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_enorm_le_boundaryBesovNorm_extend ψ
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundaryBesovNorm_extend_le ψ
  refine ⟨max C₁ C₂, (max_lt hC₁.lt_top hC₂.lt_top).ne, fun t => ?_⟩
  rw [Ω.boundaryBesovNorm_congr ψ (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Ω.traceL2_apply_ae ψ t))]
  exact ⟨(h₁ t).trans (mul_le_mul' (le_max_left _ _) le_rfl),
    (h₂ t).trans (mul_le_mul' (le_max_right _ _) le_rfl)⟩

/-- **The range of `H^{1/2}(Γ) → L_2(Γ)` is `B^{1/2}_{2,2}(Γ)`**: for every resolution of unity
`ψ`, `g ∈ L_2(Γ)` is `τ t` for some `t ∈ H^{1/2}(Γ)` iff `g ∈ B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
`Rd.BoundedLipschitzDomain.exists_traceL2_ae_eq`). -/
theorem mem_range_traceL2_iff (ψ : Ω.BoundaryPartition) (g : Ω.BoundaryL2) :
    g ∈ LinearMap.range (Ω.traceL2 : Ω.TraceSpace →ₗ[ℂ] Ω.BoundaryL2) ↔
      Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact (Ω.memBoundaryBesov_extend ψ t).congr
      (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Ω.traceL2_apply_ae ψ t)))
  · intro hg
    obtain ⟨t, ht⟩ := Ω.exists_traceL2_ae_eq ψ hg
    exact ⟨t, Lp.ext ht⟩

/-! ### The Banach space `B^{1/2}_{2,2}(Γ)` -/

section BoundaryL2Ops

variable {Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- `B^s_{p,q}(Γ)` contains the class `0` of `L_2(Γ)`. -/
theorem memBoundaryBesov_coe_zero (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) :
    Ω.MemBoundaryBesov p ψ s q ((0 : Ω.BoundaryL2) : V → ℂ) :=
  ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ 0).2
    ((Ω.boundaryBesovNorm_zero ψ s q).trans_lt ENNReal.zero_lt_top)).congr
    (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_zero ℂ 2 Ω.surfaceMeasure)))

/-- `B^s_{p,q}(Γ)` is closed under the addition of `L_2(Γ)`, for `q ≥ 1`
(`Rd.BoundedLipschitzDomain.MemBoundaryBesov.add`). -/
theorem MemBoundaryBesov.coe_add {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f g : Ω.BoundaryL2} (hf : Ω.MemBoundaryBesov p ψ s q f)
    (hg : Ω.MemBoundaryBesov p ψ s q g) :
    Ω.MemBoundaryBesov p ψ s q ((f + g : Ω.BoundaryL2) : V → ℂ) :=
  (hf.add hq hg).congr
    (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_add f g)))

/-- `B^s_{p,q}(Γ)` is closed under the scalar multiplication of `L_2(Γ)`
(`Rd.BoundedLipschitzDomain.MemBoundaryBesov.const_smul`). -/
theorem MemBoundaryBesov.coe_smul {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (c : ℂ)
    {f : Ω.BoundaryL2} (hf : Ω.MemBoundaryBesov p ψ s q f) :
    Ω.MemBoundaryBesov p ψ s q ((c • f : Ω.BoundaryL2) : V → ℂ) :=
  (hf.const_smul c).congr
    (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_smul c f)))

/-- `B^s_{p,q}(Γ)` is closed under the negation of `L_2(Γ)`, the multiplication by `-1`. -/
theorem MemBoundaryBesov.coe_neg {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞}
    {f : Ω.BoundaryL2} (hf : Ω.MemBoundaryBesov p ψ s q f) :
    Ω.MemBoundaryBesov p ψ s q ((-f : Ω.BoundaryL2) : V → ℂ) := by
  rw [← neg_one_smul ℂ f]
  exact hf.coe_smul (-1)

end BoundaryL2Ops

/-- **The space `B^{1/2}_{2,2}(Γ)`** as a normed space: the elements `g ∈ L_2(Γ)` of
`B^{1/2}_{2,2}(Γ)` for the canonical resolution of unity
`Rd.BoundedLipschitzDomain.boundaryPartition`, with the norm `‖g‖_{B^{1/2}_{2,2}(Γ)}` by chart
pieces (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`). A structure around `L_2(Γ)` that
carries the norm by chart pieces. It is a Banach space, isomorphic to `H^{1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesovHalf`). -/
@[ext]
structure BoundaryBesovHalf where
  /-- The function in `L_2(Γ)`. -/
  toL2 : Ω.BoundaryL2
  /-- It lies in `B^{1/2}_{2,2}(Γ)`. -/
  mem : Ω.MemBoundaryBesov 2 Ω.boundaryPartition (1 / 2) 2 toL2

namespace BoundaryBesovHalf

variable {Ω}

/-- An element of `B^{1/2}_{2,2}(Γ)` is determined by its function in `L_2(Γ)`. -/
theorem toL2_injective : Function.Injective (toL2 : Ω.BoundaryBesovHalf → Ω.BoundaryL2) :=
  fun _ _ h => BoundaryBesovHalf.ext h

/-- The zero function. -/
noncomputable instance instZero : Zero Ω.BoundaryBesovHalf :=
  ⟨⟨0, memBoundaryBesov_coe_zero _ _ _⟩⟩

/-- The sum of two functions of `B^{1/2}_{2,2}(Γ)`. -/
noncomputable instance instAdd : Add Ω.BoundaryBesovHalf :=
  ⟨fun a b => ⟨a.toL2 + b.toL2, a.mem.coe_add one_le_two b.mem⟩⟩

/-- The negative of a function of `B^{1/2}_{2,2}(Γ)`. -/
noncomputable instance instNeg : Neg Ω.BoundaryBesovHalf := ⟨fun a => ⟨-a.toL2, a.mem.coe_neg⟩⟩

/-- The difference of two functions of `B^{1/2}_{2,2}(Γ)`. -/
noncomputable instance instSub : Sub Ω.BoundaryBesovHalf :=
  ⟨fun a b => ⟨a.toL2 - b.toL2, by
    rw [sub_eq_add_neg]
    exact a.mem.coe_add one_le_two b.mem.coe_neg⟩⟩

/-- Complex multiples of a function of `B^{1/2}_{2,2}(Γ)`. -/
noncomputable instance instSMul : SMul ℂ Ω.BoundaryBesovHalf :=
  ⟨fun c a => ⟨c • a.toL2, a.mem.coe_smul c⟩⟩

/-- Natural multiples of a function of `B^{1/2}_{2,2}(Γ)`. -/
noncomputable instance instSMulNat : SMul ℕ Ω.BoundaryBesovHalf :=
  ⟨fun n a => ⟨n • a.toL2, by
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    exact a.mem.coe_smul _⟩⟩

/-- Integer multiples of a function of `B^{1/2}_{2,2}(Γ)`. -/
noncomputable instance instSMulInt : SMul ℤ Ω.BoundaryBesovHalf :=
  ⟨fun n a => ⟨n • a.toL2, by
    rw [← Int.cast_smul_eq_zsmul ℂ]
    exact a.mem.coe_smul _⟩⟩

/-- `B^{1/2}_{2,2}(Γ)` is an additive group, a subgroup of `L_2(Γ)`. -/
noncomputable instance instAddCommGroup : AddCommGroup Ω.BoundaryBesovHalf :=
  toL2_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The inclusion `B^{1/2}_{2,2}(Γ) → L_2(Γ)` as an additive map. -/
noncomputable def toL2AddMonoidHom : Ω.BoundaryBesovHalf →+ Ω.BoundaryL2 where
  toFun := toL2
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `B^{1/2}_{2,2}(Γ)` is a complex vector space, a subspace of `L_2(Γ)`. -/
noncomputable instance instModule : Module ℂ Ω.BoundaryBesovHalf :=
  Function.Injective.module (R := ℂ) toL2AddMonoidHom toL2_injective fun _ _ => rfl

/-- **The norm of `B^{1/2}_{2,2}(Γ)`**: `‖g‖_{B^{1/2}_{2,2}(Γ)}` by chart pieces, for the canonical
resolution of unity. -/
noncomputable instance instNorm : Norm Ω.BoundaryBesovHalf :=
  ⟨fun a => (Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2 a.toL2).toReal⟩

/-- The norm of `B^{1/2}_{2,2}(Γ)` is `‖g‖_{B^{1/2}_{2,2}(Γ)}` by chart pieces. -/
protected theorem norm_def (a : Ω.BoundaryBesovHalf) :
    ‖a‖ = (Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2 a.toL2).toReal :=
  rfl

/-- The quasi-norm of an element of `B^{1/2}_{2,2}(Γ)` is finite. -/
theorem boundaryBesovNorm_lt_top (a : Ω.BoundaryBesovHalf) :
    Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2 a.toL2 < ∞ :=
  (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top _ _).1 a.mem

/-- The norm is homogeneous (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_const_smul`). -/
protected theorem norm_smul (c : ℂ) (a : Ω.BoundaryBesovHalf) : ‖c • a‖ = ‖c‖ * ‖a‖ := by
  rw [BoundaryBesovHalf.norm_def, BoundaryBesovHalf.norm_def]
  change (Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2
    ((c • a.toL2 : Ω.BoundaryL2) : V → ℂ)).toReal = _
  rw [Ω.boundaryBesovNorm_congr _
      (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_smul c a.toL2)),
    Ω.boundaryBesovNorm_const_smul _ c _, ENNReal.toReal_mul, toReal_eNorm]

/-- The triangle inequality (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_add_le`). -/
protected theorem norm_add_le (a b : Ω.BoundaryBesovHalf) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [BoundaryBesovHalf.norm_def, BoundaryBesovHalf.norm_def, BoundaryBesovHalf.norm_def,
    ← ENNReal.toReal_add a.boundaryBesovNorm_lt_top.ne b.boundaryBesovNorm_lt_top.ne]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2
    ⟨a.boundaryBesovNorm_lt_top.ne, b.boundaryBesovNorm_lt_top.ne⟩) ?_
  change Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2
    ((a.toL2 + b.toL2 : Ω.BoundaryL2) : V → ℂ) ≤ _
  rw [Ω.boundaryBesovNorm_congr _
    (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_add a.toL2 b.toL2))]
  exact Ω.boundaryBesovNorm_add_le _ one_le_two _ _

/-- **The norm is definite**: `‖g‖_{B^{1/2}_{2,2}(Γ)} = 0` iff `g = 0`; a vanishing norm makes all
chart pieces vanish (`Rd.BoundedLipschitzDomain.chart_ae_eq_zero_of_boundaryBesovNorm_eq_zero`),
hence `g = 0` almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.eventuallyEq_zero_iff_forall_chart`). -/
protected theorem norm_eq_zero_iff (a : Ω.BoundaryBesovHalf) : ‖a‖ = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [BoundaryBesovHalf.norm_def, ENNReal.toReal_eq_zero_iff] at h
    have h0 := h.resolve_right a.boundaryBesovNorm_lt_top.ne
    ext1
    change a.toL2 = 0
    rw [Lp.eq_zero_iff_ae_eq_zero]
    exact Ω.ae_surfaceMeasure_iff_aeBoundary.2
      ((Ω.eventuallyEq_zero_iff_forall_chart Ω.boundaryPartition _).2
        (Ω.chart_ae_eq_zero_of_boundaryBesovNorm_eq_zero _ h0))
  · rintro rfl
    rw [BoundaryBesovHalf.norm_def]
    change (Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2
      ((0 : Ω.BoundaryL2) : V → ℂ)).toReal = 0
    rw [Ω.boundaryBesovNorm_congr _
        (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_zero ℂ 2 Ω.surfaceMeasure)),
      Ω.boundaryBesovNorm_zero, ENNReal.toReal_zero]

/-- The axioms of a normed space for `B^{1/2}_{2,2}(Γ)`. -/
theorem normedSpaceCore : NormedSpace.Core ℂ Ω.BoundaryBesovHalf where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul := BoundaryBesovHalf.norm_smul
  norm_triangle := BoundaryBesovHalf.norm_add_le
  norm_eq_zero_iff := BoundaryBesovHalf.norm_eq_zero_iff

/-- `B^{1/2}_{2,2}(Γ)` is a normed group (Mathlib's `NormedAddCommGroup.ofCore`). -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup Ω.BoundaryBesovHalf :=
  NormedAddCommGroup.ofCore normedSpaceCore

/-- `B^{1/2}_{2,2}(Γ)` is a complex normed space (Mathlib's `NormedSpace.ofCore`). -/
noncomputable instance instNormedSpace : NormedSpace ℂ Ω.BoundaryBesovHalf :=
  NormedSpace.ofCore normedSpaceCore

end BoundaryBesovHalf

/-- The trace `t ↦ τ t` from `H^{1/2}(Γ)` into `B^{1/2}_{2,2}(Γ)` as a linear map
(`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`). -/
noncomputable def traceSpaceToBoundaryBesovHalf : Ω.TraceSpace →ₗ[ℂ] Ω.BoundaryBesovHalf where
  toFun t := ⟨Ω.traceL2 t, (Ω.mem_range_traceL2_iff Ω.boundaryPartition _).1
    (LinearMap.mem_range.2 ⟨t, rfl⟩)⟩
  map_add' t t' := BoundaryBesovHalf.ext (map_add Ω.traceL2 t t')
  map_smul' c t := BoundaryBesovHalf.ext (map_smul Ω.traceL2 c t)

/-- The trace `H^{1/2}(Γ) → B^{1/2}_{2,2}(Γ)` is bijective: injective by
`Rd.BoundedLipschitzDomain.traceL2_injective`, surjective by
`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`. -/
theorem traceSpaceToBoundaryBesovHalf_bijective :
    Function.Bijective Ω.traceSpaceToBoundaryBesovHalf := by
  refine ⟨fun t t' h => Ω.traceL2_injective (congrArg BoundaryBesovHalf.toL2 h), fun b => ?_⟩
  obtain ⟨t, ht⟩ := LinearMap.mem_range.1
    ((Ω.mem_range_traceL2_iff Ω.boundaryPartition b.toL2).2 b.mem)
  exact ⟨t, BoundaryBesovHalf.ext ht⟩

/-- The trace `H^{1/2}(Γ) → B^{1/2}_{2,2}(Γ)` as a linear isomorphism. -/
noncomputable def traceSpaceLinearEquiv :
    Ω.TraceSpace ≃ₗ[ℂ] Ω.BoundaryBesovHalf :=
  LinearEquiv.ofBijective _ Ω.traceSpaceToBoundaryBesovHalf_bijective

/-- The linear isomorphism sends `t` to `τ t`. -/
theorem toL2_traceSpaceLinearEquiv (t : Ω.TraceSpace) :
    (Ω.traceSpaceLinearEquiv t).toL2 = Ω.traceL2 t :=
  rfl

/-- **The constant of the norm equivalence** `H^{1/2}(Γ) ≅ B^{1/2}_{2,2}(Γ)` for the canonical
resolution of unity, a choice among the constants of
`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`. -/
noncomputable def traceNormConst : ℝ≥0∞ :=
  (Ω.exists_traceL2_norm_equiv Ω.boundaryPartition).choose

/-- The constant of the norm equivalence is finite. -/
theorem traceNormConst_ne_top : Ω.traceNormConst ≠ ∞ :=
  (Ω.exists_traceL2_norm_equiv Ω.boundaryPartition).choose_spec.1

/-- The two bounds of the norm equivalence with the constant `Ω.traceNormConst`. -/
theorem traceNormConst_spec (t : Ω.TraceSpace) :
    ‖t‖ₑ ≤ Ω.traceNormConst * Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2 (Ω.traceL2 t) ∧
      Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2 (Ω.traceL2 t) ≤
        Ω.traceNormConst * ‖t‖ₑ :=
  (Ω.exists_traceL2_norm_equiv Ω.boundaryPartition).choose_spec.2 t

/-- `‖τ t‖_{B^{1/2}_{2,2}(Γ)} ≤ C ‖t‖` with `C = Ω.traceNormConst`. -/
theorem norm_traceSpaceLinearEquiv_le (t : Ω.TraceSpace) :
    ‖Ω.traceSpaceLinearEquiv t‖ ≤ Ω.traceNormConst.toReal * ‖t‖ := by
  rw [BoundaryBesovHalf.norm_def, toL2_traceSpaceLinearEquiv, ← toReal_eNorm t,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top Ω.traceNormConst_ne_top eNorm_ne_top)
    (Ω.traceNormConst_spec t).2

/-- `‖t‖ ≤ C ‖τ t‖_{B^{1/2}_{2,2}(Γ)}` with `C = Ω.traceNormConst`, for the inverse map. -/
theorem norm_traceSpaceLinearEquiv_symm_le (b : Ω.BoundaryBesovHalf) :
    ‖Ω.traceSpaceLinearEquiv.symm b‖ ≤ Ω.traceNormConst.toReal * ‖b‖ := by
  have h := (Ω.traceNormConst_spec (Ω.traceSpaceLinearEquiv.symm b)).1
  have hb : Ω.traceL2 (Ω.traceSpaceLinearEquiv.symm b) = b.toL2 :=
    congrArg BoundaryBesovHalf.toL2 (Ω.traceSpaceLinearEquiv.apply_symm_apply b)
  rw [hb] at h
  rw [← toReal_eNorm (Ω.traceSpaceLinearEquiv.symm b),
    BoundaryBesovHalf.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top Ω.traceNormConst_ne_top
    b.boundaryBesovNorm_lt_top.ne) h

/-- **`H^{1/2}(Γ) ≅ B^{1/2}_{2,2}(Γ)`**. The trace `t ↦ τ t` is an isomorphism of normed spaces
from the trace space onto `B^{1/2}_{2,2}(Γ)` with the norm by chart pieces (Mathlib's
`LinearEquiv.toContinuousLinearEquivOfBounds`), with the bounds of
`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv` in both directions. -/
noncomputable def traceSpaceEquivBoundaryBesovHalf : Ω.TraceSpace ≃L[ℂ] Ω.BoundaryBesovHalf :=
  Ω.traceSpaceLinearEquiv.toContinuousLinearEquivOfBounds
    Ω.traceNormConst.toReal Ω.traceNormConst.toReal
    Ω.norm_traceSpaceLinearEquiv_le
    Ω.norm_traceSpaceLinearEquiv_symm_le

/-- The isomorphism of normed spaces sends `t` to `τ t`. -/
theorem toL2_traceSpaceEquivBoundaryBesovHalf (t : Ω.TraceSpace) :
    (Ω.traceSpaceEquivBoundaryBesovHalf t).toL2 = Ω.traceL2 t :=
  rfl

/-- **`B^{1/2}_{2,2}(Γ)` is a Banach space**: it is isomorphic to the Hilbert space `H^{1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesovHalf`; Mathlib's `completeSpace_congr`). -/
instance completeSpace_boundaryBesovHalf : CompleteSpace Ω.BoundaryBesovHalf :=
  (completeSpace_congr (e := Ω.traceSpaceEquivBoundaryBesovHalf.toEquiv)
    Ω.traceSpaceEquivBoundaryBesovHalf.isUniformEmbedding).1 inferInstance

/-- **The bounded linear right inverse of the trace** (as in McLean, Theorem 3.37): the map
`B^{1/2}_{2,2}(Γ) → H^1(Ω)`, `g ↦ E τ⁻¹ g`, the inverse of the isomorphism
`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesovHalf` followed by the extension `E`. -/
noncomputable def traceRightInverse : Ω.BoundaryBesovHalf →L[ℂ] Ω.SobolevOne :=
  Ω.extend ∘L (Ω.traceSpaceEquivBoundaryBesovHalf.symm : Ω.BoundaryBesovHalf →L[ℂ] Ω.TraceSpace)

/-- The trace of `E τ⁻¹ g` is `τ⁻¹ g` (`Rd.BoundedLipschitzDomain.trace_extend`). -/
theorem trace_traceRightInverse (b : Ω.BoundaryBesovHalf) :
    Ω.trace (Ω.traceRightInverse b) = Ω.traceSpaceEquivBoundaryBesovHalf.symm b :=
  Ω.trace_extend _

/-- **The right inverse inverts the trace**: `γ_{L_2}(E τ⁻¹ g) = g` in `L_2(Γ)` for every
`g ∈ B^{1/2}_{2,2}(Γ)`, with the trace `γ_{L_2} = τ ∘ γ : H^1(Ω) → L_2(Γ)`
(`Rd.BoundedLipschitzDomain.boundaryTraceL2`). -/
theorem boundaryTraceL2_traceRightInverse (b : Ω.BoundaryBesovHalf) :
    Ω.boundaryTraceL2 (Ω.traceRightInverse b) = b.toL2 := by
  change Ω.traceL2 (Ω.trace (Ω.traceRightInverse b)) = b.toL2
  rw [Ω.trace_traceRightInverse, ← Ω.toL2_traceSpaceEquivBoundaryBesovHalf,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **The right inverse is bounded**: `‖E τ⁻¹ g‖ ≤ C ‖g‖_{B^{1/2}_{2,2}(Γ)}` with
`C = Ω.traceNormConst`, since `E` is an isometry
(`Rd.BoundedLipschitzDomain.norm_extend_apply`,
`Rd.BoundedLipschitzDomain.norm_traceSpaceLinearEquiv_symm_le`). -/
theorem norm_traceRightInverse_le (b : Ω.BoundaryBesovHalf) :
    ‖Ω.traceRightInverse b‖ ≤ Ω.traceNormConst.toReal * ‖b‖ :=
  (Ω.norm_extend_apply _).trans_le (Ω.norm_traceSpaceLinearEquiv_symm_le b)

end BoundedLipschitzDomain

end Rd
