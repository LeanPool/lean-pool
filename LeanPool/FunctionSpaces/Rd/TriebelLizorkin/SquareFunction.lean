/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.VectorValuedSingularIntegrals
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkin

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The square function theorem `L_p = F^0_{p,2}`

Let `V` have dimension `n ≥ 1` and `1 < p < ∞`. The **square function** of `f ∈ L_p(V)` is
`x ↦ ‖((ψ_j ⋆ f)(x))_j‖_{ℓ_2}`, and its `L_p` norm is the Triebel–Lizorkin norm
`‖f‖_{F^0_{p,2}}` by definition (`Rd.triebelLizorkinNorm_zero_left`). The square
function theorem is the two-sided bound of this norm by `‖f‖_p`, with named constants,
formulas in the Schwartz seminorms of the fixed blocks and synthesis kernels that are proved
finite (`Rd.squareFunctionConst_ne_top`, `Rd.squareSynthesisConst_ne_top`):

* `‖f‖_{F^0_{p,2}} ≤ Q_{V,p} ‖f‖_p` (`Rd.triebelLizorkinNorm_zero_two_le`, constant
  `Rd.squareFunctionConst`): the analysis bound of the Calderón–Zygmund family `(ψ_j)_j`;
* `‖f‖_p ≤ QTilde_{V,p} ‖f‖_{F^0_{p,2}}` (`Rd.enorm_le_triebelLizorkinNorm_zero_two`, constant
  `Rd.squareSynthesisConst`): the reproducing formula
  `∑_{j < J} psiDual_j ⋆ (ψ_j ⋆ f) = ∑_{j < J} Δ_j f` almost everywhere, and these partial
  sums tend to `f` in `L_p` (`Rd.sum_conv_psiDual_blockFun_ae`,
  `Rd.tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub`), and the synthesis bound of the
  Calderón–Zygmund family `(psiDual_j)_j`.

By the upper bound every `f ∈ L_p(V)` lies in `F^0_{p,2}` (`Rd.memTriebelLizorkin_zero_two`), so
the subspace `F^0_{p,2}` of `L_p(V)` is all of `L_p(V)`
(`Rd.triebelLizorkinSpace_zero_two_eq_top`). With the Besov sandwich of `F^s_{p,2}` for `s > 0`,
every `f` in the Besov space `B^s_{p,min(p,2)}` lies in `F^s_{p,2}` for every `s ≥ 0`
(`Rd.memTriebelLizorkin_two_of_memApprox`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology
open ENNReal (lqNorm)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The constants -/

variable (V) in
/-- The constant `Q_{V,p}` of the **upper square function bound**
`‖f‖_{F^0_{p,2}} ≤ Q_{V,p} ‖f‖_p`: the strong type constant `Rd.czConst` of the
Calderón–Zygmund family of the blocks `ψ_j`, with overlap `2` and Hörmander constant
`4 H_{A^ψ}`, where `A^ψ = Rd.psiBaseBound V` (`Rd.isCZFamily_psi`). -/
noncomputable def squareFunctionConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  czConst V p 2 (4 * familyHormanderConst V (psiBaseBound V))

/-- The constant `Rd.squareFunctionConst V p` is finite for `1 < p < ∞`. -/
theorem squareFunctionConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    squareFunctionConst V p ≠ ∞ :=
  czConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

variable (V) in
/-- The constant `QTilde_{V,p}` of the **lower square function bound**
`‖f‖_p ≤ QTilde_{V,p} ‖f‖_{F^0_{p,2}}`: the strong type constant `Rd.czConst` of the
Calderón–Zygmund family of the synthesis kernels `psiDual_j`, with overlap `4` and Hörmander
constant `4 H_{Ã}`, where `Ã = Rd.psiDualBaseBound V` (`Rd.isCZFamily_psiDual`). -/
noncomputable def squareSynthesisConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  czConst V p 4 (4 * familyHormanderConst V (psiDualBaseBound V))

/-- The constant `Rd.squareSynthesisConst V p` is finite for `1 < p < ∞`. -/
theorem squareSynthesisConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    squareSynthesisConst V p ≠ ∞ :=
  czConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

/-! ### The square function -/

/-- **The upper square function bound**: in dimension `n ≥ 1`, for `1 < p < ∞` and
`f ∈ L_p(V)`, `‖f‖_{F^0_{p,2}} ≤ Q_{V,p} ‖f‖_p` with `Q_{V,p} = Rd.squareFunctionConst V p`. This is
the strong type of the analysis operator of the Calderón–Zygmund family `(ψ_j)_j`. -/
theorem triebelLizorkinNorm_zero_two_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm 0 2 f ≤ squareFunctionConst V p * ‖f‖ₑ := by
  rw [triebelLizorkinNorm_zero_left, Lp.eNorm_def]
  exact isCZFamily_psi.eLpNorm_lqNorm_conv_le hp1 hp (Lp.memLp f)

/-- **`L_p ⊆ F^0_{p,2}`**: in dimension `n ≥ 1`, for `1 < p < ∞`, every `f ∈ L_p(V)` has a
finite Triebel–Lizorkin norm `‖f‖_{F^0_{p,2}}`. -/
theorem memTriebelLizorkin_zero_two [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) : MemTriebelLizorkin 0 2 f :=
  (triebelLizorkinNorm_zero_two_le hp1 hp f).trans_lt
    (ENNReal.mul_lt_top (squareFunctionConst_ne_top hp1 hp).lt_top eNorm_lt_top)

/-! ### The reproducing formula -/

/-- **The synthesis kernels reproduce the blocks**: for `1 ≤ p < ∞` and `f ∈ L_p(V)`,
`psiDual_j ⋆ (ψ_j ⋆ f) = ψ_j ⋆ f` almost everywhere, by associativity of convolution and
`psiDual_j ⋆ ψ_j = ψ_j` (`Rd.conv_psiDual_psi`). -/
theorem conv_psiDual_blockFun_ae (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    conv (psiDual j) (blockFun j f) volume =ᵐ[volume] blockFun j f := by
  have h := conv_conv_ae Fact.out hp (integrable_psiDual j) (integrable_psi j) (Lp.memLp f)
  rw [conv_psiDual_psi] at h
  exact h.symm

/-- **The reproducing sums**: for `1 ≤ p < ∞`, `f ∈ L_p(V)` and every finite set `s ⊆ ℕ`,
`∑_{j ∈ s} psiDual_j ⋆ (ψ_j ⋆ f) = ∑_{j ∈ s} Δ_j f` almost everywhere. -/
theorem sum_conv_psiDual_blockFun_ae (hp : p ≠ ∞) (s : Finset ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    (fun x => ∑ j ∈ s, conv (psiDual j) (blockFun j f) volume x) =ᵐ[volume]
      ⇑(∑ j ∈ s, lpBlock hp j f) := by
  have h1 : ∀ᵐ x ∂volume, ∀ j, conv (psiDual j) (blockFun j f) volume x = blockFun j f x :=
    ae_all_iff.2 fun j => conv_psiDual_blockFun_ae hp j f
  have h2 : ∀ᵐ x ∂volume, ∀ j, lpBlock hp j f x = blockFun j f x :=
    ae_all_iff.2 fun j => lpBlock_ae_eq_blockFun hp j f
  filter_upwards [h1, h2, Lp.coeFn_fun_finsetSum s fun j => lpBlock hp j f] with x hx1 hx2 hx3
  rw [hx3]
  exact Finset.sum_congr rfl fun j _ => (hx1 j).trans (hx2 j).symm

/-- **The reproducing formula**: for `1 ≤ p < ∞` and `f ∈ L_p(V)`,
`∑_{j < J} psiDual_j ⋆ (ψ_j ⋆ f) → f` in `L_p(V)` as `J → ∞`, since the partial sums are the
partial sums `∑_{j < J} Δ_j f` of the Littlewood–Paley decomposition (`Rd.tendsto_sum_lpBlock`). -/
theorem tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) :
    Tendsto (fun J => eLpNorm ((fun x => ∑ j ∈ Finset.range J,
      conv (psiDual j) (blockFun j f) volume x) - ⇑f) p volume) atTop (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).1 (tendsto_sum_lpBlock hp f)
  refine h.congr fun J => eLpNorm_congr_ae ?_
  exact ((sum_conv_psiDual_blockFun_ae hp _ f).sub EventuallyEq.rfl).symm

/-! ### The lower bound and `L_p = F^0_{p,2}` -/

/-- **The lower square function bound**: in dimension `n ≥ 1`, for `1 < p < ∞` and
`f ∈ L_p(V)`, `‖f‖_p ≤ QTilde_{V,p} ‖f‖_{F^0_{p,2}}` with `QTilde_{V,p} =
Rd.squareSynthesisConst V p`.
The partial sums `∑_{j < J} Δ_j f` tend to `f` and equal `∑_{j < J} psiDual_j ⋆ (ψ_j ⋆ f)`,
whose `L_p` norms the synthesis bound of the Calderón–Zygmund family `(psiDual_j)_j` controls. -/
theorem enorm_le_triebelLizorkinNorm_zero_two [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) :
    ‖f‖ₑ ≤ squareSynthesisConst V p * triebelLizorkinNorm 0 2 f := by
  have h : Tendsto (fun J => ‖∑ j ∈ Finset.range J, lpBlock hp j f‖ₑ) atTop (𝓝 ‖f‖ₑ) :=
    (tendsto_sum_lpBlock hp f).eNorm
  refine le_of_tendsto' h fun J => ?_
  rw [Lp.eNorm_def, ← eLpNorm_congr_ae (sum_conv_psiDual_blockFun_ae hp _ f),
    triebelLizorkinNorm_zero_left]
  exact isCZFamily_psiDual.eLpNorm_sum_conv_le hp1 hp _ fun j => memLp_blockFun j f

/-- **The square function theorem `L_p = F^0_{p,2}`**: in dimension `n ≥ 1`, for `1 < p < ∞`,
the subspace `F^0_{p,2}` of `L_p(V)` is all of `L_p(V)`. The norms are equivalent by
`Rd.triebelLizorkinNorm_zero_two_le` and `Rd.enorm_le_triebelLizorkinNorm_zero_two`. -/
theorem triebelLizorkinSpace_zero_two_eq_top [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) :
    triebelLizorkinSpace (V := V) hp 0 2 one_le_two = ⊤ :=
  Submodule.eq_top_iff'.2 fun f => memTriebelLizorkin_zero_two hp1 hp f

/-! ### Besov spaces in `F^s_{p,2}` -/

/-- **`B^s_{p,min(p,2)} ⊆ F^s_{p,2}` for `s ≥ 0`**: in dimension `n ≥ 1`, for `1 < p < ∞` and
`s ≥ 0`, every `f` in the approximation space `A^s_{min(p,2)}` of the band-limited scheme lies in
`F^s_{p,2}(V)`: for `s > 0` by the Besov sandwich (`Rd.memTriebelLizorkin_of_memApprox`), for
`s = 0` since `F^0_{p,2} = L_p(V)` by the square function theorem
(`Rd.memTriebelLizorkin_zero_two`). -/
theorem memTriebelLizorkin_two_of_memApprox [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 ≤ s) {f : Lp ℂ p (volume : Measure V)}
    (hf : (bandScheme hp).MemApprox s (min p 2) f) : MemTriebelLizorkin s 2 f := by
  rcases hs.eq_or_lt with rfl | hs
  · exact memTriebelLizorkin_zero_two hp1 hp f
  · exact memTriebelLizorkin_of_memApprox hp hs one_le_two hf

end Rd
