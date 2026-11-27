/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.SingularIntegrals
public import LeanPool.FunctionSpaces.Torus.TriebelLizorkin

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The square function theorem on the torus

Let `d ≥ 1` and `1 < p < ∞`. The norm `‖f‖_{F^0_{p,2}(𝕋^d)}` of `f ∈ L_p(𝕋^d)` is the `L_p` norm
of the square function `t ↦ ‖((ψ_j ⋆ f)(t))_j‖_{ℓ_2}` of the Littlewood–Paley blocks
(`Torus.triebelLizorkinNorm_zero_left`). The square function theorem on the torus is the
two-sided bound of this norm by `‖f‖_p`, with named constants that are proved finite
(`Torus.squareFunctionConst_ne_top`, `Torus.squareSynthesisConst_ne_top`):

* `‖f‖_{F^0_{p,2}(𝕋^d)} ≤ Q^𝕋_p ‖f‖_p` (`Torus.triebelLizorkinNorm_zero_two_le`, constant
  `Torus.squareFunctionConst`): the analysis bound of the vector-valued singular integrals on the
  torus for the Calderón–Zygmund family `(ψ_j)_j`;
* `‖f‖_p ≤ QTilde^𝕋_p ‖f‖_{F^0_{p,2}(𝕋^d)}` (`Torus.enorm_le_triebelLizorkinNorm_zero_two`,
  constant `Torus.squareSynthesisConst`): the synthesis kernels reproduce the blocks,
  `psiDual_j ⋆ Δ_j f = Δ_j f` (`Torus.econvLp_psiDual_lpBlock`), so
  `∑_{j ∈ s} psiDual_j ⋆ Δ_j f = ∑_{j ∈ s} Δ_j f` almost everywhere
  (`Torus.sum_econv_psiDual_lpBlock_ae`); these partial sums tend to `f`
  (`Torus.tendsto_sum_lpBlock`), and the synthesis bound for the family `(psiDual_j)_j` applies.

Hence `F^0_{p,2}(𝕋^d) = L_p(𝕋^d)` (`Torus.triebelLizorkinSpace_zero_two_eq_top`), and
`B^s_{p,min(p,2)}(𝕋^d) ⊆ F^s_{p,2}(𝕋^d)` holds for every `s ≥ 0`
(`Torus.memTriebelLizorkin_two_of_memBesov`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Filter
open scoped ENNReal TorusHaar Topology

open ENNReal (lqNorm)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The constants -/

variable (d) in
/-- The constant `Q^𝕋_p` of the **upper square function bound on the torus**: the constant
`Torus.periodicCZConst` of the Calderón–Zygmund family of the blocks `ψ_j`, with overlap `2`,
Hörmander constant `4 H_{A^ψ}` and far mass bound `2 T_{A^ψ}`, where `A^ψ = Rd.psiBaseBound`
(`Rd.isCZFamily_psi`, `Torus.farMass_psi_le`). -/
noncomputable def squareFunctionConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  periodicCZConst d p 2
    (4 * Rd.familyHormanderConst (EuclideanSpace ℝ d) (Rd.psiBaseBound (EuclideanSpace ℝ d)))
    (2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.psiBaseBound (EuclideanSpace ℝ d)) 0 1)

/-- The constant `Torus.squareFunctionConst d p` is finite for `1 < p < ∞`. -/
theorem squareFunctionConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    squareFunctionConst d p ≠ ∞ :=
  periodicCZConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyHormanderConst_ne_top _))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyTailConst_ne_top _ _ _))

variable (d) in
/-- The constant `QTilde^𝕋_p` of the **lower square function bound on the torus**: the constant
`Torus.periodicCZConst` of the Calderón–Zygmund family of the synthesis kernels `psiDual_j`,
with overlap `4`, Hörmander constant `4 H_Ã` and far mass bound `2 T_Ã`, where
`Ã = Rd.psiDualBaseBound` (`Rd.isCZFamily_psiDual`, `Torus.farMass_psiDual_le`). -/
noncomputable def squareSynthesisConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  periodicCZConst d p 4
    (4 * Rd.familyHormanderConst (EuclideanSpace ℝ d) (Rd.psiDualBaseBound (EuclideanSpace ℝ d)))
    (2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.psiDualBaseBound (EuclideanSpace ℝ d)) 0 1)

/-- The constant `Torus.squareSynthesisConst d p` is finite for `1 < p < ∞`. -/
theorem squareSynthesisConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    squareSynthesisConst d p ≠ ∞ :=
  periodicCZConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyHormanderConst_ne_top _))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyTailConst_ne_top _ _ _))

/-! ### The upper bound -/

/-- **The upper square function bound on the torus**: for `d ≥ 1`, `1 < p < ∞` and
`f ∈ L_p(𝕋^d)`, `‖f‖_{F^0_{p,2}(𝕋^d)} ≤ Q^𝕋_p ‖f‖_p` with
`Q^𝕋_p = Torus.squareFunctionConst d p`: the analysis bound on the torus
(`Torus.eLpNorm_lqNorm_econv_le`) for the Calderón–Zygmund family `(ψ_j)_j`. -/
theorem triebelLizorkinNorm_zero_two_le [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    triebelLizorkinNorm 0 2 f ≤ squareFunctionConst d p * ‖f‖ₑ := by
  rw [triebelLizorkinNorm_zero_left]
  exact eLpNorm_lqNorm_econv_le Rd.isCZFamily_psi farMass_psi_le hp1 hp f

/-- **`L_p(𝕋^d) ⊆ F^0_{p,2}(𝕋^d)`**: for `d ≥ 1` and `1 < p < ∞`, every `f ∈ L_p(𝕋^d)` has a
finite Triebel–Lizorkin norm `‖f‖_{F^0_{p,2}(𝕋^d)}`. -/
theorem memTriebelLizorkin_zero_two [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : MemTriebelLizorkin 0 2 f :=
  (triebelLizorkinNorm_zero_two_le hp1 hp f).trans_lt
    (ENNReal.mul_lt_top (squareFunctionConst_ne_top hp1 hp).lt_top eNorm_lt_top)

/-! ### The reproducing formula -/

/-- **The synthesis kernels reproduce the blocks**: for `1 ≤ p < ∞` and `f ∈ L_p(𝕋^d)`,
`psiDual_j ⋆ Δ_j f = Δ_j f`, since `psiDual_j ⋆ ψ_j = ψ_j` on `ℝ^d` (`Rd.conv_psiDual_psi`). -/
theorem econvLp_psiDual_lpBlock (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    econvLp hp (Rd.integrable_psiDual j) (lpBlock hp j f) = lpBlock hp j f :=
  econvLp_comp_econvLp_of_eq hp (Rd.integrable_psiDual j) (Rd.integrable_psi j)
    (Rd.integrable_psi j) (Rd.conv_psiDual_psi j) f

/-- **The reproducing sums**: for `1 ≤ p < ∞`, `f ∈ L_p(𝕋^d)` and every finite set `s ⊆ ℕ`,
`∑_{j ∈ s} psiDual_j ⋆ Δ_j f = ∑_{j ∈ s} Δ_j f` almost everywhere, with the pointwise
convolutions of representatives on the left. -/
theorem sum_econv_psiDual_lpBlock_ae (hp : p ≠ ∞) (s : Finset ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (fun t => ∑ j ∈ s, econv (Rd.psiDual j) (lpBlock hp j f) t) =ᵐ[volume]
      ⇑(∑ j ∈ s, lpBlock hp j f) := by
  have h := coeFn_sum_econvLp_ae hp s (fun j => Rd.integrable_psiDual (V := EuclideanSpace ℝ d) j)
    fun j => lpBlock hp j f
  simp only [econvLp_psiDual_lpBlock] at h
  exact h.symm

/-! ### The lower bound and `L_p = F^0_{p,2}` -/

/-- **The lower square function bound on the torus**: for `d ≥ 1`, `1 < p < ∞` and
`f ∈ L_p(𝕋^d)`, `‖f‖_p ≤ QTilde^𝕋_p ‖f‖_{F^0_{p,2}(𝕋^d)}` with
`QTilde^𝕋_p = Torus.squareSynthesisConst d p`. The partial sums `∑_{j < J} Δ_j f` tend to `f`
(`Torus.tendsto_sum_lpBlock`) and equal `∑_{j < J} psiDual_j ⋆ Δ_j f`, whose `L_p` norms the
synthesis bound on the torus (`Torus.eLpNorm_sum_econv_le`) for the family `(psiDual_j)_j`
controls. -/
theorem enorm_le_triebelLizorkinNorm_zero_two [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖f‖ₑ ≤ squareSynthesisConst d p * triebelLizorkinNorm 0 2 f := by
  have h : Tendsto (fun J => ‖∑ j ∈ Finset.range J, lpBlock hp j f‖ₑ) atTop (𝓝 ‖f‖ₑ) :=
    (tendsto_sum_lpBlock hp f).eNorm
  have hblock : (fun t => lqNorm 2 fun j => ‖lpBlock hp j f t‖ₑ) =ᵐ[volume]
      fun t => lqNorm 2 fun j => ‖blockFun j f t‖ₑ := by
    filter_upwards [ae_all_iff.2 fun j => lpBlock_ae_eq_blockFun hp j f] with t ht
    simp only [ht]
  refine le_of_tendsto' h fun J => ?_
  rw [Lp.eNorm_def, ← eLpNorm_congr_ae (sum_econv_psiDual_lpBlock_ae hp _ f),
    triebelLizorkinNorm_zero_left, ← eLpNorm_congr_ae hblock]
  exact eLpNorm_sum_econv_le Rd.isCZFamily_psiDual farMass_psiDual_le hp1 hp _
    (fun j => (Lp.stronglyMeasurable _).measurable) fun j => Lp.memLp _

/-- **The square function theorem on the torus**: for `d ≥ 1` and `1 < p < ∞`, the subspace
`F^0_{p,2}(𝕋^d)` of `L_p(𝕋^d)` is all of `L_p(𝕋^d)`. The norms are equivalent by
`Torus.triebelLizorkinNorm_zero_two_le` and `Torus.enorm_le_triebelLizorkinNorm_zero_two`. -/
theorem triebelLizorkinSpace_zero_two_eq_top [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) :
    triebelLizorkinSpace (d := d) (p := p) 0 2 one_le_two = ⊤ :=
  Submodule.eq_top_iff'.2 fun f => memTriebelLizorkin_zero_two hp1 hp f

/-- **`B^s_{p,min(p,2)}(𝕋^d) ⊆ F^s_{p,2}(𝕋^d)` for every `s ≥ 0`**: for `d ≥ 1` and
`1 < p < ∞`; for `s > 0` this is the Besov sandwich (`Torus.memTriebelLizorkin_of_memBesov`), and
for `s = 0` the square function theorem gives `F^0_{p,2}(𝕋^d) = L_p(𝕋^d)`. This is the torus
form of `Rd.memTriebelLizorkin_two_of_memApprox`. -/
theorem memTriebelLizorkin_two_of_memBesov [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 ≤ s) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : (trigScheme d).MemBesov volume p s (min p 2) f) : MemTriebelLizorkin s 2 f := by
  rcases hs.lt_or_eq with hs | rfl
  · exact memTriebelLizorkin_of_memBesov hp hs one_le_two hf
  · exact memTriebelLizorkin_zero_two hp1 hp f

end Torus
