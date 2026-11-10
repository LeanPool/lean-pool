/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Basic
public import LeanPool.HyperellipticCurves.Curve.TraceMatrix
public import LeanPool.HyperellipticCurves.Log.Analytic.Lambda

import LeanPool.HyperellipticCurves.ForMathlib.DualAnnihilator
import LeanPool.HyperellipticCurves.ForMathlib.PolynomialDegreeLT
import LeanPool.HyperellipticCurves.ForMathlib.RankBaseChange
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The rank hypothesis and the annihilating differential

The opening nodes of the counting chapter.

`ChabautyColeman.HypJac.rank` is the rational rank of the Jacobian over the arithmetic base
field, the `ℚ`-dimension of `ℚ ⊗[ℤ] J(K₀)`; no finite generation is assumed, so it is a
cardinal. The standing hypothesis of the Chabauty–Coleman method is that it is bounded by a
natural number `r` smaller than the genus; the bound of `thm:main-count` is `2r`.

Under that hypothesis the differentials pairing to zero with all of `J¹ = ker(J(K₀) → J(κ_bar))`
under the pairing `λ` of blueprint `def:lambda` form a subspace of codimension at most `r`
(`ChabautyColeman.exists_annihilator_submodule`) — one differential per residue disk is what
the improved bound spends. A differential is given by its coordinate vector `cs` in the
`ω′`-basis, and `λ` enters only through its three formal properties (additive in the class,
linear in the coordinates), so the statement is proved for an abstract pairing on an
arbitrary commutative group of rational rank `≤ r` and instantiated at
`ChabautyColeman.lambda` on `J¹` in `ChabautyColeman.exists_annihilator_tracePoly`; the rank
bound for the subgroup `J¹` comes from the rank hypothesis by flatness of `ℚ` over `ℤ`
(`ChabautyColeman.HypJac.rank_subgroup_le`).

## Main definitions

* `ChabautyColeman.HypJac.rank`: the rational rank `rk J(K₀)` of the Jacobian, a cardinal.
* `ChabautyColeman.lambdaEval`: the pairing read as a homomorphism from the group to the
  dual of the space of coordinate vectors.
* `ChabautyColeman.lambdaEvalRat`: its factorization through `ℚ ⊗[ℤ] -`.

## Main statements

* `ChabautyColeman.exists_annihilator_submodule`: the annihilating differentials form a
  subspace of codimension at most `r`.
* `ChabautyColeman.exists_annihilator_residue`: over the residue field, the numerators with
  integral annihilating representatives form a subspace of codimension at most `r`.
* `ChabautyColeman.exists_annihilator_tracePoly`: the instance at `ChabautyColeman.lambda`
  with the numerators of the trace-form basis (`ChabautyColeman.tracePoly`) — the form in
  which each residue disk of `thm:main-count` picks its own differential.

Blueprint nodes: `def:rank-hyp`, `lem:eval-factors`, `thm:annihilator`, `lem:normalize`.
-/

@[expose] public section

open Polynomial Module IsLocalRing
open scoped TensorProduct

namespace ChabautyColeman

variable (K₀ : Type*) [Field K₀] (f₀ : K₀[X]) [Fact (Odd f₀.natDegree)]

/-- **The rank of the Jacobian** over the arithmetic base field `K₀` (blueprint
`def:rank-hyp`): the `ℚ`-dimension of its rationalization. The Jacobian is written
multiplicatively, so the rationalization is `ℚ ⊗[ℤ] Additive (HypJac K₀ f₀)`; no finite
generation is assumed, so the rank is a cardinal, and the rank hypothesis of the
Chabauty–Coleman method reads `rank ≤ r` for a natural number `r < genus f₀`. -/
noncomputable def HypJac.rank : Cardinal := Module.rank ℚ (ℚ ⊗[ℤ] Additive (HypJac K₀ f₀))

variable {K₀ f₀}

/-- The rank of a subgroup of the Jacobian — in particular of the kernel of reduction `J¹`,
on which the pairing `λ` lives — is at most the rank of the Jacobian: the rationalization
`ℚ ⊗[ℤ] -` preserves the inclusion of the subgroup by flatness of `ℚ` over `ℤ`. -/
theorem HypJac.rank_subgroup_le (H : Subgroup (HypJac K₀ f₀)) :
    Module.rank ℚ (ℚ ⊗[ℤ] Additive ↥H) ≤ HypJac.rank K₀ f₀ :=
  LinearMap.rank_baseChange_le_of_injective ℚ
    (f := (MonoidHom.toAdditive H.subtype).toIntLinearMap) H.subtype_injective

section Abstract

variable {G : Type*} [CommGroup G] {L : Type*} [Field L] {n : ℕ}
  (lam : (Fin n → L) → G → L)
  (hmul : ∀ cs c c', lam cs (c * c') = lam cs c + lam cs c')
  (hadd : ∀ cs cs' c, lam (cs + cs') c = lam cs c + lam cs' c)
  (hsmul : ∀ (r : L) cs c, lam (r • cs) c = r * lam cs c)

/-- A pairing of a commutative group `G` (in the application: the kernel of reduction `J¹`
inside the Jacobian) with the coordinate vectors of the differentials, read as a
homomorphism to the dual space: `c ↦ (cs ↦ λ_cs(c))`. The group is written
multiplicatively, so the source is `Additive G`. -/
def lambdaEval : Additive G →+ Module.Dual L (Fin n → L) :=
  AddMonoidHom.mk' (fun c ↦
    { toFun cs := lam cs c.toMul
      map_add' cs cs' := hadd cs cs' _
      map_smul' r cs := hsmul r cs _ }) fun _ _ ↦ LinearMap.ext fun cs ↦ hmul cs _ _

@[simp]
theorem lambdaEval_apply (c : G) (cs : Fin n → L) :
    lambdaEval lam hmul hadd hsmul (Additive.ofMul c) cs = lam cs c :=
  rfl

variable [CharZero L]

/-- **The evaluation map factors through `⊗ ℚ`** (blueprint `lem:eval-factors`): the values
of the pairing lie in the `ℚ`-vector space `L`, so the homomorphism
`ChabautyColeman.lambdaEval` extends to a `ℚ`-linear map on the rationalized group. -/
noncomputable def lambdaEvalRat :
    ℚ ⊗[ℤ] Additive G →ₗ[ℚ] Module.Dual L (Fin n → L) :=
  (lambdaEval lam hmul hadd hsmul).toIntLinearMap.liftBaseChange ℚ

@[simp]
theorem lambdaEvalRat_tmul (q : ℚ) (c : G) :
    lambdaEvalRat lam hmul hadd hsmul (q ⊗ₜ Additive.ofMul c)
      = q • lambdaEval lam hmul hadd hsmul (Additive.ofMul c) :=
  rfl

include hmul hadd hsmul in
/-- **The space of annihilating differentials** (blueprint `thm:annihilator`): if the
rational rank of the group is at most `r`, the coordinate vectors `cs` — i.e. the
differentials `∑ cs i ω′_i` — pairing to zero with every element form a subspace of
codimension at most `r`.

The pairing enters only through the three hypotheses `hmul`, `hadd`, `hsmul`; see
`ChabautyColeman.exists_annihilator_tracePoly` for the instance at `ChabautyColeman.lambda`
on `J¹` (whose rank bound comes from `ChabautyColeman.HypJac.rank_subgroup_le` and the rank
hypothesis). -/
theorem exists_annihilator_submodule {r : ℕ} (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive G) ≤ r) :
    ∃ W : Submodule L (Fin n → L), n ≤ finrank L W + r ∧ ∀ cs ∈ W, ∀ c, lam cs c = 0 := by
  have : Module.Finite ℚ (ℚ ⊗[ℤ] Additive G) :=
    Module.rank_lt_aleph0_iff.mp (hrk.trans_lt Cardinal.natCast_lt_aleph0)
  have hle : finrank ℚ (ℚ ⊗[ℤ] Additive G) ≤ r := by
    rwa [← Nat.cast_le (α := Cardinal), Module.finrank_eq_rank]
  have hW := Module.finrank_le_finrank_iInf_ker_add_finrank (lambdaEvalRat lam hmul hadd hsmul)
  rw [Module.finrank_fin_fun] at hW
  refine ⟨⨅ q, LinearMap.ker (lambdaEvalRat lam hmul hadd hsmul q), by lia, fun cs hcs c ↦ ?_⟩
  simpa using LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hcs (1 ⊗ₜ Additive.ofMul c))

include hmul hadd hsmul in
/-- **Integral numerators for the annihilating differentials** (blueprint `lem:normalize`):
over the residue field, the numerators of the annihilating differentials that have integral
representatives form a subspace `V` of codimension at most `r`, and every element of `V` has
degree `< n` and is the reduction of an integral numerator of an annihilating differential of
degree `< n` — in particular a *nonzero* element of `V` gives a numerator with nonzero
reduction, which is what makes its order at a residue point finite.

The numerators `P i` of the basis differentials `ω′_i` enter through the two properties the
`ω′`-basis has: they are linearly independent (`hP`, from
`ChabautyColeman.sum_smul_tracePoly_ne_zero`) and each of them is the numerator of a regular
differential (`hPdeg`, the degree bound). Passing from the annihilator over `L` to the
residue field is `Polynomial.exists_submodule_map_residue`: the integral annihilating
numerators form a lattice, whose reduction has the same dimension. -/
theorem exists_annihilator_residue {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O L] [IsFractionRing O L] (P : Fin n → L[X])
    (hP : LinearIndependent L P) (hPdeg : ∀ i, (P i).degree < n) {r : ℕ}
    (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive G) ≤ r) :
    ∃ V : Submodule (ResidueField O) (ResidueField O)[X], n ≤ finrank (ResidueField O) V + r ∧
      ∀ h ∈ V, h.degree < n ∧ ∃ (cs : Fin n → L) (h₀ : O[X]), (∀ c, lam cs c = 0) ∧
        h₀.map (residue O) = h ∧ h₀.degree < n ∧
        h₀.map (algebraMap O L) = ∑ i, cs i • P i := by
  obtain ⟨W, hW, hann⟩ := exists_annihilator_submodule lam hmul hadd hsmul hrk
  set F := Fintype.linearCombination L P
  have hdeg : ∀ h ∈ Submodule.map F W, h.degree < n := by
    rintro h ⟨cs, -, rfl⟩
    simp only [F, Fintype.linearCombination_apply]
    exact (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
      fun i _ ↦ (degree_smul_le _ _).trans_lt (hPdeg i))
  obtain ⟨V, hV, hlift⟩ := Polynomial.exists_submodule_map_residue O (Submodule.map F W) hdeg
  refine ⟨V, ?_, fun h hh ↦ ?_⟩
  · have hWF : finrank L W = finrank L (Submodule.map F W) :=
      (Submodule.equivMapOfInjective F hP.fintypeLinearCombination_injective W).finrank_eq
    lia
  · obtain ⟨h₀, hres, cs, hcsW, hcs⟩ := hlift h hh
    have h₀deg : h₀.degree < n := by
      rw [← degree_map_eq_of_injective (IsFractionRing.injective O L)]
      exact hdeg _ ⟨cs, hcsW, hcs⟩
    exact ⟨hres ▸ degree_map_le.trans_lt h₀deg, cs, h₀, hann cs hcsW, hres, h₀deg, hcs.symm⟩

end Abstract

section AnnihilatorTracePoly

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [Invertible (2 : O)] {C : HyperellipticCurve O} [C.IsOdd]
  {uτ vτ w c₁ c₂ : O[X]}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {π : O} {p e : ℕ}
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The annihilating differentials, normalized in the trace-form basis** (blueprint
`thm:annihilator` composed with `lem:normalize` and the trace-form numerators): under the
rank hypothesis, there is a subspace `V` of `(ResidueField O)[X]` of codimension at most `r`
(so `V ≠ ⊥` as soon as `r < uτ.natDegree`) consisting of reductions of integral numerators of
differentials annihilating `λ` on all of `J¹`: every `h ∈ V` is the reduction of an integral
numerator `h₀` of degree `< uτ.natDegree` whose coordinates in the trace-form basis are the
coefficient vector `cs`; a *nonzero* `h` therefore gives a numerator with nonzero reduction,
which is what makes its order at a residue point finite. `V` depends on `τ` alone, not on any
residue disk, so each disk of blueprint `thm:main-count` picks its own differential out of
`V`. -/
theorem exists_annihilator_tracePoly
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - C.f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    {r : ℕ} (hrk : HypJac.rank K₀ C₀.f ≤ r) :
    ∃ V : Submodule (ResidueField O) (ResidueField O)[X],
      uτ.natDegree ≤ finrank (ResidueField O) V + r ∧
      ∀ h ∈ V, h.degree < uτ.natDegree ∧ ∃ (cs : Fin uτ.natDegree → FractionRing O) (h₀ : O[X]),
        (∀ c, lambda hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot hcc ha hbv
            hsplit hunit hd hram hpe hf₀ c = 0)
        ∧ h₀.map (residue O) = h ∧ h₀.degree < uτ.natDegree
        ∧ h₀.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
            tracePoly (uτ.map (algebraMap O (FractionRing O)))
              (c₂.map (algebraMap O (FractionRing O)))
              (Fin.cast (hu.natDegree_map (algebraMap O (FractionRing O))).symm i) := by
  set φ := algebraMap O (FractionRing O)
  set P : Fin uτ.natDegree → (FractionRing O)[X] :=
    fun i ↦ tracePoly (uτ.map φ) (c₂.map φ) (Fin.cast (hu.natDegree_map φ).symm i)
  have hdu : uτ.natDegree = (uτ.map φ).natDegree := (hu.natDegree_map φ).symm
  have hcop : IsCoprime (uτ.map φ) (c₂.map φ) :=
    ⟨c₁.map φ, 2 * vτ.map φ, by linear_combination map_bezout φ hbez⟩
  have hPne0 (cs : Fin uτ.natDegree → FractionRing O) (hcs : cs ≠ 0) : ∑ i, cs i • P i ≠ 0 := by
    have hre : ∑ i, cs i • P i
        = ∑ l, cs (Fin.cast hdu.symm l) • tracePoly (uτ.map φ) (c₂.map φ) l :=
      Fintype.sum_equiv (finCongr hdu) _ _ fun i ↦ rfl
    rw [hre]
    refine sum_smul_tracePoly_ne_zero (hu.map φ) hcop fun h0 ↦ hcs ?_
    exact funext fun i ↦ by simpa using congrFun h0 (Fin.cast hdu i)
  have hPne : LinearIndependent (FractionRing O) P :=
    Fintype.linearIndependent_iff.mpr fun g hg i ↦ congrFun (not_imp_not.mp (hPne0 g) hg) i
  have hPdeg (i : Fin uτ.natDegree) : (P i).degree < uτ.natDegree :=
    (degree_tracePoly_lt _).trans_le (mod_cast (hu.natDegree_map φ).le)
  exact exists_annihilator_residue
    (fun cs c ↦ lambda hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c)
    (fun cs c c' ↦ lambda_mul hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot hcc
        ha hbv hsplit hunit hd hram hpe hf₀ c c')
    (fun cs cs' c ↦ lambda_add_left hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot
        hcc ha hbv hsplit hunit hd hram hpe hf₀ cs' c)
    (fun t cs c ↦ lambda_smul_left hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot
        hcc ha hbv hsplit hunit hd hram hpe hf₀ t c)
    (O := O) P hPne hPdeg
    ((HypJac.rank_subgroup_le (J1 K₀ C₀.f C.monic_f C.natDegree_pos hf₀)).trans hrk)

end AnnihilatorTracePoly

end ChabautyColeman

end
