/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Hyperbolic
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.RankEight
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.RankTwo
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Reducedness
public import LeanPool.CompositionAlgebrasOverRings.LGRing.ConstantRank
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Semilocal
public import LeanPool.CompositionAlgebrasOverRings.Module.IdempotentFactor

/-!
# Reduced and split composition algebras (`GPR 22.16`)

The structure theorems in ranks two, four, and eight identify a reduced composition algebra with
the split quadratic algebra, twisted matrices on a line bundle, or twisted Zorn matrices on a
rank-three projective module. If constant-rank finite projectives over every idempotent factor are
free, the latter two presentations are the standard split models. This proves the converse half
of `GPR 22.16`; the LG-ring theorem follows because idempotent factors remain LG and their
constant-rank projectives are free (`GPR 11.24`, `GN 2.6(b)`).

⚠ **On "division".** In this file "division algebra" is expressed by
`ConicAlgebra.HasTwoSidedInverses` — every nonzero element has a two-sided inverse — which in
general is weaker than being a division algebra in the sense of `GPR 8.6`. For composition algebras
over a field, which are alternative, the two agree once `1 ≠ 0` (`GPR 13.8`,
`ConicAlgebra.IsComposition.isDivision_iff_hasTwoSidedInverses`), and
`ConicAlgebra.IsComposition.isSplitOfRank_iff_not_isDivision` restates the field case of `GPR 22.18`
with `IsDivision`; both are in `Composition/Fields/Basic.lean`.

## Main results

* `ConicAlgebra.isSplitOfRank_one` : the rank-one case.
* `ConicAlgebra.IsElementaryIdempotent.isSplitOfRank_two` : the rank-two case.
* `ConicAlgebra.IsElementaryIdempotent.isSplitOfRank_four_of_isLGRing` : the rank-four case.
* `ConicAlgebra.IsElementaryIdempotent.isSplitOfRank_eight_of_isLGRing` : the rank-eight case.
* `ConicAlgebra.IsReduced.isSplit_of_projectiveConstantRankFree` : the converse of
  **`GPR 22.16`** under `GPR`'s own hypothesis, that constant-rank finite projective `k`-modules
  are free; `ConicAlgebra.IsElementaryIdempotent.ProjectiveConstantRankFree.onFactors` passes the
  hypothesis to the idempotent factors.
* `ConicAlgebra.IsReduced.isSplit_of_projective_constantRank_free_on_factors` : the same under
  the factorwise freeness hypothesis.
* `ConicAlgebra.IsReduced.isSplit_of_isLGRing` : **`GPR 22.16`**, reduced implies split over an
  LG ring.
* `ConicAlgebra.IsComposition.isSplitOfRank_iff_isGPRIsotropic_of_projectiveConstantRankFree`,
  `IsComposition.isSplitOfRank_iff_exists_isometryEquiv_dualProd_of_projectiveConstantRankFree` :
  **`GPR 22.18`** (i) ↔ (ii) ↔ (iii) under `GPR`'s hypothesis, in ranks two, four, and eight.
* `ConicAlgebra.IsComposition.isSplitOfRank_iff_isGPRIsotropic_of_isLGRing`,
  `ConicAlgebra.IsComposition.isSplitOfRank_iff_exists_isometryEquiv_dualProd_of_isLGRing`,
  `ConicAlgebra.IsComposition.isSplitOfRank_of_isometryEquiv_dualProd` : the LG-ring case.
* `ConicAlgebra.isGPRIsotropic_norm_of_isometryEquiv_dualProd` : a hyperbolic norm is isotropic
  (`GPR 22.9`, (iv) ⇒ (iii)), with no hypothesis on the hyperbolic module.
* `ConicAlgebra.IsComposition.isSplitOfRank_iff_not_hasTwoSidedInverses` : over a field, splitness
  is equivalent to failure of the division property (**`GPR 22.18`**).
* `ConicAlgebra.IsComposition.isSplitOfRank_iff_not_anisotropic_of_pid` : over a PID, splitness
  is equivalent to the existence of a nonzero null vector (**`GPR 22.19`**).
* `ConicAlgebra.IsComposition.isSplitOfRank_iff_not_noZeroDivisors_of_pid` : over a PID,
  splitness is equivalent to having zero divisors (**`GPR 22.19`**).

Together with `isSplitOfRank_iff_isGPRIsotropic_of_pid` these are conditions (ii)–(v) of
`GPR 22.19`. Condition (i), splitness after extension to the fraction field, is
`Composition/Fields/FractionField.lean`.

## References

* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Lemma 2.6(b).
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.24,
  22.16, 22.18--22.19.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A]
  [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A} {c : A}

omit [SMulCommClass k A A] [IsAlternative A] in
/-- A constant-rank-one conic algebra over a nontrivial ring is the standard rank-one algebra. -/
theorem isSplitOfRank_one [Nontrivial k]
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) : C.IsSplitOfRank 1 :=
  exists_isometryEquiv_map_one_map_mul_of_rankAtStalk_eq_one C (baseRing k) hA
    (by rw [Module.rankAtStalk_self]; rfl)

namespace IsElementaryIdempotent

/-- The factor-stable freeness hypothesis used in the converse of `GPR 22.16`: every finite
projective module of constant rank over every idempotent factor of `k` is free. -/
def ProjectiveConstantRankFreeOnFactors (k : Type u) [CommRing k] : Prop :=
  ∀ (e : k), IsIdempotentElem e →
    ∀ (M : Type (max u v)) [AddCommGroup M] [Module (k ⧸ Ideal.span {1 - e}) M]
      [Module.Finite (k ⧸ Ideal.span {1 - e}) M]
      [Module.Projective (k ⧸ Ideal.span {1 - e}) M], ∀ (r : ℕ),
      (Module.rankAtStalk (R := k ⧸ Ideal.span {1 - e}) M = fun _ ↦ r) →
        Module.Free (k ⧸ Ideal.span {1 - e}) M

/-- **`GPR`'s freeness hypothesis** in `GPR 22.16`–`22.18`: every finitely generated projective
`k`-module of constant rank (in the universe `w`) is free. It holds over every LG ring
(`ProjectiveConstantRankFree.of_isLGRing`, `GPR 11.24`), and its factorwise form
`ProjectiveConstantRankFreeOnFactors` follows from it (`ProjectiveConstantRankFree.onFactors`). -/
def ProjectiveConstantRankFree (k : Type u) [CommRing k] : Prop :=
  ∀ (M : Type w) [AddCommGroup M] [Module k M] [Module.Finite k M] [Module.Projective k M],
    ∀ (r : ℕ), (Module.rankAtStalk (R := k) M = fun _ ↦ r) → Module.Free k M

/-- `GPR`'s freeness hypothesis implies its factorwise form: a constant-rank projective module over
an idempotent factor `k ⧸ (1 - e)` is free, by `Module.free_of_forall_free_of_isIdempotentElem`. -/
theorem ProjectiveConstantRankFree.onFactors (h : ProjectiveConstantRankFree.{u, max u v} k) :
    ProjectiveConstantRankFreeOnFactors.{u, v} k :=
  fun _ he M _ _ _ _ r hM ↦ Module.free_of_forall_free_of_isIdempotentElem he
    (fun N _ _ _ _ r hN ↦ h N r hN) M r hM

/-- Over an LG ring every finitely generated projective module of constant rank is free
(`GPR 11.24`, `GN 2.6(b)`), so `GPR`'s freeness hypothesis holds. -/
theorem ProjectiveConstantRankFree.of_isLGRing (hLG : IsLGRing k) :
    ProjectiveConstantRankFree.{u, w} k :=
  fun M _ _ _ _ r hM ↦ Module.free_of_isLGRing_of_rankAtStalk_eq hLG r M hM

private theorem finrank_eq_of_rankAtStalk_eq [Nontrivial k]
    {M : Type v} [AddCommGroup M] [Module k M] [Module.Free k M]
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ n) : Module.finrank k M = n := by
  obtain ⟨p, hp⟩ := Ideal.exists_maximal k
  have h := congrFun (Module.rankAtStalk_eq_finrank_of_free.symm.trans hM)
    ⟨p, hp.isPrime⟩
  simpa only [Pi.natCast_apply, Nat.cast_id] using h

omit [IsAlternative A] in
/-- **`GPR 22.16`, rank two:** a reduced constant-rank-two composition algebra is split. -/
theorem isSplitOfRank_two (hc : C.IsElementaryIdempotent c)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) : C.IsSplitOfRank 2 := by
  let e := hc.splitEtaleEquiv hA
  have hiso : (splitEtale k).Isomorphic C :=
    ⟨⟨e, fun x ↦ by
        rw [splitEtale_norm]
        exact hc.norm_splitEtaleEquiv hA x⟩,
      hc.splitEtaleEquiv_one hA, hc.splitEtaleEquiv_mul hA⟩
  exact hiso.symm

/-- **`GPR 22.16`, rank four:** over a nontrivial LG ring, a reduced constant-rank-four
composition algebra is split. -/
theorem isSplitOfRank_four_of_isLGRing [Nontrivial k]
    (hc : C.IsElementaryIdempotent c) (hLG : IsLGRing k)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) : C.IsSplitOfRank 4 := by
  let L := TwistingModule (k := k) c
  let : Module.Finite k L := IsAlternative.finite_peirceComponent true false
  let : Module.Projective k L :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  have hL : Module.rankAtStalk (R := k) L = 1 :=
    hc.rankAtStalk_offDiagonal_eq_one hcomp.isMultiplicative
      (hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)) hA true
  let : Module.Free k L := Module.free_of_isLGRing_of_rankAtStalk_eq hLG 1 L hL
  let b : Module.Basis Unit k L :=
    Module.basisUnique Unit (finrank_eq_of_rankAtStalk_eq hL)
  exact (hc.isomorphic_twistedMat (k := k) hcomp hA).symm.trans
    (isomorphic_twistedMat_ofBasis k b)

/-- **`GPR 22.16`, rank four under its abstract freeness hypothesis.** -/
theorem isSplitOfRank_four_of_projective_constantRank_free [Nontrivial k]
    (hc : C.IsElementaryIdempotent c)
    (hfree : ∀ (M : Type v) [AddCommGroup M] [Module k M] [Module.Finite k M]
      [Module.Projective k M], ∀ (r : ℕ),
      (Module.rankAtStalk (R := k) M = fun _ ↦ r) → Module.Free k M)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) : C.IsSplitOfRank 4 := by
  let L := TwistingModule (k := k) c
  let : Module.Finite k L := IsAlternative.finite_peirceComponent true false
  let : Module.Projective k L :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  have hL : Module.rankAtStalk (R := k) L = fun _ ↦ 1 :=
    hc.rankAtStalk_offDiagonal_eq_one hcomp.isMultiplicative
      (hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)) hA true
  let : Module.Free k L := hfree L 1 hL
  let b : Module.Basis Unit k L := Module.basisUnique Unit (finrank_eq_of_rankAtStalk_eq hL)
  exact (hc.isomorphic_twistedMat (k := k) hcomp hA).symm.trans
    (isomorphic_twistedMat_ofBasis k b)

/-- **`GPR 22.19`, rank four:** over a PID, a reduced constant-rank-four composition algebra is
split. The twisting line is projective, hence flat and torsion-free, and a finite torsion-free
module over a PID is free. -/
theorem isSplitOfRank_four_of_pid [IsDomain k] [IsPrincipalIdealRing k]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) : C.IsSplitOfRank 4 := by
  let L := TwistingModule (k := k) c
  let : Module.Finite k L := IsAlternative.finite_peirceComponent true false
  let : Module.Projective k L :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  let : Module.IsTorsionFree k L := inferInstance
  let : Module.Free k L := Module.free_of_finite_type_torsion_free'
  have hL : Module.rankAtStalk (R := k) L = 1 :=
    hc.rankAtStalk_offDiagonal_eq_one hcomp.isMultiplicative
      (hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)) hA true
  let b : Module.Basis Unit k L :=
    Module.basisUnique Unit (finrank_eq_of_rankAtStalk_eq hL)
  exact (hc.isomorphic_twistedMat (k := k) hcomp hA).symm.trans
    (isomorphic_twistedMat_ofBasis k b)

/-- **`GPR 22.16`, rank eight:** over a nontrivial LG ring, a reduced constant-rank-eight
composition algebra is split. -/
theorem isSplitOfRank_eight_of_isLGRing [Nontrivial k]
    (hc : C.IsElementaryIdempotent c) (hLG : IsLGRing k)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) : C.IsSplitOfRank 8 := by
  let M := ZornTwistingModule (k := k) c
  let : Module.Finite k M := IsAlternative.finite_peirceComponent true false
  let : Module.Projective k M :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let P := hc.peirceVectorProductPair hcomp.isMultiplicative hreg
  have hM : Module.rankAtStalk (R := k) M = 3 :=
    hc.rankAtStalk_twistingModule_eq_three hcomp.isMultiplicative hreg hA
  let : Module.Free k M := Module.free_of_isLGRing_of_rankAtStalk_eq hLG 3 M hM
  let b : Module.Basis (Fin 3) k M :=
    Module.finBasisOfFinrankEq k M (finrank_eq_of_rankAtStalk_eq hM)
  exact (hc.isomorphic_twistedZor (k := k) hcomp.isMultiplicative hreg).symm.trans
    (isomorphic_twistedZor_of_exists_basis P b)

/-- **`GPR 22.16`, rank eight under its abstract freeness hypothesis.** -/
theorem isSplitOfRank_eight_of_projective_constantRank_free [Nontrivial k]
    (hc : C.IsElementaryIdempotent c)
    (hfree : ∀ (M : Type v) [AddCommGroup M] [Module k M] [Module.Finite k M]
      [Module.Projective k M], ∀ (r : ℕ),
      (Module.rankAtStalk (R := k) M = fun _ ↦ r) → Module.Free k M)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) : C.IsSplitOfRank 8 := by
  let M := ZornTwistingModule (k := k) c
  let : Module.Finite k M := IsAlternative.finite_peirceComponent true false
  let : Module.Projective k M :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let P := hc.peirceVectorProductPair hcomp.isMultiplicative hreg
  have hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3 :=
    hc.rankAtStalk_twistingModule_eq_three hcomp.isMultiplicative hreg hA
  let : Module.Free k M := hfree M 3 hM
  let b : Module.Basis (Fin 3) k M :=
    Module.finBasisOfFinrankEq k M (finrank_eq_of_rankAtStalk_eq hM)
  exact (hc.isomorphic_twistedZor (k := k) hcomp.isMultiplicative hreg).symm.trans
    (isomorphic_twistedZor_of_exists_basis P b)

/-- **`GPR 22.19`, rank eight:** over a PID, a reduced constant-rank-eight composition algebra is
split. The rank-three twisting module is projective, hence finite free over the PID. -/
theorem isSplitOfRank_eight_of_pid [IsDomain k] [IsPrincipalIdealRing k]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) : C.IsSplitOfRank 8 := by
  let M := ZornTwistingModule (k := k) c
  let : Module.Finite k M := IsAlternative.finite_peirceComponent true false
  let : Module.Projective k M :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  let : Module.IsTorsionFree k M := inferInstance
  let : Module.Free k M := Module.free_of_finite_type_torsion_free'
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let P := hc.peirceVectorProductPair hcomp.isMultiplicative hreg
  have hM : Module.rankAtStalk (R := k) M = 3 :=
    hc.rankAtStalk_twistingModule_eq_three hcomp.isMultiplicative hreg hA
  let b : Module.Basis (Fin 3) k M :=
    Module.finBasisOfFinrankEq k M (finrank_eq_of_rankAtStalk_eq hM)
  exact (hc.isomorphic_twistedZor (k := k) hcomp.isMultiplicative hreg).symm.trans
    (isomorphic_twistedZor_of_exists_basis P b)

end IsElementaryIdempotent

namespace IsReduced

omit [IsAlternative A] in
/-- **Full converse of `GPR 22.16`, in a factor-stable formulation of its freeness hypothesis.**
If finite projective constant-rank modules over the idempotent factors of `k` are free, every
reduced composition algebra over `k` is split. Together with `IsSplit.isReduced`, this gives both
directions of `GPR 22.16` over arbitrary commutative rings satisfying that hypothesis. -/
theorem isSplit_of_projective_constantRank_free_on_factors (h : C.IsReduced)
    (hfree : IsElementaryIdempotent.ProjectiveConstantRankFreeOnFactors.{u, v} k) :
    C.IsSplit := by
  let S₁ := SplitRankFactor k A 1
  let S₂ := SplitRankFactor k A 2
  let S₄ := SplitRankFactor k A 4
  let S₈ := SplitRankFactor k A 8
  have hrank₁ : Module.rankAtStalk (R := S₁) (S₁ ⊗[k] A) = fun _ ↦ 1 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 1
  have hrank₂ : Module.rankAtStalk (R := S₂) (S₂ ⊗[k] A) = fun _ ↦ 2 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 2
  have hrank₄ : Module.rankAtStalk (R := S₄) (S₄ ⊗[k] A) = fun _ ↦ 4 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 4
  have hrank₈ : Module.rankAtStalk (R := S₈) (S₈ ⊗[k] A) = fun _ ↦ 8 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 8
  have hone : (C.splitRankComponent 1).IsSplitOfRank 1 := by
    rcases subsingleton_or_nontrivial S₁ with hS | hS
    · let := hS; exact Isomorphic.of_subsingleton
    · let := hS; exact isSplitOfRank_one hrank₁
  have htwo : (C.splitRankComponent 2).IsSplitOfRank 2 := by
    obtain ⟨c₂, hc₂⟩ := h.hasElementaryIdempotent_splitRankComponent_two
    exact hc₂.isSplitOfRank_two hrank₂
  have hfour : (C.splitRankComponent 4).IsSplitOfRank 4 := by
    rcases subsingleton_or_nontrivial S₄ with hS | hS
    · let := hS; exact Isomorphic.of_subsingleton
    · let := hS
      have hc := h.isComposition.baseChangeOfProjective S₄
      let : IsAlternative (S₄ ⊗[k] A) := hc.isAlternative_general
      obtain ⟨c₄, hc₄⟩ := h.hasElementaryIdempotent_splitRankComponent_four
      exact hc₄.isSplitOfRank_four_of_projective_constantRank_free
        (hfree _ (Module.isIdempotentElem_rankIdempotent k A 4)) hc hrank₄
  have height : (C.splitRankComponent 8).IsSplitOfRank 8 := by
    rcases subsingleton_or_nontrivial S₈ with hS | hS
    · let := hS; exact Isomorphic.of_subsingleton
    · let := hS
      have hc := h.isComposition.baseChangeOfProjective S₈
      let : IsAlternative (S₈ ⊗[k] A) := hc.isAlternative_general
      obtain ⟨c₈, hc₈⟩ := h.hasElementaryIdempotent_splitRankComponent_eight
      exact hc₈.isSplitOfRank_eight_of_projective_constantRank_free
        (hfree _ (Module.isIdempotentElem_rankIdempotent k A 8)) hc hrank₈
  exact ⟨h.isComposition, hone, htwo, hfour, height⟩

omit [IsAlternative A] in
/-- **`GPR 22.16`, converse, under `GPR`'s own hypothesis.** If every finitely generated projective
`k`-module of constant rank is free, every reduced composition algebra over `k` is split. The
hypothesis passes to the idempotent factors of the rank decomposition
(`IsElementaryIdempotent.ProjectiveConstantRankFree.onFactors`). -/
theorem isSplit_of_projectiveConstantRankFree (h : C.IsReduced)
    (hfree : IsElementaryIdempotent.ProjectiveConstantRankFree.{u, max u v} k) : C.IsSplit :=
  h.isSplit_of_projective_constantRank_free_on_factors hfree.onFactors

omit [IsAlternative A] in
/-- **`GPR 22.16`, reduced ⇒ split over an LG ring.** Each rank component has constant rank by
the rank decomposition. Its base is again LG because it is an idempotent factor; ranks four and
eight are therefore untwisted by freeness of constant-rank projective modules. -/
theorem isSplit_of_isLGRing (h : C.IsReduced) (hLG : IsLGRing k) : C.IsSplit := by
  let S₁ := SplitRankFactor k A 1
  let S₂ := SplitRankFactor k A 2
  let S₄ := SplitRankFactor k A 4
  let S₈ := SplitRankFactor k A 8
  have hrank₁ : Module.rankAtStalk (R := S₁) (S₁ ⊗[k] A) = fun _ ↦ 1 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 1
  have hrank₂ : Module.rankAtStalk (R := S₂) (S₂ ⊗[k] A) = fun _ ↦ 2 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 2
  have hrank₄ : Module.rankAtStalk (R := S₄) (S₄ ⊗[k] A) = fun _ ↦ 4 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 4
  have hrank₈ : Module.rankAtStalk (R := S₈) (S₈ ⊗[k] A) = fun _ ↦ 8 :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A 8
  have hcomp₄ := h.isComposition.baseChangeOfProjective S₄
  have hcomp₈ := h.isComposition.baseChangeOfProjective S₈
  have hone : (C.splitRankComponent 1).IsSplitOfRank 1 := by
    rcases subsingleton_or_nontrivial S₁ with hS₁ | hS₁
    · let := hS₁
      exact Isomorphic.of_subsingleton
    · let := hS₁
      exact isSplitOfRank_one hrank₁
  have htwo : (C.splitRankComponent 2).IsSplitOfRank 2 := by
    obtain ⟨c₂, hc₂⟩ := h.hasElementaryIdempotent_splitRankComponent_two
    exact hc₂.isSplitOfRank_two hrank₂
  have hfour : (C.splitRankComponent 4).IsSplitOfRank 4 := by
    rcases subsingleton_or_nontrivial S₄ with hS₄ | hS₄
    · let := hS₄
      exact Isomorphic.of_subsingleton
    · let := hS₄
      have hLG₄ : IsLGRing S₄ :=
        hLG.quotient_span_one_sub_of_isIdempotentElem
          (Module.isIdempotentElem_rankIdempotent k A 4)
      let hreg₄ := hcomp₄.isGPRRegular_of_rankAtStalk_ne_one hrank₄ (by omega)
      let : IsAlternative (S₄ ⊗[k] A) :=
        hcomp₄.isMultiplicative.isAlternative hreg₄.isGPRNondegenerate
      obtain ⟨c₄, hc₄⟩ := h.hasElementaryIdempotent_splitRankComponent_four
      exact hc₄.isSplitOfRank_four_of_isLGRing hLG₄ hcomp₄ hrank₄
  have height : (C.splitRankComponent 8).IsSplitOfRank 8 := by
    rcases subsingleton_or_nontrivial S₈ with hS₈ | hS₈
    · let := hS₈
      exact Isomorphic.of_subsingleton
    · let := hS₈
      have hLG₈ : IsLGRing S₈ :=
        hLG.quotient_span_one_sub_of_isIdempotentElem
          (Module.isIdempotentElem_rankIdempotent k A 8)
      let hreg₈ := hcomp₈.isGPRRegular_of_rankAtStalk_ne_one hrank₈ (by omega)
      let : IsAlternative (S₈ ⊗[k] A) :=
        hcomp₈.isMultiplicative.isAlternative hreg₈.isGPRNondegenerate
      obtain ⟨c₈, hc₈⟩ := h.hasElementaryIdempotent_splitRankComponent_eight
      exact hc₈.isSplitOfRank_eight_of_isLGRing hLG₈ hcomp₈ hrank₈
  exact ⟨h.isComposition, hone, htwo, hfour, height⟩

end IsReduced

omit [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A] [Module.Finite k A]
  [Module.Projective k A] in
/-- **A hyperbolic norm is isotropic** (`GPR 22.9`, (iv) ⇒ (iii)). If `n ≅ dualProd k M`, write
`1 = e₁ + e₂` across the two totally isotropic summands: the preimage `(φ, m)` of `1` has
`φ m = n(1) = 1`, so `m` is unimodular and `(0, m)` is a unimodular null vector. No hypothesis on
`M` is needed. -/
theorem isGPRIsotropic_norm_of_isometryEquiv_dualProd {M : Type*} [AddCommGroup M] [Module k M]
    (e : (QuadraticForm.dualProd k M).IsometryEquiv C.norm) : C.norm.IsGPRIsotropic := by
  have h1 : QuadraticForm.dualProd k M (e.symm 1) = 1 := by rw [e.symm.map_app, C.norm_one]
  have hm : Module.IsUnimodular k (e.symm 1).2 :=
    Module.isUnimodular_of_apply_eq_one (f := (e.symm 1).1) h1
  exact (QuadraticForm.isGPRIsotropic_dualProd hm).map_isometryEquiv e

namespace IsComposition

omit [IsAlternative A] in
/-- **`GPR 22.18`, split ↔ isotropic, under `GPR`'s hypothesis.** If every finitely generated
projective `k`-module of constant rank is free, a composition algebra of constant rank two, four,
or eight is split exactly when its norm has a unimodular null vector. The reverse implication
produces an elementary idempotent (`GPR 22.9`) and then untwists the reduced model with the
freeness hypothesis (`GPR 22.16`). -/
theorem isSplitOfRank_iff_isGPRIsotropic_of_projectiveConstantRankFree [Nontrivial k]
    (hfree : IsElementaryIdempotent.ProjectiveConstantRankFree.{u, v} k)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) : C.IsSplitOfRank r ↔ C.norm.IsGPRIsotropic := by
  constructor
  · intro hsplit
    obtain ⟨c, hc⟩ := hsplit.hasElementaryIdempotent_of_two_or_four_or_eight hr
    exact hc.isGPRIsotropic
  · intro hiso
    have hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
    obtain ⟨c, hc⟩ := exists_isElementaryIdempotent_of_isGPRIsotropic
      hreg hcomp.isMultiplicative hiso
    let : IsAlternative A :=
      hcomp.isMultiplicative.isAlternative hreg.isGPRNondegenerate
    rcases hr with rfl | rfl | rfl
    · exact hc.isSplitOfRank_two hA
    · exact hc.isSplitOfRank_four_of_projective_constantRank_free hfree hcomp hA
    · exact hc.isSplitOfRank_eight_of_projective_constantRank_free hfree hcomp hA

omit [IsAlternative A] in
/-- **`GPR 22.18`, split ↔ hyperbolic, under `GPR`'s hypothesis.** If every finitely generated
projective `k`-module of constant rank is free, a composition algebra of constant rank two, four,
or eight is split exactly when its norm is hyperbolic, i.e. isometric to
`QuadraticForm.dualProd k M` for a finitely generated projective `M`. Forwards, an elementary
idempotent gives the Peirce presentation `peirceHyperbolicIsometryEquiv` (`GPR 22.9`,
(i) ⇒ (iv)); backwards, a hyperbolic norm is isotropic
(`isGPRIsotropic_norm_of_isometryEquiv_dualProd`). -/
theorem isSplitOfRank_iff_exists_isometryEquiv_dualProd_of_projectiveConstantRankFree
    [Nontrivial k] (hfree : IsElementaryIdempotent.ProjectiveConstantRankFree.{u, v} k)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.IsSplitOfRank r ↔ ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module k M)
      (_ : Module.Finite k M) (_ : Module.Projective k M),
      Nonempty ((QuadraticForm.dualProd k M).IsometryEquiv C.norm) := by
  constructor
  · intro hsplit
    obtain ⟨c, hc⟩ := hsplit.hasElementaryIdempotent_of_two_or_four_or_eight hr
    have hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
    let : IsAlternative A := hcomp.isMultiplicative.isAlternative hreg.isGPRNondegenerate
    have := IsAlternative.finite_peirceComponent (R := k) (c := c) true false
    have := IsAlternative.projective_peirceComponent (R := k) hc.mul_self true false
    exact ⟨_, _, _, inferInstance, inferInstance,
      ⟨hc.peirceHyperbolicIsometryEquiv hcomp.isMultiplicative hreg⟩⟩
  · rintro ⟨M, _, _, _, _, ⟨e⟩⟩
    exact (hcomp.isSplitOfRank_iff_isGPRIsotropic_of_projectiveConstantRankFree hfree hA hr).mpr
      (isGPRIsotropic_norm_of_isometryEquiv_dualProd e)

omit [IsAlternative A] in
/-- **`GPR 22.18`, split ↔ hyperbolic over an LG ring**: the case of
`isSplitOfRank_iff_exists_isometryEquiv_dualProd_of_projectiveConstantRankFree` where the
freeness hypothesis is `GPR 11.24`. -/
theorem isSplitOfRank_iff_exists_isometryEquiv_dualProd_of_isLGRing [Nontrivial k]
    (hcomp : C.IsComposition.{u, v, u}) (hLG : IsLGRing k)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.IsSplitOfRank r ↔ ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module k M)
      (_ : Module.Finite k M) (_ : Module.Projective k M),
      Nonempty ((QuadraticForm.dualProd k M).IsometryEquiv C.norm) :=
  hcomp.isSplitOfRank_iff_exists_isometryEquiv_dualProd_of_projectiveConstantRankFree
    (.of_isLGRing hLG) hA hr

omit [IsAlternative A] in
/-- **`GPR 22.18`, split ↔ isotropic over an LG ring.** For a constant-rank composition
algebra of rank two, four, or eight, splitness is equivalent to the existence of a unimodular null
vector. The forward implication transports the elementary idempotent of the standard model; the
reverse implication uses `GPR 22.9` and the reduced classification of `GPR 22.16`. -/
theorem isSplitOfRank_iff_isGPRIsotropic_of_isLGRing [Nontrivial k]
    (hcomp : C.IsComposition.{u, v, u}) (hLG : IsLGRing k)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) : C.IsSplitOfRank r ↔ C.norm.IsGPRIsotropic := by
  constructor
  · intro hsplit
    obtain ⟨c, hc⟩ := hsplit.hasElementaryIdempotent_of_two_or_four_or_eight hr
    exact hc.isGPRIsotropic
  · intro hiso
    have hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
    obtain ⟨c, hc⟩ := exists_isElementaryIdempotent_of_isGPRIsotropic
      hreg hcomp.isMultiplicative hiso
    let : IsAlternative A :=
      hcomp.isMultiplicative.isAlternative hreg.isGPRNondegenerate
    rcases hr with rfl | rfl | rfl
    · exact hc.isSplitOfRank_two hA
    · exact hc.isSplitOfRank_four_of_isLGRing hLG hcomp hA
    · exact hc.isSplitOfRank_eight_of_isLGRing hLG hcomp hA

omit [IsAlternative A] in
/-- **`GPR 22.18`, hyperbolic ⇒ split over an LG ring.** A norm isometric to a hyperbolic form
`QuadraticForm.dualProd k M` is isotropic (`isGPRIsotropic_norm_of_isometryEquiv_dualProd`), with
no hypothesis on `M`; the split/isotropic equivalence finishes the argument. -/
theorem isSplitOfRank_of_isometryEquiv_dualProd [Nontrivial k]
    (hcomp : C.IsComposition.{u, v, u}) (hLG : IsLGRing k)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) {M : Type*} [AddCommGroup M] [Module k M]
    (e : (QuadraticForm.dualProd k M).IsometryEquiv C.norm) : C.IsSplitOfRank r :=
  (hcomp.isSplitOfRank_iff_isGPRIsotropic_of_isLGRing hLG hA hr).mpr
    (isGPRIsotropic_norm_of_isometryEquiv_dualProd e)

omit [IsAlternative A] in
/-- **`GPR 22.18`, split ↔ not division over a field.** For a constant-rank composition algebra
of rank two, four, or eight, splitness is equivalent to the failure of the property that every
nonzero element has a two-sided inverse. -/
theorem isSplitOfRank_iff_not_hasTwoSidedInverses {K : Type u} [Field K] {B : Type v}
    [NonAssocRing B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]
    [Module.Finite K B] [Module.Projective K B] {D : ConicAlgebra K B}
    (hcomp : D.IsComposition.{u, v, u})
    (hB : Module.rankAtStalk (R := K) B = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) : D.IsSplitOfRank r ↔ ¬ D.HasTwoSidedInverses :=
  ((hcomp.isSplitOfRank_iff_isGPRIsotropic_of_isLGRing (isLGRing_of_field K) hB hr).trans
    QuadraticMap.isGPRIsotropic_iff_not_anisotropic).trans
      (not_congr hcomp.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.symm)

omit [IsAlternative A] in
/-- **`GPR 22.19`, split ↔ GPR-isotropic over a PID.** For a constant-rank composition algebra
of rank two, four, or eight, a unimodular null vector is equivalent to splitness. Projective
twisting modules are free over the PID, replacing the LG-ring freeness step in `GPR 22.18`. -/
theorem isSplitOfRank_iff_isGPRIsotropic_of_pid [IsDomain k] [IsPrincipalIdealRing k]
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) : C.IsSplitOfRank r ↔ C.norm.IsGPRIsotropic := by
  constructor
  · intro hsplit
    obtain ⟨c, hc⟩ := hsplit.hasElementaryIdempotent_of_two_or_four_or_eight hr
    exact hc.isGPRIsotropic
  · intro hiso
    have hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
    obtain ⟨c, hc⟩ := exists_isElementaryIdempotent_of_isGPRIsotropic
      hreg hcomp.isMultiplicative hiso
    let : IsAlternative A :=
      hcomp.isMultiplicative.isAlternative hreg.isGPRNondegenerate
    rcases hr with rfl | rfl | rfl
    · exact hc.isSplitOfRank_two hA
    · exact hc.isSplitOfRank_four_of_pid hcomp hA
    · exact hc.isSplitOfRank_eight_of_pid hcomp hA

omit [IsAlternative A] in
/-- **`GPR 22.19`, split ↔ a nonzero null vector over a PID.** This is where GPR's
unimodular-vector isotropy and mathlib's failure of anisotropy become equivalent, by
`GPR Exc. 12.38(c)` (`QuadraticMap.isGPRIsotropic_iff_not_anisotropic_of_pid`). -/
theorem isSplitOfRank_iff_not_anisotropic_of_pid [IsDomain k] [IsPrincipalIdealRing k]
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) : C.IsSplitOfRank r ↔ ¬ C.norm.Anisotropic :=
  (hcomp.isSplitOfRank_iff_isGPRIsotropic_of_pid hA hr).trans
    QuadraticMap.isGPRIsotropic_iff_not_anisotropic_of_pid

omit [IsAlternative A] in
/-- **`GPR 22.19`, split ↔ zero divisors over a PID.** Here "has zero divisors" is expressed
canonically as the negation of mathlib's `NoZeroDivisors` predicate. -/
theorem isSplitOfRank_iff_not_noZeroDivisors_of_pid [IsDomain k] [IsPrincipalIdealRing k]
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) : C.IsSplitOfRank r ↔ ¬ NoZeroDivisors A :=
  (hcomp.isSplitOfRank_iff_not_anisotropic_of_pid hA hr).trans
    (not_congr hcomp.isMultiplicative.anisotropic_iff_noZeroDivisors_of_isDomain)

end IsComposition

end ConicAlgebra
