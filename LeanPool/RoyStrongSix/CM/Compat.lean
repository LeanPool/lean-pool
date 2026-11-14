/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module
public import Mathlib.RingTheory.Regular.Category

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring

-- Compatibility layer for the port of Guan–Hu's Cohen–Macaulay files
-- (github.com/Thmoas-Guan/mathlib4_fork, branch ABS-Criterion-Project-new, commit 0ff6e01f,
-- Apache-2.0).
-- Part A: the fork's names for depth lemmas that Mathlib upstreamed under new names.
-- Part B: fork lemmas not (yet) in Mathlib, copied from `Regular/Depth.lean` (l. 742–1036) and
-- `KrullDimension/Polynomial.lean` (l. 40–221). Fixes are marked `PORT`.

/-! # Compatibility lemmas for the Cohen–Macaulay and unmixedness development -/

@[expose] public section

namespace LeanPool

universe w v u

open _root_.IsLocalRing LinearMap
open RingTheory.Sequence _root_.Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R] [Small.{v} R]

open Pointwise _root_.ModuleCat IsSMulRegular

/-! ### Part A: renames -/

/-- Fork name for `ModuleCat.depth` (a notation, so that `rw` with either name works). -/
notation "moduleDepth" => ModuleCat.depth

lemma ext_subsingleton_of_lt_moduleDepth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < moduleDepth N M) : Subsingleton (Ext N M i) :=
  ModuleCat.subsingleton_ext_of_lt_depth lt

lemma moduleDepth_eq_depth_of_supp_eq [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = I.depth M :=
  ModuleCat.depth_eq_depth_of_support_eq I N M smul_lt hsupp

lemma moduleDepth_eq_of_iso_fst (M : ModuleCat.{v} R) {N N' : ModuleCat.{v} R} (e : N ≅ N') :
    moduleDepth N M = moduleDepth N' M := ModuleCat.depth_eq_of_iso_left M e

lemma moduleDepth_eq_of_iso_snd (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    moduleDepth N M = moduleDepth N M' := ModuleCat.depth_eq_of_iso_right N e

lemma moduleDepth_eq_zero_of_hom_nontrivial (N M : ModuleCat.{v} R) :
    moduleDepth N M = 0 ↔ Nontrivial (N →ₗ[R] M) :=
      ModuleCat.depth_eq_zero_iff_nontrivial_linearMap N M

lemma moduleDepth_ge_min_of_shortExact_snd_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₂ N ≥ moduleDepth S.X₁ N ⊓ moduleDepth S.X₃ N :=
  ModuleCat.depth_min_fst_trd_le_snd_left S hS N

lemma moduleDepth_eq_sSup_length_regular [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } :=
  ModuleCat.depth_eq_sSup_length_isRegular I N M smul_lt hsupp

lemma IsLocalRing.depth_eq_sSup_length_regular [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ maximalIdeal R) } :=
  IsLocalRing.depth_eq_sSup_length_isRegular M

lemma IsLocalRing.ideal_depth_eq_sSup_length_regular [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M]
    [Nontrivial M] : I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } :=
  IsLocalRing.ideal_depth_eq_sSup_length_isRegular I netop M

/-! ### Part B: fork lemmas missing from Mathlib -/

section depth

lemma moduleDepth_quotSMulTop_succ_eq_moduleDepth (N M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (QuotSMulTop x M)) + 1 = moduleDepth N M := by
  simp only [ModuleCat.depth, add_comm]  -- PORT: unfold `ModuleCat.depth`
  have iff (i : ℕ) : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) ↔
    (Subsingleton (Ext N M i) ∧ Subsingleton (Ext N M (i + 1))) := by
    refine ⟨fun h ↦ ?_, fun ⟨h1, h3⟩ ↦ ?_⟩
    · constructor
      · exact @Function.Injective.subsingleton _ _ _ ((AddCommGrpCat.mono_iff_injective _).mp
          (ShortComplex.Exact.mono_g
          (Ext.covariant_sequence_exact₂' N reg.smulShortComplex_shortExact i)
          (Ext.postcomp_smul_id_eq_zero_of_mem_annihilator mem i))) h
      · exact @Function.Surjective.subsingleton _ _ _ h ((AddCommGrpCat.epi_iff_surjective _).mp
          (ShortComplex.Exact.epi_f
          (Ext.covariant_sequence_exact₁' N reg.smulShortComplex_shortExact i (i + 1) rfl)
          (Ext.postcomp_smul_id_eq_zero_of_mem_annihilator mem (i + 1))))
    · exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' N reg.smulShortComplex_shortExact i (i + 1) rfl)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h1).eq_zero_of_src _)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h3).eq_zero_of_tgt _)
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    by_cases eq0 : i = 0
    · rw [eq0, Ext.addEquiv₀.subsingleton_congr, ModuleCat.homAddEquiv.subsingleton_congr]
      exact linearMap_subsingleton_of_mem_annihilator reg mem
    · have eq : i - 1 + 1 = i := Nat.sub_one_add_one eq0
      have : i - 1 < n := by
        enat_to_nat
        omega
      have := ((iff (i - 1)).mp (hn (i - 1) this)).2
      simpa only [eq] using this
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        enat_to_nat
        omega
      rw [add_comm, ← this]
      apply add_le_add_left
      apply le_sSup
      intro i hi
      have lt2 : i + 1 < n := by
        enat_to_nat
        omega
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

lemma Ideal.depth_quotSMulTop_succ_eq_moduleDepth (I : Ideal R) (M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ I) :
    I.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = I.depth M := by
  apply moduleDepth_quotSMulTop_succ_eq_moduleDepth _ M x reg
  simpa [LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ I)), Ideal.annihilator_quotient]

lemma IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth [IsLocalRing R] (M : ModuleCat.{v} R)
    (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = IsLocalRing.depth M :=
  Ideal.depth_quotSMulTop_succ_eq_moduleDepth (maximalIdeal R) M x reg mem

lemma moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth (N M : ModuleCat.{v} R)
    (rs : List R) (reg : IsWeaklyRegular M rs) (h : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    moduleDepth N M := by
  generalize len : rs.length = n
  induction n generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using moduleDepth_eq_of_iso_snd N (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  · rename_i n hn
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [moduleDepth_eq_of_iso_snd N
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso,
        ← moduleDepth_quotSMulTop_succ_eq_moduleDepth N M x this (h x List.mem_cons_self),
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
        (fun r hr ↦ h r (List.mem_cons_of_mem x hr)) len, add_assoc]

lemma ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth (I : Ideal R)
    (M : ModuleCat.{v} R) (rs : List R) (reg : IsWeaklyRegular M rs)
    (h : ∀ r ∈ rs, r ∈ I) :
    I.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    I.depth M := by
  apply moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth _ M rs reg
  convert h
  rw [LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ I)), Ideal.annihilator_quotient]

lemma depth_quotient_regular_sequence_add_length_eq_depth [IsLocalRing R]
    (M : ModuleCat.{v} R) (rs : List R)
    (reg : IsRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    IsLocalRing.depth M := by
  apply ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth _ M rs reg.toIsWeaklyRegular
  intro r hr
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  by_contra isu
  absurd reg.2
  simp [eq_top_of_isUnit_mem (ofList rs) (Ideal.subset_span hr) isu]

section ring

local instance (R : Type*) [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
    IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective

lemma IsLocalRing.depth_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] (e : R ≃+* R') :
    IsLocalRing.depth (ModuleCat.of R R) = IsLocalRing.depth (ModuleCat.of R' R') := by
  let _ : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let _ : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let e' : R ≃ₛₗ[e.toRingHom] R' := {
    __ := e
    map_smul' a b := by simp }
  simp only [depth_eq_sSup_length_regular]
  congr!
  rename_i n
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · use List.map e.toRingHom rs, (LinearEquiv.isRegular_congr' e' rs).mp reg
    simpa [len]
  · use List.map e.symm.toRingHom rs, (LinearEquiv.isRegular_congr' e'.symm rs).mp reg
    simpa [len]

lemma IsLocalRing.depth_eq_of_algebraMap_surjective [IsLocalRing R] [IsNoetherianRing R]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra R S] [Small.{v} S] [IsNoetherianRing S]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module S M]
    [IsScalarTower R S M] [Nontrivial M] (surj : Function.Surjective (algebraMap R S)) :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S M) := by
  have : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  have loc_hom : IsLocalHom (algebraMap R S) :=
    Function.Surjective.isLocalHom (algebraMap R S) surj
  simp only [depth_eq_sSup_length_regular]
  congr!
  rename_i n
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · have mem' : ∀ r ∈ rs.map (algebraMap R S), r ∈ maximalIdeal S := by
      intro r hr
      simp only [List.mem_map] at hr
      rcases hr with ⟨r', hr', eq⟩
      simpa [← eq] using mem r' hr'
    have reg' : RingTheory.Sequence.IsRegular M (rs.map (algebraMap R S)) := by
      refine ⟨(RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff S M rs).mpr reg.1, ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs.map (algebraMap R S), reg', mem'
    simpa
  · rcases List.map_surjective_iff.mpr surj rs with ⟨rs', hrs'⟩
    have mem' : ∀ r ∈ rs', r ∈ maximalIdeal R := by
      intro r hr
      have : algebraMap R S r ∈ maximalIdeal S := by
        apply mem
        simp only [← hrs', List.mem_map]
        use r
      simpa using this
    have reg' : RingTheory.Sequence.IsRegular M rs' := by
      refine ⟨(RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff S M rs').mp
        (by simpa [hrs'] using reg.1), ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs', reg', mem'
    simpa [← hrs'] using len

omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_regular_succ_eq_depth [IsLocalRing R] [IsNoetherianRing R] (x : R)
    (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
      have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ x • (⊤ : Ideal R)) (R ⧸ x • (⊤ : Ideal R))) + 1 =
    IsLocalRing.depth (ModuleCat.of R R) := by
  have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
  have loc_hom : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
  rw [← IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth (ModuleCat.of R R) x reg mem, eq_comm]
  congr 1
  apply depth_eq_of_algebraMap_surjective _
  simpa only [Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective

omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_span_regular_succ_eq_depth [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      have : Nontrivial (R ⧸ Ideal.span {x}) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) + 1 =
    IsLocalRing.depth (ModuleCat.of R R) := by
  let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
    have : Nontrivial (R ⧸ Ideal.span {x}) :=
      Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  let : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
      Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
  have := Submodule.ideal_span_singleton_smul x (⊤ :Ideal R)
  simp only [smul_eq_mul, mul_top] at this
  rw [IsLocalRing.depth_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R this).toRingEquiv,
    IsLocalRing.depth_quotient_regular_succ_eq_depth x reg mem]

omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_regular_sequence_add_length_eq_depth [IsLocalRing R]
    [IsNoetherianRing R] (rs : List R) (reg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ Ideal.ofList rs) :=
      have : Nontrivial (R ⧸ Ideal.ofList rs) := Submodule.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top IsPrime.ne_top' (span_le.mpr mem))
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList rs)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ Ideal.ofList rs)
      (R ⧸ Ideal.ofList rs)) + rs.length =
    IsLocalRing.depth (ModuleCat.of R R) := by
  generalize len : rs.length = n
  induction n generalizing R rs
  · let e : R ⧸ ofList rs ≃+* R :=
      (RingEquiv.ofBijective _ ((Ideal.Quotient.mk_bijective_iff_eq_bot (Ideal.ofList rs)).mpr
        (by simp [List.length_eq_zero_iff.mp len]))).symm
    have : IsLocalRing (R ⧸ ofList rs) := RingEquiv.isLocalRing e.symm
    have : IsNoetherianRing (R ⧸ ofList rs) := isNoetherianRing_of_ringEquiv R e.symm
    simpa using IsLocalRing.depth_eq_of_ringEquiv e
  · rename_i n hn _ _ _
    match rs with
    | [] => simp at len
    | x :: rs' =>
      let _ : IsLocalRing (R ⧸ Ideal.ofList (x :: rs')) :=
        have : Nontrivial (R ⧸ Ideal.ofList (x :: rs')) :=
          Submodule.Quotient.nontrivial_iff.mpr
          (ne_top_of_le_ne_top IsPrime.ne_top' (span_le.mpr mem))
        have : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList (x :: rs'))) :=
          IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
        IsLocalRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc,
       ← depth_quotient_regular_succ_eq_depth x ((isWeaklyRegular_cons_iff _ x rs').mp reg).1 mem.1]
      have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul] using mem.1)
      have loc_hom : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
        IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R)))
          Ideal.Quotient.mk_surjective
      have mem' : ∀ r ∈ List.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))) rs',
        r ∈ maximalIdeal (R ⧸ x • (⊤ : Ideal R)) := by
        intro r hr
        rcases List.mem_map.mp hr with ⟨r', hr', eq⟩
        simpa [← eq] using mem.2 r' hr'
      simp only [ne_eq, ENat.one_ne_top, not_false_eq_true, add_left_inj_of_ne_top,
        ← hn (rs'.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))))
        ((RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ x • (⊤ : Ideal R))
          (R ⧸ x • (⊤ : Ideal R)) rs').mpr ((isWeaklyRegular_cons_iff _ x rs').mp reg).2) mem'
          (by simpa using len)]
      let f := (Ideal.Quotient.mk (ofList (rs'.map (Ideal.Quotient.mk (x • (⊤ : Ideal R)))))).comp
        (Ideal.Quotient.mk (x • (⊤ : Ideal R)))
      have surj : Function.Surjective f := by
        simp only [RingHom.coe_comp, f]
        exact Function.Surjective.comp Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
      have eq : RingHom.ker f = ofList (x :: rs') := by
        have := Submodule.ideal_span_singleton_smul x (⊤ : Ideal R)
        simp only [smul_eq_mul, mul_top] at this
        simp only [← RingHom.comap_ker, mk_ker, ofList_cons, this, f, sup_comm]
        convert Ideal.comap_map_of_surjective' (Ideal.Quotient.mk (x • (⊤ : Ideal R)))
          Ideal.Quotient.mk_surjective (Ideal.span {r | r ∈ rs'})
        · simp
        · exact mk_ker.symm
      let e : R ⧸ ofList (x :: rs') ≃+* ((R ⧸ x • (⊤ : Ideal R)) ⧸
        ofList (rs'.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))))) :=
        (Ideal.quotientEquivAlgOfEq R eq).symm.toRingEquiv.trans
        (RingHom.quotientKerEquivOfSurjective surj)
      let _ := RingEquiv.isLocalRing e
      let _ := isNoetherianRing_of_ringEquiv _ e
      exact congrArg (fun a : ℕ∞ => a + n) (IsLocalRing.depth_eq_of_ringEquiv e)

end ring

end depth

section PolyHeight

open _root_.Polynomial

variable (R : Type*) [CommRing R]

open _root_.IsLocalRing

lemma eq_radical_of_maximalIdeal_mem_minimalPrimes [IsLocalRing R] (I : Ideal R)
    (mem : maximalIdeal R ∈ I.minimalPrimes) : maximalIdeal R = I.radical := by
  have eq : I.minimalPrimes = {maximalIdeal R} := by
    ext p
    refine ⟨fun h ↦ Set.mem_singleton_iff.mpr ?_, fun h ↦ by simpa [Set.mem_singleton_iff.mp h]⟩
    let _ : p.IsPrime := h.1.1
    exact Minimal.eq_of_le mem.out h.1 (le_maximalIdeal_of_isPrime p)
  simpa [eq] using Ideal.sInf_minimalPrimes (I := I)

namespace Polynomial

variable [IsNoetherianRing R]

lemma height_map_maximalIdeal [IsLocalRing R] :
    ((maximalIdeal R).map C).height = (maximalIdeal R).height := by
  let : (Ideal.map C (maximalIdeal R)).IsPrime := inferInstance  -- PORT: now an instance
  apply le_antisymm
  · rcases (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing with ⟨s, min, card⟩
    have eq := eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min
    have eqrad : Ideal.map C (maximalIdeal R) = ((Ideal.span s).map C).radical := by
      apply le_antisymm _ ((Ideal.IsPrime.radical_le_iff ‹_›).mpr (Ideal.map_mono min.1.2))
      simpa [eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min] using Ideal.map_radical_le _
    let _ : ((Ideal.span (s : Set R)).map C).radical.IsPrime := by simpa [← eqrad]
    have : Ideal.map C (maximalIdeal R) ∈ ((Ideal.span s).map C).minimalPrimes := by
      rw [eqrad]
      refine ⟨?_, fun p ⟨prime, Ile⟩ _ ↦ (Ideal.IsPrime.radical_le_iff prime).mpr Ile⟩
      simpa [Ideal.radical_le_radical_iff.mp (le_refl _)]
    apply le_trans (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ this)
    have fg : (Ideal.map C (Ideal.span (s : Set R))).FG :=
      (isNoetherianRing_iff_ideal_fg R[X]).mp inferInstance _
    simp only [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg, map_natCast, ← card, Nat.cast_le]
    rw [Ideal.map_span, ← Set.ncard_coe_finset s]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _))
      (Set.ncard_image_le s.finite_toSet)
  · -- PORT: `Ideal.primeHeight` is private now; go through `PrimeSpectrum.height_eq_orderHeight`
    let map' : PrimeSpectrum R → PrimeSpectrum R[X] := fun p ↦
      ⟨p.1.map C, (have := p.2; inferInstance)⟩
    have hmono : StrictMono map' := by
      intro p q lt
      simp only [← PrimeSpectrum.asIdeal_lt_asIdeal, map']
      apply (Set.ssubset_iff_of_subset (Ideal.map_mono (le_of_lt lt))).mpr
      rcases (Set.ssubset_iff_of_subset (le_of_lt lt)).mp lt with ⟨x, hx⟩
      use C x
      simp only [SetLike.mem_coe, Ideal.mem_map_of_mem _ hx.1, Ideal.mem_map_C_iff, not_forall,
        true_and]
      use 0
      simpa using hx.2
    have h := Order.height_le_height_apply_of_strictMono map' hmono
      (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)
    rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
    exact h

lemma height_of_comap_eq_maximalIdeal [IsLocalRing R] (m : Ideal R[X]) [h : m.IsPrime]
    (eqm : m.comap C = maximalIdeal R) : m.height ≤ (maximalIdeal R).height + 1 := by
  let : (Ideal.map C (maximalIdeal R)).IsPrime := inferInstance  -- PORT: now an instance
  have maple : (maximalIdeal R).map C ≤ m := by simp [Ideal.map_le_iff_le_comap, eqm]
  let _ : IsPrincipalIdealRing (IsLocalRing.ResidueField R)[X] := inferInstance
  rcases IsPrincipalIdealRing.principal (Ideal.map (mapRingHom (residue R)) m) with ⟨x, hx⟩
  rcases map_surjective (residue R) residue_surjective x with ⟨y, hy⟩
  have eqsup : m = (maximalIdeal R).map C ⊔ Ideal.span {y} := by
    calc
      m = m ⊔ RingHom.ker (mapRingHom (residue R)) := by
        simpa only [ker_mapRingHom, left_eq_sup, ker_residue] using maple
      _ = ((Ideal.span {y}).map (mapRingHom (residue R))).comap (mapRingHom (residue R)) := by
        simp [← Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), hx, Ideal.map_span, hy]
      _ = _ := by
        simp only [Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), sup_comm, ker_mapRingHom, ker_residue]
  rcases (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing with ⟨s, min, card⟩
  have eq := eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min
  have eqrad : Ideal.map C (maximalIdeal R) = ((Ideal.span s).map C).radical := by
    apply le_antisymm _ ((Ideal.IsPrime.radical_le_iff ‹_›).mpr (Ideal.map_mono min.1.2))
    simpa [eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min] using Ideal.map_radical_le _
  have : m ∈ (((Ideal.span s).map C) ⊔ Ideal.span {y}).minimalPrimes := by
    refine ⟨?_, fun p ⟨prime, le⟩ _ ↦ by
      simpa [eqsup, eqrad, Ideal.IsPrime.radical_le_iff prime] using le⟩
    simp only [h, sup_le_iff, true_and]
    simpa only [eqsup, le_sup_right, and_true] using le_sup_of_le_left (Ideal.map_mono min.1.2)
  rw [Ideal.map_span, ← Ideal.span_union] at this
  apply le_trans (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ this)
  have fg : (Ideal.span (⇑C '' ↑s ∪ {y})).FG :=
    (isNoetherianRing_iff_ideal_fg R[X]).mp inferInstance _
  simp only [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg, map_natCast, ← card]
  rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast, ← Set.ncard_coe_finset s]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _))
  apply le_trans (Set.ncard_union_le _ _)
  simpa only [Set.ncard_singleton, add_le_add_iff_right] using (Set.ncard_image_le s.finite_toSet)

end Polynomial

end PolyHeight

/-! ### Part C: `Ideal.primeHeight` (now private in Mathlib) -/

section PrimeHeight

variable {R : Type*} [CommRing R]

/-- The fork's `Ideal.primeHeight`: the order height of `I` in the prime spectrum. -/
noncomputable def Ideal.primeHeight (I : Ideal R) [hI : I.IsPrime] : ℕ∞ :=
  Order.height (⟨I, hI⟩ : PrimeSpectrum R)

lemma Ideal.height_eq_primeHeight (I : Ideal R) [I.IsPrime] : I.height = Ideal.primeHeight I :=
  PrimeSpectrum.height_eq_orderHeight ⟨I, inferInstance⟩

lemma Ideal.primeHeight_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) :
    Ideal.primeHeight I + 1 ≤ Ideal.primeHeight J := by
  rw [← Ideal.height_eq_primeHeight I, ← Ideal.height_eq_primeHeight J]
  exact Ideal.height_add_one_le_of_lt_of_isPrime h

end PrimeHeight

end LeanPool
