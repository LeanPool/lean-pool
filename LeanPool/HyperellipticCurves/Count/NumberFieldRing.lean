/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.WittVector.Complete

import LeanPool.HyperellipticCurves.ForMathlib.AdicComplete
import LeanPool.HyperellipticCurves.ForMathlib.Ideal
import LeanPool.HyperellipticCurves.ForMathlib.Idempotents
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.PrimitiveElement

/-!
# The completed maximal unramified extension, as a factor of `𝕎(𝔽_barp) ⊗ A`

Let `A` be a commutative ring — in the application, the ring of integers `O_K` of a number
field `K`, or `ℤ` itself — and `𝔭` a maximal ideal of `A` of residue characteristic `p`.
The abstract Chabauty–Coleman theorems (`LeanPool.HyperellipticCurves.Count.Main`) run over a
complete
discrete valuation ring of characteristic `0` with algebraically closed residue field; for
`K` and `𝔭` the right such ring is the ring of integers of the completed maximal
unramified extension of the completion `K_𝔭`. This file constructs it without any theory
of complete discretely valued fields, as a direct factor of the `p`-adically complete ring
`R := 𝕎(𝔽_barp) ⊗[ℤ] A` (blueprint chapter "The theorem over number fields").

This file provides the ring `R`, the residue homomorphism `ρ : R → 𝔽_barp` attached to an
embedding `σ : A ⧸ 𝔭 → 𝔽_barp`, the `p`-adic completeness of `R` (for `A` finite free over
`ℤ`), and the idempotent `ε ∈ R` cutting out the local factor (blueprint
`lem:idempotent`): `ε` lies in `J·R` for the complementary factor `J` of `p·A = 𝔭^e·J`
and reduces modulo `𝔭R` to the idempotent attached to `σ` by the separable-corner lemma
(`exists_isIdempotentElem_ker_eq_span`).
The quotient `O := R ⧸ (1 - ε)` is studied in
`LeanPool.HyperellipticCurves.Count.NumberFieldFactor`.
-/

@[expose] public section

open Polynomial IsLocalRing

open scoped TensorProduct

namespace ChabautyColeman

namespace NumberFieldBase

variable {A : Type*} [CommRing A]
variable (p : ℕ) [Fact p.Prime] (𝔭 : Ideal A)

-- the residue ring at a maximal ideal is used as a field throughout
attribute [local instance] Ideal.Quotient.field

local notation "k" => AlgebraicClosure (ZMod p)
local notation "W" => WittVector p (AlgebraicClosure (ZMod p))
local notation "R" => TensorProduct ℤ (WittVector p (AlgebraicClosure (ZMod p))) A

/-! ### The base-change ring and its residue homomorphism -/

variable (σ : (A ⧸ 𝔭) →+* AlgebraicClosure (ZMod p))

/-- The residue homomorphism of the base-change ring: on `𝕎(𝔽_barp)` the residue
(constant coefficient), on `A` the reduction modulo `𝔭` followed by the embedding `σ`
(blueprint `def:witt-tensor`). -/
noncomputable def rho : R →+* k :=
  (Algebra.TensorProduct.lift (WittVector.constantCoeff : W →+* k).toIntAlgHom
    ((σ.comp (Ideal.Quotient.mk 𝔭)).toIntAlgHom) fun _ _ ↦ Commute.all _ _).toRingHom

theorem rho_tmul (w : W) (a : A) :
    rho p 𝔭 σ (w ⊗ₜ a) = WittVector.constantCoeff w * σ (Ideal.Quotient.mk 𝔭 a) :=
  Algebra.TensorProduct.lift_tmul ..

theorem rho_surjective : Function.Surjective (rho p 𝔭 σ) := fun x ↦
  ⟨(WittVector.mk p fun _ ↦ x) ⊗ₜ 1, by simp [rho_tmul]⟩

/-! ### Extending ideals of `A` to `R` -/

/-- The extension of an ideal of `A` to the base-change ring `R`. -/
noncomputable def extIdeal (I : Ideal A) : Ideal R :=
  I.map (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R).toRingHom

theorem tmul_one_mem_extIdeal {I : Ideal A} {a : A} (ha : a ∈ I) : (1 : W) ⊗ₜ a ∈ extIdeal p I :=
  Ideal.mem_map_of_mem _ ha

theorem natCast_mem_extIdeal {I : Ideal A} {n : ℕ} (hn : (n : A) ∈ I) : (n : R) ∈ extIdeal p I :=
  map_natCast (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R).toRingHom n ▸
    tmul_one_mem_extIdeal p hn

theorem extIdeal_mul (I J : Ideal A) : extIdeal p (I * J) = extIdeal p I * extIdeal p J :=
  Ideal.map_mul ..

theorem extIdeal_pow (I : Ideal A) (n : ℕ) : extIdeal p (I ^ n) = extIdeal p I ^ n :=
  Ideal.map_pow ..

theorem extIdeal_sup (I J : Ideal A) : extIdeal p (I ⊔ J) = extIdeal p I ⊔ extIdeal p J :=
  Ideal.map_sup ..

theorem extIdeal_top : extIdeal p (⊤ : Ideal A) = ⊤ :=
  Ideal.map_top ..

theorem extIdeal_mono {I J : Ideal A} (h : I ≤ J) : extIdeal p I ≤ extIdeal p J :=
  Ideal.map_mono h

theorem extIdeal_span_natCast (n : ℕ) :
    extIdeal p (Ideal.span {(n : A)}) = Ideal.span {(n : R)} := by
  rw [extIdeal, Ideal.map_span, Set.image_singleton, map_natCast]

/-- The residue homomorphism kills the extension of `𝔭`, in the form `Ideal.Quotient.lift`
consumes. -/
theorem rho_eq_zero_of_mem_extIdeal : ∀ a ∈ extIdeal p 𝔭, rho p 𝔭 σ a = 0 := by
  have h : extIdeal p 𝔭 ≤ RingHom.ker (rho p 𝔭 σ) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      simp [RingHom.mem_ker, rho_tmul, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact h

/-- The residue homomorphism induced on `R ⧸ 𝔭R`. -/
noncomputable def rhoQuot : R ⧸ extIdeal p 𝔭 →+* k :=
  Ideal.Quotient.lift (extIdeal p 𝔭) (rho p 𝔭 σ) (rho_eq_zero_of_mem_extIdeal p 𝔭 σ)

@[simp]
theorem rhoQuot_mk (r : R) :
    rhoQuot p 𝔭 σ (Ideal.Quotient.mk (extIdeal p 𝔭) r) = rho p 𝔭 σ r := rfl

/-! ### The corner of `R ⧸ 𝔭R` at the embedding `σ` -/

-- The map `𝔽_barp → R ⧸ 𝔭R` induced by `W → R` through the residue identification
-- `W ⧸ (p) ≃ 𝔽_barp`; internal to the construction of the idempotent.
private noncomputable def kToQuot (hp𝔭 : (p : A) ∈ 𝔭) : k →+* R ⧸ extIdeal p 𝔭 :=
  (Ideal.Quotient.lift (Ideal.span {(p : W)})
      ((Ideal.Quotient.mk (extIdeal p 𝔭)).comp (algebraMap W R)) (fun _ ha ↦ by
        obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp ha
        rw [RingHom.comp_apply, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (natCast_mem_extIdeal p hp𝔭))).comp
    (WittVector.quotientPEquiv (p := p)).symm.toRingHom

private theorem kToQuot_constantCoeff (hp𝔭 : (p : A) ∈ 𝔭) (w : W) :
    kToQuot p 𝔭 hp𝔭 (WittVector.constantCoeff w)
      = Ideal.Quotient.mk (extIdeal p 𝔭) (algebraMap W R w) := by
  have h : (WittVector.quotientPEquiv (p := p)).symm (WittVector.constantCoeff w)
      = Ideal.Quotient.mk (Ideal.span {(p : W)}) w := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [kToQuot, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h,
    Ideal.Quotient.lift_mk, RingHom.comp_apply]

-- The reduction of `A` into `R ⧸ 𝔭R`, through the residue field of `𝔭`.
private noncomputable def resQuot : (A ⧸ 𝔭) →+* R ⧸ extIdeal p 𝔭 :=
  Ideal.Quotient.lift 𝔭
    ((Ideal.Quotient.mk (extIdeal p 𝔭)).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R).toRingHom)
    fun _a ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (tmul_one_mem_extIdeal p ha)

private theorem resQuot_mk (a : A) :
    resQuot p 𝔭 (Ideal.Quotient.mk 𝔭 a) = Ideal.Quotient.mk (extIdeal p 𝔭) ((1 : W) ⊗ₜ a) :=
  Ideal.Quotient.lift_mk ..

-- The residue map retracts the Witt corner: `ρ` composed with `kToQuot` is the identity.
private theorem rhoQuot_kToQuot (hp𝔭 : (p : A) ∈ 𝔭) (x : k) :
    rhoQuot p 𝔭 σ (kToQuot p 𝔭 hp𝔭 x) = x := by
  have hx : x = WittVector.constantCoeff (WittVector.mk p fun _ ↦ x) := rfl
  rw [hx, kToQuot_constantCoeff, rhoQuot_mk, Algebra.TensorProduct.algebraMap_apply,
    rho_tmul, map_one, map_one, mul_one, Algebra.algebraMap_self, RingHom.id_apply]

-- Evaluating a polynomial over `𝔽p` at the image of `ξ`, with coefficients through `kToQuot`,
-- is the reduction of its value at the class of `ξ` in the residue field.
private theorem eval₂_kToQuot_map [Algebra (ZMod p) (A ⧸ 𝔭)] (hp𝔭 : (p : A) ∈ 𝔭) (ξ : A)
    (gZ : Polynomial (ZMod p)) :
    eval₂ (kToQuot p 𝔭 hp𝔭) (Ideal.Quotient.mk (extIdeal p 𝔭) ((1 : W) ⊗ₜ ξ))
        (gZ.map (algebraMap (ZMod p) k))
      = resQuot p 𝔭 (aeval (Ideal.Quotient.mk 𝔭 ξ) gZ) := by
  have hZ : (kToQuot p 𝔭 hp𝔭).comp (algebraMap (ZMod p) k)
      = (resQuot p 𝔭).comp (algebraMap (ZMod p) (A ⧸ 𝔭)) := RingHom.ext_zmod _ _
  rw [eval₂_map, hZ, ← resQuot_mk, ← hom_eval₂, ← aeval_def]

-- Every element of `R ⧸ 𝔭R` is a polynomial in the image of a generator of the residue field
-- of `𝔭`, with coefficients in `𝔽_barp` through `kToQuot`.
private theorem exists_eval₂_eq [Algebra (ZMod p) (A ⧸ 𝔭)] (hp𝔭 : (p : A) ∈ 𝔭) {ξ : A}
    (hgen : Algebra.adjoin (ZMod p) {Ideal.Quotient.mk 𝔭 ξ} = ⊤) (b : R ⧸ extIdeal p 𝔭) :
    ∃ g : Polynomial k,
      eval₂ (kToQuot p 𝔭 hp𝔭) (Ideal.Quotient.mk (extIdeal p 𝔭) ((1 : W) ⊗ₜ ξ)) g = b := by
  set φ := kToQuot p 𝔭 hp𝔭 with hφ
  set t := Ideal.Quotient.mk (extIdeal p 𝔭) ((1 : W) ⊗ₜ ξ) with ht
  have hres (y : A ⧸ 𝔭) : ∃ gZ : Polynomial (ZMod p),
      eval₂ φ t (gZ.map (algebraMap (ZMod p) k)) = resQuot p 𝔭 y := by
    obtain ⟨gZ, hgZ⟩ : ∃ gZ : Polynomial (ZMod p), aeval (Ideal.Quotient.mk 𝔭 ξ) gZ = y := by
      have hmem : y ∈ Algebra.adjoin (ZMod p) {Ideal.Quotient.mk 𝔭 ξ} := by rw [hgen]; trivial
      rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hmem
    exact ⟨gZ, by rw [hφ, ht, eval₂_kToQuot_map, hgZ]⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := extIdeal p 𝔭) b
  induction r using TensorProduct.inductionOn with
  | add y z hy hz =>
    obtain ⟨gy, hgy⟩ := hy
    obtain ⟨gz, hgz⟩ := hz
    exact ⟨gy + gz, by rw [eval₂_add, hgy, hgz, map_add]⟩
  | tmul w a =>
    have hsplit : Ideal.Quotient.mk (extIdeal p 𝔭) (w ⊗ₜ a)
        = φ (WittVector.constantCoeff w) * resQuot p 𝔭 (Ideal.Quotient.mk 𝔭 a) := by
      rw [hφ, kToQuot_constantCoeff, resQuot_mk, ← map_mul,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    obtain ⟨gZ, hgZ⟩ := hres (Ideal.Quotient.mk 𝔭 a)
    refine ⟨WittVector.constantCoeff w • gZ.map (algebraMap (ZMod p) k), ?_⟩
    rw [eval₂_smul, hgZ, hsplit]

/-- The residue characteristic: a quotient by a proper ideal containing the prime `p` has
characteristic `p`. -/
theorem charP_quotient {I : Ideal A} (hI : I ≠ ⊤) (hpI : (p : A) ∈ I) : CharP (A ⧸ I) p := by
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
  rwa [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]

/-- The idempotent of `R ⧸ 𝔭R` cutting out the corner at `σ`: the kernel of the map induced
by the residue homomorphism `ρ` is generated by an idempotent, by the separable-corner
principle (`exists_isIdempotentElem_ker_eq_span`) applied to a primitive element of the
residue field of `𝔭` (blueprint `lem:idempotent`, the seed). -/
theorem exists_isIdempotentElem_ker_lift_rho [𝔭.IsMaximal] [Finite (A ⧸ 𝔭)] (hp𝔭 : (p : A) ∈ 𝔭) :
    ∃ γ : R ⧸ extIdeal p 𝔭, IsIdempotentElem γ ∧
      RingHom.ker (rhoQuot p 𝔭 σ) = Ideal.span {1 - γ} := by
  classical
  -- the residue field of `𝔭` and its structure over `𝔽p`
  have hchar : CharP (A ⧸ 𝔭) p := charP_quotient p (Ideal.IsMaximal.ne_top ‹_›) hp𝔭
  let : Algebra (ZMod p) (A ⧸ 𝔭) := ZMod.algebra _ p
  -- a primitive element of the residue field and its data
  obtain ⟨ξbar, hξgen⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) (A ⧸ 𝔭)
  have halg : IsAlgebraic (ZMod p) ξbar := (Algebra.IsIntegral.isIntegral ξbar).isAlgebraic
  have hgen : Algebra.adjoin (ZMod p) {ξbar} = ⊤ := by
    have h := congrArg IntermediateField.toSubalgebra hξgen
    rwa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg,
      IntermediateField.top_toSubalgebra] at h
  obtain ⟨ξ, hξ⟩ := Ideal.Quotient.mk_surjective (I := 𝔭) ξbar
  set m := minpoly (ZMod p) ξbar
  set t := Ideal.Quotient.mk (extIdeal p 𝔭) ((1 : W) ⊗ₜ ξ) with ht
  -- the minimal polynomial, mapped to `k`, kills `t` and has `ρ_bar t` as a simple root
  have haev : eval₂ (kToQuot p 𝔭 hp𝔭) t (m.map (algebraMap (ZMod p) k)) = 0 := by
    rw [ht, eval₂_kToQuot_map, hξ, minpoly.aeval, map_zero]
  have hρt : rhoQuot p 𝔭 σ t = σ ξbar := by
    rw [ht, rhoQuot_mk, rho_tmul, map_one, one_mul, hξ]
  have hσZ : (σ.comp (algebraMap (ZMod p) (A ⧸ 𝔭)) : ZMod p →+* k) = algebraMap (ZMod p) k :=
    RingHom.ext_zmod _ _
  have hsep : m.Separable := Algebra.IsSeparable.isSeparable (ZMod p) ξbar
  have hder : ((m.map (algebraMap (ZMod p) k)).derivative).eval (rhoQuot p 𝔭 σ t) ≠ 0 := by
    rw [hρt, derivative_map, eval_map]
    refine hsep.eval₂_derivative_ne_zero _ ?_
    rw [show m.eval₂ (algebraMap (ZMod p) k) (σ ξbar) = σ (aeval ξbar m) by
      rw [aeval_def, hom_eval₂, hσZ], minpoly.aeval, map_zero]
  exact exists_isIdempotentElem_ker_eq_span_of_ringHom (t := t)
    (m := m.map (algebraMap (ZMod p) k)) _ (rhoQuot p 𝔭 σ) (rhoQuot_kToQuot p 𝔭 σ hp𝔭)
    (exists_eval₂_eq p 𝔭 hp𝔭 (by rw [hξ]; exact hgen)) haev hder

/-! ### `p`-adic completeness of `R` -/

variable [Module.Free ℤ A] [Module.Finite ℤ A]

instance isAdicCompleteSpanP : IsAdicComplete (Ideal.span {(p : R)}) R := by
  have hb : IsAdicComplete (Ideal.span {(p : W)}) R :=
    ((Module.Free.chooseBasis ℤ A).baseChange W).isAdicComplete
  have h := (IsAdicComplete.map_algebraMap_iff (Ideal.span {(p : W)}) (M := R) (S := R)).mpr hb
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

/-! ### The idempotent cutting out the local factor -/

/-- **The idempotent below the corner** (blueprint `lem:idempotent`): given the factorization
`p·A = 𝔭^e·J` with `𝔭 + J = A`, there is an idempotent `ε ∈ J·R` with
`ker ρ = 𝔭R + (1 - ε)`. The quotient `R ⧸ (1 - ε)` is the complete local ring the
main theorems run over. -/
theorem exists_isIdempotentElem_ker_rho [𝔭.IsMaximal] [Finite (A ⧸ 𝔭)]
    (hp𝔭 : (p : A) ∈ 𝔭) {e : ℕ} (he : 0 < e) {J : Ideal A}
    (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J) (hcop : 𝔭 ⊔ J = ⊤) :
    ∃ ε : R, IsIdempotentElem ε ∧ ε ∈ extIdeal p J ∧
      RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε} := by
  obtain ⟨γ, hγ, hker⟩ := exists_isIdempotentElem_ker_lift_rho p 𝔭 σ hp𝔭
  -- a lift `c` of `γ` inside `J·R`
  have hcopR : extIdeal p 𝔭 ⊔ extIdeal p J = ⊤ := by
    rw [← extIdeal_sup, hcop, extIdeal_top]
  obtain ⟨c, hcJ, hmkc⟩ := Ideal.exists_mem_mk_eq_of_sup_eq_top hcopR γ
  -- its defect lies in the extension of `𝔭·J`, whose adic topology is the `p`-adic one
  have hdefect : c ^ 2 - c ∈ extIdeal p (𝔭 * J) := by
    rw [extIdeal_mul, Ideal.mul_eq_inf_of_coprime hcopR]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hmkc, sq, hγ.eq, sub_self]
    · exact Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ hcJ 2 two_pos) hcJ
  have hle1 : Ideal.span {(p : R)} ≤ extIdeal p (𝔭 * J) :=
    (Ideal.span_singleton_le_iff_mem _).mpr <| natCast_mem_extIdeal p <|
      Ideal.mul_mono_left (Ideal.pow_le_self he.ne') (hpJ ▸ Ideal.mem_span_singleton_self _)
  have hle2 : extIdeal p (𝔭 * J) ^ e ≤ Ideal.span {(p : R)} := by
    rw [← extIdeal_pow, ← extIdeal_span_natCast p]
    refine extIdeal_mono p ?_
    calc (𝔭 * J) ^ e = 𝔭 ^ e * J ^ e := mul_pow ..
      _ ≤ 𝔭 ^ e * J := Ideal.mul_mono_right (Ideal.pow_le_self he.ne')
      _ = Ideal.span {(p : A)} := hpJ.symm
  have hcompl : IsAdicComplete (extIdeal p (𝔭 * J)) R :=
    isAdicComplete_of_le_of_pow_le he hle1 hle2
  obtain ⟨ε, hε, hεc⟩ := IsAdicComplete.exists_isIdempotentElem_of_sq_sub_mem
    (extIdeal p (𝔭 * J)) hdefect
  rw [extIdeal_mul] at hεc
  have hεJ : ε ∈ extIdeal p J := by
    simpa using Ideal.add_mem _ (Ideal.mul_le_right hεc) hcJ
  refine ⟨ε, hε, hεJ, ?_⟩
  -- the kernel of `ρ`: pull `ker ρ_bar = (1 - γ)` back along the quotient map
  have hεc𝔭 : ε - c ∈ extIdeal p 𝔭 := Ideal.mul_le_left hεc
  have hkerpull : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - c} :=
    Ideal.ker_eq_sup_of_ker_quotient_lift _ _ (hker.trans
      (by rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, hmkc]))
  rw [hkerpull]
  -- replace `c` by `ε` using `ε - c ∈ 𝔭R`
  exact Ideal.sup_span_singleton_eq_of_sub_mem (by rwa [sub_sub_sub_cancel_left])

end NumberFieldBase

end ChabautyColeman

end
