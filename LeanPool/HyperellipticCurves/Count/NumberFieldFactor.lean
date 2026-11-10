/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.NumberFieldRing
public import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

import LeanPool.HyperellipticCurves.ForMathlib.AdicComplete
import LeanPool.HyperellipticCurves.ForMathlib.AdicTopology
import LeanPool.HyperellipticCurves.ForMathlib.IsAlgClosed
import LeanPool.HyperellipticCurves.ForMathlib.WittVector
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# The local factor is a complete discrete valuation ring

Continuing `LeanPool.HyperellipticCurves.Count.NumberFieldRing`: given the idempotent `ε ∈ J·R` with
`ker ρ = 𝔭R + (1 - ε)` produced there, this file studies the quotient
`Factor p ε := R ⧸ (1 - ε)` (blueprint `def:local-factor`, `lem:factor-dvr`). The image of
`J` in the factor is the unit ideal, so the image of `𝔭` satisfies `(𝔭O)^e = pO` on the
nose; the factor is `p`-adically — equivalently `𝔭O`-adically — complete, local with maximal
ideal `𝔭O = ker ρ_O`, and a discrete valuation ring of characteristic `0` in which the image
`π` of a uniformizer of `A_𝔭` generates the maximal ideal and satisfies `π^e = p·(unit)`.
As in `LeanPool.HyperellipticCurves.Count.NumberFieldRing`, the base ring `A` is abstract — the ring
of
integers of a number field, or `ℤ` itself.

`Factor` is a definition (not notation for the quotient) so that it carries a single
canonical `CommRing` instance: the raw quotient of the tensor ring has several
definitionally equal but syntactically different instance paths, which block rewriting.
It also carries the canonical `p`-adic topology (as a `WithIdeal` instance), which
`isAdic_map` identifies with the `𝔭O`-adic one.
The certificate hypotheses are bundled as `FactorData`, declared before the lemmas that
consume it so that its namespace can carry their bundled forms (`h.isLocalRing`,
`h.map_eq_span`, ...) alongside the consequences of the certificate itself;
`LeanPool.HyperellipticCurves.Count.NumberField` instantiates the pack from
`exists_isIdempotentElem_ker_rho`
and assembles the main theorems.
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

-- `Ideal.Quotient.field` is not a global instance; it is enabled here for `A ⧸ 𝔭`.
attribute [local instance] Ideal.Quotient.field

namespace ChabautyColeman

namespace NumberFieldBase

variable {A : Type*} [CommRing A]
variable (p : ℕ) [Fact p.Prime] (𝔭 : Ideal A)

local notation "k" => AlgebraicClosure (ZMod p)
local notation "W" => WittVector p (AlgebraicClosure (ZMod p))
local notation "R" => TensorProduct ℤ (WittVector p (AlgebraicClosure (ZMod p))) A

variable (σ : (A ⧸ 𝔭) →+* AlgebraicClosure (ZMod p))
variable (ε : TensorProduct ℤ (WittVector p (AlgebraicClosure (ZMod p))) A)

/-! ### The factor as a type with one canonical ring structure -/

/-- The local factor `R ⧸ (1 - ε)` (blueprint `def:local-factor`), as a definition so that
it carries a single canonical `CommRing` instance. -/
def Factor : Type _ :=
  TensorProduct ℤ (WittVector p (AlgebraicClosure (ZMod p))) A ⧸ Ideal.span {1 - ε}

noncomputable instance : CommRing (Factor p ε) :=
  inferInstanceAs (CommRing (TensorProduct ℤ (WittVector p (AlgebraicClosure (ZMod p))) A
    ⧸ Ideal.span {1 - ε}))

/-- The local factor carries the `p`-adic topology (with the uniform structure, the
nonarchimedean and topological-ring instances that `WithIdeal` provides). -/
noncomputable instance : WithIdeal (Factor p ε) := ⟨Ideal.span {(p : Factor p ε)}⟩

/-- The topology installed on the factor is the `p`-adic one; `isAdic_map` identifies it with
the `𝔭O`-adic topology. -/
theorem isAdic_span_natCast : IsAdic (Ideal.span {(p : Factor p ε)}) := rfl

/-- The quotient projection onto the local factor. -/
noncomputable def mkFactor : R →+* Factor p ε :=
  Ideal.Quotient.mk (Ideal.span {1 - ε})

theorem mkFactor_surjective : Function.Surjective (mkFactor p ε) :=
  Ideal.Quotient.mk_surjective

theorem mkFactor_eq_zero_iff {r : R} : mkFactor p ε r = 0 ↔ r ∈ Ideal.span {1 - ε} :=
  Ideal.Quotient.eq_zero_iff_mem

theorem ker_mkFactor : RingHom.ker (mkFactor p ε) = Ideal.span {1 - ε} :=
  Ideal.mk_ker

theorem mkFactor_epsilon : mkFactor p ε ε = 1 :=
  (sub_eq_zero.mp (by
    simpa using (mkFactor_eq_zero_iff p ε).mpr (Ideal.mem_span_singleton_self (1 - ε)))).symm

/-- The canonical map from the base ring `A` into the local factor, sending `a` to the class
of `1 ⊗ a`. -/
noncomputable def resO : A →+* Factor p ε :=
  (mkFactor p ε).comp (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R).toRingHom

theorem resO_apply (a : A) : resO p ε a = mkFactor p ε ((1 : W) ⊗ₜ a) := rfl

/-! ### The certificate pack -/

/-- The full certificate for the local factor: the idempotent with its kernel identity, the
factorization of `p·A`, and a uniformizer certificate for `𝔭`
(blueprint `def:local-factor`). Its consequences, and the bundled forms of the lemmas that
consume it, are collected in the `FactorData` namespace. -/
structure FactorData (e : ℕ) (J C : Ideal A) (ϖ : A) : Prop where
  /-- The element cutting out the factor is idempotent. -/
  idem : IsIdempotentElem ε
  /-- The ramification index is positive. -/
  epos : 0 < e
  /-- The residue characteristic factors as `p·A = 𝔭^e·J`. -/
  hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J
  /-- `ε` lies in the extension to `R` of the complementary factor `J`. -/
  memJ : ε ∈ extIdeal p J
  /-- The kernel of `ρ` is cut out by `𝔭` and `1 - ε`. -/
  ker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε}
  /-- `ϖ` is a uniformizer at `𝔭`: the ideal it generates factors as `𝔭·C` ... -/
  span_uniformizer : Ideal.span {ϖ} = 𝔭 * C
  /-- ... with a complementary factor `C` not contained in `𝔭`. -/
  not_le : ¬ C ≤ 𝔭

variable {ε}

variable {p 𝔭 σ} in
/-- The kernel identity for `ε` provides the vanishing that `rhoO` needs. -/
theorem rho_one_sub_eq_zero
    (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε}) :
    rho p 𝔭 σ (1 - ε) = 0 :=
  RingHom.mem_ker.mp (hker ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

/-- The residue homomorphism descends to the local factor. -/
noncomputable def rhoO (h1ε : rho p 𝔭 σ (1 - ε) = 0) : Factor p ε →+* k :=
  Ideal.Quotient.lift _ (rho p 𝔭 σ) fun _ ha ↦ by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, h1ε, zero_mul]

theorem rhoO_mk (h1ε : rho p 𝔭 σ (1 - ε) = 0) (r : R) :
    rhoO p 𝔭 σ h1ε (mkFactor p ε r) = rho p 𝔭 σ r :=
  Ideal.Quotient.lift_mk ..

theorem rhoO_resO (h1ε : rho p 𝔭 σ (1 - ε) = 0) (a : A) :
    rhoO p 𝔭 σ h1ε (resO p ε a) = σ (Ideal.Quotient.mk 𝔭 a) := by
  rw [resO_apply, rhoO_mk, rho_tmul, map_one, one_mul]

theorem rhoO_surjective (h1ε : rho p 𝔭 σ (1 - ε) = 0) :
    Function.Surjective (rhoO p 𝔭 σ h1ε) := fun x ↦ by
  obtain ⟨r, hr⟩ := rho_surjective p 𝔭 σ x
  exact ⟨mkFactor p ε r, by rw [rhoO_mk, hr]⟩

/-- The factor is nontrivial: `rhoO` maps it onto the field `𝔽_barp`, where `1 ≠ 0`. -/
theorem nontrivial_factor (h1ε : rho p 𝔭 σ (1 - ε) = 0) : Nontrivial (Factor p ε) :=
  nontrivial_of_ne 1 0 fun h ↦ one_ne_zero (α := k) (by
    simpa using congrArg (rhoO p 𝔭 σ h1ε) h)

/-- The image of an ideal of `A` in the factor is the image of its extension to `R`. -/
theorem map_resO_eq (I : Ideal A) :
    I.map (resO p ε) = (extIdeal p I).map (mkFactor p ε) := by
  rw [extIdeal, Ideal.map_map]
  rfl

/-- The kernel of the residue homomorphism of the factor is the image of `𝔭`. -/
theorem ker_rhoO (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε}) :
    RingHom.ker (rhoO p 𝔭 σ (rho_one_sub_eq_zero hker)) = 𝔭.map (resO p ε) := by
  ext x
  obtain ⟨r, rfl⟩ := mkFactor_surjective p ε x
  rw [RingHom.mem_ker, rhoO_mk, ← RingHom.mem_ker, hker, map_resO_eq, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ (mkFactor_surjective p ε), ← RingHom.ker_eq_comap_bot,
    ker_mkFactor]

/-! ### The residue field of the factor -/

section Residue

variable [IsLocalRing (Factor p ε)] (h1ε : rho p 𝔭 σ (1 - ε) = 0)
  (hmax : maximalIdeal (Factor p ε) = RingHom.ker (rhoO p 𝔭 σ h1ε))

/-- The residue field of the factor is `𝔽_barp`, via the descended residue homomorphism. -/
noncomputable def residueFactorEquiv : ResidueField (Factor p ε) ≃+* k :=
  (Ideal.quotEquivOfEq hmax).trans
    (RingHom.quotientKerEquivOfSurjective (rhoO_surjective p 𝔭 σ h1ε))

include h1ε hmax in
/-- The residue field of the factor is algebraically closed, `residueFactorEquiv`
identifying it with `𝔽_barp`. `LeanPool.HyperellipticCurves.Count.NumberField` installs it as an
instance before
applying the abstract main theorem. -/
theorem isAlgClosed_residueField : IsAlgClosed (ResidueField (Factor p ε)) :=
  IsAlgClosed.of_ringEquiv' (residueFactorEquiv p 𝔭 σ h1ε hmax).symm

include h1ε hmax in
/-- The residue field is `𝔽_barp`, of characteristic `p`, so for odd `p` the element `2` does
not vanish in it — as the hyperelliptic model `y² = f(x)` requires. -/
theorem neZero_two_residueField (hp2 : p ≠ 2) : NeZero (2 : ResidueField (Factor p ε)) :=
  ⟨fun h0 ↦ by
    have h := congrArg (residueFactorEquiv p 𝔭 σ h1ε hmax) h0
    rw [map_ofNat, map_zero, ← Nat.cast_ofNat] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff k p 2).mp h))⟩

end Residue

/-! ### The image of `𝔭` is maximal -/

/-- The image of `𝔭` in the factor is maximal: it is the kernel of the residue
homomorphism of the factor. -/
theorem isMaximal_map_resO
    (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε}) :
    (𝔭.map (resO p ε)).IsMaximal := by
  rw [← ker_rhoO p 𝔭 σ hker]
  exact RingHom.ker_isMaximal_of_surjective _ (rhoO_surjective p 𝔭 σ _)

/-- The maximal ideal of the factor is the image of `𝔭`. -/
theorem maximalIdeal_factor [IsLocalRing (Factor p ε)]
    (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε}) :
    maximalIdeal (Factor p ε) = 𝔭.map (resO p ε) :=
  (IsLocalRing.eq_maximalIdeal (isMaximal_map_resO p 𝔭 σ hker)).symm

section

variable {p 𝔭 σ} {e : ℕ} {J C : Ideal A} {ϖ : A}

namespace FactorData

variable (h : FactorData p 𝔭 σ ε e J C ϖ)
include h

/-- The image of `𝔭` in the factor is maximal. -/
theorem isMaximal_map : (𝔭.map (resO p ε)).IsMaximal :=
  isMaximal_map_resO p 𝔭 σ h.ker

/-- The maximal ideal of the factor is the image of `𝔭`. -/
theorem maximalIdeal_eq [IsLocalRing (Factor p ε)] :
    maximalIdeal (Factor p ε) = 𝔭.map (resO p ε) :=
  maximalIdeal_factor p 𝔭 σ h.ker

end FactorData

end

/-! ### The image of `J` is everything, and `(𝔭O)^e = pO` -/

/-- The image of `J` in the factor is the unit ideal: `ε` lies in the extension of `J` to
`R` and becomes `1` in the factor. -/
theorem map_eq_top_of_mem {J : Ideal A} (hεJ : ε ∈ extIdeal p J) :
    J.map (resO p ε) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← mkFactor_epsilon p ε, map_resO_eq]
  exact Ideal.mem_map_of_mem _ hεJ

/-- The exact power identity `(𝔭O)^e = pO`: the complementary factor `J` of
`p·A = 𝔭^e·J` becomes the unit ideal in the factor. -/
theorem span_natCast_eq_pow {e : ℕ} {J : Ideal A}
    (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J) (hεJ : ε ∈ extIdeal p J) :
    Ideal.span {(p : Factor p ε)} = 𝔭.map (resO p ε) ^ e := by
  have h := congrArg (Ideal.map (resO p ε)) hpJ
  rwa [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_mul, Ideal.map_pow,
    map_eq_top_of_mem p hεJ, Ideal.mul_top] at h

/-- The `p`-adic topology of the factor is the `𝔭O`-adic one. -/
theorem isAdic_map {e : ℕ} (he : 0 < e) {J : Ideal A} (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J)
    (hεJ : ε ∈ extIdeal p J) : IsAdic (𝔭.map (resO p ε)) :=
  IsAdic.of_pow he (span_natCast_eq_pow p 𝔭 hpJ hεJ ▸ isAdic_span_natCast p ε)

section

variable {p 𝔭 σ} {e : ℕ} {J C : Ideal A} {ϖ : A}

namespace FactorData

variable (h : FactorData p 𝔭 σ ε e J C ϖ)
include h

/-- The `p`-adic topology of the factor is the `𝔭O`-adic one. -/
theorem isAdic_map : IsAdic (𝔭.map (resO p ε)) :=
  NumberFieldBase.isAdic_map p 𝔭 h.epos h.hpJ h.memJ

end FactorData

end

/-! ### Torsion-freeness and characteristic zero -/

variable [Module.Free ℤ A]

/-- The factor is torsion-free: multiplying a relation by `ε` lifts it to the base-change
ring `R`, which is torsion-free as a free module over the characteristic-zero domain `W`. -/
theorem hasUniqueDiv_factor (hε : IsIdempotentElem ε) : HasUniqueDiv (Factor p ε) where
  nsmul_right_injective n hn a b hab := by
    have : HasUniqueDiv R := .of_isTorsionFree W _
    obtain ⟨r, hr⟩ := mkFactor_surjective p ε (a - b)
    have hmem : n • r ∈ Ideal.span {1 - ε} := by
      rw [← mkFactor_eq_zero_iff, map_nsmul, hr, smul_sub, sub_eq_zero]
      exact hab
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hmem
    have hεd : n • (r * ε) = 0 := by
      rw [← smul_mul_assoc, hd, mul_right_comm, hε.one_sub_mul_self, zero_mul]
    have hmk : mkFactor p ε r = mkFactor p ε (r * ε) := by
      rw [map_mul, mkFactor_epsilon, mul_one]
    rw [← sub_eq_zero, ← hr, hmk, (nsmul_eq_zero_iff_right hn).mp hεd, map_zero]

/-- The factor has characteristic `0`. -/
theorem charZero_factor (hε : IsIdempotentElem ε) (h1ε : rho p 𝔭 σ (1 - ε) = 0) :
    CharZero (Factor p ε) :=
  have := nontrivial_factor p 𝔭 σ h1ε
  have := hasUniqueDiv_factor p hε
  CharZero.of_hasUniqueDiv (Factor p ε) (Factor p ε)

section

variable {p 𝔭 σ} {e : ℕ} {J C : Ideal A} {ϖ : A}

namespace FactorData

variable (h : FactorData p 𝔭 σ ε e J C ϖ)
include h

/-- The factor is torsion-free. -/
theorem hasUniqueDiv : HasUniqueDiv (Factor p ε) :=
  hasUniqueDiv_factor p h.idem

/-- The factor has characteristic `0`. -/
theorem charZero : CharZero (Factor p ε) :=
  charZero_factor p 𝔭 σ h.idem (rho_one_sub_eq_zero h.ker)

end FactorData

end

/-! ### Completeness and locality of the factor -/

variable [Module.Finite ℤ A]

/-- The factor is `p`-adically complete: it is the quotient of the `p`-adically complete
ring `R` by `(1 - ε)`, and completeness passes to such a corner. -/
theorem isAdicComplete_span_natCast (hε : IsIdempotentElem ε) :
    IsAdicComplete (Ideal.span {(p : Factor p ε)}) (Factor p ε) := by
  have h := hε.isAdicComplete_quotient (Ideal.span {(p : R)})
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

/-- The factor is Hausdorff for its `p`-adic topology. -/
theorem t2Space_factor (hε : IsIdempotentElem ε) : T2Space (Factor p ε) :=
  (isAdic_span_natCast p ε).isHausdorff_iff.mp (isAdicComplete_span_natCast p hε).toIsHausdorff

/-- The factor is complete for its `p`-adic topology. -/
theorem completeSpace_factor (hε : IsIdempotentElem ε) : CompleteSpace (Factor p ε) :=
  (isAdic_span_natCast p ε).isPrecomplete_iff.mp
    (isAdicComplete_span_natCast p hε).toIsPrecomplete

/-- `𝔭O`-adic completeness follows from `p`-adic completeness: the two filtrations are
cofinal, since `(𝔭O)^e = pO`. -/
theorem isAdicComplete_map (hε : IsIdempotentElem ε) {e : ℕ} (he : 0 < e)
    {J : Ideal A} (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J) (hεJ : ε ∈ extIdeal p J) :
    IsAdicComplete (𝔭.map (resO p ε)) (Factor p ε) := by
  have h1 := isAdicComplete_span_natCast p hε
  have hle : Ideal.span {(p : Factor p ε)} ≤ 𝔭.map (resO p ε) := by
    rw [span_natCast_eq_pow p 𝔭 hpJ hεJ]
    exact Ideal.pow_le_self he.ne'
  exact isAdicComplete_of_le_of_pow_le he hle (span_natCast_eq_pow p 𝔭 hpJ hεJ).ge

/-- The factor is a local ring: it is `𝔭O`-adically complete, and `𝔭O` is maximal. -/
theorem isLocalRing_factor (hε : IsIdempotentElem ε) {e : ℕ} (he : 0 < e)
    {J : Ideal A} (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J) (hεJ : ε ∈ extIdeal p J)
    (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε}) :
    IsLocalRing (Factor p ε) :=
  have := isMaximal_map_resO p 𝔭 σ hker
  have := isAdicComplete_map p 𝔭 hε he hpJ hεJ
  isLocalRing_of_isAdicComplete_maximal (𝔭.map (resO p ε))

/-- Elements outside the image of `𝔭` are units: `𝔭O` is the maximal ideal of the local
factor. -/
theorem isUnit_of_notMem_map (hε : IsIdempotentElem ε) {e : ℕ} (he : 0 < e)
    {J : Ideal A} (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J) (hεJ : ε ∈ extIdeal p J)
    (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε})
    {x : Factor p ε} (hx : x ∉ 𝔭.map (resO p ε)) : IsUnit x :=
  have := isLocalRing_factor p 𝔭 σ hε he hpJ hεJ hker
  notMem_maximalIdeal.mp (maximalIdeal_factor p 𝔭 σ hker ▸ hx)

section

variable {p 𝔭 σ} {e : ℕ} {J C : Ideal A} {ϖ : A}

namespace FactorData

variable (h : FactorData p 𝔭 σ ε e J C ϖ)
include h

/-- The factor is `𝔭O`-adically complete. -/
theorem isAdicComplete : IsAdicComplete (𝔭.map (resO p ε)) (Factor p ε) :=
  isAdicComplete_map p 𝔭 h.idem h.epos h.hpJ h.memJ

/-- The factor is Hausdorff. -/
theorem t2Space : T2Space (Factor p ε) := t2Space_factor p h.idem

/-- The factor is complete. -/
theorem completeSpace : CompleteSpace (Factor p ε) := completeSpace_factor p h.idem

/-- The factor is a local ring. -/
theorem isLocalRing : IsLocalRing (Factor p ε) :=
  isLocalRing_factor p 𝔭 σ h.idem h.epos h.hpJ h.memJ h.ker

/-- Elements outside the image of `𝔭` are units. -/
theorem isUnit_of_notMem_map {x : Factor p ε} (hx : x ∉ 𝔭.map (resO p ε)) : IsUnit x :=
  NumberFieldBase.isUnit_of_notMem_map p 𝔭 σ h.idem h.epos h.hpJ h.memJ h.ker hx

end FactorData

end

/-! ### The uniformizer -/

/-- Elements of `A` outside `𝔭` become units of the factor. -/
theorem isUnit_resO_of_notMem [𝔭.IsMaximal] (hε : IsIdempotentElem ε) {e : ℕ} (he : 0 < e)
    {J : Ideal A} (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J) (hεJ : ε ∈ extIdeal p J)
    (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε})
    {s : A} (hs : s ∉ 𝔭) : IsUnit (resO p ε s) := by
  refine isUnit_of_notMem_map p 𝔭 σ hε he hpJ hεJ hker fun hmem ↦ hs ?_
  rw [← ker_rhoO p 𝔭 σ hker, RingHom.mem_ker, rhoO_resO] at hmem
  rw [← map_zero σ] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp (σ.injective hmem)

/-- **The image of `𝔭` is principal**, generated by the image of any `ϖ` with
`(ϖ) = 𝔭·C`, `C ⊄ 𝔭` (a uniformizer of the localization at `𝔭`). -/
theorem map_eq_span [𝔭.IsMaximal] (hε : IsIdempotentElem ε) {e : ℕ} (he : 0 < e)
    {J : Ideal A} (hpJ : Ideal.span {(p : A)} = 𝔭 ^ e * J) (hεJ : ε ∈ extIdeal p J)
    (hker : RingHom.ker (rho p 𝔭 σ) = extIdeal p 𝔭 ⊔ Ideal.span {1 - ε})
    {ϖ : A} {C : Ideal A} (hϖC : Ideal.span {ϖ} = 𝔭 * C) (hC : ¬ C ≤ 𝔭) :
    𝔭.map (resO p ε) = Ideal.span {resO p ε ϖ} := by
  have hϖ𝔭 : ϖ ∈ 𝔭 := Ideal.mul_le_left (hϖC ▸ Ideal.mem_span_singleton_self ϖ)
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hsC, hs𝔭⟩ := IsConcreteLE.not_le_iff_exists.mp hC
    have hxs : x * s ∈ Ideal.span {ϖ} := hϖC ▸ Ideal.mul_mem_mul hx hsC
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hxs
    have hsu := isUnit_resO_of_notMem p 𝔭 σ hε he hpJ hεJ hker hs𝔭
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    refine (IsUnit.dvd_mul_right hsu).mp ⟨resO p ε a, ?_⟩
    rw [← map_mul, ← map_mul, ha]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hϖ𝔭

/-! ### The discrete-valuation structure -/

variable {e : ℕ} {J C : Ideal A} {ϖ : A}

variable [𝔭.IsMaximal]

namespace FactorData

variable {p 𝔭 σ}
variable (h : FactorData p 𝔭 σ ε e J C ϖ)
include h

/-- The image of `𝔭` is generated by the image of the uniformizer. -/
theorem map_eq_span : 𝔭.map (resO p ε) = Ideal.span {resO p ε ϖ} :=
  NumberFieldBase.map_eq_span p 𝔭 σ h.idem h.epos h.hpJ h.memJ h.ker h.span_uniformizer h.not_le

/-- Elements of `A` outside `𝔭` become units of the factor. -/
theorem isUnit_resO_of_notMem {s : A} (hs : s ∉ 𝔭) : IsUnit (resO p ε s) :=
  NumberFieldBase.isUnit_resO_of_notMem p 𝔭 σ h.idem h.epos h.hpJ h.memJ h.ker hs

/-- The image of the uniformizer satisfies `π^e = p·(unit)`. -/
theorem exists_unit_pow_eq :
    ∃ w : (Factor p ε)ˣ, resO p ε ϖ ^ e = (p : Factor p ε) * w := by
  have hspan : Ideal.span {resO p ε ϖ ^ e} = Ideal.span {(p : Factor p ε)} := by
    rw [← Ideal.span_singleton_pow, ← h.map_eq_span, ← span_natCast_eq_pow p 𝔭 h.hpJ h.memJ]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp
    (hspan ▸ Ideal.mem_span_singleton_self (resO p ε ϖ ^ e))
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp
    (hspan ▸ Ideal.mem_span_singleton_self (p : Factor p ε))
  have := h.hasUniqueDiv
  have h0 : (1 : Factor p ε) - w * v = 0 :=
    (nsmul_eq_zero_iff_right (Fact.out : p.Prime).ne_zero).mp
      (by rw [nsmul_eq_mul]; linear_combination hv + v * hw)
  exact ⟨⟨w, v, by linear_combination -h0, by linear_combination -h0⟩, hw⟩

/-- No power of the uniformizer vanishes: `π^(e·j) = p^j·(unit)`, and `p` is regular. -/
theorem resO_pow_ne_zero (j : ℕ) : resO p ε ϖ ^ j ≠ 0 := by
  intro h0
  obtain ⟨w, hw⟩ := h.exists_unit_pow_eq
  have := h.hasUniqueDiv
  have h1 : (p ^ j) • (w : Factor p ε) ^ j = 0 := by
    rw [nsmul_eq_mul]
    push_cast
    rw [← mul_pow, ← hw, pow_right_comm, h0, zero_pow h.epos.ne']
  have hw0 : (w : Factor p ε) ^ j = 0 :=
    (nsmul_eq_zero_iff_right (pow_ne_zero j (Fact.out : p.Prime).ne_zero)).mp h1
  have := nontrivial_factor p 𝔭 σ (rho_one_sub_eq_zero h.ker)
  exact Units.ne_zero (w ^ j) (by rwa [Units.val_pow_eq_pow_val])

/-- The image of the uniformizer is nonzero. -/
theorem resO_ne_zero : resO p ε ϖ ≠ 0 := by simpa using h.resO_pow_ne_zero 1

/-- **Every nonzero element of the factor is a unit times a power of the uniformizer.** -/
theorem exists_unit_mul_pow {x : Factor p ε} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (Factor p ε)ˣ), ↑u * resO p ε ϖ ^ n = x := by
  have hcompl := h.isAdicComplete
  have hspan := h.map_eq_span
  obtain ⟨n, hxn, hxn1⟩ := IsHausdorff.exists_mem_pow_and_notMem_pow_succ (𝔭.map (resO p ε)) hx
  rw [hspan, Ideal.span_singleton_pow] at hxn
  rw [hspan] at hxn1
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxn
  have hyu : IsUnit y := by
    by_contra hyn
    have hymem : y ∈ 𝔭.map (resO p ε) := by
      by_contra hyn'
      exact hyn (h.isUnit_of_notMem_map hyn')
    rw [hspan, Ideal.mem_span_singleton] at hymem
    obtain ⟨d, hd⟩ := hymem
    refine hxn1 ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr ⟨d, by rw [hy, hd, pow_succ]; ring⟩
  refine ⟨n, hyu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  linear_combination -hy

/-- The factor is a domain. -/
theorem isDomain : IsDomain (Factor p ε) := by
  have hnt := nontrivial_factor p 𝔭 σ (rho_one_sub_eq_zero h.ker)
  have hnzd : NoZeroDivisors (Factor p ε) := by
    constructor
    intro a b hab
    by_contra! hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨n, u, hu⟩ := h.exists_unit_mul_pow ha
    obtain ⟨m, v, hv⟩ := h.exists_unit_mul_pow hb
    have hz : (↑(u * v) : Factor p ε) * resO p ε ϖ ^ (n + m) = 0 := by
      rw [← hu, ← hv] at hab
      rw [Units.val_mul, pow_add]
      linear_combination hab
    refine h.resO_pow_ne_zero (n + m) ?_
    simpa [← mul_assoc] using congrArg (fun t ↦ (↑(u * v)⁻¹ : Factor p ε) * t) hz
  exact NoZeroDivisors.to_isDomain _

/-- The image of the uniformizer is irreducible. -/
theorem irreducible : Irreducible (resO p ε ϖ) := by
  have := h.isDomain
  refine Ideal.irreducible_of_isMaximal_span_singleton h.resO_ne_zero ?_
  rw [← h.map_eq_span]
  exact h.isMaximal_map

/-- **The local factor is a discrete valuation ring.** -/
theorem isDiscreteValuationRing [IsDomain (Factor p ε)] :
    IsDiscreteValuationRing (Factor p ε) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨resO p ε ϖ, h.irreducible, fun {x} hx ↦ ?_⟩
  obtain ⟨n, u, hu⟩ := h.exists_unit_mul_pow hx
  exact ⟨n, u, by rw [mul_comm]; exact hu⟩

/-- **The bundled uniformizer certificate** consumed by the abstract main theorems:
the image of `ϖ` generates the maximal ideal, `p` lies in it, and `p ∣ π^e`. -/
theorem isUniformizer [IsLocalRing (Factor p ε)] : IsLocalRing.IsUniformizer (resO p ε ϖ) p e := by
  have hspanp := span_natCast_eq_pow p 𝔭 h.hpJ h.memJ
  refine ⟨Fact.out, ?_, ?_, ?_⟩
  · rw [h.maximalIdeal_eq, h.map_eq_span]
  · rw [h.maximalIdeal_eq]
    refine Ideal.pow_le_self h.epos.ne' ?_
    rw [← hspanp]
    exact Ideal.mem_span_singleton_self _
  · obtain ⟨w, hw⟩ := h.exists_unit_pow_eq
    exact ⟨w, hw⟩

end FactorData

end NumberFieldBase

end ChabautyColeman

end
