/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Roy.Subquot
public import LeanPool.RoyStrongSix.Roy.Support
public import LeanPool.RoyStrongSix.Thm1.MultEst

/-!
# From the obstruction subgroup `H = h₀ × T_U` to the map `s`

`MultEst Qbar` returns `h₀ ⊂ Qbar^{d₀}` and a space of characters `U ⊂ ℚ^{d₁}`. We build the
block-diagonal map

  `s(u, v) = (Ψ u, Φ v) : ℂ^{d₀} × ℂ^{d₁} → ℂ^{d₀ - dim h₀} × ℂ^{dim U}`.

* `Ψ` has `Qbar` entries and kernel `h₀` on `Qbar`-points.
* The rows of `Φ` are a `ℚ`-basis of `U`.

`exists_quotient` proves:
* `s` is surjective, and sends `Qbar^{d₀} × 0` into `Qbar^{d₀'} × 0` and `0 × ℚ^{d₁}` into `0 ×
ℚ^{d₁'}`;
* `dim s(W) = dim W_K − dim (W_K ∩ (h₀ × U^⊥))`, the exponent `c` of `MultEst`, where
  `W_K = W ∩ Qbar^d` (`finrank_map_eq`);
* if `g ≡ g' (mod H)` for `g = exp_G γ` and `g' = exp_G γ'`, then `s(γ − γ') ∈ Ω'`
(`sub_mem_Omega`).
-/

@[expose] public section

namespace LeanPool

open Module Submodule Matrix
open StrongSix.Roy

namespace StrongSix.Thm1

/-! ### Generic linear algebra -/

/-- A matrix with linearly independent rows has a surjective `mulVecLin`. -/
theorem mulVecLin_surjective {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (M : Matrix (Fin m) (Fin n) 𝕜)
    (h : LinearIndependent 𝕜 fun k => M k) : Function.Surjective M.mulVecLin := by
  have hr : M.rank = m := by
    rw [Matrix.rank_eq_finrank_span_row]
    exact (finrank_span_eq_card h).trans (Fintype.card_fin m)
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hr, finrank_fin_fun]
  exact LinearMap.range_eq_top.mp htop

variable {d0 d1 : ℕ}

/-- The inclusion `Qbar^n → ℂ^n`. -/
noncomputable def incl (n : ℕ) : (Fin n → Qb) →ₗ[Qb] (Fin n → ℂ) :=
  LinearMap.compLeft (Algebra.linearMap Qb ℂ) (Fin n)

theorem incl_apply {n : ℕ} (x : Fin n → Qb) (i : Fin n) : incl n x i = (x i : ℂ) := rfl

theorem incl_injective (n : ℕ) : Function.Injective (incl n) := fun x y h => by
  funext i
  exact Subtype.val_injective (congrFun h i)

/-- The inclusion `Qbar^{d₀} × Qbar^{d₁} → E`. -/
noncomputable def inclL (d0 d1 : ℕ) : LieG Qb d0 d1 →ₗ[Qb] E d0 d1 :=
  LinearMap.prodMap (incl d0) (incl d1)

theorem inclL_injective : Function.Injective (inclL d0 d1) := fun x y h => by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (incl_injective d0 h1) (incl_injective d1 h2)

theorem algVec_incl {n : ℕ} (x : Fin n → Qb) : AlgVec (incl n x) := fun i =>
  mem_algebraicClosure_iff.mp (x i).2

/-- Every algebraic vector comes from `Qbar^n`. -/
theorem exists_incl_of_algVec {n : ℕ} {u : Fin n → ℂ} (hu : AlgVec u) : ∃ x, incl n x = u :=
  ⟨fun i => ⟨u i, mem_algebraicClosure_iff.mpr (hu i)⟩, rfl⟩

/-- `algPts U = inclL '' (comap inclL U)`. -/
theorem algPts_eq_map (U : Submodule ℂ (E d0 d1)) :
    algPts U = ((U.restrictScalars Qb).comap (inclL d0 d1)).map (inclL d0 d1) := by
  ext p
  constructor
  · rintro ⟨hpU, h1, h2⟩
    obtain ⟨x0, hx0⟩ := exists_incl_of_algVec h1
    obtain ⟨x1, hx1⟩ := exists_incl_of_algVec h2
    have hp : inclL d0 d1 (x0, x1) = p := Prod.ext hx0 hx1
    exact ⟨(x0, x1), by simpa [hp] using hpU, hp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, algVec_incl _, algVec_incl _⟩

/-- **Dimensions of `Qbar`-rational subspaces** are dimensions of their `Qbar`-points. -/
theorem finrank_eq_of_rational {U : Submodule ℂ (E d0 d1)} (hU : RationalOverQbar U) :
    finrank ℂ U = finrank Qb ((U.restrictScalars Qb).comap (inclL d0 d1)) := by
  have h1 : finrank ℂ U = finrank Qb (algPtsT U) := by
    conv_lhs => rw [(rationalOverQbar_iff U).mp hU, span_algPts_eq_map]
    rw [LinearEquiv.finrank_map_eq, finrank_span_of_le_Fpts _ (algPtsT_le U)]
  have h2 : finrank Qb (algPtsT U) = finrank Qb (algPts U) := by
    have : algPtsT U = (algPts U).map ((eqv d0 d1).symm.toLinearMap.restrictScalars Qb) := by
      ext x
      simp only [algPtsT, mem_comap, mem_map]
      constructor
      · intro hx; exact ⟨_, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this]
    exact LinearEquiv.finrank_map_eq ((eqv d0 d1).symm.restrictScalars Qb) _
  rw [h1, h2, algPts_eq_map]
  exact ((Submodule.equivMapOfInjective (inclL d0 d1) inclL_injective
    ((U.restrictScalars Qb).comap (inclL d0 d1))).finrank_eq).symm

/-! ### The additive block `Ψ` -/

section Build

variable (h0 : Submodule Qb (Fin d0 → Qb)) (U : Submodule ℚ (Fin d1 → ℚ))

/-- A surjection `Qbar^{d₀} → Qbar^{d₀ - dim h₀}` with kernel `h₀`. -/
noncomputable def psiK : (Fin d0 → Qb) →ₗ[Qb] (Fin (d0 - finrank Qb h0) → Qb) :=
  (LinearEquiv.ofFinrankEq ((Fin d0 → Qb) ⧸ h0) (Fin (d0 - finrank Qb h0) → Qb)
    (by rw [Submodule.finrank_quotient, finrank_fin_fun, finrank_fin_fun])).toLinearMap ∘ₗ h0.mkQ

theorem ker_psiK : LinearMap.ker (psiK h0) = h0 := by
  rw [psiK, LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem psiK_surjective : Function.Surjective (psiK h0) :=
  (LinearEquiv.surjective _).comp (Submodule.mkQ_surjective h0)

/-- The matrix of `ψ`. -/
noncomputable def Mpsi : Matrix (Fin (d0 - finrank Qb h0)) (Fin d0) Qb := LinearMap.toMatrix'
  (psiK h0)

/-- `Ψ : ℂ^{d₀} → ℂ^{d₀'}`, with `Qbar` entries. -/
noncomputable def PsiC : (Fin d0 → ℂ) →ₗ[ℂ] (Fin (d0 - finrank Qb h0) → ℂ) :=
  ((Mpsi h0).map (algebraMap Qb ℂ)).mulVecLin

theorem PsiC_incl (x : Fin d0 → Qb) : PsiC h0 (incl d0 x) = incl _ (psiK h0 x) := by
  funext k
  rw [incl_apply, PsiC, Matrix.mulVecLin_apply, ← LinearMap.toMatrix'_mulVec (psiK h0)]
  exact (RingHom.map_mulVec (algebraMap Qb ℂ) (Mpsi h0) x k).symm

theorem rows_Mpsi_linearIndependent : LinearIndependent Qb fun k => Mpsi h0 k := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k0
  obtain ⟨x, hx⟩ := psiK_surjective h0 (Pi.single k0 1)
  have h1 : c ⬝ᵥ (Mpsi h0 *ᵥ x) = 0 := by
    rw [Matrix.dotProduct_mulVec]
    have : c ᵥ* Mpsi h0 = 0 := by
      funext j
      have := congrFun hc j
      simpa [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm] using this
    rw [this, zero_dotProduct]
  rw [Mpsi, LinearMap.toMatrix'_mulVec, hx, dotProduct_single, mul_one] at h1
  exact h1

theorem PsiC_surjective : Function.Surjective (PsiC h0) := by
  apply mulVecLin_surjective
  have hrow : (fun k => (Mpsi h0).map (algebraMap Qb ℂ) k) = fun k => incl d0 (Mpsi h0 k) := rfl
  rw [hrow]
  refine linearIndependent_of_Fpts (F := Qb) (fun k => algVec_iff.mp (algVec_incl _)) ?_
  exact (rows_Mpsi_linearIndependent h0).map' (incl d0)
    (LinearMap.ker_eq_bot.mpr (incl_injective d0))

/-! ### The multiplicative block `Φ` -/

/-- The rows of `Φ`: a `ℚ`-basis of `U`. -/
noncomputable def phiRow (k : Fin (finrank ℚ U)) : Fin d1 → ℚ := (Module.finBasis ℚ U k : Fin d1
  → ℚ)

theorem phiRow_mem (k : Fin (finrank ℚ U)) : phiRow U k ∈ U := (Module.finBasis ℚ U k).2

theorem phiRow_linearIndependent : LinearIndependent ℚ (phiRow U) :=
  (Module.finBasis ℚ U).linearIndependent.map' U.subtype (Submodule.ker_subtype U)

/-- `Φ : ℂ^{d₁} → ℂ^{dim U}`, with rational entries. -/
noncomputable def PhiC : (Fin d1 → ℂ) →ₗ[ℂ] (Fin (finrank ℚ U) → ℂ) :=
  (Matrix.of fun k j => ((phiRow U k j : ℚ) : ℂ)).mulVecLin

theorem PhiC_apply (v : Fin d1 → ℂ) (k : Fin (finrank ℚ U)) :
    PhiC U v k = ∑ j, ((phiRow U k j : ℚ) : ℂ) * v j := rfl

/-- The inclusion `ℚ^n → ℂ^n`. -/
noncomputable def inclQ (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℂ) :=
  LinearMap.compLeft (Algebra.linearMap ℚ ℂ) (Fin n)

theorem inclQ_injective (n : ℕ) : Function.Injective (inclQ n) := fun x y h => by
  funext i
  have := congrFun h i
  simpa [inclQ] using this

theorem PhiC_surjective : Function.Surjective (PhiC U) := by
  apply mulVecLin_surjective
  have hrow : (fun k => (Matrix.of fun k j => ((phiRow U k j : ℚ) : ℂ)) k) =
      fun k => inclQ d1 (phiRow U k) := rfl
  rw [hrow]
  refine linearIndependent_of_Fpts (F := ℚ) (fun k => ratVec_iff.mp fun j => ⟨_, rfl⟩) ?_
  exact (phiRow_linearIndependent U).map' (inclQ d1)
    (LinearMap.ker_eq_bot.mpr (inclQ_injective d1))

/-! ### The map `s` -/

/-- `s(u, v) = (Ψ u, Φ v)`. -/
noncomputable def sMap : E d0 d1 →ₗ[ℂ] E (d0 - finrank Qb h0) (finrank ℚ U) :=
  LinearMap.prodMap (PsiC h0) (PhiC U)

theorem sMap_surjective : Function.Surjective (sMap h0 U) := by
  rintro ⟨a, b⟩
  obtain ⟨u, rfl⟩ := PsiC_surjective h0 a
  obtain ⟨v, rfl⟩ := PhiC_surjective U b
  exact ⟨(u, v), rfl⟩

theorem sMap_alg (u : Fin d0 → ℂ) (hu : AlgVec u) :
    ∃ u', AlgVec u' ∧ sMap h0 U (u, 0) = (u', 0) := by
  obtain ⟨x, rfl⟩ := exists_incl_of_algVec hu
  refine ⟨incl _ (psiK h0 x), algVec_incl _, ?_⟩
  simp [sMap, PsiC_incl]

theorem PhiC_ratVec (v : Fin d1 → ℂ) (hv : RatVec v) : RatVec (PhiC U v) := by
  intro k
  choose q hq using hv
  refine ⟨∑ j, phiRow U k j * q j, ?_⟩
  rw [PhiC_apply]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [hq j]

theorem sMap_rat (v : Fin d1 → ℂ) (hv : RatVec v) :
    ∃ v', RatVec v' ∧ sMap h0 U (0, v) = (0, v') :=
  ⟨PhiC U v, PhiC_ratVec U v hv, by simp [sMap]⟩

/-- The kernel of `s` on `Qbar`-points is `h₀ × U^⊥`. -/
theorem sMap_inclL_eq_zero_iff (x : LieG Qb d0 d1) :
    sMap h0 U (inclL d0 d1 x) = 0 ↔ x ∈ h0.prod (torusLie Qb U) := by
  have e1 : sMap h0 U (inclL d0 d1 x) = (incl _ (psiK h0 x.1), PhiC U (incl d1 x.2)) := by
    simp [sMap, inclL, PsiC_incl]
  rw [e1, Prod.mk_eq_zero, Submodule.mem_prod]
  apply and_congr
  · rw [show x.1 ∈ h0 ↔ psiK h0 x.1 = 0 by rw [← LinearMap.mem_ker, ker_psiK]]
    constructor
    · intro h; exact incl_injective _ (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  · -- `Φ (x₂) = 0` iff `Σ φ_j x₂_j = 0` for all `φ ∈ U`
    have hk : ∀ k, PhiC U (incl d1 x.2) k = ((∑ j, (phiRow U k j : Qb) * x.2 j : Qb) : ℂ) := by
      intro k
      rw [PhiC_apply]
      push_cast
      rfl
    constructor
    · intro h φ hφ
      have hrepr := (Module.finBasis ℚ U).sum_repr ⟨φ, hφ⟩
      have hφeq : φ = ∑ k, (Module.finBasis ℚ U).repr ⟨φ, hφ⟩ k • phiRow U k := by
        have := congrArg Subtype.val hrepr
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      have hzero : ∀ k, (∑ j, (phiRow U k j : Qb) * x.2 j) = 0 := fun k => by
        have := congrFun h k
        rw [hk, Pi.zero_apply] at this
        exact_mod_cast this
      rw [hφeq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have := hzero k
      calc ∑ j, ((Module.finBasis ℚ U).repr ⟨φ, hφ⟩ k : Qb) * (phiRow U k j : Qb) * x.2 j
          = ((Module.finBasis ℚ U).repr ⟨φ, hφ⟩ k : Qb) * ∑ j, (phiRow U k j : Qb) * x.2 j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [this, mul_zero]
    · intro h
      funext k
      rw [hk, h _ (phiRow_mem U k)]
      rfl

theorem ker_sMap_rational : RationalOverQbar (LinearMap.ker (sMap h0 U)) := by
  rw [sMap, LinearMap.ker_prodMap]
  refine rationalOverQbar_prod (isRat_ker (F := Qb) _ fun x hx => ?_) (isRat_ker (F := ℚ) _ fun
    x hx => ?_)
  · obtain ⟨y, rfl⟩ := exists_incl_of_algVec (algVec_iff.mpr hx)
    rw [PsiC_incl]
    exact algVec_iff.mp (algVec_incl _)
  · exact ratVec_iff.mp (PhiC_ratVec U x (ratVec_iff.mpr hx))

/-- The `Qbar`-points `W_K = W ∩ Qbar^d` of `W`, as a subspace of `Qbar^{d₀} × Qbar^{d₁}`. -/
noncomputable def WK (W : Submodule ℂ (E d0 d1)) : Submodule Qb (LieG Qb d0 d1) :=
  (W.restrictScalars Qb).comap (inclL d0 d1)

/-- **`dim s(W) = c`**, the exponent of `T` in `MultEst`. -/
theorem finrank_map_sMap (W : Submodule ℂ (E d0 d1)) (hW : RationalOverQbar W) :
    finrank ℂ (W.map (sMap h0 U)) =
      finrank Qb (WK W) - finrank Qb ↥(WK W ⊓ h0.prod (torusLie Qb U)) := by
  have h1 := finrank_map_add_inf_ker (sMap h0 U) W
  have h2 : finrank ℂ W = finrank Qb (WK W) := finrank_eq_of_rational hW
  have h3 : finrank ℂ ↥(W ⊓ LinearMap.ker (sMap h0 U)) =
      finrank Qb ↥(WK W ⊓ h0.prod (torusLie Qb U)) := by
    have hsub : (((W ⊓ LinearMap.ker (sMap h0 U)).restrictScalars Qb).comap (inclL d0 d1)) =
        WK W ⊓ h0.prod (torusLie Qb U) := by
      ext x
      simp only [WK, mem_comap, Submodule.restrictScalars_mem, mem_inf, LinearMap.mem_ker,
        sMap_inclL_eq_zero_iff]
    rw [finrank_eq_of_rational (rationalOverQbar_inf hW (ker_sMap_rational h0 U)), hsub]
  omega

/-- A common denominator: `m · φ` is integral for some `m ≠ 0`. -/
theorem exists_common_den {n : ℕ} (φ : Fin n → ℚ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ z : Fin n → ℤ, ∀ j, (z j : ℚ) = m * φ j := by
  classical
  refine ⟨∏ j, (φ j).den, Finset.prod_ne_zero_iff.mpr fun j _ => (φ j).den_nz, ?_⟩
  refine ⟨fun j => (∏ i ∈ Finset.univ.erase j, ((φ i).den : ℤ)) * (φ j).num, fun j => ?_⟩
  push_cast
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_assoc, Rat.den_mul_eq_num]

/-- **Equivalence mod `H` forces `s(γ − γ') ∈ Ω'`.** Here `g = exp_G γ` and `g' = exp_G γ'`. -/
theorem sMap_sub_mem_Omega (γ γ' : E d0 d1) (g g' : GPt Qb d0 d1)
    (hg1 : ∀ i, algebraMap Qb ℂ (g.1 i) = γ.1 i)
    (hg2 : ∀ j, algebraMap Qb ℂ (g.2 j : Qb) = Complex.exp (γ.2 j))
    (hg1' : ∀ i, algebraMap Qb ℂ (g'.1 i) = γ'.1 i)
    (hg2' : ∀ j, algebraMap Qb ℂ (g'.2 j : Qb) = Complex.exp (γ'.2 j))
    (hE : EquivMod h0 U g g') :
    sMap h0 U (γ - γ') ∈ Omega (d0 - finrank Qb h0) (finrank ℚ U) := by
  -- the additive part vanishes
  have hadd : PsiC h0 (γ.1 - γ'.1) = 0 := by
    have : γ.1 - γ'.1 = incl d0 (g.1 - g'.1) := by
      funext i; simp [incl_apply, ← hg1, ← hg1']
    rw [this, PsiC_incl]
    have hk : psiK h0 (g.1 - g'.1) = 0 := by
      rw [← LinearMap.mem_ker, ker_psiK]; exact hE.1
    rw [hk, map_zero]
  -- each multiplicative coordinate is in `2πi ℚ`
  have hmul : ∀ k, ∃ q : ℚ, PhiC U (γ.2 - γ'.2) k = (q : ℂ) * ω := by
    intro k
    obtain ⟨m, hm, z, hz⟩ := exists_common_den (phiRow U k)
    have hzU : (fun j => (z j : ℚ)) ∈ U := by
      have : (fun j => (z j : ℚ)) = (m : ℚ) • phiRow U k := funext fun j => by simp [hz j]
      rw [this]; exact U.smul_mem _ (phiRow_mem U k)
    have hprod := hE.2 z hzU
    have hC : Complex.exp (∑ j, (z j : ℂ) * (γ.2 j - γ'.2 j)) = 1 := by
      have := congrArg (fun u : Qbˣ => algebraMap Qb ℂ (u : Qb)) hprod
      simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val, map_prod,
        map_zpow₀, map_div₀, hg2, hg2', Units.val_one, map_one] at this
      rw [Complex.exp_sum]
      rw [← this]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Complex.exp_int_mul, Complex.exp_sub]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hC
    refine ⟨n / m, ?_⟩
    have hsum : (∑ j, (z j : ℂ) * (γ.2 j - γ'.2 j)) = (m : ℂ) * PhiC U (γ.2 - γ'.2) k := by
      rw [PhiC_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (z j : ℂ) = ((z j : ℚ) : ℂ) := by push_cast; rfl
      rw [this, hz j]
      simp only [Pi.sub_apply]
      push_cast; ring
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    rw [hsum] at hn
    rw [ω]
    push_cast
    field_simp
    linear_combination hn
  choose q hq using hmul
  rw [Omega_eq_map]
  refine ⟨fun k => (q k : ℂ), ratVec_iff.mp fun k => ⟨q k, rfl⟩, ?_⟩
  change (0, ω • fun k => (q k : ℂ)) = sMap h0 U (γ - γ')
  rw [sMap, LinearMap.prodMap_apply, Prod.fst_sub, Prod.snd_sub, hadd]
  congr 1
  funext k
  rw [hq k]
  simp [mul_comm]

end Build

end StrongSix.Thm1

end LeanPool
