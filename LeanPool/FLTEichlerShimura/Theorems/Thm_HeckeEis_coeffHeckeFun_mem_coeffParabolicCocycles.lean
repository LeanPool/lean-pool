/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node HeckeEis.coeffHeckeFun_mem_coeffParabolicCocycles
(600d226f-3cc9-5bc7-917a-bc0a0e9e5854) by Claude (2026-09-05).

Proof based on Prove2Me submission a1c720ca-353d-5914-9331-55d4d08f3909
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Gamma0HeckeOperatorHom
public import LeanPool.FLTEichlerShimura.Definitions.Def_Gamma0CoeffCohomology

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import LeanPool.FLTEichlerShimura.Theorems.Thm_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Hecke operator preserves parabolic cocycles with coefficients

Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, let $K$ be a commutative ring, let $V$ be
a $K$-module and let $\rho$ be a $K$-linear representation of $\Gamma_0(N) \le
\mathrm{SL}(2,\mathbb{Z})$ on $V$. Write $\mathrm{heckeUpper}\,N\,\ell$ for the subgroup of
$\Gamma_0(N)$ consisting of those matrices whose upper right entry is divisible by $\ell$, and
$\mathrm{heckeConj}\,N\,\ell$ for the homomorphism from it to $\Gamma_0(N)$ sending $g$ to
$!![g_{00}, g_{01}/\ell; \ell\, g_{10}, g_{11}]$, i.e. conjugation by $\mathrm{diag}(1,\ell)$. Let
$a : V \to V$ be $K$-linear and assume $a \circ \rho(\mathrm{heckeConj}\,N\,\ell\,u) = \rho(u) \circ
a$ for every $u \in \mathrm{heckeUpper}\,N\,\ell$. Let $z : \Gamma_0(N) \to V$ be a parabolic
$1$-cocycle, that is: $z(gh) = z(g) + \rho(g)(z(h))$ for all $g,h$, and $z(\gamma) \in
\mathrm{range}(\rho(\gamma) - 1)$ for every $\gamma \in \Gamma_0(N)$ whose underlying integral
matrix satisfies $(\operatorname{tr}\gamma)^2 = 4$. Then the function
$\mathrm{coeffHeckeFun}\,N\,\ell\,\rho\,a\,z$, whose value at $g$ is the sum over the (finitely
many) cosets $q \in \Gamma_0(N)/\mathrm{heckeUpper}\,N\,\ell$ of $\rho((g \cdot
q)^{\mathrm{out}})\bigl(a\bigl(z(\mathrm{heckeConj}\,N\,\ell\,((g\cdot q)^{\mathrm{out}})^{-1} g\,
q^{\mathrm{out}})\bigr)\bigr)$ with $q^{\mathrm{out}}$ the chosen coset representative, is again a
parabolic $1$-cocycle.

This is the cochain-level statement that the Hecke correspondence at $\ell$, with coefficients
twisted by the intertwining map $a$, acts on parabolic cocycles of $\Gamma_0(N)$, so that it
descends to parabolic cohomology; the underlying cocycle property alone is
[`HeckeEis.coeffHeckeFun_mem_coeffCocycles`](thm.html#HeckeEis.coeffHeckeFun_mem_coeffCocycles), and
the content added here is the parabolicity condition at elements of trace $\pm 2$. It is used in the
construction of the Hecke action on $H^1_{\mathrm{par}}$ and in the passage from eigensystems in
cohomology to modular forms.

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles.lean

Prove2Me submission: `a1c720ca-353d-5914-9331-55d4d08f3909` (ACCEPTED).
-/

section privateSection


namespace P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis"
  "heckeConjMat heckeUpper coe_heckeConjSL heckeConj coe_heckeConj transferAux coe_transferAux \
    coeffCocycles mem_coeffCocycles_iff IsParabolicCocycle coeffParabolicCocycles \
    mem_coeffParabolicCocycles_iff coeffHeckeFun coeffHeckeFun_apply \
    coeffHeckeFun_mem_coeffCocycles"
namespace ParabolicHeckeSol
p2m_open "HeckeEis"

open CongruenceSubgroup Function
open scoped MatrixGroups

theorem fin_two_sq_eq_trace_smul_sub_one
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) :
    A ^ 2 = A.trace • A - 1 := by
  have hadj : A.adjugate = A.trace • 1 - A := by
    ext i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.trace_fin_two, Matrix.one_fin_two]
  have hAA : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  rw [hadj, mul_sub, Matrix.mul_smul, mul_one, ← sq] at hAA
  have hrearr := sub_sub_cancel (A.trace • A) (A ^ 2)
  rw [hAA] at hrearr; exact hrearr.symm

theorem trace_sq_pow
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) (htr : A.trace ^ 2 = 4) (n : ℕ) :
    (A ^ n).trace ^ 2 = 4 := by
  have hrec : ∀ k, (A ^ (k + 2)).trace = A.trace * (A ^ (k + 1)).trace - (A ^ k).trace := by
    intro k
    have hstep : A ^ (k + 2) = A.trace • A ^ (k + 1) - A ^ k := by
      rw [show k + 2 = 2 + k from Nat.add_comm k 2, pow_add,
        fin_two_sq_eq_trace_smul_sub_one A hdet, sub_mul, smul_mul_assoc,
        ← pow_succ', one_mul]
    rw [hstep, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have hinv : ∀ k, ((A ^ k).trace = 2 ∧ (A ^ (k + 1)).trace = A.trace) ∨
      ((A ^ k).trace = A.trace ∧ (A ^ (k + 1)).trace = 2) := by
    intro k
    induction k with
    | zero =>
      refine Or.inl ⟨?_, by rw [zero_add, pow_one]⟩
      rw [pow_zero, Matrix.trace_one, Fintype.card_fin]; rfl
    | succ m ih =>
      rcases ih with ⟨he, ho⟩ | ⟨he, ho⟩
      · exact Or.inr ⟨ho, by rw [hrec m, ho, he, ← sq, htr]; ring⟩
      · exact Or.inl ⟨ho, by rw [hrec m, ho, he]; ring⟩
  rcases hinv n with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; norm_num
  · rw [h]; exact htr

theorem trace_conj (g h : SL(2, ℤ)) :
    ((g * h * g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

theorem trace_heckeConjMat (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : (heckeConjMat ℓ g).trace =
  g.trace := by
  simp [heckeConjMat, Matrix.trace_fin_two]

section Orbit

variable {N ℓ : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def S (q : Gamma0 N ⧸ heckeUpper N ℓ) : V →ₗ[K] V := ρ (Quotient.out q) ∘ₗ a

variable {ρ a}

theorem S_heckeConj_transferAux
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (v : V) :
    S ρ a (γ • q) (ρ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) v) = ρ γ (S ρ a q v) := by
  have h1 := LinearMap.congr_fun (ha (transferAux (heckeUpper N ℓ) γ q)) v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
  rw [S, S, LinearMap.comp_apply, LinearMap.comp_apply, h1, ← Module.End.mul_apply, ← map_mul,
    coe_transferAux,
    mul_inv_cancel_left, map_mul, Module.End.mul_apply]

variable (γ : Gamma0 N) (x : Gamma0 N ⧸ heckeUpper N ℓ)

def tau (k : ℕ) : ↥(heckeUpper N ℓ) := transferAux (heckeUpper N ℓ) γ (γ ^ k • x)

def piProd : ℕ → ↥(heckeUpper N ℓ)
  | 0 => 1
  | k + 1 => tau γ x k * piProd k

omit [NeZero ℓ] in
theorem coe_piProd (k : ℕ) :
    ((piProd γ x k : ↥(heckeUpper N ℓ)) : Gamma0 N) = (Quotient.out (γ ^ k • x))⁻¹ * (γ ^ k *
      Quotient.out x) := by
  induction k with
  | zero => simp [piProd]
  | succ k ih =>
    rw [piProd, Subgroup.coe_mul, ih, tau, coe_transferAux, ← mul_smul, ← pow_succ']
    group

variable {γ x}

theorem P_succ (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) (k : ℕ) :
    S ρ a (γ ^ (k + 1) • x) (z (heckeConj N ℓ (piProd γ x (k + 1))))
      = S ρ a (γ • (γ ^ k • x)) (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ ^ k • x))))
        + ρ γ (S ρ a (γ ^ k • x) (z (heckeConj N ℓ (piProd γ x k)))) := by
  rw [piProd, map_mul, (mem_coeffCocycles_iff ρ z).mp hz, map_add, pow_succ', mul_smul,
    ← S_heckeConj_transferAux ha γ (γ ^ k • x)]
  rfl

theorem sum_range_eq (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ
  a)
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) (m : ℕ) :
    (LinearMap.range (ρ γ - 1)).mkQ
        (∑ k ∈ Finset.range m,
          S ρ a (γ • (γ ^ k • x)) (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ ^ k • x)))))
      = (LinearMap.range (ρ γ - 1)).mkQ (S ρ a (γ ^ m • x) (z (heckeConj N ℓ (piProd γ x m)))) := by
  induction m with
  | zero =>
    have h0 : z (heckeConj N ℓ (piProd γ x 0)) = 0 := by
      rw [piProd, map_one]
      have := (mem_coeffCocycles_iff ρ z).mp hz 1 1
      rw [mul_one, map_one, Module.End.one_apply] at this
      simpa using this
    simp only [Finset.sum_range_zero, h0, map_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, map_add, ih, P_succ ha hz m, map_add]
    rw [add_comm]
    congr 1
    symm
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨S ρ a (γ ^ m • x) (z (heckeConj N ℓ (piProd γ x m))), by
      rw [LinearMap.sub_apply, Module.End.one_apply]⟩

theorem P_mem_range (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    {z : Gamma0 N → V} {m : ℕ} (hx : γ ^ m • x = x)
    (hpar : z (heckeConj N ℓ (piProd γ x m)) ∈ LinearMap.range (ρ (heckeConj N ℓ (piProd γ x m)) -
      1)) :
    S ρ a (γ ^ m • x) (z (heckeConj N ℓ (piProd γ x m))) ∈ LinearMap.range (ρ γ - 1) := by
  obtain ⟨w, hw⟩ := hpar
  have h1 := LinearMap.congr_fun (ha (piProd γ x m)) w
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
  have hout : Quotient.out x * ((piProd γ x m : ↥(heckeUpper N ℓ)) : Gamma0 N) = γ ^ m *
    Quotient.out x := by
    rw [coe_piProd, hx, mul_inv_cancel_left]
  rw [← hw, LinearMap.sub_apply, Module.End.one_apply, map_sub, hx, S, LinearMap.comp_apply,
    LinearMap.comp_apply,
    h1, ← Module.End.mul_apply, ← map_mul, hout, map_mul, Module.End.mul_apply, map_pow]
  refine ⟨(∑ i ∈ Finset.range m, (ρ γ) ^ i) (ρ (Quotient.out x) (a w)), ?_⟩
  rw [← Module.End.mul_apply, mul_geom_sum, LinearMap.sub_apply, Module.End.one_apply]

end Orbit

section Main

variable {N ℓ : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {ρ : Representation K (Gamma0 N) V} {a : V →ₗ[K] V}

theorem isParabolicCocycle_coeffHeckeFun
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    {z : Gamma0 N → V} (hz : z ∈ coeffParabolicCocycles ρ) :
    IsParabolicCocycle ρ (coeffHeckeFun N ℓ ρ a z) := by
  let : Fintype (Gamma0 N ⧸ heckeUpper N ℓ) := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  obtain ⟨hzc, hzp⟩ := (mem_coeffParabolicCocycles_iff ρ z).mp hz
  intro γ hγ
  set R : Submodule K V := LinearMap.range (ρ γ - 1) with hR
  set f : (Gamma0 N ⧸ heckeUpper N ℓ) → (Gamma0 N ⧸ heckeUpper N ℓ) := fun q => γ • q with hf
  set v : (Gamma0 N ⧸ heckeUpper N ℓ) → V ⧸ R := fun q =>
    R.mkQ (ρ (Quotient.out (γ • q)) (a (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q))))) with
      hv
  have hfit : ∀ (k : ℕ) (q : Gamma0 N ⧸ heckeUpper N ℓ), f^[k] q = γ ^ k • q := fun k q => congr_fun
    (smul_iterate γ k) q
  have hfpos : ∀ q, 0 < minimalPeriod f q := by
    intro q
    have hn : 0 < orderOf (MulAction.toPermHom (Gamma0 N) (Gamma0 N ⧸ heckeUpper N ℓ) γ) :=
      orderOf_pos _
    refine IsPeriodicPt.minimalPeriod_pos hn ?_
    have h1 := pow_orderOf_eq_one (MulAction.toPermHom (Gamma0 N) (Gamma0 N ⧸ heckeUpper N ℓ) γ)
    rw [← map_pow] at h1
    have h2 := Equiv.congr_fun h1 q
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply] at h2
    change f^[_] q = q
    rw [hfit]
    exact h2
  have htr : ∀ (q : Gamma0 N ⧸ heckeUpper N ℓ) (m : ℕ), γ ^ m • q = q →
      (((heckeConj N ℓ (piProd γ q m) : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2
        = 4 := by
    intro q m hx
    rw [coe_heckeConj, coe_heckeConjSL, trace_heckeConjMat, coe_piProd, hx]
    have e : ((((Quotient.out q)⁻¹ * (γ ^ m * Quotient.out q) : Gamma0 N)) : SL(2, ℤ))
        = (((Quotient.out q : Gamma0 N) : SL(2, ℤ)))⁻¹ * ((γ : SL(2, ℤ)) ^ m)
            * ((((Quotient.out q : Gamma0 N) : SL(2, ℤ)))⁻¹)⁻¹ := by
      rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
        mul_assoc]
    rw [e, trace_conj, Matrix.SpecialLinearGroup.coe_pow]
    exact trace_sq_pow _ (Matrix.SpecialLinearGroup.det_coe _) hγ m
  have hsum : ∀ q, ∑ k ∈ Finset.range (minimalPeriod f q), v (f^[k] q) = 0 := by
    intro q
    have hx : γ ^ minimalPeriod f q • q = q := by rw [← hfit]; exact iterate_minimalPeriod
    have key := sum_range_eq (γ := γ) (x := q) ha hzc (minimalPeriod f q)
    simp only [S, LinearMap.comp_apply] at key
    simp only [hv, hfit]
    rw [← map_sum, key, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hP := P_mem_range (ρ := ρ) (a := a) ha hx (hzp _ (htr q _ hx))
    simpa only [S, LinearMap.comp_apply] using hP
  obtain ⟨G, hG⟩ := Function.exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero f hfpos v hsum
  have htot : ∑ q, v q = 0 := by
    rw [Finset.sum_congr rfl fun q _ => hG q, Finset.sum_sub_distrib, sub_eq_zero]
    exact (MulAction.bijective γ).sum_comp G
  rw [← Submodule.Quotient.mk_eq_zero R, ← Submodule.mkQ_apply, coeffHeckeFun_apply, map_sum]
  exact htot

end Main

end HeckeEis.ParabolicHeckeSol

end

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles.HeckeEis
  HeckeEis.ParabolicHeckeSol CongruenceSubgroup in
theorem solution (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffParabolicCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffParabolicCocycles ρ :=
  (mem_coeffParabolicCocycles_iff ρ _).mpr
    ⟨HeckeEis.coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha ((mem_coeffParabolicCocycles_iff ρ z).mp
      hz).1,
      isParabolicCocycle_coeffHeckeFun ha hz⟩

end S_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles
end P2MW
export P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles (solution)

end privateSection

public section publicSection


open scoped MatrixGroups

theorem HeckeEis.coeffHeckeFun_mem_coeffParabolicCocycles (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffParabolicCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffParabolicCocycles ρ :=
      _root_.P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles.solution N ℓ ρ a ha hz

end publicSection
