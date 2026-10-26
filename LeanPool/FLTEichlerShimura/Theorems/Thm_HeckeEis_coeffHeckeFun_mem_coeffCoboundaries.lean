/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node HeckeEis.coeffHeckeFun_mem_coeffCoboundaries
(7e920852-4d0d-5756-925e-21e268c92631) by Claude (2026-09-05).

Proof based on Prove2Me submission ef4c7cb3-2936-51c4-953d-94be9ec44797
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Gamma0CoeffCohomology

import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Cochain Hecke operator preserves coefficient coboundaries

Let $N,\ell$ be natural numbers with $\ell\neq 0$, let $K$ be a commutative ring, $V$ a $K$-module,
and let $\rho$ be a $K$-linear representation of $\Gamma_0(N)$ on $V$. Write $U=$
[`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128) for the subgroup of $\Gamma_0(N)$
consisting of those matrices $g$ with $\ell \mid g_{01}$, and let [`HeckeEis.heckeConj N
ℓ`](def/Gamma0HeckeOperatorHom.html#L172) be the group homomorphism $U\to\Gamma_0(N)$ sending
$g=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ to $\begin{pmatrix}a&b/\ell\\ c\ell&d\end{pmatrix}$, i.e.
conjugation by $\mathrm{diag}(1,\ell)$. Let $a\colon V\to V$ be $K$-linear and assume
$a\circ\rho(\mathrm{heckeConj}(u))=\rho(u)\circ a$ for every $u\in U$. Let $z\colon\Gamma_0(N)\to V$
lie in [`HeckeEis.coeffCoboundaries ρ`](def/Gamma0CoeffCohomology.html#L45), the image of the linear
map $v\mapsto (g\mapsto \rho(g)v-v)$; that is, $z(g)=\rho(g)v-v$ for some $v\in V$. The conclusion
is that the function
$$g\longmapsto \sum_{q\in\Gamma_0(N)/U}\rho\bigl(\overline{g\cdot
q}\bigr)\,a\bigl(z\bigl(\mathrm{heckeConj}(\overline{g\cdot q}^{-1}\,g\,\overline q)\bigr)\bigr),$$
where $\overline{\,\cdot\,}$ denotes the chosen representative of a coset and the finite sum is over
the (finite-index) quotient $\Gamma_0(N)/U$, again lies in [`HeckeEis.coeffCoboundaries
ρ`](def/Gamma0CoeffCohomology.html#L45).

This is the statement that the cochain-level Hecke operator $T_\ell$ on $V$-valued functions on
$\Gamma_0(N)$, built from a double-coset decomposition together with an intertwining endomorphism
$a$ of the coefficient module, carries $1$-coboundaries to $1$-coboundaries. Together with the
companion statement for cocycles it allows $T_\ell$ to be defined on $H^1(\Gamma_0(N),\rho)$, and it
is used by the subsequent results on Hecke-equivariant maps to and from coefficient cohomology.

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries.lean

Prove2Me submission: `ef4c7cb3-2936-51c4-953d-94be9ec44797` (ACCEPTED).
-/

section privateSection

namespace P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries

open scoped MatrixGroups

namespace HeckeEis
p2m_export "HeckeEis"
  "heckeUpper heckeConj transferAux coe_transferAux transferAux_mul coeffCocycles \
    coeffCoboundaryMap_apply coeffCoboundaries coeffHeckeFun coeffHeckeFun_apply"
p2m_open "HeckeEis"
namespace Sh2
open CongruenceSubgroup
open scoped MatrixGroups

variable (N ℓ : ℕ) [NeZero ℓ]
  {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
  (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)

local notation "U" => heckeUpper N ℓ
local notation "c" => heckeConj N ℓ

include ha in
theorem ha_apply (u : ↥U) (v : V) : a (ρ (c u) v) = ρ (u : Gamma0 N) (a v) := by
  have := LinearMap.congr_fun (ha u) v
  simpa using this

omit [NeZero ℓ] in
theorem out_mul_transferAux (g : Gamma0 N) (q : Gamma0 N ⧸ U) :
    (g • q).out * (transferAux U g q : Gamma0 N) = g * q.out := by
  rw [coe_transferAux, mul_inv_cancel_left]

include ha in
theorem mem_coeffCoboundaries {z : Gamma0 N → V} (hz : z ∈ coeffCoboundaries ρ) :
    coeffHeckeFun N ℓ ρ a z ∈ coeffCoboundaries ρ := by
  let := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  obtain ⟨v, rfl⟩ := hz
  refine ⟨∑ q : Gamma0 N ⧸ U, ρ q.out (a v), ?_⟩
  funext g
  simp only [coeffCoboundaryMap_apply, coeffHeckeFun_apply, map_sub, map_sum,
    Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ha_apply N ℓ ρ a ha]
    rw [← Module.End.mul_apply (ρ (g • q).out) (ρ _), ← map_mul, out_mul_transferAux, map_mul,
      Module.End.mul_apply]
  · exact (Fintype.sum_bijective (g • ·) (MulAction.bijective g)
      (fun q : Gamma0 N ⧸ U => ρ (g • q).out (a v)) (fun q : Gamma0 N ⧸ U => ρ q.out (a v)) fun q =>
        rfl).symm

end Sh2
end HeckeEis

theorem solution (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCoboundaries ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCoboundaries ρ :=
  HeckeEis.Sh2.mem_coeffCoboundaries N ℓ ρ a ha hz

end S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
end P2MW
export P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries (solution)

end privateSection

public section publicSection

open scoped MatrixGroups

theorem HeckeEis.coeffHeckeFun_mem_coeffCoboundaries (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCoboundaries ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCoboundaries ρ :=
      _root_.P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries.solution N ℓ ρ a ha hz

end publicSection
