/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node HeckeEis.coeffHeckeFun_mem_coeffCocycles
(ef9163d8-d772-5478-b82b-14a7128aa783) by Claude (2026-09-05).

Proof based on Prove2Me submission ed472e60-a50b-5947-81a9-5baea7bf6ab1
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Gamma0CoeffCohomology

import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Cochain-level Hecke operator preserves 1-cocycles

Fix natural numbers $N$ and $\ell$ with $\ell \neq 0$, a commutative ring $K$, a $K$-module $V$, and
a representation $\rho$ of the congruence subgroup $\Gamma_0(N)$ on $V$ over $K$. Write $U =$
[`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128) for the subgroup of $\Gamma_0(N)$
consisting of those elements whose upper-right entry is divisible by $\ell$, and $c =$
[`HeckeEis.heckeConj N ℓ`](def/Gamma0HeckeOperatorHom.html#L172) for the group homomorphism $U \to
\Gamma_0(N)$ sending a matrix $\begin{pmatrix} \alpha & \beta \\ \gamma & \delta\end{pmatrix}$ in
$U$ to $\begin{pmatrix} \alpha & \beta/\ell \\ \gamma\ell & \delta\end{pmatrix}$. Let $a : V \to V$
be $K$-linear and assume the equivariance $a \circ \rho(c(u)) = \rho(u) \circ a$ for every $u \in
U$. Let $z : \Gamma_0(N) \to V$ satisfy the inhomogeneous $1$-cocycle identity $z(gh) = z(g) +
\rho(g)(z(h))$ for all $g, h \in \Gamma_0(N)$. The conclusion is that the function $g \mapsto
\sum_{q \in \Gamma_0(N)/U} \rho\bigl(\overline{g \cdot
q}\bigr)\bigl(a\bigl(z\bigl(c(\overline{g\cdot q}^{-1} g \overline{q})\bigr)\bigr)\bigr)$, the sum
being over the coset space $\Gamma_0(N)/U$ and $\overline{q}$ denoting the chosen representative of
a coset $q$, again satisfies the same $1$-cocycle identity.

This is the $1$-cocycle level construction of the double-coset Hecke operator $T_\ell$ (restriction
to $U$, twist by the conjugation $c$ and the intertwiner $a$, then corestriction back to
$\Gamma_0(N)$) on inhomogeneous cochains with coefficients in an arbitrary representation. It is the
cocycle half of the input needed to induce $T_\ell$ on $H^1$ and on parabolic cohomology, and is
cited by the companion statements about coboundaries, parabolic cocycles and the resulting
Hecke-equivariant maps on $H^1$.

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles.lean

Prove2Me submission: `ed472e60-a50b-5947-81a9-5baea7bf6ab1` (ACCEPTED).
-/

section privateSection

namespace P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCocycles

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
theorem mem_coeffCocycles {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    coeffHeckeFun N ℓ ρ a z ∈ coeffCocycles ρ := by
  let := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  intro g h
  simp only [coeffHeckeFun_apply]
  have key : ∀ q : Gamma0 N ⧸ U,
      ρ ((g * h) • q).out (a (z (c (transferAux U (g * h) q))))
        = ρ (g • (h • q)).out (a (z (c (transferAux U g (h • q)))))
          + ρ g (ρ (h • q).out (a (z (c (transferAux U h q))))) := by
    intro q
    rw [transferAux_mul, map_mul, hz, map_add, map_add, mul_smul]
    congr 1
    rw [ha_apply N ℓ ρ a ha, ← Module.End.mul_apply, ← map_mul, out_mul_transferAux, map_mul,
      Module.End.mul_apply]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, map_sum]
  congr 1
  exact Fintype.sum_bijective (h • ·) (MulAction.bijective h) _ _ fun q => rfl

end Sh2
end HeckeEis

theorem solution (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCocycles ρ :=
  HeckeEis.Sh2.mem_coeffCocycles N ℓ ρ a ha hz

end S_HeckeEis_coeffHeckeFun_mem_coeffCocycles
end P2MW
export P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCocycles (solution)

end privateSection

public section publicSection

open scoped MatrixGroups

theorem HeckeEis.coeffHeckeFun_mem_coeffCocycles (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCocycles ρ :=
      _root_.P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCocycles.solution N ℓ ρ a ha hz

end publicSection
