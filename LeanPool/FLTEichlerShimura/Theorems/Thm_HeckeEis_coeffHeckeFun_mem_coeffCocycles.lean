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

public import LeanPool.FLTEichlerShimura.Definitions.Def_Gamma0HeckeOperatorHom
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

theorem cocycle_one {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem cocycle_map_inv {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) (x : ↥U) :
    z (c x⁻¹) = -(ρ (c x⁻¹) (z (c x))) := by
  have h1 : z (c x⁻¹ * c x) = z (c x⁻¹) + ρ (c x⁻¹) (z (c x)) := hz _ _
  rw [← map_mul, inv_mul_cancel, map_one, cocycle_one N ρ hz] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

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

include ha in
theorem sum_repr_sub_mem_coeffCoboundaries
    (s : Gamma0 N ⧸ U → Gamma0 N) (t : Gamma0 N → Gamma0 N ⧸ U → ↥U)
    (hs : ∀ q, (s q : Gamma0 N ⧸ U) = q)
    (hst : ∀ g q, s (g • q) * (t g q : Gamma0 N) = g * s q)
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    (fun g => let := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
        ∑ q : Gamma0 N ⧸ U, ρ (s (g • q)) (a (z (c (t g q)))))
      - coeffHeckeFun N ℓ ρ a z ∈ coeffCoboundaries ρ := by
  let := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  have hu_mem : ∀ q : Gamma0 N ⧸ U, (q.out)⁻¹ * s q ∈ U := fun q =>
    QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans (hs q).symm)
  have hex : ∀ q : Gamma0 N ⧸ U, ∃ uq : ↥U, s q = q.out * (uq : Gamma0 N) := fun q =>
    ⟨⟨_, hu_mem q⟩, by rw [Subgroup.coe_mk, mul_inv_cancel_left]⟩
  choose u hsq using hex
  have ht : ∀ g q, t g q = (u (g • q))⁻¹ * transferAux U g q * u q := by
    intro g q
    apply Subtype.ext
    have h1 := hst g q
    rw [hsq, hsq] at h1
    push_cast [coe_transferAux]
    calc ((t g q : ↥U) : Gamma0 N)
        = ((g • q).out * ↑(u (g • q)))⁻¹ * (((g • q).out * ↑(u (g • q))) * ↑(t g q)) := by group
      _ = ((g • q).out * ↑(u (g • q)))⁻¹ * (g * (q.out * ↑(u q))) := by rw [h1]
      _ = (↑(u (g • q)))⁻¹ * ((g • q).out⁻¹ * (g * q.out)) * ↑(u q) := by group
  set F : V := ∑ q : Gamma0 N ⧸ U, ρ q.out (a (z (c (u q)))) with hF
  refine ⟨F, ?_⟩
  funext g
  simp only [coeffCoboundaryMap_apply, Pi.sub_apply, coeffHeckeFun_apply]
  have key : ∀ q : Gamma0 N ⧸ U,
      ρ (s (g • q)) (a (z (c (t g q))))
        = -(ρ (g • q).out (a (z (c (u (g • q))))))
          + ρ (g • q).out (a (z (c (transferAux U g q))))
          + ρ g (ρ q.out (a (z (c (u q))))) := by
    intro q
    rw [hsq (g • q), ht g q, map_mul c, map_mul c,
      hz (c (u (g • q))⁻¹ * c (transferAux U g q)) (c (u q)),
      hz (c (u (g • q))⁻¹) (c (transferAux U g q)),
      cocycle_map_inv N ℓ ρ hz (u (g • q)), ← map_mul c]
    simp only [map_add, map_neg, ha_apply N ℓ ρ a ha]
    have e12 : ∀ v : V, ρ ((g • q).out * ((u (g • q) : ↥U) : Gamma0 N)) (ρ (((u (g • q))⁻¹ : ↥U) :
      Gamma0 N) v)
        = ρ (g • q).out v := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel_right]
    have e3 : ∀ v : V, ρ ((g • q).out * ((u (g • q) : ↥U) : Gamma0 N))
        (ρ (((u (g • q))⁻¹ * transferAux U g q : ↥U) : Gamma0 N) v) = ρ g (ρ q.out v) := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← out_mul_transferAux N ℓ g q]
      group
    rw [e12, e12, e3]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← map_sum]
  have hre : ∑ q : Gamma0 N ⧸ U, ρ (g • q).out (a (z (c (u (g • q))))) = F :=
    Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => rfl
  rw [hre]
  abel

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
