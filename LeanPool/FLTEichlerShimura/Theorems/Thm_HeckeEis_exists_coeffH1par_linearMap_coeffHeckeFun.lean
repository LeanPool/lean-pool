/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun
(5687e012-801a-55f3-80ae-d7d0dbe45568) by Claude (2026-09-05).

Proof based on Prove2Me submission 424062d0-1ce2-5345-9953-29cf4d1db00e
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Gamma0CoeffCohomology

import LeanPool.FLTEichlerShimura.Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import LeanPool.FLTEichlerShimura.Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Existence of the induced Hecke endomorphism of H¹ₚₐᵣ

Fix natural numbers $N$ and $\ell$ with $\ell \neq 0$, a commutative ring $K$, a $K$-module $V$, a
representation $\rho$ of the group $\Gamma_0(N)$ on $V$ over $K$, and a $K$-linear endomorphism $a$
of $V$. Assume the intertwining hypothesis: for every $u$ in [`HeckeEis.heckeUpper N
ℓ`](def/Gamma0HeckeOperatorHom.html#L128), the subgroup of those elements of $\Gamma_0(N)$ whose
upper right entry is divisible by $\ell$, one has $a \circ \rho(\mathrm{heckeConj}(u)) = \rho(u)
\circ a$, where $\mathrm{heckeConj}(u)$ is the matrix obtained from $u = \begin{pmatrix} \alpha &
\beta \\ \gamma & \delta\end{pmatrix}$ as $\begin{pmatrix} \alpha & \beta/\ell \\ \gamma\ell &
\delta\end{pmatrix}$ (conjugation by $\mathrm{diag}(1,\ell)$), viewed again in $\Gamma_0(N)$. The
conclusion asserts the existence of a $K$-linear endomorphism $T$ of [`HeckeEis.coeffH1par
ρ`](def/Gamma0CoeffCohomology.html#L100) — the quotient of the submodule of parabolic cocycles
(functions $z : \Gamma_0(N) \to V$ with $z(gh) = z(g) + \rho(g)z(h)$ and $z(\gamma) \in
\mathrm{im}(\rho(\gamma) - 1)$ whenever the integral matrix $\gamma$ has $\mathrm{tr}(\gamma)^2 =
4$) by the parabolic cocycles that are coboundaries — such that for every parabolic cocycle $z$
there is a parabolic cocycle $w$ whose underlying function $\Gamma_0(N) \to V$ equals
[`HeckeEis.coeffHeckeFun N ℓ ρ a z`](def/Gamma0CoeffCohomology.html#L129), the finite sum over $q
\in \Gamma_0(N)/\mathrm{heckeUpper}(N,\ell)$ of $\rho((g\cdot
q)^{\mathrm{out}})\bigl(a\,z(\mathrm{heckeConj}(\mathrm{transferAux}(g,q)))\bigr)$, and such that
$T$ sends the class of $z$ to the class of $w$. Thus the statement simultaneously records that the
cochain-level operator preserves parabolic cocycles and that it descends to the quotient.

This is the construction of the Hecke operator $T_\ell$ on the parabolic cohomology
$H^1_{\mathrm{par}}(\Gamma_0(N), \rho)$ from its cochain-level avatar, in the classical
Eichler–Shimura setting where the coefficient datum is a linear map $a$ intertwining $\rho$ with its
conjugate by $\mathrm{diag}(1,\ell)$. It is used in the construction of Hecke eigenclasses in
parabolic cohomology of binary-form representations and, through those, in the integral-structure
statement for cusp forms.

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.lean

Prove2Me submission: `424062d0-1ce2-5345-9953-29cf4d1db00e` (ACCEPTED).
-/

section privateSection


namespace P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis"
  "heckeUpper heckeConj coeffCoboundaries coeffParabolicCocycles coeffH1par coeffH1parMk \
    coeffHeckeFun coeffHeckeFun_apply coeffHeckeFun_mem_coeffCoboundaries \
    coeffHeckeFun_mem_coeffParabolicCocycles"
namespace InducedHeckeSol
p2m_open "HeckeEis"

open CongruenceSubgroup
open scoped MatrixGroups

variable (N ℓ : ℕ) [NeZero ℓ] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def coeffHeckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    funext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

@[scoped simp] theorem coeffHeckeLin_apply (z : Gamma0 N → V) : coeffHeckeLin N ℓ ρ a z =
  coeffHeckeFun N ℓ ρ a z := rfl

variable {ρ a}

def parabolicHecke (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ
  a) :
    ↥(coeffParabolicCocycles ρ) →ₗ[K] ↥(coeffParabolicCocycles ρ) :=
  (coeffHeckeLin N ℓ ρ a).restrict fun _ hz => HeckeEis.coeffHeckeFun_mem_coeffParabolicCocycles N ℓ
    ρ a ha hz

theorem coe_parabolicHecke (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0
  N) ∘ₗ a)
    (z : ↥(coeffParabolicCocycles ρ)) :
    ((parabolicHecke N ℓ ha z : ↥(coeffParabolicCocycles ρ)) : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a
      z := rfl

def heckeH1par (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a) :
    coeffH1par ρ →ₗ[K] coeffH1par ρ :=
  Submodule.mapQ ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype)
    ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype) (parabolicHecke N ℓ ha)
    (fun z hz => by
      change ((parabolicHecke N ℓ ha z : ↥(coeffParabolicCocycles ρ)) : Gamma0 N → V) ∈
        coeffCoboundaries ρ
      rw [coe_parabolicHecke]
      exact HeckeEis.coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz)

theorem heckeH1par_mk (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ
  a)
    (z : ↥(coeffParabolicCocycles ρ)) :
    heckeH1par N ℓ ha (coeffH1parMk ρ z) = coeffH1parMk ρ (parabolicHecke N ℓ ha z) :=
  rfl

end HeckeEis.InducedHeckeSol

end

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.HeckeEis
  HeckeEis.InducedHeckeSol CongruenceSubgroup in
theorem solution (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a) :
    ∃ T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ,
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
        (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
          T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w :=
  ⟨heckeH1par N ℓ ha, fun z => ⟨parabolicHecke N ℓ ha z, rfl, heckeH1par_mk N ℓ ha z⟩⟩

end S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun
end P2MW
export P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun (solution)

end privateSection

public section publicSection


open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a) :
    ∃ T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ,
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
        (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
          T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w :=
            _root_.P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.solution N ℓ ρ a ha

end publicSection
