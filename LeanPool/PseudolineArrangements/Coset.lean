/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.Cartographic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Coset flag systems and orientability

Every subgroup `H` of the cartographic group gives a flag system on the cosets
`cartographicGroup n ⧸ H` (`GMap.cosetGMap`). Every nonempty connected flag system is isomorphic
to one of them, namely to the coset flag system of the stabilizer of a flag
(`GMap.exists_iso_cosetGMap`), and two coset flag systems are isomorphic exactly when the
subgroups are conjugate (`GMap.nonempty_iso_cosetGMap_iff`). This is the classification of
transitive actions of the cartographic group by conjugacy classes of stabilizers.

The even part of the monodromy group is the image of the kernel of the length parity of the
cartographic group. A connected flag system without fixed darts is orientable exactly when the
even part is not transitive on flags (`GMap.isOrientable_iff_not_isPretransitive_evenMonodromy`).

## References

* S. Wilson, *Maniplexes: Part 1: maps, polytopes, symmetry and operators*, Symmetry 4 (2012),
  265–275, §5, p. 270.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv

namespace GMap

variable {n : ℕ} {D D' : Type*} (G : GMap n D)

/-! ### Coset flag systems -/

/-- The coset flag system of `H ≤ cartographicGroup n` on `cartographicGroup n ⧸ H`. -/
noncomputable def cosetGMap (H : Subgroup (cartographicGroup n)) :
    GMap n (cartographicGroup n ⧸ H) :=
  ofMonodromyHom (MulAction.toPermHom (cartographicGroup n) (cartographicGroup n ⧸ H))

theorem monodromyHom_cosetGMap (H : Subgroup (cartographicGroup n)) (w : cartographicGroup n)
    (q : cartographicGroup n ⧸ H) : (cosetGMap H).monodromyHom w q = w • q := by
  rw [cosetGMap, monodromyHom_ofMonodromyHom]
  rfl

theorem cosetGMap_adj (H : Subgroup (cartographicGroup n)) (i : Fin (n + 1))
    (q : cartographicGroup n ⧸ H) :
    (cosetGMap H).adj i q = (cartographicMatrix n).simple i • q := rfl

/-- The stabilizer of a flag in the cartographic group, acting through the monodromy
homomorphism. -/
noncomputable def stabilizer (d : D) : Subgroup (cartographicGroup n) :=
  (MulAction.stabilizer (Perm D) d).comap G.monodromyHom

theorem mem_stabilizer_iff {d : D} {w : cartographicGroup n} :
    w ∈ G.stabilizer d ↔ G.monodromyHom w d = d := Iff.rfl

/-- The orbit map of a flag, from the cosets of its stabilizer. -/
noncomputable def orbitMap (d : D) : cartographicGroup n ⧸ G.stabilizer d → D :=
  Quotient.lift (fun w => G.monodromyHom w d) fun a b hab => by
    have h : a⁻¹ * b ∈ G.stabilizer d := QuotientGroup.leftRel_apply.1 hab
    rw [mem_stabilizer_iff, map_mul, Perm.mul_apply, map_inv] at h
    change G.monodromyHom a d = G.monodromyHom b d
    calc G.monodromyHom a d = G.monodromyHom a ((G.monodromyHom a)⁻¹ (G.monodromyHom b d)) := by
          rw [h]
      _ = G.monodromyHom b d := perm_apply_inv_self _ _

theorem orbitMap_mk (d : D) (w : cartographicGroup n) :
    G.orbitMap d (w : cartographicGroup n ⧸ G.stabilizer d) = G.monodromyHom w d := rfl

theorem orbitMap_injective (d : D) : Function.Injective (G.orbitMap d) := by
  intro q q'
  induction q using QuotientGroup.induction_on
  induction q' using QuotientGroup.induction_on
  rename_i a b
  intro h
  rw [orbitMap_mk, orbitMap_mk] at h
  refine QuotientGroup.eq.2 ?_
  rw [mem_stabilizer_iff, map_mul, Perm.mul_apply, ← h, map_inv]
  simp

theorem orbitMap_surjective (hG : G.IsConnected) (d : D) : Function.Surjective (G.orbitMap d) :=
  fun e => by
    obtain ⟨w, hw⟩ := (G.isConnected_iff_exists_monodromyHom).1 hG d e
    exact ⟨w, hw⟩

theorem orbitMap_adj (d : D) (i : Fin (n + 1)) (q : cartographicGroup n ⧸ G.stabilizer d) :
    G.orbitMap d ((cosetGMap (G.stabilizer d)).adj i q) = G.adj i (G.orbitMap d q) := by
  induction q using QuotientGroup.induction_on
  rw [cosetGMap_adj, MulAction.Quotient.smul_coe, smul_eq_mul, orbitMap_mk, orbitMap_mk,
    map_mul, Perm.mul_apply, monodromyHom_simple]

/-- A connected flag system is isomorphic to the coset flag system of the stabilizer of any of
its flags. -/
noncomputable def isoCosetGMap (hG : G.IsConnected) (d : D) :
    G.Iso (cosetGMap (G.stabilizer d)) where
  toEquiv := (Equiv.ofBijective _ ⟨G.orbitMap_injective d, G.orbitMap_surjective hG d⟩).symm
  map_adj i e := by
    set F := Equiv.ofBijective _ ⟨G.orbitMap_injective d, G.orbitMap_surjective hG d⟩
    apply F.injective
    rw [F.apply_symm_apply]
    change _ = G.orbitMap d _
    rw [orbitMap_adj]
    exact congrArg _ (F.apply_symm_apply e).symm

/-- Every nonempty connected flag system is isomorphic to a coset flag system. -/
theorem exists_iso_cosetGMap [Nonempty D] (hG : G.IsConnected) :
    ∃ H : Subgroup (cartographicGroup n), Nonempty (G.Iso (cosetGMap H)) :=
  ⟨_, ⟨G.isoCosetGMap hG (Classical.arbitrary D)⟩⟩

/-- An isomorphism of coset flag systems commutes with the action of the cartographic group. -/
theorem Iso.map_smul_cosetGMap {H K : Subgroup (cartographicGroup n)}
    (f : (cosetGMap H).Iso (cosetGMap K)) (w : cartographicGroup n)
    (q : cartographicGroup n ⧸ H) : f.toEquiv (w • q) = w • f.toEquiv q := by
  rw [← monodromyHom_cosetGMap, ← monodromyHom_cosetGMap]
  exact (cosetGMap H).map_monodromyHom f.map_adj w q

/-- The map `x H ↦ x g⁻¹ K` between coset spaces, when `g H g⁻¹ ≤ K`. -/
noncomputable def cosetMap {H K : Subgroup (cartographicGroup n)} (g : cartographicGroup n)
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ K) : cartographicGroup n ⧸ H → cartographicGroup n ⧸ K :=
  Quotient.map' (fun x => x * g⁻¹) fun a b hab => by
    have := QuotientGroup.leftRel_apply.1 hab
    refine QuotientGroup.leftRel_apply.2 ?_
    have h' := h _ this
    simpa [mul_assoc] using h'

theorem cosetMap_mk {H K : Subgroup (cartographicGroup n)} (g : cartographicGroup n)
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ K) (x : cartographicGroup n) :
    cosetMap g h (x : cartographicGroup n ⧸ H) = ((x * g⁻¹ : cartographicGroup n) : _ ⧸ K) := rfl

theorem smul_coe_eq_self_iff {S : Subgroup (cartographicGroup n)} (w x : cartographicGroup n) :
    w • (x : cartographicGroup n ⧸ S) = x ↔ x⁻¹ * w * x ∈ S := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, eq_comm, QuotientGroup.eq, ← mul_assoc]

open scoped Pointwise in
/-- Two coset flag systems are isomorphic iff the subgroups are conjugate. -/
theorem nonempty_iso_cosetGMap_iff (H K : Subgroup (cartographicGroup n)) :
    Nonempty ((cosetGMap H).Iso (cosetGMap K)) ↔
      ∃ g : cartographicGroup n, K = MulAut.conj g • H := by
  have hmem : ∀ (g : cartographicGroup n) (x : cartographicGroup n),
      x ∈ MulAut.conj g • H ↔ g⁻¹ * x * g ∈ H := fun g x => by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨f⟩
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective
      (f.toEquiv ((1 : cartographicGroup n) : cartographicGroup n ⧸ H))
    have key : ∀ w : cartographicGroup n, g₀⁻¹ * w * g₀ ∈ K ↔ w ∈ H := by
      intro w
      rw [← smul_coe_eq_self_iff, hg₀, ← Iso.map_smul_cosetGMap, f.toEquiv.apply_eq_iff_eq,
        smul_coe_eq_self_iff, inv_one, one_mul, mul_one]
    refine ⟨g₀⁻¹, ?_⟩
    ext k
    rw [hmem, inv_inv, ← key]
    simp [mul_assoc]
  · rintro ⟨g, rfl⟩
    have h₁ : ∀ x ∈ H, g * x * g⁻¹ ∈ MulAut.conj g • H := fun x hx => by
      rw [hmem]; simpa [mul_assoc] using hx
    have h₂ : ∀ y ∈ MulAut.conj g • H, g⁻¹ * y * g⁻¹⁻¹ ∈ H := fun y hy => by
      rw [inv_inv]; exact (hmem g y).1 hy
    refine ⟨⟨⟨cosetMap g h₁, cosetMap g⁻¹ h₂, fun q => ?_, fun q => ?_⟩, fun i q => ?_⟩⟩
    · induction q using QuotientGroup.induction_on
      simp [cosetMap_mk]
    · induction q using QuotientGroup.induction_on
      simp [cosetMap_mk]
    · induction q using QuotientGroup.induction_on
      simp only [Equiv.coe_fn_mk, cosetGMap_adj, MulAction.Quotient.smul_coe, smul_eq_mul,
        cosetMap_mk, mul_assoc]

end GMap

end LeanPool.PseudolineArrangements
