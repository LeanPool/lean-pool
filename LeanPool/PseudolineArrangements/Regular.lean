/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.Coset

/-!
# Regular flag systems

A connected flag system is regular when its monodromy group acts freely on flags
(`GMap.IsRegular`). For a connected flag system this happens exactly when the automorphism group
acts transitively (`GMap.isRegular_iff_isPretransitive_aut`), and, for a finite nonempty one,
exactly when it has as many automorphisms as flags (`GMap.isRegular_iff_natCard_aut`). A nonempty
regular flag system is the coset flag system of a normal subgroup of the cartographic group
(`GMap.exists_normal_iso_cosetGMap`), whose automorphism group is the opposite of the quotient
group (`GMap.nonempty_mulEquiv_aut_cosetGMap`).

Conversely, a family `ρ` of involutions of a group `W` satisfying the relations of the
cartographic group gives a flag system on `W` by left multiplication (`GMap.ofGroup`); it is
connected exactly when the `ρ i` generate `W` (`GMap.isConnected_ofGroup_iff`), and it is then
regular with automorphism group `Wᵐᵒᵖ`, acting by right multiplication
(`GMap.isRegular_ofGroup`). Every nonempty regular flag system is the flag system of its own
monodromy group (`GMap.nonempty_iso_ofMonodromy`).

## References

* S. Wilson, *Maniplexes: Part 1: maps, polytopes, symmetry and operators*, Symmetry 4 (2012),
  265–275, §7, p. 272.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv

namespace GMap

variable {n : ℕ} {D : Type*} (G : GMap n D)

/-- Regular: connected, with a monodromy group acting freely. -/
def IsRegular : Prop := G.IsConnected ∧ ∀ g ∈ G.monodromy, ∀ d, g d = d → g = 1

theorem aut_eq_centralizer_monodromy : G.aut = Subgroup.centralizer G.monodromy := by
  rw [aut, monodromy, Subgroup.centralizer_closure]

theorem commute_of_mem_aut {σ g : Perm D} (hσ : σ ∈ G.aut) (hg : g ∈ G.monodromy) (d : D) :
    σ (g d) = g (σ d) := by
  rw [aut_eq_centralizer_monodromy, Subgroup.mem_centralizer_iff] at hσ
  exact (congrArg (fun τ : Perm D => τ d) (hσ g hg)).symm

variable {G}

theorem IsRegular.monodromyHom_eq (hG : G.IsRegular) {w w' : cartographicGroup n} {d : D}
    (h : G.monodromyHom w d = G.monodromyHom w' d) : G.monodromyHom w = G.monodromyHom w' := by
  have hmem : (G.monodromyHom w')⁻¹ * G.monodromyHom w ∈ G.monodromy :=
    G.monodromy.mul_mem (G.monodromy.inv_mem (G.monodromyHom_mem_monodromy w'))
      (G.monodromyHom_mem_monodromy w)
  have := hG.2 _ hmem d (by rw [Perm.mul_apply, h, perm_inv_apply_self])
  exact inv_mul_eq_one.1 this |>.symm

/-- In a regular flag system, any flag can be moved to any other by an automorphism. -/
theorem IsRegular.exists_mem_aut (hG : G.IsRegular) (d e : D) : ∃ σ ∈ G.aut, σ d = e := by
  have hconn := (G.isConnected_iff_exists_monodromyHom).1 hG.1
  choose w hw using hconn d
  choose w' hw' using hconn e
  have key : ∀ x v, G.monodromyHom v d = x → G.monodromyHom (w x) e = G.monodromyHom v e :=
    fun x v hv => by rw [hG.monodromyHom_eq ((hw x).trans hv.symm)]
  have key' : ∀ y v, G.monodromyHom v e = y → G.monodromyHom (w' y) d = G.monodromyHom v d :=
    fun y v hv => by rw [hG.monodromyHom_eq ((hw' y).trans hv.symm)]
  let σ : Perm D :=
    { toFun := fun x => G.monodromyHom (w x) e
      invFun := fun y => G.monodromyHom (w' y) d
      left_inv := fun x => show G.monodromyHom (w' (G.monodromyHom (w x) e)) d = x by
        rw [key' _ (w x) rfl, hw]
      right_inv := fun y => show G.monodromyHom (w (G.monodromyHom (w' y) d)) e = y by
        rw [key _ (w' y) rfl, hw'] }
  refine ⟨σ, (G.mem_aut_iff).2 fun i x => ?_, ?_⟩
  · change G.monodromyHom (w _) e = G.adj i (G.monodromyHom (w x) e)
    rw [key _ ((cartographicMatrix n).simple i * w x)
      (by rw [map_mul, Perm.mul_apply, monodromyHom_simple, hw]), map_mul, Perm.mul_apply,
      monodromyHom_simple]
  · change G.monodromyHom (w d) e = e
    rw [key d 1 (by simp)]
    simp

variable (G)

/-- For a connected flag system, regular iff the automorphism group acts transitively. -/
theorem isRegular_iff_isPretransitive_aut (hG : G.IsConnected) :
    G.IsRegular ↔ MulAction.IsPretransitive G.aut D := by
  constructor
  · intro h
    refine ⟨fun d e => ?_⟩
    obtain ⟨σ, hσ, he⟩ := h.exists_mem_aut d e
    exact ⟨⟨σ, hσ⟩, he⟩
  · intro h
    refine ⟨hG, fun g hg d hd => Equiv.ext fun e => ?_⟩
    obtain ⟨τ, rfl⟩ := h.exists_smul_eq d e
    change g ((τ : Perm D) d) = (τ : Perm D) d
    rw [← G.commute_of_mem_aut τ.2 hg, hd]

/-- For a finite nonempty connected flag system, regular iff it has `Nat.card D`
automorphisms. -/
theorem isRegular_iff_natCard_aut [Finite D] [Nonempty D] (hG : G.IsConnected) :
    G.IsRegular ↔ Nat.card G.aut = Nat.card D := by
  obtain ⟨d₀⟩ := ‹Nonempty D›
  set f : G.aut → D := fun σ => (σ : Perm D) d₀
  have hf : Function.Injective f := fun σ τ h =>
    Subtype.ext (G.eq_of_mem_aut_of_apply_eq hG σ.2 τ.2 d₀ h)
  rw [isRegular_iff_isPretransitive_aut G hG]
  constructor
  · intro h
    refine Nat.card_eq_of_bijective f ⟨hf, fun e => ?_⟩
    exact h.exists_smul_eq d₀ e
  · intro h
    have hs := (hf.bijective_of_nat_card_le h.ge).2
    refine ⟨fun d e => ?_⟩
    obtain ⟨σ, rfl⟩ := hs d
    obtain ⟨τ, rfl⟩ := hs e
    refine ⟨τ * σ⁻¹, ?_⟩
    change (τ : Perm D) ((σ : Perm D)⁻¹ ((σ : Perm D) d₀)) = (τ : Perm D) d₀
    rw [perm_inv_apply_self]

variable {G} in
/-- In a regular flag system the stabilizer of a flag is the kernel of the monodromy
homomorphism. -/
theorem IsRegular.stabilizer_eq_ker (hG : G.IsRegular) (d : D) :
    G.stabilizer d = G.monodromyHom.ker := by
  ext w
  rw [mem_stabilizer_iff, MonoidHom.mem_ker]
  constructor
  · exact fun h => hG.2 _ (G.monodromyHom_mem_monodromy w) d h
  · intro h; rw [h]; rfl

/-- A nonempty regular flag system is isomorphic to the coset flag system of a normal
subgroup. -/
theorem exists_normal_iso_cosetGMap [Nonempty D] (hG : G.IsRegular) :
    ∃ N : Subgroup (cartographicGroup n), N.Normal ∧ Nonempty (G.Iso (cosetGMap N)) := by
  obtain ⟨d₀⟩ := ‹Nonempty D›
  refine ⟨G.stabilizer d₀, ?_, ⟨G.isoCosetGMap hG.1 d₀⟩⟩
  rw [hG.stabilizer_eq_ker d₀]
  infer_instance

/-! ### The regular flag system of a group -/

/-- The regular flag system of `ρ : Fin (n + 1) → W` satisfying the relations of the cartographic
group: flags `W`, `adj i g = ρ i * g`. -/
def ofGroup {W : Type*} [Group W] (ρ : Fin (n + 1) → W) (hρ : ∀ i, ρ i * ρ i = 1)
    (hfar : ∀ i j : Fin (n + 1), (i : ℕ) + 2 ≤ j → Commute (ρ i) (ρ j)) : GMap n W where
  adj i := Equiv.mulLeft (ρ i)
  involutive i g := by simp [← mul_assoc, hρ i]
  commute_of_far i j h := by
    unfold Commute SemiconjBy
    refine Equiv.ext fun g => ?_
    simp [Perm.mul_apply, ← mul_assoc, (hfar i j h).eq]

section OfGroup

variable {W : Type*} [Group W] (ρ : Fin (n + 1) → W) (hρ : ∀ i, ρ i * ρ i = 1)
  (hfar : ∀ i j : Fin (n + 1), (i : ℕ) + 2 ≤ j → Commute (ρ i) (ρ j))

theorem ofGroup_adj (i : Fin (n + 1)) (g : W) : (ofGroup ρ hρ hfar).adj i g = ρ i * g := rfl

theorem monodromy_ofGroup :
    (ofGroup ρ hρ hfar).monodromy = (Subgroup.closure (Set.range ρ)).map
      (MulAction.toPermHom W W) := by
  rw [MonoidHom.map_closure, ← Set.range_comp, monodromy]
  rfl

/-- The regular flag system of `ρ` is connected iff the `ρ i` generate `W`. -/
theorem isConnected_ofGroup_iff :
    (ofGroup ρ hρ hfar).IsConnected ↔ Subgroup.closure (Set.range ρ) = ⊤ := by
  rw [isConnected_iff_forall_exists, monodromy_ofGroup]
  constructor
  · intro h
    refine (Subgroup.eq_top_iff' _).2 fun w => ?_
    obtain ⟨_, ⟨u, hu, rfl⟩, huw⟩ := h 1 w
    change u * 1 = w at huw
    rw [mul_one] at huw
    exact huw ▸ hu
  · intro h d e
    refine ⟨_, ⟨e * d⁻¹, h ▸ Subgroup.mem_top _, rfl⟩, ?_⟩
    change e * d⁻¹ * d = e
    simp

/-- Right multiplication, as a homomorphism `Wᵐᵒᵖ →* Perm W`. -/
def rightMulHom : Wᵐᵒᵖ →* Perm W := MulAction.toPermHom Wᵐᵒᵖ W

theorem rightMulHom_apply (g : Wᵐᵒᵖ) (x : W) : rightMulHom g x = x * g.unop := rfl

theorem rightMulHom_injective : Function.Injective (rightMulHom (W := W)) := by
  intro a b h
  have := congrArg (fun σ : Perm W => σ 1) h
  simpa [rightMulHom_apply] using this

/-- When the `ρ i` generate `W`, the automorphisms of the flag system of `ρ` are the right
multiplications. -/
theorem range_rightMulHom (hgen : Subgroup.closure (Set.range ρ) = ⊤) :
    (rightMulHom (W := W)).range = (ofGroup ρ hρ hfar).aut := by
  ext σ
  rw [MonoidHom.mem_range, mem_aut_iff]
  constructor
  · rintro ⟨g, rfl⟩ i x
    simp [rightMulHom_apply, ofGroup_adj, mul_assoc]
  · intro h
    have hall : ∀ w : W, ∀ x, σ (w * x) = w * σ x := by
      intro w
      have hw : w ∈ Subgroup.closure (Set.range ρ) := hgen ▸ Subgroup.mem_top w
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h i
      | one => simp
      | mul a b _ _ ha hb => intro x; rw [mul_assoc, ha, hb, mul_assoc]
      | inv a _ ha =>
        intro x
        have := ha (a⁻¹ * x)
        rw [mul_inv_cancel_left] at this
        rw [this, inv_mul_cancel_left]
    refine ⟨MulOpposite.op (σ 1), Equiv.ext fun x => ?_⟩
    rw [rightMulHom_apply, MulOpposite.unop_op, ← hall, mul_one]

/-- When the `ρ i` generate `W`, the regular flag system of `ρ` is regular, with automorphism
group `Wᵐᵒᵖ`. -/
theorem isRegular_ofGroup (hgen : Subgroup.closure (Set.range ρ) = ⊤) :
    (ofGroup ρ hρ hfar).IsRegular ∧ Nonempty ((ofGroup ρ hρ hfar).aut ≃* Wᵐᵒᵖ) := by
  refine ⟨⟨(isConnected_ofGroup_iff ρ hρ hfar).2 hgen, fun g hg d hd => ?_⟩, ⟨?_⟩⟩
  · rw [monodromy_ofGroup] at hg
    obtain ⟨u, _, rfl⟩ := hg
    change u * d = d at hd
    rw [mul_eq_right] at hd
    rw [hd, map_one]
  · exact ((MonoidHom.ofInjective rightMulHom_injective).trans
      (MulEquiv.subgroupCongr (range_rightMulHom ρ hρ hfar hgen))).symm

end OfGroup

/-- The automorphism group of the coset flag system of a normal subgroup `N` is
`(cartographicGroup n ⧸ N)ᵐᵒᵖ`. -/
theorem nonempty_mulEquiv_aut_cosetGMap (N : Subgroup (cartographicGroup n)) [N.Normal] :
    Nonempty ((cosetGMap N).aut ≃* (cartographicGroup n ⧸ N)ᵐᵒᵖ) := by
  set s := (cartographicMatrix n).toCoxeterSystem.simple
  set ρ : Fin (n + 1) → cartographicGroup n ⧸ N := fun i => (s i : cartographicGroup n ⧸ N)
  have hρ : ∀ i, ρ i * ρ i = 1 := fun i => by
    rw [← QuotientGroup.mk_mul, CoxeterSystem.simple_mul_simple_self, QuotientGroup.mk_one]
  have hfar : ∀ i j : Fin (n + 1), (i : ℕ) + 2 ≤ j → Commute (ρ i) (ρ j) := fun i j h =>
    (commute_simple_of_eq_two _ (stringCoxeterMatrix_of_far h)).map (QuotientGroup.mk' N)
  have hgen : Subgroup.closure (Set.range ρ) = ⊤ := by
    have : Set.range ρ = QuotientGroup.mk' N '' Set.range s := by
      rw [← Set.range_comp]; rfl
    rw [this, ← MonoidHom.map_closure, CoxeterSystem.subgroupClosure_range_simple,
      ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  have hadj : (cosetGMap N).adj = (ofGroup ρ hρ hfar).adj := by
    funext i
    refine Equiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on
    rfl
  have haut : (cosetGMap N).aut = (ofGroup ρ hρ hfar).aut := by
    rw [aut, aut, hadj]
  exact ⟨(MulEquiv.subgroupCongr haut).trans
    (isRegular_ofGroup ρ hρ hfar hgen).2.some⟩

/-! ### The regular flag system of the monodromy group -/

/-- The generators `adj i` of the monodromy group, as elements of it. -/
def monodromyGen (i : Fin (n + 1)) : G.monodromy :=
  ⟨G.adj i, Subgroup.subset_closure ⟨i, rfl⟩⟩

/-- The generators of the monodromy group are involutions. -/
theorem monodromyGen_mul_self (i : Fin (n + 1)) : G.monodromyGen i * G.monodromyGen i = 1 :=
  Subtype.ext (Equiv.ext fun d => G.involutive i d)

/-- Distant generators of the monodromy group commute. -/
theorem commute_monodromyGen (i j : Fin (n + 1)) (h : (i : ℕ) + 2 ≤ j) :
    Commute (G.monodromyGen i) (G.monodromyGen j) :=
  Subtype.ext (G.commute_of_far i j h).eq

/-- The regular flag system of the monodromy group. -/
def ofMonodromy : GMap n G.monodromy :=
  ofGroup G.monodromyGen G.monodromyGen_mul_self G.commute_monodromyGen

/-- Every nonempty regular flag system is isomorphic to the regular flag system of its monodromy
group. -/
theorem nonempty_iso_ofMonodromy [Nonempty D] (hG : G.IsRegular) :
    Nonempty (G.Iso G.ofMonodromy) := by
  obtain ⟨d₀⟩ := ‹Nonempty D›
  set f : G.monodromy → D := fun g => (g : Perm D) d₀
  have hinj : Function.Injective f := by
    intro g h hgh
    have hmem : (h : Perm D)⁻¹ * g ∈ G.monodromy :=
      G.monodromy.mul_mem (G.monodromy.inv_mem h.2) g.2
    have := hG.2 _ hmem d₀ (by
      change (h : Perm D)⁻¹ ((g : Perm D) d₀) = d₀
      change (g : Perm D) d₀ = (h : Perm D) d₀ at hgh
      rw [hgh, perm_inv_apply_self])
    exact Subtype.ext (inv_mul_eq_one.1 this).symm
  have hsurj : Function.Surjective f := fun e => by
    obtain ⟨g, hg, he⟩ := (G.isConnected_iff_forall_exists).1 hG.1 d₀ e
    exact ⟨⟨g, hg⟩, he⟩
  set F := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨⟨F.symm, fun i d => ?_⟩⟩
  apply F.injective
  rw [F.apply_symm_apply]
  change G.adj i d = ((G.monodromyGen i * F.symm d : G.monodromy) : Perm D) d₀
  rw [Subgroup.coe_mul, Perm.mul_apply]
  change G.adj i d = G.adj i (f (F.symm d))
  rw [show f (F.symm d) = F (F.symm d) from rfl, F.apply_symm_apply]

end GMap

end LeanPool.PseudolineArrangements
