/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.FBLOrderContinuity.BanLat.AMSpace.Maximal
public import LeanPool.OrderClosures.BanLat.Operators.Hom
public import LeanPool.FBLOrderContinuity.BanLat.RieszDec
public import Mathlib.Topology.ContinuousMap.Compact



/-!
# Characters of AM-spaces with unit

This file introduces the character space of an AM-space with unit and records
its basic order, norm, and topological properties.
-/

@[expose] public section

namespace AMSpaceWithUnit

variable (X : Type*) [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [AMSpaceWithUnit X]

/-- A **lattice character** of an AM-space with unit is a real-valued vector
lattice homomorphism that maps the distinguished unit to `1`. -/
structure LatticeCharacter extends VecLatHom X ℝ where
  /-- A lattice character maps the distinguished unit to `1`. -/
  map_unit : toVecLatHom (AMSpaceWithUnit.unit : X) = 1

namespace LatticeCharacter

variable {X}

/-- The canonical `FunLike` instance, making `LatticeCharacter X` a type of
functions `X → ℝ`. -/
noncomputable instance instFunLike : FunLike (LatticeCharacter X) X ℝ where
  coe φ := fun x => φ.toVecLatHom x
  coe_injective := by
    intro φ ψ h
    cases φ
    cases ψ
    congr
    exact DFunLike.coe_injective h

@[simp] theorem coe_mk (f : VecLatHom X ℝ)
    (hf : f (AMSpaceWithUnit.unit : X) = 1) (x : X) :
    (mk f hf : X → ℝ) x = f x := rfl

@[simp] theorem map_unit_apply (φ : LatticeCharacter X) :
    φ (AMSpaceWithUnit.unit : X) = 1 :=
  φ.map_unit

/-- A lattice character preserves suprema. -/
theorem map_sup (φ : LatticeCharacter X) (x y : X) :
    φ (x ⊔ y) = max (φ x) (φ y) :=
  φ.toVecLatHom.toLatticeHom.map_sup' x y

/-- A lattice character preserves infima. -/
theorem map_inf (φ : LatticeCharacter X) (x y : X) :
    φ (x ⊓ y) = min (φ x) (φ y) :=
  φ.toVecLatHom.toLatticeHom.map_inf' x y

/-- A lattice character is monotone. -/
theorem monotone (φ : LatticeCharacter X) : Monotone (φ : X → ℝ) :=
  φ.toVecLatHom.monotone

/-- A lattice character sends positive elements to non-negative reals. -/
theorem nonneg_apply (φ : LatticeCharacter X) {x : X} (hx : 0 ≤ x) :
    0 ≤ φ x :=
  φ.toVecLatHom.map_nonneg hx

theorem abs_le_norm_smul_unit (x : X) :
    |x| ≤ ‖x‖ • (AMSpaceWithUnit.unit : X) := by
  have hx : x ∈ OrderIdeal.principal (AMSpaceWithUnit.unit : X) := by
    rw [principal_unit_eq_top (X := X)]
    exact OrderIdeal.mem_top
  have h := OrderIdeal.abs_le_gaugeNorm_smul_abs (AMSpaceWithUnit.unit : X) hx
  rw [← AMSpaceWithUnit.norm_eq_gaugeNorm, abs_of_nonneg (unit_nonneg (X := X))] at h
  exact h

/-- The fundamental norm bound for a lattice character: `|φ x| ≤ ‖x‖`. -/
theorem abs_apply_le_norm (φ : LatticeCharacter X) (x : X) :
    |φ x| ≤ ‖x‖ := by
  have h1 : |(φ x : ℝ)| = φ.toVecLatHom |x| := (φ.toVecLatHom.map_abs x).symm
  have h2 : φ.toVecLatHom (‖x‖ • (AMSpaceWithUnit.unit : X)) = ‖x‖ := by
    rw [map_smul, φ.map_unit, smul_eq_mul, mul_one]
  rw [h1, ← h2]
  exact φ.toVecLatHom.monotone (abs_le_norm_smul_unit x)

/-- A lattice character is a continuous functional. -/
theorem continuous (φ : LatticeCharacter X) : Continuous (φ : X → ℝ) := by
  have h : Continuous (φ.toVecLatHom.toLinearMap : X → ℝ) :=
    AddMonoidHomClass.continuous_of_bound φ.toVecLatHom.toLinearMap 1 fun x => by
      rw [Real.norm_eq_abs, one_mul]
      exact abs_apply_le_norm φ x
  exact h

variable (X)

/-- The character space is topologised as a subspace of `X → ℝ` with the
product topology. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (LatticeCharacter X) :=
  TopologicalSpace.induced (fun φ : LatticeCharacter X => (φ : X → ℝ))
    Pi.topologicalSpace

/-- For each `x : X`, the evaluation map `φ ↦ φ x` is continuous. -/
theorem continuous_eval (x : X) :
    Continuous (fun φ : LatticeCharacter X => φ x) :=
  (continuous_apply x).comp continuous_induced_dom

/-- The character space is Hausdorff. -/
instance instT2Space : T2Space (LatticeCharacter X) :=
  T2Space.of_injective_continuous (f := fun φ : LatticeCharacter X => (φ : X → ℝ))
    DFunLike.coe_injective continuous_induced_dom

theorem range_coe_eq_inter :
    Set.range (fun φ : LatticeCharacter X => (φ : X → ℝ)) =
    (⋂ p : X × X, {g : X → ℝ | g (p.1 + p.2) = g p.1 + g p.2}) ∩
    (⋂ p : ℝ × X, {g : X → ℝ | g (p.1 • p.2) = p.1 * g p.2}) ∩
    (⋂ p : X × X, {g : X → ℝ | g (p.1 ⊔ p.2) = max (g p.1) (g p.2)}) ∩
    (⋂ p : X × X, {g : X → ℝ | g (p.1 ⊓ p.2) = min (g p.1) (g p.2)}) ∩
    {g : X → ℝ | g (AMSpaceWithUnit.unit : X) = 1} := by
  ext g
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
    Prod.forall]
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact fun x y => map_add φ.toVecLatHom x y
    · exact fun c x => map_smul φ.toVecLatHom c x
    · exact LatticeCharacter.map_sup φ
    · exact LatticeCharacter.map_inf φ
    · exact φ.map_unit
  · rintro ⟨⟨⟨⟨hadd, hsmul⟩, hsup⟩, hinf⟩, hunit⟩
    refine ⟨⟨⟨⟨⟨g, hadd⟩, hsmul⟩, hsup, hinf⟩, hunit⟩, rfl⟩

/-- The character space is compact in the product topology. -/
instance instCompactSpace : CompactSpace (LatticeCharacter X) := by
  let ι : LatticeCharacter X → (X → ℝ) := fun φ x => φ x
  have hι : Topology.IsInducing ι := ⟨rfl⟩
  refine ⟨?_⟩
  rw [Topology.IsInducing.isCompact_iff hι, Set.image_univ]
  set K : Set (X → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-‖x‖) ‖x‖) with hK_def
  have hK_compact : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hrange_sub : Set.range ι ⊆ K := by
    rintro g ⟨φ, rfl⟩ x _
    simp only [Set.mem_Icc]
    exact abs_le.mp (φ.abs_apply_le_norm x)
  have hrange_closed : IsClosed (Set.range ι) := by
    have heq : (Set.range ι) =
        Set.range (fun φ : LatticeCharacter X => (φ : X → ℝ)) := rfl
    rw [heq, range_coe_eq_inter]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 + p.2))
        ((continuous_apply p.1).add (continuous_apply p.2))
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 • p.2))
        (continuous_const.mul (continuous_apply p.2))
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 ⊔ p.2))
        ((continuous_apply p.1).max (continuous_apply p.2))
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 ⊓ p.2))
        ((continuous_apply p.1).min (continuous_apply p.2))
    · exact isClosed_eq (continuous_apply (AMSpaceWithUnit.unit : X)) continuous_const
  exact hK_compact.of_isClosed_subset hrange_closed hrange_sub

/-! ### Characters from maximal ideals -/

variable {X}

/-- The ideal obtained by adjoining one generator to an order ideal. -/
noncomputable def addPrincipal (M : OrderIdeal X) (y : X) : OrderIdeal X :=
  OrderIdeal.ofSolid (M.toSubmodule + (OrderIdeal.principal y).toSubmodule) <| by
    intro a b hab habs
    obtain ⟨m, hm_mem, u, hu_mem, rfl⟩ := Submodule.mem_sup.mp hab
    have habs' : |b| ≤ |m| + |u| := habs.trans (abs_add_le m u)
    have hm_abs_mem : |m| ∈ M := M.abs_mem hm_mem
    have hu_abs_mem : |u| ∈ OrderIdeal.principal y :=
      (OrderIdeal.principal y).abs_mem hu_mem
    have hpos_le : b⁺ ≤ |m| + |u| :=
      sup_le ((le_abs_self b).trans habs') (add_nonneg (abs_nonneg m) (abs_nonneg u))
    have hneg_le : b⁻ ≤ |m| + |u| :=
      sup_le ((neg_le_abs b).trans habs') (add_nonneg (abs_nonneg m) (abs_nonneg u))
    obtain ⟨p₁, p₂, hp₁_nn, hp₁_le, hp₂_nn, hp₂_le, hp_eq⟩ :=
      riesz_decomposition (b⁺) |m| |u| (posPart_nonneg b)
        (abs_nonneg m) (abs_nonneg u) hpos_le
    obtain ⟨n₁, n₂, hn₁_nn, hn₁_le, hn₂_nn, hn₂_le, hn_eq⟩ :=
      riesz_decomposition (b⁻) |m| |u| (negPart_nonneg b)
        (abs_nonneg m) (abs_nonneg u) hneg_le
    have hp₁_M : p₁ ∈ M := M.solid hm_abs_mem hp₁_nn hp₁_le
    have hp₂_I : p₂ ∈ OrderIdeal.principal y :=
      (OrderIdeal.principal y).solid hu_abs_mem hp₂_nn hp₂_le
    have hn₁_M : n₁ ∈ M := M.solid hm_abs_mem hn₁_nn hn₁_le
    have hn₂_I : n₂ ∈ OrderIdeal.principal y :=
      (OrderIdeal.principal y).solid hu_abs_mem hn₂_nn hn₂_le
    have hb_eq : b = (p₁ - n₁) + (p₂ - n₂) := by
      have hp := posPart_sub_negPart b
      rw [hp_eq, hn_eq] at hp
      rw [← hp]
      abel
    rw [hb_eq]
    exact Submodule.add_mem _
      (Submodule.sub_mem _ (Submodule.mem_sup_left hp₁_M)
        (Submodule.mem_sup_left hn₁_M))
      (Submodule.sub_mem _ (Submodule.mem_sup_right hp₂_I)
        (Submodule.mem_sup_right hn₂_I))

theorem addPrincipal_le (M : OrderIdeal X) (y : X) :
    M ≤ addPrincipal M y := by
  intro x hx
  change x ∈ M.toSubmodule + (OrderIdeal.principal y).toSubmodule
  exact Submodule.mem_sup_left hx

theorem self_mem_addPrincipal (M : OrderIdeal X) (y : X) :
    y ∈ addPrincipal M y := by
  change y ∈ M.toSubmodule + (OrderIdeal.principal y).toSubmodule
  exact Submodule.mem_sup_right (OrderIdeal.self_mem_principal y)

theorem mem_of_disjoint_notMem (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M)
    {y z : X} (hy_nn : 0 ≤ y) (hz_nn : 0 ≤ z) (hdisj : y ⊓ z = 0)
    (hy_notin : y ∉ M) : z ∈ M := by
  have hM_lt : M ≤ addPrincipal M y := addPrincipal_le M y
  have hM_ne_addP : M ≠ addPrincipal M y := by
    intro heq
    apply hy_notin
    rw [heq]
    exact self_mem_addPrincipal M y
  have htop : addPrincipal M y = ⊤ := by
    by_contra hne
    exact hM_ne_addP (hmax _ hM_lt hne).symm
  have hz_in : z ∈ (addPrincipal M y).toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  have hz_in' : z ∈ M.toSubmodule + (OrderIdeal.principal y).toSubmodule := hz_in
  obtain ⟨m, hm, u, hu, hzmu⟩ := Submodule.mem_sup.mp hz_in'
  obtain ⟨c, hc, hu_bound⟩ := hu
  have hz_abs : z ≤ |m| + |u| := by
    calc
      z = m + u := hzmu.symm
      _ ≤ |m| + |u| := add_le_add (le_abs_self m) (le_abs_self u)
  obtain ⟨z₁, z₂, hz₁_nn, hz₁_le_m, hz₂_nn, hz₂_le_u, hz₁₂⟩ :=
    riesz_decomposition z |m| |u| hz_nn (abs_nonneg m) (abs_nonneg u) hz_abs
  have hz₁_M : z₁ ∈ M := M.solid (M.abs_mem hm) hz₁_nn hz₁_le_m
  have hy_z₂ : y ⊓ z₂ = 0 := by
    apply le_antisymm
    · have : z₂ ≤ z := le_trans (le_add_of_nonneg_left hz₁_nn) hz₁₂.symm.le
      calc
        y ⊓ z₂ ≤ y ⊓ z := inf_le_inf le_rfl this
        _ = 0 := hdisj
    · exact le_inf hy_nn hz₂_nn
  have hz₂_le_cy : z₂ ≤ c • y := by
    have h1 : z₂ ≤ c • |y| := hz₂_le_u.trans hu_bound
    rwa [abs_of_nonneg hy_nn] at h1
  have hz₂_disj_cy : (c • y) ⊓ z₂ = 0 :=
    inf_eq_zero_of_isVLDisjoint (smul_nonneg hc hy_nn) hz₂_nn
      ((isVLDisjoint_of_inf_eq_zero hy_z₂).smul_left c)
  have hz₂_zero : z₂ = 0 := by
    have h := inf_eq_left.mpr hz₂_le_cy
    rw [inf_comm] at hz₂_disj_cy
    rw [hz₂_disj_cy] at h
    exact h.symm
  rw [hz₁₂, hz₂_zero, add_zero]
  exact hz₁_M

theorem smul_unit_notMem_of_proper (M : OrderIdeal X) (hMne : M ≠ ⊤)
    {c : ℝ} (hc : 0 < c) :
    c • (AMSpaceWithUnit.unit : X) ∉ M := by
  intro h
  apply hMne
  rw [top_iff_unit_mem]
  have heq : (1 / c) • (c • (AMSpaceWithUnit.unit : X)) =
      AMSpaceWithUnit.unit := by
    rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  rw [← heq]
  exact M.toSubmodule.smul_mem _ h

theorem nonneg_le_smul_unit_notMem (M : OrderIdeal X) (hMne : M ≠ ⊤)
    {c : ℝ} (hc : 0 < c) {y : X}
    (hy : c • (AMSpaceWithUnit.unit : X) ≤ y) (hyM : y ∈ M) : False := by
  apply smul_unit_notMem_of_proper M hMne hc
  have h_pos : 0 ≤ c • (AMSpaceWithUnit.unit : X) :=
    smul_nonneg hc.le (unit_nonneg (X := X))
  exact M.solid hyM h_pos hy

/-- Scalar multiples of the unit lying below `x` modulo the ideal. -/
def charSetA (M : OrderIdeal X) (x : X) : Set ℝ :=
  {c : ℝ | (c • AMSpaceWithUnit.unit - x)⁺ ∈ M}

/-- Scalar multiples of the unit lying above `x` modulo the ideal. -/
def charSetB (M : OrderIdeal X) (x : X) : Set ℝ :=
  {c : ℝ | (x - c • AMSpaceWithUnit.unit)⁺ ∈ M}

theorem mem_charSetA {M : OrderIdeal X} {x : X} {c : ℝ} :
    c ∈ charSetA M x ↔ (c • AMSpaceWithUnit.unit - x)⁺ ∈ M := Iff.rfl

theorem mem_charSetB {M : OrderIdeal X} {x : X} {c : ℝ} :
    c ∈ charSetB M x ↔ (x - c • AMSpaceWithUnit.unit)⁺ ∈ M := Iff.rfl

theorem neg_norm_smul_unit_le (x : X) :
    -((‖x‖ : ℝ) • AMSpaceWithUnit.unit) ≤ x :=
  neg_le.mp (abs_le'.mp (abs_le_norm_smul_unit x)).2

theorem le_norm_smul_unit (x : X) :
    x ≤ (‖x‖ : ℝ) • AMSpaceWithUnit.unit :=
  (abs_le'.mp (abs_le_norm_smul_unit x)).1

theorem neg_norm_mem_charSetA (M : OrderIdeal X) (x : X) :
    -‖x‖ ∈ charSetA M x := by
  rw [mem_charSetA]
  have hle : (-‖x‖ : ℝ) • AMSpaceWithUnit.unit - x ≤ 0 := by
    rw [neg_smul, sub_nonpos]
    exact neg_norm_smul_unit_le x
  rw [posPart_eq_zero.mpr hle]
  exact M.toSubmodule.zero_mem

theorem norm_mem_charSetB (M : OrderIdeal X) (x : X) :
    ‖x‖ ∈ charSetB M x := by
  rw [mem_charSetB]
  have hle : x - (‖x‖ : ℝ) • AMSpaceWithUnit.unit ≤ 0 :=
    sub_nonpos.mpr (le_norm_smul_unit x)
  rw [posPart_eq_zero.mpr hle]
  exact M.toSubmodule.zero_mem

theorem charSetA_nonempty (M : OrderIdeal X) (x : X) :
    (charSetA M x).Nonempty :=
  ⟨-‖x‖, neg_norm_mem_charSetA M x⟩

theorem charSetB_nonempty (M : OrderIdeal X) (x : X) :
    (charSetB M x).Nonempty :=
  ⟨‖x‖, norm_mem_charSetB M x⟩

theorem charSetA_downwardClosed (M : OrderIdeal X) (x : X)
    {c d : ℝ} (hc : c ∈ charSetA M x) (hdc : d ≤ c) : d ∈ charSetA M x := by
  rw [mem_charSetA] at hc ⊢
  apply M.solid hc (posPart_nonneg _)
  apply sup_le_sup_right
  exact sub_le_sub_right
    (smul_le_smul_of_nonneg_right hdc (unit_nonneg (X := X))) _

theorem charSetB_upwardClosed (M : OrderIdeal X) (x : X)
    {c d : ℝ} (hc : c ∈ charSetB M x) (hcd : c ≤ d) : d ∈ charSetB M x := by
  rw [mem_charSetB] at hc ⊢
  apply M.solid hc (posPart_nonneg _)
  apply sup_le_sup_right
  exact sub_le_sub_left
    (smul_le_smul_of_nonneg_right hcd (unit_nonneg (X := X))) _

theorem charSetA_bddAbove (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X) :
    BddAbove (charSetA M x) := by
  refine ⟨‖x‖, fun c hc => ?_⟩
  by_contra hlt
  push Not at hlt
  have hxle := le_norm_smul_unit x
  have h1 : (c - ‖x‖) • (AMSpaceWithUnit.unit : X) ≤
      c • AMSpaceWithUnit.unit - x := by
    rw [sub_smul]
    exact sub_le_sub_left hxle (c • AMSpaceWithUnit.unit)
  have hpos : 0 < c - ‖x‖ := sub_pos.mpr hlt
  have h2 : (c - ‖x‖) • (AMSpaceWithUnit.unit : X) ≤
      (c • AMSpaceWithUnit.unit - x)⁺ :=
    h1.trans (le_posPart _)
  exact nonneg_le_smul_unit_notMem M hMne hpos h2 hc

theorem charSetB_bddBelow (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X) :
    BddBelow (charSetB M x) := by
  refine ⟨-‖x‖, fun c hc => ?_⟩
  by_contra hlt
  push Not at hlt
  have hxle := neg_norm_smul_unit_le x
  have h1 : (-‖x‖ - c) • (AMSpaceWithUnit.unit : X) ≤
      x - c • AMSpaceWithUnit.unit := by
    rw [sub_smul, neg_smul]
    have : -(‖x‖ • (AMSpaceWithUnit.unit : X)) -
        c • AMSpaceWithUnit.unit ≤ x - c • AMSpaceWithUnit.unit :=
      sub_le_sub_right hxle (c • AMSpaceWithUnit.unit)
    exact this
  have hpos : 0 < -‖x‖ - c := by linarith
  have h2 : (-‖x‖ - c) • (AMSpaceWithUnit.unit : X) ≤
      (x - c • AMSpaceWithUnit.unit)⁺ :=
    h1.trans (le_posPart _)
  exact nonneg_le_smul_unit_notMem M hMne hpos h2 hc

theorem charSetA_union_charSetB (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M)
    (x : X) (c : ℝ) :
    c ∈ charSetA M x ∨ c ∈ charSetB M x := by
  set y := (c • (AMSpaceWithUnit.unit : X) - x)⁺ with hy_def
  set z := (x - c • (AMSpaceWithUnit.unit : X))⁺ with hz_def
  have hyz : y ⊓ z = 0 := by
    have heq : (x - c • (AMSpaceWithUnit.unit : X))⁺ =
        (c • AMSpaceWithUnit.unit - x)⁻ := by
      rw [show (x - c • (AMSpaceWithUnit.unit : X)) =
          -(c • AMSpaceWithUnit.unit - x) from by abel,
        show ((-(c • (AMSpaceWithUnit.unit : X) - x))⁺ : X) =
          (c • AMSpaceWithUnit.unit - x)⁻ from rfl]
    rw [hy_def, hz_def, heq]
    exact posPart_inf_negPart_eq_zero _
  have hy_nn : 0 ≤ y := posPart_nonneg _
  have hz_nn : 0 ≤ z := posPart_nonneg _
  by_cases hy : y ∈ M
  · left
    exact hy
  · right
    rw [mem_charSetB]
    exact mem_of_disjoint_notMem M hmax hy_nn hz_nn hyz hy

theorem charSetA_charSetB_unique (M : OrderIdeal X) (hMne : M ≠ ⊤)
    (x : X) {c : ℝ} (hcA : c ∈ charSetA M x) (hcB : c ∈ charSetB M x)
    {d : ℝ} (hdA : d ∈ charSetA M x) (hdB : d ∈ charSetB M x) : c = d := by
  rw [mem_charSetA] at hcA hdA
  rw [mem_charSetB] at hcB hdB
  have hc_neg_in : (c • (AMSpaceWithUnit.unit : X) - x)⁻ ∈ M := by
    have h : (c • (AMSpaceWithUnit.unit : X) - x)⁻ =
        (x - c • AMSpaceWithUnit.unit)⁺ := by
      rw [show x - c • (AMSpaceWithUnit.unit : X) =
          -(c • AMSpaceWithUnit.unit - x) from by abel,
        show ((-(c • (AMSpaceWithUnit.unit : X) - x))⁺ : X) =
          (c • AMSpaceWithUnit.unit - x)⁻ from rfl]
    rw [h]
    exact hcB
  have hd_neg_in : (d • (AMSpaceWithUnit.unit : X) - x)⁻ ∈ M := by
    have h : (d • (AMSpaceWithUnit.unit : X) - x)⁻ =
        (x - d • AMSpaceWithUnit.unit)⁺ := by
      rw [show x - d • (AMSpaceWithUnit.unit : X) =
          -(d • AMSpaceWithUnit.unit - x) from by abel,
        show ((-(d • (AMSpaceWithUnit.unit : X) - x))⁺ : X) =
          (d • AMSpaceWithUnit.unit - x)⁻ from rfl]
    rw [h]
    exact hdB
  have hc_in : c • (AMSpaceWithUnit.unit : X) - x ∈ M := by
    have h := M.toSubmodule.sub_mem hcA hc_neg_in
    rwa [posPart_sub_negPart] at h
  have hd_in : d • (AMSpaceWithUnit.unit : X) - x ∈ M := by
    have h := M.toSubmodule.sub_mem hdA hd_neg_in
    rwa [posPart_sub_negPart] at h
  have hcd_in : (c - d) • (AMSpaceWithUnit.unit : X) ∈ M := by
    have h := M.toSubmodule.sub_mem hc_in hd_in
    have heq :
        (c • (AMSpaceWithUnit.unit : X) - x) -
          (d • AMSpaceWithUnit.unit - x) =
        (c - d) • AMSpaceWithUnit.unit := by
      rw [sub_smul]
      abel
    rwa [heq] at h
  by_contra hne
  have hne' : c - d ≠ 0 := sub_ne_zero.mpr hne
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have h_neg : -((c - d) • (AMSpaceWithUnit.unit : X)) ∈ M :=
      M.toSubmodule.neg_mem hcd_in
    rw [← neg_smul] at h_neg
    exact smul_unit_notMem_of_proper M hMne (neg_pos.mpr hlt) h_neg
  · exact smul_unit_notMem_of_proper M hMne hgt hcd_in

theorem charSetA_le_charSetB (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X)
    {a : ℝ} (ha : a ∈ charSetA M x) {b : ℝ} (hb : b ∈ charSetB M x) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  have hbA : b ∈ charSetA M x := charSetA_downwardClosed M x ha hlt.le
  have haB : a ∈ charSetB M x := charSetB_upwardClosed M x hb hlt.le
  exact absurd (charSetA_charSetB_unique M hMne x hbA hb ha haB) (ne_of_gt hlt).symm

theorem inf_charSetB_le_sup_charSetA (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    sInf (charSetB M x) ≤ sSup (charSetA M x) := by
  by_contra hgt
  push Not at hgt
  obtain ⟨c, hc1, hc2⟩ := exists_between hgt
  have hcA : c ∉ charSetA M x := fun h =>
    not_lt.mpr (le_csSup (charSetA_bddAbove M hMne x) h) hc1
  have hcB : c ∉ charSetB M x := fun h =>
    not_lt.mpr (csInf_le (charSetB_bddBelow M hMne x) h) hc2
  rcases charSetA_union_charSetB M hmax x c with h | h
  · exact hcA h
  · exact hcB h

theorem sup_charSetA_eq_inf_charSetB (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    sSup (charSetA M x) = sInf (charSetB M x) := by
  apply le_antisymm
  · apply csSup_le (charSetA_nonempty M x)
    intro a ha
    apply le_csInf (charSetB_nonempty M x)
    intro b hb
    exact charSetA_le_charSetB M hMne x ha hb
  · exact inf_charSetB_le_sup_charSetA M hmax hMne x

/-- The scalar value of `x` determined by the lower cut modulo the ideal. -/
noncomputable def charValue (M : OrderIdeal X) (x : X) : ℝ :=
  sSup (charSetA M x)

theorem charValue_eq_inf_charSetB (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    charValue M x = sInf (charSetB M x) :=
  sup_charSetA_eq_inf_charSetB M hmax hMne x

theorem charValue_zero (M : OrderIdeal X) (hmax : ∀ J : OrderIdeal X,
    M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    charValue M (0 : X) = 0 := by
  apply le_antisymm
  · rw [charValue_eq_inf_charSetB M hmax hMne]
    apply csInf_le (charSetB_bddBelow M hMne 0)
    rw [mem_charSetB]
    have : (0 - (0 : ℝ) • (AMSpaceWithUnit.unit : X))⁺ = 0 := by
      rw [zero_smul, sub_zero, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem
  · apply le_csSup (charSetA_bddAbove M hMne 0)
    rw [mem_charSetA]
    have : ((0 : ℝ) • (AMSpaceWithUnit.unit : X) - 0)⁺ = 0 := by
      rw [zero_smul, sub_zero, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem

theorem charValue_unit (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    charValue M (AMSpaceWithUnit.unit : X) = 1 := by
  apply le_antisymm
  · rw [charValue_eq_inf_charSetB M hmax hMne]
    apply csInf_le (charSetB_bddBelow M hMne AMSpaceWithUnit.unit)
    rw [mem_charSetB]
    have : ((AMSpaceWithUnit.unit : X) - (1 : ℝ) • AMSpaceWithUnit.unit)⁺ = 0 := by
      rw [one_smul, sub_self, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem
  · apply le_csSup (charSetA_bddAbove M hMne AMSpaceWithUnit.unit)
    rw [mem_charSetA]
    have : ((1 : ℝ) • (AMSpaceWithUnit.unit : X) - AMSpaceWithUnit.unit)⁺ = 0 := by
      rw [one_smul, sub_self, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem

theorem charValue_add_le_aux (M : OrderIdeal X) (x y : X)
    {c₁ : ℝ} (hc₁ : c₁ ∈ charSetA M x) {c₂ : ℝ} (hc₂ : c₂ ∈ charSetA M y) :
    c₁ + c₂ ∈ charSetA M (x + y) := by
  rw [mem_charSetA] at hc₁ hc₂ ⊢
  have h1 : ((c₁ + c₂) • (AMSpaceWithUnit.unit : X) - (x + y))⁺ ≤
      (c₁ • AMSpaceWithUnit.unit - x)⁺ + (c₂ • AMSpaceWithUnit.unit - y)⁺ := by
    have hsum : (c₁ + c₂) • (AMSpaceWithUnit.unit : X) - (x + y) =
        (c₁ • AMSpaceWithUnit.unit - x) + (c₂ • AMSpaceWithUnit.unit - y) := by
      rw [add_smul]
      abel
    rw [hsum]
    exact posPart_add_le _ _
  exact M.solid (M.toSubmodule.add_mem hc₁ hc₂) (posPart_nonneg _) h1

theorem charValue_add_le_aux' (M : OrderIdeal X) (x y : X)
    {c₁ : ℝ} (hc₁ : c₁ ∈ charSetB M x) {c₂ : ℝ} (hc₂ : c₂ ∈ charSetB M y) :
    c₁ + c₂ ∈ charSetB M (x + y) := by
  rw [mem_charSetB] at hc₁ hc₂ ⊢
  have h1 : ((x + y) - (c₁ + c₂) • (AMSpaceWithUnit.unit : X))⁺ ≤
      (x - c₁ • AMSpaceWithUnit.unit)⁺ + (y - c₂ • AMSpaceWithUnit.unit)⁺ := by
    have hsum : (x + y) - (c₁ + c₂) • (AMSpaceWithUnit.unit : X) =
        (x - c₁ • AMSpaceWithUnit.unit) + (y - c₂ • AMSpaceWithUnit.unit) := by
      rw [add_smul]
      abel
    rw [hsum]
    exact posPart_add_le _ _
  exact M.solid (M.toSubmodule.add_mem hc₁ hc₂) (posPart_nonneg _) h1

section CharValueOps

open scoped Pointwise

theorem charSetA_add_subset (M : OrderIdeal X) (x y : X) :
    (charSetA M x + charSetA M y : Set ℝ) ⊆ charSetA M (x + y) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact charValue_add_le_aux M x y ha hb

theorem charSetB_add_subset (M : OrderIdeal X) (x y : X) :
    (charSetB M x + charSetB M y : Set ℝ) ⊆ charSetB M (x + y) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact charValue_add_le_aux' M x y ha hb

theorem charValue_add (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x y : X) :
    charValue M (x + y) = charValue M x + charValue M y := by
  apply le_antisymm
  · rw [charValue_eq_inf_charSetB M hmax hMne x,
      charValue_eq_inf_charSetB M hmax hMne y,
      charValue_eq_inf_charSetB M hmax hMne (x + y)]
    have hsub : (charSetB M x + charSetB M y : Set ℝ) ⊆ charSetB M (x + y) :=
      charSetB_add_subset M x y
    have hinf_sum : sInf (charSetB M x + charSetB M y) =
        sInf (charSetB M x) + sInf (charSetB M y) :=
      csInf_add (charSetB_nonempty M x) (charSetB_bddBelow M hMne x)
        (charSetB_nonempty M y) (charSetB_bddBelow M hMne y)
    rw [← hinf_sum]
    apply csInf_le_csInf (charSetB_bddBelow M hMne (x + y))
      ((charSetB_nonempty M x).add (charSetB_nonempty M y))
    exact hsub
  · have hsub : (charSetA M x + charSetA M y : Set ℝ) ⊆ charSetA M (x + y) :=
      charSetA_add_subset M x y
    have hsup_sum : sSup (charSetA M x + charSetA M y) =
        sSup (charSetA M x) + sSup (charSetA M y) :=
      csSup_add (charSetA_nonempty M x) (charSetA_bddAbove M hMne x)
        (charSetA_nonempty M y) (charSetA_bddAbove M hMne y)
    change charValue M x + charValue M y ≤ charValue M (x + y)
    unfold charValue
    rw [← hsup_sum]
    apply csSup_le_csSup (charSetA_bddAbove M hMne (x + y))
      ((charSetA_nonempty M x).add (charSetA_nonempty M y))
    exact hsub

theorem charSetA_neg_eq (M : OrderIdeal X) (x : X) :
    charSetA M (-x) = -charSetB M x := by
  ext c
  simp only [charSetA, charSetB, Set.mem_ofPred_eq, Set.mem_neg]
  constructor
  · intro hc
    have : (c • (AMSpaceWithUnit.unit : X) - -x) =
        (x - (-c) • AMSpaceWithUnit.unit) := by
      rw [neg_smul]
      abel
    rw [this] at hc
    exact hc
  · intro hc
    have : (x - (-c) • (AMSpaceWithUnit.unit : X)) =
        (c • AMSpaceWithUnit.unit - -x) := by
      rw [neg_smul]
      abel
    rw [this] at hc
    exact hc

theorem charValue_neg (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    charValue M (-x) = -charValue M x := by
  unfold charValue
  rw [charSetA_neg_eq M x]
  rw [csSup_neg (charSetB_nonempty M x) (charSetB_bddBelow M hMne x)]
  rw [← sup_charSetA_eq_inf_charSetB M hmax hMne x]

theorem charSetA_smul_pos (M : OrderIdeal X) {c : ℝ} (hc : 0 < c) (x : X) :
    charSetA M (c • x) = c • charSetA M x := by
  ext d
  simp only [charSetA, Set.mem_ofPred_eq, Set.mem_smul_set]
  constructor
  · intro hd
    refine ⟨d / c, ?_, ?_⟩
    · have h1 : c • ((d / c) • (AMSpaceWithUnit.unit : X) - x) =
          d • AMSpaceWithUnit.unit - c • x := by
        rw [smul_sub, smul_smul, mul_div_cancel₀ _ (ne_of_gt hc)]
      have h2 : (c • ((d / c) • (AMSpaceWithUnit.unit : X) - x))⁺ ∈ M := by
        rw [h1]
        exact hd
      have h3 : c • ((d / c) • (AMSpaceWithUnit.unit : X) - x)⁺ =
          (c • ((d / c) • AMSpaceWithUnit.unit - x))⁺ := by
        rw [posPart_def, posPart_def, nonneg_smul_sup, smul_zero]
        exact hc.le
      rw [← h3] at h2
      have h4 : (c⁻¹ : ℝ) • c •
          ((d / c) • (AMSpaceWithUnit.unit : X) - x)⁺ ∈ M :=
        M.toSubmodule.smul_mem _ h2
      rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] at h4
    · rw [smul_eq_mul]
      field_simp
  · rintro ⟨d', hd', rfl⟩
    show ((c • d') • (AMSpaceWithUnit.unit : X) - c • x)⁺ ∈ M
    have h1 : (c • d') • (AMSpaceWithUnit.unit : X) - c • x =
        c • (d' • AMSpaceWithUnit.unit - x) := by
      rw [smul_sub, smul_eq_mul, mul_smul]
    rw [h1]
    have h2 : (c • (d' • (AMSpaceWithUnit.unit : X) - x))⁺ =
        c • (d' • AMSpaceWithUnit.unit - x)⁺ := by
      rw [posPart_def, posPart_def, nonneg_smul_sup, smul_zero]
      exact hc.le
    rw [h2]
    exact M.toSubmodule.smul_mem _ hd'

theorem charValue_smul_pos (M : OrderIdeal X) {c : ℝ} (hc : 0 < c) (x : X) :
    charValue M (c • x) = c * charValue M x := by
  unfold charValue
  rw [charSetA_smul_pos M hc x, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]

theorem charValue_smul (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤)
    (c : ℝ) (x : X) :
    charValue M (c • x) = c * charValue M x := by
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  · rw [show (c • x : X) = -((-c) • x) from by rw [neg_smul, neg_neg]]
    rw [charValue_neg M hmax hMne, charValue_smul_pos M (neg_pos.mpr hlt)]
    ring
  · subst heq
    simp [charValue_zero M hmax hMne]
  · exact charValue_smul_pos M hgt x

theorem charValue_nonneg (M : OrderIdeal X) (hMne : M ≠ ⊤) {x : X}
    (hx : 0 ≤ x) : 0 ≤ charValue M x := by
  apply le_csSup (charSetA_bddAbove M hMne x)
  rw [mem_charSetA]
  have h : (0 : X) = ((0 : ℝ) • AMSpaceWithUnit.unit - x)⁺ := by
    rw [zero_smul, zero_sub, posPart_def, ← negPart_def]
    exact (negPart_eq_zero.mpr hx).symm
  rw [← h]
  exact M.toSubmodule.zero_mem

theorem charValue_eq_zero_of_mem (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤)
    {x : X} (hx : x ∈ M) : charValue M x = 0 := by
  have hposPart : x⁺ ∈ M := by
    rw [posPart_def]
    exact M.sup_mem hx M.toSubmodule.zero_mem
  have hnegPart : x⁻ ∈ M := by
    rw [negPart_def]
    exact M.sup_mem (M.toSubmodule.neg_mem hx) M.toSubmodule.zero_mem
  apply le_antisymm
  · rw [charValue_eq_inf_charSetB M hmax hMne]
    apply csInf_le (charSetB_bddBelow M hMne x)
    rw [mem_charSetB, zero_smul, sub_zero]
    exact hposPart
  · apply le_csSup (charSetA_bddAbove M hMne x)
    rw [mem_charSetA, zero_smul, zero_sub]
    have h : (-x)⁺ = x⁻ := by rw [posPart_def, ← negPart_def]
    rw [h]
    exact hnegPart

theorem charValue_disjoint (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤)
    {x y : X} (hxy : x ⊓ y = 0) :
    charValue M x ⊓ charValue M y = 0 := by
  have hx_nn : 0 ≤ x := by
    rw [← hxy]
    exact inf_le_left
  have hy_nn : 0 ≤ y := by
    rw [← hxy]
    exact inf_le_right
  have hx_in_or_y_in : x ∈ M ∨ y ∈ M := by
    by_cases hx : x ∈ M
    · left
      exact hx
    · right
      exact mem_of_disjoint_notMem M hmax hx_nn hy_nn hxy hx
  rcases hx_in_or_y_in with hx | hy
  · rw [charValue_eq_zero_of_mem M hmax hMne hx]
    exact min_eq_left (charValue_nonneg M hMne hy_nn)
  · rw [charValue_eq_zero_of_mem M hmax hMne hy]
    exact min_eq_right (charValue_nonneg M hMne hx_nn)

end CharValueOps

/-- The real lattice character associated with a maximal proper ideal. -/
noncomputable def vecLatHomOfMaximal (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    VecLatHom X ℝ :=
  IsVecLatHom.mk' (charValue M)
    (IsVecLatHom.of_disjoint
      ⟨charValue_add M hmax hMne, fun c x => by
        rw [charValue_smul M hmax hMne]
        rfl⟩
      (fun _ _ hxy => charValue_disjoint M hmax hMne hxy))

/-- The lattice character arising from a maximal proper ideal. -/
noncomputable def ofMaximalIdeal (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    LatticeCharacter X where
  toVecLatHom := vecLatHomOfMaximal M hmax hMne
  map_unit := charValue_unit M hmax hMne

variable (X)

theorem unit_ne_zero [Nontrivial X] :
    (AMSpaceWithUnit.unit : X) ≠ 0 := by
  intro hunit
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  obtain ⟨c, hc, hle⟩ := (strongOrderUnit_unit' (X := X)).2 x
  rw [hunit, smul_zero] at hle
  exact hx ((abs_eq_zero_iff_zero x).mp (le_antisymm hle (abs_nonneg x)))

theorem exists_character [Nontrivial X] : Nonempty (LatticeCharacter X) := by
  classical
  let zeroIdeal : OrderIdeal X := OrderIdeal.ofSolid ⊥ <| by
    intro x y hx hxy
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, abs_zero] at hxy
    exact (abs_eq_zero_iff_zero y).mp (le_antisymm hxy (abs_nonneg y))
  have hZero_ne : zeroIdeal ≠ ⊤ := by
    rw [ne_eq, top_iff_unit_mem]
    change (AMSpaceWithUnit.unit : X) ∉ (⊥ : Submodule ℝ X)
    rw [Submodule.mem_bot]
    exact unit_ne_zero X
  obtain ⟨M, _, hMne, hMmax⟩ := exists_le_maximal zeroIdeal hZero_ne
  exact ⟨ofMaximalIdeal M hMmax hMne⟩

theorem principal_norm_smul_unit_sub_ne_top [Nontrivial X] {x : X}
    (hx_nonneg : 0 ≤ x) (hx_ne : x ≠ 0) :
    OrderIdeal.principal ((‖x‖ : ℝ) • AMSpaceWithUnit.unit - x) ≠ ⊤ := by
  classical
  rw [ne_eq, top_iff_unit_mem]
  intro hunit
  rw [OrderIdeal.mem_principal] at hunit
  obtain ⟨c, hc_nonneg, hc_le⟩ := hunit
  have ha_nonneg : 0 ≤ (‖x‖ : ℝ) • (AMSpaceWithUnit.unit : X) - x :=
    sub_nonneg.mpr (le_norm_smul_unit x)
  rw [abs_of_nonneg (unit_nonneg (X := X)), abs_of_nonneg ha_nonneg] at hc_le
  rcases eq_or_lt_of_le hc_nonneg with hc_zero | hc_pos
  · rw [← hc_zero, zero_smul] at hc_le
    exact unit_ne_zero X (le_antisymm hc_le (unit_nonneg (X := X)))
  · have hinv_pos : 0 < 1 / c := one_div_pos.mpr hc_pos
    have hscaled : (1 / c) • (AMSpaceWithUnit.unit : X) ≤
        (‖x‖ : ℝ) • AMSpaceWithUnit.unit - x := by
      have h := smul_le_smul_of_nonneg_left hc_le hinv_pos.le
      rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hc_pos), one_smul] at h
      simpa [one_div] using h
    have hx_le : x ≤ (‖x‖ - 1 / c : ℝ) • (AMSpaceWithUnit.unit : X) := by
      have h := add_le_add_left hscaled x
      have hright : ((‖x‖ : ℝ) • AMSpaceWithUnit.unit - x) + x =
          (‖x‖ : ℝ) • AMSpaceWithUnit.unit := by abel
      rw [hright] at h
      have h' := sub_le_sub_right h ((1 / c) • (AMSpaceWithUnit.unit : X))
      have hleft' : (1 / c) • (AMSpaceWithUnit.unit : X) + x -
          (1 / c) • AMSpaceWithUnit.unit = x := by abel
      have hright' : (‖x‖ : ℝ) • (AMSpaceWithUnit.unit : X) -
          (1 / c) • (AMSpaceWithUnit.unit : X) =
          (‖x‖ - 1 / c : ℝ) • (AMSpaceWithUnit.unit : X) := by
        rw [sub_smul]
      rwa [hleft', hright'] at h'
    have hcoeff_nonneg : 0 ≤ ‖x‖ - 1 / c := by
      by_contra hneg
      push Not at hneg
      have hsmul_nonpos : (‖x‖ - 1 / c : ℝ) • (AMSpaceWithUnit.unit : X) ≤ 0 :=
        smul_nonpos_of_nonpos_of_nonneg hneg.le (unit_nonneg (X := X))
      have hx_zero : x = 0 := le_antisymm (hx_le.trans hsmul_nonpos) hx_nonneg
      exact hx_ne hx_zero
    have hnorm_le : ‖x‖ ≤ ‖x‖ - 1 / c := by
      calc
        ‖x‖ = OrderIdeal.gaugeNorm (AMSpaceWithUnit.unit : X) x :=
          AMSpaceWithUnit.norm_eq_gaugeNorm x
        _ ≤ ‖x‖ - 1 / c := by
          apply OrderIdeal.gaugeNorm_le_of_abs_le _ hcoeff_nonneg
          rwa [abs_of_nonneg hx_nonneg, abs_of_nonneg (unit_nonneg (X := X))]
    linarith [hinv_pos]

/-- Every positive element of a non-trivial AM-space with unit attains its norm
at a lattice character. -/
theorem exists_apply_eq_norm_of_nonneg [Nontrivial X] {x : X} (hx : 0 ≤ x) :
    ∃ φ : LatticeCharacter X, φ x = ‖x‖ := by
  by_cases hx_zero : x = 0
  · obtain ⟨φ⟩ := exists_character X
    refine ⟨φ, ?_⟩
    rw [hx_zero]
    change φ.toVecLatHom 0 = ‖(0 : X)‖
    rw [map_zero, norm_zero]
  · let a : X := (‖x‖ : ℝ) • AMSpaceWithUnit.unit - x
    have hproper : OrderIdeal.principal a ≠ ⊤ := by
      dsimp [a]
      exact principal_norm_smul_unit_sub_ne_top (X := X) hx hx_zero
    obtain ⟨M, haM, hMne, hMmax⟩ := exists_le_maximal (OrderIdeal.principal a) hproper
    let φ := ofMaximalIdeal M hMmax hMne
    refine ⟨φ, ?_⟩
    have ha_mem : a ∈ M := haM (OrderIdeal.self_mem_principal a)
    have hφa : charValue M a = 0 :=
      charValue_eq_zero_of_mem M hMmax hMne ha_mem
    have hφ_apply : ∀ y : X, φ y = charValue M y := fun _ => rfl
    have hlinear : charValue M a = ‖x‖ - charValue M x := by
      dsimp [a]
      rw [show ((‖x‖ : ℝ) • AMSpaceWithUnit.unit - x : X) =
          (‖x‖ : ℝ) • AMSpaceWithUnit.unit + (-x) from sub_eq_add_neg _ _,
        charValue_add M hMmax hMne,
        charValue_smul M hMmax hMne,
        charValue_unit M hMmax hMne,
        show (-x : X) = (-1 : ℝ) • x from by rw [neg_smul, one_smul],
        charValue_smul M hMmax hMne]
      ring
    rw [hφ_apply x]
    linarith

/-- Every element of a non-trivial AM-space with unit attains its norm in
absolute value at a lattice character. -/
theorem exists_abs_apply_eq_norm [Nontrivial X] (x : X) :
    ∃ φ : LatticeCharacter X, |φ x| = ‖x‖ := by
  obtain ⟨φ, hφ⟩ := exists_apply_eq_norm_of_nonneg (X := X) (x := |x|) (abs_nonneg x)
  refine ⟨φ, ?_⟩
  rw [show |φ x| = φ |x| from (φ.toVecLatHom.map_abs x).symm, hφ, norm_abs_eq_norm]

end LatticeCharacter

end AMSpaceWithUnit
