/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.OrderClosures.BanLat.Substructures.Band.DisjointComplement
public import LeanPool.FBLOrderContinuity.BanLat.Substructures.Band.Lattice
public import LeanPool.FBLOrderContinuity.BanLat.Substructures.Band.Generated
public import LeanPool.OrderClosures.BanLat.Operators.Positive
public import LeanPool.OrderClosures.BanLat.Operators.Hom



/-!
# Projection bands

A band `B` in a vector lattice `X` is a **projection band** when every element
of `X` decomposes (uniquely) as a sum of an element of `B` and an element of
the disjoint complement `Bᵈ`. Equivalently, `X = B ⊕ Bᵈ` as a direct sum.

The associated **band projection** is the linear map sending `x` to its
component in `B`; it is an idempotent positive operator dominated by the
identity, and a vector lattice homomorphism. A linear operator `T` arises as a
band projection iff `T² = T` and `0 ≤ T ≤ I`.
-/

@[expose] public section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- A band `B` in a vector lattice is a **projection band** if every element
of `X` decomposes (uniquely) as a sum of an element of `B` and an element of
`Bᵈ`. Equivalently, `X = B ⊕ Bᵈ` as a direct sum. -/
structure ProjectionBand (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    extends Band X where
  decomposition' : ∀ x : X, ∃ y z : X, y ∈ carrier
    ∧ z ∈ disjointComplement carrier ∧ x = y + z

namespace ProjectionBand

instance : SetLike (ProjectionBand X) X where
  coe B := B.carrier
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h

variable (B : ProjectionBand X)

/-- Every element of `X` decomposes as `y + z` with `y ∈ B` and `z ∈ Bᵈ`. -/
theorem decomposition (x : X) :
    ∃ y z : X, y ∈ B ∧ z ∈ disjointComplement (B : Set X) ∧ x = y + z :=
  B.decomposition' x

/-- The decomposition in a projection band is unique. -/
theorem decomposition_unique {x y₁ z₁ y₂ z₂ : X}
    (hy₁ : y₁ ∈ B) (hz₁ : z₁ ∈ disjointComplement (B : Set X))
    (hy₂ : y₂ ∈ B) (hz₂ : z₂ ∈ disjointComplement (B : Set X))
    (h₁ : x = y₁ + z₁) (h₂ : x = y₂ + z₂) :
    y₁ = y₂ ∧ z₁ = z₂ := by
  -- y₁ - y₂ = z₂ - z₁, and this element lies in B ∩ Bᵈ ⊆ {0}
  have heq : y₁ - y₂ = z₂ - z₁ := by
    have h := h₁.symm.trans h₂
    calc y₁ - y₂ = (y₁ + z₁) - z₁ - y₂ := by abel
      _ = (y₂ + z₂) - z₁ - y₂ := by rw [h]
      _ = z₂ - z₁ := by abel
  have hmem_B : y₁ - y₂ ∈ B :=
    B.toBand.toOrderIdeal.toSubmodule.sub_mem hy₁ hy₂
  have hmem_Bd : y₁ - y₂ ∈ disjointComplement (B : Set X) := by
    rw [heq]
    exact (Band.disjointComplement
      (B : Set X)).toOrderIdeal.toSubmodule.sub_mem
      (show z₂ ∈ (Band.disjointComplement (B : Set X)).toOrderIdeal.toSubmodule
        from hz₂) hz₁
  have hmem_both : y₁ - y₂ ∈ (↑B) ∩ (↑B)ᵈ := ⟨hmem_B, hmem_Bd⟩
  have hzero : y₁ - y₂ = 0 :=
    Set.mem_singleton_iff.mp (disjointComplement_inter_eq_zero (↑B) hmem_both)
  refine ⟨sub_eq_zero.mp hzero, ?_⟩
  have : z₂ - z₁ = 0 := heq ▸ hzero
  exact eq_of_sub_eq_zero this |>.symm

/-- The **band projection** onto a projection band: the linear map sending
`x` to its component in `B`. -/
noncomputable def bandProjection : X →ₗ[ℝ] X where
  toFun x := (B.decomposition x).choose
  map_add' := fun x y => by
    set yx := (B.decomposition x).choose
    set zx := (B.decomposition x).choose_spec.choose
    set yy := (B.decomposition y).choose
    set zy := (B.decomposition y).choose_spec.choose
    set yxy := (B.decomposition (x + y)).choose
    set zxy := (B.decomposition (x + y)).choose_spec.choose
    have hyx : yx ∈ B := (B.decomposition x).choose_spec.choose_spec.1
    have hzx : zx ∈ (↑B)ᵈ := (B.decomposition x).choose_spec.choose_spec.2.1
    have hx_eq : x = yx + zx := (B.decomposition x).choose_spec.choose_spec.2.2
    have hyy : yy ∈ B := (B.decomposition y).choose_spec.choose_spec.1
    have hzy : zy ∈ (↑B)ᵈ := (B.decomposition y).choose_spec.choose_spec.2.1
    have hy_eq : y = yy + zy := (B.decomposition y).choose_spec.choose_spec.2.2
    have hyxy : yxy ∈ B := (B.decomposition (x + y)).choose_spec.choose_spec.1
    have hzxy : zxy ∈ (↑B)ᵈ :=
      (B.decomposition (x + y)).choose_spec.choose_spec.2.1
    have hxy_eq : x + y = yxy + zxy :=
      (B.decomposition (x + y)).choose_spec.choose_spec.2.2
    have hsum_B : yx + yy ∈ B := B.toBand.toOrderIdeal.toSubmodule.add_mem hyx hyy
    have hsum_Bd : zx + zy ∈ (↑B)ᵈ :=
      ((Band.disjointComplement (B : Set X)).toOrderIdeal).toSubmodule.add_mem
        (show zx ∈ ((Band.disjointComplement (B : Set X)).toOrderIdeal).toSubmodule from hzx)
        hzy
    have hsum_eq : x + y = (yx + yy) + (zx + zy) := by rw [hx_eq, hy_eq]; abel
    exact (B.decomposition_unique hyxy hzxy hsum_B hsum_Bd hxy_eq hsum_eq).1
  map_smul' := fun r x => by
    set yx := (B.decomposition x).choose
    set zx := (B.decomposition x).choose_spec.choose
    set yr := (B.decomposition (r • x)).choose
    set zr := (B.decomposition (r • x)).choose_spec.choose
    have hyx : yx ∈ B := (B.decomposition x).choose_spec.choose_spec.1
    have hzx : zx ∈ (↑B)ᵈ := (B.decomposition x).choose_spec.choose_spec.2.1
    have hx_eq : x = yx + zx := (B.decomposition x).choose_spec.choose_spec.2.2
    have hyr : yr ∈ B := (B.decomposition (r • x)).choose_spec.choose_spec.1
    have hzr : zr ∈ (↑B)ᵈ :=
      (B.decomposition (r • x)).choose_spec.choose_spec.2.1
    have hr_eq : r • x = yr + zr :=
      (B.decomposition (r • x)).choose_spec.choose_spec.2.2
    have hscal_B : r • yx ∈ B := B.toBand.toOrderIdeal.toSubmodule.smul_mem r hyx
    have hscal_Bd : r • zx ∈ (↑B)ᵈ :=
      ((Band.disjointComplement (B : Set X)).toOrderIdeal).toSubmodule.smul_mem r
        (show zx ∈ ((Band.disjointComplement (B : Set X)).toOrderIdeal).toSubmodule from hzx)
    have hscal_eq : r • x = r • yx + r • zx := by rw [hx_eq, smul_add]
    simp only [RingHom.id_apply]
    exact (B.decomposition_unique hyr hzr hscal_B hscal_Bd hr_eq hscal_eq).1

/-- The band projection is idempotent. -/
theorem bandProjection_sq :
    B.bandProjection ∘ₗ B.bandProjection = B.bandProjection := by
  ext x
  simp only [LinearMap.comp_apply]
  -- Bx ∈ B, and Bx = Bx + 0 with 0 ∈ Bᵈ
  have hBx_mem : B.bandProjection x ∈ B :=
    (B.decomposition x).choose_spec.choose_spec.1
  have hBBx_mem : B.bandProjection (B.bandProjection x) ∈ B :=
    (B.decomposition (B.bandProjection x)).choose_spec.choose_spec.1
  set z' := (B.decomposition (B.bandProjection x)).choose_spec.choose
  have hz' : z' ∈ disjointComplement (B : Set X) :=
    (B.decomposition (B.bandProjection x)).choose_spec.choose_spec.2.1
  have hBx_dec : B.bandProjection x =
      B.bandProjection (B.bandProjection x) + z' :=
    (B.decomposition (B.bandProjection x)).choose_spec.choose_spec.2.2
  have h0_mem : (0 : X) ∈ disjointComplement (B : Set X) :=
    ((Band.disjointComplement (B : Set X)).toOrderIdeal).toSubmodule.zero_mem
  have hBx_eq : B.bandProjection x = B.bandProjection x + 0 := (add_zero _).symm
  exact (B.decomposition_unique hBBx_mem hz' hBx_mem h0_mem hBx_dec hBx_eq).1

private theorem id_sub_bandProjection_mem' (x : X) :
    x - B.bandProjection x ∈ disjointComplement (B : Set X) := by
  have spec := (B.decomposition x).choose_spec.choose_spec
  have heq : x = B.bandProjection x + (B.decomposition x).choose_spec.choose :=
    spec.2.2
  have : x - B.bandProjection x = (B.decomposition x).choose_spec.choose :=
    (eq_sub_of_add_eq' heq.symm).symm
  rw [this]; exact spec.2.1

/-- The band projection is nonnegative as an operator: `0 ≤ B`. -/
theorem bandProjection_nonneg : 0 ≤ B.bandProjection := by
  rw [Positive.zero_le_iff]
  intro x hx
  set Bx := B.bandProjection x
  set Qx := x - Bx with hQx_def
  have hBx_mem : Bx ∈ B := (B.decomposition x).choose_spec.choose_spec.1
  have hQx_mem : Qx ∈ disjointComplement (B : Set X) := id_sub_bandProjection_mem' B x
  have hBxneg_mem_B : Bx⁻ ∈ B :=
    B.toBand.toOrderIdeal.solid (B.toBand.abs_mem hBx_mem)
      (negPart_nonneg Bx) (sup_le (neg_le_abs Bx) (abs_nonneg Bx))
  have hle_neg_Bx : -Bx ≤ Qx := by
    rw [neg_le_sub_iff_le_add]; exact le_add_of_nonneg_left hx
  have hle : Bx⁻ ≤ |Qx| :=
    le_trans (sup_le_sup_right hle_neg_Bx 0)
      (sup_le (le_abs_self Qx) (abs_nonneg Qx))
  have hQx_abs_mem : |Qx| ∈ disjointComplement (B : Set X) :=
    ((Band.disjointComplement (B : Set X)).toOrderIdeal).abs_mem hQx_mem
  have hBxneg_mem_Bd : Bx⁻ ∈ disjointComplement (B : Set X) :=
    ((Band.disjointComplement (B : Set X)).toOrderIdeal).solid
      hQx_abs_mem (negPart_nonneg Bx) hle
  have hzero : Bx⁻ = 0 :=
    Set.mem_singleton_iff.mp (disjointComplement_inter_eq_zero (↑B)
      ⟨hBxneg_mem_B, hBxneg_mem_Bd⟩)
  exact negPart_eq_zero.mp hzero

/-- The band projection is dominated by the identity as an operator: `B ≤ I`. -/
theorem bandProjection_le_id : B.bandProjection ≤ LinearMap.id := by
  rw [Positive.le_iff]
  intro x hx
  rw [← sub_nonneg]
  change 0 ≤ LinearMap.id x - B.bandProjection x
  set Bx := B.bandProjection x
  set Qx := x - Bx
  have hBx_mem : Bx ∈ B := (B.decomposition x).choose_spec.choose_spec.1
  have hQx_mem : Qx ∈ disjointComplement (B : Set X) :=
    id_sub_bandProjection_mem' B x
  have hQxneg_mem_Bd : Qx⁻ ∈ disjointComplement (B : Set X) :=
    ((Band.disjointComplement (B : Set X)).toOrderIdeal).solid
      (((Band.disjointComplement (B : Set X)).toOrderIdeal).abs_mem hQx_mem)
      (negPart_nonneg Qx) (sup_le (neg_le_abs Qx) (abs_nonneg Qx))
  have hle_neg_Qx : -Qx ≤ Bx := by
    change -(x - Bx) ≤ Bx; rw [neg_sub]; exact sub_le_self Bx (by exact hx)
  have hle : Qx⁻ ≤ |Bx| :=
    le_trans (sup_le_sup_right hle_neg_Qx 0)
      (sup_le (le_abs_self Bx) (abs_nonneg Bx))
  have hQxneg_mem_B : Qx⁻ ∈ B :=
    B.toBand.toOrderIdeal.solid (B.toBand.abs_mem hBx_mem) (negPart_nonneg Qx) hle
  have hzero : Qx⁻ = 0 :=
    Set.mem_singleton_iff.mp (disjointComplement_inter_eq_zero (↑B)
      ⟨hQxneg_mem_B, hQxneg_mem_Bd⟩)
  exact negPart_eq_zero.mp hzero

/-- The band projection maps into the band. -/
theorem bandProjection_mem (x : X) :
    B.bandProjection x ∈ B := by
  exact (B.decomposition x).choose_spec.choose_spec.1

/-- The complement `I - B` maps into the disjoint complement. -/
theorem id_sub_bandProjection_mem (x : X) :
    x - B.bandProjection x ∈ disjointComplement (B : Set X) := by
  set y := (B.decomposition x).choose
  set z := (B.decomposition x).choose_spec.choose
  have hz : z ∈ disjointComplement (B : Set X) :=
    (B.decomposition x).choose_spec.choose_spec.2.1
  have hxyz : x = y + z :=
    (B.decomposition x).choose_spec.choose_spec.2.2
  have : x - B.bandProjection x = z := by
    change x - y = z; rw [hxyz, add_sub_cancel_left]
  rw [this]; exact hz

/-- A band projection acts as the identity on elements already in the band. -/
theorem bandProjection_eq_of_mem {x : X} (hx : x ∈ B) :
    B.bandProjection x = x := by
  have h0_mem : (0 : X) ∈ disjointComplement (B : Set X) :=
    ((Band.disjointComplement (B : Set X)).toOrderIdeal).toSubmodule.zero_mem
  have hQx_mem : x - B.bandProjection x ∈ disjointComplement (B : Set X) :=
    id_sub_bandProjection_mem' B x
  have hx_dec : x = B.bandProjection x + (x - B.bandProjection x) := by abel
  exact (B.decomposition_unique (B.bandProjection_mem x) hQx_mem
    hx h0_mem hx_dec (add_zero x).symm).1

/-- The range of the band projection is the band itself. -/
theorem range_bandProjection :
    Set.range B.bandProjection = (B : Set X) := by
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact B.bandProjection_mem y
  · intro hx; exact ⟨x, B.bandProjection_eq_of_mem hx⟩

/-- The band projection vanishes on elements of the disjoint complement. -/
theorem bandProjection_eq_zero_of_mem_dc {x : X}
    (hx : x ∈ disjointComplement (B : Set X)) :
    B.bandProjection x = 0 := by
  have h0_mem : (0 : X) ∈ (B : Set X) := B.toBand.toOrderIdeal.toSubmodule.zero_mem
  have hdec : x = B.bandProjection x + (x - B.bandProjection x) := by abel
  exact (B.decomposition_unique (B.bandProjection_mem x)
    (B.id_sub_bandProjection_mem x) h0_mem hx hdec (zero_add x).symm).1

/-- The disjoint complement of a projection band is a projection band. -/
def disjointComplementProjectionBand : ProjectionBand X where
  toBand := Band.disjointComplement (B : Set X)
  decomposition' := fun x => ⟨x - B.bandProjection x, B.bandProjection x,
    (show x - B.bandProjection x ∈ ((B : Set X))ᵈ from B.id_sub_bandProjection_mem x),
    (show B.bandProjection x ∈ ((B : Set X))ᵈᵈ from
      subset_disjointComplement_disjointComplement (B : Set X) (B.bandProjection_mem x)),
    by abel⟩

/-- An ideal `J` is a projection band iff `J + Jᵈ = X`. -/
theorem projectionBand_iff_add_disjointComplement
    (J : OrderIdeal X) :
    (∃ B : ProjectionBand X, (B : Set X) = (J : Set X)) ↔
      ∀ x : X, ∃ y z : X, y ∈ (J : Set X)
        ∧ z ∈ disjointComplement (J : Set X) ∧ x = y + z := by
  constructor
  · rintro ⟨B, hBJ⟩ x
    obtain ⟨y, z, hy, hz, hxyz⟩ := B.decomposition x
    exact ⟨y, z, hBJ ▸ hy, hBJ ▸ hz, hxyz⟩
  · intro hdecomp
    have heq : ((J : Set X)ᵈ)ᵈ = (J : Set X) := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨y, z, hy, hz, hxyz⟩ := hdecomp x
        have hy_dd : y ∈ ((J : Set X)ᵈ)ᵈ :=
          subset_disjointComplement_disjointComplement (J : Set X) hy
        have hxmy_dd : x - y ∈ ((J : Set X)ᵈ)ᵈ :=
          ((Band.disjointComplement ((J : Set X)ᵈ)).toOrderIdeal).toSubmodule.sub_mem
            hx hy_dd
        have hxmy_both : x - y ∈ (J : Set X)ᵈ ∩ ((J : Set X)ᵈ)ᵈ :=
          ⟨(hxyz ▸ add_sub_cancel_left y z : x - y = z) ▸ hz, hxmy_dd⟩
        rwa [sub_eq_zero.mp (Set.mem_singleton_iff.mp
          (disjointComplement_inter_eq_zero ((J : Set X)ᵈ) hxmy_both))]
      · exact subset_disjointComplement_disjointComplement (J : Set X)
    exact ⟨{
      toBand := Band.ofPosDirectedSSupMem J
        (fun S hS _hpos _hdir hne x hx => by
          have hS_dd : S ⊆ ((J : Set X)ᵈ)ᵈ := fun s hs =>
            subset_disjointComplement_disjointComplement (J : Set X) (hS hs)
          have hx_dd := (Band.disjointComplement ((J : Set X)ᵈ)).sSup_mem
            hS_dd hne hx
          change x ∈ ((J : Set X)ᵈ)ᵈ at hx_dd
          rw [heq] at hx_dd; exact hx_dd)
      decomposition' := hdecomp }, rfl⟩

/-- If `X = J₁ ⊕ J₂` where `J₁` and `J₂` are ideals with `J₁ ⊥ J₂`, then
both are projection bands and `J₂ = J₁ᵈ`. -/
theorem of_direct_sum_of_disjoint (J₁ J₂ : OrderIdeal X)
    (hperp : ∀ x ∈ (J₁ : Set X), ∀ y ∈ (J₂ : Set X), IsVLDisjoint x y)
    (hdecomp : ∀ x : X, ∃ y ∈ (J₁ : Set X), ∃ z ∈ (J₂ : Set X),
      x = y + z) :
    disjointComplement (J₁ : Set X) = (J₂ : Set X)
      ∧ ∃ B : ProjectionBand X, (B : Set X) = (J₁ : Set X) := by
  have hJ₂_sub : (J₂ : Set X) ⊆ ((J₁ : Set X))ᵈ := fun z hz a ha =>
    isVLDisjoint_comm.mpr (hperp a ha z hz)
  have hJ₁d_sub : ((J₁ : Set X))ᵈ ⊆ (J₂ : Set X) := by
    intro z hz
    obtain ⟨y, hy, w, hw, hzyw⟩ := hdecomp z
    have hw_d : w ∈ ((J₁ : Set X))ᵈ := hJ₂_sub hw
    have hy_d : y ∈ ((J₁ : Set X))ᵈ := by
      have : y = z - w := by rw [hzyw]; abel
      rw [this]
      exact ((Band.disjointComplement (J₁ : Set X)).toOrderIdeal).toSubmodule.sub_mem
        (show z ∈ ((Band.disjointComplement (J₁ : Set X)).toOrderIdeal).toSubmodule
          from hz) hw_d
    have hy_zero : y = 0 := Set.mem_singleton_iff.mp
      (disjointComplement_inter_eq_zero (J₁ : Set X) ⟨hy, hy_d⟩)
    rw [hy_zero, zero_add] at hzyw; rwa [hzyw]
  refine ⟨Set.Subset.antisymm hJ₁d_sub hJ₂_sub, ?_⟩
  have hdecomp' : ∀ x : X, ∃ y z : X, y ∈ (J₁ : Set X)
      ∧ z ∈ disjointComplement (J₁ : Set X) ∧ x = y + z := fun x => by
    obtain ⟨y, hy, z, hz, hxyz⟩ := hdecomp x
    exact ⟨y, z, hy, hJ₂_sub hz, hxyz⟩
  exact (projectionBand_iff_add_disjointComplement J₁).mpr hdecomp'

/-! ### Characterisation of band projections -/

private theorem bpi_monotone {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x) {x y : X} (hxy : x ≤ y) :
    T x ≤ T y := by
  have : 0 ≤ T (y - x) := hpos _ (sub_nonneg.mpr hxy)
  rwa [map_sub, sub_nonneg] at this

/-- Range and kernel have disjoint positive cones. -/
private theorem bpi_pos_cone_disjoint {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {y z : X} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hTy : T y = y) (hTz : T z = 0) :
    y ⊓ z = 0 := by
  have hyz_nn : 0 ≤ y ⊓ z := le_inf hy hz
  have hT_yz_le_z : T (y ⊓ z) ≤ T z := bpi_monotone hpos inf_le_right
  rw [hTz] at hT_yz_le_z
  have hT_yz_zero : T (y ⊓ z) = 0 := le_antisymm hT_yz_le_z (hpos _ hyz_nn)
  -- Apply the same argument to `I - T`, which is positive and dominated by the identity.
  have hIT_mono : ∀ {a b : X}, a ≤ b → a - T a ≤ b - T b := fun {a b} hab => by
    have h1 : 0 ≤ (b - a) - T (b - a) := sub_nonneg.mpr
      (hle (b - a) (sub_nonneg.mpr hab))
    rw [map_sub] at h1
    -- h1 : 0 ≤ (b - a) - (T b - T a) = (b - T b) - (a - T a)
    rwa [show (b - a) - (T b - T a) = (b - T b) - (a - T a) by abel,
         sub_nonneg] at h1
  have : y ⊓ z ≤ 0 := by
    calc y ⊓ z = (y ⊓ z) - T (y ⊓ z) := by rw [hT_yz_zero, sub_zero]
      _ ≤ y - T y := hIT_mono inf_le_left
      _ = 0 := by rw [hTy, sub_self]
  exact le_antisymm this hyz_nn

/-- If `T w = w` then `T(w⁺) = w⁺` and `T(w⁻) = w⁻`. -/
private theorem bpi_preserves_parts {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {w : X} (hTw : T w = w) :
    T w⁺ = w⁺ ∧ T w⁻ = w⁻ := by
  have hTwp_le : T w⁺ ≤ w⁺ := hle w⁺ (posPart_nonneg w)
  have hTwn_le : T w⁻ ≤ w⁻ := hle w⁻ (negPart_nonneg w)
  have hdiff : T w⁺ - T w⁻ = w⁺ - w⁻ := by
    rw [← map_sub, posPart_sub_negPart, hTw]
  have hTdisj : T w⁺ ⊓ T w⁻ = 0 :=
    le_antisymm (le_trans (inf_le_inf hTwp_le hTwn_le)
      (le_of_eq (posPart_inf_negPart_eq_zero w)))
      (le_inf (hpos w⁺ (posPart_nonneg w)) (hpos w⁻ (negPart_nonneg w)))
  exact isVLDisjoint_decomposition_unique
    (hpos w⁺ (posPart_nonneg w)) (hpos w⁻ (negPart_nonneg w))
    (posPart_nonneg w) (negPart_nonneg w)
    (isVLDisjoint_of_inf_eq_zero hTdisj)
    (isVLDisjoint_of_inf_eq_zero (posPart_inf_negPart_eq_zero w))
    hdiff

/-- If `T w = w` then `T |w| = |w|`. -/
private theorem bpi_preserves_abs {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {w : X} (hTw : T w = w) : T |w| = |w| := by
  rw [show |w| = w⁺ + w⁻ from (posPart_add_negPart w).symm, map_add,
    (bpi_preserves_parts hpos hle hTw).1, (bpi_preserves_parts hpos hle hTw).2]

/-- Solidity of the range: if `T x = x`, `0 ≤ y ≤ x`, then `T y = y`. -/
private theorem bpi_range_solid {T : X →ₗ[ℝ] X}
    (hTT : T ∘ₗ T = T) (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {x y : X} (hx_fixed : T x = x) (hy_nn : 0 ≤ y) (hyx : y ≤ x) :
    T y = y := by
  have hTy_le_y : T y ≤ y := hle y hy_nn
  have hd_nn : 0 ≤ y - T y := sub_nonneg.mpr hTy_le_y
  have hd_le_x : y - T y ≤ x := le_trans (sub_le_self y (hpos y hy_nn)) hyx
  have hx_nn : 0 ≤ x := le_trans hy_nn hyx
  have hres : T (y - T y) = 0 := by
    have : T (T y) = T y := LinearMap.congr_fun hTT y
    rw [map_sub, this, sub_self]
  have hdisjoint := bpi_pos_cone_disjoint hpos hle hx_nn hd_nn hx_fixed hres
  have hle_zero : y - T y ≤ 0 := by
    calc y - T y ≤ x ⊓ (y - T y) := le_inf hd_le_x le_rfl
      _ = 0 := hdisjoint
  exact eq_of_sub_eq_zero (le_antisymm hle_zero hd_nn) |>.symm

/-- The range `{x | T x = x}` is an `OrderIdeal`. -/
private noncomputable def bpi_rangeIdeal {T : X →ₗ[ℝ] X}
    (hTT : T ∘ₗ T = T) (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x) : OrderIdeal X :=
  OrderIdeal.ofSolid
    { carrier := {x | T x = x}
      add_mem' := fun {a b} (ha : T a = a) (hb : T b = b) =>
        show T (a + b) = a + b by rw [map_add, ha, hb]
      zero_mem' := map_zero T
      smul_mem' := fun r a (ha : T a = a) =>
        show T (r • a) = r • a by rw [map_smul, ha] }
    (fun a b (ha : T a = a) hab => by
      change T b = b
      have ha_abs : T |a| = |a| := bpi_preserves_abs hpos hle ha
      have hb_abs : T |b| = |b| :=
        bpi_range_solid hTT hpos hle ha_abs (abs_nonneg b) hab
      have hTyp : T b⁺ = b⁺ := bpi_range_solid hTT hpos hle hb_abs
        (posPart_nonneg b) (sup_le (le_abs_self b) (abs_nonneg b))
      have hTyn : T b⁻ = b⁻ := bpi_range_solid hTT hpos hle hb_abs
        (negPart_nonneg b) (sup_le (neg_le_abs b) (abs_nonneg b))
      calc T b = T (b⁺ - b⁻) := by rw [posPart_sub_negPart]
        _ = T b⁺ - T b⁻ := map_sub T b⁺ b⁻
        _ = b⁺ - b⁻ := by rw [hTyp, hTyn]
        _ = b := posPart_sub_negPart b)

/-- The kernel `{x | T x = 0}` is an `OrderIdeal`. -/
private noncomputable def bpi_kernelIdeal {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x) : OrderIdeal X :=
  OrderIdeal.ofSolid
    { carrier := {x | T x = 0}
      add_mem' := fun {a b} (ha : T a = 0) (hb : T b = 0) =>
        show T (a + b) = 0 by rw [map_add, ha, hb, add_zero]
      zero_mem' := map_zero T
      smul_mem' := fun r a (ha : T a = 0) =>
        show T (r • a) = 0 by rw [map_smul, ha, smul_zero] }
    (fun a b (ha : T a = 0) hab => by
      change T b = 0
      -- From T a = 0 derive T|a| = 0 via T a⁺ = T a⁻ and disjointness
      have hTxp_le : T a⁺ ≤ a⁺ := hle a⁺ (posPart_nonneg a)
      have hTxn_le : T a⁻ ≤ a⁻ := hle a⁻ (negPart_nonneg a)
      have hTdiff : T a⁺ - T a⁻ = 0 := by
        rw [← map_sub, posPart_sub_negPart]; exact ha
      have heq : T a⁺ = T a⁻ := sub_eq_zero.mp hTdiff
      have hTxp_zero : T a⁺ = 0 := by
        apply le_antisymm _ (hpos a⁺ (posPart_nonneg a))
        calc T a⁺ ≤ a⁺ ⊓ T a⁺ := le_inf hTxp_le le_rfl
          _ ≤ a⁺ ⊓ a⁻ := inf_le_inf_left a⁺ (heq ▸ hTxn_le)
          _ = 0 := posPart_inf_negPart_eq_zero a
      have hTxn_zero : T a⁻ = 0 := heq ▸ hTxp_zero
      have hTabsa : T |a| = 0 := by
        rw [show |a| = a⁺ + a⁻ from (posPart_add_negPart a).symm,
            map_add, hTxp_zero, hTxn_zero, add_zero]
      -- T|b| ≤ T|a| = 0 by monotonicity
      have hTabsb : T |b| = 0 :=
        le_antisymm (le_trans (bpi_monotone hpos hab) (le_of_eq hTabsa))
          (hpos |b| (abs_nonneg b))
      -- T b⁺, T b⁻ ≤ T|b| = 0
      have hTyp : T b⁺ = 0 :=
        le_antisymm (le_trans (bpi_monotone hpos
          (sup_le (le_abs_self b) (abs_nonneg b))) (le_of_eq hTabsb))
          (hpos b⁺ (posPart_nonneg b))
      have hTyn : T b⁻ = 0 :=
        le_antisymm (le_trans (bpi_monotone hpos
          (sup_le (neg_le_abs b) (abs_nonneg b))) (le_of_eq hTabsb))
          (hpos b⁻ (negPart_nonneg b))
      calc T b = T (b⁺ - b⁻) := by rw [posPart_sub_negPart]
        _ = T b⁺ - T b⁻ := map_sub T b⁺ b⁻
        _ = 0 := by rw [hTyp, hTyn, sub_self])

/-- Range and kernel are VL-disjoint. -/
private theorem bpi_range_kernel_disjoint {T : X →ₗ[ℝ] X}
    (hTT : T ∘ₗ T = T) (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    (u : X) (hu : u ∈ (bpi_rangeIdeal hTT hpos hle : Set X))
    (v : X) (hv : v ∈ (bpi_kernelIdeal hpos hle : Set X)) :
    IsVLDisjoint u v := by
  change T u = u at hu; change T v = 0 at hv
  have hu_abs : T |u| = |u| := bpi_preserves_abs hpos hle hu
  have hv_abs : T |v| = 0 :=
    show |v| ∈ (bpi_kernelIdeal hpos hle : Set X) from
      (bpi_kernelIdeal hpos hle).abs_mem hv
  change |u| ⊓ |v| = 0
  exact bpi_pos_cone_disjoint (y := |u|) (z := |v|) hpos hle
    (abs_nonneg u) (abs_nonneg v) hu_abs hv_abs

/-- A linear operator is a band projection iff `T² = T` and `0 ≤ T ≤ id`. -/
theorem bandProjection_iff (T : X →ₗ[ℝ] X) :
    (∃ B : ProjectionBand X, B.bandProjection = T) ↔
      T ∘ₗ T = T ∧ 0 ≤ T ∧ T ≤ LinearMap.id := by
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.bandProjection_sq, B.bandProjection_nonneg, B.bandProjection_le_id⟩
  · -- The converse requires showing Range(T) is a projection band
    rintro ⟨hTT, hpos₀, hle₀⟩
    have hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x := Positive.zero_le_iff.mp hpos₀
    have hle : ∀ x : X, 0 ≤ x → T x ≤ x := fun x hx => Positive.le_iff.mp hle₀ x hx
    set R := bpi_rangeIdeal hTT hpos hle
    set K := bpi_kernelIdeal hpos hle
    -- R and K are disjoint and decompose X
    have hperp : ∀ u ∈ (R : Set X), ∀ v ∈ (K : Set X),
        IsVLDisjoint u v :=
      bpi_range_kernel_disjoint hTT hpos hle
    have hdecomp : ∀ x : X, ∃ y ∈ (R : Set X), ∃ z ∈ (K : Set X),
        x = y + z := fun x => by
      refine ⟨T x, ?_, x - T x, ?_, ?_⟩
      · change T (T x) = T x; exact LinearMap.congr_fun hTT x
      · change T (x - T x) = 0
        have : T (T x) = T x := LinearMap.congr_fun hTT x
        rw [map_sub, this, sub_self]
      · abel
    obtain ⟨hdc, B, hBset⟩ := of_direct_sum_of_disjoint R K hperp hdecomp
    refine ⟨B, ?_⟩
    ext x
    -- B.bandProjection x and T x are both the R-component of x
    have hTx_B : T x ∈ (B : Set X) := by
      rw [hBset]; change T (T x) = T x; exact LinearMap.congr_fun hTT x
    have hQx_Bd : x - T x ∈ disjointComplement (B : Set X) := by
      rw [hBset, hdc]
      change T (x - T x) = 0
      have : T (T x) = T x := LinearMap.congr_fun hTT x
      rw [map_sub, this, sub_self]
    have hBx_dec : x = B.bandProjection x + (x - B.bandProjection x) := by
      abel
    have hTx_dec : x = T x + (x - T x) := by abel
    exact (B.decomposition_unique (B.bandProjection_mem x)
      (B.id_sub_bandProjection_mem x) hTx_B hQx_Bd hBx_dec hTx_dec).1

/-- A band projection is a lattice homomorphism. -/
theorem bandProjection_isVecLatHom :
    IsVecLatHom B.bandProjection.toFun := by
  have hpos : Positive B.bandProjection := Positive.zero_le_iff.mp B.bandProjection_nonneg
  have hle : ∀ x : X, 0 ≤ x → B.bandProjection x ≤ x :=
    fun x hx => Positive.le_iff.mp B.bandProjection_le_id x hx
  apply IsVecLatHom.of_disjoint
  · exact B.bandProjection.isLinear
  · intro x y hxy
    have hx : 0 ≤ x := hxy ▸ inf_le_left
    have hy : 0 ≤ y := hxy ▸ inf_le_right
    apply le_antisymm
    · calc B.bandProjection x ⊓ B.bandProjection y
          ≤ x ⊓ y := inf_le_inf (hle x hx) (hle y hy)
        _ = 0 := hxy
    · exact le_inf (hpos _ hx) (hpos _ hy)

/-! ### Band projection lemmas -/

/-- A band projection sends every band to itself: for any band `J` and any
projection band `B`, if `x ∈ J` then `B.bandProjection x ∈ J`. -/
private lemma bandProjection_mem_band (B : ProjectionBand X) (J : Band X)
    {x : X} (hx : x ∈ J) : B.bandProjection x ∈ J := by
  have hpos : ∀ y, 0 ≤ y → y ∈ J → B.bandProjection y ∈ J := fun y hy hyJ =>
    J.solid hyJ
      (Positive.zero_le_iff.mp B.bandProjection_nonneg y hy)
      (Positive.le_iff.mp B.bandProjection_le_id y hy)
  have habs : |x| ∈ J := J.abs_mem hx
  have hxp : x⁺ ∈ J :=
    J.solid habs (posPart_nonneg x) (sup_le (le_abs_self x) (abs_nonneg x))
  have hxn : x⁻ ∈ J :=
    J.solid habs (negPart_nonneg x) (sup_le (neg_le_abs x) (abs_nonneg x))
  have heq : B.bandProjection x =
      B.bandProjection x⁺ - B.bandProjection x⁻ := by
    rw [← map_sub, posPart_sub_negPart]
  rw [heq]
  exact J.toOrderIdeal.toSubmodule.sub_mem
    (hpos _ (posPart_nonneg x) hxp) (hpos _ (negPart_nonneg x) hxn)

/-- An element disjoint from two bands is disjoint from their supremum. -/
private lemma mem_disjointComplement_band_sup {B₁ B₂ : Band X} {z : X}
    (h₁ : z ∈ disjointComplement (B₁ : Set X))
    (h₂ : z ∈ disjointComplement (B₂ : Set X)) :
    z ∈ disjointComplement ((B₁ ⊔ B₂ : Band X) : Set X) := by
  intro a ha
  have hle : B₁ ⊔ B₂ ≤ Band.disjointComplement {z} :=
    sup_le
      (fun b hb c hc => by rcases hc with rfl; exact isVLDisjoint_comm.mp (h₁ b hb))
      (fun b hb c hc => by rcases hc with rfl; exact isVLDisjoint_comm.mp (h₂ b hb))
  exact isVLDisjoint_comm.mp (hle ha z rfl)

/-! ### Lattice structure of projection bands

Projection bands of `X`, ordered by inclusion, form a Boolean algebra. The
order, top, and bottom are inherited from the lattice of bands; binary infima
are given by intersection, binary suprema set-theoretically by the algebraic
sum `B₁ + B₂ = {y + z : y ∈ B₁, z ∈ B₂}`, and the complement is the disjoint
complement. -/

/-- Projection bands inherit the partial order by inclusion from `SetLike`. -/
instance : PartialOrder (ProjectionBand X) := .ofSetLike (ProjectionBand X)

/-- The whole space `X` is a projection band. -/
instance : Top (ProjectionBand X) where
  top :=
    { toBand := (⊤ : Band X)
      decomposition' := fun x => ⟨x, 0,
        show x ∈ ((⊤ : Band X) : Set X) from Band.mem_top,
        fun a _ => isVLDisjoint_zero_left a, (add_zero x).symm⟩ }

@[simp] theorem mem_top {x : X} : x ∈ (⊤ : ProjectionBand X) :=
  show x ∈ ((⊤ : Band X) : Set X) from Band.mem_top

/-- The trivial band `{0}` is a projection band. -/
instance : Bot (ProjectionBand X) where
  bot :=
    { toBand := (⊥ : Band X)
      decomposition' := fun x => ⟨0, x,
        show (0 : X) ∈ ((⊥ : Band X) : Set X) from
          (⊥ : Band X).toOrderIdeal.toSubmodule.zero_mem,
        fun a ha => by
          have ha0 : a = 0 := Band.mem_bot.mp ha
          rw [ha0]; exact isVLDisjoint_zero_right x,
        (zero_add x).symm⟩ }

@[simp] theorem mem_bot {x : X} : x ∈ (⊥ : ProjectionBand X) ↔ x = 0 :=
  show x ∈ ((⊥ : Band X) : Set X) ↔ x = 0 from Band.mem_bot

/-- The disjoint complement of a projection band, again a projection band. -/
instance : Compl (ProjectionBand X) where
  compl B := B.disjointComplementProjectionBand

/-- The complement projection band has the expected underlying disjoint complement. -/
theorem coe_compl (B : ProjectionBand X) :
    ((Bᶜ : ProjectionBand X) : Set X) = ((B : Set X))ᵈ := rfl

/-- Binary infimum of projection bands: the set-theoretic intersection. -/
instance : Min (ProjectionBand X) where
  min B₁ B₂ :=
    { toBand := B₁.toBand ⊓ B₂.toBand
      decomposition' := fun x => by
        refine ⟨B₂.bandProjection (B₁.bandProjection x),
          x - B₂.bandProjection (B₁.bandProjection x),
          ⟨bandProjection_mem_band B₂ B₁.toBand (B₁.bandProjection_mem x),
            B₂.bandProjection_mem _⟩, ?_, by abel⟩
        intro a ha
        have ha₁ : a ∈ (B₁ : Set X) := ha.1
        have ha₂ : a ∈ (B₂ : Set X) := ha.2
        have hsplit : x - B₂.bandProjection (B₁.bandProjection x)
            = (x - B₁.bandProjection x) +
              (B₁.bandProjection x - B₂.bandProjection (B₁.bandProjection x)) := by
          abel
        rw [hsplit]
        exact (B₁.id_sub_bandProjection_mem x a ha₁).add_left
          (B₂.id_sub_bandProjection_mem (B₁.bandProjection x) a ha₂) }

/-- Binary supremum of projection bands: the algebraic sum
`{y + z : y ∈ B₁, z ∈ B₂}`. -/
instance : Max (ProjectionBand X) where
  max B₁ B₂ :=
    { toBand := B₁.toBand ⊔ B₂.toBand
      decomposition' := fun x => by
        set p := B₁.bandProjection x with hp_def
        set q := B₂.bandProjection (x - p) with hq_def
        refine ⟨p + q, x - (p + q), ?_, ?_, by abel⟩
        · -- p + q ∈ B₁.toBand ⊔ B₂.toBand
          have hp : p ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
            (le_sup_left : B₁.toBand ≤ _) (B₁.bandProjection_mem x)
          have hq : q ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
            (le_sup_right : B₂.toBand ≤ _) (B₂.bandProjection_mem _)
          exact (B₁.toBand ⊔ B₂.toBand).toOrderIdeal.toSubmodule.add_mem hp hq
        · -- x - (p + q) ∈ disjointComplement
          have hxmp : x - p ∈ disjointComplement (B₁ : Set X) :=
            B₁.id_sub_bandProjection_mem x
          have hq_B₁d : q ∈ disjointComplement (B₁ : Set X) :=
            bandProjection_mem_band B₂
              (Band.disjointComplement (B₁ : Set X)) hxmp
          have hxpq_B₁d : x - (p + q) ∈ disjointComplement (B₁ : Set X) := by
            have heq : x - (p + q) = (x - p) - q := by abel
            rw [heq]
            exact (Band.disjointComplement (B₁ : Set X)).toOrderIdeal.toSubmodule.sub_mem
              hxmp hq_B₁d
          have hxpq_B₂d : x - (p + q) ∈ disjointComplement (B₂ : Set X) := by
            have heq : x - (p + q) = (x - p) - q := by abel
            rw [heq]
            exact B₂.id_sub_bandProjection_mem (x - p)
          exact mem_disjointComplement_band_sup hxpq_B₁d hxpq_B₂d }

@[simp] theorem inf_toBand (B₁ B₂ : ProjectionBand X) :
    (B₁ ⊓ B₂).toBand = B₁.toBand ⊓ B₂.toBand := rfl

@[simp] theorem sup_toBand (B₁ B₂ : ProjectionBand X) :
    (B₁ ⊔ B₂).toBand = B₁.toBand ⊔ B₂.toBand := rfl

/-- For two projection bands, the supremum of their underlying bands coincides
with the set of algebraic sums `{y + z : y ∈ B₁, z ∈ B₂}`. -/
theorem coe_band_sup_eq_add (B₁ B₂ : ProjectionBand X) :
    ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X)
      = {x | ∃ y ∈ (B₁ : Set X), ∃ z ∈ (B₂ : Set X), x = y + z} := by
  ext x
  refine ⟨fun hx => ?_, ?_⟩
  · set p := B₁.bandProjection x with hp_def
    set q := B₂.bandProjection (x - p) with hq_def
    refine ⟨p, B₁.bandProjection_mem x, q, B₂.bandProjection_mem _, ?_⟩
    have hxmp : x - p ∈ disjointComplement (B₁ : Set X) :=
      B₁.id_sub_bandProjection_mem x
    have hq_B₁d : q ∈ disjointComplement (B₁ : Set X) :=
      bandProjection_mem_band B₂
        (Band.disjointComplement (B₁ : Set X)) hxmp
    have hxpq_B₁d : x - (p + q) ∈ disjointComplement (B₁ : Set X) := by
      have heq : x - (p + q) = (x - p) - q := by abel
      rw [heq]
      exact (Band.disjointComplement (B₁ : Set X)).toOrderIdeal.toSubmodule.sub_mem
        hxmp hq_B₁d
    have hxpq_B₂d : x - (p + q) ∈ disjointComplement (B₂ : Set X) := by
      have heq : x - (p + q) = (x - p) - q := by abel
      rw [heq]
      exact B₂.id_sub_bandProjection_mem (x - p)
    have hxpq_supd : x - (p + q) ∈
        disjointComplement ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
      mem_disjointComplement_band_sup hxpq_B₁d hxpq_B₂d
    have hxpq_sup : x - (p + q) ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) := by
      have hp_sup : p ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
        (le_sup_left : B₁.toBand ≤ _) (B₁.bandProjection_mem x)
      have hq_sup : q ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
        (le_sup_right : B₂.toBand ≤ _) (B₂.bandProjection_mem _)
      exact (B₁.toBand ⊔ B₂.toBand).toOrderIdeal.toSubmodule.sub_mem hx
        ((B₁.toBand ⊔ B₂.toBand).toOrderIdeal.toSubmodule.add_mem hp_sup hq_sup)
    have hzero : x - (p + q) = 0 :=
      Set.mem_singleton_iff.mp
        (disjointComplement_inter_eq_zero _ ⟨hxpq_sup, hxpq_supd⟩)
    exact (sub_eq_zero.mp hzero)
  · rintro ⟨y, hy, z, hz, rfl⟩
    have hy_sup : y ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
      (le_sup_left : B₁.toBand ≤ _) hy
    have hz_sup : z ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
      (le_sup_right : B₂.toBand ≤ _) hz
    exact (B₁.toBand ⊔ B₂.toBand).toOrderIdeal.toSubmodule.add_mem hy_sup hz_sup

/-- Projection bands of `X`, ordered by inclusion, form a Boolean algebra.
The binary lattice operations are intersection and algebraic sum, top and
bottom are the whole space and the trivial band `{0}`, and the complement is
the disjoint complement. -/
instance : BooleanAlgebra (ProjectionBand X) where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  le_sup_left B₁ B₂ x hx := (le_sup_left : B₁.toBand ≤ B₁.toBand ⊔ B₂.toBand) hx
  le_sup_right B₁ B₂ x hx := (le_sup_right : B₂.toBand ≤ B₁.toBand ⊔ B₂.toBand) hx
  sup_le B₁ B₂ K h₁ h₂ x hx :=
    (sup_le (show B₁.toBand ≤ K.toBand from h₁)
      (show B₂.toBand ≤ K.toBand from h₂)) hx
  inf_le_left _ _ _ h := h.1
  inf_le_right _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ hx := ⟨h₁ hx, h₂ hx⟩
  le_sup_inf := fun B B₁ B₂ t ht => by
    obtain ⟨ht_BB₁, ht_BB₂⟩ := ht
    set p := B.bandProjection t with hp_def
    have hp_B : p ∈ B := B.bandProjection_mem t
    have hcomp : ∀ (J : ProjectionBand X), t ∈ ((B.toBand ⊔ J.toBand : Band X) : Set X) →
        t - p ∈ J := fun J ht_BJ => by
      rw [coe_band_sup_eq_add B J] at ht_BJ
      obtain ⟨b, hbB, a, haJ, htba⟩ := ht_BJ
      have hpa : p = b + B.bandProjection a := by
        rw [hp_def, htba, map_add, B.bandProjection_eq_of_mem hbB]
      have hq_eq : t - p = a - B.bandProjection a := by rw [htba, hpa]; abel
      rw [hq_eq]
      exact J.toBand.toOrderIdeal.toSubmodule.sub_mem haJ
        (bandProjection_mem_band B J.toBand haJ)
    have hq_B₁ : t - p ∈ B₁ := hcomp B₁ ht_BB₁
    have hq_B₂ : t - p ∈ B₂ := hcomp B₂ ht_BB₂
    change t ∈ ((B.toBand ⊔ (B₁.toBand ⊓ B₂.toBand) : Band X) : Set X)
    rw [show (B₁.toBand ⊓ B₂.toBand : Band X) = (B₁ ⊓ B₂).toBand from rfl,
        coe_band_sup_eq_add B (B₁ ⊓ B₂)]
    exact ⟨p, hp_B, t - p, ⟨hq_B₁, hq_B₂⟩, by abel⟩
  top := ⊤
  bot := ⊥
  le_top _ _ _ := Submodule.mem_top
  bot_le B x hx := by
    rw [mem_bot.mp hx]; exact B.toBand.toOrderIdeal.toSubmodule.zero_mem
  compl := (·ᶜ)
  inf_compl_le_bot := fun B x hx => by
    have hx0 : x = 0 := Set.mem_singleton_iff.mp
      (disjointComplement_inter_eq_zero (B : Set X) ⟨hx.1, hx.2⟩)
    exact mem_bot.mpr hx0
  top_le_sup_compl := fun B x _ => by
    obtain ⟨y, z, hy, hz, heq⟩ := B.decomposition x
    change x ∈ ((B.toBand ⊔ Bᶜ.toBand : Band X) : Set X)
    rw [coe_band_sup_eq_add B Bᶜ]
    exact ⟨y, hy, z, hz, heq⟩
  sdiff B₁ B₂ := B₁ ⊓ B₂ᶜ
  himp B₁ B₂ := B₂ ⊔ B₁ᶜ

/-! ### Band projections of associated lattice operations -/

/-- The band projection onto `B₁ ⊓ B₂` is the composition of the band
projections of `B₁` and `B₂`. -/
theorem bandProjection_inf (B₁ B₂ : ProjectionBand X) :
    (B₁ ⊓ B₂).bandProjection = B₁.bandProjection ∘ₗ B₂.bandProjection := by
  ext x
  change (B₁ ⊓ B₂).bandProjection x = B₁.bandProjection (B₂.bandProjection x)
  set y := B₁.bandProjection (B₂.bandProjection x)
  have hy_B₂ : y ∈ B₂ :=
    bandProjection_mem_band B₁ B₂.toBand (B₂.bandProjection_mem x)
  have hy_B₁ : y ∈ B₁ := B₁.bandProjection_mem _
  have hy_inf : y ∈ ((B₁ ⊓ B₂ : ProjectionBand X) : Set X) := ⟨hy_B₁, hy_B₂⟩
  have hd : x - y ∈ disjointComplement ((B₁ ⊓ B₂ : ProjectionBand X) : Set X) := by
    intro a ha
    have ha₁ : a ∈ (B₁ : Set X) := ha.1
    have ha₂ : a ∈ (B₂ : Set X) := ha.2
    have hsplit : x - y = (x - B₂.bandProjection x) +
        (B₂.bandProjection x - y) := by abel
    rw [hsplit]
    exact (B₂.id_sub_bandProjection_mem x a ha₂).add_left
      (B₁.id_sub_bandProjection_mem (B₂.bandProjection x) a ha₁)
  have heq₁ : x = (B₁ ⊓ B₂).bandProjection x + (x - (B₁ ⊓ B₂).bandProjection x) :=
    by abel
  have heq₂ : x = y + (x - y) := by abel
  exact ((B₁ ⊓ B₂).decomposition_unique
    ((B₁ ⊓ B₂).bandProjection_mem x)
    ((B₁ ⊓ B₂).id_sub_bandProjection_mem x)
    hy_inf hd heq₁ heq₂).1

/-- Two band projections commute. -/
theorem bandProjection_comm (B₁ B₂ : ProjectionBand X) :
    B₁.bandProjection ∘ₗ B₂.bandProjection
      = B₂.bandProjection ∘ₗ B₁.bandProjection := by
  rw [← bandProjection_inf B₁ B₂, ← bandProjection_inf B₂ B₁,
      show (B₁ ⊓ B₂ : ProjectionBand X) = B₂ ⊓ B₁ from inf_comm _ _]

/-- The band projection onto `B₁ ⊔ B₂` equals `P₁ + P₂ - P₁ ∘ P₂`. -/
theorem bandProjection_sup (B₁ B₂ : ProjectionBand X) :
    (B₁ ⊔ B₂).bandProjection
      = B₁.bandProjection + B₂.bandProjection
        - B₁.bandProjection ∘ₗ B₂.bandProjection := by
  ext x
  change (B₁ ⊔ B₂).bandProjection x =
    B₁.bandProjection x + B₂.bandProjection x -
      B₁.bandProjection (B₂.bandProjection x)
  set y := B₁.bandProjection x + B₂.bandProjection x -
    B₁.bandProjection (B₂.bandProjection x) with hy_def
  have hy_sup : y ∈ ((B₁ ⊔ B₂ : ProjectionBand X) : Set X) := by
    change y ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X)
    have h1 : B₁.bandProjection x ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
      (le_sup_left : B₁.toBand ≤ _) (B₁.bandProjection_mem x)
    have h2 : B₂.bandProjection x ∈ ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
      (le_sup_right : B₂.toBand ≤ _) (B₂.bandProjection_mem x)
    have h3 : B₁.bandProjection (B₂.bandProjection x) ∈
        ((B₁.toBand ⊔ B₂.toBand : Band X) : Set X) :=
      (le_sup_left : B₁.toBand ≤ _) (B₁.bandProjection_mem _)
    exact (B₁.toBand ⊔ B₂.toBand).toOrderIdeal.toSubmodule.sub_mem
      ((B₁.toBand ⊔ B₂.toBand).toOrderIdeal.toSubmodule.add_mem h1 h2) h3
  have hxy_B₁d : x - y ∈ disjointComplement (B₁ : Set X) := by
    have heq : x - y = (x - B₁.bandProjection x) -
        (B₂.bandProjection x - B₁.bandProjection (B₂.bandProjection x)) := by
      rw [hy_def]; abel
    rw [heq]
    exact (Band.disjointComplement (B₁ : Set X)).toOrderIdeal.toSubmodule.sub_mem
      (B₁.id_sub_bandProjection_mem x)
      (B₁.id_sub_bandProjection_mem (B₂.bandProjection x))
  have hxy_B₂d : x - y ∈ disjointComplement (B₂ : Set X) := by
    have heq : x - y = (x - B₂.bandProjection x) -
        B₁.bandProjection (x - B₂.bandProjection x) := by
      rw [hy_def, map_sub]; abel
    rw [heq]
    exact (Band.disjointComplement (B₂ : Set X)).toOrderIdeal.toSubmodule.sub_mem
      (B₂.id_sub_bandProjection_mem x)
      (bandProjection_mem_band B₁ (Band.disjointComplement (B₂ : Set X))
        (B₂.id_sub_bandProjection_mem x))
  have hxy_supd : x - y ∈
      disjointComplement ((B₁ ⊔ B₂ : ProjectionBand X) : Set X) :=
    mem_disjointComplement_band_sup hxy_B₁d hxy_B₂d
  have heq₁ : x = (B₁ ⊔ B₂).bandProjection x + (x - (B₁ ⊔ B₂).bandProjection x) :=
    by abel
  have heq₂ : x = y + (x - y) := by abel
  exact ((B₁ ⊔ B₂).decomposition_unique
    ((B₁ ⊔ B₂).bandProjection_mem x)
    ((B₁ ⊔ B₂).id_sub_bandProjection_mem x)
    hy_sup hxy_supd heq₁ heq₂).1

/-- The band projection onto the complement equals `id - P`. -/
theorem bandProjection_compl (B : ProjectionBand X) :
    Bᶜ.bandProjection = LinearMap.id - B.bandProjection := by
  ext x
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  have hy_comp : x - B.bandProjection x ∈ ((Bᶜ : ProjectionBand X) : Set X) :=
    B.id_sub_bandProjection_mem x
  have hz_compd : B.bandProjection x ∈
      disjointComplement ((Bᶜ : ProjectionBand X) : Set X) := fun a ha =>
    isVLDisjoint_comm.mp (ha _ (B.bandProjection_mem x))
  have heq₁ : x = Bᶜ.bandProjection x + (x - Bᶜ.bandProjection x) := by abel
  have heq₂ : x = (x - B.bandProjection x) + B.bandProjection x := by abel
  exact (Bᶜ.decomposition_unique
    (Bᶜ.bandProjection_mem x)
    (Bᶜ.id_sub_bandProjection_mem x)
    hy_comp hz_compd heq₁ heq₂).1

/-! ### Characterisation via order interval suprema -/

/-- For a non-negative element, the existence of `IsLUB (B ∩ [0, x])` yields a
disjoint decomposition `x = y + z` with `y ∈ B`, `z ∈ Bᵈ`. -/
private lemma exists_decomposition_of_isLUB_pos {B : Band X}
    (hLUB : ∀ x : X, 0 ≤ x → ∃ s, IsLUB ((B : Set X) ∩ Set.Icc 0 x) s)
    {x : X} (hx_nn : 0 ≤ x) :
    ∃ y z : X, y ∈ (B : Set X) ∧ z ∈ disjointComplement (B : Set X) ∧ x = y + z := by
  obtain ⟨sp, hsp⟩ := hLUB x hx_nn
  have hzero_in_S : (0 : X) ∈ (B : Set X) ∩ Set.Icc 0 x :=
    ⟨B.toOrderIdeal.toSubmodule.zero_mem, le_refl 0, hx_nn⟩
  have hsp_mem : sp ∈ B := B.sSup_mem (fun y hy => hy.1) ⟨0, hzero_in_S⟩ hsp
  have hsp_nn : 0 ≤ sp := hsp.1 hzero_in_S
  have hsp_le : sp ≤ x := hsp.2 (fun y hy => hy.2.2)
  refine ⟨sp, x - sp, hsp_mem, ?_, by abel⟩
  intro a ha
  set d := x - sp with hd_def
  have hd_nn : 0 ≤ d := sub_nonneg.mpr hsp_le
  have hda_nn : 0 ≤ d ⊓ |a| := le_inf hd_nn (abs_nonneg _)
  have habs_B : |a| ∈ B := B.abs_mem ha
  have hda_B : d ⊓ |a| ∈ B := B.solid habs_B hda_nn inf_le_right
  have hsum_B : sp + d ⊓ |a| ∈ B :=
    B.toOrderIdeal.toSubmodule.add_mem hsp_mem hda_B
  have hsum_le : sp + d ⊓ |a| ≤ x := by
    have h1 : sp + d ⊓ |a| ≤ sp + d := by gcongr; exact inf_le_left
    have h2 : sp + d = x := by rw [hd_def]; abel
    exact h2 ▸ h1
  have hub : sp + d ⊓ |a| ≤ sp :=
    hsp.1 ⟨hsum_B, add_nonneg hsp_nn hda_nn, hsum_le⟩
  have hda_zero : d ⊓ |a| ≤ 0 := by
    have h1 : sp + d ⊓ |a| - sp ≤ sp - sp := sub_le_sub_right hub _
    rw [add_sub_cancel_left, sub_self] at h1; exact h1
  have hda_eq : d ⊓ |a| = 0 := le_antisymm hda_zero hda_nn
  change |x - sp| ⊓ |a| = 0
  rw [abs_of_nonneg hd_nn]; exact hda_eq

/-- For a projection band `B` and `x ∈ X₊`, the band projection of `x` is the
supremum of `B ∩ [0, x]`. -/
theorem isLUB_inter_Icc_bandProjection (B : ProjectionBand X) {x : X} (hx : 0 ≤ x) :
    IsLUB ((B : Set X) ∩ Set.Icc 0 x) (B.bandProjection x) := by
  have hBx_nn : 0 ≤ B.bandProjection x :=
    Positive.zero_le_iff.mp B.bandProjection_nonneg x hx
  have hBx_le : B.bandProjection x ≤ x :=
    Positive.le_iff.mp B.bandProjection_le_id x hx
  have hBx_mem : B.bandProjection x ∈ B := B.bandProjection_mem x
  refine ⟨?_, fun u hu => hu ⟨hBx_mem, hBx_nn, hBx_le⟩⟩
  rintro y ⟨hyB, _, hyx⟩
  have hPy : B.bandProjection y = y := B.bandProjection_eq_of_mem hyB
  have h := Positive.zero_le_iff.mp B.bandProjection_nonneg (x - y)
    (sub_nonneg.mpr hyx)
  rw [map_sub] at h
  have hmono : B.bandProjection y ≤ B.bandProjection x := sub_nonneg.mp h
  exact hPy ▸ hmono

/-- A band `B` is a projection band iff for every `x ∈ X₊` the set
`B ∩ [0, x]` admits a supremum. -/
theorem projectionBand_iff_isLUB_inter_Icc (B : Band X) :
    (∃ P : ProjectionBand X, (P : Set X) = (B : Set X))
      ↔ ∀ x : X, 0 ≤ x → ∃ s, IsLUB ((B : Set X) ∩ Set.Icc 0 x) s := by
  refine ⟨fun ⟨P, hPB⟩ x hx => ⟨P.bandProjection x, ?_⟩, fun hLUB => ?_⟩
  · have h := isLUB_inter_Icc_bandProjection P hx
    rw [hPB] at h; exact h
  · have hadd : ∀ x : X, ∃ y z : X, y ∈ (B : Set X)
        ∧ z ∈ disjointComplement (B : Set X) ∧ x = y + z := by
      intro x
      obtain ⟨yp, zp, hyp, hzp, hxp⟩ :=
        exists_decomposition_of_isLUB_pos hLUB (posPart_nonneg x)
      obtain ⟨yn, zn, hyn, hzn, hxn⟩ :=
        exists_decomposition_of_isLUB_pos hLUB (negPart_nonneg x)
      refine ⟨yp - yn, zp - zn,
        B.toOrderIdeal.toSubmodule.sub_mem hyp hyn,
        (Band.disjointComplement (B : Set X)).toOrderIdeal.toSubmodule.sub_mem hzp hzn,
        ?_⟩
      calc x = x⁺ - x⁻ := (posPart_sub_negPart x).symm
        _ = (yp + zp) - (yn + zn) := by rw [← hxp, ← hxn]
        _ = (yp - yn) + (zp - zn) := by abel
    exact (projectionBand_iff_add_disjointComplement B.toOrderIdeal).mpr hadd

/-- If a projection band `B` has the same underlying set as the principal band
generated by `a ∈ X₊`, then for every `x ∈ X₊` the band projection of `x`
equals the supremum of `(x ⊓ n • a)_{n ∈ ℕ}`. -/
theorem isLUB_range_bandProjection_of_principalBand [IsVLArchimedean X]
    {a : X} (ha : 0 ≤ a)
    (B : ProjectionBand X) (hB : (B : Set X) = (Band.generated {a} : Set X))
    {x : X} (hx : 0 ≤ x) :
    IsLUB (Set.range fun n : ℕ => x ⊓ (n : ℕ) • a) (B.bandProjection x) := by
  have hBx_nn : 0 ≤ B.bandProjection x :=
    Positive.zero_le_iff.mp B.bandProjection_nonneg x hx
  have hBx_le : B.bandProjection x ≤ x :=
    Positive.le_iff.mp B.bandProjection_le_id x hx
  have hBx_in : B.bandProjection x ∈ B := B.bandProjection_mem x
  have ha_in : a ∈ B := by
    have : a ∈ (B : Set X) := by rw [hB]; exact Band.subset_generated _ rfl
    exact this
  have hin : ∀ n : ℕ, x ⊓ n • a ∈ B := by
    intro n
    have hna_in : n • a ∈ B :=
      B.toBand.toOrderIdeal.toSubmodule.nsmul_mem ha_in n
    exact B.toBand.solid hna_in (le_inf hx (nsmul_nonneg ha n)) inf_le_right
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    have h := isLUB_inter_Icc_bandProjection B hx
    exact h.1 ⟨hin n, le_inf hx (nsmul_nonneg ha n), inf_le_left⟩
  · intro u hu
    have hBx_gen : B.bandProjection x ∈ Band.generated ({a} : Set X) := by
      have : B.bandProjection x ∈ (B : Set X) := hBx_in
      rw [hB] at this; exact this
    have hLUB := (Band.mem_generated_singleton_iff_isLUB_inf_nsmul ha hBx_nn).mp hBx_gen
    apply hLUB.2
    rintro _ ⟨n, rfl⟩
    calc B.bandProjection x ⊓ n • a
        ≤ x ⊓ n • a := inf_le_inf_right _ hBx_le
      _ ≤ u := hu ⟨n, rfl⟩

/-- The principal band generated by `a ∈ X₊` is a projection band iff for every
`x ∈ X₊` the family `(x ⊓ n • a)_{n ∈ ℕ}` admits a supremum. -/
theorem principalBand_projectionBand_iff_isLUB_range [IsVLArchimedean X]
    {a : X} (ha : 0 ≤ a) :
    (∃ P : ProjectionBand X, (P : Set X) = (Band.generated {a} : Set X))
      ↔ ∀ x : X, 0 ≤ x →
        ∃ s, IsLUB (Set.range fun n : ℕ => x ⊓ (n : ℕ) • a) s := by
  refine ⟨fun ⟨P, hPB⟩ x hx => ⟨P.bandProjection x,
    isLUB_range_bandProjection_of_principalBand ha P hPB hx⟩, fun hLUB => ?_⟩
  apply (projectionBand_iff_isLUB_inter_Icc (Band.generated {a})).mpr
  intro x hx
  obtain ⟨s, hs⟩ := hLUB x hx
  have hin : ∀ n : ℕ, x ⊓ n • a ∈ Band.generated ({a} : Set X) := by
    intro n
    have ha_in : a ∈ Band.generated ({a} : Set X) := Band.subset_generated _ rfl
    have hna_in : n • a ∈ Band.generated ({a} : Set X) :=
      (Band.generated _).toOrderIdeal.toSubmodule.nsmul_mem ha_in n
    exact (Band.generated _).solid hna_in
      (le_inf hx (nsmul_nonneg ha n)) inf_le_right
  have h0_eq : (fun n : ℕ => x ⊓ n • a) 0 = 0 := by
    change x ⊓ (0 : ℕ) • a = 0
    rw [zero_nsmul]; exact inf_of_le_right hx
  have hs_nn : 0 ≤ s := by
    have := hs.1 ⟨0, rfl⟩
    rw [h0_eq] at this; exact this
  have hs_le_x : s ≤ x := hs.2 (by rintro _ ⟨n, rfl⟩; exact inf_le_left)
  refine ⟨s, ?_, fun u hu => ?_⟩
  · rintro y ⟨hy_gen, hy_nn, hy_le_x⟩
    have hLUB_y :=
      (Band.mem_generated_singleton_iff_isLUB_inf_nsmul ha hy_nn).mp hy_gen
    apply hLUB_y.2
    rintro _ ⟨n, rfl⟩
    calc y ⊓ n • a
        ≤ x ⊓ n • a := inf_le_inf_right _ hy_le_x
      _ ≤ s := hs.1 ⟨n, rfl⟩
  · apply hs.2
    rintro _ ⟨n, rfl⟩
    exact hu ⟨hin n, le_inf hx (nsmul_nonneg ha n), inf_le_left⟩

end ProjectionBand
