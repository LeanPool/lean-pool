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
public import LeanPool.OrderClosures.BanLat.Substructures.Ideal
public import LeanPool.OrderClosures.BanLat.Operators.Hom
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic



/-!
# Quotients of vector and Banach lattices

The quotient of a vector lattice `X` by an order ideal `J` carries a natural
vector lattice structure for which the canonical projection is a lattice
homomorphism. When `X` is a normed vector lattice and `J` is norm-closed,
the quotient norm is a lattice norm; completeness passes to the quotient.
-/

@[expose] public section

section -- Algebraic quotient

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

namespace OrderIdeal

/-! ### Kernel characterisation -/

/-- The kernel of a vector lattice homomorphism is an order ideal. -/
noncomputable def ofKerVecLatHom {Y : Type*} [AddCommGroup Y]
    [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (T : VecLatHom X Y) : OrderIdeal X :=
  OrderIdeal.ofSolid (LinearMap.ker T.toLinearMap) fun x y hx hle => by
    rw [LinearMap.mem_ker] at hx ⊢
    have hTx : (T : X → Y) x = 0 := hx
    have hab : |T y| ≤ |T x| := by
      rw [← VecLatHom.map_abs, ← VecLatHom.map_abs]
      exact T.monotone hle
    rw [hTx, abs_zero] at hab
    have := (abs_eq_zero_iff_zero (T y)).mp (le_antisymm hab (abs_nonneg _))
    exact this

/-- The underlying submodule of `ofKerVecLatHom T` is `ker T`. -/
theorem ofKerVecLatHom_toSubmodule {Y : Type*}
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] (T : VecLatHom X Y) :
    (ofKerVecLatHom T).toSubmodule =
      LinearMap.ker T.toLinearMap := rfl

variable (J : OrderIdeal X)

/-! ### Lattice structure on the quotient -/

theorem sup_sub_mem (J : OrderIdeal X) {a₁ a₂ b₁ b₂ : X}
    (h₁ : a₁ - b₁ ∈ J.toSubmodule) (h₂ : a₂ - b₂ ∈ J.toSubmodule) :
    (a₁ ⊔ a₂) - (b₁ ⊔ b₂) ∈ J.toSubmodule := by
  have key : (a₁ ⊔ a₂) - (b₁ ⊔ b₂) =
      ((a₁ ⊔ a₂) - (b₁ ⊔ a₂)) + ((b₁ ⊔ a₂) - (b₁ ⊔ b₂)) := by abel
  rw [key]
  apply J.toSubmodule.add_mem
  · exact J.mem_of_abs_le_abs h₁
      (abs_sup_sub_sup_le_abs a₁ b₁ a₂)
  · exact J.mem_of_abs_le_abs h₂ (by
      rw [sup_comm b₁ a₂, sup_comm b₁ b₂]
      exact abs_sup_sub_sup_le_abs a₂ b₂ b₁)

theorem inf_sub_mem (J : OrderIdeal X) {a₁ a₂ b₁ b₂ : X}
    (h₁ : a₁ - b₁ ∈ J.toSubmodule) (h₂ : a₂ - b₂ ∈ J.toSubmodule) :
    (a₁ ⊓ a₂) - (b₁ ⊓ b₂) ∈ J.toSubmodule := by
  have h₁' : -a₁ - (-b₁) ∈ J.toSubmodule := by
    rw [show -a₁ - (-b₁) = -(a₁ - b₁) from by abel]
    exact J.toSubmodule.neg_mem h₁
  have h₂' : -a₂ - (-b₂) ∈ J.toSubmodule := by
    rw [show -a₂ - (-b₂) = -(a₂ - b₂) from by abel]
    exact J.toSubmodule.neg_mem h₂
  have key : a₁ ⊓ a₂ - (b₁ ⊓ b₂) =
      -((-a₁ ⊔ -a₂) - (-b₁ ⊔ -b₂)) := by
    have := neg_inf a₁ a₂; have := neg_inf b₁ b₂
    rw [show a₁ ⊓ a₂ = -(-a₁ ⊔ -a₂) from by rw [← neg_inf]; simp,
        show b₁ ⊓ b₂ = -(-b₁ ⊔ -b₂) from by rw [← neg_inf]; simp]
    abel
  rw [key]
  exact J.toSubmodule.neg_mem (sup_sub_mem J h₁' h₂')

/-- Supremum on the quotient by an order ideal, computed on representatives. -/
noncomputable def quotSup (J : OrderIdeal X) :
    X ⧸ J.toSubmodule → X ⧸ J.toSubmodule → X ⧸ J.toSubmodule :=
  fun a b => Quotient.liftOn₂' a b
    (fun x y => (Submodule.Quotient.mk (x ⊔ y) : X ⧸ J.toSubmodule))
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => by
      rw [Submodule.Quotient.eq]
      rw [Submodule.quotientRel_def] at h₁ h₂
      exact sup_sub_mem J h₁ h₂)

/-- Infimum on the quotient by an order ideal, computed on representatives. -/
noncomputable def quotInf (J : OrderIdeal X) :
    X ⧸ J.toSubmodule → X ⧸ J.toSubmodule → X ⧸ J.toSubmodule :=
  fun a b => Quotient.liftOn₂' a b
    (fun x y => (Submodule.Quotient.mk (x ⊓ y) : X ⧸ J.toSubmodule))
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => by
      rw [Submodule.Quotient.eq]
      rw [Submodule.quotientRel_def] at h₁ h₂
      exact inf_sub_mem J h₁ h₂)

theorem quotSup_mk (J : OrderIdeal X) (x y : X) :
    quotSup J (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊔ y) := rfl

theorem quotInf_mk (J : OrderIdeal X) (x y : X) :
    quotInf J (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊓ y) := rfl

/-- The quotient of a vector lattice by an order ideal is a lattice,
with `Q(x) ⊔ Q(y) = Q(x ⊔ y)`. -/
noncomputable instance instQuotientLattice :
    Lattice (X ⧸ J.toSubmodule) := by
  letI : Max (X ⧸ J.toSubmodule) := ⟨quotSup J⟩
  letI : Min (X ⧸ J.toSubmodule) := ⟨quotInf J⟩
  exact Lattice.mk'
    (fun a b => by
      induction a, b using Quotient.inductionOn₂'
      exact congr_arg Submodule.Quotient.mk (sup_comm _ _))
    (fun a b c => by
      induction a, b, c using Quotient.inductionOn₃'
      exact congr_arg Submodule.Quotient.mk (sup_assoc _ _ _))
    (fun a b => by
      induction a, b using Quotient.inductionOn₂'
      exact congr_arg Submodule.Quotient.mk (inf_comm _ _))
    (fun a b c => by
      induction a, b, c using Quotient.inductionOn₃'
      exact congr_arg Submodule.Quotient.mk (inf_assoc _ _ _))
    (fun a b => by
      induction a, b using Quotient.inductionOn₂'
      exact congr_arg Submodule.Quotient.mk sup_inf_self)
    (fun a b => by
      induction a, b using Quotient.inductionOn₂'
      exact congr_arg Submodule.Quotient.mk inf_sup_self)

/-- `a ≤ b` in the quotient lattice iff `a ⊔ b = b`. -/
theorem quot_le_iff {a b : X ⧸ J.toSubmodule} :
    a ≤ b ↔ a ⊔ b = b :=
  Iff.rfl


/-- The quotient order is compatible with addition. -/
instance instQuotientIsOrderedAddMonoid :
    IsOrderedAddMonoid (X ⧸ J.toSubmodule) where
  add_le_add_left := fun a b hab c => by
    rw [quot_le_iff] at hab ⊢
    induction a, b, c using Quotient.inductionOn₃'
    rename_i x y z
    change Quotient.mk'' (x ⊔ y) = Quotient.mk'' y at hab
    change Quotient.mk'' ((x + z) ⊔ (y + z)) =
      Quotient.mk'' (y + z)
    rw [show (x + z) ⊔ (y + z) = (x ⊔ y) + z from
      (sup_add x y z).symm]
    have hmem : (x ⊔ y) - y ∈ J.toSubmodule :=
      (Submodule.Quotient.eq J.toSubmodule).mp hab
    exact (Submodule.Quotient.eq J.toSubmodule).mpr
      (by convert hmem using 1; abel)

/-- The quotient of a vector lattice by an order ideal is a vector
lattice. The `Module ℝ` structure is inherited from Mathlib's quotient
module. -/
noncomputable instance instQuotientVectorLattice :
    VectorLattice (X ⧸ J.toSubmodule) :=
  { (inferInstance : Module ℝ (X ⧸ J.toSubmodule)) with
    smul_le_smul_of_nonneg_left := fun c hc a b hab => by
      rw [quot_le_iff] at hab ⊢
      induction a, b using Quotient.inductionOn₂'
      rename_i x y
      change Quotient.mk'' (x ⊔ y) = Quotient.mk'' y at hab
      change Quotient.mk'' ((c • x) ⊔ (c • y)) =
        Quotient.mk'' (c • y)
      rw [show (c • x) ⊔ (c • y) = c • (x ⊔ y) from
        (nonneg_smul_sup x y c hc).symm]
      have hmem : (x ⊔ y) - y ∈ J.toSubmodule :=
        (Submodule.Quotient.eq J.toSubmodule).mp hab
      exact (Submodule.Quotient.eq J.toSubmodule).mpr
        (by rw [show c • (x ⊔ y) - c • y = c • ((x ⊔ y) - y)
              from (smul_sub c _ _).symm]
            exact J.toSubmodule.smul_mem c hmem) }

/-! ### The quotient map as a lattice homomorphism -/

/-- Abbreviation for the canonical linear quotient map. -/
abbrev mkQ : X →ₗ[ℝ] X ⧸ J.toSubmodule :=
  Submodule.mkQ J.toSubmodule

/-- The quotient map preserves suprema. -/
theorem mkQ_sup (x y : X) :
    J.mkQ (x ⊔ y) = J.mkQ x ⊔ J.mkQ y := rfl

/-- The quotient map preserves infima. -/
theorem mkQ_inf (x y : X) :
    J.mkQ (x ⊓ y) = J.mkQ x ⊓ J.mkQ y := rfl

/-- The quotient map preserves absolute values. -/
theorem mkQ_abs (x : X) :
    J.mkQ |x| = |J.mkQ x| := by
  simp only [abs, J.mkQ_sup, map_neg]

/-- The quotient map as a vector lattice homomorphism. -/
noncomputable def mkQVecLatHom :
    VecLatHom X (X ⧸ J.toSubmodule) :=
  { J.mkQ with
    map_sup' := fun x y => J.mkQ_sup x y
    map_inf' := fun x y => J.mkQ_inf x y }

/-- `mkQVecLatHom` agrees with the canonical linear quotient map. -/
@[simp]
theorem mkQVecLatHom_apply (x : X) :
    J.mkQVecLatHom x = J.mkQ x := rfl

/-! ### Lifting properties -/

/-- Every positive element in the quotient has a positive
representative. -/
theorem lift_pos {φ : X ⧸ J.toSubmodule} (hφ : 0 ≤ φ) :
    ∃ x : X, 0 ≤ x ∧ J.mkQ x = φ := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective J.toSubmodule φ
  refine ⟨a⁺, posPart_nonneg a, ?_⟩
  change J.mkQ a⁺ = J.mkQ a
  calc J.mkQ a⁺ = J.mkQ (a ⊔ 0) := rfl
    _ = J.mkQ a ⊔ J.mkQ 0 := J.mkQ_sup a 0
    _ = J.mkQ a ⊔ 0 := by rw [map_zero]
    _ = J.mkQ a := sup_eq_left.mpr hφ

/-- If `φ ≤ ψ` in the quotient, any representative of `φ` can be
dominated by a representative of `ψ`. -/
theorem lift_le {φ ψ : X ⧸ J.toSubmodule} (h : φ ≤ ψ)
    (x : X) (hx : J.mkQ x = φ) :
    ∃ y : X, J.mkQ y = ψ ∧ x ≤ y := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective J.toSubmodule ψ
  refine ⟨x ⊔ b, ?_, le_sup_left⟩
  change J.mkQ (x ⊔ b) = J.mkQ b
  rw [J.mkQ_sup, hx]
  exact sup_eq_right.mpr h

/-- If `x ≤ z` in `X` and `Q(x) ≤ φ ≤ Q(z)`, there exists `y ∈ φ`
with `x ≤ y ≤ z`. -/
theorem lift_between {x z : X} (hxz : x ≤ z)
    {φ : X ⧸ J.toSubmodule}
    (hx : J.mkQ x ≤ φ) (hz : φ ≤ J.mkQ z) :
    ∃ y : X, J.mkQ y = φ ∧ x ≤ y ∧ y ≤ z := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective J.toSubmodule φ
  refine ⟨(x ⊔ a) ⊓ z, ?_, le_inf le_sup_left hxz, inf_le_right⟩
  change J.mkQ ((x ⊔ a) ⊓ z) = J.mkQ a
  rw [J.mkQ_inf, J.mkQ_sup]
  have h1 : J.mkQ x ⊔ J.mkQ a = J.mkQ a := sup_eq_right.mpr
    (by simpa only [Submodule.mkQ_apply] using hx)
  have h2 : J.mkQ a ⊓ J.mkQ z = J.mkQ a := inf_eq_left.mpr
    (by simpa only [Submodule.mkQ_apply] using hz)
  rw [h1, h2]

/-- If `0 ≤ y` and `Q(y) = |φ|`, there exists `x ∈ φ` with
`|x| ≤ y`. -/
theorem lift_abs_le {φ : X ⧸ J.toSubmodule} {y : X}
    (hy : 0 ≤ y) (habs : J.mkQ y = |φ|) :
    ∃ x : X, J.mkQ x = φ ∧ |x| ≤ y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective J.toSubmodule φ
  have habs' : J.mkQ y = |J.mkQ a| := habs
  rw [← J.mkQ_abs] at habs'
  have ha_le : J.mkQ a ≤ J.mkQ y := by
    calc J.mkQ a ≤ |J.mkQ a| := le_abs_self _
      _ = J.mkQ |a| := (J.mkQ_abs a).symm
      _ = J.mkQ y := habs'.symm
  have hle_a : J.mkQ (-y) ≤ J.mkQ a := by
    rw [map_neg]
    calc -J.mkQ y = -(J.mkQ |a|) := by rw [habs']
      _ = J.mkQ (-|a|) := (map_neg J.mkQ |a|).symm
      _ ≤ J.mkQ a := by
        apply J.mkQVecLatHom.monotone
        calc -|a| = (-a) ⊓ a := by
              rw [abs, neg_sup, neg_neg, inf_comm]
          _ ≤ a := inf_le_right
  obtain ⟨x, hx_eq, hx_ge, hx_le⟩ :=
    J.lift_between (neg_le_self hy) hle_a ha_le
  refine ⟨x, hx_eq, ?_⟩
  rw [abs]; exact sup_le hx_le (neg_le.mp hx_ge)

/-- An increasing positive sequence in the quotient can be lifted to
an increasing positive sequence of representatives. -/
theorem lift_increasing_seq
    (φ : ℕ → X ⧸ J.toSubmodule)
    (hpos : ∀ n, 0 ≤ φ n) (hmono : Monotone φ) :
    ∃ f : ℕ → X,
      (∀ n, J.mkQ (f n) = φ n) ∧
      (∀ n, 0 ≤ f n) ∧ Monotone f := by
  -- Build the sequence by dependent choice: each step lifts and
  -- dominates the previous element.
  -- Step function: given xₙ with mkQ xₙ = φ n and 0 ≤ xₙ,
  -- produce x_{n+1} with mkQ x_{n+1} = φ (n+1) and xₙ ≤ x_{n+1}.
  have step : ∀ n (x : X), 0 ≤ x → J.mkQ x = φ n →
      ∃ y : X, 0 ≤ y ∧ J.mkQ y = φ (n + 1) ∧ x ≤ y := by
    intro n x hnn heq
    obtain ⟨y, hy_eq, hxy⟩ := J.lift_le (hmono (Nat.le_succ n)) x heq
    exact ⟨y, le_trans hnn hxy, hy_eq, hxy⟩
  -- Base case
  obtain ⟨x₀, hx₀_nn, hx₀_eq⟩ := J.lift_pos (hpos 0)
  -- Build the sequence as ℕ → {x : X // 0 ≤ x ∧ J.mkQ x = φ n}
  -- using Nat.rec
  let F : (n : ℕ) → {x : X // 0 ≤ x ∧ J.mkQ x = φ n} :=
    fun n => Nat.rec
      ⟨x₀, hx₀_nn, hx₀_eq⟩
      (fun k (prev : {x : X // 0 ≤ x ∧ J.mkQ x = φ k}) =>
        ⟨(step k prev.1 prev.2.1 prev.2.2).choose,
          (step k prev.1 prev.2.1 prev.2.2).choose_spec.1,
          (step k prev.1 prev.2.1 prev.2.2).choose_spec.2.1⟩)
      n
  refine ⟨fun n => (F n).1, fun n => (F n).2.2, fun n => (F n).2.1, ?_⟩
  apply monotone_nat_of_le_succ
  intro n
  exact (step n (F n).1 (F n).2.1 (F n).2.2).choose_spec.2.2

/-! ### Factoring operators through the quotient -/

/-- A positive operator whose kernel contains `J` factors through
the quotient as a positive operator. -/
theorem liftQ_positive {Y : Type*} [AddCommGroup Y]
    [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (T : X →ₗ[ℝ] Y)
    (hker : J.toSubmodule ≤ LinearMap.ker T)
    (hpos : Positive T) :
    Positive (Submodule.liftQ J.toSubmodule T hker) := by
  intro φ hφ
  obtain ⟨x, hx_nn, hx_eq⟩ := J.lift_pos hφ
  rw [← hx_eq]
  change 0 ≤ T x
  exact hpos x hx_nn

/-- A vector lattice homomorphism whose kernel contains `J` factors
through the quotient as a vector lattice homomorphism. -/
noncomputable def liftQVecLatHom {Y : Type*}
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] (T : VecLatHom X Y)
    (hker : J.toSubmodule ≤ LinearMap.ker T.toLinearMap) :
    VecLatHom (X ⧸ J.toSubmodule) Y :=
  { Submodule.liftQ J.toSubmodule T.toLinearMap hker with
    map_sup' := fun a b => by
      induction a, b using Quotient.inductionOn₂'
      change Submodule.liftQ J.toSubmodule T.toLinearMap hker
        (J.mkQ (_ ⊔ _)) = _
      rw [J.mkQ_sup]
      change T (_ ⊔ _) = T _ ⊔ T _
      exact T.map_sup' _ _
    map_inf' := fun a b => by
      induction a, b using Quotient.inductionOn₂'
      change Submodule.liftQ J.toSubmodule T.toLinearMap hker
        (J.mkQ (_ ⊓ _)) = _
      rw [J.mkQ_inf]
      change T (_ ⊓ _) = T _ ⊓ T _
      exact T.map_inf' _ _ }

/-- The factored lattice hom agrees with the original on
representatives. -/
@[simp]
theorem liftQVecLatHom_apply {Y : Type*}
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] (T : VecLatHom X Y)
    (hker : J.toSubmodule ≤ LinearMap.ker T.toLinearMap)
    (x : X) :
    J.liftQVecLatHom T hker (Submodule.Quotient.mk x) = T x := rfl

/-! ### Uniformly closed ideals and the Archimedean property -/

/-- An order ideal is **uniformly closed** if it is closed under
uniform convergence: whenever `(xₙ) ⊂ J` and
`|x - xₙ| ≤ (1/(n+1)) • u` for some `u ≥ 0`, then `x ∈ J`. -/
def IsUniformlyClosed : Prop :=
  ∀ (x u : X) (f : ℕ → X), 0 ≤ u →
    (∀ n, f n ∈ J) →
    (∀ n, |x - f n| ≤ (1 / (↑(n + 1) : ℝ)) • u) →
    x ∈ J

theorem mkQ_eq_zero_iff {x : X} :
    J.mkQ x = 0 ↔ x ∈ J := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact Iff.rfl

theorem archimedean_of_uniformlyClosed
    (huc : J.IsUniformlyClosed) :
    IsVLArchimedean (X ⧸ J.toSubmodule) := by
  apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
  intro φ ψ hφ hsmul
  obtain ⟨a, ha_nn, ha_eq⟩ := J.lift_pos hφ
  obtain ⟨y, rfl⟩ :=
    Submodule.Quotient.mk_surjective J.toSubmodule ψ
  set u := |y| with hu_def
  have hu_nn : (0 : X) ≤ u := abs_nonneg y
  have hsmul' : ∀ n : ℕ, n • J.mkQ a ≤ J.mkQ u := fun n =>
    calc n • J.mkQ a = n • φ := by rw [ha_eq]
      _ ≤ J.mkQ y := hsmul n
      _ ≤ |J.mkQ y| := le_abs_self _
      _ = J.mkQ u := (J.mkQ_abs y).symm
  -- For each n, build fₙ ∈ J with |a - fₙ| ≤ (1/(n+1)) • u
  have key : ∀ n : ℕ, ∃ fn : X, fn ∈ J ∧
      |a - fn| ≤ (1 / (↑(n + 1) : ℝ)) • u := by
    intro n
    have hc_pos : (0 : ℝ) < ↑(n + 1) :=
      Nat.cast_pos.mpr (Nat.succ_pos n)
    have hc_ne : (↑(n + 1) : ℝ) ≠ 0 := ne_of_gt hc_pos
    -- dₘ = (n+1) • a - ((n+1) • a ⊓ u) is in J
    have hdm_mem : (n + 1) • a - ((n + 1) • a ⊓ u) ∈ J := by
      rw [← J.mkQ_eq_zero_iff, map_sub, map_nsmul, J.mkQ_inf, map_nsmul,
        inf_eq_left.mpr (hsmul' (n + 1)), sub_self]
    -- fₙ = (n+1)⁻¹ • dₘ ∈ J
    set fn := (↑(n + 1) : ℝ)⁻¹ •
      ((n + 1) • a - ((n + 1) • a ⊓ u))
    refine ⟨fn, J.toSubmodule.smul_mem _ hdm_mem, ?_⟩
    -- a - fₙ = (n+1)⁻¹ • ((n+1) • a ⊓ u)
    have step : a - fn = (↑(n + 1) : ℝ)⁻¹ •
        ((n + 1) • a ⊓ u) := by
      have h : (↑(n + 1) : ℝ)⁻¹ • ((n + 1) : ℕ) • a = a := by
        rw [← Nat.cast_smul_eq_nsmul ℝ (n + 1) a, smul_smul,
          inv_mul_cancel₀ hc_ne, one_smul]
      calc a - fn
        _ = a - (↑(n + 1) : ℝ)⁻¹ • (n + 1) • a +
            (↑(n + 1) : ℝ)⁻¹ • ((n + 1) • a ⊓ u) := by
            change a - (↑(n + 1) : ℝ)⁻¹ •
              ((n + 1) • a - (n + 1) • a ⊓ u) = _
            rw [smul_sub]; abel
        _ = _ := by rw [h, sub_self, zero_add]
    have hcm_nn : (0 : X) ≤ (n + 1) • a ⊓ u :=
      le_inf (nsmul_nonneg ha_nn _) hu_nn
    rw [step, abs_of_nonneg (smul_nonneg (inv_pos.mpr hc_pos).le
      hcm_nn), one_div]
    exact smul_le_smul_of_nonneg_left
      inf_le_right (inv_pos.mpr hc_pos).le
  have hmem : a ∈ J :=
    huc a u (fun n => (key n).choose) hu_nn
      (fun n => (key n).choose_spec.1)
      (fun n => (key n).choose_spec.2)
  rw [← ha_eq, ← J.mkQ_eq_zero_iff.mpr hmem]

theorem uniformlyClosed_of_archimedean
    (harch : IsVLArchimedean (X ⧸ J.toSubmodule)) :
    J.IsUniformlyClosed := by
  intro x u f hu hfJ hbound
  have hQf : ∀ n : ℕ, J.mkQ (f n) = 0 := fun n =>
    J.mkQ_eq_zero_iff.mpr (hfJ n)
  have hQx_bound : ∀ n : ℕ, |J.mkQ x| ≤
      (1 / (↑(n + 1) : ℝ)) • J.mkQ u := fun n =>
    calc |J.mkQ x|
        = |J.mkQ x - J.mkQ (f n)| := by rw [hQf n, sub_zero]
      _ = |J.mkQ (x - f n)| := by rw [map_sub]
      _ = J.mkQ |x - f n| := (J.mkQ_abs (x - f n)).symm
      _ ≤ J.mkQ ((1 / (↑(n + 1) : ℝ)) • u) :=
          J.mkQVecLatHom.monotone (hbound n)
      _ = _ := by rw [map_smul]
  have hsmul : ∀ m : ℕ, m • |J.mkQ x| ≤ J.mkQ u := by
    intro m; rcases m with _ | n
    · simp only [zero_nsmul]; exact J.mkQVecLatHom.monotone hu
    · rw [show (n + 1) • |J.mkQ x| =
          (↑(n + 1) : ℝ) • |J.mkQ x| from
          (Nat.cast_smul_eq_nsmul ℝ (n + 1) _).symm]
      calc (↑(n + 1) : ℝ) • |J.mkQ x|
          ≤ (↑(n + 1) : ℝ) • ((1 / (↑(n + 1) : ℝ)) • J.mkQ u) :=
            smul_le_smul_of_nonneg_left (hQx_bound n)
              (Nat.cast_nonneg' (n + 1))
        _ = J.mkQ u := by
            rw [smul_smul, one_div, mul_inv_cancel₀
              (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_smul]
  have habs_zero := harch.eq_zero_of_nonneg_of_forall_nsmul_le
    (abs_nonneg (J.mkQ x)) hsmul
  exact J.mkQ_eq_zero_iff.mp
    ((abs_eq_zero_iff_zero (J.mkQ x)).mp habs_zero)

/-- The quotient `X ⧸ J` is Archimedean iff `J` is uniformly
closed. -/
theorem quotient_archimedean_iff_uniformlyClosed :
    IsVLArchimedean (X ⧸ J.toSubmodule) ↔
      J.IsUniformlyClosed :=
  ⟨uniformlyClosed_of_archimedean J, archimedean_of_uniformlyClosed J⟩

end OrderIdeal

end -- Algebraic quotient

section -- Normed quotient

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [NormedVectorLattice X]

namespace OrderIdeal

variable (J : OrderIdeal X)

/-! ### Normed quotient -/

/-- The quotient of a normed vector lattice by a closed order ideal
is a normed additive commutative group: the quotient seminorm
separates points. -/
@[reducible]
noncomputable def quotientNormedAddCommGroup
    (hJ : IsClosed (J : Set X)) :
    NormedAddCommGroup (X ⧸ J.toSubmodule) :=
  haveI : IsClosed (J.toSubmodule : Set X) := hJ
  Submodule.Quotient.normedAddCommGroup J.toSubmodule

/-- The quotient of a normed vector lattice by a closed order ideal
is a normed vector lattice: the quotient norm is a lattice norm. -/
@[reducible]
noncomputable def quotientNormedVectorLattice
    (hJ : IsClosed (J : Set X)) :
    @NormedVectorLattice (X ⧸ J.toSubmodule)
      (quotientNormedAddCommGroup J hJ)
      (instQuotientLattice J) (instQuotientIsOrderedAddMonoid J) := by
  haveI hcl : IsClosed (J.toSubmodule : Set X) := hJ
  letI : NormedAddCommGroup (X ⧸ J.toSubmodule) := quotientNormedAddCommGroup J hJ
  letI : Lattice (X ⧸ J.toSubmodule) := instQuotientLattice J
  letI : IsOrderedAddMonoid (X ⧸ J.toSubmodule) := instQuotientIsOrderedAddMonoid J
  letI : VectorLattice (X ⧸ J.toSubmodule) := instQuotientVectorLattice J
  let solidNorm : HasSolidNorm (X ⧸ J.toSubmodule) := {
    solid := fun {a b} hab => by
      apply le_of_forall_pos_lt_add'
      intro ε hε
      obtain ⟨β, hβ_eq, hβ_norm⟩ :=
        Submodule.Quotient.norm_mk_lt b hε
      -- lift_between with [-|β|, |β|]
      have hle_neg_abs : -|β| ≤ |β| :=
        le_trans (neg_nonpos_of_nonneg (abs_nonneg β)) (abs_nonneg β)
      have hQ_abs : J.mkQ (|β|) = |b| := by
        rw [J.mkQ_abs]; exact congrArg (|·|) hβ_eq
      have ha_le : a ≤ J.mkQ (|β|) := by
        rw [hQ_abs]; exact le_trans (le_abs_self a) hab
      have neg_abs_le_self : ∀ (x : X ⧸ J.toSubmodule), -|x| ≤ x :=
        fun x => by
          change -(x ⊔ -x) ≤ x
          rw [neg_sup, neg_neg]
          exact inf_le_right
      have hle_a : J.mkQ (-|β|) ≤ a := by
        rw [map_neg, hQ_abs]
        exact le_trans (neg_le_neg hab) (neg_abs_le_self a)
      obtain ⟨γ, hγ_eq, hγ_ge, hγ_le⟩ :=
        J.lift_between hle_neg_abs hle_a ha_le
      have hγ_abs : |γ| ≤ |β| := by
        have h1 : |γ| ≤ |( |β| )| :=
          abs_le_abs hγ_le (neg_le.mp hγ_ge)
        rwa [abs_abs] at h1
      have : ‖J.mkQ γ‖ ≤ ‖γ‖ :=
        Submodule.Quotient.norm_mk_le (S := J.toSubmodule) γ
      calc
        ‖a‖ = ‖J.mkQ γ‖ := by rw [hγ_eq]
        _ ≤ ‖γ‖ := this
        _ ≤ ‖β‖ := norm_le_norm_of_abs_le_abs hγ_abs
        _ < ‖b‖ + ε := hβ_norm
  }
  let normSmul : NormSMulClass ℝ (X ⧸ J.toSubmodule) := {
    norm_smul := fun r x => by
      have : NormSMulClass ℝ (X ⧸ J.toSubmodule) :=
        @NormedSpace.toNormSMulClass ℝ (X ⧸ J.toSubmodule) _
          (Submodule.Quotient.seminormedAddCommGroup J.toSubmodule)
          (Submodule.Quotient.normedSpace J.toSubmodule ℝ)
      exact this.norm_smul r x
  }
  exact @NormedVectorLattice.mk (X ⧸ J.toSubmodule)
    (quotientNormedAddCommGroup J hJ)
    (instQuotientLattice J)
    (instQuotientIsOrderedAddMonoid J)
    (instQuotientVectorLattice J)
    solidNorm
    normSmul

end OrderIdeal

end -- Normed quotient

section -- Banach lattice quotient

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

namespace OrderIdeal

variable (J : OrderIdeal X)

/-- The quotient of a Banach lattice by a closed order ideal is a
Banach lattice. -/
@[reducible]
noncomputable def quotientBanachLattice
    (hJ : IsClosed (J : Set X)) :
    @BanachLattice (X ⧸ J.toSubmodule)
      (quotientNormedAddCommGroup J hJ)
      (instQuotientLattice J) (instQuotientIsOrderedAddMonoid J) :=
  haveI : IsClosed (J.toSubmodule : Set X) := hJ
  letI : NormedAddCommGroup (X ⧸ J.toSubmodule) := quotientNormedAddCommGroup J hJ
  let completeSpace : CompleteSpace (X ⧸ J.toSubmodule) := inferInstance
  @BanachLattice.mk (X ⧸ J.toSubmodule)
    (quotientNormedAddCommGroup J hJ)
    (instQuotientLattice J)
    (instQuotientIsOrderedAddMonoid J)
    (quotientNormedVectorLattice J hJ)
    completeSpace

end OrderIdeal

end -- Banach lattice quotient
