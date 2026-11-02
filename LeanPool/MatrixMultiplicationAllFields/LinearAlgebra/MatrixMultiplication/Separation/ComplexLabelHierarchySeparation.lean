/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteSeparation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexAuxiliarySeparation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexLocalMaps
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSharedAuxiliaryBank

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace LabelHierarchySeparation

section Bank

variable {K I : Type*} [CommSemiring K] [Fintype I]
variable {X Y Z : I → Type*}

variable {Node : Type*} [Fintype Node]

/-- Transport a dependent coordinate family along a population-preserving reindexing. -/
def populationCoordinateEquiv {J : Type*} (D : Node → Type*)
    (pool : I → Node) (reference : J → Node) (e : I ≃ J)
    (same : ∀ i, reference (e i) = pool i) :
    (∀ i, D (pool i)) ≃ (∀ j, D (reference j)) :=
  e.piCongr (fun i => Equiv.cast (congrArg D (same i).symm))

omit [CommSemiring K] [Fintype Node] in
theorem tensor_transport {AX AY AZ : Node → Type*}
    (T : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    {node node' : Node} (h : node = node') (x : AX node) (y : AY node) (z : AZ node) :
    T node' (Equiv.cast (congrArg AX h) x) (Equiv.cast (congrArg AY h) y)
      (Equiv.cast (congrArg AZ h) z) = T node x y z := by
  cases h
  rfl

omit [Fintype Node] in
theorem bankTensor_population_reindex {J : Type*} [Fintype J]
    {AX AY AZ : Node → Type*}
    (T : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    (pool : I → Node) (reference : J → Node) (e : I ≃ J)
    (same : ∀ i, reference (e i) = pool i) :
    Tensor.pullback (populationCoordinateEquiv AX pool reference e same)
      (populationCoordinateEquiv AY pool reference e same)
      (populationCoordinateEquiv AZ pool reference e same)
      (bankTensor (fun j => T (reference j))) = bankTensor (fun i => T (pool i)) := by
  unfold populationCoordinateEquiv
  apply bankTensor_reindex e
  intro i x y z
  exact tensor_transport T (same i).symm x y z

omit [Fintype Node] in
theorem bankTensor_population_rankAtMost {J : Type*} [Fintype J]
    {AX AY AZ : Node → Type*}
    (T : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    (pool : I → Node) (reference : J → Node) (e : I ≃ J)
    (same : ∀ i, reference (e i) = pool i)
    {r : ℕ} (hT : Tensor.RankAtMost (bankTensor (fun j => T (reference j))) r) :
    Tensor.RankAtMost (bankTensor (fun i => T (pool i))) r := by
  rw [← bankTensor_population_reindex T pool reference e same]
  exact hT.pullback _ _ _

/-- Individual occurrences of each node in a prescribed resource population. -/
abbrev BankOccurrences (population : Node → ℕ) :=
  (node : Node) × Fin (population node)

theorem canonical_bank_product {M : Type*} [CommMonoid M]
    (population : Node → ℕ) (cost : Node → M) :
    (∏ i : BankOccurrences population, cost i.1) =
      ∏ node, cost node ^ population node := by
  simp [BankOccurrences, Fintype.prod_sigma]

theorem canonical_pairing_card [DecidableEq Node] (population dimension : Node → ℕ) :
    Fintype.card (∀ i : BankOccurrences population, Fin (dimension i.1)) =
      ∏ node, dimension node ^ population node := by
  classical
  simp only [Fintype.card_pi, Fintype.card_fin, canonical_bank_product]

theorem canonical_bank_rankAtMost
    {AX AY AZ : Node → Type*}
    (E : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    (population rank : Node → ℕ)
    (hE : ∀ node, Tensor.RankAtMost (E node) (rank node)) :
    Tensor.RankAtMost
      (bankTensor (fun i : BankOccurrences population => E i.1))
      (∏ node, rank node ^ population node) := by
  simpa only [canonical_bank_product] using
    bankTensor_rankAtMost
      (fun i : BankOccurrences population => E i.1)
      (fun i => rank i.1) (fun i => hE i.1)

theorem occurrence_product {M : Type*} [CommMonoid M] [DecidableEq Node]
    (pool : I → Node) (cost : Node → M) :
    (∏ i, cost (pool i)) =
      ∏ node, cost node ^ Fintype.card {i // pool i = node} := by
  rw [← Fintype.prod_fiberwise' pool cost]
  simp

theorem exact_population_product {M : Type*} [CommMonoid M] [DecidableEq Node]
    (pool : I → Node) (population : Node → ℕ)
    (exactPopulation : ∀ node,
      Fintype.card {i // pool i = node} = population node) (cost : Node → M) :
    (∏ i, cost (pool i)) = ∏ node, cost node ^ population node := by
  rw [occurrence_product]
  simp only [exactPopulation]

omit [Fintype Node] in
theorem exact_population_bank_equiv [DecidableEq Node]
    (pool : I → Node) (population : Node → ℕ)
    (exactPopulation : ∀ node,
      Fintype.card {i // pool i = node} = population node) :
    ∃ e : I ≃ BankOccurrences population, ∀ i, (e i).1 = pool i := by
  classical
  let ef : ∀ node, {i // pool i = node} ≃ Fin (population node) :=
    fun node => Fintype.equivOfCardEq (by simp [exactPopulation node])
  refine ⟨(Equiv.sigmaFiberEquiv pool).symm.trans
    (Equiv.sigmaCongrRight ef), ?_⟩
  intro i
  rfl

end Bank

section PrefixSeparation

variable {X Y Z Prefix Label Pairing G : Type*}
variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [DecidableEq Label] [DecidableEq Pairing]

omit [Fintype G] in
theorem prefix_separation_identity
    (T : Tensor ℂ X Y Z)
    (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (tag : Prefix → Label → G) (point : Prefix → Label → Pairing → G)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (collision : ∀ p s s' i j,
      point p s i + (tag p s - point p s j) = tag p s' ↔
        s = s' ∧ i = j) :
    Tensor.pullback
      (fun x : X × Pairing => (x.1, point (px x.1) (lx x.1) x.2))
      (fun y : Y × Pairing =>
        (y.1, tag (py y.1) (ly y.1) - point (py y.1) (ly y.1) y.2))
      (fun z : Z × Label => (z.1, tag (pz z.1) z.2))
      (Tensor.product T (groupTensor G)) = separatedTensor lx T := by
  funext x y z
  by_cases hzero : T x.1 y.1 z.1 = 0
  · simp [Tensor.pullback, Tensor.product, separatedTensor, hzero]
  · obtain ⟨hxy, hxz⟩ := prefixes x.1 y.1 z.1 hzero
    have hl := labels x.1 y.1 z.1 hzero
    simp only [Tensor.pullback, Tensor.product, groupTensor, separatedTensor]
    simp only [← hxy, ← hxz, ← hl, collision, mul_ite, mul_one, mul_zero]

omit [DecidableEq G] in
theorem prefix_separation_rankAtMost
    (T : Tensor ℂ X Y Z)
    (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (tag : Prefix → Label → G) (point : Prefix → Label → Pairing → G)
    {r : ℕ} (hT : Tensor.RankAtMost T r)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (collision : ∀ p s s' i j,
      point p s i + (tag p s - point p s j) = tag p s' ↔
        s = s' ∧ i = j) :
    Tensor.RankAtMost (separatedTensor (U := Pairing) lx T)
      (r * Fintype.card G) := by
  classical
  rw [← prefix_separation_identity T px py pz lx ly tag point
    prefixes labels collision]
  exact (hT.product (groupTensor_rankAtMost G)).pullback _ _ _

@[simp] theorem separated_coefficient
    (T : Tensor ℂ X Y Z) (lx : X → Label)
    (x : X) (y : Y) (z : Z) (u : Pairing) :
    separatedTensor lx T (x, u) (y, u) (z, lx x) = T x y z := by
  simp [separatedTensor]

theorem deterministic_separation_identity
    [Subsingleton Label] [Subsingleton Pairing]
    (T : Tensor ℂ X Y Z) (lx : X → Label) :
    separatedTensor (U := Pairing) lx T =
      Tensor.pullback Prod.fst Prod.fst Prod.fst T := by
  funext x y z
  simp [separatedTensor, Tensor.pullback, Subsingleton.elim (lx x.1) z.2,
    Subsingleton.elim x.2 y.2]

theorem separated_prefix_synchronized
    (T : Tensor ℂ X Y Z)
    (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (x : X × Pairing) (y : Y × Pairing) (z : Z × Label)
    (h : separatedTensor lx T x y z ≠ 0) :
    (px x.1, lx x.1) = (py y.1, ly y.1) ∧
      (px x.1, lx x.1) = (pz z.1, z.2) := by
  have hguard : lx x.1 = z.2 ∧ x.2 = y.2 := by
    by_contra hn
    exact h (by simp [separatedTensor, hn])
  have hT : T x.1 y.1 z.1 ≠ 0 := by
    simpa [separatedTensor, hguard] using h
  obtain ⟨hxy, hxz⟩ := prefixes x.1 y.1 z.1 hT
  exact ⟨Prod.ext hxy (labels x.1 y.1 z.1 hT), Prod.ext hxz hguard.1⟩

end PrefixSeparation

section ExactPools

variable {X Y Z Prefix Label : Type*} [DecidableEq Label]

/-- Choose equally sized finite label pools' enumerations by standard finite sets. -/
noncomputable def poolEnumeration (pool : Prefix → Finset Label) (k : ℕ)
    (counts : ∀ p, (pool p).card = k) : ∀ p, ↥(pool p) ≃ Fin k :=
  fun p => Finset.equivFinOfCardEq (counts p)

/-- Encode an allowed label by its index in the pool selected by its prefix. -/
def poolCode (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (prior : X → Prefix) (label : X → Label)
    (allowed : ∀ x, label x ∈ pool (prior x)) : X → Fin k :=
  fun x => enumerate (prior x) ⟨label x, allowed x⟩

omit [DecidableEq Label] in
@[simp] theorem poolCode_decode (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (prior : X → Prefix) (label : X → Label)
    (allowed : ∀ x, label x ∈ pool (prior x)) (x : X) :
    ((enumerate (prior x)).symm (poolCode pool enumerate prior label allowed x)).val =
      label x := by
  simp [poolCode]

omit [DecidableEq Label] in
theorem poolCode_agree (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (px : X → Prefix) (py : Y → Prefix) (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (x : X) (y : Y) (hp : px x = py y) (hl : lx x = ly y) :
    poolCode pool enumerate px lx ax x = poolCode pool enumerate py ly ay y := by
  have congr_code : ∀ (p q : Prefix) (a : ↥(pool p)) (b : ↥(pool q)),
      p = q → a.val = b.val → enumerate p a = enumerate q b := by
    intro p q a b hp hl
    cases hp
    exact congrArg (enumerate p) (Subtype.ext hl)
  exact congr_code _ _ ⟨lx x, ax x⟩ ⟨ly y, ay y⟩ hp hl

/-- Rank budget for one label pool, using the trivial cost for a singleton pool. -/
noncomputable def poolAuxiliaryCost (k : ℕ) : ℕ :=
  if k = 1 then 1 else Separation.gridGroupOrder k

/-- Ambient finite group chosen to separate a label pool. -/
abbrev PoolAuxiliaryGroup (k : ℕ) :=
  Separation.AuxiliaryGroup (Separation.gridDimension k) (Separation.gridWidth k)

/-- The trivial or group tensor used as one pool's auxiliary resource. -/
noncomputable def poolAuxiliaryTensor (k : ℕ) :
    Tensor ℂ (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) :=
  if k = 1 then Tensor.rankOne (fun _ => 1) (fun _ => 1) (fun _ => 1)
  else groupTensor (PoolAuxiliaryGroup k)

theorem poolAuxiliaryTensor_rankAtMost (k : ℕ) :
    Tensor.RankAtMost (poolAuxiliaryTensor k) (poolAuxiliaryCost k) := by
  classical
  by_cases hk : k = 1
  · simpa only [poolAuxiliaryTensor, poolAuxiliaryCost, ite_eq_left hk] using
      Tensor.rankOne_rankAtMost (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
        (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
        (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
  · simpa only [poolAuxiliaryTensor, poolAuxiliaryCost, ite_eq_right hk,
      PoolAuxiliaryGroup, Separation.card_auxiliaryGroup, Separation.gridGroupOrder]
      using groupTensor_rankAtMost (PoolAuxiliaryGroup k)

omit [DecidableEq Label] in
theorem exact_pool_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T ∈
      Tensor.restrictionOrbit (Tensor.product T
        (groupTensor (Separation.AuxiliaryGroup
          (Separation.gridDimension k) (Separation.gridWidth k)))) := by
  classical
  have hagree : ∀ x y z, T x y z ≠ 0 →
      poolCode pool (poolEnumeration pool k counts) px lx ax x =
        poolCode pool (poolEnumeration pool k counts) py ly ay y := by
    intro x y z h
    exact poolCode_agree pool _ px py lx ly ax ay x y
      (prefixes x y z h) (labels x y z h)
  exact finite_grid_separation_mem_restrictionOrbit T
    (poolCode pool (poolEnumeration pool k counts) px lx ax)
    (poolCode pool (poolEnumeration pool k counts) py ly ay)
    (d := Separation.gridDimension k) (Q := Separation.gridWidth k) (m := k)
    (by simpa only [Fintype.card_fin] using Separation.grid_population_bound k)
    (Separation.grid_population_bound k) hagree

omit [DecidableEq Label] in
theorem exact_pool_raw_prefix_synchronized
    (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (_ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    {Pairing : Type*} [DecidableEq Pairing]
    (x : X × Pairing) (y : Y × Pairing) (z : Z × Fin k)
    (h : separatedTensor (poolCode pool enumerate px lx ax) T x y z ≠ 0) :
    (px x.1, lx x.1) = (py y.1, ly y.1) ∧
      (px x.1, lx x.1) = (pz z.1, ((enumerate (pz z.1)).symm z.2).val) := by
  have guard : poolCode pool enumerate px lx ax x.1 = z.2 ∧ x.2 = y.2 := by
    by_contra hn
    exact h (by simp [separatedTensor, hn])
  have hT : T x.1 y.1 z.1 ≠ 0 := by
    simpa [separatedTensor, guard] using h
  obtain ⟨hxy, hxz⟩ := prefixes x.1 y.1 z.1 hT
  have hz : lx x.1 = ((enumerate (pz z.1)).symm z.2).val := by
    rw [← hxz, ← guard.1]
    exact (poolCode_decode pool enumerate px lx ax x.1).symm
  exact ⟨Prod.ext hxy (labels x.1 y.1 z.1 hT), Prod.ext hxz hz⟩

omit [DecidableEq Label] in
theorem exact_pool_rankAtMost
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    {r : ℕ} (hT : Tensor.RankAtMost T r)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost
      (separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T)
      (r * poolAuxiliaryCost k) := by
  classical
  by_cases hk : k = 1
  · subst k
    have hcost : poolAuxiliaryCost 1 = 1 := by simp [poolAuxiliaryCost]
    rw [hcost, mul_one, deterministic_separation_identity]
    exact hT.pullback (fun x : X × Fin 1 => x.1)
      (fun y : Y × Fin 1 => y.1) (fun z : Z × Fin 1 => z.1)
  · have hagree : ∀ x y z, T x y z ≠ 0 →
        poolCode pool (poolEnumeration pool k counts) px lx ax x =
          poolCode pool (poolEnumeration pool k counts) py ly ay y := by
      intro x y z h
      exact poolCode_agree pool _ px py lx ly ax ay x y
        (prefixes x y z h) (labels x y z h)
    have hr := finite_grid_separation_rankAtMost T
      (poolCode pool (poolEnumeration pool k counts) px lx ax)
      (poolCode pool (poolEnumeration pool k counts) py ly ay)
      (d := Separation.gridDimension k) (Q := Separation.gridWidth k) (m := k)
      (lt_of_lt_of_le (by decide : 0 < 2) (Separation.gridWidth_ge_two k))
      (by simpa only [Fintype.card_fin] using Separation.grid_population_bound k)
      (Separation.grid_population_bound k) hT hagree
    simpa only [poolAuxiliaryCost, ite_eq_right hk, Separation.gridGroupOrder] using hr

omit [DecidableEq Label] in
theorem exact_pool_borderRankAtMost
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    {r : ℕ} (hT : Tensor.BorderRankAtMost T r)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost
      (separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T)
      (r * poolAuxiliaryCost k) := by
  classical
  by_cases hk : k = 1
  · subst k
    have hcost : poolAuxiliaryCost 1 = 1 := by simp [poolAuxiliaryCost]
    rw [hcost, mul_one, deterministic_separation_identity]
    exact hT.pullback (fun x : X × Fin 1 => x.1)
      (fun y : Y × Fin 1 => y.1) (fun z : Z × Fin 1 => z.1)
  · have hagree : ∀ x y z, T x y z ≠ 0 →
        poolCode pool (poolEnumeration pool k counts) px lx ax x =
          poolCode pool (poolEnumeration pool k counts) py ly ay y := by
      intro x y z h
      exact poolCode_agree pool _ px py lx ly ax ay x y
        (prefixes x y z h) (labels x y z h)
    have hr := finite_grid_separation_borderRankAtMost T
      (poolCode pool (poolEnumeration pool k counts) px lx ax)
      (poolCode pool (poolEnumeration pool k counts) py ly ay)
      (d := Separation.gridDimension k) (Q := Separation.gridWidth k) (m := k)
      (lt_of_lt_of_le (by decide : 0 < 2) (Separation.gridWidth_ge_two k))
      (by simpa only [Fintype.card_fin] using Separation.grid_population_bound k)
      (Separation.grid_population_bound k) hT hagree
    simpa only [poolAuxiliaryCost, ite_eq_right hk, Separation.gridGroupOrder] using hr

omit [DecidableEq Label] in
theorem exact_pool_optimized_pullback
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    ∃ (fx : X × Fin k → PoolAuxiliaryGroup k)
      (fy : Y × Fin k → PoolAuxiliaryGroup k)
      (fz : Z × Fin k → PoolAuxiliaryGroup k),
      Tensor.pullback (fun x => (x.1, fx x)) (fun y => (y.1, fy y))
        (fun z => (z.1, fz z)) (Tensor.product T (poolAuxiliaryTensor k)) =
        separatedTensor
          (poolCode pool (poolEnumeration pool k counts) px lx ax) T := by
  classical
  by_cases hk : k = 1
  · subst k
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
    funext x y z
    simp [Tensor.pullback, Tensor.product, poolAuxiliaryTensor, Tensor.rankOne,
      separatedTensor, Subsingleton.elim x.2 y.2,
      Subsingleton.elim (poolCode pool (poolEnumeration pool 1 counts) px lx ax x.1) z.2]
  · obtain ⟨tag, point, collision⟩ := Separation.exists_modular_separation
      (Separation.grid_population_bound k) (Separation.grid_population_bound k)
    have hagree : ∀ x y z, T x y z ≠ 0 →
        poolCode pool (poolEnumeration pool k counts) px lx ax x =
          poolCode pool (poolEnumeration pool k counts) py ly ay y := by
      intro x y z h
      exact poolCode_agree pool _ px py lx ly ax ay x y
        (prefixes x y z h) (labels x y z h)
    refine ⟨fun x => point
        (poolCode pool (poolEnumeration pool k counts) px lx ax x.1) x.2,
      fun y => tag (poolCode pool (poolEnumeration pool k counts) py ly ay y.1) -
        point (poolCode pool (poolEnumeration pool k counts) py ly ay y.1) y.2,
      fun z => tag z.2, ?_⟩
    simpa only [poolAuxiliaryTensor, ite_eq_right hk] using finite_separation_identity T
      (poolCode pool (poolEnumeration pool k counts) px lx ax)
      (poolCode pool (poolEnumeration pool k counts) py ly ay) tag point hagree collision

omit [DecidableEq Label] in
theorem exact_pool_optimized_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T ∈
      Tensor.restrictionOrbit (Tensor.product T (poolAuxiliaryTensor k)) := by
  classical
  obtain ⟨fx, fy, fz, heq⟩ :=
    exact_pool_optimized_pullback pool k counts T px py lx ly ax ay prefixes labels
  rw [← heq]
  exact ⟨_, _, _, Tensor.pullback_eq_restrict _ _ _ _⟩

end ExactPools

section SharedBranches

variable {K X Y Z A B C A' B' C' Label : Type*}
variable [CommSemiring K] [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype A] [Fintype B] [Fintype C] [Fintype Label]

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem shared_branch_rankAtMost
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (MX : Label → X → A' → A → K) (MY : Label → Y → B' → B → K)
    (MZ : Label → Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (synchronized : LocalMaps.SupportedOn (LocalMaps.Synchronized lx ly lz) T)
    [Finite X] [Finite Y] [Finite Z] :
    Tensor.RankAtMost
      (fun x y z => ∑ label,
        LocalMaps.fiberTransform (MX label) (MY label) (MZ label)
          (LocalMaps.originalMask (LocalMaps.InBranch lx ly lz label) T) x y z)
      r := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Fintype Y := Fintype.ofFinite Y
  let : Fintype Z := Fintype.ofFinite Z
  rw [← LocalMaps.controlled_eq_sum_branches_of_supported
    lx ly lz MX MY MZ T synchronized]
  rw [LocalMaps.fiberTransform_eq_restrict]
  exact hT.restrict _ _ _

end SharedBranches

section FiniteAssembly

universe u

variable {K : Type*} [CommSemiring K]
variable {X Y Z A B C : ℕ → Type*}

/-- Coordinate records for the auxiliary tensors accumulated through n stages. -/
def AuxiliaryCoordinates (A : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => AuxiliaryCoordinates A n × A n

instance auxiliaryCoordinatesFintype [∀ n, Fintype (A n)] (n : ℕ) :
    Fintype (AuxiliaryCoordinates A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
      let : Fintype (AuxiliaryCoordinates A n) := ih
      exact inferInstanceAs (Fintype (AuxiliaryCoordinates A n × A n))

/-- Tensor product of the auxiliary resources accumulated through n stages. -/
def auxiliaryTensor (E : ∀ n, Tensor K (A n) (B n) (C n)) :
    ∀ n, Tensor K (AuxiliaryCoordinates A n)
      (AuxiliaryCoordinates B n) (AuxiliaryCoordinates C n)
  | 0 => fun _ _ _ => 1
  | n + 1 => Tensor.product (auxiliaryTensor E n) (E n)

/-- Recover the original source coordinate from successive source-and-auxiliary splittings. -/
def sourceCoordinate (step : ∀ n, X (n + 1) → X n × A n) :
    ∀ n, X n → X 0
  | 0 => id
  | n + 1 => fun x => sourceCoordinate step n (step n x).1

/-- Collect the auxiliary coordinates from successive source-and-auxiliary splittings. -/
def auxiliaryCoordinate (step : ∀ n, X (n + 1) → X n × A n) :
    ∀ n, X n → AuxiliaryCoordinates A n
  | 0 => fun _ => PUnit.unit
  | n + 1 => fun x => (auxiliaryCoordinate step n (step n x).1, (step n x).2)

/-- Execute successive coordinate pullbacks after tensoring in each stage's auxiliary
resource. -/
def stageTensor (T : Tensor K (X 0) (Y 0) (Z 0))
    (E : ∀ n, Tensor K (A n) (B n) (C n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) :
    ∀ n, Tensor K (X n) (Y n) (Z n)
  | 0 => T
  | n + 1 => Tensor.pullback (fx n) (fy n) (fz n)
      (Tensor.product (stageTensor T E fx fy fz n) (E n))

theorem stageTensor_eq_shared_bank
    (T : Tensor K (X 0) (Y 0) (Z 0))
    (E : ∀ n, Tensor K (A n) (B n) (C n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) (n : ℕ) :
    stageTensor T E fx fy fz n =
      Tensor.pullback
        (fun x => (sourceCoordinate fx n x, auxiliaryCoordinate fx n x))
        (fun y => (sourceCoordinate fy n y, auxiliaryCoordinate fy n y))
        (fun z => (sourceCoordinate fz n z, auxiliaryCoordinate fz n z))
        (Tensor.product T (auxiliaryTensor E n)) := by
  induction n with
  | zero =>
      funext x y z
      simp [stageTensor, Tensor.pullback, Tensor.product, sourceCoordinate,
        auxiliaryTensor]
  | succ n ih =>
      funext x y z
      simp only [stageTensor, Tensor.pullback, Tensor.product]
      rw [ih]
      simp only [Tensor.pullback, Tensor.product, sourceCoordinate,
        auxiliaryCoordinate, auxiliaryTensor, mul_assoc]

theorem auxiliaryTensor_rankAtMost
    (E : ∀ n, Tensor K (A n) (B n) (C n)) (r : ℕ → ℕ)
    (hE : ∀ n, Tensor.RankAtMost (E n) (r n)) (n : ℕ) :
    Tensor.RankAtMost (auxiliaryTensor E n) (∏ j ∈ Finset.range n, r j) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_zero]
      refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
      funext x y z
      simp [auxiliaryTensor, Tensor.rankOne]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      exact ih.product (hE n)

theorem stageTensor_rankAtMost
    (T : Tensor K (X 0) (Y 0) (Z 0)) {rT : ℕ}
    (hT : Tensor.RankAtMost T rT)
    (E : ∀ n, Tensor K (A n) (B n) (C n)) (r : ℕ → ℕ)
    (hE : ∀ n, Tensor.RankAtMost (E n) (r n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) (n : ℕ) :
    Tensor.RankAtMost (stageTensor T E fx fy fz n)
      (rT * ∏ j ∈ Finset.range n, r j) := by
  rw [stageTensor_eq_shared_bank]
  exact (hT.product (auxiliaryTensor_rankAtMost E r hE n)).pullback _ _ _

theorem stageTensor_borderRankAtMost
    (T : Tensor ℂ (X 0) (Y 0) (Z 0)) {rT : ℕ}
    (hT : Tensor.BorderRankAtMost T rT)
    (E : ∀ n, Tensor ℂ (A n) (B n) (C n)) (r : ℕ → ℕ)
    (hE : ∀ n, Tensor.RankAtMost (E n) (r n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) (n : ℕ) :
    Tensor.BorderRankAtMost (stageTensor T E fx fy fz n)
      (rT * ∏ j ∈ Finset.range n, r j) := by
  classical
  rw [stageTensor_eq_shared_bank]
  exact (hT.product (auxiliaryTensor_rankAtMost E r hE n).borderRankAtMost).pullback _ _ _

end FiniteAssembly

end LabelHierarchySeparation
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
