/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import LeanPool.MicrowaveNetworks.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Computing with hybrid couplers and phase shifters

A network made of hybrid couplers and phase shifters, interconnected through interconnections
and permutation networks, and connected in series and in parallel, is represented by its
transmission scattering matrix (`Network n`).

## Main definitions

* `interconnection`, `phaseShifter`, `hybridCoupler`, `permutationNetwork`: the components.
* `series`, `parallel`: series and parallel connection of two networks.
* `Implementable`: the networks obtainable from the components by series and parallel
  connections.
* `phaseDiagonal`: the diagonal matrix `diag(exp(j φ₁), …, exp(j φₙ))`.
* `block`: the 2 × 2 block `D(θ₁₁, θ₁₂, θ₂₁)`, implementable with one hybrid coupler and
  three phase shifters.
* `blockDiagonal`: the block diagonal matrix of `C` blocks `D(θ₁₁⁽ᶜ⁾, θ₁₂⁽ᶜ⁾, θ₂₁⁽ᶜ⁾)` and `S`
  phases `exp(j φₛ)`.
* `Layer`: a layer `P_ℓ D_ℓ`, made of a block diagonal matrix `D_ℓ` and a permutation matrix
  `P_ℓ`.
* `layered`: the product `P_L D_L ⋯ P_1 D_1 P_0` of layers and an initial permutation matrix.
* `dft`: the `N × N` discrete Fourier transform (DFT) matrix.

## Main results

* `implementable_iff_layered`: a network is implementable if and only if its transmission
  scattering matrix is `P_L D_L ⋯ P_1 D_1 P_0`, for some permutation matrices `P_ℓ` and block
  diagonal matrices `D_ℓ`.
* `implementable_dft`: the `N × N` DFT, with `N = 2^L`, is implementable.
-/

public section

namespace MiLAC.HybridCouplersPhaseShifters

/-- A hybrid coupler, with transmission scattering matrix `(1/√2) [[j, 1], [1, j]]`. -/
@[expose] noncomputable def hybridCoupler : Network 2 :=
  (1 / Real.sqrt 2 : ℂ) • !![Complex.I, 1; 1, Complex.I]

/-- A network implementable with hybrid couplers, interconnections, phase shifters, and
permutation networks. -/
inductive Implementable : {n : ℕ} → Network n → Prop where
  /-- An interconnection is implementable. -/
  | ic : Implementable interconnection
  /-- A phase shifter is implementable. -/
  | ps (φ : ℝ) : Implementable (phaseShifter φ)
  /-- A permutation network is implementable. -/
  | pn {n : ℕ} (σ : Equiv.Perm (Fin n)) : Implementable (permutationNetwork σ)
  /-- A hybrid coupler is implementable. -/
  | hc : Implementable hybridCoupler
  /-- The series of two implementable networks is implementable. -/
  | series {n : ℕ} {A B : Network n} :
      Implementable A → Implementable B → Implementable (series A B)
  /-- The parallel of two implementable networks is implementable. -/
  | parallel {n m : ℕ} {A : Network n} {B : Network m} :
      Implementable A → Implementable B → Implementable (parallel A B)

/-! ## Preliminary lemmas -/

/-- Permutation matrices multiply anti-homomorphically: `P_τ P_σ = P_(σ * τ)`. -/
lemma permutationNetwork_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permutationNetwork τ * permutationNetwork σ = permutationNetwork (σ * τ) := by
  unfold permutationNetwork
  rw [Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]

/-- Left-multiplying by a permutation matrix permutes the rows. -/
lemma permutationNetwork_mul_eq_submatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Network n) :
    permutationNetwork σ * M = M.submatrix σ id :=
  PEquiv.toMatrix_toPEquiv_mul σ M

/-- Right-multiplying by a permutation matrix permutes the columns. -/
lemma mul_permutationNetwork_eq_submatrix {n : ℕ} (M : Network n) (σ : Equiv.Perm (Fin n)) :
    M * permutationNetwork σ = M.submatrix id σ.symm :=
  PEquiv.mul_toMatrix_toPEquiv M σ

/-- The product of two parallels is the parallel of the products. -/
lemma parallel_mul {n m : ℕ} (A B : Network n) (C D : Network m) :
    parallel A C * parallel B D = parallel (A * B) (C * D) := by
  simp [parallel, Matrix.reindex_apply, Matrix.fromBlocks_multiply]

/-- The parallel of two permutation networks is a permutation network. -/
lemma parallel_permutationNetwork {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    parallel (permutationNetwork σ) (permutationNetwork τ) =
      permutationNetwork (finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)) := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [permutationNetwork, PEquiv.toMatrix_apply, Equiv.permCongr_apply]

/-- Two networks (possibly of syntactically different sizes) are equal up to a relabelling of
their ports. -/
@[expose] def NetEquiv (X Y : Σ n : ℕ, Network n) : Prop :=
  ∃ e : Fin X.1 ≃ Fin Y.1, X.2 = Y.2.submatrix e e

/-- Equality up to a relabelling of the ports is transitive. -/
lemma NetEquiv.trans {X Y Z : Σ n : ℕ, Network n}
    (hXY : NetEquiv X Y) (hYZ : NetEquiv Y Z) : NetEquiv X Z := by
  obtain ⟨e, he⟩ := hXY
  obtain ⟨f, hf⟩ := hYZ
  exact ⟨e.trans f, by rw [he, hf, Matrix.submatrix_submatrix]; rfl⟩

/-- The parallel is commutative, up to a relabelling of the ports. -/
lemma parallel_swap {n m : ℕ} (A : Network n) (B : Network m) :
    NetEquiv ⟨n + m, parallel A B⟩ ⟨m + n, parallel B A⟩ := by
  refine ⟨finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv), ?_⟩
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp

/-- The parallel is associative, up to a relabelling of the ports. -/
lemma parallel_assoc {a b c : ℕ} (A : Network a) (B : Network b) (C : Network c) :
    NetEquiv ⟨a + b + c, parallel (parallel A B) C⟩
      ⟨a + (b + c), parallel A (parallel B C)⟩ := by
  refine ⟨finCongr (add_assoc a b c), ?_⟩
  have h1 : ∀ x : Fin a, finCongr (add_assoc a b c) (Fin.castAdd c (Fin.castAdd b x)) =
      Fin.castAdd (b + c) x := fun x => by ext; simp
  have h2 : ∀ x : Fin b, finCongr (add_assoc a b c) (Fin.castAdd c (Fin.natAdd a x)) =
      Fin.natAdd a (Fin.castAdd c x) := fun x => by ext; simp
  have h3 : ∀ x : Fin c, finCongr (add_assoc a b c) (Fin.natAdd (a + b) x) =
      Fin.natAdd a (Fin.natAdd b x) := fun x => by ext; simp [add_assoc]
  ext i j
  induction i using Fin.addCases with
  | left i =>
      induction i using Fin.addCases <;>
      induction j using Fin.addCases with
      | left j => induction j using Fin.addCases <;> simp [h1, h2]
      | right j => simp [h1, h2, h3]
  | right i =>
      induction j using Fin.addCases with
      | left j => induction j using Fin.addCases <;> simp [h1, h2, h3]
      | right j => simp [h3]

/-- Equality up to a relabelling of the ports is preserved by placing a network below. -/
lemma NetEquiv.parallel_left {X Y : Σ n : ℕ, Network n} (h : NetEquiv X Y) {a : ℕ}
    (A : Network a) :
    NetEquiv ⟨X.1 + a, parallel X.2 A⟩ ⟨Y.1 + a, parallel Y.2 A⟩ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, M⟩ := X
  dsimp only at e he ⊢
  rw [he]
  refine ⟨finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl _)).trans
    finSumFinEquiv), ?_⟩
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp

/-- A network is equal to its relabelling, up to a relabelling of the ports. -/
lemma NetEquiv.reindex {n k : ℕ} (e : Fin k ≃ Fin n) (M : Network k) :
    NetEquiv ⟨n, Matrix.reindex e e M⟩ ⟨k, M⟩ :=
  ⟨e.symm, rfl⟩

/-- The product of two implementable networks is implementable. -/
lemma implementable_mul {n : ℕ} {A B : Network n}
    (hA : Implementable A) (hB : Implementable B) : Implementable (A * B) :=
  Implementable.series hB hA

/-- Permuting the rows and the columns of an implementable network keeps it implementable. -/
lemma implementable_submatrix {n : ℕ} {A : Network n} (hA : Implementable A)
    (σ τ : Equiv.Perm (Fin n)) : Implementable (A.submatrix σ τ) := by
  have h : A.submatrix σ τ =
      permutationNetwork σ * A * permutationNetwork τ.symm := by
    rw [permutationNetwork_mul_eq_submatrix, mul_permutationNetwork_eq_submatrix,
      Matrix.submatrix_submatrix]
    simp
  rw [h]
  exact implementable_mul (implementable_mul (Implementable.pn σ) hA)
    (Implementable.pn τ.symm)

/-- A matrix is implementable on its index type if a finite port relabelling gives
an implementable network. The relabelling witness rules out infinite index types. -/
@[expose] def ImplementableOn {ι : Type*} (M : Matrix ι ι ℂ) : Prop :=
  ∃ (n : ℕ) (e : ι ≃ Fin n), Implementable (Matrix.reindex e e M)

/-- An infinite collection of ports cannot be implemented by a finite network. -/
lemma not_implementableOn_of_infinite {ι : Type*} [Infinite ι] (M : Matrix ι ι ℂ) :
    ¬ImplementableOn M := by
  rintro ⟨n, e, _⟩
  exact (Finite.of_injective e e.injective).false

/-- An implementation after one relabelling witnesses implementability. -/
lemma ImplementableOn.of_equiv {ι : Type*}
    {M : Matrix ι ι ℂ} {m : ℕ} (g : ι ≃ Fin m)
    (h : Implementable (Matrix.reindex g g M)) : ImplementableOn M :=
  ⟨m, g, h⟩

/-- An implementable matrix is implementable after any finite port relabelling. -/
lemma ImplementableOn.to_equiv {ι : Type*} {M : Matrix ι ι ℂ}
    (h : ImplementableOn M) (n : ℕ) (e : ι ≃ Fin n) :
    Implementable (Matrix.reindex e e M) := by
  obtain ⟨m, g, h⟩ := h
  have hmn : m = n := by simpa using Fintype.card_congr (g.symm.trans e)
  subst hmn
  have hM : Matrix.reindex e e M =
      (Matrix.reindex g g M).submatrix (e.symm.trans g) (e.symm.trans g) := by
    ext i j
    simp [Matrix.reindex_apply]
  rw [hM]
  exact implementable_submatrix h _ _

/-- For a network indexed by `Fin n`, `ImplementableOn` is `Implementable`. -/
lemma implementableOn_iff {n : ℕ} (A : Network n) :
    ImplementableOn A ↔ Implementable A := by
  constructor
  · intro h
    simpa using h.to_equiv n (Equiv.refl _)
  · intro h
    exact ImplementableOn.of_equiv (Equiv.refl _) (by simpa using h)

/-- Implementability is invariant under a relabelling of the ports. -/
lemma ImplementableOn.reindex {ι κ : Type*}
    {M : Matrix ι ι ℂ} (h : ImplementableOn M) (f : ι ≃ κ) :
    ImplementableOn (Matrix.reindex f f M) := by
  obtain ⟨n, e, h⟩ := h
  refine ImplementableOn.of_equiv (f.symm.trans e) ?_
  convert h using 1
  ext i j
  simp [Matrix.reindex_apply]

/-- The product of two implementable matrices is implementable. -/
lemma ImplementableOn.mul {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hA : ImplementableOn A) (hB : ImplementableOn B) : ImplementableOn (A * B) := by
  obtain ⟨n, e, hA⟩ := hA
  refine ImplementableOn.of_equiv e ?_
  have hM : Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [hM]
  exact implementable_mul hA (hB.to_equiv n e)

/-- A block diagonal matrix of two implementable matrices is implementable. -/
lemma ImplementableOn.fromBlocks {ι κ : Type*}
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : ImplementableOn A) (hB : ImplementableOn B) :
    ImplementableOn (Matrix.fromBlocks A 0 0 B) := by
  obtain ⟨n, eA, hA⟩ := hA
  obtain ⟨m, eB, hB⟩ := hB
  refine ImplementableOn.of_equiv ((Equiv.sumCongr eA eB).trans finSumFinEquiv) ?_
  have hM : Matrix.reindex ((Equiv.sumCongr eA eB).trans finSumFinEquiv)
      ((Equiv.sumCongr eA eB).trans finSumFinEquiv) (Matrix.fromBlocks A 0 0 B) =
      parallel (Matrix.reindex eA eA A) (Matrix.reindex eB eB B) := by
    ext i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [Matrix.reindex_apply]
  rw [hM]
  exact Implementable.parallel hA hB

/-- A matrix with no ports is implementable. -/
lemma implementableOn_of_isEmpty {ι : Type*} [IsEmpty ι]
    (M : Matrix ι ι ℂ) : ImplementableOn M := by
  refine ImplementableOn.of_equiv (m := 0) (Equiv.equivOfIsEmpty _ _) ?_
  convert Implementable.pn (Equiv.refl (Fin 0)) using 1
  ext i
  exact Fin.elim0 i

/-- A block diagonal matrix with a single implementable block is implementable. -/
lemma ImplementableOn.blockDiagonal_one {m : Type*}
    (g : Fin 1 → Matrix m m ℂ) (h : ImplementableOn (g 0)) :
    ImplementableOn (Matrix.blockDiagonal g) := by
  have hM : Matrix.blockDiagonal g =
      Matrix.reindex (Equiv.prodUnique m (Fin 1)).symm (Equiv.prodUnique m (Fin 1)).symm
        (g 0) := by
    ext ⟨i, c⟩ ⟨j, d⟩
    simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply, Fin.fin_one_eq_zero c,
      Fin.fin_one_eq_zero d]
  rw [hM]
  exact h.reindex _

/-- A block diagonal matrix of implementable blocks is implementable. -/
lemma ImplementableOn.blockDiagonal {m : Type*} :
    ∀ (N : ℕ) (g : Fin N → Matrix m m ℂ), (∀ c, ImplementableOn (g c)) →
      ImplementableOn (Matrix.blockDiagonal g)
  | 0, g, _ => implementableOn_of_isEmpty _
  | N + 1, g, hg => by
      let f : m × Fin (N + 1) ≃ (m × Fin N) ⊕ (m × Fin 1) :=
        (Equiv.prodCongr (Equiv.refl m) finSumFinEquiv.symm).trans
          (Equiv.prodSumDistrib _ _ _)
      have hsplit : Matrix.reindex f f (Matrix.blockDiagonal g) =
          Matrix.fromBlocks (Matrix.blockDiagonal (fun c : Fin N => g (Fin.castAdd 1 c))) 0 0
            (Matrix.blockDiagonal (fun c : Fin 1 => g (Fin.natAdd N c))) := by
        ext (⟨i, c⟩ | ⟨i, c⟩) (⟨j, d⟩ | ⟨j, d⟩)
        all_goals simp [f, Matrix.reindex_apply, Matrix.blockDiagonal_apply]
      have h : ImplementableOn (Matrix.reindex f f (Matrix.blockDiagonal g)) := by
        rw [hsplit]
        exact ImplementableOn.fromBlocks
          (ImplementableOn.blockDiagonal N _ fun c => hg _)
          (ImplementableOn.blockDiagonal_one _ (hg _))
      simpa using h.reindex f.symm

/-- Relabelling the rows and the columns of an implementable matrix into `Fin n` independently
gives an implementable network. -/
lemma ImplementableOn.submatrix_symm {ι : Type*}
    {M : Matrix ι ι ℂ} (h : ImplementableOn M) {n : ℕ} (e₁ e₂ : ι ≃ Fin n) :
    Implementable (M.submatrix e₁.symm e₂.symm) := by
  have hM : M.submatrix e₁.symm e₂.symm =
      Matrix.reindex e₁ e₁ M * permutationNetwork (e₁.symm.trans e₂) := by
    rw [mul_permutationNetwork_eq_submatrix]
    ext i j
    simp [Matrix.reindex_apply]
  rw [hM]
  exact implementable_mul (h.to_equiv n e₁) (Implementable.pn _)

/-! ## Characterization of implementable networks -/

/-- The 2 × 2 block `D(θ₁₁, θ₁₂, θ₂₁)`. -/
@[expose] noncomputable def block (θ₁₁ θ₁₂ θ₂₁ : ℝ) : Network 2 :=
  (1 / Real.sqrt 2 : ℂ) • !![
    Complex.exp (θ₁₁ * Complex.I),
    Complex.exp (θ₁₂ * Complex.I);
    Complex.exp (θ₂₁ * Complex.I),
    Complex.exp ((Real.pi - θ₁₁ + θ₁₂ + θ₂₁) * Complex.I)]

/-- The block diagonal matrix
`diag(D(θ₁₁⁽¹⁾, θ₁₂⁽¹⁾, θ₂₁⁽¹⁾), …, D(θ₁₁⁽ᶜ⁾, θ₁₂⁽ᶜ⁾, θ₂₁⁽ᶜ⁾), exp(j φ₁), …, exp(j φ_S))`. -/
@[expose] noncomputable def blockDiagonal {C S : ℕ}
    (θ₁₁ θ₁₂ θ₂₁ : Fin C → ℝ) (φ : Fin S → ℝ) : Network (2 * C + S) :=
  parallel
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.blockDiagonal fun c => block (θ₁₁ c) (θ₁₂ c) (θ₂₁ c)))
    (phaseDiagonal φ)

/-- A layer `P_ℓ D_ℓ`: a block diagonal matrix `D_ℓ` followed by a permutation matrix `P_ℓ`. -/
structure Layer (n : ℕ) where
  /-- The number of blocks of `D_ℓ`. -/
  C : ℕ
  /-- The number of phases of `D_ℓ`. -/
  S : ℕ
  /-- The parameters `θ₁₁` of the blocks of `D_ℓ`. -/
  θ₁₁ : Fin C → ℝ
  /-- The parameters `θ₁₂` of the blocks of `D_ℓ`. -/
  θ₁₂ : Fin C → ℝ
  /-- The parameters `θ₂₁` of the blocks of `D_ℓ`. -/
  θ₂₁ : Fin C → ℝ
  /-- The phases of `D_ℓ`. -/
  φ : Fin S → ℝ
  /-- `D_ℓ` has `n` ports. -/
  size : 2 * C + S = n
  /-- The permutation of `P_ℓ`. -/
  σ : Equiv.Perm (Fin n)

/-- The product `P_L D_L ⋯ P_1 D_1 P_0`, with layers listed from `L` down to `1`
(`Matrix.reindex` only renames the `2 C + S` ports of `D_ℓ` as the `n` ports of the network). -/
@[expose] noncomputable def layered {n : ℕ} (σ₀ : Equiv.Perm (Fin n)) : List (Layer n) → Network n
  | [] => permutationNetwork σ₀
  | layer :: layers =>
      permutationNetwork layer.σ *
        Matrix.reindex (finCongr layer.size) (finCongr layer.size)
          (blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ) *
        layered σ₀ layers

/-! ### Sufficiency -/

/-- Every phase-only implementation is also an implementation with hybrid couplers available. -/
lemma implementable_of_phaseShifters {n : ℕ} {A : Network n}
    (h : MiLAC.PhaseShifters.Implementable A) : Implementable A := by
  induction h with
  | ic => exact Implementable.ic
  | ps φ => exact Implementable.ps φ
  | pn σ => exact Implementable.pn σ
  | series _ _ hA hB => exact Implementable.series hA hB
  | parallel _ _ hA hB => exact Implementable.parallel hA hB

/-- A diagonal matrix of phases is implementable. -/
lemma implementable_if_phaseDiagonal {n : ℕ} (φ : Fin n → ℝ) :
    Implementable (phaseDiagonal φ) :=
  implementable_of_phaseShifters (MiLAC.PhaseShifters.implementable_if_phaseDiagonal φ)

/-- A block `D(θ₁₁, θ₁₂, θ₂₁)` is implementable, with a phase shifter, a hybrid coupler, and
two phase shifters in series. -/
lemma implementable_if_block (θ₁₁ θ₁₂ θ₂₁ : ℝ) :
    Implementable (block θ₁₁ θ₁₂ θ₂₁) := by
  have hdecomp : block θ₁₁ θ₁₂ θ₂₁ =
      parallel (phaseShifter θ₁₂) (phaseShifter (Real.pi / 2 - θ₁₁ + θ₁₂ + θ₂₁)) *
        hybridCoupler * parallel (phaseShifter (θ₁₁ - θ₁₂ - Real.pi / 2)) interconnection := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block, hybridCoupler, parallel, Matrix.reindex_apply, Matrix.mul_apply,
        Fin.sum_univ_two, phaseShifter, interconnection, finSumFinEquiv, Fin.addCases,
        add_mul, sub_mul, Complex.exp_add, Complex.exp_sub] <;>
      field_simp <;> simp [Complex.I_sq]
  rw [hdecomp]
  exact Implementable.series (Implementable.parallel (Implementable.ps _) Implementable.ic)
    (Implementable.series Implementable.hc
      (Implementable.parallel (Implementable.ps _) (Implementable.ps _)))

/-- A block diagonal matrix is implementable. -/
lemma implementable_if_blockDiagonal {C S : ℕ} (θ₁₁ θ₁₂ θ₂₁ : Fin C → ℝ) (φ : Fin S → ℝ) :
    Implementable (blockDiagonal θ₁₁ θ₁₂ θ₂₁ φ) :=
  Implementable.parallel
    ((ImplementableOn.blockDiagonal C _ fun _ =>
      (implementableOn_iff _).2 (implementable_if_block _ _ _)).to_equiv _ finProdFinEquiv)
    (implementable_if_phaseDiagonal φ)

/-- A network admitting a `layered` decomposition is implementable (sufficient condition). -/
theorem implementable_if_layered {n : ℕ} (σ₀ : Equiv.Perm (Fin n)) (layers : List (Layer n)) :
    Implementable (layered σ₀ layers) := by
  induction layers with
  | nil => exact Implementable.pn σ₀
  | cons layer layers ih =>
      have hD := ((implementableOn_iff _).2
        (implementable_if_blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ)).to_equiv n
          (finCongr layer.size)
      exact implementable_mul (implementable_mul (Implementable.pn _) hD) ih

/-! ### Necessity -/

/-- A network admits a `layered` decomposition. -/
@[expose] def IsLayered {n : ℕ} (S : Network n) : Prop :=
  ∃ σ₀ : Equiv.Perm (Fin n), ∃ layers : List (Layer n), S = layered σ₀ layers

/-- A permutation network admits a `layered` decomposition, with no layers. -/
lemma isLayered_permutationNetwork {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsLayered (permutationNetwork σ) :=
  ⟨σ, [], rfl⟩

/-- Left-multiplying a `layered` decomposition by a permutation matrix only changes its
outermost permutation: `σ₀` (if there are no layers) or the permutation of the topmost layer
(if there are). -/
lemma isLayered_permutationNetwork_mul {n : ℕ} (τ σ₀ : Equiv.Perm (Fin n))
    (layers : List (Layer n)) : IsLayered (permutationNetwork τ * layered σ₀ layers) := by
  cases layers with
  | nil => exact ⟨σ₀ * τ, [], permutationNetwork_mul σ₀ τ⟩
  | cons layer rest =>
      refine ⟨σ₀, { layer with σ := layer.σ * τ } :: rest, ?_⟩
      simp only [layered, ← permutationNetwork_mul layer.σ τ, Matrix.mul_assoc]

/-- The series of two networks admitting a `layered` decomposition admits one. -/
lemma IsLayered.series {n : ℕ} {A B : Network n} (hA : IsLayered A) (hB : IsLayered B) :
    IsLayered (series A B) := by
  obtain ⟨σA, layersA, rfl⟩ := hA
  obtain ⟨σB, layersB, rfl⟩ := hB
  induction layersB with
  | nil => exact isLayered_permutationNetwork_mul σB σA layersA
  | cons layer rest ih =>
      obtain ⟨σ₀, layers, h⟩ := ih
      refine ⟨σ₀, layer :: layers, ?_⟩
      simp only [MiLAC.series, layered, Matrix.mul_assoc] at h ⊢
      rw [h]

/-- The product of two networks admitting a `layered` decomposition admits one. -/
lemma IsLayered.mul {n : ℕ} {A B : Network n} (hA : IsLayered A) (hB : IsLayered B) :
    IsLayered (A * B) :=
  hB.series hA

/-- Admitting a `layered` decomposition is invariant under a relabelling of the ports. -/
lemma IsLayered.of_netEquiv {X Y : Σ n : ℕ, Network n}
    (h : NetEquiv X Y) (hY : IsLayered Y.2) : IsLayered X.2 := by
  obtain ⟨e, he⟩ := h
  obtain ⟨a, A⟩ := X
  obtain ⟨b, B⟩ := Y
  have hab : a = b := by simpa using Fintype.card_congr e
  subst hab
  dsimp only at e he hY ⊢
  have hA : A = permutationNetwork e * B * permutationNetwork e.symm := by
    rw [permutationNetwork_mul_eq_submatrix, mul_permutationNetwork_eq_submatrix,
      Matrix.submatrix_submatrix, he]
    simp
  rw [hA]
  exact ((isLayered_permutationNetwork e).mul hY).mul
    (isLayered_permutationNetwork e.symm)

/-- A block diagonal matrix admits a `layered` decomposition, with one layer. -/
lemma isLayered_blockDiagonal {C S : ℕ} (θ₁₁ θ₁₂ θ₂₁ : Fin C → ℝ) (φ : Fin S → ℝ) :
    IsLayered (blockDiagonal θ₁₁ θ₁₂ θ₂₁ φ) := by
  refine ⟨1, [⟨C, S, θ₁₁, θ₁₂, θ₂₁, φ, rfl, 1⟩], ?_⟩
  simp [layered, permutationNetwork, Equiv.Perm.one_def]

/-- Placing an identity below a diagonal matrix of phases adds zero phases. -/
lemma phaseDiagonal_parallel_one {n : ℕ} (φ : Fin n → ℝ) (m : ℕ) :
    parallel (phaseDiagonal φ) (1 : Network m) = phaseDiagonal (Fin.append φ 0) := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [phaseDiagonal, Matrix.diagonal_apply, Matrix.one_apply]

/-- Placing an identity below the block diagonal matrix of a layer gives a network admitting a
`layered` decomposition. -/
lemma isLayered_parallel_blockDiagonal_one {n : ℕ} (layer : Layer n) (m : ℕ) :
    IsLayered (parallel (Matrix.reindex (finCongr layer.size) (finCongr layer.size)
      (blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ)) (1 : Network m)) := by
  have h : NetEquiv
      ⟨n + m, parallel (Matrix.reindex (finCongr layer.size) (finCongr layer.size)
        (blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ)) (1 : Network m)⟩
      ⟨2 * layer.C + (layer.S + m),
        blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ (Fin.append layer.φ 0)⟩ := by
    refine ((NetEquiv.reindex _ _).parallel_left _).trans ?_
    refine (parallel_assoc _ _ _).trans ?_
    rw [phaseDiagonal_parallel_one]
    exact ⟨Equiv.refl _, rfl⟩
  exact IsLayered.of_netEquiv h (isLayered_blockDiagonal _ _ _ _)

/-- Placing an identity below a network admitting a `layered` decomposition gives a network
admitting one. -/
lemma IsLayered.parallel_one {n : ℕ} {S : Network n}
    (hS : IsLayered S) (m : ℕ) : IsLayered (parallel S (1 : Network m)) := by
  obtain ⟨σ₀, layers, rfl⟩ := hS
  induction layers with
  | nil =>
      have hone : (1 : Network m) = permutationNetwork 1 := by
        simp [permutationNetwork, Equiv.Perm.one_def]
      simp only [layered]
      rw [hone, parallel_permutationNetwork]
      exact isLayered_permutationNetwork _
  | cons layer layers ih =>
      have hone : (1 : Network m) = permutationNetwork 1 * 1 * 1 := by
        simp [permutationNetwork, Equiv.Perm.one_def]
      simp only [layered]
      rw [hone, ← parallel_mul, ← parallel_mul, parallel_permutationNetwork]
      exact ((isLayered_permutationNetwork _).mul
        (isLayered_parallel_blockDiagonal_one layer m)).mul ih

/-- Placing an identity above a network admitting a `layered` decomposition gives a network
admitting one. -/
lemma IsLayered.one_parallel {n : ℕ} {S : Network n}
    (hS : IsLayered S) (m : ℕ) : IsLayered (parallel (1 : Network m) S) :=
  IsLayered.of_netEquiv (X := ⟨m + n, parallel (1 : Network m) S⟩)
    (parallel_swap _ _) (hS.parallel_one m)

/-- The parallel of two networks admitting a `layered` decomposition admits one. -/
lemma IsLayered.parallel {n m : ℕ} {A : Network n} {B : Network m}
    (hA : IsLayered A) (hB : IsLayered B) : IsLayered (parallel A B) := by
  have hsplit : MiLAC.parallel A B =
      MiLAC.parallel A 1 *
        MiLAC.parallel 1 B := by
    rw [parallel_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hsplit]
  exact (hA.parallel_one m).mul (hB.one_parallel n)

/-- A phase shifter admits a `layered` decomposition, with one layer and a single phase. -/
lemma isLayered_phaseShifter (φ : ℝ) : IsLayered (phaseShifter φ) := by
  have h : phaseShifter φ = blockDiagonal (C := 0) Fin.elim0 Fin.elim0 Fin.elim0 ![φ] := by
    ext i j
    fin_cases i
    fin_cases j
    change _ = parallel _ (phaseDiagonal ![φ]) (Fin.natAdd (2 * 0) 0) (Fin.natAdd (2 * 0) 0)
    rw [parallel_natAdd_natAdd]
    simp [phaseDiagonal, phaseShifter]
  rw [h]
  exact isLayered_blockDiagonal _ _ _ _

/-- A hybrid coupler admits a `layered` decomposition, with one layer and the single block
`D(π/2, 0, 0)`. -/
lemma isLayered_hybridCoupler : IsLayered hybridCoupler := by
  have h : hybridCoupler = blockDiagonal ![Real.pi / 2] ![0] ![0] (S := 0) Fin.elim0 := by
    have hI : Complex.exp (((Real.pi : ℂ) - Real.pi / 2) * Complex.I) = Complex.I := by
      rw [show ((Real.pi : ℂ) - Real.pi / 2) = Real.pi / 2 by ring,
        Complex.exp_pi_div_two_mul_I]
    ext i j
    change hybridCoupler i j = parallel _ _ (Fin.castAdd 0 i) (Fin.castAdd 0 j)
    rw [parallel_castAdd_castAdd]
    fin_cases i <;> fin_cases j <;>
      simp [hybridCoupler, block, hI, Matrix.reindex_apply, Matrix.blockDiagonal_apply,
        finProdFinEquiv, Fin.divNat, Fin.modNat]
  rw [h]
  exact isLayered_blockDiagonal _ _ _ _

/-- An implementable network admits a `layered` decomposition (necessary condition). -/
theorem implementable_only_if_layered {n : ℕ}
    {S : Network n} (hS : Implementable S) :
    ∃ σ₀ : Equiv.Perm (Fin n), ∃ layers : List (Layer n), S = layered σ₀ layers := by
  induction hS with
  | ic =>
      rw [interconnection_eq_phaseShifter_zero]
      exact isLayered_phaseShifter 0
  | ps φ => exact isLayered_phaseShifter φ
  | pn σ => exact isLayered_permutationNetwork σ
  | hc => exact isLayered_hybridCoupler
  | series _ _ hA hB => exact IsLayered.series hA hB
  | parallel _ _ hA hB => exact IsLayered.parallel hA hB

/-! ### Main theorem -/

/-- A network is implementable if and only if its transmission scattering matrix is
`P_L D_L ⋯ P_1 D_1 P_0`, for some permutation matrices `P_ℓ` and block diagonal matrices `D_ℓ`. -/
theorem implementable_iff_layered {n : ℕ} {S : Network n} :
    Implementable S ↔
      ∃ σ₀ : Equiv.Perm (Fin n), ∃ layers : List (Layer n), S = layered σ₀ layers := by
  constructor
  · exact implementable_only_if_layered
  · rintro ⟨σ₀, layers, rfl⟩
    exact implementable_if_layered σ₀ layers

/-! ## Discrete Fourier transform -/

/-- The `N × N` DFT matrix, `[F_N]_{i,k} = ω^{ik} / √N` with `ω = exp(-j 2π / N)` (indices
start from 0 here, from 1 in the paper). -/
@[expose] noncomputable def dft (N : ℕ) : Network N :=
  fun i k => (1 / Real.sqrt N : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I * (i : ℕ) * (k : ℕ) / N)

/-- The 2 × 2 butterfly blocks of the radix-2 FFT, `(1/√2) [[1, ω^i], [1, -ω^i]]` with
`ω = exp(-j 2π / 2^(L+1))`. -/
@[expose] noncomputable def butterfly (L : ℕ) (i : Fin (2 ^ L)) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => (1 / Real.sqrt 2 : ℂ) * ((-1) ^ ((a : ℕ) * (b : ℕ)) *
    Complex.exp (-2 * Real.pi * Complex.I * (i : ℕ) * (b : ℕ) / 2 ^ (L + 1)))

/-- Each butterfly block is a block `D(0, -2π i / 2^(L+1), 0)`. -/
lemma butterfly_eq_block (L : ℕ) (i : Fin (2 ^ L)) :
    butterfly L i = block 0 (-2 * Real.pi * (i : ℕ) / 2 ^ (L + 1)) 0 := by
  ext a b
  have h01 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((i : ℕ) : ℂ)) / 2 ^ (L + 1)) =
      Complex.exp (-(2 * (Real.pi : ℂ) * ((i : ℕ) : ℂ)) / 2 ^ (L + 1) * Complex.I) := by
    congr 1
    ring
  have h11 : Complex.exp (((Real.pi : ℂ) + -(2 * (Real.pi : ℂ) * ((i : ℕ) : ℂ)) / 2 ^ (L + 1)) *
      Complex.I) =
      -Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((i : ℕ) : ℂ)) / 2 ^ (L + 1)) := by
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring_nf
  fin_cases a <;> fin_cases b <;> simp [butterfly, block, h01, h11]

/-- The exponential identity behind the radix-2 decomposition of the DFT. -/
lemma dft_exp (L a b i k : ℕ) :
    Complex.exp (-2 * Real.pi * Complex.I * ((i : ℂ) + 2 ^ L * a) * ((b : ℂ) + 2 * k) /
        2 ^ (L + 1)) =
      (-1) ^ (a * b) *
        Complex.exp (-2 * Real.pi * Complex.I * i * b / 2 ^ (L + 1)) *
        Complex.exp (-2 * Real.pi * Complex.I * i * k / 2 ^ L) := by
  have harg : -2 * Real.pi * Complex.I * ((i : ℂ) + 2 ^ L * a) * ((b : ℂ) + 2 * k) /
        2 ^ (L + 1) =
      -2 * Real.pi * Complex.I * i * b / 2 ^ (L + 1) +
        -2 * Real.pi * Complex.I * i * k / 2 ^ L +
        ((-(a * k : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) +
        ((a * b : ℕ) : ℂ) * (-(Real.pi * Complex.I)) := by
    push_cast
    field_simp
    ring
  rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_nat_mul, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  simp
  ring

/-- The `N × N` DFT, with `N = 2^L`, is implementable with hybrid couplers and phase shifters
(Corollary 3 in the paper). -/
theorem implementable_dft (L : ℕ) : Implementable (dft (2 ^ L)) := by
  induction L with
  | zero =>
      have h : dft (2 ^ 0) = interconnection := by
        ext i j
        fin_cases i
        fin_cases j
        simp [dft, interconnection]
      rw [h]
      exact Implementable.ic
  | succ L ih =>
      -- rows are indexed by (a, i) ↦ i + 2^L a, columns by (b, k) ↦ b + 2 k
      let out : Fin 2 × Fin (2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        finProdFinEquiv.trans (finCongr (by ring))
      let inp : Fin 2 × Fin (2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by ring)))
      -- butterflies, and two DFTs of half size in parallel
      let B : Matrix (Fin 2 × Fin (2 ^ L)) (Fin 2 × Fin (2 ^ L)) ℂ :=
        Matrix.blockDiagonal (butterfly L)
      let K : Matrix (Fin 2 × Fin (2 ^ L)) (Fin 2 × Fin (2 ^ L)) ℂ :=
        Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
          (Matrix.blockDiagonal (fun _ : Fin 2 => dft (2 ^ L)))
      have hB : ImplementableOn B := by
        refine ImplementableOn.blockDiagonal _ _ fun i => ?_
        rw [implementableOn_iff, butterfly_eq_block]
        exact implementable_if_block _ _ _
      have hK : ImplementableOn K :=
        (ImplementableOn.blockDiagonal _ _
          fun _ => (implementableOn_iff _).2 ih).reindex _
      have hBK : ∀ a b : Fin 2, ∀ i k : Fin (2 ^ L),
          (B * K) (a, i) (b, k) = butterfly L i a b * dft (2 ^ L) i k := by
        intro a b i k
        rw [Matrix.mul_apply, Fintype.sum_prod_type]
        simp [B, K, Matrix.blockDiagonal_apply, Matrix.reindex_apply]
      have hdft : dft (2 ^ (L + 1)) = (B * K).submatrix out.symm inp.symm := by
        ext x y
        obtain ⟨⟨a, i⟩, rfl⟩ := out.surjective x
        obtain ⟨⟨b, k⟩, rfl⟩ := inp.surjective y
        rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hBK]
        have hx : ((out (a, i) : ℕ) : ℂ) = (i : ℂ) + 2 ^ L * (a : ℕ) := by
          simp [out, finProdFinEquiv]
        have hy : ((inp (b, k) : ℕ) : ℂ) = ((b : ℕ) : ℂ) + 2 * (k : ℕ) := by
          simp [inp, finProdFinEquiv]
        have hs : ((Real.sqrt ((2 ^ (L + 1) : ℕ) : ℝ)) : ℂ) =
            (Real.sqrt 2 : ℂ) * (Real.sqrt ((2 ^ L : ℕ) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]
          push_cast
          ring_nf
        simp only [dft, butterfly]
        rw [hx, hy, hs]
        push_cast
        rw [dft_exp]
        ring
      rw [hdft]
      exact (hB.mul hK).submatrix_symm out inp

end MiLAC.HybridCouplersPhaseShifters
