/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Convex.MoreauYosida
public import LeanPool.DFT.Lattice.KohnSham.Duality

/-!
# The regularised Kohn–Sham iteration on a lattice

Densities and potentials live in the Euclidean space `ℓ²(V)` (`EuclideanSpace ℝ V`), as in Penz et
al., PRL 123, 037401 (2019). For a symmetric Hamiltonian `H0` and occupations `n`:

* `densDomE n`: the ensemble density domain (compact, convex, nonempty);
* `liebE H0 n`: Lieb's functional on `ℓ²(V)`, convex and lower semicontinuous on the domain
  (`liebE_lsc`);
* `Freg H0 n ε = myEnv (densDomE n) (liebE H0 n) ε`: its Moreau–Yosida regularisation.

Main results:
* `lattice_myksoda`: for an interacting `H0` and a reference `H0'` (e.g. `H0F G t Vint` and
  `H0F G t 0`), the MYKSODA iteration has decreasing energies; every accumulation point `z` is a
  regularised ground-state quasi-density; `ρ = z + ε v` lies in the density domain and minimises
  the Lieb energy, `F(ρ) + v·ρ = E(v)` (that it is the density of a ground-state ensemble is not
  stated); and the Kohn–Sham potentials converge along the subsequence to `v_KS`, for which
  `ρ_KS = z + ε v_KS` minimises the non-interacting Lieb energy (eq. (24) of the paper).
* `lattice_myksoda_exists`: the iteration is well defined from any starting point.
-/

@[expose] public section

open Filter Topology RealInnerProductSpace Matrix

namespace DFT

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [Nonempty C]

/-- The density domain in `ℓ²(V)`. -/
def densDomE (n : V → C → ℝ) : Set (EuclideanSpace ℝ V) := (fun x => WithLp.ofLp x) ⁻¹' DensDomain n

/-- Lieb's functional on `ℓ²(V)`. -/
noncomputable def liebE (H0 : Matrix C C ℝ) (n : V → C → ℝ) (x : EuclideanSpace ℝ V) : ℝ :=
  lieb H0 n (WithLp.ofLp x)

/-- The Moreau–Yosida regularized Lieb functional. -/
noncomputable def Freg (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ε : ℝ) : EuclideanSpace ℝ V → ℝ :=
  myEnv (densDomE n) (liebE H0 n) ε

/-- The gradient of the Moreau–Yosida regularized Lieb functional. -/
noncomputable def gFreg (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ε : ℝ) :
    EuclideanSpace ℝ V → EuclideanSpace ℝ V :=
  myGrad (densDomE n) (liebE H0 n) ε

lemma inner_eq_dot (x y : EuclideanSpace ℝ V) : ⟪x, y⟫ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- The probability vectors on `C`. -/
def probVec (C : Type*) [Fintype C] : Set (C → ℝ) := {lam | (∀ c, 0 ≤ lam c) ∧ ∑ c, lam c = 1}

omit [DecidableEq C] [Nonempty C] in
lemma isCompact_probVec : IsCompact (probVec C) := by
  have hbox : probVec C ⊆ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    rintro lam ⟨h0, h1⟩ c _
    exact ⟨h0 c, h1 ▸ Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ c)⟩
  refine (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset ?_ hbox
  have : probVec C = (⋂ c, {lam : C → ℝ | 0 ≤ lam c}) ∩ {lam | ∑ c, lam c = 1} := by
    ext lam; simp [probVec]
  rw [this]
  exact (isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c)).inter
    (isClosed_eq (f := fun lam : C → ℝ => ∑ c, lam c) (by fun_prop) continuous_const)

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma densDomain_eq (n : V → C → ℝ) :
    DensDomain n = (fun lam : C → ℝ => fun i => ∑ c, lam c * n i c) '' probVec C := by
  ext ρ
  constructor
  · rintro ⟨lam, h0, h1, rfl⟩; exact ⟨lam, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨lam, ⟨h0, h1⟩, rfl⟩; exact ⟨lam, h0, h1, rfl⟩

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma isCompact_densDomain (n : V → C → ℝ) : IsCompact (DensDomain n) := by
  rw [densDomain_eq]
  exact isCompact_probVec.image (by fun_prop)

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma isCompact_densDomE (n : V → C → ℝ) : IsCompact (densDomE n) :=
  (EuclideanSpace.equiv V ℝ).toHomeomorph.isCompact_preimage.mpr (isCompact_densDomain n)

omit [Fintype V] [DecidableEq C] in
lemma densDomE_nonempty (n : V → C → ℝ) : (densDomE n).Nonempty := by
  classical
  obtain ⟨c0⟩ := (inferInstance : Nonempty C)
  refine ⟨WithLp.toLp 2 (fun i => n i c0), fun c => if c = c0 then 1 else 0,
    fun c => by dsimp only; split_ifs <;> norm_num, by simp, ?_⟩
  funext i; simp

lemma convexOn_liebE {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) :
    ConvexOn ℝ (densDomE n) (liebE H0 n) :=
  (lieb_convexOn hH0 n).comp_linearMap (EuclideanSpace.equiv V ℝ).toLinearEquiv.toLinearMap

omit [DecidableEq C] [Fintype V] in
lemma convex_densDomE [Finite V] {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) :
    Convex ℝ (densDomE n) := by
  classical
  let := Fintype.ofFinite V
  exact (convexOn_liebE hH0 n).1

/-- Lieb's functional is lower semicontinuous on the density domain (a supremum of continuous
functions). -/
lemma liebE_lsc {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) :
    LowerSemicontinuousOn (liebE H0 n) (densDomE n) := by
  intro x hx y hy
  obtain ⟨_, ⟨v, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hy
  have hc : Continuous fun x' : EuclideanSpace ℝ V => Egs H0 n v - v ⬝ᵥ WithLp.ofLp x' := by
    have : Continuous fun x' : EuclideanSpace ℝ V => WithLp.ofLp x' :=
        (EuclideanSpace.equiv V ℝ).continuous
    fun_prop
  have hev : ∀ᶠ x' in 𝓝 x, y < Egs H0 n v - v ⬝ᵥ WithLp.ofLp x' :=
    (hc.tendsto x).eventually (lt_mem_nhds hlt)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with x' h1 h2
  exact lt_of_lt_of_le h1 (le_lieb hH0 n h2 v)

lemma isMYSmooth_Freg {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsMYSmooth ε (Freg H0 n ε) (gFreg H0 n ε) :=
  isMYSmooth_myEnv (isCompact_densDomE n) (densDomE_nonempty n) (convex_densDomE hH0 n)
    (convexOn_liebE hH0 n) (liebE_lsc hH0 n) hε

/-- **From quasi-densities back to densities.** If `∇F_ε(z) = -v`, then `ρ = z + ε v` is in the
density domain and minimises `F(ρ) + v·ρ`; its value is the ground-state energy `E(v)`. -/
theorem density_of_quasi {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {ε : ℝ} (hε : 0 < ε)
    {z v : EuclideanSpace ℝ V} (hz : gFreg H0 n ε z = -v) :
    WithLp.ofLp (z + ε • v) ∈ DensDomain n ∧
      lieb H0 n (WithLp.ofLp (z + ε • v)) + WithLp.ofLp v ⬝ᵥ WithLp.ofLp (z + ε • v) =
        Egs H0 n (WithLp.ofLp v) := by
  have hp : prox (densDomE n) (liebE H0 n) ε z = z + ε • v := by
    have := sub_smul_myGrad (D := densDomE n) (f := liebE H0 n) hε z
    unfold gFreg at hz
    rw [hz, smul_neg, sub_neg_eq_add] at this
    exact this.symm
  obtain ⟨hmem, -⟩ :=
      prox_spec (ε := ε) (isCompact_densDomE n) (densDomE_nonempty n) (liebE_lsc hH0 n) z
  rw [hp] at hmem
  refine ⟨hmem, le_antisymm ?_ ((lieb_duality hH0 n _).1 _ hmem)⟩
  -- the minimum over the domain is at most the value at a ground-state density
  obtain ⟨ψ, hψ, hn⟩ := exists_groundState (hamN_isSymm hH0 n (WithLp.ofLp v))
  rw [(lieb_duality hH0 n _).2 ψ hψ hn]
  have hq : WithLp.toLp 2 (dens n ψ) ∈ densDomE n := dens_mem_domain n hn
  have hvi := prox_vi (isCompact_densDomE n) (densDomE_nonempty n) (convex_densDomE hH0 n)
    (convexOn_liebE hH0 n) (liebE_lsc hH0 n) hε z hq
  rw [hp] at hvi
  have e : ε⁻¹ * ⟪z - (z + ε • v), WithLp.toLp 2 (dens n ψ) - (z + ε • v)⟫ =
      -(⟪v, WithLp.toLp 2 (dens n ψ)⟫ - ⟪v, z + ε • v⟫) := by
    rw [sub_add_cancel_left, inner_neg_left, inner_smul_left, inner_sub_right]
    simp only [RCLike.conj_to_real]
    field_simp
  rw [e] at hvi
  simp only [liebE] at hvi
  rw [inner_eq_dot, inner_eq_dot] at hvi
  linarith

variable {ε : ℝ} {H0 H0' : Matrix C C ℝ} {n : V → C → ℝ}

/-- **Convergence of the regularised Kohn–Sham iteration on a lattice** (MYKSODA, corrected
version).

`H0` is the interacting Hamiltonian, `H0'` the non-interacting reference, `v` the external potential
and `ε > 0` the regularisation parameter. The iteration (steps (b), (c)) runs with the Moreau–Yosida
regularised Lieb functionals of both systems. Then:
1. the regularised energies decrease;
2. there is an accumulation point;
3. for every accumulation point `z` (along `φ`):
   * `ρ = z + ε v` lies in the density domain and minimises the interacting Lieb energy:
     `F(ρ) + v·ρ = E(v)`;
   * `z` minimises the regularised energy `F_ε + ⟪v,·⟫`, and the energies of the whole sequence
     converge to this minimum;
   * the Kohn–Sham potentials converge along `φ` to `v_KS`, and `ρ_KS = z + ε v_KS` minimises the
     reference Lieb energy in `v_KS`: `F₀(ρ_KS) + v_KS·ρ_KS = E₀(v_KS)`.
   (That `ρ`, `ρ_KS` are densities of ground-state ensembles is not stated.) -/
theorem lattice_myksoda (hε : 0 < ε) (hH0 : H0.IsSymm) (hH0' : H0'.IsSymm) (v : EuclideanSpace ℝ V)
    {x x' : ℕ → EuclideanSpace ℝ V}
    (hb : ∀ i, gFreg H0' n ε (x' i) = -(v + gFreg H0 n ε (x i) - gFreg H0' n ε (x i)))
    (hc : ∀ i, x (i + 1) = x i + ksStep ε (gFreg H0 n ε (x i) + v) (x' i - x i) • (x' i - x i)) :
    Antitone (fun i => Freg H0 n ε (x i) + ⟪v, x i⟫) ∧
    (∃ z, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 z)) ∧
    ∀ z (φ : ℕ → ℕ), StrictMono φ → Tendsto (x ∘ φ) atTop (𝓝 z) →
      (∀ y, Freg H0 n ε z + ⟪v, z⟫ ≤ Freg H0 n ε y + ⟪v, y⟫) ∧
      Tendsto (fun i => Freg H0 n ε (x i) + ⟪v, x i⟫) atTop (𝓝 (Freg H0 n ε z + ⟪v, z⟫)) ∧
      (WithLp.ofLp (z + ε • v) ∈ DensDomain n ∧
        lieb H0 n (WithLp.ofLp (z + ε • v)) + WithLp.ofLp v ⬝ᵥ WithLp.ofLp (z + ε • v) =
          Egs H0 n (WithLp.ofLp v)) ∧
      ∃ vKS : EuclideanSpace ℝ V,
        Tendsto (fun i => v + gFreg H0 n ε (x (φ i)) - gFreg H0' n ε (x (φ i))) atTop (𝓝 vKS) ∧
        WithLp.ofLp (z + ε • vKS) ∈ DensDomain n ∧
        lieb H0' n (WithLp.ofLp (z + ε • vKS)) + WithLp.ofLp vKS ⬝ᵥ WithLp.ofLp (z + ε • vKS) =
          Egs H0' n (WithLp.ofLp vKS) := by
  have hF := isMYSmooth_Freg hH0 n hε
  have hT := isMYSmooth_Freg hH0' n hε
  obtain ⟨hanti, -, hacc, hlim⟩ := myksoda_converges hε hF hT
    (myEnv_prox_bounded (isCompact_densDomE n) (densDomE_nonempty n) (liebE_lsc hH0' n) hε)
    (myEnv_sublevel_bounded (isCompact_densDomE n) (densDomE_nonempty n) (liebE_lsc hH0 n) hε v) hb
        hc
  refine ⟨hanti, hacc, fun z φ hφ hz => ?_⟩
  obtain ⟨hgz, hmin, hen, hks⟩ := hlim z φ hφ hz
  refine ⟨hmin, hen, density_of_quasi hH0 n hε (eq_neg_of_add_eq_zero_left hgz), -gFreg H0' n ε z,
      hks,
    density_of_quasi hH0' n hε (neg_neg _).symm⟩

/-- **The lattice MYKSODA iteration is well defined** from any starting quasi-density. -/
theorem lattice_myksoda_exists (hε : 0 < ε) (hH0' : H0'.IsSymm) (v x0 : EuclideanSpace ℝ V) :
    ∃ x x' : ℕ → EuclideanSpace ℝ V, x 0 = x0 ∧
      (∀ i, gFreg H0' n ε (x' i) = -(v + gFreg H0 n ε (x i) - gFreg H0' n ε (x i))) ∧
      ∀ i, x (i + 1) = x i + ksStep ε (gFreg H0 n ε (x i) + v) (x' i - x i) • (x' i - x i) :=
  myksoda_exists hε (isMYSmooth_Freg hH0' n hε)
    (fun w c => myEnv_sublevel_bounded (isCompact_densDomE n) (densDomE_nonempty n)
        (liebE_lsc hH0' n) hε w c)
    v x0

end DFT
