/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Generic.DensityDim.Gap
public import LeanPool.DFT.Lattice.Generic.Krylov
public import LeanPool.DFT.Lattice.Generic.ZeroSetDim
public import Mathlib.Algebra.MvPolynomial.Monad
meta import Mathlib.Tactic.Abel
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.FinCases
meta import Mathlib.Tactic.GCongr
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.NormNum
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Push

/-!
# Non-uniquely v-representable densities have codimension at least two

`NonUVDens H0 n` is the set of densities of normalised, non-degenerate ground states `ψ` of some
`H(v)` that are also ground states of some `H(v')` with `v - v'` not constant. If the
non-uniquely-v-representable potentials lie in the zero set of a nonzero polynomial (generic HK,
`generic_hk_ae`), then (`M` = number of sites)

* `dimH_nonUVDens_le`: `dimH (NonUVDens H0 n) ≤ M - 3`;
* `dimH_nonUVDens`: if `NonUVDens H0 n` is nonempty, `dimH (NonUVDens H0 n) + 3 ≤ M`.

Densities live in the `(M-1)`-dimensional affine space `Σ_i ρ_i = N`, so the bad densities have
codimension at least two there.

Proof. Split by the support `S` of the bad state and a lower bound on its gap. The bad state is
also the ground state of `H(v - k)` for small `k` in the space `K_S` of potentials constant on `S`
(`persist_gap`), which contains the constants and the non-constant `v - v'`, so `dim K_S ≥ 2`.
Locally, sliding along `K_S` moves each bad potential onto one affine slice `a + W` (`W` a
complement of `K_S`) without changing the density, and onto the zero set of the polynomial. That
zero set within the slice has dimension `≤ dim W - 1 ≤ M - 3`, and the density is a pointwise
Lipschitz function of the potential near gapped ground states (`dens_lipschitz_of_gap`).
-/

@[expose] public section

namespace DFT

open Matrix MvPolynomial Module

section General

/-- Local-to-global bound for the Hausdorff dimension of an image (Lindelöf). -/
theorem dimH_image_le_of_local {X Y : Type*} [EMetricSpace X]
    [SecondCountableTopology X] [EMetricSpace Y] {f : X → Y} {s : Set X}
    {D : ENNReal} (h : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ dimH (f '' (s ∩ U)) ≤ D) :
    dimH (f '' s) ≤ D := by
  choose! U hUo hxU hU using h
  obtain ⟨T, hT, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x : s => U x) (fun x => hUo x x.2)
  have hsub : f '' s ⊆ ⋃ x ∈ T, f '' (s ∩ U x) := by
    rintro _ ⟨y, hy, rfl⟩
    have : y ∈ ⋃ x : s, U x := Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxU y hy⟩
    rw [← hTU] at this
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.mp this
    exact Set.mem_iUnion₂.mpr ⟨x, hxT, y, ⟨hy, hyx⟩, rfl⟩
  calc dimH (f '' s) ≤ dimH (⋃ x ∈ T, f '' (s ∩ U x)) := dimH_mono hsub
    _ = ⨆ x ∈ T, dimH (f '' (s ∩ U x)) := dimH_bUnion hT _
    _ ≤ D := iSup₂_le fun x _ => hU x x.2

/-- Zero set of a polynomial within an affine slice `a + W` on which it does not vanish
identically: `dimH + 1 ≤ dim W`, provided the zero set in the slice is nonempty. -/
theorem dimH_slice_zeroSet_add_one_le {V : Type*} [Fintype V] {P : MvPolynomial V ℝ}
    {W : Submodule ℝ (V → ℝ)} {a w0 : V → ℝ} (hw0 : w0 ∈ W) (hP : eval (a + w0) P ≠ 0)
    (hne : {u : V → ℝ | u - a ∈ W ∧ eval u P = 0}.Nonempty) :
    dimH {u : V → ℝ | u - a ∈ W ∧ eval u P = 0} + 1 ≤ finrank ℝ W := by
  classical
  set d := finrank ℝ W
  let b := finBasis ℝ W
  let e : (Fin d → ℝ) → (V → ℝ) := fun x => a + ∑ j, x j • (b j : V → ℝ)
  set Q : MvPolynomial (Fin d) ℝ :=
    bind₁ (fun i => C (a i) + ∑ j, C ((b j : V → ℝ) i) * X j) P
  have hQe : ∀ x, eval x Q = eval (e x) P := by
    intro x
    change eval₂Hom (RingHom.id ℝ) x _ = eval₂Hom (RingHom.id ℝ) _ P
    rw [eval₂Hom_bind₁]
    congr 2
    funext i
    simp [e, Finset.sum_apply, mul_comm]
    rfl
  have hrepr : ∀ y : W, e (b.repr y) = a + y := by
    intro y
    simp only [e]
    congr 1
    conv_rhs => rw [← b.sum_repr y]
    rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]; rfl
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    have := hQe (b.repr ⟨w0, hw0⟩)
    rw [h, map_zero, hrepr] at this
    exact this.symm
  have hsub : {u : V → ℝ | u - a ∈ W ∧ eval u P = 0} ⊆ e '' {x | eval x Q = 0} := by
    rintro u ⟨hu, hPu⟩
    refine ⟨b.repr ⟨u - a, hu⟩, ?_, ?_⟩
    · change eval _ Q = 0
      rw [hQe, hrepr]; simpa using hPu
    · rw [hrepr]; simp
  have hLip : ∃ K, LipschitzWith K e := by
    let L : (Fin d → ℝ) →ₗ[ℝ] (V → ℝ) := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
    have hL : ∀ x, L x = ∑ j, x j • (b j : V → ℝ) := by
      intro x; simp [L, Module.Basis.equivFun_symm_apply]; rfl
    let L' := LinearMap.toContinuousLinearMap L
    refine ⟨‖L'‖₊, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [e, dist_add_left]
    rw [← hL, ← hL]
    exact L'.lipschitzWith.dist_le_mul x y
  obtain ⟨K, hK⟩ := hLip
  obtain ⟨u, hu⟩ := hne
  obtain ⟨x, hx, -⟩ := hsub hu
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exfalso
    have : x = b.repr ⟨w0, hw0⟩ := funext fun j => absurd j.2 (by omega)
    have h := hQe (b.repr ⟨w0, hw0⟩)
    rw [hrepr, ← this] at h
    exact hP (h.symm.trans hx)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  calc dimH {u : V → ℝ | u - a ∈ W ∧ eval u P = 0} + 1
      ≤ dimH {x : Fin d → ℝ | eval x Q = 0} + 1 :=
        add_le_add_left ((dimH_mono hsub).trans (hK.dimH_image_le _)) 1
    _ ≤ (Fintype.card (Fin d) : ENNReal) := dimH_zeroSet_add_one_le hQ
    _ = d := by simp

end General

section

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- **Non-uniquely v-representable densities of non-degenerate ground states.** Densities of a
normalised ground state `ψ` of `H(v)`, unique up to scale, that is also a ground state of `H(v')`
with `v - v'` not constant. -/
def NonUVDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) : Set (V → ℝ) :=
  {ρ | ∃ (v v' : V → ℝ) (ψ : C → ℝ), IsGroundState (hamN H0 n v) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧
      (∀ φ, IsGroundState (hamN H0 n v) φ → ∃ a : ℝ, φ = a • ψ) ∧
      IsGroundState (hamN H0 n v') ψ ∧ (¬ ∃ k, ∀ i, v i - v' i = k) ∧ dens n ψ = ρ}

omit [DecidableEq C] in
/-- Potentials whose coupling `Σ_i w_i n_i(c)` is constant on the configurations in `S`. -/
def invisible (n : V → C → ℝ) (S : Finset C) : Submodule ℝ (V → ℝ) where
  carrier := {w | ∃ κ : ℝ, ∀ c ∈ S, ∑ i, w i * n i c = κ}
  add_mem' := by
    rintro w w' ⟨κ, hκ⟩ ⟨κ', hκ'⟩
    exact ⟨κ + κ', fun c hc => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hκ c hc, hκ' c hc]⟩
  zero_mem' := ⟨0, fun c _ => by simp⟩
  smul_mem' := by
    rintro r w ⟨κ, hκ⟩
    exact ⟨r * κ, fun c hc => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hκ c hc]⟩

/-- Two potentials sharing a ground state differ by a potential that is constant on its support. -/
lemma sub_mem_invisible {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {v v' : V → ℝ}
    {ψ : C → ℝ} {S : Finset C} (hψ : IsGroundState (hamN H0 n v) ψ)
    (hψ' : IsGroundState (hamN H0 n v') ψ) (hS : ∀ c, c ∈ S ↔ ψ c ≠ 0) :
    v - v' ∈ invisible n S := by
  have e1 := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
  have e2 := isGroundState_eigen (hamN_isSymm hH0 n v') hψ'
  exact ⟨_, fun c hc => potential_sub_eq_on_support e1 e2 ((hS c).mp hc)⟩

omit [Fintype C] [DecidableEq C] in
/-- With a fixed particle number, `invisible n S` contains the constants; with one non-constant
element it has dimension at least two. -/
lemma two_le_finrank_invisible {n : V → C → ℝ} (hN : ∃ N : ℝ, ∀ c, ∑ i, n i c = N)
    {S : Finset C} {u : V → ℝ} (hu : u ∈ invisible n S) (hnc : ¬ ∃ k, ∀ i, u i = k) :
    2 ≤ finrank ℝ (invisible n S) := by
  obtain ⟨N, hN⟩ := hN
  obtain ⟨i0⟩ : Nonempty V := by
    by_contra h; rw [not_nonempty_iff] at h; exact hnc ⟨0, fun i => h.elim i⟩
  have h1 : (fun _ : V => (1 : ℝ)) ∈ invisible n S := ⟨N, fun c _ => by simp [hN c]⟩
  have hli : LinearIndependent ℝ ![(fun _ : V => (1 : ℝ)), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      have := congrFun hst i0
      simp only [zero_smul, add_zero, Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at this
      exact ⟨this, rfl⟩
    · exfalso
      apply hnc
      refine ⟨-s / t, fun i => ?_⟩
      have := congrFun hst i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at this
      field_simp
      linarith
  have hle : Submodule.span ℝ (Set.range ![(fun _ : V => (1 : ℝ)), u]) ≤ invisible n S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact h1
    · exact hu
  calc 2 = finrank ℝ (Submodule.span ℝ (Set.range ![(fun _ : V => (1 : ℝ)), u])) := by
        rw [finrank_span_eq_card hli]; simp
    _ ≤ _ := Submodule.finrank_mono hle

/-- Potentials with a bad (shared, non-trivially) normalised ground state of support `S` and gap at
least `g`. -/
def badSet (H0 : Matrix C C ℝ) (n : V → C → ℝ) (S : Finset C) (g : ℝ) : Set (V → ℝ) :=
  {v | ∃ ψ : C → ℝ, IsGroundState (hamN H0 n v) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧ HasGap (hamN H0 n v) ψ g ∧
    (∀ c, c ∈ S ↔ ψ c ≠ 0) ∧
    ∃ v' : V → ℝ, IsGroundState (hamN H0 n v') ψ ∧ ¬ ∃ k, ∀ i, v i - v' i = k}

/-- Density of a chosen normalised ground state of `H(v)`. -/
noncomputable def gsDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : V → ℝ :=
  dens n (Classical.epsilon fun ψ : C → ℝ => IsGroundState (hamN H0 n v) ψ ∧ ψ ⬝ᵥ ψ = 1)

lemma gsDens_spec [Nonempty C] {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ)
    (v : V → ℝ) :
    ∃ φ, IsGroundState (hamN H0 n v) φ ∧ φ ⬝ᵥ φ = 1 ∧ gsDens H0 n v = dens n φ :=
  have h := Classical.epsilon_spec (exists_groundState (hamN_isSymm hH0 n v))
  ⟨_, h.1, h.2, rfl⟩

omit [Fintype C] [DecidableEq C] in
lemma nonempty_of_isGroundState {H : Matrix C C ℝ} {ψ : C → ℝ} [Fintype C]
    (hψ : IsGroundState H ψ) : Nonempty C := by
  by_contra h; rw [not_nonempty_iff] at h; exact hψ.1 (Subsingleton.elim _ _)

lemma gsDens_eq_of_gap {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {v : V → ℝ}
    {ψ : C → ℝ} (hψ : IsGroundState (hamN H0 n v) ψ) (hn : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : HasGap (hamN H0 n v) ψ g) : gsDens H0 n v = dens n ψ := by
  have := nonempty_of_isGroundState hψ
  obtain ⟨φ, hφ, hφn, h⟩ := gsDens_spec hH0 n v
  rw [h]
  exact dens_eq_of_gap (hamN_isSymm hH0 n v) n hψ hn hg hgap hφ hφn

/-- Local version of the dimension bound around a bad potential. -/
theorem local_dimH_bound {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    (hN : ∃ N : ℝ, ∀ c, ∑ i, n i c = N) {P : MvPolynomial V ℝ} (hP : P ≠ 0)
    (hPZ : ∀ v, NonUV H0 n v → eval v P = 0) {S : Finset C} {g : ℝ} (hg : 0 < g)
    {v0 : V → ℝ} (hv0 : v0 ∈ badSet H0 n S g) :
    ∃ U : Set (V → ℝ), IsOpen U ∧ v0 ∈ U ∧
      dimH (gsDens H0 n '' (badSet H0 n S g ∩ U)) + 3 ≤ Fintype.card V := by
  classical
  obtain ⟨ψ0, hψ0, -, -, hS0, v0', hψ0', hnc0⟩ := id hv0
  set K := invisible n S
  have hK2 : 2 ≤ finrank ℝ K := two_le_finrank_invisible hN
    (sub_mem_invisible hH0 hψ0 hψ0' hS0) (fun ⟨k, hk⟩ => hnc0 ⟨k, fun i => hk i⟩)
  obtain ⟨W, hKW⟩ := Submodule.exists_isCompl K
  have hdim : finrank ℝ K + finrank ℝ W = Fintype.card V := by
    rw [Submodule.finrank_add_eq_of_isCompl hKW, Module.finrank_fintype_fun_eq_card]
  set p := K.projection W hKW
  have hpK : ∀ y, p y ∈ K := fun y => Submodule.projection_apply_mem hKW y
  have hpfix : ∀ y ∈ K, p y = y := fun y hy => Submodule.projection_apply_of_mem_left hKW hy
  have hpW : ∀ y, y - p y ∈ W := by
    intro y
    rw [← Submodule.projection_apply_eq_zero_iff hKW, map_sub, hpfix _ (hpK y), sub_self]
  have hpc : Continuous p := LinearMap.continuous_of_finiteDimensional p
  obtain ⟨cp, hcp0, hp_le⟩ : ∃ cp : ℝ, 0 ≤ cp ∧ ∀ y, ‖p y‖ ≤ cp * ‖y‖ :=
    ⟨‖LinearMap.toContinuousLinearMap p‖, norm_nonneg _,
      fun y => (LinearMap.toContinuousLinearMap p).le_opNorm y⟩
  set Λ := ∑ i, ∑ c', |n i c'|
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  set R := g / (4 * (2 * Λ + 1))
  have hR : 0 < R := by positivity
  have hRg : R * (4 * (2 * Λ + 1)) = g := by simp only [R]; field_simp
  -- the anchor of the slice
  obtain ⟨a, haK, har, w0, hw0, hPa⟩ :
      ∃ a, a - v0 ∈ K ∧ ‖a - v0‖ < R ∧ ∃ w0 ∈ W, eval (a + w0) P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP
    refine eq_zero_of_vanish_on_open (U := {x | ‖p (x - v0)‖ < R}) ?_ (z := v0) ?_ ?_
    · exact isOpen_lt (continuous_norm.comp (hpc.comp (continuous_id.sub continuous_const)))
        continuous_const
    · simp [hR]
    · intro x hx
      have := hcon (v0 + p (x - v0)) (by rw [add_sub_cancel_left]; exact hpK _)
        (by rw [add_sub_cancel_left]; exact hx)
        ((x - v0) - p (x - v0)) (hpW _)
      convert this using 2
      abel_nf
  set r2 := R / (cp + 1)
  have hr2 : 0 < r2 := by positivity
  have hr2R : r2 * (cp + 1) = R := by simp only [r2]; field_simp
  refine ⟨Metric.ball v0 r2, Metric.isOpen_ball, Metric.mem_ball_self hr2, ?_⟩
  set T := {u : V → ℝ | (u - a ∈ W ∧ eval u P = 0) ∧ ∃ (ψ : C → ℝ) (g' : ℝ), 0 < g' ∧
    IsGroundState (hamN H0 n u) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧ HasGap (hamN H0 n u) ψ g'}
  -- each bad potential near `v0` slides into `T` without changing its density
  have hproj : ∀ v ∈ badSet H0 n S g ∩ Metric.ball v0 r2,
      ∃ u ∈ T, gsDens H0 n u = gsDens H0 n v := by
    rintro v ⟨⟨ψ, hψ, hn, hgap, hS, v', hψ', hnc⟩, hv⟩
    set k := p (v - a)
    have hk : ‖k‖ ≤ 2 * R := by
      have hka : k = p (v - v0) + (v0 - a) := by
        change p (v - a) = _
        rw [show v - a = (v - v0) + (v0 - a) by abel, map_add,
          hpfix (v0 - a) (by rw [← neg_sub]; exact K.neg_mem haK)]
      rw [hka]
      have h1 : ‖p (v - v0)‖ ≤ R := by
        have hv' : ‖v - v0‖ < r2 := by rwa [← dist_eq_norm]
        calc ‖p (v - v0)‖ ≤ cp * ‖v - v0‖ := hp_le _
          _ ≤ cp * r2 := mul_le_mul_of_nonneg_left hv'.le hcp0
          _ ≤ R := by nlinarith
      have h2 : ‖v0 - a‖ < R := by rw [norm_sub_rev]; exact har
      linarith [norm_add_le (p (v - v0)) (v0 - a)]
    obtain ⟨κ, hκ⟩ := hpK (v - a)
    obtain ⟨c0, hc0⟩ : ∃ c0, ψ c0 ≠ 0 := by
      by_contra h; push Not at h; exact hψ.1 (funext h)
    have hm : ∀ c, |∑ i, k i * n i c - κ| ≤ 2 * Λ * ‖k‖ := by
      intro c
      have h1 := abs_sum_mul_le n k c
      have h2 := abs_sum_mul_le n k c0
      rw [hκ c0 ((hS c0).mpr hc0)] at h2
      calc |∑ i, k i * n i c - κ| ≤ |∑ i, k i * n i c| + |κ| := abs_sub _ _
        _ ≤ 2 * Λ * ‖k‖ := by linarith
    have hε : |(-1 : ℝ)| * (2 * Λ * ‖k‖) ≤ g / 2 := by
      rw [abs_neg, abs_one, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 2 * Λ)]
    have hpers := persist_gap hH0 hψ hn (ε := -1) hgap (fun c hc => hκ c ((hS c).mpr hc)) hm
      (hε.trans (by linarith))
    set u := v + (-1 : ℝ) • k
    have hgap' : HasGap (hamN H0 n u) ψ (g / 2) := hpers.2.mono (by linarith)
    refine ⟨u, ⟨⟨?_, ?_⟩, ψ, g / 2, by positivity, hpers.1, hn, hgap'⟩, ?_⟩
    · have : u - a = (v - a) - p (v - a) := by simp only [u, k]; module
      rw [this]; exact hpW _
    · apply hPZ
      by_cases hc : ∃ k', ∀ i, u i - v i = k'
      · obtain ⟨k', hk'⟩ := hc
        refine ⟨ψ, v', hpers.1, hψ', fun ⟨k'', hk''⟩ => hnc ⟨k'' - k', fun i => ?_⟩⟩
        have := hk' i; have := hk'' i; linarith
      · exact ⟨ψ, v, hpers.1, hψ, hc⟩
    · rw [gsDens_eq_of_gap hH0 hpers.1 hn (by positivity) hgap', gsDens_eq_of_gap hH0 hψ hn hg hgap]
  have hsub1 : gsDens H0 n '' (badSet H0 n S g ∩ Metric.ball v0 r2) ⊆ gsDens H0 n '' T := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, he⟩ := hproj v hv
    exact ⟨u, hu, he⟩
  have hLipT : dimH (gsDens H0 n '' T) ≤ dimH T := by
    apply dimH_image_le_of_pointwise_lipschitz
    rintro x ⟨-, ψ, g', hg', hψ, hn, hgap⟩
    obtain ⟨Kc, δ, hδ, hK⟩ := dens_lipschitz_of_gap hH0 n hψ hn hg' hgap
    refine ⟨Kc, δ, hδ, fun z _ hz => ?_⟩
    have := nonempty_of_isGroundState hψ
    obtain ⟨φ, hφ, hφn, hzeq⟩ := gsDens_spec hH0 n z
    rw [hzeq, gsDens_eq_of_gap hH0 hψ hn hg' hgap]
    exact hK z φ hφ hφn hz
  have hTsub : T ⊆ {u : V → ℝ | u - a ∈ W ∧ eval u P = 0} := fun u hu => hu.1
  have hTne : T.Nonempty := by
    obtain ⟨u, hu, -⟩ := hproj v0 ⟨hv0, Metric.mem_ball_self hr2⟩
    exact ⟨u, hu⟩
  have hslice := dimH_slice_zeroSet_add_one_le hw0 hPa (hTne.mono hTsub)
  have hW2 : finrank ℝ W + 2 ≤ Fintype.card V := by omega
  calc dimH (gsDens H0 n '' (badSet H0 n S g ∩ Metric.ball v0 r2)) + 3
      ≤ dimH {u : V → ℝ | u - a ∈ W ∧ eval u P = 0} + 1 + 2 := by
        rw [add_assoc, show (1 : ENNReal) + 2 = 3 by norm_num]
        exact add_le_add ((dimH_mono hsub1).trans (hLipT.trans (dimH_mono hTsub))) le_rfl
    _ ≤ (finrank ℝ W : ENNReal) + 2 := by gcongr
    _ ≤ Fintype.card V := by exact_mod_cast hW2

lemma nonUVDens_subset {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) :
    NonUVDens H0 n ⊆ ⋃ (S : Finset C) (m : ℕ), gsDens H0 n '' badSet H0 n S (1 / (m + 1)) := by
  rintro ρ ⟨v, v', ψ, hψ, hn, hu, hψ', hnc, rfl⟩
  obtain ⟨g, hg, hgap⟩ := exists_gap_of_unique hψ hn hu
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hg
  exact Set.mem_iUnion₂.mpr ⟨Finset.univ.filter (fun c => ψ c ≠ 0), m, v,
    ⟨ψ, hψ, hn, hgap.mono hm.le, fun c => by simp, v', hψ', hnc⟩,
    gsDens_eq_of_gap hH0 hψ hn hg hgap⟩

/-- **Non-uv densities have codimension at least two.** If the occupations have a fixed particle
number and all non-uniquely-v-representable potentials are zeros of a nonzero polynomial, then the
densities of non-degenerate ground states shared by potentials differing by more than a constant
have Hausdorff dimension at most `M - 3` (`M` the number of sites; truncated subtraction). -/
theorem dimH_nonUVDens_le {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    (hN : ∃ N : ℝ, ∀ c, ∑ i, n i c = N) {P : MvPolynomial V ℝ} (hP : P ≠ 0)
    (hPZ : ∀ v, NonUV H0 n v → eval v P = 0) :
    dimH (NonUVDens H0 n) ≤ (Fintype.card V : ENNReal) - 3 := by
  refine (dimH_mono (nonUVDens_subset hH0 n)).trans ?_
  rw [dimH_iUnion]
  refine iSup_le fun S => ?_
  rw [dimH_iUnion]
  refine iSup_le fun m => ?_
  apply dimH_image_le_of_local
  intro v0 hv0
  obtain ⟨U, hU, hv0U, hb⟩ := local_dimH_bound hH0 hN hP hPZ (by positivity) hv0
  exact ⟨U, hU, hv0U, ENNReal.le_sub_of_add_le_right (by simp) hb⟩

/-- **Non-uv densities have codimension at least two** (form `dimH + 3 ≤ M`). If there are any
such densities, then `M ≥ 3` and they form a set of Hausdorff dimension at most `M - 3`. -/
theorem dimH_nonUVDens {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    (hN : ∃ N : ℝ, ∀ c, ∑ i, n i c = N) {P : MvPolynomial V ℝ} (hP : P ≠ 0)
    (hPZ : ∀ v, NonUV H0 n v → eval v P = 0) (hne : (NonUVDens H0 n).Nonempty) :
    dimH (NonUVDens H0 n) + 3 ≤ Fintype.card V := by
  obtain ⟨ρ, hρ⟩ := hne
  obtain ⟨S, m, v, hv, -⟩ := Set.mem_iUnion₂.mp (nonUVDens_subset hH0 n hρ)
  obtain ⟨U, -, -, hb⟩ := local_dimH_bound hH0 hN hP hPZ (by positivity) hv
  have h3 : (3 : ENNReal) ≤ Fintype.card V := le_trans le_add_self hb
  calc dimH (NonUVDens H0 n) + 3 ≤ ((Fintype.card V : ENNReal) - 3) + 3 :=
        add_le_add (dimH_nonUVDens_le hH0 hN hP hPZ) le_rfl
    _ = Fintype.card V := tsub_add_cancel_of_le h3

end

end DFT
