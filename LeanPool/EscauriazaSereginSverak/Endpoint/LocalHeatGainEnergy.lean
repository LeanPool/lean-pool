/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityHeatSmooth

/-!
# The energy estimate for smooth zero-initial heat solutions

For a smooth solution `w` of `∂ₜ w - Δ w = H` with compact spatial support and
zero initial value at `t = a`, pairing the equation with `(1 - Δ)^m w` gives

`‖w(t)‖²_{H^m} + ∫_a^b ‖w‖²_{H^{m+1}} ≤ C ∫_a^b ‖H‖²_{H^{m-1}}`

(`lem:local-heat-gain`, step `#fourier-energy-estimate`). At integer order
this pairing is the sum of the `L²` energies of the spatial derivatives
`∂^β w`, `|β| ≤ m`. Each `∂^β w` solves the heat equation with source `∂^β H`,
written in divergence form `∂_k(∂^{β'} H)` when `β = β' ++ [k]` is nonempty,
so that only `m - 1` derivatives of `H` enter. The smooth energy bound
`smoothVorticityEnergyGronwall` then applies to each derivative.

The constant depends on `m` and on an upper bound for `b - a`: the Young
absorption controls only the gradient part of the `H^{m+1}` norm, and the
remaining `‖w‖²_{H^m}` term is handled by Grönwall's inequality.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The iterated spatial coordinate derivative of a space-time field along a
word; the first letter is applied first. -/
@[expose] def spaceTimeWord : List (Fin 3) → (Vec3 × ℝ → ℝ) → Vec3 × ℝ → ℝ
  | [], W => W
  | j :: β, W => spaceTimeWord β (fun p => spatialPartial W j p)

/-- The last letter of a word is the outermost derivative. -/
theorem spaceTimeWord_append (β : List (Fin 3)) (k : Fin 3) (W : Vec3 × ℝ → ℝ) :
    spaceTimeWord (β ++ [k]) W = fun p => spatialPartial (spaceTimeWord β W) k p := by
  induction β generalizing W with
  | nil => rfl
  | cons j β ih => exact ih (fun p => spatialPartial W j p)

/-- Spatial word derivatives of a smooth space-time field are smooth. -/
theorem contDiff_spaceTimeWord (β : List (Fin 3)) {W : Vec3 × ℝ → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) : ContDiff ℝ (⊤ : ℕ∞) (spaceTimeWord β W) := by
  induction β generalizing W with
  | nil => exact hW
  | cons j β ih => exact ih (vorticityHeatSmooth_spatialPartial_contDiff hW j)

/-- On a time slice, the space-time word derivative is the spatial word
derivative of the slice. -/
theorem spaceTimeWord_slice (β : List (Fin 3)) (W : Vec3 × ℝ → ℝ) (t : ℝ) :
    (fun y => spaceTimeWord β W (y, t)) = wordDeriv β (fun y => W (y, t)) := by
  induction β generalizing W with
  | nil => rfl
  | cons j β ih => exact ih (fun p => spatialPartial W j p)

/-- Time differentiation commutes with spatial word derivatives of smooth
fields. -/
theorem timePartial_spaceTimeWord (β : List (Fin 3)) {W : Vec3 × ℝ → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) :
    (fun p : Vec3 × ℝ => timePartial (spaceTimeWord β W) p) =
      spaceTimeWord β (fun q => timePartial W q) := by
  induction β generalizing W with
  | nil => rfl
  | cons j β ih =>
      change (fun p : Vec3 × ℝ =>
          timePartial (spaceTimeWord β (fun q => spatialPartial W j q)) p) =
        spaceTimeWord β (fun q => spatialPartial (fun r => timePartial W r) j q)
      rw [ih (vorticityHeatSmooth_spatialPartial_contDiff hW j)]
      congr 1
      funext q
      exact timePartial_spatialPartial_comm hW q j

/-- The spatial second derivative `∂_k ∂_k` commutes with spatial word
derivatives of smooth fields. -/
theorem spatialSecondPartial_spaceTimeWord (β : List (Fin 3)) (k : Fin 3)
    {W : Vec3 × ℝ → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W) :
    (fun p : Vec3 × ℝ => spatialSecondPartial (spaceTimeWord β W) k k p) =
      spaceTimeWord β (fun q => spatialSecondPartial W k k q) := by
  induction β generalizing W with
  | nil => rfl
  | cons j β ih =>
      change (fun p : Vec3 × ℝ => spatialSecondPartial
          (spaceTimeWord β (fun q => spatialPartial W j q)) k k p) =
        spaceTimeWord β (fun q => spatialPartial (fun r => spatialSecondPartial W k k r) j q)
      rw [ih (vorticityHeatSmooth_spatialPartial_contDiff hW j)]
      congr 1
      funext q
      have hWk := vorticityHeatSmooth_spatialPartial_contDiff hW k
      have h1 : (fun r : Vec3 × ℝ =>
          spatialPartial (fun s : Vec3 × ℝ => spatialPartial W j s) k r) =
          fun r : Vec3 × ℝ => spatialPartial (fun s : Vec3 × ℝ => spatialPartial W k s) j r := by
        funext r
        exact spatialSecondPartial_comm hW r j k
      show spatialPartial (fun r : Vec3 × ℝ =>
          spatialPartial (fun s : Vec3 × ℝ => spatialPartial W j s) k r) k q =
        spatialPartial (fun r : Vec3 × ℝ =>
          spatialPartial (fun s : Vec3 × ℝ => spatialPartial W k s) k r) j q
      rw [h1]
      exact spatialSecondPartial_comm hWk q j k

/-- Spatial differentiation of a difference of smooth fields. -/
theorem spatialPartial_sub_sum {A : Vec3 × ℝ → ℝ} {B : Fin 3 → Vec3 × ℝ → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (B k)) (j : Fin 3)
    (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => A q - ∑ k : Fin 3, B k q) j p =
      spatialPartial A j p - ∑ k : Fin 3, spatialPartial (B k) j p := by
  have hS : ContDiff ℝ (⊤ : ℕ∞) (fun q => ∑ k : Fin 3, B k q) :=
    ContDiff.sum (s := Finset.univ) fun k _ => hB k
  have hAS : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q - ∑ k : Fin 3, B k q) :=
    hA.sub hS
  rw [vorticityHeatSmooth_spatialPartial_eq hAS, vorticityHeatSmooth_spatialPartial_eq hA]
  simp_rw [vorticityHeatSmooth_spatialPartial_eq (hB _)]
  have hAd : DifferentiableAt ℝ A p := hA.differentiable (by simp) p
  have hBd (k : Fin 3) : DifferentiableAt ℝ (B k) p := (hB k).differentiable (by simp) p
  rw [fderiv_fun_sub hAd (DifferentiableAt.fun_sum fun k _ => hBd k),
    fderiv_fun_sum fun k _ => hBd k]
  simp

/-- Spatial word derivatives are linear on smooth fields. -/
theorem spaceTimeWord_sub_sum (β : List (Fin 3)) {A : Vec3 × ℝ → ℝ}
    {B : Fin 3 → Vec3 × ℝ → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (B k)) :
    spaceTimeWord β (fun q => A q - ∑ k : Fin 3, B k q) =
      fun p => spaceTimeWord β A p - ∑ k : Fin 3, spaceTimeWord β (B k) p := by
  induction β generalizing A B with
  | nil => rfl
  | cons j β ih =>
      change spaceTimeWord β (fun p : Vec3 × ℝ =>
          spatialPartial (fun q : Vec3 × ℝ => A q - ∑ k : Fin 3, B k q) j p) =
        fun p => spaceTimeWord β (fun q => spatialPartial A j q) p -
          ∑ k : Fin 3, spaceTimeWord β (fun q => spatialPartial (B k) j q) p
      rw [show (fun p : Vec3 × ℝ =>
          spatialPartial (fun q : Vec3 × ℝ => A q - ∑ k : Fin 3, B k q) j p) =
          fun p => spatialPartial A j p - ∑ k : Fin 3, spatialPartial (B k) j p from
        funext (spatialPartial_sub_sum hA hB j)]
      exact ih (vorticityHeatSmooth_spatialPartial_contDiff hA j)
        (fun k => vorticityHeatSmooth_spatialPartial_contDiff (hB k) j)

/-- Fields vanishing outside a compact spatial set keep this property under
spatial differentiation. -/
theorem spatialPartial_eq_zero_of_compl {K : Set Vec3} (hK : IsCompact K)
    {V : Vec3 × ℝ → ℝ} (hV : ∀ x, x ∉ K → ∀ t, V (x, t) = 0) (j : Fin 3) :
    ∀ x, x ∉ K → ∀ t, spatialPartial V j (x, t) = 0 := by
  intro x hx t
  have hev : (fun y : Vec3 => V (y, t)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hV y hy t
  change (fderiv ℝ (fun y : Vec3 => V (y, t)) x) (basisVec j) = 0
  rw [hev.fderiv_eq]
  simp

/-- Fields vanishing outside a compact spatial set keep this property under
time differentiation. -/
theorem timePartial_eq_zero_of_compl {K : Set Vec3}
    {V : Vec3 × ℝ → ℝ} (hV : ∀ x, x ∉ K → ∀ t, V (x, t) = 0) :
    ∀ x, x ∉ K → ∀ t, timePartial V (x, t) = 0 := by
  intro x hx t
  have hfun : (fun s : ℝ => V (x, s)) = fun _ => 0 := funext fun s => hV x hx s
  change (fderiv ℝ (fun s : ℝ => V (x, s)) t) 1 = 0
  rw [hfun]
  simp

/-- Word derivatives of fields vanishing outside a compact spatial set vanish
there too. -/
theorem spaceTimeWord_eq_zero_of_compl {K : Set Vec3} (hK : IsCompact K)
    (β : List (Fin 3)) {V : Vec3 × ℝ → ℝ} (hV : ∀ x, x ∉ K → ∀ t, V (x, t) = 0) :
    ∀ x, x ∉ K → ∀ t, spaceTimeWord β V (x, t) = 0 := by
  induction β generalizing V with
  | nil => exact hV
  | cons j β ih => exact ih (spatialPartial_eq_zero_of_compl hK hV j)

/-- Word derivatives of a field vanishing on a time slice vanish on that
slice. -/
theorem spaceTimeWord_eq_zero_of_slice (β : List (Fin 3)) {V : Vec3 × ℝ → ℝ} {a : ℝ}
    (hV : ∀ x, V (x, a) = 0) : ∀ x, spaceTimeWord β V (x, a) = 0 := by
  induction β generalizing V with
  | nil => exact hV
  | cons j β ih =>
      apply ih
      intro x
      have hfun : (fun y : Vec3 => V (y, a)) = fun _ => 0 := funext hV
      change (fderiv ℝ (fun y : Vec3 => V (y, a)) x) (basisVec j) = 0
      rw [hfun]
      simp

theorem spatialPartial_const_zero (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j p = 0 := by
  change (fderiv ℝ (fun _ : Vec3 => (0 : ℝ)) p.1) (basisVec j) = 0
  simp

theorem timePartial_const_zero (p : Vec3 × ℝ) :
    timePartial (fun _ : Vec3 × ℝ => (0 : ℝ)) p = 0 := by
  change (fderiv ℝ (fun _ : ℝ => (0 : ℝ)) p.2) 1 = 0
  simp

theorem spatialSecondPartial_const_zero (j k : Fin 3) (p : Vec3 × ℝ) :
    spatialSecondPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j k p = 0 := by
  have h : (fun w : ParabolicPoint => spatialPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j w) =
      fun _ => 0 := funext fun w => spatialPartial_const_zero j w
  unfold spatialSecondPartial
  rw [h]
  exact spatialPartial_const_zero k p

/-- The smooth energy bound for a scalar solution of
`∂ₜ z - Δ z = Σ_j ∂_j F_j + g` with compact spatial support and zero value at
`t = a`. -/
theorem scalarHeatEnergy_smooth {a b : ℝ} (hab : a ≤ b) {z g : Vec3 × ℝ → ℝ}
    {F : Fin 3 → Vec3 × ℝ → ℝ} (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j)) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {K : Set Vec3} (hK : IsCompact K)
    (hzero : ∀ x, x ∉ K → ∀ t, z (x, t) = 0 ∧ (∀ j, F j (x, t) = 0) ∧ g (x, t) = 0)
    (heq : ∀ p : Vec3 × ℝ, timePartial z p - ∑ j : Fin 3, spatialSecondPartial z j j p =
      ∑ j : Fin 3, spatialPartial (F j) j p + g p)
    (hinit : ∀ x, z (x, a) = 0) :
    let f := fun s => 2 * (∫ x : Vec3, ∑ j : Fin 3, F j (x, s) ^ 2) + ∫ x : Vec3, g (x, s) ^ 2
    (∀ t ∈ Icc a b, ∫ x : Vec3, z (x, t) ^ 2 ≤ Real.exp (b - a) * ∫ s in a..b, f s) ∧
    (∫ t in a..b, ∫ x : Vec3, ∑ j : Fin 3, spatialPartial z j (x, t) ^ 2) ≤
      (1 + (b - a) * Real.exp (b - a)) * ∫ s in a..b, f s := by
  intro f
  let zv : Vec3 × ℝ → Vec3 := fun p => ![z p, 0, 0]
  let Fv : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun p j => ![F j p, 0, 0]
  let gv : Vec3 × ℝ → Vec3 := fun p => ![g p, 0, 0]
  let v : Vec3 × ℝ → Vec3 := fun _ => 0
  have hvec {W : Vec3 × ℝ → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W) :
      ContDiff ℝ (⊤ : ℕ∞) (fun p => (![W p, 0, 0] : Vec3)) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · exact hW
    · exact contDiff_const
    · exact contDiff_const
  have hsq (c : ℝ) : ∑ i : Fin 3, ((![c, 0, 0] : Vec3) i) ^ 2 = c ^ 2 := by
    simp [Fin.sum_univ_three]
  obtain ⟨he, hd⟩ := smoothVorticityEnergyGronwall (a := a) (b := b) (M := 0) (e₀ := 0)
    (v := v) (z := zv) (F := Fv) (g := gv) hab le_rfl contDiff_const (hvec hz)
    (fun j i => (contDiff_pi.1 (hvec (hF j))) i) (hvec hg)
    ⟨K, hK, fun x hx t => by
      obtain ⟨h1, h2, h3⟩ := hzero x hx t
      refine ⟨?_, fun j i => ?_, ?_⟩
      · funext i
        fin_cases i <;> simp [zv, h1]
      · fin_cases i <;> simp [Fv, h2 j]
      · funext i
        fin_cases i <;> simp [gv, h3]⟩
    (fun x t i => by
      fin_cases i
      · change timePartial z (x, t) - ∑ j : Fin 3, spatialSecondPartial z j j (x, t) =
          -(∑ j : Fin 3, spatialPartial
              (fun w : Vec3 × ℝ => (0 : ℝ) * z w - zv w j * 0) j (x, t)) +
            ∑ j : Fin 3, spatialPartial (F j) j (x, t) + g (x, t)
        have h0 (j : Fin 3) :
            (fun w : Vec3 × ℝ => (0 : ℝ) * z w - zv w j * 0) = fun _ => 0 := by
          funext w
          simp
        simp only [h0, spatialPartial_const_zero, Finset.sum_const_zero, neg_zero, zero_add]
        exact heq (x, t)
      · change timePartial (fun _ : Vec3 × ℝ => (0 : ℝ)) (x, t) -
            ∑ j : Fin 3, spatialSecondPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j j (x, t) =
          -(∑ j : Fin 3, spatialPartial
              (fun w : Vec3 × ℝ => (0 : ℝ) * 0 - zv w j * 0) j (x, t)) +
            ∑ j : Fin 3, spatialPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j (x, t) + 0
        have h0 (j : Fin 3) :
            (fun w : Vec3 × ℝ => (0 : ℝ) * 0 - zv w j * 0) = fun _ => 0 := by
          funext w
          simp
        simp only [h0, spatialPartial_const_zero, spatialSecondPartial_const_zero,
          timePartial_const_zero, Finset.sum_const_zero, neg_zero, sub_zero, add_zero]
      · change timePartial (fun _ : Vec3 × ℝ => (0 : ℝ)) (x, t) -
            ∑ j : Fin 3, spatialSecondPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j j (x, t) =
          -(∑ j : Fin 3, spatialPartial
              (fun w : Vec3 × ℝ => (0 : ℝ) * 0 - zv w j * 0) j (x, t)) +
            ∑ j : Fin 3, spatialPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j (x, t) + 0
        have h0 (j : Fin 3) :
            (fun w : Vec3 × ℝ => (0 : ℝ) * 0 - zv w j * 0) = fun _ => 0 := by
          funext w
          simp
        simp only [h0, spatialPartial_const_zero, spatialSecondPartial_const_zero,
          timePartial_const_zero, Finset.sum_const_zero, neg_zero, sub_zero, add_zero])
    (fun x t => by simp [v, vec3EuclideanNorm])
    (by simp [zv, hinit, hsq])
  have hdpt (j : Fin 3) (p : Vec3 × ℝ) :
      ∑ i : Fin 3, (spatialPartial (fun w : Vec3 × ℝ => zv w i) j p) ^ 2 =
        (spatialPartial z j p) ^ 2 := by
    rw [Fin.sum_univ_three]
    change (spatialPartial z j p) ^ 2 +
        (spatialPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j p) ^ 2 +
        (spatialPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j p) ^ 2 = _
    rw [spatialPartial_const_zero]
    ring
  have hFpt (p : Vec3 × ℝ) :
      ∑ j : Fin 3, ∑ i : Fin 3, (Fv p j i) ^ 2 = ∑ j : Fin 3, F j p ^ 2 := by
    simp [Fv, hsq]
  simp only [hdpt, hFpt] at he hd
  simp only [zv, gv, hsq] at he hd
  have hc : (72 * (0 : ℝ) ^ 2 + 1) * (b - a) = b - a := by ring
  rw [hc] at he hd
  simp only [zero_add] at he hd
  refine ⟨fun t ht => he t ht, ?_⟩
  refine hd.trans (le_of_eq ?_)
  ring

/-- The spatial `L²` energy of a continuous field vanishing outside a compact
spatial set is continuous in time. -/
theorem continuous_integral_sq_of_compl {V : Vec3 × ℝ → ℝ} (hV : Continuous V)
    {K : Set Vec3} (hK : IsCompact K) (h0 : ∀ x, x ∉ K → ∀ t, V (x, t) = 0) :
    Continuous fun s => ∫ x : Vec3, V (x, s) ^ 2 := by
  have heq : (fun s => ∫ x : Vec3, V (x, s) ^ 2) = fun s => ∫ x in K, V (x, s) ^ 2 := by
    funext s
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    simp [h0 x hx s]
  rw [heq]
  have hc : Continuous (Function.uncurry fun (s : ℝ) (x : Vec3) => V (x, s) ^ 2) :=
    (hV.comp (continuous_snd.prodMk continuous_fst)).pow 2
  exact continuous_parametric_integral_of_continuous hc hK

/-- Every word of length at most `m + 1` is empty or a word of length at most
`m` followed by one letter. -/
theorem sum_sobolevWords_succ_le (m : ℕ) (φ : List (Fin 3) → ℝ) (hφ : ∀ α, 0 ≤ φ α) :
    ∑ γ ∈ sobolevWords (m + 1), φ γ ≤
      φ [] + ∑ β ∈ sobolevWords m, ∑ j : Fin 3, φ (β ++ [j]) := by
  classical
  let S : Finset (List (Fin 3)) :=
    insert [] ((sobolevWords m ×ˢ (Finset.univ : Finset (Fin 3))).image
      fun q => q.1 ++ [q.2])
  have hsub : sobolevWords (m + 1) ⊆ S := by
    intro γ hγ
    rw [mem_sobolevWords] at hγ
    by_cases hnil : γ = []
    · simp [S, hnil]
    · refine Finset.mem_insert_of_mem (Finset.mem_image.2
        ⟨(γ.dropLast, γ.getLast hnil), ?_, List.dropLast_append_getLast hnil⟩)
      simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_sobolevWords,
        List.length_dropLast]
      omega
  have hinj : Set.InjOn (fun q : List (Fin 3) × Fin 3 => q.1 ++ [q.2])
      ↑(sobolevWords m ×ˢ (Finset.univ : Finset (Fin 3))) := by
    intro q _ q' _ h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    exact Prod.ext h1 h2
  calc
    ∑ γ ∈ sobolevWords (m + 1), φ γ ≤ ∑ γ ∈ S, φ γ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun α _ _ => hφ α
    _ ≤ φ [] + ∑ γ ∈ (sobolevWords m ×ˢ (Finset.univ : Finset (Fin 3))).image
          (fun q => q.1 ++ [q.2]), φ γ := by
      by_cases hmem : ([] : List (Fin 3)) ∈ (sobolevWords m ×ˢ
          (Finset.univ : Finset (Fin 3))).image (fun q => q.1 ++ [q.2])
      · simp only [S, Finset.insert_eq_of_mem hmem]
        linarith only [hφ []]
      · rw [Finset.sum_insert hmem]
    _ = φ [] + ∑ β ∈ sobolevWords m, ∑ j : Fin 3, φ (β ++ [j]) := by
      rw [Finset.sum_image hinj, Finset.sum_product]

/-- `lem:local-heat-gain`, step `#fourier-energy-estimate`, with the constant
depending on `m` and on an upper bound `L` for `b - a`. -/
theorem localHeatGain_fourierEnergy (m : ℕ) (hm : m = 1 ∨ m = 2) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ) (w : Vec3 × ℝ → ℝ), a < b → b - a ≤ L →
      ContDiff ℝ (⊤ : ℕ∞) w →
      (∃ K : Set Vec3, IsCompact K ∧ ∀ x, x ∉ K → ∀ t, w (x, t) = 0) →
      (∀ x, w (x, a) = 0) →
      ∀ t ∈ Icc a b,
        sobolevNormSqOn m univ (fun α => wordDeriv α (fun y => w (y, t))) +
            ∫ s in a..b, sobolevNormSqOn (m + 1) univ
              (fun α => wordDeriv α (fun y => w (y, s))) ≤
          C * ∫ s in a..b, sobolevNormSqOn (m - 1) univ
            (fun α => wordDeriv α (fun y => timePartial w (y, s) -
              ∑ j : Fin 3, spatialSecondPartial w j j (y, s))) := by
  have hm1 : 1 ≤ m := by rcases hm with h | h <;> omega
  let N : ℝ := (sobolevWords m).card
  let E : ℝ := Real.exp L
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hE : 0 ≤ E := (Real.exp_pos L).le
  refine ⟨2 * (N * E + L * E + N * (1 + L * E)), by positivity, ?_⟩
  intro a b w hab hbL hw ⟨K, hK, hwK⟩ hw0 t ht
  have hab' : a ≤ b := hab.le
  -- the source
  let H : Vec3 × ℝ → ℝ := fun q => timePartial w q - ∑ k : Fin 3, spatialSecondPartial w k k q
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => timePartial w q) :=
    vorticityHeatSmooth_timePartial_contDiff hw
  have hB (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => spatialSecondPartial w k k q) :=
    vorticityHeatSmooth_spatialPartial_contDiff
      (vorticityHeatSmooth_spatialPartial_contDiff hw k) k
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hA.sub (ContDiff.sum (s := Finset.univ) fun k _ => hB k)
  have hHK : ∀ x, x ∉ K → ∀ s, H (x, s) = 0 := by
    intro x hx s
    have h1 := timePartial_eq_zero_of_compl hwK x hx s
    have h2 (k : Fin 3) : spatialSecondPartial w k k (x, s) = 0 :=
      spatialPartial_eq_zero_of_compl hK (spatialPartial_eq_zero_of_compl hK hwK k) k x hx s
    simp only [H, h1, h2, Finset.sum_const_zero, sub_zero]
  -- the equation for each word derivative
  have hwordEq (β : List (Fin 3)) (p : Vec3 × ℝ) :
      timePartial (spaceTimeWord β w) p -
          ∑ k : Fin 3, spatialSecondPartial (spaceTimeWord β w) k k p =
        spaceTimeWord β H p := by
    have h1 : timePartial (spaceTimeWord β w) p =
        spaceTimeWord β (fun q => timePartial w q) p :=
      congrFun (timePartial_spaceTimeWord β hw) p
    have h2 (k : Fin 3) : spatialSecondPartial (spaceTimeWord β w) k k p =
        spaceTimeWord β (fun q => spatialSecondPartial w k k q) p :=
      congrFun (spatialSecondPartial_spaceTimeWord β k hw) p
    have h3 : spaceTimeWord β (fun q => timePartial w q -
          ∑ k : Fin 3, spatialSecondPartial w k k q) p =
        spaceTimeWord β (fun q => timePartial w q) p -
          ∑ k : Fin 3, spaceTimeWord β (fun q => spatialSecondPartial w k k q) p :=
      congrFun (spaceTimeWord_sub_sum β hA hB) p
    rw [h1, Finset.sum_congr rfl fun k _ => h2 k]
    exact h3.symm
  -- the norm of the source
  let Nsq : ℝ → ℝ := fun s => ∑ α ∈ sobolevWords (m - 1), ∫ x : Vec3, spaceTimeWord α H (x, s) ^ 2
  have hNsq_nonneg (s : ℝ) : 0 ≤ Nsq s :=
    Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hcontWord (β : List (Fin 3)) {V : Vec3 × ℝ → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
      (hVK : ∀ x, x ∉ K → ∀ s, V (x, s) = 0) :
      Continuous fun s => ∫ x : Vec3, spaceTimeWord β V (x, s) ^ 2 :=
    continuous_integral_sq_of_compl (contDiff_spaceTimeWord β hV).continuous hK
      (spaceTimeWord_eq_zero_of_compl hK β hVK)
  have hNsq_cont : Continuous Nsq :=
    continuous_finsetSum _ fun α _ => hcontWord α hH hHK
  have hNsq_eq (s : ℝ) : sobolevNormSqOn (m - 1) univ
      (fun α => wordDeriv α (fun y => timePartial w (y, s) -
        ∑ j : Fin 3, spatialSecondPartial w j j (y, s))) = Nsq s := by
    unfold sobolevNormSqOn
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Measure.restrict_univ]
    congr 1
    funext x
    show (wordDeriv α (fun y => H (y, s)) x) ^ 2 = _
    rw [← spaceTimeWord_slice α H s]
  have hJ : 0 ≤ ∫ s in a..b, Nsq s :=
    intervalIntegral.integral_nonneg hab' fun s _ => hNsq_nonneg s
  -- energy bounds for each word derivative
  have hword (β : List (Fin 3)) (hβ : β ∈ sobolevWords m) :
      (∀ t ∈ Icc a b, ∫ x : Vec3, spaceTimeWord β w (x, t) ^ 2 ≤
        Real.exp (b - a) * (2 * ∫ s in a..b, Nsq s)) ∧
      (∫ t in a..b, ∫ x : Vec3, ∑ j : Fin 3, spatialPartial (spaceTimeWord β w) j (x, t) ^ 2) ≤
        (1 + (b - a) * Real.exp (b - a)) * (2 * ∫ s in a..b, Nsq s) := by
    rw [mem_sobolevWords] at hβ
    have hzβ := contDiff_spaceTimeWord β hw
    have hzβK := spaceTimeWord_eq_zero_of_compl hK β hwK
    have hzβa := spaceTimeWord_eq_zero_of_slice β hw0
    -- the source in the form `Σ_j ∂_j F_j + g`
    obtain ⟨F, g, hF, hg, hFK, hgK, hsrc, hf⟩ : ∃ (F : Fin 3 → Vec3 × ℝ → ℝ)
        (g : Vec3 × ℝ → ℝ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j)) ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ j x, x ∉ K → ∀ s, F j (x, s) = 0) ∧ (∀ x, x ∉ K → ∀ s, g (x, s) = 0) ∧
        (∀ p, spaceTimeWord β H p = ∑ j : Fin 3, spatialPartial (F j) j p + g p) ∧
        ∀ s, 2 * (∫ x : Vec3, ∑ j : Fin 3, F j (x, s) ^ 2) + (∫ x : Vec3, g (x, s) ^ 2) ≤
          2 * Nsq s := by
      by_cases hnil : β = []
      · subst hnil
        refine ⟨fun _ _ => 0, H, fun _ => contDiff_const, hH, fun _ _ _ _ => rfl, hHK,
          fun p => ?_, fun s => ?_⟩
        · simp [spatialPartial_const_zero]
          rfl
        · have hmem : ([] : List (Fin 3)) ∈ sobolevWords (m - 1) := by
            rw [mem_sobolevWords]
            simp
          have hle := Finset.single_le_sum (f := fun α => ∫ x : Vec3, spaceTimeWord α H (x, s) ^ 2)
            (fun α _ => integral_nonneg fun x => sq_nonneg _) hmem
          have hle' : ∫ x : Vec3, H (x, s) ^ 2 ≤ Nsq s := hle
          have h0 : (∫ x : Vec3, ∑ j : Fin 3,
              (fun (_ : Fin 3) (_ : Vec3 × ℝ) => (0 : ℝ)) j (x, s) ^ 2) = 0 := by simp
          rw [h0]
          linarith only [hle', hNsq_nonneg s]
      · let β'' := β.dropLast
        let k₀ := β.getLast hnil
        have hβeq : β = β'' ++ [k₀] := (List.dropLast_append_getLast hnil).symm
        let S := spaceTimeWord β'' H
        refine ⟨fun j q => if j = k₀ then S q else 0, fun _ => 0, fun j => ?_,
          contDiff_const, fun j x hx s => ?_, fun _ _ _ => rfl, fun p => ?_, fun s => ?_⟩
        · by_cases hj : j = k₀
          · simp only [hj, ite_true]
            exact contDiff_spaceTimeWord β'' hH
          · simp only [hj, ite_false]
            exact contDiff_const
        · by_cases hj : j = k₀
          · simp only [hj, ite_true]
            exact spaceTimeWord_eq_zero_of_compl hK β'' hHK x hx s
          · simp [hj]
        · rw [hβeq, spaceTimeWord_append, Finset.sum_eq_single k₀]
          · simp [S]
          · intro j _ hj
            have hfun : (fun q : Vec3 × ℝ => if j = k₀ then S q else 0) = fun _ => 0 := by
              funext q
              simp [hj]
            show spatialPartial (fun q : Vec3 × ℝ => if j = k₀ then S q else 0) j p = 0
            rw [hfun]
            exact spatialPartial_const_zero j p
          · simp
        · have hmem : β'' ∈ sobolevWords (m - 1) := by
            rw [mem_sobolevWords]
            simp only [β'', List.length_dropLast]
            omega
          have hle := Finset.single_le_sum
            (f := fun α => ∫ x : Vec3, spaceTimeWord α H (x, s) ^ 2)
            (fun α _ => integral_nonneg fun x => sq_nonneg _) hmem
          have hsum (x : Vec3) : ∑ j : Fin 3, (if j = k₀ then S (x, s) else 0) ^ 2 =
              S (x, s) ^ 2 := by
            rw [Finset.sum_eq_single k₀]
            · simp
            · intro j _ hj
              simp [hj]
            · simp
          simp only [hsum]
          have hle' : ∫ x : Vec3, S (x, s) ^ 2 ≤ Nsq s := hle
          have h0 : (∫ x : Vec3, (fun _ : Vec3 × ℝ => (0 : ℝ)) (x, s) ^ 2) = 0 := by simp
          rw [h0]
          linarith only [hle']
    have hheq (p : Vec3 × ℝ) : timePartial (spaceTimeWord β w) p -
        ∑ j : Fin 3, spatialSecondPartial (spaceTimeWord β w) j j p =
        ∑ j : Fin 3, spatialPartial (F j) j p + g p := (hwordEq β p).trans (hsrc p)
    obtain ⟨he, hd⟩ := scalarHeatEnergy_smooth hab' hzβ hF hg hK
      (fun x hx s => ⟨hzβK x hx s, fun j => hFK j x hx s, hgK x hx s⟩) hheq hzβa
    have hfcont : Continuous fun s =>
        2 * (∫ x : Vec3, ∑ j : Fin 3, F j (x, s) ^ 2) + ∫ x : Vec3, g (x, s) ^ 2 := by
      refine (continuous_const.mul ?_).add
        (continuous_integral_sq_of_compl hg.continuous hK hgK)
      have hsw : (fun s => ∫ x : Vec3, ∑ j : Fin 3, F j (x, s) ^ 2) =
          fun s => ∑ j : Fin 3, ∫ x : Vec3, F j (x, s) ^ 2 := by
        funext s
        refine integral_finsetSum _ fun j _ => ?_
        have hc : Continuous fun x : Vec3 => F j (x, s) ^ 2 :=
          ((hF j).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
        exact hc.integrable_of_hasCompactSupport
          (HasCompactSupport.intro hK fun x hx => by simp [hFK j x hx s])
      rw [hsw]
      exact continuous_finsetSum _ fun j _ =>
        continuous_integral_sq_of_compl (hF j).continuous hK (hFK j)
    have hfle : (∫ s in a..b, (2 * (∫ x : Vec3, ∑ j : Fin 3, F j (x, s) ^ 2) +
        ∫ x : Vec3, g (x, s) ^ 2)) ≤ 2 * ∫ s in a..b, Nsq s := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hab' (hfcont.intervalIntegrable _ _)
        ((continuous_const.mul hNsq_cont).intervalIntegrable _ _) fun s _ => hf s
    have hexp : 0 ≤ Real.exp (b - a) := (Real.exp_pos _).le
    have hba : 0 ≤ b - a := by linarith only [hab]
    refine ⟨fun t ht => (he t ht).trans (mul_le_mul_of_nonneg_left hfle hexp), ?_⟩
    exact hd.trans (mul_le_mul_of_nonneg_left hfle (by positivity))
  -- assembly
  set J := ∫ s in a..b, Nsq s with hJdef
  have hexpE : Real.exp (b - a) ≤ E := Real.exp_le_exp.2 hbL
  have hba : 0 ≤ b - a := by linarith only [hab]
  have hsliceSq (γ : List (Fin 3)) (s : ℝ) :
      (∫ x in univ, (wordDeriv γ (fun y => w (y, s)) x) ^ 2) =
        ∫ x : Vec3, spaceTimeWord γ w (x, s) ^ 2 := by
    rw [Measure.restrict_univ, ← spaceTimeWord_slice γ w s]
  have hintSq (γ : List (Fin 3)) (s : ℝ) :
      Integrable (fun x : Vec3 => spaceTimeWord γ w (x, s) ^ 2) := by
    have hc : Continuous fun x : Vec3 => spaceTimeWord γ w (x, s) ^ 2 :=
      ((contDiff_spaceTimeWord γ hw).continuous.comp
        (continuous_id.prodMk continuous_const)).pow 2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun x hx => by
      simp [spaceTimeWord_eq_zero_of_compl hK γ hwK x hx s])
  -- the value at time `t`
  have hfirst : sobolevNormSqOn m univ (fun α => wordDeriv α (fun y => w (y, t))) ≤
      N * (E * (2 * J)) := by
    unfold sobolevNormSqOn
    simp only [hsliceSq]
    calc
      ∑ β ∈ sobolevWords m, ∫ x : Vec3, spaceTimeWord β w (x, t) ^ 2 ≤
          ∑ β ∈ sobolevWords m, E * (2 * J) :=
        Finset.sum_le_sum fun β hβ =>
          ((hword β hβ).1 t ht).trans (mul_le_mul_of_nonneg_right hexpE (by positivity))
      _ = N * (E * (2 * J)) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the dissipation
  let D : List (Fin 3) → ℝ → ℝ := fun β s =>
    ∑ j : Fin 3, ∫ x : Vec3, spaceTimeWord (β ++ [j]) w (x, s) ^ 2
  have hDcont (β : List (Fin 3)) : Continuous (D β) :=
    continuous_finsetSum _ fun j _ => hcontWord (β ++ [j]) hw hwK
  have hD_eq (β : List (Fin 3)) (s : ℝ) : D β s =
      ∫ x : Vec3, ∑ j : Fin 3, spatialPartial (spaceTimeWord β w) j (x, s) ^ 2 := by
    have hfun : (fun x : Vec3 => ∑ j : Fin 3, spatialPartial (spaceTimeWord β w) j (x, s) ^ 2) =
        fun x => ∑ j : Fin 3, spaceTimeWord (β ++ [j]) w (x, s) ^ 2 := by
      funext x
      refine Finset.sum_congr rfl fun j _ => ?_
      exact congrArg (· ^ 2) (congrFun (spaceTimeWord_append β j w) (x, s)).symm
    rw [hfun, integral_finsetSum _ fun j _ => hintSq (β ++ [j]) s]
  have he0cont : Continuous fun s => ∫ x : Vec3, spaceTimeWord [] w (x, s) ^ 2 :=
    hcontWord [] hw hwK
  have hsecond_pt (s : ℝ) :
      sobolevNormSqOn (m + 1) univ (fun α => wordDeriv α (fun y => w (y, s))) ≤
        (∫ x : Vec3, spaceTimeWord [] w (x, s) ^ 2) + ∑ β ∈ sobolevWords m, D β s := by
    unfold sobolevNormSqOn
    simp only [hsliceSq]
    exact sum_sobolevWords_succ_le m (fun γ => ∫ x : Vec3, spaceTimeWord γ w (x, s) ^ 2)
      fun γ => integral_nonneg fun x => sq_nonneg _
  have hsecond_cont : Continuous fun s =>
      sobolevNormSqOn (m + 1) univ (fun α => wordDeriv α (fun y => w (y, s))) := by
    unfold sobolevNormSqOn
    simp only [hsliceSq]
    exact continuous_finsetSum _ fun γ _ => hcontWord γ hw hwK
  have hmem0 : ([] : List (Fin 3)) ∈ sobolevWords m := by
    rw [mem_sobolevWords]
    simp
  have hsecond : (∫ s in a..b,
      sobolevNormSqOn (m + 1) univ (fun α => wordDeriv α (fun y => w (y, s)))) ≤
      L * (E * (2 * J)) + N * ((1 + L * E) * (2 * J)) := by
    calc
      _ ≤ ∫ s in a..b, ((∫ x : Vec3, spaceTimeWord [] w (x, s) ^ 2) +
            ∑ β ∈ sobolevWords m, D β s) :=
        intervalIntegral.integral_mono_on hab' (hsecond_cont.intervalIntegrable _ _)
          ((he0cont.add (continuous_finsetSum _ fun β _ => hDcont β)).intervalIntegrable _ _)
          fun s _ => hsecond_pt s
      _ = (∫ s in a..b, ∫ x : Vec3, spaceTimeWord [] w (x, s) ^ 2) +
            ∑ β ∈ sobolevWords m, ∫ s in a..b, D β s := by
        rw [intervalIntegral.integral_add (he0cont.intervalIntegrable _ _)
          ((continuous_finsetSum _ fun β _ => hDcont β).intervalIntegrable _ _),
          intervalIntegral.integral_finsetSum fun β _ => (hDcont β).intervalIntegrable _ _]
      _ ≤ (b - a) * (Real.exp (b - a) * (2 * J)) +
            ∑ β ∈ sobolevWords m, (1 + (b - a) * Real.exp (b - a)) * (2 * J) := by
        gcongr with β hβ
        · calc
            _ ≤ ∫ s in a..b, Real.exp (b - a) * (2 * J) :=
              intervalIntegral.integral_mono_on hab' (he0cont.intervalIntegrable _ _)
                intervalIntegrable_const fun s hs => (hword [] hmem0).1 s hs
            _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
        · have h := (hword β hβ).2
          rw [← intervalIntegral.integral_congr fun s _ => hD_eq β s] at h
          exact h
      _ ≤ L * (E * (2 * J)) + N * ((1 + L * E) * (2 * J)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
  have hrhs : (∫ s in a..b, sobolevNormSqOn (m - 1) univ
      (fun α => wordDeriv α (fun y => timePartial w (y, s) -
        ∑ j : Fin 3, spatialSecondPartial w j j (y, s)))) = J := by
    rw [hJdef]
    exact intervalIntegral.integral_congr fun s _ => hNsq_eq s
  rw [hrhs]
  calc
    _ ≤ N * (E * (2 * J)) + (L * (E * (2 * J)) + N * ((1 + L * E) * (2 * J))) :=
      add_le_add hfirst hsecond
    _ = 2 * (N * E + L * E + N * (1 + L * E)) * J := by ring

end ESS
