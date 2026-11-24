import Mathlib

open MeasureTheory Set Real
open scoped InnerProductSpace ContDiff Pointwise
open Laplacian

namespace Polya

/-! ## The abstract statement -/

section Abstract

variable {d : ℕ}

/-- Classical Dirichlet eigenfunction of `-Δ` on `Ω` with eigenvalue `μ`. -/
structure IsDirichletEigenfunction (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  /-- interior regularity -/
  contDiffOn : ContDiffOn ℝ 2 u Ω
  /-- continuity up to the boundary -/
  continuousOn : ContinuousOn u (closure Ω)
  /-- Dirichlet boundary condition -/
  boundary : ∀ x ∈ frontier Ω, u x = 0
  /-- nontriviality -/
  ne_zero : ∃ x ∈ Ω, u x ≠ 0
  /-- the eigenvalue equation `-Δ u = μ u` in `Ω` -/
  eigen : ∀ x ∈ Ω, Δ u x = -μ * u x

/-- Volume `ω_d` of the unit ball of `ℝᵈ`. -/
noncomputable def unitBallVolume (d : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- The Weyl/Pólya quantity `ω_d |Ω| λ^{d/2} / (2π)^d`. -/
noncomputable def polyaBound (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (lam : ℝ) : ℝ :=
  unitBallVolume d * (volume Ω).toReal * lam ^ ((d : ℝ) / 2) / (2 * π) ^ d

/-- `CountingBound Ω lam B`: every finite family of classical Dirichlet eigenfunctions of `Ω`
with eigenvalues `≤ lam` whose restrictions to `Ω` are linearly independent has at most `B`
members. -/
def CountingBound (Ω : Set (EuclideanSpace ℝ (Fin d))) (lam B : ℝ) : Prop :=
  ∀ (N : ℕ) (u : Fin N → EuclideanSpace ℝ (Fin d) → ℝ) (μ : Fin N → ℝ),
    (∀ i, IsDirichletEigenfunction Ω (μ i) (u i)) → (∀ i, μ i ≤ lam) →
    LinearIndependent ℝ (fun i => Ω.domRestrict (u i)) → (N : ℝ) ≤ B

/-- Pólya's inequality for a single domain. -/
def PolyaInequality (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → CountingBound Ω lam (polyaBound d Ω lam)

/-- **Pólya's conjecture (Dirichlet) in dimension `d`.  Only a statement — NOT proved.** -/
def PolyaConjectureDim (d : ℕ) : Prop :=
  ∀ Ω : Set (EuclideanSpace ℝ (Fin d)), IsOpen Ω → Bornology.IsBounded Ω → PolyaInequality Ω

/-- **Pólya's conjecture (Dirichlet), all dimensions `d ≥ 1`.  Only a statement.** -/
def PolyaConjecture : Prop := ∀ d : ℕ, 1 ≤ d → PolyaConjectureDim d

/-- **Planar Pólya conjecture** `N_Ω(λ) ≤ |Ω| λ / (4π)`.  **Only a statement.** -/
def PolyaConjecturePlanar : Prop :=
  ∀ Ω : Set (EuclideanSpace ℝ (Fin 2)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ lam : ℝ, 0 ≤ lam → CountingBound Ω lam ((volume Ω).toReal * lam / (4 * π))

/-- The Li–Yau bound (1983) in counting form.  **Only a statement** (a known theorem for the
genuine spectrum; not formalised). -/
def LiYauBound (d : ℕ) : Prop :=
  ∀ Ω : Set (EuclideanSpace ℝ (Fin d)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ lam : ℝ, 0 ≤ lam →
      CountingBound Ω lam ((((d : ℝ) + 2) / d) ^ ((d : ℝ) / 2) * polyaBound d Ω lam)

theorem unitBallVolume_nonneg (d : ℕ) : 0 ≤ unitBallVolume d := ENNReal.toReal_nonneg

theorem unitBallVolume_two : unitBallVolume 2 = π := by
  simp [unitBallVolume, pi_pos.le]

theorem unitBallVolume_three : unitBallVolume 3 = 4 * π / 3 := by
  have : (0 : ℝ) ≤ π * 4 / 3 := by positivity
  simp [unitBallVolume, this]
  ring

theorem polyaBound_two (Ω : Set (EuclideanSpace ℝ (Fin 2))) (lam : ℝ) :
    polyaBound 2 Ω lam = (volume Ω).toReal * lam / (4 * π) := by
  have hpi := pi_pos
  rw [polyaBound, unitBallVolume_two]
  norm_num
  field_simp
  ring

/-- The planar formulation is literally the case `d = 2` of the general one. -/
theorem polyaConjecturePlanar_iff : PolyaConjecturePlanar ↔ PolyaConjectureDim 2 := by
  simp only [PolyaConjecturePlanar, PolyaConjectureDim, PolyaInequality, polyaBound_two]

theorem polyaBound_nonneg (Ω : Set (EuclideanSpace ℝ (Fin d))) {lam : ℝ} (h : 0 ≤ lam) :
    0 ≤ polyaBound d Ω lam := by
  have := unitBallVolume_nonneg d
  have := pi_pos
  unfold polyaBound
  positivity

theorem polyaBound_mono_lam (Ω : Set (EuclideanSpace ℝ (Fin d))) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : polyaBound d Ω a ≤ polyaBound d Ω b := by
  have := unitBallVolume_nonneg d
  have := pi_pos
  unfold polyaBound
  gcongr

theorem polyaBound_mono_set {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (h : Ω ⊆ Ω')
    (hfin : volume Ω' ≠ ⊤) {lam : ℝ} (hl : 0 ≤ lam) : polyaBound d Ω lam ≤ polyaBound d Ω' lam := by
  have := unitBallVolume_nonneg d
  have := pi_pos
  have h2 : (volume Ω).toReal ≤ (volume Ω').toReal :=
    ENNReal.toReal_mono hfin (measure_mono h)
  unfold polyaBound
  gcongr

/-- **Scale invariance of the Pólya quantity**: `|cΩ| (λ/c²)^{d/2} = |Ω| λ^{d/2}`. -/
theorem polyaBound_smul (Ω : Set (EuclideanSpace ℝ (Fin d))) {c lam : ℝ} (hc : 0 < c)
    (hl : 0 ≤ lam) : polyaBound d (c • Ω) (lam / c ^ 2) = polyaBound d Ω lam := by
  have hpi := pi_pos
  unfold polyaBound
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (pow_pos hc d),
    div_rpow hl (by positivity)]
  have : (c ^ 2) ^ ((d : ℝ) / 2) = c ^ d := by
    rw [← rpow_natCast, ← rpow_mul hc.le, ← rpow_natCast]
    congr 1
    push_cast
    ring
  rw [this]
  field_simp

theorem CountingBound.mono {Ω : Set (EuclideanSpace ℝ (Fin d))} {lam lam' B B' : ℝ}
    (h : CountingBound Ω lam B) (hl : lam' ≤ lam) (hB : B ≤ B') : CountingBound Ω lam' B' :=
  fun N u μ hu hμ hli => (h N u μ hu (fun i => (hμ i).trans hl) hli).trans hB

/-- Pólya's inequality is formally stronger than (implies) the Li–Yau-type bound for the same
domain, since `((d+2)/d)^{d/2} ≥ 1`. -/
theorem PolyaConjectureDim.liYauBound (hd : 1 ≤ d) (h : PolyaConjectureDim d) : LiYauBound d := by
  intro Ω hΩ hb lam hl
  refine (h Ω hΩ hb lam hl).mono le_rfl ?_
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ ((d : ℝ) + 2) / d := by rw [le_div_iff₀ hd']; linarith
  have h2 : (1 : ℝ) ≤ (((d : ℝ) + 2) / d) ^ ((d : ℝ) / 2) :=
    one_le_rpow h1 (by positivity)
  have := polyaBound_nonneg Ω hl
  nlinarith

end Abstract

/-! ## Lattice points in a quarter ellipse -/

section Lattice

theorem integral_sqrt_one_sub_sq_zero_one : ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) = π / 4 := by
  have h1 : ∫ x in (-1 : ℝ)..0, √(1 - x ^ 2) = ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (fun x => √(1 - x ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  have hc : Continuous fun x : ℝ => √(1 - x ^ 2) := by fun_prop
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) 0) (hc.intervalIntegrable 0 1)
  rw [integral_sqrt_one_sub_sq, h1] at h2
  linarith

/-- The profile of the quarter ellipse `x²/a² + y²/b² ≤ R`. -/
private noncomputable def prof (a b R : ℝ) (t : ℝ) : ℝ := b * √(R - t ^ 2 / a ^ 2)

private theorem prof_antitoneOn {a b R : ℝ} (hb : 0 ≤ b) :
    AntitoneOn (prof a b R) (Ici 0) := by
  intro x hx y hy hxy
  unfold prof
  have hx0 : (0 : ℝ) ≤ x := hx
  gcongr

theorem integral_prof {a b R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..a * √R, prof a b R t = π / 4 * (a * b * R) := by
  have h := intervalIntegral.mul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (f := prof a b R) (c := a * √R)
  rw [mul_zero, mul_one] at h
  rw [← h]
  have : ∀ s : ℝ, prof a b R (a * √R * s) = (b * √R) * √(1 - s ^ 2) := by
    intro s
    unfold prof
    have : R - (a * √R * s) ^ 2 / a ^ 2 = R * (1 - s ^ 2) := by
      have := sq_sqrt hR
      field_simp
      nlinarith
    rw [this, sqrt_mul hR]
    ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq_zero_one]
  have := mul_self_sqrt hR
  linear_combination (π / 4 * a * b) * this

/-- The set of positive-integer lattice points in the quarter ellipse. -/
def ellipseLattice (a b R : ℝ) : Set (ℕ × ℕ) :=
  {p | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ (p.1 : ℝ) ^ 2 / a ^ 2 + (p.2 : ℝ) ^ 2 / b ^ 2 ≤ R}

private theorem prof_nonneg {a b R : ℝ} (hb : 0 ≤ b) (t : ℝ) : 0 ≤ prof a b R t :=
  mul_nonneg hb (sqrt_nonneg _)

private theorem prof_continuous (a b R : ℝ) : Continuous (prof a b R) := by
  unfold prof; fun_prop

private theorem ellipseLattice_subset {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ellipseLattice a b R ⊆ ↑((Finset.range ⌊a * √R⌋₊).biUnion fun i =>
      (Finset.Icc 1 ⌊prof a b R ((i + 1 : ℕ) : ℝ)⌋₊).image fun n => (i + 1, n)) := by
  rintro ⟨m, n⟩ ⟨hm, hn, h⟩
  simp only at hm hn h
  have h1 : 0 ≤ (m : ℝ) ^ 2 / a ^ 2 := by positivity
  have h2 : 0 ≤ (n : ℝ) ^ 2 / b ^ 2 := by positivity
  have hR : 0 ≤ R := by linarith
  have hmle : (m : ℝ) ≤ a * √R := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, sq_sqrt hR]
    have : (m : ℝ) ^ 2 / a ^ 2 ≤ R := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hnle : (n : ℝ) ≤ prof a b R m := by
    unfold prof
    have h3 : 0 ≤ R - (m : ℝ) ^ 2 / a ^ 2 := by linarith
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, sq_sqrt h3]
    have : (n : ℝ) ^ 2 / b ^ 2 ≤ R - (m : ℝ) ^ 2 / a ^ 2 := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  simp only [Finset.coe_biUnion, Finset.coe_range, mem_Iio, Finset.coe_image, Finset.coe_Icc,
    mem_iUnion, mem_image, mem_Icc, Prod.mk.injEq, exists_prop]
  refine ⟨m - 1, ?_, n, ⟨hn, ?_⟩, by omega, rfl⟩
  · have : m ≤ ⌊a * √R⌋₊ := Nat.le_floor hmle
    omega
  · have : m - 1 + 1 = m := by omega
    rw [this]
    exact Nat.le_floor hnle

theorem ellipseLattice_finite {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (ellipseLattice a b R).Finite :=
  (Finset.finite_toSet _).subset (ellipseLattice_subset ha hb)

/-- **Lattice points in a quarter ellipse.**  The number of pairs of positive integers `(m, n)`
with `m²/a² + n²/b² ≤ R` is at most the area `π a b R / 4` of the quarter ellipse. -/
theorem ncard_ellipseLattice_le {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 ≤ R) :
    ((ellipseLattice a b R).ncard : ℝ) ≤ π / 4 * (a * b * R) := by
  set M := ⌊a * √R⌋₊ with hM
  have hMle : (M : ℝ) ≤ a * √R := Nat.floor_le (by positivity)
  have hcard : (ellipseLattice a b R).ncard ≤
      ∑ i ∈ Finset.range M, ⌊prof a b R ((i + 1 : ℕ) : ℝ)⌋₊ := by
    refine (Set.ncard_le_ncard (ellipseLattice_subset ha hb) (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
    refine Finset.card_image_le.trans ?_
    simp
  have hsum : (∑ i ∈ Finset.range M, (⌊prof a b R ((i + 1 : ℕ) : ℝ)⌋₊ : ℝ)) ≤
      ∑ i ∈ Finset.range M, prof a b R (0 + ((i + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [zero_add]
    exact Nat.floor_le (prof_nonneg hb.le _)
  have hint : (∑ i ∈ Finset.range M, prof a b R (0 + ((i + 1 : ℕ) : ℝ))) ≤
      ∫ t in (0 : ℝ)..0 + M, prof a b R t :=
    AntitoneOn.sum_le_integral ((prof_antitoneOn hb.le).mono fun x hx => hx.1)
  have hmono : (∫ t in (0 : ℝ)..0 + M, prof a b R t) ≤ ∫ t in (0 : ℝ)..a * √R, prof a b R t := by
    rw [zero_add]
    exact intervalIntegral.integral_mono_interval le_rfl (Nat.cast_nonneg _) hMle
      (Filter.Eventually.of_forall fun t => prof_nonneg hb.le t)
      ((prof_continuous a b R).intervalIntegrable _ _)
  rw [integral_prof ha hR] at hmono
  calc ((ellipseLattice a b R).ncard : ℝ)
      ≤ ((∑ i ∈ Finset.range M, ⌊prof a b R ((i + 1 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ∑ i ∈ Finset.range M, (⌊prof a b R ((i + 1 : ℕ) : ℝ)⌋₊ : ℝ) := by push_cast; rfl
    _ ≤ _ := hsum.trans (hint.trans hmono)

/-- Quarter disc: `#{(m, n) ∈ ℕ₊² : m² + n² ≤ r²} ≤ π r² / 4`. -/
theorem ncard_quarterDisc_le (r : ℝ) :
    (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ r ^ 2}).ncard : ℝ) ≤
      π * r ^ 2 / 4 := by
  have h := ncard_ellipseLattice_le (a := 1) (b := 1) one_pos one_pos (sq_nonneg r)
  simp only [ellipseLattice, one_pow, div_one, mul_one, one_mul] at h
  linarith

end Lattice

/-! ## The one-dimensional case, classical formulation -/

section Interval

variable {L μ : ℝ} {u : ℝ → ℝ}

/-- Classical Dirichlet eigenfunction on the interval `(0, L)`: `u` is twice differentiable on
`[0, L]` (one-sided at the endpoints) with `u'' = -μ u`, `u 0 = u L = 0`, and `u ≢ 0`. -/
def IsDirichletEigenfunctionInterval (L μ : ℝ) (u : ℝ → ℝ) : Prop :=
  (∃ u' : ℝ → ℝ,
    (∀ x ∈ Icc 0 L, HasDerivWithinAt u (u' x) (Icc 0 L) x) ∧
    (∀ x ∈ Icc 0 L, HasDerivWithinAt u' (-μ * u x) (Icc 0 L) x)) ∧
  u 0 = 0 ∧ u L = 0 ∧ ∃ x ∈ Icc 0 L, u x ≠ 0

private theorem eq_of_hasDerivWithinAt_zero {E : ℝ → ℝ}
    (h : ∀ x ∈ Icc 0 L, HasDerivWithinAt E 0 (Icc 0 L) x) : ∀ x ∈ Icc 0 L, E x = E 0 := by
  refine constant_of_has_deriv_right_zero (fun x hx => (h x hx).continuousWithinAt) ?_
  intro x hx
  exact (h x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

/-- **ODE uniqueness (energy method).**  If `v'' = -μ v` on `[0, L]` with `μ > 0` and
`v 0 = v' 0 = 0`, then `v = 0` and `v' = 0` on `[0, L]`. -/
theorem eq_zero_of_ode (hμ : 0 < μ) {v v' : ℝ → ℝ}
    (hv : ∀ x ∈ Icc 0 L, HasDerivWithinAt v (v' x) (Icc 0 L) x)
    (hv' : ∀ x ∈ Icc 0 L, HasDerivWithinAt v' (-μ * v x) (Icc 0 L) x)
    (h0 : v 0 = 0) (h0' : v' 0 = 0) {x : ℝ} (hx : x ∈ Icc 0 L) : v x = 0 ∧ v' x = 0 := by
  have hE : ∀ y ∈ Icc 0 L, HasDerivWithinAt (fun y => v' y ^ 2 + μ * v y ^ 2) 0 (Icc 0 L) y := by
    intro y hy
    convert ((hv' y hy).pow 2).add (((hv y hy).pow 2).const_mul μ) using 1
    ring
  have hEx := eq_of_hasDerivWithinAt_zero hE x hx
  simp only [h0, h0', mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at hEx
  have ha : 0 ≤ v' x ^ 2 := sq_nonneg _
  have hb : 0 ≤ μ * v x ^ 2 := by positivity
  have ha0 : v' x ^ 2 = 0 := by linarith
  have hb0 : μ * v x ^ 2 = 0 := by linarith
  have hb1 : v x ^ 2 = 0 := (mul_eq_zero.mp hb0).resolve_left hμ.ne'
  exact ⟨pow_eq_zero_iff two_ne_zero |>.1 hb1, pow_eq_zero_iff two_ne_zero |>.1 ha0⟩

/-- If `u'' = -μ u` on `[0, L]` with `μ > 0` and `u 0 = 0`, then
`u x = (u' 0 / √μ) sin (√μ x)` on `[0, L]`. -/
theorem eq_sin_of_ode (hμ : 0 < μ) {u' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (u' x) (Icc 0 L) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivWithinAt u' (-μ * u x) (Icc 0 L) x)
    (h0 : u 0 = 0) {x : ℝ} (hx : x ∈ Icc 0 L) :
    u x = u' 0 / √μ * sin (√μ * x) := by
  have hw : √μ * √μ = μ := mul_self_sqrt hμ.le
  have hw0 : √μ ≠ 0 := (sqrt_pos.2 hμ).ne'
  set w := √μ with hwdef
  set c := u' 0 / w with hc
  have hcw : c * w = u' 0 := by rw [hc]; field_simp
  have hv : ∀ y ∈ Icc 0 L, HasDerivWithinAt (fun y => u y - c * sin (w * y))
      (u' y - c * w * cos (w * y)) (Icc 0 L) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using (hasDerivAt_id y).const_mul w
    have h2 := (((hasDerivAt_sin (w * y)).comp y h1).const_mul c).hasDerivWithinAt
      (s := Icc 0 L)
    convert (hu y hy).sub h2 using 1
    · rfl
    · ring
  have hv' : ∀ y ∈ Icc 0 L, HasDerivWithinAt (fun y => u' y - c * w * cos (w * y))
      (-μ * (u y - c * sin (w * y))) (Icc 0 L) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using (hasDerivAt_id y).const_mul w
    have h2 := (((hasDerivAt_cos (w * y)).comp y h1).const_mul (c * w)).hasDerivWithinAt
      (s := Icc 0 L)
    convert (hu' y hy).sub h2 using 1
    · rfl
    · rw [← hw]; ring
  have := (eq_zero_of_ode hμ hv hv' (by simp [h0]) (by simp [hcw]) hx).1
  linarith

/-- There is no classical Dirichlet eigenfunction on an interval with eigenvalue `μ ≤ 0`. -/
theorem IsDirichletEigenfunctionInterval.pos (hL : 0 < L)
    (h : IsDirichletEigenfunctionInterval L μ u) : 0 < μ := by
  by_contra hμ
  push Not at hμ
  obtain ⟨⟨u', hu, hu'⟩, h0, hLz, y, hy, huy⟩ := h
  -- `w = u u'` has nonnegative derivative `u'² - μ u²`
  have hw : ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun x => u x * u' x)
      (u' x ^ 2 - μ * u x ^ 2) (Icc 0 L) x := by
    intro x hx
    convert (hu x hx).mul (hu' x hx) using 1
    ring
  have hmono : MonotoneOn (fun x => u x * u' x) (Icc 0 L) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 L)
      (fun x hx => (hw x hx).continuousWithinAt) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hw x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [((hw x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
      nlinarith [sq_nonneg (u' x), sq_nonneg (u x)]
  have h0m : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hLm : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  have hwz : ∀ x ∈ Icc 0 L, u x * u' x = 0 := by
    intro x hx
    have h1 := hmono h0m hx hx.1
    have h2 := hmono hx hLm hx.2
    simp only [h0, hLz, zero_mul] at h1 h2
    linarith
  have hsq : ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun x => u x ^ 2) 0 (Icc 0 L) x := by
    intro x hx
    convert (hu x hx).pow 2 using 1
    have := hwz x hx
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    linarith
  have := eq_of_hasDerivWithinAt_zero hsq y hy
  simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
  exact huy (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- `sin (k π x / L)` is a classical Dirichlet eigenfunction of `(0, L)` for `(k π / L)²`. -/
theorem sin_isDirichletEigenfunctionInterval (hL : 0 < L) {k : ℕ} (hk : 1 ≤ k) :
    IsDirichletEigenfunctionInterval L ((k * π / L) ^ 2) (fun x => sin (k * π / L * x)) := by
  have h1 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => k * π / L * y) (k * π / L) x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (k * π / L)
  refine ⟨⟨fun x => k * π / L * cos (k * π / L * x), fun x _ => ?_, fun x _ => ?_⟩, by simp, ?_,
    L / (2 * k), ⟨by positivity, ?_⟩, ?_⟩
  · convert ((hasDerivAt_sin _).comp x (h1 x)).hasDerivWithinAt using 1
    · rfl
    · simp only; ring
  · convert (((hasDerivAt_cos _).comp x (h1 x)).const_mul (k * π / L)).hasDerivWithinAt using 1
    · rfl
    · simp only; ring
  · have : k * π / L * L = k * π := by field_simp
    simp only [this]
    exact sin_nat_mul_pi k
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have : k * π / L * (L / (2 * k)) = π / 2 := by field_simp
    simp [this]

/-- **Classification of the Dirichlet spectrum of an interval** (classical formulation): every
eigenfunction is, on `[0, L]`, a nonzero multiple of `sin (k π x / L)` for some integer `k ≥ 1`,
and its eigenvalue is `(k π / L)²`. -/
theorem IsDirichletEigenfunctionInterval.exists_nat (hL : 0 < L)
    (h : IsDirichletEigenfunctionInterval L μ u) :
    ∃ k : ℕ, 1 ≤ k ∧ μ = (k * π / L) ^ 2 ∧
      ∃ c : ℝ, c ≠ 0 ∧ ∀ x ∈ Icc 0 L, u x = c * sin (k * π / L * x) := by
  have hμ := h.pos hL
  obtain ⟨⟨u', hu, hu'⟩, h0, hLz, y, hy, huy⟩ := h
  have hform : ∀ x ∈ Icc 0 L, u x = u' 0 / √μ * sin (√μ * x) := fun x hx =>
    eq_sin_of_ode hμ hu hu' h0 hx
  have hsq : 0 < √μ := sqrt_pos.2 hμ
  have hc : u' 0 / √μ ≠ 0 := by
    intro hc
    apply huy
    rw [hform y hy, hc, zero_mul]
  have hsin : sin (√μ * L) = 0 := by
    have := hform L ⟨hL.le, le_rfl⟩
    rw [hLz] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hsin
  have hpos : 0 < √μ * L := mul_pos hsq hL
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n * π := by rw [hn]; exact hpos
    have : (0 : ℝ) < n := pos_of_mul_pos_left this pi_pos.le
    exact_mod_cast this
  lift n to ℕ using hn0.le
  have hn' : ((n : ℕ) : ℝ) * π = √μ * L := by exact_mod_cast hn
  have hw : √μ = n * π / L := by rw [hn']; field_simp
  refine ⟨n, by exact_mod_cast hn0, ?_, u' 0 / √μ, hc, fun x hx => ?_⟩
  · rw [← hw, sq_sqrt hμ.le]
  · rw [hform x hx, hw]

/-- The Dirichlet eigenvalues of `(0, L)` (classical formulation) are exactly the numbers
`(k π / L)²`, `k = 1, 2, …`. -/
theorem exists_isDirichletEigenfunctionInterval_iff (hL : 0 < L) :
    (∃ u, IsDirichletEigenfunctionInterval L μ u) ↔ ∃ k : ℕ, 1 ≤ k ∧ μ = (k * π / L) ^ 2 := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨k, hk, hμ, -⟩ := hu.exists_nat hL
    exact ⟨k, hk, hμ⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, sin_isDirichletEigenfunctionInterval hL hk⟩

/-- **Pólya's inequality for an interval, classical formulation, with the sharp integer bound.**
Any family of `N` classical Dirichlet eigenfunctions of `(0, L)` with eigenvalues `≤ lam` whose
restrictions to `[0, L]` are linearly independent satisfies `N ≤ ⌊L √lam / π⌋`. -/
theorem card_le_floor_interval (hL : 0 < L) {lam : ℝ} {N : ℕ} (u : Fin N → ℝ → ℝ)
    (μ : Fin N → ℝ) (hu : ∀ i, IsDirichletEigenfunctionInterval L (μ i) (u i))
    (hμ : ∀ i, μ i ≤ lam)
    (hli : LinearIndependent ℝ (fun i => (Icc (0 : ℝ) L).domRestrict (u i))) :
    N ≤ ⌊L * √lam / π⌋₊ := by
  choose k hk hμk c hc hform using fun i => (hu i).exists_nat hL
  have hinj : Function.Injective k := by
    intro i j hij
    by_contra hne
    have hli' := Fintype.linearIndependent_iff.1 hli
      (fun l => if l = i then c j else if l = j then -c i else 0) ?_ i
    · simp only [ite_true] at hli'
      exact hc j hli'
    · funext x
      have hsum : ∀ l : Fin N, (if l = i then c j else if l = j then -c i else 0) •
          (Icc (0 : ℝ) L).domRestrict (u l) =
          (if l = i then c j • (Icc (0 : ℝ) L).domRestrict (u i) else 0) +
          (if l = j then (-c i) • (Icc (0 : ℝ) L).domRestrict (u j) else 0) := by
        intro l
        by_cases h1 : l = i
        · subst h1; simp [hne]
        · by_cases h2 : l = j
          · subst h2; simp [h1]
          · simp [h1, h2]
      simp only [hsum, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [Pi.add_apply, Pi.smul_apply, Set.domRestrict, smul_eq_mul, Pi.zero_apply]
      rw [hform i x x.2, hform j x x.2, hij]
      ring
  have hle : ∀ i, k i ∈ Finset.Icc 1 ⌊L * √lam / π⌋₊ := by
    intro i
    rw [Finset.mem_Icc]
    refine ⟨hk i, Nat.le_floor ?_⟩
    have h1 : ((k i : ℝ) * π / L) ^ 2 ≤ lam := by rw [← hμk i]; exact hμ i
    have h2 : (k i : ℝ) * π / L ≤ √lam := Real.le_sqrt_of_sq_le h1
    rw [le_div_iff₀ pi_pos]
    rw [div_le_iff₀ hL] at h2
    linarith
  calc N = (Finset.univ : Finset (Fin N)).card := by simp
    _ = (Finset.univ.image k).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (Finset.Icc 1 ⌊L * √lam / π⌋₊).card :=
        Finset.card_le_card (by intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx; exact hle i)
    _ = ⌊L * √lam / π⌋₊ := by simp

/-- **Pólya's inequality holds on every interval** (classical one-dimensional formulation):
`N_{(0,L)}(λ) ≤ L √λ / π = ω₁ L λ^{1/2} / (2π)` with `ω₁ = 2`. -/
theorem polya_interval (hL : 0 < L) {lam : ℝ} {N : ℕ} (u : Fin N → ℝ → ℝ)
    (μ : Fin N → ℝ) (hu : ∀ i, IsDirichletEigenfunctionInterval L (μ i) (u i))
    (hμ : ∀ i, μ i ≤ lam)
    (hli : LinearIndependent ℝ (fun i => (Icc (0 : ℝ) L).domRestrict (u i))) :
    (N : ℝ) ≤ L * √lam / π := by
  have h := card_le_floor_interval hL u μ hu hμ hli
  have h0 : 0 ≤ L * √lam / π := by have := pi_pos; positivity
  calc (N : ℝ) ≤ (⌊L * √lam / π⌋₊ : ℝ) := by exact_mod_cast h
    _ ≤ _ := Nat.floor_le h0

end Interval

end Polya
