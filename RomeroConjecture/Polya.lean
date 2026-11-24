import Mathlib

/-!
# Pólya's eigenvalue conjecture (Dirichlet version)

**STATUS: IN PROGRESS / NOT YET SOLVED.**
This file contains a formal *statement* of Pólya's conjecture and machine-checked proofs of some
elementary partial results (the interval in a classical formulation; the lattice-point inequality
behind the rectangle).  It does **not** prove the conjecture, and does not claim to.

## The mathematics

Let `Ω ⊂ ℝᵈ` be a bounded open set, `0 < λ₁ ≤ λ₂ ≤ …` the eigenvalues (with multiplicity) of the
Dirichlet Laplacian `-Δ` on `Ω`, and `N_Ω(λ) = #{k : λ_k ≤ λ}` the counting function.  Weyl's law
says `N_Ω(λ) ~ ω_d |Ω| λ^{d/2} / (2π)^d` as `λ → ∞`, where `ω_d` is the volume of the unit ball.

**Conjecture (G. Pólya).**  For every bounded open `Ω ⊂ ℝᵈ` and every `λ ≥ 0`,
`N_Ω(λ) ≤ ω_d |Ω| λ^{d/2} / (2π)^d`; equivalently `λ_k ≥ 4π² (k / (ω_d |Ω|))^{2/d}` for all `k`.
In the plane: `N_Ω(λ) ≤ |Ω| λ / (4π)`, i.e. `λ_k ≥ 4π k / |Ω|`.
(There is a companion conjecture with the reverse inequality for Neumann eigenvalues; it is not
treated here.)

## Status in the literature (checked by a few web searches, November 2026 — see caveats)

Attribution/dating.  Recent papers (e.g. Filonov–Levitin–Polterovich–Sher) date the conjecture to
G. Pólya, *Mathematics and Plausible Reasoning* (Princeton, 1954); others cite
G. Pólya, *On the eigenvalues of vibrating membranes*, Proc. London Math. Soc. (3) 11 (1961),
419–433, where it is **proved for planar domains that tile the plane** (Dirichlet case; the
Neumann case under extra assumptions).  We did not consult the originals, so the precise place
where the conjecture is first *stated* for arbitrary domains is recorded here with uncertainty.

* Tiling domains: Pólya 1961 (Dirichlet); R. Kellner 1966 removed Pólya's extra assumptions in
  the Neumann case (reported as "On a theorem of Pólya", Amer. Math. Monthly 73 (1966) — title
  and journal from memory, **not** confirmed by our search); N. Filonov, arXiv:2006.10663,
  treats the Neumann case for all tiling sets.
* Weaker universal bounds: F. A. Berezin (1972) and P. Li, S.-T. Yau (Comm. Math. Phys. 1983):
  `λ_k ≥ (d/(d+2)) · 4π² (k / (ω_d |Ω|))^{2/d}`, i.e. Pólya's bound up to the factor `d/(d+2)`
  (the years are the commonly quoted ones; only the names were confirmed by our search).
* Products: A. Laptev, J. Funct. Anal. 151 (1997): if Pólya (Dirichlet) holds for
  `Ω₁ ⊂ ℝ^{d₁}`, `d₁ ≥ 2`, then it holds for `Ω₁ × Ω₂` for every bounded `Ω₂`.
* Balls: N. Filonov, M. Levitin, I. Polterovich, D. Sher, *Pólya's conjecture for Euclidean
  balls*, Invent. Math. 234 (2023), 129–169 — the disk, planar sectors, and (Dirichlet) balls in
  every dimension; the Neumann disk case there uses a computer-assisted step.  Same authors:
  *Pólya's conjecture for Dirichlet eigenvalues of annuli*, J. London Math. Soc. 113 (2026),
  e70425 (arXiv:2505.21737) — first non-simply-connected planar examples.
* 2026 preprints listed on MathWorld's "Pólya Eigenvalue Conjecture" page, which we have **not**
  verified and treat as unconfirmed: Dai–Sun arXiv:2610.05146 (Neumann, annuli); Y. Li
  arXiv:2610.27707 and arXiv:2610.31464 (spherical shells); Dai–Zhao arXiv:2611.13910 (hyperbolic
  balls); and, most notably, Q. Tang, Z. Wang, *Strict Dirichlet Pólya inequality for simply
  connected planar domains*, arXiv:2610.13139 (9 Oct 2026), claiming the Dirichlet inequality for
  **every bounded simply connected planar domain** (and a Neumann companion for Lipschitz ones),
  with acknowledged ChatGPT assistance and Lean formalisations produced with Aristotle/Codex.
  According to MathWorld (as of Oct 2026) no independent specialist review of the complete
  argument had been reported.  We could not confirm any refereed acceptance.
* What is open: as far as we could determine, **the conjecture for general bounded domains (any
  `d ≥ 2`) is open**; nobody claims the general case.  Even if the Tang–Wang preprint is correct,
  multiply connected planar domains and all dimensions `d ≥ 3` remain open.

## Formalisation choices and their limits

Mathlib has no Sobolev spaces and no spectral theory of the Dirichlet Laplacian, so there is no
enumerated spectrum `λ_k` to talk about.  We use:

* `IsDirichletEigenfunction Ω μ u` — a **classical** eigenfunction: `u` is `C²` in `Ω`,
  continuous on `closure Ω`, zero on `frontier Ω`, not identically zero on `Ω`, and
  `Δ u = -μ u` pointwise in `Ω` (`Δ` is Mathlib's `InnerProductSpace.laplacian`).
* `CountingBound Ω lam B` — "`N_Ω(lam) ≤ B`" without an enumerated spectrum: every finite family
  of eigenfunctions with eigenvalues `≤ lam` whose *restrictions to `Ω`* are linearly independent
  has at most `B` members.  (Restricting to `Ω` matters: the values of `u` off `closure Ω` are
  unconstrained.)  For a self-adjoint operator with discrete spectrum, the largest such family
  has exactly `N(lam)` members, which is the (informal, unformalised) justification.
* `polyaBound d Ω lam = ω_d |Ω| lam^{d/2} / (2π)^d` with `ω_d = volume (ball 0 1)` and
  `|Ω| = volume Ω` in `EuclideanSpace ℝ (Fin d)`.

Fidelity caveats (none of the following facts is formalised; they are the informal justification):

* A classical eigenfunction on a bounded open set lies in `H¹₀(Ω)` and is an eigenfunction of the
  Friedrichs (form) Dirichlet Laplacian.  Conversely, form eigenfunctions are real-analytic in
  `Ω`, but they extend continuously by zero to the boundary only at *regular* boundary points
  (Wiener criterion).  So for domains all of whose boundary points are regular (Lipschitz
  domains, convex domains, simply connected planar domains, …) the
  definition agrees with the textbook one.  For irregular domains (e.g. a punctured disc, whose
  form eigenfunctions are those of the disc and do not all vanish at the puncture) there are
  *fewer* classical eigenfunctions, so `CountingBound` is *weaker* there.  Hence
  `PolyaConjecture` below is implied by the textbook conjecture, and coincides with it when
  restricted to boundary-regular domains; it is not literally the same statement on arbitrary
  bounded open sets.  (By domain monotonicity/approximation the textbook conjecture for all
  bounded open sets is expected to reduce to nice domains, but that is not formalised either.)
* No existence theory is formalised.  If some `Ω` had no classical eigenfunctions the inequality
  would hold vacuously for it.  Non-vacuity is checked only for rectangles
  (`prodSin_isDirichletEigenfunction`).
* The equivalent eigenvalue form `λ_k ≥ 4π² (k/(ω_d|Ω|))^{2/d}` is not stated formally (no
  enumeration of the spectrum is available).
* `d = 0` is excluded from `PolyaConjecture` (it is a degenerate, trivially true case).

## What is proved in this file (no `sorry`, no axioms beyond the standard three)

About the abstract statement:
* `unitBallVolume_one/two/three` : `ω₁ = 2`, `ω₂ = π`, `ω₃ = 4π/3`.
* `polyaBound_two` and `polyaConjecturePlanar_iff` : the planar form `|Ω| λ / (4π)` is literally
  the case `d = 2`.
* `polyaBound_nonneg`, `polyaBound_mono_lam`, `polyaBound_mono_set`, `CountingBound.mono`.
* `polyaBound_smul` : scale invariance `polyaBound d (c • Ω) (λ / c²) = polyaBound d Ω λ`
  (of the *bound* only; the corresponding rescaling of eigenfunctions is not formalised).
* `PolyaConjectureDim.liYauBound` : the (unproved) conjecture formally implies the (unproved
  here) Li–Yau-type statement `LiYauBound d` — a consistency check, nothing more.
* `polyaInequality_empty` : sanity check, the inequality holds for `Ω = ∅`.

The interval `(0, L)` in a **classical one-dimensional formulation**
(`IsDirichletEigenfunctionInterval`: `u'' = -μ u` on `[0, L]` with one-sided derivatives,
`u 0 = u L = 0`, `u ≢ 0`) — a complete treatment:
* `sin_isDirichletEigenfunctionInterval` : `sin (k π x / L)` is an eigenfunction for `(kπ/L)²`.
* `eq_zero_of_ode`, `eq_sin_of_ode` : ODE uniqueness by the energy method.
* `IsDirichletEigenfunctionInterval.pos` : every eigenvalue is `> 0`.
* `IsDirichletEigenfunctionInterval.exists_nat` : every eigenfunction is `c sin (k π x / L)` on
  `[0, L]` with `k ≥ 1`, `c ≠ 0`, and eigenvalue `(kπ/L)²`.
* `exists_isDirichletEigenfunctionInterval_iff` : the spectrum is exactly `{(kπ/L)² : k ≥ 1}`.
* `card_le_floor_interval`, `polya_interval` : **Pólya's inequality for intervals**: any `N`
  eigenfunctions with eigenvalues `≤ λ`, linearly independent on `[0, L]`, satisfy
  `N ≤ ⌊L√λ/π⌋ ≤ L√λ/π = ω₁ L λ^{1/2}/(2π)` (`intervalBound_eq`).

"Model spectrum" theorems.  These are statements about explicit sets of integers; they do **not**
depend on (and are not connected by a completeness theorem to) the abstract eigenfunction
definition:
* `ncard_intervalModel`, `ncard_intervalModel_le` :
  `#{k ≥ 1 : (kπ/L)² ≤ λ} = ⌊L√λ/π⌋ ≤ L√λ/π`.
* `integral_sqrt_one_sub_sq_zero_one` : `∫₀¹ √(1 - x²) dx = π/4`.
* `ncard_ellipseLattice_le` : `#{(m,n) ∈ ℕ₊² : m²/a² + n²/b² ≤ R} ≤ π a b R / 4`
  (sum–integral comparison for the antitone profile `b √(R - t²/a²)`).
* `ncard_quarterDisc_le` : `#{(m,n) ∈ ℕ₊² : m² + n² ≤ r²} ≤ π r² / 4`.
* `ncard_rectangleModel_le`, `ncard_squareModel_le`, `ncard_rectangleModel_le_polyaBound` :
  `#{(m,n) ∈ ℕ₊² : π²(m²/a² + n²/b²) ≤ λ} ≤ a b λ / (4π) = polyaBound 2 (rect a b) λ`.

The rectangle `rect a b = (0,a) × (0,b) ⊂ ℝ²` in the abstract sense:
* `isOpen_rect`, `isBounded_rect`, `volume_rect`, `frontier_rect_subset`.
* `laplacian_prodSin` : `Δ (sin(αx) sin(βy)) = -(α² + β²) sin(αx) sin(βy)`.
* `prodSin_isDirichletEigenfunction` : `sin(mπx/a) sin(nπy/b)` (`m, n ≥ 1`) **is** an
  `IsDirichletEigenfunction` of `rect a b` with eigenvalue `π²(m²/a² + n²/b²)`.

## What is NOT proved

* `PolyaConjecture`, `PolyaConjectureDim d`, `PolyaConjecturePlanar` — only stated, as `Prop`s.
* `LiYauBound d` — a known theorem (for the genuine spectrum), only stated here.
* `PolyaInequality (rect a b)` in the abstract sense is **not** proved: that would need the
  completeness of the product eigenfunctions `sin sin` (that there are no other eigenfunctions),
  which is not formalised.  What is proved is the inequality for the model spectrum plus the fact
  that the model functions are abstract eigenfunctions.  (Rectangles tile the plane, so this case
  is covered by Pólya's 1961 theorem in the literature.)
* The one-dimensional result is proved for the classical formulation on `ℝ`
  (`IsDirichletEigenfunctionInterval`), not for `IsDirichletEigenfunction` on subsets of
  `EuclideanSpace ℝ (Fin 1)`; the two are not linked here.  The 1D class asks for two one-sided
  derivatives up to the endpoints, which is automatic for genuine eigenfunctions but is a
  (harmless) extra assumption relative to "`C²` inside, continuous up to the boundary".
* No disk/ball/annulus result, no tiling argument, no Weyl law, no Neumann version.
-/

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

/-- Sanity check: Pólya's inequality holds (trivially) for the empty set. -/
theorem polyaInequality_empty : PolyaInequality (∅ : Set (EuclideanSpace ℝ (Fin d))) := by
  intro lam hl N u μ hu _ _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using polyaBound_nonneg _ hl
  · obtain ⟨x, hx, -⟩ := (hu ⟨0, hN⟩).ne_zero
    exact hx.elim

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

/-! ## The rectangle `(0, a) × (0, b)`: explicit eigenfunctions and the model spectrum -/

section Rect

/-- `sin (α x₀) sin (β x₁)` on `ℝ²`. -/
noncomputable def prodSin (α β : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ := sin (α * x 0) * sin (β * x 1)

theorem hasFDerivAt_prodSin (α β : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (prodSin α β)
      ((α * cos (α * x 0) * sin (β * x 1)) • (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) +
        (β * sin (α * x 0) * cos (β * x 1)) • (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) x := by
  have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => y 0) (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => y 1) (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt
  have := ((h0.const_mul α).sin).mul ((h1.const_mul β).sin)
  convert this using 1
  · rfl
  · ext v
    simp
    ring

theorem laplacian_prodSin (α β : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Δ (prodSin α β) x = -(α ^ 2 + β ^ 2) * prodSin α β x := by
  have hfd : fderiv ℝ (prodSin α β) = fun x : EuclideanSpace ℝ (Fin 2) =>
      (α * cos (α * x 0) * sin (β * x 1)) • (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) +
        (β * sin (α * x 0) * cos (β * x 1)) • (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
    funext fun x => (hasFDerivAt_prodSin α β x).fderiv
  have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => y 0) (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => y 1) (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt
  have h2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) =>
      (α * cos (α * x 0) * sin (β * x 1)) • (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) +
        (β * sin (α * x 0) * cos (β * x 1)) • (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) _ x :=
    ((((h0.const_mul α).cos.const_mul α).mul (h1.const_mul β).sin).smul_const
      (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).add
    ((((h0.const_mul α).sin.const_mul β).mul (h1.const_mul β).cos).smul_const
      (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply, hfd, Fin.sum_univ_two]
  rw [h2.fderiv]
  simp [prodSin]
  ring

theorem contDiff_prodSin (α β : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (prodSin α β) := by
  unfold prodSin; fun_prop

/-- The open rectangle `(0, a) × (0, b)` in `ℝ²`. -/
def rect (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 ∈ Ioo 0 a ∧ x 1 ∈ Ioo 0 b}

theorem isOpen_rect (a b : ℝ) : IsOpen (rect a b) := by
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 := by fun_prop
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 1 := by fun_prop
  exact (isOpen_Ioo.preimage h0).inter (isOpen_Ioo.preimage h1)

theorem frontier_rect_subset (a b : ℝ) :
    frontier (rect a b) ⊆ {x | x 0 = 0 ∨ x 0 = a ∨ x 1 = 0 ∨ x 1 = b} := by
  intro x hx
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 := by fun_prop
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 1 := by fun_prop
  have hcl : IsClosed {x : EuclideanSpace ℝ (Fin 2) | x 0 ∈ Icc 0 a ∧ x 1 ∈ Icc 0 b} :=
    (isClosed_Icc.preimage h0).inter (isClosed_Icc.preimage h1)
  have hsub : rect a b ⊆ {x : EuclideanSpace ℝ (Fin 2) | x 0 ∈ Icc 0 a ∧ x 1 ∈ Icc 0 b} := fun y hy =>
    ⟨Ioo_subset_Icc_self hy.1, Ioo_subset_Icc_self hy.2⟩
  have hx1 := closure_minimal hsub hcl hx.1
  have hx2 : x ∉ rect a b := by
    have := hx.2
    rwa [(isOpen_rect a b).interior_eq] at this
  simp only [rect, mem_ofPred_eq, mem_Ioo, mem_Icc] at hx1 hx2 ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3, c4⟩ := hcon
  exact hx2 ⟨⟨lt_of_le_of_ne hx1.1.1 (Ne.symm c1), lt_of_le_of_ne hx1.1.2 c2⟩,
    lt_of_le_of_ne hx1.2.1 (Ne.symm c3), lt_of_le_of_ne hx1.2.2 c4⟩

theorem isBounded_rect (a b : ℝ) : Bornology.IsBounded (rect a b) := by
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := |a| + |b|)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  have ha : |a| = a := abs_of_pos (h1.trans h2)
  have hb : |b| = b := abs_of_pos (h3.trans h4)
  rw [ha, hb, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
  nlinarith

theorem volume_rect {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (volume (rect a b)).toReal = a * b := by
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    (isOpen_rect a b).measurableSet.nullMeasurableSet]
  have : WithLp.toLp 2 ⁻¹' rect a b = univ.pi fun i : Fin 2 => Ioo (![0, 0] i) (![a, b] i) := by
    ext f
    simp [rect, Fin.forall_fin_two]
  rw [this, Real.volume_pi_Ioo]
  simp [Fin.prod_univ_two, ENNReal.toReal_mul, ha, hb]

/-- **The products `sin (m π x / a) sin (n π y / b)` are Dirichlet eigenfunctions of the
rectangle in the abstract sense of `IsDirichletEigenfunction`**, with eigenvalue
`π² (m²/a² + n²/b²)`. -/
theorem prodSin_isDirichletEigenfunction {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IsDirichletEigenfunction (rect a b) (π ^ 2 * ((m : ℝ) ^ 2 / a ^ 2 + (n : ℝ) ^ 2 / b ^ 2))
      (prodSin (m * π / a) (n * π / b)) where
  contDiffOn := (contDiff_prodSin _ _).contDiffOn
  continuousOn := (contDiff_prodSin _ _ (n := 0)).continuous.continuousOn
  boundary := by
    intro x hx
    have h1 : sin (m * π / a * a) = 0 := by
      rw [div_mul_cancel₀ _ ha.ne']; exact sin_nat_mul_pi m
    have h2 : sin (n * π / b * b) = 0 := by
      rw [div_mul_cancel₀ _ hb.ne']; exact sin_nat_mul_pi n
    rcases frontier_rect_subset a b hx with h | h | h | h <;> simp [prodSin, h, h1, h2]
  ne_zero := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨!₂[a / (2 * m), b / (2 * n)], ⟨⟨by simp; positivity, ?_⟩, ⟨by simp; positivity, ?_⟩⟩, ?_⟩
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      simp only [Fin.isValue, Matrix.cons_val_zero]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    · have e1 : m * π / a * (a / (2 * m)) = π / 2 := by field_simp
      have e2 : n * π / b * (b / (2 * n)) = π / 2 := by field_simp
      simp [prodSin, e1, e2]
  eigen := by
    intro x _
    rw [laplacian_prodSin]
    congr 1
    field_simp

/-- Hence every model value `π² (m²/a² + n²/b²)`, `m, n ≥ 1`, is a Dirichlet eigenvalue of the
rectangle in the abstract sense.  (The converse — that there are no others, and the
multiplicities — is *not* proved here.) -/
theorem exists_isDirichletEigenfunction_rect {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ u, IsDirichletEigenfunction (rect a b)
      (π ^ 2 * ((m : ℝ) ^ 2 / a ^ 2 + (n : ℝ) ^ 2 / b ^ 2)) u :=
  ⟨_, prodSin_isDirichletEigenfunction ha hb hm hn⟩

/-- The model Dirichlet spectrum of the rectangle, as an index set: pairs `(m, n)` of positive
integers with `π² (m²/a² + n²/b²) ≤ lam`. -/
def rectangleModel (a b lam : ℝ) : Set (ℕ × ℕ) :=
  {p | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ π ^ 2 * ((p.1 : ℝ) ^ 2 / a ^ 2 + (p.2 : ℝ) ^ 2 / b ^ 2) ≤ lam}

theorem rectangleModel_eq (a b lam : ℝ) :
    rectangleModel a b lam = ellipseLattice a b (lam / π ^ 2) := by
  have hpi : (0 : ℝ) < π ^ 2 := by have := pi_pos; positivity
  ext p
  simp only [rectangleModel, ellipseLattice, mem_ofPred_eq]
  rw [le_div_iff₀' hpi]

theorem rectangleModel_finite {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (lam : ℝ) :
    (rectangleModel a b lam).Finite := by
  rw [rectangleModel_eq]; exact ellipseLattice_finite ha hb

/-- **Pólya's inequality for the model spectrum of a rectangle**:
`#{(m, n) ∈ ℕ₊² : π² (m²/a² + n²/b²) ≤ λ} ≤ a b λ / (4π)`. -/
theorem ncard_rectangleModel_le {a b lam : ℝ} (ha : 0 < a) (hb : 0 < b) (hlam : 0 ≤ lam) :
    ((rectangleModel a b lam).ncard : ℝ) ≤ a * b * lam / (4 * π) := by
  have hpi := pi_pos
  rw [rectangleModel_eq]
  refine (ncard_ellipseLattice_le ha hb (by positivity)).trans_eq ?_
  field_simp

/-- The same, phrased with the Pólya quantity of the actual rectangle in `ℝ²`. -/
theorem ncard_rectangleModel_le_polyaBound {a b lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlam : 0 ≤ lam) :
    ((rectangleModel a b lam).ncard : ℝ) ≤ polyaBound 2 (rect a b) lam := by
  rw [polyaBound_two, volume_rect ha.le hb.le]
  exact ncard_rectangleModel_le ha hb hlam

/-- Square of side `a`: `#{(m, n) ∈ ℕ₊² : π² (m² + n²) / a² ≤ λ} ≤ a² λ / (4π)`. -/
theorem ncard_squareModel_le {a lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) :
    ((rectangleModel a a lam).ncard : ℝ) ≤ a ^ 2 * lam / (4 * π) := by
  have := ncard_rectangleModel_le ha ha hlam
  rwa [← sq] at this

end Rect

/-! ## The model spectrum of an interval -/

section IntervalModel

/-- The model Dirichlet spectrum of `(0, L)` as an index set: `k ≥ 1` with `(kπ/L)² ≤ lam`. -/
def intervalModel (L lam : ℝ) : Set ℕ := {k | 1 ≤ k ∧ ((k : ℝ) * π / L) ^ 2 ≤ lam}

theorem intervalModel_eq {L : ℝ} (hL : 0 < L) (lam : ℝ) :
    intervalModel L lam = ↑(Finset.Icc 1 ⌊L * √lam / π⌋₊) := by
  have hpi := pi_pos
  ext k
  simp only [intervalModel, mem_ofPred_eq, Finset.coe_Icc, mem_Icc]
  refine and_congr_right fun hk => ?_
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h0 : 0 ≤ L * √lam / π := by positivity
  rw [Nat.le_floor_iff h0, le_div_iff₀ hpi, ← Real.le_sqrt' (by positivity), div_le_iff₀ hL,
    mul_comm L]

/-- The counting function of the model spectrum of an interval is exactly `⌊L √λ / π⌋`. -/
theorem ncard_intervalModel {L : ℝ} (hL : 0 < L) (lam : ℝ) :
    (intervalModel L lam).ncard = ⌊L * √lam / π⌋₊ := by
  rw [intervalModel_eq hL, Set.ncard_coe_finset]; simp

/-- **Pólya's inequality for the model spectrum of an interval**: `N(λ) ≤ L √λ / π`. -/
theorem ncard_intervalModel_le {L : ℝ} (hL : 0 < L) (lam : ℝ) :
    ((intervalModel L lam).ncard : ℝ) ≤ L * √lam / π := by
  rw [ncard_intervalModel hL]
  exact Nat.floor_le (by have := pi_pos; positivity)

theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  have := InnerProductSpace.volume_ball_of_dim_odd (E := EuclideanSpace ℝ (Fin 1)) (k := 0)
    (by simp) 0 1
  simp [unitBallVolume, this]

/-- `L √λ / π` is the Pólya quantity `ω₁ L λ^{1/2} / (2π)¹` of a one-dimensional domain of
length `L`. -/
theorem intervalBound_eq (L lam : ℝ) :
    L * √lam / π = unitBallVolume 1 * L * lam ^ (((1 : ℕ) : ℝ) / 2) / (2 * π) ^ 1 := by
  have := pi_pos
  rw [unitBallVolume_one, sqrt_eq_rpow]
  field_simp
  simp

end IntervalModel

end Polya

#print axioms Polya.unitBallVolume_one
#print axioms Polya.unitBallVolume_two
#print axioms Polya.unitBallVolume_three
#print axioms Polya.polyaBound_two
#print axioms Polya.polyaConjecturePlanar_iff
#print axioms Polya.polyaBound_mono_lam
#print axioms Polya.polyaBound_mono_set
#print axioms Polya.polyaBound_smul
#print axioms Polya.PolyaConjectureDim.liYauBound
#print axioms Polya.polyaInequality_empty
#print axioms Polya.integral_sqrt_one_sub_sq_zero_one
#print axioms Polya.ncard_ellipseLattice_le
#print axioms Polya.ncard_quarterDisc_le
#print axioms Polya.sin_isDirichletEigenfunctionInterval
#print axioms Polya.eq_zero_of_ode
#print axioms Polya.eq_sin_of_ode
#print axioms Polya.IsDirichletEigenfunctionInterval.pos
#print axioms Polya.IsDirichletEigenfunctionInterval.exists_nat
#print axioms Polya.exists_isDirichletEigenfunctionInterval_iff
#print axioms Polya.card_le_floor_interval
#print axioms Polya.polya_interval
#print axioms Polya.laplacian_prodSin
#print axioms Polya.volume_rect
#print axioms Polya.prodSin_isDirichletEigenfunction
#print axioms Polya.ncard_rectangleModel_le
#print axioms Polya.ncard_rectangleModel_le_polyaBound
#print axioms Polya.ncard_squareModel_le
#print axioms Polya.ncard_intervalModel
#print axioms Polya.ncard_intervalModel_le
#print axioms Polya.intervalBound_eq
