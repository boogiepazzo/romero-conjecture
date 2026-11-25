import Mathlib

/-!
# The Hot Spots conjecture (J. Rauch, 1974)

**STATUS: IN PROGRESS / NOT YET SOLVED.**
This file contains a formal *statement* of the conjecture and machine-checked proofs of
some elementary partial results (most notably the complete one-dimensional case in its
classical formulation).  It does **not** prove the conjecture, and does not claim to.

## The mathematics

Let `Ω ⊂ ℝⁿ` be a bounded domain whose boundary is thermally insulated (Neumann boundary
condition `∂u/∂ν = 0`).  Let `μ₂ > 0` be the first nonzero eigenvalue of the Neumann Laplacian
`-Δ` on `Ω`.  For generic initial data the hottest and coldest points of the solution of the
heat equation approach, as `t → ∞`, the maximum and minimum points of a `μ₂`-eigenfunction.

**Conjecture (Rauch, 1974; first appeared in print in Kawohl's 1985 Lecture Notes).**
Every eigenfunction for `μ₂` attains its maximum and its minimum over `closure Ω` only on the
boundary `∂Ω`.

## Status in the literature (as checked by web search in November 2026 — see caveats)

* False in general:
  - K. Burdzy, W. Werner, *A counterexample to the "hot spots" conjecture*, Ann. of Math. 149
    (1999) — a planar domain with two holes.
  - R. Bass, K. Burdzy, *Fiber Brownian motion and the "hot spots" problem*, Duke Math. J. 105
    (2000); K. Burdzy, *The hot spots problem in planar domains with one hole*, Duke Math. J.
    129 (2005).  All these planar counterexamples are **not** simply connected.
  - J. de Dios Pont, *Convex sets can have interior hot spots*, arXiv:2412.06344 (Dec 2024):
    the conjecture is **false for convex domains in all sufficiently high dimensions**.
  - R. Atar, K. Burdzy, *A starlike 3-dimensional counterexample to the hot spots conjecture*,
    arXiv:2610.19908 (Oct 2026, preprint): a bounded Lipschitz starlike counterexample in `ℝ³`.
* True for special classes: B. Kawohl (1985, cylinders `D × (0, a)`); R. Bañuelos, K. Burdzy
  (1999, certain symmetric/long convex planar domains); D. Jerison, N. Nadirashvili (2000, planar
  convex domains with two axes of symmetry); R. Atar, K. Burdzy (2004, lip domains);
  C. Judge, S. Mondal (2020, all Euclidean triangles; erratum 2022).
* Very recent, *not yet refereed* claims (reported on MathWorld's "Hot Spots Conjecture" page and
  in arXiv preprints of Sep–Nov 2026; we have **not** verified them and treat them as unconfirmed):
  a preprint attributed to OpenAI (24 Sep 2026) asserting the strict conjecture for *smooth*
  bounded simply connected planar domains; conditional extensions to nonsmooth simply connected
  planar domains with simple `μ₂`, in a non-strict form (K. Burdzy, arXiv:2610.12622;
  R. Bañuelos, arXiv:2610.32920); and piecewise smooth planar Jordan domains with convex corners,
  including all convex polygons (Pineda Montoya, Gallego González, Porras Barrera, Rúa Muñoz,
  arXiv:2611.26403).
* What is open: in the refereed literature, the conjecture for **planar convex domains** (and,
  more generally, simply connected planar domains) is open; it is also open for convex domains
  in low dimensions `n ≥ 3`.  Even if the 2026 preprints above are correct, the strict statement
  for *arbitrary* (non-piecewise-smooth) convex planar domains is not claimed by them.

The statement formalised below as `HotSpotsConjecturePlanarConvex` is the planar convex version.

## Formalisation choices and their limits

Mathlib has no Sobolev spaces, so eigenfunctions are described by a *weak (variational)
identity tested against smooth functions on the whole space*:
`∫_Ω ⟪∇u, ∇φ⟫ = μ ∫_Ω u φ` for every `φ ∈ C^∞(ℝⁿ)`.
Because `φ` is **not** required to vanish near `∂Ω`, this encodes the natural (Neumann) boundary
condition without ever mentioning a normal vector, so no boundary regularity of `Ω` is needed.
The candidate `u` is required to be `C²` in the open set `Ω`, continuous on `closure Ω`, and to
have square-integrable gradient on `Ω`.

* For bounded *Lipschitz* domains (in particular bounded convex domains) this is faithful:
  restrictions of `C^∞(ℝⁿ)` functions are dense in `H¹(Ω)`, genuine Neumann eigenfunctions are
  real-analytic inside `Ω` and Hölder continuous up to the boundary, and a function that is `C²`
  in `Ω` with `u, ∇u ∈ L²(Ω)` lies in `H¹(Ω)`.  None of these facts is formalised here; they are
  the (informal) justification that the definition matches the textbook one.
* For domains with very rough boundary (no extension property) the test class `C^∞(ℝⁿ)|_Ω`
  need not be dense in `H¹(Ω)` and eigenfunctions need not extend continuously to `closure Ω`,
  so there the definition may differ from the usual one.  The conjecture stated here only
  quantifies over convex domains, where this issue does not arise.
* The "first nonzero eigenvalue" is the least `μ > 0` admitting an eigenfunction in this sense.
* The conjecture is stated in its *strict* form ("extrema only on the boundary").

## What is proved in this file (all without `sorry`/axioms beyond the standard three)

General `n`-dimensional facts about the weak formulation:
* `IsNeumannEigenfunction.integral_eq_zero` : an eigenfunction with `μ ≠ 0` has zero mean.
* `IsNeumannEigenfunction.exists_pos`, `.exists_neg` : on a bounded open `Ω` it takes both
  strictly positive and strictly negative values.
* `IsNeumannEigenfunction.pos_of_isMaxOn`, `.neg_of_isMinOn` : its max over `closure Ω` is
  positive and its min is negative.

The one-dimensional case `Ω = (0, L)` in the **classical** formulation
(`u'' = -μ u` on `[0, L]`, `u'(0) = u'(L) = 0`, `u ≢ 0`):
* `cos_isNeumannEigenfunctionInterval` : `cos (π x / L)` is an eigenfunction for `(π/L)²`.
* `hasDerivAt_cos_interval`, `hasDerivAt_deriv_cos_interval` : its first two derivatives.
* `strictAntiOn_cos_interval`, `cos_interval_eq_zero_of_isMaxOn`, `cos_interval_eq_of_isMinOn` :
  it is strictly decreasing on `[0, L]`, so its max over `[0, L]` is attained only at `0` and
  its min only at `L` (via the general lemmas `eq_left_of_strictAntiOn_of_isMaxOn`,
  `eq_right_of_strictAntiOn_of_isMinOn`).
* `eq_cos_of_ode` : if `u'' = -μ u` on `[0, L]`, `μ > 0`, `u'(0) = 0`, then
  `u = u 0 * cos (√μ x)` and `u' = -(u 0 * √μ * sin (√μ x))` on `[0, L]`.
* `IsNeumannEigenfunctionInterval.eq_cos` : (ODE uniqueness, by an energy argument) every
  eigenfunction is `u 0 * cos (√μ x)` with `u 0 ≠ 0` and `sin (√μ L) = 0`.
* `IsNeumannEigenfunctionInterval.le_eigenvalue` : every positive eigenvalue is `≥ (π/L)²`.
* `isFirstNeumannEigenvalueInterval_iff` : the first nonzero eigenvalue is exactly `(π/L)²`.
* `IsNeumannEigenfunctionInterval.eq_const_mul_cos` : every eigenfunction for `(π/L)²` is, on
  `[0, L]`, a nonzero multiple of `cos (π x / L)`.
* `IsNeumannEigenfunctionInterval.eq_endpoint_of_isExtrOn` : hence its extrema over `[0, L]`
  are attained only at `0` or `L`.
* `hotSpotsPropertyInterval` : **the hot spots property holds on every interval** (classical
  formulation): extrema over `closure (Ioo 0 L)` lie in `frontier (Ioo 0 L)`.
* `IsNeumannEigenfunctionInterval.weak` : a classical 1D eigenfunction satisfies the weak
  identity `∫₀ᴸ u' φ' = μ ∫₀ᴸ u φ` for every `C¹` test function `φ`.

## What is NOT proved

* `HotSpotsConjecturePlanarConvex` (the conjecture itself) — only stated, as a `Prop`.
* `HotSpotsConjectureConvex n` for `n ≥ 3` — only stated; reported false for large `n`
  (de Dios Pont 2024), which is also not formalised here.
* No link between the classical 1D formulation and the weak `n`-dimensional formulation for
  `n = 1` is proved beyond `IsNeumannEigenfunctionInterval.weak` (classical ⇒ weak on `ℝ`); in
  particular `HotSpotsProperty` for subsets of `EuclideanSpace ℝ (Fin 1)` is not proved.
* No existence theory (spectral theorem for the Neumann Laplacian) is formalised: in the
  `n`-dimensional setting it is not proved that `IsFirstNeumannEigenvalue Ω μ` holds for any `μ`
  (if it held for none, `HotSpotsProperty Ω` would be vacuously true — mathematically this does
  not happen for bounded Lipschitz domains, but that is not checked here).
-/

open MeasureTheory Set Real
open scoped RealInnerProductSpace Gradient ContDiff

namespace HotSpots

/-! ## The weak formulation in `ℝⁿ` -/

section Weak

variable {n : ℕ}

/-- `u` is a (real) Neumann eigenfunction of `-Δ` on `Ω` with eigenvalue `μ`, in the weak sense
tested against smooth functions on the whole space (see the file header for a discussion). -/
structure IsNeumannEigenfunction (Ω : Set (EuclideanSpace ℝ (Fin n))) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  /-- interior regularity -/
  contDiffOn : ContDiffOn ℝ 2 u Ω
  /-- continuity up to the boundary -/
  continuousOn : ContinuousOn u (closure Ω)
  /-- finite Dirichlet energy -/
  integrable_grad : IntegrableOn (fun x => ‖∇ u x‖ ^ 2) Ω
  /-- nontriviality -/
  ne_zero : ∃ x ∈ Ω, u x ≠ 0
  /-- weak eigenvalue equation with natural (Neumann) boundary condition -/
  weak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ φ →
    (∫ x in Ω, inner ℝ (∇ u x) (∇ φ x)) = μ * ∫ x in Ω, u x * φ x

/-- `μ` is the first nonzero Neumann eigenvalue of `Ω`: the least positive `μ` admitting an
eigenfunction. -/
def IsFirstNeumannEigenvalue (Ω : Set (EuclideanSpace ℝ (Fin n))) (μ : ℝ) : Prop :=
  0 < μ ∧ (∃ u, IsNeumannEigenfunction Ω μ u) ∧
    ∀ ν, 0 < ν → (∃ u, IsNeumannEigenfunction Ω ν u) → μ ≤ ν

/-- The (strict) hot spots property for `Ω`: every eigenfunction for the first nonzero Neumann
eigenvalue attains its maximum and its minimum over `closure Ω` only on the boundary. -/
def HotSpotsProperty (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ μ u, IsFirstNeumannEigenvalue Ω μ → IsNeumannEigenfunction Ω μ u →
    ∀ x ∈ closure Ω, (IsMaxOn u (closure Ω) x ∨ IsMinOn u (closure Ω) x) → x ∈ frontier Ω

/-- The hot spots conjecture for bounded convex domains of `ℝⁿ`.
**Only a statement.**  Reported FALSE for all sufficiently large `n` (J. de Dios Pont,
arXiv:2412.06344, 2024); that disproof is not formalised here. -/
def HotSpotsConjectureConvex (n : ℕ) : Prop :=
  ∀ Ω : Set (EuclideanSpace ℝ (Fin n)),
    IsOpen Ω → Bornology.IsBounded Ω → Convex ℝ Ω → Ω.Nonempty → HotSpotsProperty Ω

/-- **The hot spots conjecture for planar convex domains.**
**Only a statement — NOT proved here.**  Open in the refereed literature as of 2026. -/
def HotSpotsConjecturePlanarConvex : Prop := HotSpotsConjectureConvex 2

variable {Ω : Set (EuclideanSpace ℝ (Fin n))} {μ : ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}

/-- An eigenfunction for a nonzero eigenvalue has zero mean (test the weak identity with
`φ = 1`). -/
theorem IsNeumannEigenfunction.integral_eq_zero (h : IsNeumannEigenfunction Ω μ u)
    (hμ : μ ≠ 0) : ∫ x in Ω, u x = 0 := by
  have := h.weak (fun _ => 1) contDiff_const
  simp only [gradient_fun_const, inner_zero_right, integral_zero, mul_one] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hμ

/-- On a bounded domain an eigenfunction is integrable. -/
theorem IsNeumannEigenfunction.integrableOn (h : IsNeumannEigenfunction Ω μ u)
    (hb : Bornology.IsBounded Ω) : IntegrableOn u Ω :=
  (h.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure

private theorem eqOn_zero_of_nonneg_of_integral_eq_zero {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΩ : IsOpen Ω) (hc : ContinuousOn v Ω) (hi : IntegrableOn v Ω)
    (h0 : ∀ x ∈ Ω, 0 ≤ v x) (hint : ∫ x in Ω, v x = 0) : EqOn v 0 Ω := by
  have hnn : 0 ≤ᵐ[volume.restrict Ω] v :=
    (ae_restrict_iff' hΩ.measurableSet).2 (Filter.Eventually.of_forall h0)
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 hint
  exact Measure.eqOn_open_of_ae_eq this hΩ hc continuousOn_const

/-- An eigenfunction for a nonzero eigenvalue on a bounded open set is positive somewhere. -/
theorem IsNeumannEigenfunction.exists_pos (h : IsNeumannEigenfunction Ω μ u) (hμ : μ ≠ 0)
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : ∃ x ∈ Ω, 0 < u x := by
  by_contra hcon
  push Not at hcon
  have hc : ContinuousOn u Ω := h.continuousOn.mono subset_closure
  have key : EqOn (fun x => -u x) 0 Ω :=
    eqOn_zero_of_nonneg_of_integral_eq_zero hΩ hc.neg (h.integrableOn hb).neg
      (fun x hx => neg_nonneg.2 (hcon x hx))
      (by rw [integral_neg, h.integral_eq_zero hμ, neg_zero])
  obtain ⟨x, hx, hux⟩ := h.ne_zero
  exact hux (by simpa using key hx)

/-- An eigenfunction for a nonzero eigenvalue on a bounded open set is negative somewhere. -/
theorem IsNeumannEigenfunction.exists_neg (h : IsNeumannEigenfunction Ω μ u) (hμ : μ ≠ 0)
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : ∃ x ∈ Ω, u x < 0 := by
  by_contra hcon
  push Not at hcon
  have hc : ContinuousOn u Ω := h.continuousOn.mono subset_closure
  have key : EqOn u 0 Ω :=
    eqOn_zero_of_nonneg_of_integral_eq_zero hΩ hc (h.integrableOn hb) hcon
      (h.integral_eq_zero hμ)
  obtain ⟨x, hx, hux⟩ := h.ne_zero
  exact hux (by simpa using key hx)

/-- The maximum of an eigenfunction (nonzero eigenvalue) over `closure Ω` is positive. -/
theorem IsNeumannEigenfunction.pos_of_isMaxOn (h : IsNeumannEigenfunction Ω μ u) (hμ : μ ≠ 0)
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsMaxOn u (closure Ω) x) : 0 < u x := by
  obtain ⟨y, hy, hpos⟩ := h.exists_pos hμ hΩ hb
  exact hpos.trans_le (hx (subset_closure hy))

/-- The minimum of an eigenfunction (nonzero eigenvalue) over `closure Ω` is negative. -/
theorem IsNeumannEigenfunction.neg_of_isMinOn (h : IsNeumannEigenfunction Ω μ u) (hμ : μ ≠ 0)
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsMinOn u (closure Ω) x) : u x < 0 := by
  obtain ⟨y, hy, hneg⟩ := h.exists_neg hμ hΩ hb
  exact (hx (subset_closure hy)).trans_lt hneg

end Weak

/-! ## Strictly monotone functions have their extrema only at the endpoints -/

section Monotone

variable {f : ℝ → ℝ} {a b x : ℝ}

theorem eq_left_of_strictAntiOn_of_isMaxOn (hf : StrictAntiOn f (Icc a b)) (hx : x ∈ Icc a b)
    (hmax : IsMaxOn f (Icc a b) x) : x = a := by
  by_contra hne
  have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
  have ha : a ∈ Icc a b := ⟨le_rfl, hx.1.trans hx.2⟩
  exact absurd (hmax ha) (not_le.2 (hf ha hx hax))

theorem eq_right_of_strictAntiOn_of_isMinOn (hf : StrictAntiOn f (Icc a b)) (hx : x ∈ Icc a b)
    (hmin : IsMinOn f (Icc a b) x) : x = b := by
  by_contra hne
  have hxb : x < b := lt_of_le_of_ne hx.2 hne
  have hb : b ∈ Icc a b := ⟨hx.1.trans hx.2, le_rfl⟩
  exact absurd (hmin hb) (not_le.2 (hf hx hb hxb))

end Monotone

/-! ## The one-dimensional case, classical formulation -/

section Interval

variable {L μ : ℝ} {u : ℝ → ℝ}

/-- Classical Neumann eigenfunction on the interval `(0, L)`: `u` is twice differentiable on
`[0, L]` (one-sided at the endpoints) with `u'' = -μ u`, `u'(0) = u'(L) = 0`, and `u ≢ 0`. -/
def IsNeumannEigenfunctionInterval (L μ : ℝ) (u : ℝ → ℝ) : Prop :=
  (∃ u' : ℝ → ℝ,
    (∀ x ∈ Icc 0 L, HasDerivWithinAt u (u' x) (Icc 0 L) x) ∧
    (∀ x ∈ Icc 0 L, HasDerivWithinAt u' (-μ * u x) (Icc 0 L) x) ∧
    u' 0 = 0 ∧ u' L = 0) ∧
  ∃ x ∈ Icc 0 L, u x ≠ 0

/-- First nonzero Neumann eigenvalue of the interval `(0, L)` (classical formulation). -/
def IsFirstNeumannEigenvalueInterval (L μ : ℝ) : Prop :=
  0 < μ ∧ (∃ u, IsNeumannEigenfunctionInterval L μ u) ∧
    ∀ ν, 0 < ν → (∃ u, IsNeumannEigenfunctionInterval L ν u) → μ ≤ ν

/-- Hot spots property of the interval `(0, L)` (classical formulation). -/
def HotSpotsPropertyInterval (L : ℝ) : Prop :=
  ∀ μ u, IsFirstNeumannEigenvalueInterval L μ → IsNeumannEigenfunctionInterval L μ u →
    ∀ x ∈ closure (Ioo 0 L),
      (IsMaxOn u (closure (Ioo 0 L)) x ∨ IsMinOn u (closure (Ioo 0 L)) x) →
        x ∈ frontier (Ioo 0 L)

/-! ### (a) Calculus facts for `cos (π x / L)` -/

theorem hasDerivAt_cos_interval (L x : ℝ) :
    HasDerivAt (fun x => cos (π * x / L)) (-(π / L) * sin (π * x / L)) x := by
  have h1 : HasDerivAt (fun x : ℝ => π * x / L) (π / L) x := by
    simpa using ((hasDerivAt_id x).const_mul π).div_const L
  convert (hasDerivAt_cos (π * x / L)).comp x h1 using 1
  · rfl
  · ring

theorem hasDerivAt_deriv_cos_interval (L x : ℝ) :
    HasDerivAt (fun x => -(π / L) * sin (π * x / L)) (-(π / L) ^ 2 * cos (π * x / L)) x := by
  have h1 : HasDerivAt (fun x : ℝ => π * x / L) (π / L) x := by
    simpa using ((hasDerivAt_id x).const_mul π).div_const L
  convert ((hasDerivAt_sin (π * x / L)).comp x h1).const_mul (-(π / L)) using 1
  · rfl
  · ring

/-- `cos (π x / L)` is strictly decreasing on `[0, L]`. -/
theorem strictAntiOn_cos_interval (hL : 0 < L) :
    StrictAntiOn (fun x => cos (π * x / L)) (Icc 0 L) := by
  intro x hx y hy hxy
  have hmem : ∀ z ∈ Icc (0 : ℝ) L, π * z / L ∈ Icc 0 π := fun z hz =>
    ⟨by have := pi_pos; have := hz.1; positivity, by
      rw [div_le_iff₀ hL]; exact mul_le_mul_of_nonneg_left hz.2 pi_pos.le⟩
  refine strictAntiOn_cos (hmem x hx) (hmem y hy) ?_
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hxy pi_pos) hL

/-- The maximum of `cos (π x / L)` over `[0, L]` is attained only at `0`. -/
theorem cos_interval_eq_zero_of_isMaxOn (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc 0 L)
    (h : IsMaxOn (fun x => cos (π * x / L)) (Icc 0 L) x) : x = 0 :=
  eq_left_of_strictAntiOn_of_isMaxOn (strictAntiOn_cos_interval hL) hx h

/-- The minimum of `cos (π x / L)` over `[0, L]` is attained only at `L`. -/
theorem cos_interval_eq_of_isMinOn (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc 0 L)
    (h : IsMinOn (fun x => cos (π * x / L)) (Icc 0 L) x) : x = L :=
  eq_right_of_strictAntiOn_of_isMinOn (strictAntiOn_cos_interval hL) hx h

/-- `cos (π x / L)` is a classical Neumann eigenfunction on `(0, L)` for `(π / L)²`. -/
theorem cos_isNeumannEigenfunctionInterval (hL : 0 < L) :
    IsNeumannEigenfunctionInterval L ((π / L) ^ 2) (fun x => cos (π * x / L)) := by
  refine ⟨⟨fun x => -(π / L) * sin (π * x / L), fun x _ =>
    (hasDerivAt_cos_interval L x).hasDerivWithinAt, fun x _ =>
    (hasDerivAt_deriv_cos_interval L x).hasDerivWithinAt, by simp, ?_⟩,
    0, ⟨le_rfl, hL.le⟩, by simp⟩
  have : π * L / L = π := by field_simp
  simp [this]

/-! ### (b) ODE uniqueness by the energy method -/

/-- A function on `[0, L]` whose one-sided derivative vanishes identically is constant. -/
private theorem eq_of_hasDerivWithinAt_zero {E : ℝ → ℝ}
    (h : ∀ x ∈ Icc 0 L, HasDerivWithinAt E 0 (Icc 0 L) x) : ∀ x ∈ Icc 0 L, E x = E 0 := by
  refine constant_of_has_deriv_right_zero (fun x hx => (h x hx).continuousWithinAt) ?_
  intro x hx
  exact (h x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

/-- **ODE uniqueness.**  If `u'' = -μ u` on `[0, L]` with `μ > 0` and `u'(0) = 0`, then
`u x = u 0 * cos (√μ x)` and `u' x = -(u 0 * √μ * sin (√μ x))` on `[0, L]`. -/
theorem eq_cos_of_ode (hμ : 0 < μ) {u' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (u' x) (Icc 0 L) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivWithinAt u' (-μ * u x) (Icc 0 L) x)
    (h0 : u' 0 = 0) {x : ℝ} (hx : x ∈ Icc 0 L) :
    u x = u 0 * cos (√μ * x) ∧ u' x = -(u 0 * √μ * sin (√μ * x)) := by
  have hw : √μ * √μ = μ := mul_self_sqrt hμ.le
  set w := √μ with hwdef
  -- the difference `v` and its derivative `v'`
  have hv : ∀ y ∈ Icc 0 L, HasDerivWithinAt (fun y => u y - u 0 * cos (w * y))
      (u' y + u 0 * w * sin (w * y)) (Icc 0 L) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using (hasDerivAt_id y).const_mul w
    have h2 := (((hasDerivAt_cos (w * y)).comp y h1).const_mul (u 0)).hasDerivWithinAt
      (s := Icc 0 L)
    convert (hu y hy).sub h2 using 1
    · rfl
    · ring
  have hv' : ∀ y ∈ Icc 0 L, HasDerivWithinAt (fun y => u' y + u 0 * w * sin (w * y))
      (-μ * (u y - u 0 * cos (w * y))) (Icc 0 L) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using (hasDerivAt_id y).const_mul w
    have h2 := (((hasDerivAt_sin (w * y)).comp y h1).const_mul (u 0 * w)).hasDerivWithinAt
      (s := Icc 0 L)
    convert (hu' y hy).add h2 using 1
    · rfl
    · rw [← hw]; ring
  -- the energy `v'² + μ v²` is constant
  have hE : ∀ y ∈ Icc 0 L, HasDerivWithinAt
      (fun y => (u' y + u 0 * w * sin (w * y)) ^ 2 + μ * (u y - u 0 * cos (w * y)) ^ 2)
      0 (Icc 0 L) y := by
    intro y hy
    convert ((hv' y hy).pow 2).add (((hv y hy).pow 2).const_mul μ) using 1
    ring
  have hEx := eq_of_hasDerivWithinAt_zero hE x hx
  simp only [h0, mul_zero, sin_zero, cos_zero, mul_one, sub_self, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hEx
  have ha : 0 ≤ (u' x + u 0 * w * sin (w * x)) ^ 2 := sq_nonneg _
  have hb : 0 ≤ μ * (u x - u 0 * cos (w * x)) ^ 2 := by positivity
  have ha0 : (u' x + u 0 * w * sin (w * x)) ^ 2 = 0 := by linarith
  have hb0 : μ * (u x - u 0 * cos (w * x)) ^ 2 = 0 := by linarith
  have hb1 : (u x - u 0 * cos (w * x)) ^ 2 = 0 := (mul_eq_zero.mp hb0).resolve_left hμ.ne'
  constructor
  · linarith [pow_eq_zero_iff (two_ne_zero) |>.1 hb1]
  · linarith [pow_eq_zero_iff (two_ne_zero) |>.1 ha0]

/-- Every classical Neumann eigenfunction on `(0, L)` with `μ > 0` is `u 0 * cos (√μ x)`, with
`u 0 ≠ 0` and `sin (√μ L) = 0`. -/
theorem IsNeumannEigenfunctionInterval.eq_cos (hL : 0 < L) (hμ : 0 < μ)
    (h : IsNeumannEigenfunctionInterval L μ u) :
    u 0 ≠ 0 ∧ sin (√μ * L) = 0 ∧ ∀ x ∈ Icc 0 L, u x = u 0 * cos (√μ * x) := by
  obtain ⟨⟨u', hu, hu', h0, hLd⟩, y, hy, huy⟩ := h
  have hu0 : u 0 ≠ 0 := by
    intro hzero
    apply huy
    rw [(eq_cos_of_ode hμ hu hu' h0 hy).1, hzero, zero_mul]
  refine ⟨hu0, ?_, fun x hx => (eq_cos_of_ode hμ hu hu' h0 hx).1⟩
  have := (eq_cos_of_ode hμ hu hu' h0 (⟨hL.le, le_rfl⟩ : L ∈ Icc 0 L)).2
  rw [hLd] at this
  have hsqrt : √μ ≠ 0 := (sqrt_pos.2 hμ).ne'
  have h3 : u 0 * √μ * sin (√μ * L) = 0 := by linarith
  exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero hu0 hsqrt)

/-- Every positive Neumann eigenvalue of `(0, L)` is at least `(π / L)²`. -/
theorem IsNeumannEigenfunctionInterval.le_eigenvalue (hL : 0 < L) (hμ : 0 < μ)
    (h : IsNeumannEigenfunctionInterval L μ u) : (π / L) ^ 2 ≤ μ := by
  obtain ⟨-, hsin, -⟩ := h.eq_cos hL hμ
  by_contra hlt
  push Not at hlt
  have hpos : 0 < √μ * L := mul_pos (sqrt_pos.2 hμ) hL
  have hlt' : √μ < π / L := by
    have := sqrt_lt_sqrt hμ.le hlt
    rwa [sqrt_sq (div_pos pi_pos hL).le] at this
  have : √μ * L < π := by rwa [lt_div_iff₀ hL] at hlt'
  exact (sin_pos_of_pos_of_lt_pi hpos this).ne' hsin

/-- The first nonzero Neumann eigenvalue of `(0, L)` is exactly `(π / L)²`. -/
theorem isFirstNeumannEigenvalueInterval_iff (hL : 0 < L) :
    IsFirstNeumannEigenvalueInterval L μ ↔ μ = (π / L) ^ 2 := by
  have hpos : 0 < (π / L) ^ 2 := by have := pi_pos; positivity
  constructor
  · rintro ⟨hμ, ⟨u, hu⟩, hmin⟩
    exact le_antisymm (hmin _ hpos ⟨_, cos_isNeumannEigenfunctionInterval hL⟩)
      (hu.le_eigenvalue hL hμ)
  · rintro rfl
    exact ⟨hpos, ⟨_, cos_isNeumannEigenfunctionInterval hL⟩,
      fun ν hν ⟨u, hu⟩ => hu.le_eigenvalue hL hν⟩

/-- Every eigenfunction for the first nonzero eigenvalue `(π / L)²` of `(0, L)` is a
nonzero multiple of `cos (π x / L)` on `[0, L]`. -/
theorem IsNeumannEigenfunctionInterval.eq_const_mul_cos (hL : 0 < L)
    (h : IsNeumannEigenfunctionInterval L ((π / L) ^ 2) u) :
    u 0 ≠ 0 ∧ ∀ x ∈ Icc 0 L, u x = u 0 * cos (π * x / L) := by
  have hpos : 0 < (π / L) ^ 2 := by have := pi_pos; positivity
  obtain ⟨hu0, -, hform⟩ := h.eq_cos hL hpos
  refine ⟨hu0, fun x hx => ?_⟩
  rw [hform x hx, sqrt_sq (div_pos pi_pos hL).le]
  congr 2
  ring

/-! ### (c) The hot spots property on an interval -/

private theorem le_of_mul_le_mul_left_of_neg' {a b c : ℝ} (h : c * a ≤ c * b) (hc : c < 0) :
    b ≤ a := by
  by_contra hlt
  push Not at hlt
  nlinarith [mul_pos (neg_pos.2 hc) (sub_pos.2 hlt)]

/-- For a first eigenfunction on `(0, L)`, extrema over `[0, L]` are attained only at the
endpoints. -/
theorem IsNeumannEigenfunctionInterval.eq_endpoint_of_isExtrOn (hL : 0 < L)
    (h : IsNeumannEigenfunctionInterval L ((π / L) ^ 2) u) {x : ℝ} (hx : x ∈ Icc 0 L)
    (hext : IsMaxOn u (Icc 0 L) x ∨ IsMinOn u (Icc 0 L) x) : x = 0 ∨ x = L := by
  obtain ⟨hu0, hform⟩ := h.eq_const_mul_cos hL
  -- transfer extremality of `u` to extremality of `cos (π x / L)`
  have hle : ∀ y ∈ Icc 0 L, ∀ z ∈ Icc 0 L, (u y ≤ u z ↔
      u 0 * cos (π * y / L) ≤ u 0 * cos (π * z / L)) := fun y hy z hz => by
    rw [hform y hy, hform z hz]
  rcases lt_or_gt_of_ne hu0 with hneg | hpos
  · -- negative multiple: max ↔ min of cos
    rcases hext with hmax | hmin
    · right
      refine cos_interval_eq_of_isMinOn hL hx fun y hy => ?_
      have := (hle y hy x hx).1 (hmax hy)
      exact le_of_mul_le_mul_left_of_neg' this hneg
    · left
      refine cos_interval_eq_zero_of_isMaxOn hL hx fun y hy => ?_
      have := (hle x hx y hy).1 (hmin hy)
      exact le_of_mul_le_mul_left_of_neg' this hneg
  · rcases hext with hmax | hmin
    · left
      refine cos_interval_eq_zero_of_isMaxOn hL hx fun y hy => ?_
      have := (hle y hy x hx).1 (hmax hy)
      exact le_of_mul_le_mul_left this hpos
    · right
      refine cos_interval_eq_of_isMinOn hL hx fun y hy => ?_
      have := (hle x hx y hy).1 (hmin hy)
      exact le_of_mul_le_mul_left this hpos

/-- **The hot spots property holds on every bounded interval** (classical formulation):
every eigenfunction for the first nonzero Neumann eigenvalue of `(0, L)` attains its maximum
and minimum over `[0, L] = closure (0, L)` only on `{0, L} = frontier (0, L)`. -/
theorem hotSpotsPropertyInterval (hL : 0 < L) : HotSpotsPropertyInterval L := by
  intro μ u hμ hu x hx hext
  rw [closure_Ioo hL.ne] at hx hext
  rw [frontier_Ioo hL]
  rw [(isFirstNeumannEigenvalueInterval_iff hL).1 hμ] at hu
  simpa using hu.eq_endpoint_of_isExtrOn hL hx hext

/-! ### Classical ⇒ weak in one dimension -/

/-- A classical Neumann eigenfunction on `(0, L)` satisfies the weak identity
`∫₀ᴸ u' φ' = μ ∫₀ᴸ u φ` against every `C¹` test function `φ` (no condition on `φ` at the
endpoints): the boundary terms vanish because `u'(0) = u'(L) = 0`. -/
theorem weak_of_classical (hL : 0 < L) {u' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (u' x) (Icc 0 L) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivWithinAt u' (-μ * u x) (Icc 0 L) x)
    (h0 : u' 0 = 0) (hLd : u' L = 0) {φ φ' : ℝ → ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ') :
    ∫ x in (0 : ℝ)..L, u' x * φ' x = μ * ∫ x in (0 : ℝ)..L, u x * φ x := by
  have hI : Set.uIcc 0 L = Icc 0 L := uIcc_of_le hL.le
  have hcu : ContinuousOn u (Icc 0 L) := fun x hx => (hu x hx).continuousWithinAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := 0) (b := L) (u := u') (u' := fun x => -μ * u x) (v := φ) (v' := φ')
    (by rw [hI]; exact hu') (fun x _ => (hφ x).hasDerivWithinAt)
    ((hcu.const_smul (-μ)).intervalIntegrable_of_Icc hL.le |>.congr (by intro x _; simp))
    (hφ'.intervalIntegrable _ _)
  rw [key, h0, hLd]
  simp only [zero_mul, sub_self, zero_sub, neg_mul, mul_assoc]
  rw [intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul]

/-- Version of `weak_of_classical` phrased with the eigenfunction predicate. -/
theorem IsNeumannEigenfunctionInterval.weak (hL : 0 < L)
    (h : IsNeumannEigenfunctionInterval L μ u) :
    ∃ u' : ℝ → ℝ, (∀ x ∈ Icc 0 L, HasDerivWithinAt u (u' x) (Icc 0 L) x) ∧
      ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' →
        ∫ x in (0 : ℝ)..L, u' x * φ' x = μ * ∫ x in (0 : ℝ)..L, u x * φ x := by
  obtain ⟨⟨u', hu, hu', h0, hLd⟩, -⟩ := h
  exact ⟨u', hu, fun φ φ' hφ hφ' => weak_of_classical hL hu hu' h0 hLd hφ hφ'⟩

end Interval

end HotSpots

#print axioms HotSpots.IsNeumannEigenfunction.integral_eq_zero
#print axioms HotSpots.IsNeumannEigenfunction.exists_pos
#print axioms HotSpots.IsNeumannEigenfunction.exists_neg
#print axioms HotSpots.IsNeumannEigenfunction.pos_of_isMaxOn
#print axioms HotSpots.IsNeumannEigenfunction.neg_of_isMinOn
#print axioms HotSpots.strictAntiOn_cos_interval
#print axioms HotSpots.cos_isNeumannEigenfunctionInterval
#print axioms HotSpots.eq_cos_of_ode
#print axioms HotSpots.IsNeumannEigenfunctionInterval.eq_cos
#print axioms HotSpots.IsNeumannEigenfunctionInterval.le_eigenvalue
#print axioms HotSpots.isFirstNeumannEigenvalueInterval_iff
#print axioms HotSpots.IsNeumannEigenfunctionInterval.eq_const_mul_cos
#print axioms HotSpots.IsNeumannEigenfunctionInterval.eq_endpoint_of_isExtrOn
#print axioms HotSpots.hotSpotsPropertyInterval
#print axioms HotSpots.IsNeumannEigenfunctionInterval.weak
