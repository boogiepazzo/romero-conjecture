import Mathlib

/-!
# The Elliott–Halberstam conjecture (von Mangoldt / ψ form)

**STATUS: IN PROGRESS / NOT YET SOLVED.**  The Elliott–Halberstam conjecture is an OPEN problem.
This file does **not** prove it.  It contains a faithful formal *statement* together with a
collection of machine-checked, elementary partial results and reductions.

## Statement

For `x : ℝ`, `q a : ℕ` put `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)`, with `Λ` the von Mangoldt
function, and
`E(x; q) = max_{a mod q, gcd(a, q) = 1} |ψ(x; q, a) − x / φ(q)|`.

**Conjecture (Elliott–Halberstam).** For every `θ ∈ (0, 1)` and every `A > 0` there is a constant
`C` such that for all `x ≥ 2`
`∑_{1 ≤ q ≤ x ^ θ} E(x; q) ≤ C · x / (log x) ^ A`.

In this file: `psiAP`, `E`, `EH θ` (the statement for a fixed level `θ`, all `A`), and
`ElliottHalberstamConjecture := ∀ θ, 0 < θ → θ < 1 → EH θ`.

## Attribution and history (uncertainties preserved, not resolved)

* P. D. T. A. Elliott and H. Halberstam, *A conjecture in prime number theory*, Symposia
  Mathematica, Vol. IV (INDAM, Rome, 1968/69), Academic Press, London, pp. 59–72.  The conference
  was 1968/69 and the volume is dated 1970; the conjecture is cited in the literature both as
  "1968" and as "1970".  We have not consulted the original paper; secondary sources remark that
  the original formulation differs from (and is less clean than) the modern one stated here.  The
  form used here is the standard modern ψ-form.
* For `θ < 1/2` the statement is the Bombieri–Vinogradov theorem: E. Bombieri, *On the large
  sieve*, Mathematika 12 (1965), and A. I. Vinogradov, *The density hypothesis for Dirichlet
  L-series*, Izv. Akad. Nauk SSSR Ser. Mat. 29 (1965) (with a 1966 corrigendum); the two works were
  independent, and the precise shapes of their results differ (Vinogradov's original range was
  slightly weaker).  **Bombieri–Vinogradov is not in mathlib and is not proved here.**
* The endpoint `θ = 1` is false: J. Friedlander and A. Granville, *Limitations to the
  equi-distribution of primes I*, Ann. of Math. 129 (1989), 363–382 (the estimate fails already for
  `q` up to `x / (log x)^B`).  Hence the restriction `θ < 1`.
* Consequences: Goldston–Pintz–Yıldırım (*Primes in tuples I*, arXiv 2005, Ann. of Math. 2009)
  showed any level of distribution `> 1/2` gives bounded gaps between primes, and EH gives gaps
  `≤ 16` infinitely often; Maynard (2015) improved this to `≤ 12` under EH, and Polymath8b (2014)
  to `≤ 6` under a *generalized* EH.
* Beyond `1/2` only restricted variants are known (smooth / well-factorable moduli, fixed residue
  classes, special weights): Fouvry–Iwaniec and Bombieri–Friedlander–Iwaniec (1980s), Zhang
  (Ann. of Math. 2014), Polymath8a (2014), Maynard (*Primes in arithmetic progressions to large
  moduli I–III*, arXiv 2020), Lichtman (arXiv 2023), and others.  None of these gives `EH θ` as
  defined here for any `θ > 1/2`; to our knowledge (literature check, November 2026) the statement
  `EH θ` is open for every `θ ∈ (1/2, 1)` and for `θ = 1/2` itself.

## What IS proved here (all unconditional, elementary)

* Sanity of the definitions: `psiAP_one` (`ψ(x;1,a) = ψ(x)`, mathlib's `Chebyshev.psi`),
  `psiAP_nonneg`, `psiAP_le_psi`, `psiAP_mod` / `psiAP_congr` (dependence on `a mod q` only),
  `sum_psiAP_range` (the classes mod `q` partition `ψ`),
  `psiAP_le` (trivial bound `ψ(x;q,a) ≤ (x/q + 1) log x`),
  `E_one` (`E(x;1) = |ψ(x) − x|`), `E_nonneg`, `le_E`, `E_le_iff`, `E_le` (crude bound).
* `sum_E_le`: the trivial bound `∑_{q ≤ x^θ} E(x;q) ≤ (log 4 + 5) · x^{1+θ}`.
  `E_le_trivial`, `sum_E_le_trivial`: `E(x;q) ≤ (x/q + 1) log x + x/φ(q)` and its sum over `q`
  (left in terms of `∑ 1/q` and `∑ 1/φ(q)`; these are NOT further estimated here).
* `EH.mono`: `EH θ₂ → EH θ₁` for `θ₁ ≤ θ₂`.  `EH_of_neg`: `EH θ` holds trivially for `θ < 0`.
* `EH.psi_sub_self`: `EH θ` with `θ ≥ 0` contains the prime number theorem with error
  `O_A(x / (log x)^A)`.
* `EH_iff_nat`: it suffices to treat natural exponents `A`.
  `EH_iff_large_exponent`: it suffices to treat all `A ≥ A₀`.
* `EH_iff_eventually`: it suffices to treat `x ≥ x₀` (with `x₀` allowed to depend on `A`).
* `elliottHalberstam_iff_seq`: the conjecture is equivalent to `EH (1 - 1/(k+2))` for all `k : ℕ`.
  `elliottHalberstam_iff_frequently`: equivalent to `EH θ` for `θ < 1` arbitrarily close to `1`.

## What is NOT proved here

* The conjecture itself, or `EH θ` for any single `θ ≥ 0` (even `EH 0` requires the prime number
  theorem with a strong error term; `EH θ` for `0 < θ < 1/2` is Bombieri–Vinogradov).
* The falsity of `EH 1` (Friedlander–Granville).
* Any implication to prime gaps.
-/

open Finset Real
open ArithmeticFunction hiding log

namespace ElliottHalberstam

/-! ## Definitions -/

/-- `ψ(x; q, a) = ∑_{0 < n ≤ x, n ≡ a (mod q)} Λ(n)`. -/
noncomputable def psiAP (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]), Λ n

/-- The reduced residues mod `q`, represented in `{0, …, q-1}`.
(For `q = 1` this is `{0}`; for `q = 0` it is empty.) -/
def reducedResidues (q : ℕ) : Finset ℕ := (range q).filter (fun a => a.Coprime q)

lemma reducedResidues_nonempty {q : ℕ} (hq : 1 ≤ q) : (reducedResidues q).Nonempty := by
  rcases hq.eq_or_lt with rfl | h
  · exact ⟨0, by simp [reducedResidues]⟩
  · exact ⟨1, by simp [reducedResidues, h]⟩

/-- The Elliott–Halberstam error term
`E(x; q) = max_{a mod q, (a, q) = 1} |ψ(x; q, a) − x / φ(q)|`.
The maximum is over the finite nonempty set `reducedResidues q` when `q ≥ 1`;
for the junk value `q = 0` (never used) it is `0`. -/
noncomputable def E (x : ℝ) (q : ℕ) : ℝ :=
  if h : (reducedResidues q).Nonempty then
    (reducedResidues q).sup' h (fun a => |psiAP x q a - x / (Nat.totient q : ℝ)|)
  else 0

/-- `EH θ`: the primes have level of distribution `θ` in the Elliott–Halberstam sense, i.e. for
every `A > 0` there is `C` with
`∑_{1 ≤ q ≤ x^θ} E(x; q) ≤ C · x / (log x)^A` for all real `x ≥ 2`. -/
def EH (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ A

/-- **The Elliott–Halberstam conjecture** (open). -/
def ElliottHalberstamConjecture : Prop := ∀ θ : ℝ, 0 < θ → θ < 1 → EH θ

/-! ## Sanity checks on `psiAP` -/

theorem psiAP_nonneg (x : ℝ) (q a : ℕ) : 0 ≤ psiAP x q a :=
  sum_nonneg fun _ _ => vonMangoldt_nonneg

/-- `ψ(x; q, a) ≤ ψ(x)`. -/
theorem psiAP_le_psi (x : ℝ) (q a : ℕ) : psiAP x q a ≤ Chebyshev.psi x :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => vonMangoldt_nonneg

/-- For modulus `1` we recover Chebyshev's `ψ`. -/
theorem psiAP_one (x : ℝ) (a : ℕ) : psiAP x 1 a = Chebyshev.psi x := by
  simp [psiAP, Chebyshev.psi, Nat.modEq_one]

/-- `ψ(x; q, a)` only depends on `a` modulo `q`. -/
theorem psiAP_congr (x : ℝ) {q a b : ℕ} (h : a ≡ b [MOD q]) : psiAP x q a = psiAP x q b := by
  unfold psiAP
  congr 1
  ext n
  simp only [mem_filter, and_congr_right_iff]
  exact fun _ => ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

theorem psiAP_mod (x : ℝ) (q a : ℕ) : psiAP x q (a % q) = psiAP x q a :=
  psiAP_congr x (Nat.mod_modEq a q)

/-- The residue classes mod `q` partition the sum defining `ψ`. -/
theorem sum_psiAP_range (x : ℝ) {q : ℕ} (hq : 0 < q) :
    ∑ a ∈ range q, psiAP x q a = Chebyshev.psi x := by
  unfold psiAP Chebyshev.psi
  rw [← sum_biUnion]
  · congr 1
    ext n
    simp only [mem_biUnion, mem_range, mem_filter]
    constructor
    · rintro ⟨a, -, hn, -⟩; exact hn
    · intro hn; exact ⟨n % q, Nat.mod_lt _ hq, hn, (Nat.mod_modEq n q).symm⟩
  · intro a ha b hb hab
    rw [Function.onFun, disjoint_left]
    intro n hna hnb
    simp only [mem_filter] at hna hnb
    apply hab
    have := (hna.2.symm.trans hnb.2)
    have ha' : a < q := by simpa using ha
    have hb' : b < q := by simpa using hb
    exact Nat.ModEq.eq_of_lt_of_lt this ha' hb'

/-- Number of `n ∈ (0, N]` in a fixed residue class mod `q` is at most `N / q + 1`. -/
lemma card_filter_modEq_le (N q a : ℕ) :
    ((Ioc 0 N).filter (fun n => n ≡ a [MOD q])).card ≤ N / q + 1 := by
  have : ((Ioc 0 N).filter (fun n => n ≡ a [MOD q])).card ≤ (range (N / q + 1)).card := by
    apply card_le_card_of_injOn (fun n => n / q)
    · intro n hn
      simp only [mem_coe, mem_filter, mem_Ioc] at hn
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)
    · intro n hn m hm h
      simp only [mem_coe, mem_filter, mem_Ioc] at hn hm
      have h1 : n % q = m % q := hn.2.trans hm.2.symm
      have h2 : n / q = m / q := h
      rw [← Nat.div_add_mod n q, ← Nat.div_add_mod m q, h1, h2]
  simpa using this

/-- Trivial pointwise bound `ψ(x; q, a) ≤ (x / q + 1) · log x` for `x ≥ 1`, `q ≥ 1`. -/
theorem psiAP_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 0 < q) (a : ℕ) :
    psiAP x q a ≤ (x / q + 1) * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hterm : ∀ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]), Λ n ≤ Real.log x := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    refine vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn.1.1) ?_)
    exact (Nat.cast_le.mpr hn.1.2).trans (Nat.floor_le hx0)
  calc psiAP x q a ≤ ∑ _n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]), Real.log x :=
        sum_le_sum hterm
    _ = ((Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q])).card * Real.log x := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (x / q + 1) * Real.log x := by
        apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hx)
        have h1 := card_filter_modEq_le ⌊x⌋₊ q a
        have h2 : (((Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q])).card : ℝ)
            ≤ ((⌊x⌋₊ / q : ℕ) : ℝ) + 1 := by exact_mod_cast h1
        have h3 : ((⌊x⌋₊ / q : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / q := Nat.cast_div_le
        have h4 : (⌊x⌋₊ : ℝ) / q ≤ x / q :=
          div_le_div_of_nonneg_right (Nat.floor_le hx0) hqR.le
        linarith

/-! ## Basic properties of the error term `E` -/

theorem E_def_of_pos (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    E x q = (reducedResidues q).sup' (reducedResidues_nonempty hq)
      (fun a => |psiAP x q a - x / (Nat.totient q : ℝ)|) := by
  simp [E, reducedResidues_nonempty hq]

theorem E_nonneg (x : ℝ) (q : ℕ) : 0 ≤ E x q := by
  unfold E
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    exact (abs_nonneg _).trans (le_sup' (fun a => |psiAP x q a - x / (Nat.totient q : ℝ)|) ha)
  · exact le_rfl

/-- Characterisation of upper bounds for `E`: it really is the max over reduced residues. -/
theorem E_le_iff (x : ℝ) {q : ℕ} (hq : 1 ≤ q) (B : ℝ) :
    E x q ≤ B ↔ ∀ a, a < q → a.Coprime q → |psiAP x q a - x / (Nat.totient q : ℝ)| ≤ B := by
  rw [E_def_of_pos x hq, sup'_le_iff]
  simp [reducedResidues]

/-- Every reduced residue class (any representative `a : ℕ`, not necessarily `< q`) is bounded
by `E`. -/
theorem le_E (x : ℝ) {q : ℕ} (hq : 1 ≤ q) {a : ℕ} (ha : a.Coprime q) :
    |psiAP x q a - x / (Nat.totient q : ℝ)| ≤ E x q := by
  rw [← psiAP_mod]
  refine (E_le_iff x hq _).mp le_rfl (a % q) (Nat.mod_lt _ hq) ?_
  have h := (Nat.mod_modEq a q).gcd_eq
  exact h.trans ha

/-- The maximum is attained. -/
theorem exists_eq_E (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ a, a < q ∧ a.Coprime q ∧ E x q = |psiAP x q a - x / (Nat.totient q : ℝ)| := by
  obtain ⟨a, ha, h⟩ := exists_mem_eq_sup' (reducedResidues_nonempty hq)
    (fun a => |psiAP x q a - x / (Nat.totient q : ℝ)|)
  simp only [reducedResidues, mem_filter, mem_range] at ha
  exact ⟨a, ha.1, ha.2, by rw [E_def_of_pos x hq, h]⟩

/-- `E(x; 1) = |ψ(x) − x|`. -/
theorem E_one (x : ℝ) : E x 1 = |Chebyshev.psi x - x| := by
  obtain ⟨a, -, -, h⟩ := exists_eq_E x le_rfl
  rw [h, psiAP_one]; simp

/-- Crude bound `E(x; q) ≤ (log 4 + 5) · x` for `x ≥ 0`, via Chebyshev's `ψ(x) ≤ (log 4 + 4) x`. -/
theorem E_le {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 1 ≤ q) : E x q ≤ (Real.log 4 + 5) * x := by
  rw [E_le_iff x hq]
  intro a _ _
  have h1 := psiAP_nonneg x q a
  have h2 : psiAP x q a ≤ (Real.log 4 + 4) * x :=
    (psiAP_le_psi x q a).trans (Chebyshev.psi_le_const_mul_self hx)
  have hφ : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have h3 : 0 ≤ x / (Nat.totient q : ℝ) := by positivity
  have h4 : x / (Nat.totient q : ℝ) ≤ x := div_le_self hx hφ
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith

/-- Sharper trivial bound: `E(x; q) ≤ (x / q + 1) · log x + x / φ(q)` for `x ≥ 1`, `q ≥ 1`. -/
theorem E_le_trivial {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    E x q ≤ (x / q + 1) * Real.log x + x / (Nat.totient q : ℝ) := by
  rw [E_le_iff x hq]
  intro a _ _
  have h1 := psiAP_nonneg x q a
  have h2 := psiAP_le hx hq a
  have h3 : 0 ≤ x / (Nat.totient q : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- Trivial bound on the full sum with explicit harmonic-type sums:
`∑_{q ≤ x^θ} E(x; q) ≤ (x · ∑ 1/q + x^θ) · log x + x · ∑ 1/φ(q)`. -/
theorem sum_E_le_trivial {x : ℝ} (hx : 1 ≤ x) (θ : ℝ) :
    ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤
      (x * ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, (1 : ℝ) / q + x ^ θ) * Real.log x
        + x * ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, (1 : ℝ) / (Nat.totient q : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hfl : (⌊x ^ θ⌋₊ : ℝ) ≤ x ^ θ := Nat.floor_le (Real.rpow_nonneg hx0.le θ)
  calc ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q
      ≤ ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, ((x / q + 1) * Real.log x + x / (Nat.totient q : ℝ)) :=
        sum_le_sum fun q hq => E_le_trivial hx (mem_Icc.mp hq).1
    _ = (x * ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, (1 : ℝ) / q + ⌊x ^ θ⌋₊) * Real.log x
        + x * ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, (1 : ℝ) / (Nat.totient q : ℝ) := by
        rw [sum_add_distrib, ← sum_mul, sum_add_distrib, mul_sum, mul_sum]
        simp [div_eq_mul_inv]
    _ ≤ _ := by gcongr

/-! ## A trivial bound on the full Elliott–Halberstam sum -/

/-- Trivial unconditional bound: `∑_{q ≤ x^θ} E(x; q) ≤ (log 4 + 5) · x^{1+θ}` for `x ≥ 1`. -/
theorem sum_E_le {x : ℝ} (hx : 1 ≤ x) (θ : ℝ) :
    ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ (Real.log 4 + 5) * x ^ (1 + θ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ ∑ _q ∈ Icc 1 ⌊x ^ θ⌋₊, (Real.log 4 + 5) * x :=
        sum_le_sum fun q hq => E_le hx0.le (mem_Icc.mp hq).1
    _ = (⌊x ^ θ⌋₊ : ℝ) * ((Real.log 4 + 5) * x) := by simp
    _ ≤ x ^ θ * ((Real.log 4 + 5) * x) := by
        gcongr
        exact Nat.floor_le (Real.rpow_nonneg hx0.le θ)
    _ = (Real.log 4 + 5) * x ^ (1 + θ) := by
        rw [Real.rpow_add hx0, Real.rpow_one]; ring

theorem sum_E_nonneg (x θ : ℝ) : 0 ≤ ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q :=
  sum_nonneg fun q _ => E_nonneg x q

/-! ## Monotonicity in the level `θ` -/

lemma sum_E_mono {x : ℝ} (hx : 1 ≤ x) {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) :
    ∑ q ∈ Icc 1 ⌊x ^ θ₁⌋₊, E x q ≤ ∑ q ∈ Icc 1 ⌊x ^ θ₂⌋₊, E x q := by
  apply sum_le_sum_of_subset_of_nonneg
  · apply Icc_subset_Icc_right
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx h)
  · exact fun q _ _ => E_nonneg x q

/-- A larger level of distribution implies a smaller one. -/
theorem EH.mono {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) (H : EH θ₂) : EH θ₁ := by
  intro A hA
  obtain ⟨C, hC⟩ := H A hA
  exact ⟨C, fun x hx => (sum_E_mono (by linarith) h).trans (hC x hx)⟩

/-- For negative `θ` the range of moduli is empty and `EH θ` is vacuous. -/
theorem EH_of_neg {θ : ℝ} (hθ : θ < 0) : EH θ := by
  intro A _
  refine ⟨0, fun x hx => ?_⟩
  have h1 : x ^ θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hθ
  have h2 : ⌊x ^ θ⌋₊ = 0 := Nat.floor_eq_zero.mpr h1
  simp [h2]

/-- `EH θ` for any `θ ≥ 0` contains the prime number theorem with error term
`ψ(x) − x = O_A(x / (log x)^A)` (the `q = 1` term of the sum). -/
theorem EH.psi_sub_self {θ : ℝ} (hθ : 0 ≤ θ) (H : EH θ) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨C, hC⟩ := H A hA
  refine ⟨C, fun x hx => le_trans ?_ (hC x hx)⟩
  rw [← E_one]
  have h1 : (1 : ℝ) ≤ x ^ θ := Real.one_le_rpow (by linarith) hθ
  have hmem : 1 ∈ Icc 1 ⌊x ^ θ⌋₊ := mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by simpa using h1)⟩
  exact single_le_sum (f := fun q => E x q) (fun q _ => E_nonneg x q) hmem

/-! ## Reductions in the exponent `A` -/

/-- Comparison of log-power savings: for `x ≥ 2` and `A ≤ A'`,
`x / (log x)^{A'} ≤ (log 2)^{-(A' - A)} · x / (log x)^A`. -/
lemma div_log_rpow_le {x : ℝ} (hx : 2 ≤ x) {A A' : ℝ} (h : A ≤ A') :
    x / (Real.log x) ^ A' ≤ (Real.log 2) ^ (-(A' - A)) * (x / (Real.log x) ^ A) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx : 0 < Real.log x := hl2.trans_le hl
  have key : (Real.log x) ^ (-(A' - A)) ≤ (Real.log 2) ^ (-(A' - A)) :=
    Real.rpow_le_rpow_of_nonpos hl2 hl (by linarith)
  have e : x / (Real.log x) ^ A' = (Real.log x) ^ (-(A' - A)) * (x / (Real.log x) ^ A) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hlx.le, ← Real.rpow_neg hlx.le,
      mul_left_comm, ← Real.rpow_add hlx]
    congr 2; ring
  rw [e]
  have : 0 ≤ x / (Real.log x) ^ A := by positivity
  exact mul_le_mul_of_nonneg_right key this

/-- The bound for an exponent `A'` implies the bound for every smaller exponent `A`. -/
lemma bound_of_larger_exponent {θ A A' : ℝ} (h : A ≤ A')
    (H : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ A') :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨C, hC⟩ := H
  refine ⟨|C| * (Real.log 2) ^ (-(A' - A)), fun x hx => ?_⟩
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hpos : 0 ≤ x / (Real.log x) ^ A' := by positivity
  calc ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ A' := hC x hx
    _ = C * (x / (Real.log x) ^ A') := by ring
    _ ≤ |C| * (x / (Real.log x) ^ A') := mul_le_mul_of_nonneg_right (le_abs_self C) hpos
    _ ≤ |C| * ((Real.log 2) ^ (-(A' - A)) * (x / (Real.log x) ^ A)) :=
        mul_le_mul_of_nonneg_left (div_log_rpow_le hx h) (abs_nonneg C)
    _ = |C| * (Real.log 2) ^ (-(A' - A)) * x / (Real.log x) ^ A := by ring

/-- It suffices to prove the Elliott–Halberstam bound for all `A ≥ A₀`. -/
theorem EH_iff_large_exponent (θ A₀ : ℝ) :
    EH θ ↔ ∀ A : ℝ, 0 < A → A₀ ≤ A → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ A := by
  refine ⟨fun H A hA _ => H A hA, fun H A hA => ?_⟩
  exact bound_of_larger_exponent (le_max_left A A₀)
    (H (max A A₀) (hA.trans_le (le_max_left _ _)) (le_max_right _ _))

/-- It suffices to prove the Elliott–Halberstam bound for natural-number exponents
(with the ordinary monoid power `(log x) ^ k`). -/
theorem EH_iff_nat (θ : ℝ) :
    EH θ ↔ ∀ k : ℕ, ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ k := by
  constructor
  · intro H k
    obtain ⟨C, hC⟩ := H (k + 1) (by positivity)
    have := bound_of_larger_exponent (θ := θ) (A := (k : ℝ)) (A' := (k : ℝ) + 1) (by linarith)
      ⟨C, hC⟩
    simpa [Real.rpow_natCast] using this
  · intro H A hA
    obtain ⟨k, hk⟩ := exists_nat_ge A
    obtain ⟨C, hC⟩ := H k
    exact bound_of_larger_exponent hk ⟨C, by simpa [Real.rpow_natCast] using hC⟩

/-! ## Reduction to large `x` -/

/-- It suffices to prove the Elliott–Halberstam bound for all sufficiently large `x`
(the threshold `x₀` may depend on `A`).  The range `2 ≤ x ≤ x₀` is absorbed into the constant
using the trivial bound `sum_E_le`. -/
theorem EH_iff_eventually (θ : ℝ) :
    EH θ ↔ ∀ A : ℝ, 0 < A → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 2 ≤ x →
      ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ A := by
  constructor
  · intro H A hA
    obtain ⟨C, hC⟩ := H A hA
    exact ⟨C, 2, fun x _ hx => hC x hx⟩
  · intro H A hA
    obtain ⟨C, x₀, hC⟩ := H A hA
    -- constant handling the compact range `2 ≤ x ≤ x₀`
    set X : ℝ := max x₀ 2 with hX
    have hX2 : 2 ≤ X := le_max_right _ _
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    set K : ℝ := (Real.log 4 + 5) * X ^ (1 + |θ|) * (Real.log X) ^ A with hK
    have hK0 : 0 ≤ K := by
      have : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
      positivity
    refine ⟨max C K, fun x hx => ?_⟩
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hden : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlx A
    have hfrac : 0 ≤ x / (Real.log x) ^ A := by positivity
    by_cases hxx : x₀ ≤ x
    · calc ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ C * x / (Real.log x) ^ A := hC x hxx hx
        _ = C * (x / (Real.log x) ^ A) := by ring
        _ ≤ max C K * (x / (Real.log x) ^ A) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hfrac
        _ = max C K * x / (Real.log x) ^ A := by ring
    · have hxX : x ≤ X := (le_of_not_ge hxx).trans (le_max_left _ _)
      have h1 : ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ (Real.log 4 + 5) * X ^ (1 + |θ|) := by
        refine (sum_E_le (by linarith) θ).trans ?_
        have hxa : x ^ (1 + θ) ≤ x ^ (1 + |θ|) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [le_abs_self θ])
        have hxb : x ^ (1 + |θ|) ≤ X ^ (1 + |θ|) :=
          Real.rpow_le_rpow (by linarith) hxX (by positivity)
        have : 0 ≤ Real.log 4 + 5 := by linarith
        exact mul_le_mul_of_nonneg_left (hxa.trans hxb) this
      have h2 : (Real.log x) ^ A ≤ (Real.log X) ^ A :=
        Real.rpow_le_rpow hlx.le (Real.log_le_log (by linarith) hxX) hA.le
      have h3 : (Real.log 4 + 5) * X ^ (1 + |θ|) ≤ K * x / (Real.log x) ^ A := by
        rw [le_div_iff₀ hden]
        have hc : 0 ≤ (Real.log 4 + 5) * X ^ (1 + |θ|) := by positivity
        calc (Real.log 4 + 5) * X ^ (1 + |θ|) * (Real.log x) ^ A
            ≤ (Real.log 4 + 5) * X ^ (1 + |θ|) * (Real.log X) ^ A :=
              mul_le_mul_of_nonneg_left h2 hc
          _ = K := rfl
          _ ≤ K * x := by nlinarith
      calc ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, E x q ≤ K * x / (Real.log x) ^ A := h1.trans h3
        _ = K * (x / (Real.log x) ^ A) := by ring
        _ ≤ max C K * (x / (Real.log x) ^ A) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hfrac
        _ = max C K * x / (Real.log x) ^ A := by ring

/-! ## Reductions of the full conjecture -/

/-- The conjecture is equivalent to `EH θ` for levels `θ < 1` arbitrarily close to `1`. -/
theorem elliottHalberstam_iff_frequently :
    ElliottHalberstamConjecture ↔ ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 1 - ε < θ ∧ θ < 1 ∧ EH θ := by
  constructor
  · intro H ε hε
    refine ⟨1 - min ε 1 / 2, ?_, ?_, H _ ?_ ?_⟩ <;>
      have := min_le_left ε 1 <;> have := min_le_right ε 1 <;>
      have : 0 < min ε 1 := lt_min hε one_pos <;> linarith
  · intro H θ _ hθ1
    obtain ⟨θ', h1, -, h3⟩ := H (1 - θ) (by linarith)
    exact h3.mono (by linarith)

/-- The conjecture is equivalent to `EH (1 - 1/(k+2))` for every natural number `k`
(levels `1/2, 2/3, 3/4, …`). -/
theorem elliottHalberstam_iff_seq :
    ElliottHalberstamConjecture ↔ ∀ k : ℕ, EH (1 - 1 / ((k : ℝ) + 2)) := by
  constructor
  · intro H k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have h1 : 1 / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one hk]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact H _ (by linarith) (by linarith [one_div_pos.mpr hk])
  · intro H θ _ hθ1
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - θ))
    refine (H k).mono ?_
    have h1 : (0 : ℝ) < 1 - θ := by linarith
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : 1 / ((k : ℝ) + 2) ≤ 1 - θ := by
      rw [div_le_iff₀ hk2]
      have := (div_lt_iff₀ h1).mp hk
      nlinarith
    linarith

/-- In particular the conjecture is equivalent to its restriction to `θ ∈ [1/2, 1)`; the range
`θ < 1/2` (Bombieri–Vinogradov, not proved here) is *implied by* but does not help with the rest. -/
theorem elliottHalberstam_iff_ge_half :
    ElliottHalberstamConjecture ↔ ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 → EH θ := by
  constructor
  · exact fun H θ h1 h2 => H θ (by linarith) h2
  · intro H θ _ hθ1
    exact (H (max θ (1 / 2)) (le_max_right _ _) (max_lt hθ1 (by norm_num))).mono (le_max_left _ _)

end ElliottHalberstam

section AxiomAudit
open ElliottHalberstam
#print axioms psiAP_one
#print axioms psiAP_le_psi
#print axioms sum_psiAP_range
#print axioms psiAP_le
#print axioms E_le_iff
#print axioms le_E
#print axioms E_one
#print axioms E_le
#print axioms sum_E_le
#print axioms E_le_trivial
#print axioms sum_E_le_trivial
#print axioms EH.mono
#print axioms EH_of_neg
#print axioms EH.psi_sub_self
#print axioms EH_iff_large_exponent
#print axioms EH_iff_nat
#print axioms EH_iff_eventually
#print axioms elliottHalberstam_iff_frequently
#print axioms elliottHalberstam_iff_seq
#print axioms elliottHalberstam_iff_ge_half
end AxiomAudit
