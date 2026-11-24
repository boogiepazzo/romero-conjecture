import Mathlib

/-!
# Legendre's conjecture (primes between consecutive squares)

**STATUS: IN PROGRESS / NOT YET SOLVED.**  Legendre's conjecture is an open problem.  This file
does **not** prove it.  It contains a faithful formal statement, equivalent reformulations,
implications from/to neighbouring (also open) conjectures, and a finite kernel-checked
verification.  Nothing here is progress towards the general statement.

## Statement

> For every integer `n ≥ 1` there is a prime `p` with `n² < p < (n+1)²`.

Formalized as `Legendre.LegendreConjecture`.

## Attribution, dating and status (literature check, November 2026; uncertainty preserved)

* The conjecture is universally attributed to A.-M. Legendre.  Wikipedia cites Legendre's
  *Essai sur la théorie des nombres* (2nd ed., 1808, pp. 405–406); other secondary sources cite
  the 1798 first edition or give other dates.  We did **not** consult the primary source and could
  not confirm that the statement appears there in this exact form; an early explicit discussion
  under Legendre's name is A. Desboves, *Nouv. Ann. Math.* 14 (1855) 281–295 ("Sur un théorème de
  Legendre et son application à la recherche de limites qui comprennent entre elles des nombres
  premiers").  The exact origin should be regarded as uncertain here.
* E. Landau listed it at the 1912 ICM (Cambridge) as one of four problems "unattackable at the
  present state of science" (with Goldbach, twin primes, and primes of the form `n² + 1`).
* As of late 2026 it is, to our knowledge, still open (e.g. Chamberland–Straub, *Weakening the
  Legendre conjecture*, arXiv:2602.22502, Feb 2026, treats it as open).  Papers claiming proofs
  appear periodically on preprint servers (e.g. arXiv:1211.6046, arXiv:1908.08995); we found no
  evidence that any has been accepted by the community.
* Best known results (none formalized here):
  - Ingham (1937): `p_{n+1} - p_n ≪ p_n^{5/8+ε}`, hence a prime between consecutive **cubes** for
    all large `n`.
  - Baker–Harman–Pintz (2001): a prime in `[x - x^{0.525}, x]` for all large `x`.  Legendre needs
    (roughly) exponent `1/2`.
  - Chen Jingrun (1975, Sci. Sinica 18): for all large `n` there is a number with at most two
    prime factors between `n²` and `(n+1)²` (as reported by secondary sources; primary source
    not consulted).
  - Under RH, Cramér (1920): `p_{n+1} - p_n = O(√p_n log p_n)` — still not enough.
  - Unconditional explicit results for higher powers: Dudek (2016), Mattner, Cully-Hugill (2023),
    Cully-Hugill–Johnston (primes between consecutive `m`-th powers for explicit `m`, reported as
    `m = 155`, later `90`).
* Numerical verification in the literature: Sorenson–Webster (*Res. Number Theory* 2025;
  arXiv:2401.13753, whose v1 title has `3.33·10¹³`) report verification for all
  `n ≤ 7.05·10¹³`.  Tables of maximal prime gaps below `2⁶⁴` independently cover `n ≲ 4·10⁹`.

## What is proved in this file (all machine-checked, no `sorry`, no extra axioms)

* Sanity: `consecutivePrimes_nth` (the predicate `ConsecutivePrimes` agrees with mathlib's
  enumeration `Nat.nth Nat.Prime`).
* Reformulations: `legendre_iff_theta`, `legendre_iff_theta_pred` (Chebyshev `θ`),
  `legendre_iff_primeCounting` (`π`), `legendre_iff_psi` (`ψ`, with the exact prime-power
  correction).  General lemmas `theta_lt_theta_iff`, `psi_lt_psi_iff`, `primeCounting_lt_iff`.
* `ψ` relations: `psi_increment_closed`, `psi_increment_open`
  (`ψ((n+1)²) - ψ(n²) = ∑_{n² < m ≤ (n+1)²} Λ(m)` and the open-interval version),
  `psi_increment_eq` (= `θ`-increment + `primePowerCorrection`), `LegendreConjecture.psi_lt`.
* Prime-power correction: `exists_odd_pow_of_mem` (a proper prime power strictly between
  consecutive squares is an odd power `p^k`, `k ≥ 3`), `card_properPowers_le` (at most one per
  prime `p` with `p³ < (n+1)²`), `primePowerCorrection_le`, and the honest converse
  `exists_prime_of_psi_increment_gt`.  `primePowerCorrection_five_pos` shows the correction is
  really there (`27, 32 ∈ (25, 36)`).
* Implications among **open** conjectures (conditional results only):
  `oppermann_implies_legendre`, `andrica_implies_legendre`, `andrica_iff_gap`,
  `LegendreConjecture.gap_le` / `gap_le_real` (Legendre ⇒ `q - p ≤ 4√p + 1` for consecutive
  primes), `legendre_at_of_cramerGapBound` / `eventually_legendre_of_cramerGapBound`
  (a Cramér-type bound `q - p ≤ C (log p)²` ⇒ Legendre for all `n ≥ max(2, 1024 C²)`),
  `LegendreConjecture.le_primeCounting` (Legendre ⇒ `π((n+1)²) ≥ n + 1`).
* **Numerical evidence only**: `legendre_upTo_bound`, Legendre's statement for
  `1 ≤ n ≤ legendreBound = 1000`, by `decide +kernel` on a verified trial-division checker
  (no `native_decide`).  This is a negligible fraction of the published range.

## What is NOT proved (stated only, as `def … : Prop`)

* `LegendreConjecture` itself (open).
* `OppermannConjecture`, `AndricaConjecture`, `BrocardConjecture` (all open), and
  `CramerGapBound C` (open for every `C`).
* None of the analytic theorems quoted above (Ingham, Baker–Harman–Pintz, Chen, …).
* Legendre ⇒ Brocard and Legendre ⇒ Andrica/Oppermann are **not** known and not claimed.
-/

open Finset ArithmeticFunction Chebyshev

namespace Legendre

/-! ## Statements -/

/-- **Legendre's conjecture** (OPEN): for every `n ≥ 1` there is a prime `p` with
`n² < p < (n+1)²`. -/
def LegendreConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- **Oppermann's conjecture** (OPEN, 1877): for every `n ≥ 2` there is a prime in
`(n(n-1), n²)` and a prime in `(n², n(n+1))`. -/
def OppermannConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
    (∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < n * (n + 1))

/-- `p < q` are consecutive primes: both prime and no prime strictly between them. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

/-- **Andrica's conjecture** (OPEN, 1985): `√q - √p < 1` for consecutive primes `p < q`. -/
def AndricaConjecture : Prop :=
  ∀ p q : ℕ, ConsecutivePrimes p q → √(q : ℝ) - √(p : ℝ) < 1

/-- **Brocard's conjecture** (OPEN, 1904): for consecutive primes `3 ≤ p < q` there are at least
four primes strictly between `p²` and `q²`. -/
def BrocardConjecture : Prop :=
  ∀ p q : ℕ, ConsecutivePrimes p q → 3 ≤ p → 4 ≤ ((Ioo (p ^ 2) (q ^ 2)).filter Nat.Prime).card

/-- A **Cramér-type gap hypothesis** with explicit constant `C` (OPEN for every `C`):
`q - p ≤ C (log p)²` for all consecutive primes `p < q`. -/
def CramerGapBound (C : ℝ) : Prop :=
  ∀ p q : ℕ, ConsecutivePrimes p q → (q : ℝ) - p ≤ C * Real.log p ^ 2

/-! ## Consecutive primes: basic facts -/

/-- Sanity check of `ConsecutivePrimes` against mathlib's enumeration of the primes. -/
theorem consecutivePrimes_nth (k : ℕ) :
    ConsecutivePrimes (Nat.nth Nat.Prime k) (Nat.nth Nat.Prime (k + 1)) := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  refine ⟨Nat.prime_nth_prime k, Nat.prime_nth_prime (k + 1), hmono (Nat.lt_succ_self k),
    fun r h1 h2 hr => ?_⟩
  have e : Nat.nth Nat.Prime (Nat.count Nat.Prime r) = r := Nat.nth_count hr
  rw [← e] at h1 h2
  have a1 := hmono.lt_iff_lt.1 h1
  have a2 := hmono.lt_iff_lt.1 h2
  omega

/-- Every prime has a next prime. -/
theorem exists_consecutivePrimes_right {p : ℕ} (hp : p.Prime) : ∃ q, ConsecutivePrimes p q := by
  have h : ∃ q, p < q ∧ q.Prime := by
    obtain ⟨q, hq, hq'⟩ := Nat.exists_infinite_primes (p + 1)
    exact ⟨q, by omega, hq'⟩
  exact ⟨Nat.find h, hp, (Nat.find_spec h).2, (Nat.find_spec h).1,
    fun r hr hrq hrp => Nat.find_min h hrq ⟨hr, hrp⟩⟩

/-- A prime-free open interval `(a, b)` with `a ≥ 2` is spanned by a pair of consecutive primes
`p ≤ a`, `b ≤ q`. -/
theorem exists_consecutivePrimes_spanning {a b : ℕ} (ha : 2 ≤ a)
    (h : ∀ r : ℕ, a < r → r < b → ¬ r.Prime) :
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ p ≤ a ∧ b ≤ q := by
  have hp : (Nat.findGreatest Nat.Prime a).Prime := Nat.findGreatest_spec ha Nat.prime_two
  obtain ⟨q, hq⟩ := exists_consecutivePrimes_right hp
  refine ⟨_, q, hq, Nat.findGreatest_le a, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  rcases le_or_gt q a with hqa | hqa
  · exact Nat.findGreatest_is_greatest hq.2.2.1 hqa hq.2.1
  · exact h q hqa hlt hq.2.1

/-! ## Implications between the conjectures -/

/-- Oppermann's conjecture implies Legendre's conjecture. -/
theorem oppermann_implies_legendre (h : OppermannConjecture) : LegendreConjecture := by
  intro n hn
  obtain ⟨⟨p, hp, h1, h2⟩, -⟩ := h (n + 1) (by omega)
  refine ⟨p, hp, ?_, h2⟩
  have : n ^ 2 ≤ (n + 1) * (n + 1 - 1) := by
    rw [Nat.add_sub_cancel]; nlinarith
  omega

/-- Andrica's conjecture implies Legendre's conjecture. -/
theorem andrica_implies_legendre (h : AndricaConjecture) : LegendreConjecture := by
  intro n hn
  by_contra hno
  push Not at hno
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · have := hno 2 Nat.prime_two (by norm_num)
    norm_num at this
  have ha : 2 ≤ n ^ 2 := by nlinarith
  obtain ⟨p, q, hpq, hpa, hbq⟩ := exists_consecutivePrimes_spanning (b := (n + 1) ^ 2) ha
    (fun r h1 h2 hr => absurd (hno r hr h1) (not_le.2 h2))
  have hA := h p q hpq
  have h1 : √(p : ℝ) ≤ n := by
    have : √(p : ℝ) ≤ √((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by exact_mod_cast hpa)
    rwa [Real.sqrt_sq (Nat.cast_nonneg n)] at this
  have h2 : (n : ℝ) + 1 ≤ √(q : ℝ) := by
    have : √(((n : ℝ) + 1) ^ 2) ≤ √(q : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hbq)
    rwa [Real.sqrt_sq (by positivity)] at this
  linarith

/-- Andrica's conjecture is equivalent to the gap bound `q - p < 2√p + 1` for consecutive
primes. -/
theorem andrica_iff_gap :
    AndricaConjecture ↔
      ∀ p q : ℕ, ConsecutivePrimes p q → (q : ℝ) - p < 2 * √(p : ℝ) + 1 := by
  have key : ∀ p q : ℕ, (√(q : ℝ) - √(p : ℝ) < 1 ↔ (q : ℝ) - p < 2 * √(p : ℝ) + 1) := by
    intro p q
    have hp : √(p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
    have hq : √(q : ℝ) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
    have hp0 := Real.sqrt_nonneg (p : ℝ)
    have hq0 := Real.sqrt_nonneg (q : ℝ)
    constructor
    · intro h; nlinarith
    · intro h
      by_contra hc
      rw [not_lt] at hc
      nlinarith
  exact forall_congr' fun p => forall_congr' fun q => imp_congr_right fun _ => key p q

/-- **Legendre ⇒ `O(√p)` prime gaps** (natural-number form): if Legendre's conjecture holds, then
consecutive primes `p < q` satisfy `q - p ≤ 4 ⌊√p⌋ + 1`. -/
theorem LegendreConjecture.gap_le (h : LegendreConjecture) {p q : ℕ}
    (hpq : ConsecutivePrimes p q) : q - p ≤ 4 * Nat.sqrt p + 1 := by
  obtain ⟨hp, hq, -, hbetween⟩ := hpq
  generalize hn : Nat.sqrt p = n
  have h1 : n * n ≤ p := hn ▸ Nat.sqrt_le p
  have h2 : p < (n + 1) * (n + 1) := hn ▸ Nat.lt_succ_sqrt p
  have hp2 := hp.two_le
  have hn1 : 1 ≤ n := by
    by_contra hc
    have : n = 0 := by omega
    subst this
    omega
  have hpne : p ≠ n * n := by
    intro e
    rcases (Nat.dvd_prime hp).1 ⟨n, e⟩ with h' | h'
    · subst h'; omega
    · subst h'; nlinarith
  obtain ⟨r, hr, hr1, hr2⟩ := h (n + 1) (by omega)
  have hqr : q ≤ r := by
    by_contra hc
    exact hbetween r (by nlinarith) (by omega) hr
  have hqne : q ≠ (n + 1) * (n + 3) := by
    intro e
    exact Nat.not_prime_mul (by omega) (by omega) (e ▸ hq)
  have e1 : (n + 1 + 1) ^ 2 = n * n + 4 * n + 4 := by ring
  have e2 : (n + 1) * (n + 3) = n * n + 4 * n + 3 := by ring
  omega

/-- **Legendre ⇒ `O(√p)` prime gaps** (real form): `q - p ≤ 4√p + 1` for consecutive primes. -/
theorem LegendreConjecture.gap_le_real (h : LegendreConjecture) {p q : ℕ}
    (hpq : ConsecutivePrimes p q) : (q : ℝ) - p ≤ 4 * √(p : ℝ) + 1 := by
  have h1 := h.gap_le hpq
  have h2 : (Nat.sqrt p : ℝ) ≤ √(p : ℝ) := Real.nat_sqrt_le_real_sqrt
  have h3 : (q : ℝ) ≤ p + (4 * Nat.sqrt p + 1 : ℕ) := by
    exact_mod_cast (by omega : q ≤ p + (4 * Nat.sqrt p + 1))
  push_cast at h3
  linarith

/-! ## A Cramér-type hypothesis implies Legendre for large `n` -/

/-- Elementary bound `(log x)² ≤ 16 √x` for `x ≥ 1`. -/
theorem log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 16 * √x := by
  have hs1 : 1 ≤ √(√x) := Real.one_le_sqrt.2 (Real.one_le_sqrt.2 hx)
  have h1 : Real.log x = 4 * Real.log (√(√x)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt (by linarith)]; ring
  have h2 : Real.log (√(√x)) ≤ √(√x) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h3 : 0 ≤ Real.log (√(√x)) := Real.log_nonneg hs1
  have h4 : √(√x) ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg x)
  rw [h1]
  nlinarith

/-- Explicit form: under `CramerGapBound C`, Legendre's statement holds at every `n ≥ 2` with
`32 C ≤ √n` (i.e. `n ≥ 1024 C²`). -/
theorem legendre_at_of_cramerGapBound {C : ℝ} (hC : CramerGapBound C) {n : ℕ} (hn : 2 ≤ n)
    (hlarge : 32 * C ≤ √(n : ℝ)) : ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  by_contra hno
  push Not at hno
  have ha : 2 ≤ n ^ 2 := by nlinarith
  obtain ⟨p, q, hpq, hpa, hbq⟩ := exists_consecutivePrimes_spanning (b := (n + 1) ^ 2) ha
    (fun r h1 h2 hr => absurd (hno r hr h1) (not_le.2 h2))
  have hgap := hC p q hpq
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpq.1.two_le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hp' : (p : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hpa
  have hq' : ((n : ℝ) + 1) ^ 2 ≤ q := by exact_mod_cast hbq
  have hlogp : Real.log p ≤ 2 * Real.log n := by
    have := Real.log_le_log (by linarith) hp'
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hsq : Real.log p ^ 2 ≤ 4 * Real.log n ^ 2 := by nlinarith
  have hlog := log_sq_le hn1
  have hs : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  rcases le_or_gt C 0 with hC0 | hC0
  · have : C * Real.log p ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (sq_nonneg _)
    nlinarith
  · have h5 : C * Real.log p ^ 2 ≤ C * (64 * √(n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0.le
    have h6 : 64 * C * √(n : ℝ) ≤ 2 * n := by nlinarith
    nlinarith

/-- A Cramér-type gap bound (with any constant) implies Legendre's statement for all sufficiently
large `n`.  (The hypothesis is open; this is a conditional result.) -/
theorem eventually_legendre_of_cramerGapBound (h : ∃ C : ℝ, CramerGapBound C) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max 2 ⌈(32 * C) ^ 2⌉₊, fun n hn => ?_⟩
  refine legendre_at_of_cramerGapBound hC (le_trans (le_max_left _ _) hn) ?_
  have h1 : (32 * C) ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  calc 32 * C ≤ |32 * C| := le_abs_self _
    _ = √((32 * C) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt h1

/-! ## Prime counting -/

theorem primeCounting_lt_of_prime {a b p : ℕ} (hp : p.Prime) (hap : a < p) (hpb : p ≤ b) :
    Nat.primeCounting a < Nat.primeCounting b := by
  simp only [Nat.primeCounting, Nat.primeCounting']
  calc Nat.count Nat.Prime (a + 1) ≤ Nat.count Nat.Prime p := Nat.count_monotone _ (by omega)
    _ < Nat.count Nat.Prime (p + 1) := Nat.count_strict_mono hp (Nat.lt_succ_self p)
    _ ≤ Nat.count Nat.Prime (b + 1) := Nat.count_monotone _ (by omega)

/-- `π a < π b` iff there is a prime in `(a, b]`. -/
theorem primeCounting_lt_iff {a b : ℕ} :
    Nat.primeCounting a < Nat.primeCounting b ↔ ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    refine absurd h (not_lt.2 ?_)
    simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    refine card_le_card fun p hp => ?_
    rw [mem_filter, mem_range] at hp ⊢
    refine ⟨?_, hp.2⟩
    by_contra hc
    have := hno p hp.2 (by omega)
    omega
  · rintro ⟨p, hp, h1, h2⟩
    exact primeCounting_lt_of_prime hp h1 h2

/-- Legendre's conjecture in terms of the prime counting function. -/
theorem legendre_iff_primeCounting :
    LegendreConjecture ↔
      ∀ n : ℕ, 1 ≤ n → Nat.primeCounting (n ^ 2) < Nat.primeCounting ((n + 1) ^ 2) := by
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  rw [primeCounting_lt_iff]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, h1, h2.le⟩
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, h1, lt_of_le_of_ne h2 ?_⟩
    rintro rfl
    exact Nat.Prime.not_prime_pow (le_refl 2) hp

/-- Legendre's conjecture implies `π((n+1)²) ≥ n + 1` for `n ≥ 1`. -/
theorem LegendreConjecture.le_primeCounting (h : LegendreConjecture) {n : ℕ} (hn : 1 ≤ n) :
    n + 1 ≤ Nat.primeCounting ((n + 1) ^ 2) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have := (legendre_iff_primeCounting.1 h) (m + 1) (by omega)
    omega

/-! ## Chebyshev `θ` reformulation -/

theorem theta_sub_theta {a b : ℕ} (hab : a ≤ b) :
    θ (b : ℝ) - θ (a : ℝ) = ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p := by
  simp only [Chebyshev.theta, Nat.floor_natCast, sum_filter]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

theorem psi_sub_psi {a b : ℕ} (hab : a ≤ b) :
    ψ (b : ℝ) - ψ (a : ℝ) = ∑ m ∈ Ioc a b, Λ m := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

/-- `θ(a) < θ(b)` iff there is a prime in `(a, b]`. -/
theorem theta_lt_theta_iff {a b : ℕ} (hab : a ≤ b) :
    θ (a : ℝ) < θ (b : ℝ) ↔ ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  rw [← sub_pos, theta_sub_theta hab, sum_pos_iff_of_nonneg (fun p hp =>
    Real.log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_lt.le))]
  constructor
  · rintro ⟨p, hp, -⟩
    rw [mem_filter, mem_Ioc] at hp
    exact ⟨p, hp.2, hp.1.1, hp.1.2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, mem_filter.2 ⟨mem_Ioc.2 ⟨h1, h2⟩, hp⟩,
      Real.log_pos (by exact_mod_cast hp.one_lt)⟩

/-- `ψ(a) < ψ(b)` iff there is a prime **power** in `(a, b]`. -/
theorem psi_lt_psi_iff {a b : ℕ} (hab : a ≤ b) :
    ψ (a : ℝ) < ψ (b : ℝ) ↔ ∃ m : ℕ, IsPrimePow m ∧ a < m ∧ m ≤ b := by
  rw [← sub_pos, psi_sub_psi hab, sum_pos_iff_of_nonneg (fun _ _ => vonMangoldt_nonneg)]
  constructor
  · rintro ⟨m, hm, hpos⟩
    rw [mem_Ioc] at hm
    exact ⟨m, vonMangoldt_pos_iff.1 hpos, hm.1, hm.2⟩
  · rintro ⟨m, hm, h1, h2⟩
    exact ⟨m, mem_Ioc.2 ⟨h1, h2⟩, vonMangoldt_pos_iff.2 hm⟩

theorem Ioc_pred_eq_Ioo (n : ℕ) :
    Ioc (n ^ 2) ((n + 1) ^ 2 - 1) = Ioo (n ^ 2) ((n + 1) ^ 2) := by
  ext m
  simp only [mem_Ioc, mem_Ioo]
  have : 0 < (n + 1) ^ 2 := by positivity
  omega

theorem sq_le_succ_sq_pred (n : ℕ) : n ^ 2 ≤ (n + 1) ^ 2 - 1 := by
  have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  omega

/-- **`θ` reformulation.** Legendre's conjecture is equivalent to
`θ(n²) < θ((n+1)² - 1)` for all `n ≥ 1`. -/
theorem legendre_iff_theta_pred :
    LegendreConjecture ↔
      ∀ n : ℕ, 1 ≤ n → θ ((n ^ 2 : ℕ) : ℝ) < θ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) := by
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  rw [theta_lt_theta_iff (sq_le_succ_sq_pred n)]
  have : 0 < (n + 1) ^ 2 := by positivity
  exact exists_congr fun p => by
    constructor
    · rintro ⟨hp, h1, h2⟩; exact ⟨hp, h1, by omega⟩
    · rintro ⟨hp, h1, h2⟩; exact ⟨hp, h1, by omega⟩

/-- **`θ` reformulation** (since `(n+1)²` is not prime, the right endpoint may be included):
Legendre's conjecture is equivalent to `θ(n²) < θ((n+1)²)` for all `n ≥ 1`. -/
theorem legendre_iff_theta :
    LegendreConjecture ↔ ∀ n : ℕ, 1 ≤ n → θ ((n : ℝ) ^ 2) < θ (((n : ℝ) + 1) ^ 2) := by
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  have e1 : (n : ℝ) ^ 2 = ((n ^ 2 : ℕ) : ℝ) := by push_cast; ring
  have e2 : ((n : ℝ) + 1) ^ 2 = (((n + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [e1, e2, theta_lt_theta_iff (Nat.pow_le_pow_left (Nat.le_succ n) 2)]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, h1, h2.le⟩
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, h1, lt_of_le_of_ne h2 ?_⟩
    rintro rfl
    exact Nat.Prime.not_prime_pow (le_refl 2) hp

/-! ## von Mangoldt / `ψ` formulation and the prime-power correction -/

/-- The exact `ψ`-increment over the half-open interval `(n², (n+1)²]`. -/
theorem psi_increment_closed (n : ℕ) :
    ψ (((n : ℝ) + 1) ^ 2) - ψ ((n : ℝ) ^ 2) = ∑ m ∈ Ioc (n ^ 2) ((n + 1) ^ 2), Λ m := by
  have e1 : (n : ℝ) ^ 2 = ((n ^ 2 : ℕ) : ℝ) := by push_cast; ring
  have e2 : ((n : ℝ) + 1) ^ 2 = (((n + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [e1, e2, psi_sub_psi (Nat.pow_le_pow_left (Nat.le_succ n) 2)]

/-- The exact `ψ`-increment over the open interval `(n², (n+1)²)`. -/
theorem psi_increment_open (n : ℕ) :
    ψ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) - ψ ((n ^ 2 : ℕ) : ℝ) = ∑ m ∈ Ioo (n ^ 2) ((n + 1) ^ 2), Λ m := by
  rw [psi_sub_psi (sq_le_succ_sq_pred n), Ioc_pred_eq_Ioo]

/-- Legendre's conjecture implies that `ψ` strictly increases from `n²` to `(n+1)² - 1`. -/
theorem LegendreConjecture.psi_lt (h : LegendreConjecture) {n : ℕ} (hn : 1 ≤ n) :
    ψ ((n ^ 2 : ℕ) : ℝ) < ψ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) := by
  obtain ⟨p, hp, h1, h2⟩ := h n hn
  exact (psi_lt_psi_iff (sq_le_succ_sq_pred n)).2 ⟨p, hp.isPrimePow, h1, by omega⟩

/-- The contribution of the non-primes (i.e. of proper prime powers) to the `ψ`-increment over
`(n², (n+1)²)`. -/
noncomputable def primePowerCorrection (n : ℕ) : ℝ :=
  ∑ m ∈ (Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun m => ¬ m.Prime), Λ m

theorem primePowerCorrection_nonneg (n : ℕ) : 0 ≤ primePowerCorrection n :=
  sum_nonneg fun _ _ => vonMangoldt_nonneg

/-- Exact decomposition: `ψ`-increment = `θ`-increment + prime-power correction. -/
theorem psi_increment_eq (n : ℕ) :
    ψ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) - ψ ((n ^ 2 : ℕ) : ℝ) =
      (θ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) - θ ((n ^ 2 : ℕ) : ℝ)) + primePowerCorrection n := by
  rw [psi_increment_open, theta_sub_theta (sq_le_succ_sq_pred n), Ioc_pred_eq_Ioo,
    primePowerCorrection, ← sum_filter_add_sum_filter_not _ Nat.Prime]
  congr 1
  exact sum_congr rfl fun p hp => vonMangoldt_apply_prime (mem_filter.1 hp).2

/-- **Honest `ψ` reformulation**: Legendre's conjecture holds iff for every `n ≥ 1` the
`ψ`-increment over `(n², (n+1)²)` strictly exceeds the contribution of the proper prime powers. -/
theorem legendre_iff_psi :
    LegendreConjecture ↔ ∀ n : ℕ, 1 ≤ n →
      primePowerCorrection n < ψ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) - ψ ((n ^ 2 : ℕ) : ℝ) := by
  rw [legendre_iff_theta_pred]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  rw [psi_increment_eq]
  constructor <;> intro h <;> linarith

/-- A non-prime prime power strictly between `n²` and `(n+1)²` is an **odd** power `p ^ k` with
`k ≥ 3` (there is no square strictly between consecutive squares). -/
theorem exists_odd_pow_of_mem {n m : ℕ} (hm : m ∈ Ioo (n ^ 2) ((n + 1) ^ 2))
    (hpp : IsPrimePow m) (hnp : ¬ m.Prime) :
    ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ Odd k ∧ p ^ k = m := by
  rw [mem_Ioo] at hm
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hnp (by simpa using hp)
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hodd
  · exfalso
    have e : p ^ (j + j) = (p ^ j) ^ 2 := by ring
    rw [e] at hm
    have h1 : n < p ^ j := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hm.1
    have h2 : p ^ j < n + 1 := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hm.2
    omega
  · refine ⟨p, k, hp, ?_, hodd, rfl⟩
    obtain ⟨j, rfl⟩ := hodd
    omega

/-- Each non-prime in `(n², (n+1)²)` contributes at most `(2/3) log (n+1)` to `ψ`. -/
theorem vonMangoldt_le_of_mem {n m : ℕ} (hm : m ∈ Ioo (n ^ 2) ((n + 1) ^ 2))
    (hnp : ¬ m.Prime) : Λ m ≤ 2 / 3 * Real.log ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, -, rfl⟩ := exists_odd_pow_of_mem hm hpp hnp
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    have h3 : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have h4 : p ^ 3 < (n + 1) ^ 2 := lt_of_le_of_lt h3 (mem_Ioo.1 hm).2
    have hr : (p : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 2 := by exact_mod_cast h4.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have := Real.log_le_log (pow_pos hp0 3) hr
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  · rw [vonMangoldt_eq_zero_iff.2 hpp]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

/-- The primes `p ≤ n` with `p³ < (n+1)²`: the only primes that can have a proper power in
`(n², (n+1)²)`. -/
def smallPrimes (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter fun p => p.Prime ∧ p ^ 3 < (n + 1) ^ 2

/-- The proper prime powers strictly between `n²` and `(n+1)²`. -/
noncomputable def properPowers (n : ℕ) : Finset ℕ :=
  open Classical in (Ioo (n ^ 2) ((n + 1) ^ 2)).filter fun m => IsPrimePow m ∧ ¬ m.Prime

theorem mem_properPowers {n m : ℕ} :
    m ∈ properPowers n ↔ m ∈ Ioo (n ^ 2) ((n + 1) ^ 2) ∧ IsPrimePow m ∧ ¬ m.Prime := by
  classical
  simp [properPowers]

/-- Two powers of the same prime cannot both lie in `(n², (n+1)²)`. -/
theorem pow_le_of_mem {n p k l : ℕ} (hp : p.Prime) (h1 : p ^ k ∈ Ioo (n ^ 2) ((n + 1) ^ 2))
    (h2 : p ^ l ∈ Ioo (n ^ 2) ((n + 1) ^ 2)) : k ≤ l := by
  by_contra hc
  rw [not_le] at hc
  rw [mem_Ioo] at h1 h2
  have h3 : p ^ (l + 1) ≤ p ^ k := Nat.pow_le_pow_right hp.pos hc
  have h4 : p ^ (l + 1) = p ^ l * p := pow_succ p l
  have h5 : p ^ l * 2 ≤ p ^ l * p := Nat.mul_le_mul_left _ hp.two_le
  have h6 : (n + 1) ^ 2 ≤ 2 * (n ^ 2 + 1) := by nlinarith [sq_nonneg ((n : ℤ) - 1), sq_nonneg (n - 1)]
  omega

/-- There are at most `#(smallPrimes n)` proper prime powers strictly between `n²` and
`(n+1)²` (at most one for each prime `p` with `p³ < (n+1)²`). -/
theorem card_properPowers_le (n : ℕ) : (properPowers n).card ≤ (smallPrimes n).card := by
  refine card_le_card_of_injOn Nat.minFac ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, mem_properPowers] at hm
    obtain ⟨p, k, hp, hk, -, rfl⟩ := exists_odd_pow_of_mem hm.1 hm.2.1 hm.2.2
    rw [Finset.mem_coe, hp.pow_minFac (by omega), smallPrimes, mem_filter, mem_Icc]
    have h4 : p ^ 3 < (n + 1) ^ 2 :=
      lt_of_le_of_lt (Nat.pow_le_pow_right hp.pos hk) (mem_Ioo.1 hm.1).2
    refine ⟨⟨hp.pos, ?_⟩, hp, h4⟩
    by_contra hc
    have h5 : (n + 1) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h6 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  · intro m hm m' hm' heq
    rw [Finset.mem_coe, mem_properPowers] at hm hm'
    obtain ⟨p, k, hp, hk, -, rfl⟩ := exists_odd_pow_of_mem hm.1 hm.2.1 hm.2.2
    obtain ⟨q, l, hq, hl, -, rfl⟩ := exists_odd_pow_of_mem hm'.1 hm'.2.1 hm'.2.2
    rw [hp.pow_minFac (by omega), hq.pow_minFac (by omega)] at heq
    subst heq
    rw [le_antisymm (pow_le_of_mem hp hm.1 hm'.1) (pow_le_of_mem hp hm'.1 hm.1)]

/-- Explicit bound for the prime-power correction. -/
theorem primePowerCorrection_le (n : ℕ) :
    primePowerCorrection n ≤ (smallPrimes n).card * (2 / 3 * Real.log ((n : ℝ) + 1)) := by
  classical
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : 0 ≤ 2 / 3 * Real.log ((n : ℝ) + 1) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have h1 : primePowerCorrection n = ∑ m ∈ properPowers n, Λ m := by
    rw [primePowerCorrection]
    symm
    refine sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
    · rw [mem_properPowers] at hm
      exact mem_filter.2 ⟨hm.1, hm.2.2⟩
    · rw [mem_filter] at hm
      rw [mem_properPowers] at hm'
      exact vonMangoldt_eq_zero_iff.2 fun hpp => hm' ⟨hm.1, hpp, hm.2⟩
  rw [h1]
  calc ∑ m ∈ properPowers n, Λ m
      ≤ ∑ _m ∈ properPowers n, 2 / 3 * Real.log ((n : ℝ) + 1) :=
        sum_le_sum fun m hm =>
          vonMangoldt_le_of_mem (mem_properPowers.1 hm).1 (mem_properPowers.1 hm).2.2
    _ = (properPowers n).card * (2 / 3 * Real.log ((n : ℝ) + 1)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (smallPrimes n).card * (2 / 3 * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_properPowers_le n) hL

/-- **Honest analytic criterion (converse with prime-power correction)**: if the `ψ`-increment
over `(n², (n+1)²)` exceeds `#{p ≤ n prime : p³ < (n+1)²} · (2/3) log (n+1)`, then there is a prime
strictly between `n²` and `(n+1)²`. -/
theorem exists_prime_of_psi_increment_gt {n : ℕ}
    (h : (smallPrimes n).card * (2 / 3 * Real.log ((n : ℝ) + 1)) <
      ψ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) - ψ ((n ^ 2 : ℕ) : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have h1 := primePowerCorrection_le n
  have h2 := psi_increment_eq n
  have h3 : θ ((n ^ 2 : ℕ) : ℝ) < θ (((n + 1) ^ 2 - 1 : ℕ) : ℝ) := by linarith
  obtain ⟨p, hp, hp1, hp2⟩ := (theta_lt_theta_iff (sq_le_succ_sq_pred n)).1 h3
  have : 0 < (n + 1) ^ 2 := by positivity
  exact ⟨p, hp, hp1, by omega⟩

/-- The correction is genuinely nonzero in general: `27 = 3³` and `32 = 2⁵` lie in `(25, 36)`,
so a bare "`ψ` increases ⇒ prime" converse would need an argument. -/
theorem primePowerCorrection_five_pos : 0 < primePowerCorrection 5 := by
  refine sum_pos' (fun _ _ => vonMangoldt_nonneg) ⟨27, ?_, ?_⟩
  · rw [mem_filter, mem_Ioo]
    refine ⟨by norm_num, by norm_num⟩
  · exact vonMangoldt_pos_iff.2 ⟨3, 3, Nat.prime_three.prime, by norm_num, by norm_num⟩

/-! ## Numerical verification by kernel computation

**Numerical evidence only**; no progress towards the general statement. -/

/-- Trial division by the odd numbers `d = 3, 5, 7, …`, stopping as soon as `d * d > n`.  The
current divisor is `d = 2 * (F - f) + 1`, where `F` is the initial fuel and `f + 1` the remaining
fuel.  Running out of fuel returns `false`. -/
def noDivFrom (n F : ℕ) : ℕ → Bool
  | 0 => false
  | f + 1 =>
    Nat.blt n ((2 * (F - f) + 1) * (2 * (F - f) + 1)) ||
      (n % (2 * (F - f) + 1) != 0 && noDivFrom n F f)

theorem noDivFrom_spec {n F : ℕ} : ∀ {f : ℕ}, f ≤ F → noDivFrom n F f = true →
    ∀ m, 2 * (F - f) + 3 ≤ m → m % 2 = 1 → m * m ≤ n → ¬ m ∣ n
  | 0, _, h, _, _, _, _ => by simp [noDivFrom] at h
  | f + 1, hf, h, m, hdm, hpar, hmn => by
    simp only [noDivFrom, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne] at h
    have hd : 2 * (F - (f + 1)) + 3 = 2 * (F - f) + 1 := by omega
    rw [hd] at hdm
    rcases h with h | ⟨h1, h2⟩
    · have : (2 * (F - f) + 1) * (2 * (F - f) + 1) ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
      · exact fun hdvd => h1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact noDivFrom_spec (by omega) h2 m (by omega) hpar hmn

/-- Trial-division primality test (sound; see `isPrimeB_spec`).  The fuel `f` must be large
enough (`f * f ≥ n` certainly suffices); too little fuel only makes the test return `false`. -/
def isPrimeB (n f : ℕ) : Bool :=
  Nat.beq n 2 || (Nat.ble 3 n && (n % 2 != 0 && noDivFrom n f f))

theorem isPrimeB_spec {n f : ℕ} (h : isPrimeB n f = true) : n.Prime := by
  simp only [isPrimeB, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, bne_iff_ne] at h
  rcases h with h | ⟨h3, hodd, hnd⟩
  · rw [Nat.eq_of_beq_eq_true h]
    exact Nat.prime_two
  · refine Nat.prime_def_le_sqrt.2 ⟨by omega, fun m hm2 hms hdvd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.1 hms
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · exact hodd (Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero hm).trans hdvd))
    · exact noDivFrom_spec le_rfl hnd m (by omega) hm hmm hdvd

/-- `findPrimeIn lo F f` tests `lo + f, lo + f - 1, …, lo + 1` for primality (with trial-division
fuel `F`) and returns `true` only if one of them is prime. -/
def findPrimeIn (lo F : ℕ) : ℕ → Bool
  | 0 => false
  | f + 1 => isPrimeB (lo + (f + 1)) F || findPrimeIn lo F f

theorem findPrimeIn_spec {lo F : ℕ} : ∀ {f : ℕ}, findPrimeIn lo F f = true →
    ∃ p : ℕ, p.Prime ∧ lo < p ∧ p ≤ lo + f
  | 0, h => by simp [findPrimeIn] at h
  | f + 1, h => by
    simp only [findPrimeIn, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lo + (f + 1), isPrimeB_spec h, by omega, le_rfl⟩
    · obtain ⟨p, hp, h1, h2⟩ := findPrimeIn_spec h
      exact ⟨p, hp, h1, by omega⟩

/-- `checkUpTo M = true` implies Legendre's statement for every `1 ≤ n ≤ M`: for `n = m + 1` it
searches `n² + 1, …, n² + 2n - 1` for a prime. -/
def checkUpTo : ℕ → Bool
  | 0 => true
  | m + 1 => findPrimeIn ((m + 1) * (m + 1)) (m + 2) (2 * m + 1) && checkUpTo m

theorem checkUpTo_spec : ∀ {M : ℕ}, checkUpTo M = true →
    ∀ n, 1 ≤ n → n ≤ M → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2
  | 0, _, n, h1, h2 => by omega
  | m + 1, h, n, h1, h2 => by
    simp only [checkUpTo, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h2 with rfl | hlt
    · obtain ⟨p, hp, hp1, hp2⟩ := findPrimeIn_spec h.1
      have e1 : (m + 1) ^ 2 = (m + 1) * (m + 1) := by ring
      have e2 : (m + 1 + 1) ^ 2 = (m + 1) * (m + 1) + 2 * m + 3 := by ring
      exact ⟨p, hp, by omega, by omega⟩
    · exact checkUpTo_spec h.2 n h1 (by omega)

/-- The bound up to which Legendre's conjecture is verified in this file. -/
def legendreBound : ℕ := 1000

theorem checkUpTo_legendreBound : checkUpTo 1000 = true := by decide +kernel

/-- **Numerical evidence** (not progress on the general statement): Legendre's conjecture holds
for every `1 ≤ n ≤ legendreBound`. -/
theorem legendre_upTo_bound (n : ℕ) (h1 : 1 ≤ n) (hn : n ≤ legendreBound) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 :=
  checkUpTo_spec checkUpTo_legendreBound n h1 hn

end Legendre

/-! ## Axiom audit -/

#print axioms Legendre.consecutivePrimes_nth
#print axioms Legendre.oppermann_implies_legendre
#print axioms Legendre.andrica_implies_legendre
#print axioms Legendre.andrica_iff_gap
#print axioms Legendre.LegendreConjecture.gap_le
#print axioms Legendre.LegendreConjecture.gap_le_real
#print axioms Legendre.legendre_at_of_cramerGapBound
#print axioms Legendre.eventually_legendre_of_cramerGapBound
#print axioms Legendre.primeCounting_lt_iff
#print axioms Legendre.legendre_iff_primeCounting
#print axioms Legendre.LegendreConjecture.le_primeCounting
#print axioms Legendre.theta_lt_theta_iff
#print axioms Legendre.psi_lt_psi_iff
#print axioms Legendre.legendre_iff_theta_pred
#print axioms Legendre.legendre_iff_theta
#print axioms Legendre.psi_increment_closed
#print axioms Legendre.psi_increment_open
#print axioms Legendre.LegendreConjecture.psi_lt
#print axioms Legendre.psi_increment_eq
#print axioms Legendre.legendre_iff_psi
#print axioms Legendre.exists_odd_pow_of_mem
#print axioms Legendre.card_properPowers_le
#print axioms Legendre.primePowerCorrection_le
#print axioms Legendre.exists_prime_of_psi_increment_gt
#print axioms Legendre.primePowerCorrection_five_pos
#print axioms Legendre.checkUpTo_legendreBound
#print axioms Legendre.legendre_upTo_bound
