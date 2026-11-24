import Mathlib

/-!
# Goldbach's (binary) conjecture and its von Mangoldt-weighted analytic form

**STATUS: IN PROGRESS / NOT YET SOLVED.**
Goldbach's conjecture is an OPEN problem.  This file does **not** prove it and does not claim to.
It contains a faithful formal *statement* of the conjecture, of its weighted analytic form, and a
collection of machine-checked *partial* results (elementary equivalences, comparisons between the
counting functions, classical reformulations, and a finite numerical verification).

## Statement

*Goldbach's (binary / strong / even) conjecture*: every even integer `N > 2` is the sum of two
primes.  (`GoldbachConjecture` below.)

*Weighted analytic form.*  With `Λ` the von Mangoldt function, put
`rΛ N = ∑_{m + n = N} Λ m * Λ n`.  The Hardy–Littlewood circle method studies `rΛ N` (or the
variant `rθ N = ∑_{p + q = N, p, q prime} log p * log q`); the Hardy–Littlewood conjecture
predicts `rΛ N ∼ 𝔖(N) · N` for even `N`, with `𝔖` the singular series.  Goldbach's conjecture is
equivalent to `0 < rθ N` for every even `N > 2` (proved below, `goldbach_iff_rθ_pos`), and
`rΛ N - rθ N`, the contribution of proper prime powers, is `O(√N log³ N)` (proved below with the
explicit bound `√N · log₂ N · log² N`, `rΛ_sub_rθ_le`).

## Attribution and history (literature check, November 2026; uncertainty preserved)

* Christian Goldbach, letter to Leonhard Euler, 7 June 1742 (letter XLIII in Fuss's edition of the
  correspondence).  Goldbach conjectured, in the margin, that every integer greater than 2 is a sum
  of three primes; Goldbach counted `1` as a prime, so his statements must be translated to the
  modern convention.
* Euler's reply, 30 June 1742, contains the *binary* form ("every even integer is a sum of two
  primes"), which Euler says he regards as a completely certain theorem although he cannot prove
  it; Euler attributes the observation to an earlier communication with Goldbach.  So the binary
  form as it is known today appears in Euler's letter.
* A statement of similar kind (every even number is a sum of at most three primes) appears in
  Descartes' manuscripts, which were only printed much later (in the Adam–Tannery edition of the
  *Œuvres*, vol. X, 1908); see J. Pintz's discussion.  There is no evidence that Goldbach or Euler
  knew of it; priority is therefore genuinely uncertain and we record it as such.
* G. H. Hardy and J. E. Littlewood, "Some problems of 'Partitio Numerorum' III: On the expression
  of a number as a sum of primes", Acta Math. 44 (1923) 1–70: circle method, conditional (GRH)
  ternary result, and the conjectural asymptotic formula for the binary problem.
* I. M. Vinogradov (1937): every sufficiently large odd integer is a sum of three primes
  (unconditional).
* Chen Jingrun (announced 1966, full proof 1973): every sufficiently large even integer is a sum
  of a prime and a number with at most two prime factors.
* H. A. Helfgott (preprints 2012–2013, arXiv:1205.5252, 1305.2897, 1312.7748): the ternary
  conjecture for all odd `N > 5`.  The proof is widely accepted; a monograph was accepted for the
  Annals of Mathematics Studies in 2015 and has been under revision since.  As far as our
  literature check could determine it had not yet appeared in final published form (unverified
  beyond the author's web page and secondary sources).
* T. Oliveira e Silva, S. Herzog, S. Pardi, "Empirical verification of the even Goldbach
  conjecture and computation of prime gaps up to 4·10¹⁸", Math. Comp. 83 (2014) 2033–2060:
  the binary conjecture holds for all even `4 ≤ N ≤ 4·10¹⁸`.
* Claimed proofs of the binary conjecture continue to appear on preprint servers (viXra, Zenodo,
  preprints.org, SSRN, etc.).  To our knowledge none has been accepted by the mathematical
  community; the conjecture is regarded as open as of late 2026.

## What is proved in this file (all machine-checked, no `sorry`, no extra axioms)

* `rΛ_pos_iff`     : `0 < rΛ N ↔ N` is a sum of two prime powers.
* `rθ_pos_iff`, `r_pos_iff` : `0 < rθ N ↔ 0 < r N ↔ N` is a sum of two primes.
* `goldbach_iff_rθ_pos`, `goldbach_iff_r_pos`, `GoldbachConjecture.rΛ_pos`.
* `rθ_le_rΛ`, `rθ_le_log_sq_mul_r`, `log_two_sq_mul_r_le_rθ`.
* `rΛ_sub_rθ_le`   : `rΛ N - rθ N ≤ √N · log₂ N · (log N)²` (with `Nat.sqrt`, `Nat.log 2`),
  and `rΛ_sub_rθ_le_real` with real square root and logarithm.
* `sum_two_primes_of_rΛ_gt` : if `rΛ N` exceeds that bound then `N` is a sum of two primes.
* `goldbach_implies_ternary`, `goldbach_iff_three_primes`, `goldbach_iff_primeCentered`:
  classical reductions / reformulations.
* `goldbach_upTo_bound` : numerical verification of Goldbach for all even `2 < N ≤ goldbachBound`
  by kernel computation (numerical evidence only, **not** progress on the general statement).

## What is NOT proved

* `GoldbachConjecture` itself (open).
* `HardyLittlewoodLowerBound`, the statement that `rΛ N` exceeds the error term for all even
  `N > 2` (open; it is *equivalent in strength to more than* Goldbach and is only stated).
* Any asymptotic formula for `rΛ N`.
-/

namespace Goldbach

open Finset ArithmeticFunction

/-! ## Definitions -/

/-- **Goldbach's binary conjecture** (OPEN; stated, not proved):
every even integer `N > 2` is a sum of two primes. -/
def GoldbachConjecture : Prop :=
  ∀ N : ℕ, 2 < N → Even N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N

/-- The von Mangoldt-weighted Goldbach count `rΛ N = ∑_{m + n = N} Λ m * Λ n`. -/
noncomputable def rΛ (N : ℕ) : ℝ :=
  ∑ x ∈ antidiagonal N, Λ x.1 * Λ x.2

/-- The set of ordered pairs of primes `(p, q)` with `p + q = N`. -/
def primePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal N).filter fun x => x.1.Prime ∧ x.2.Prime

/-- The prime-only weighted count `rθ N = ∑_{p + q = N, p, q prime} log p * log q`. -/
noncomputable def rθ (N : ℕ) : ℝ :=
  ∑ x ∈ primePairs N, Real.log x.1 * Real.log x.2

/-- The plain count `r N` of ordered pairs of primes `(p, q)` with `p + q = N`. -/
def r (N : ℕ) : ℕ := (primePairs N).card

/-- The (finite) set of proper prime powers `p ^ k`, `k ≥ 2`, in `[1, N]`. -/
noncomputable def properPrimePowers (N : ℕ) : Finset ℕ :=
  open Classical in (Icc 1 N).filter fun m => IsPrimePow m ∧ ¬ m.Prime

/-- OPEN, stated only: the weighted count beats the explicit prime-power error term for every
even `N > 2`.  By `sum_two_primes_of_rΛ_gt` this implies Goldbach's conjecture. -/
def HardyLittlewoodLowerBound : Prop :=
  ∀ N : ℕ, 2 < N → Even N →
    (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) * Real.log N ^ 2 < rΛ N

/-! ## Basic lemmas -/

theorem mem_primePairs {N : ℕ} {x : ℕ × ℕ} :
    x ∈ primePairs N ↔ x.1 + x.2 = N ∧ x.1.Prime ∧ x.2.Prime := by
  simp [primePairs]

theorem rθ_eq_sum_vonMangoldt (N : ℕ) : rθ N = ∑ x ∈ primePairs N, Λ x.1 * Λ x.2 := by
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨-, h1, h2⟩ := mem_primePairs.1 hx
  rw [vonMangoldt_apply_prime h1, vonMangoldt_apply_prime h2]

theorem rΛ_nonneg (N : ℕ) : 0 ≤ rΛ N :=
  sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

theorem rθ_nonneg (N : ℕ) : 0 ≤ rθ N := by
  rw [rθ_eq_sum_vonMangoldt]
  exact sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/-! ## Positivity criteria -/

/-- `rΛ N > 0` iff `N` is a sum of two prime powers (exponents `≥ 1`). -/
theorem rΛ_pos_iff (N : ℕ) :
    0 < rΛ N ↔ ∃ a b : ℕ, IsPrimePow a ∧ IsPrimePow b ∧ a + b = N := by
  unfold rΛ
  rw [sum_pos_iff_of_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg]
  constructor
  · rintro ⟨⟨a, b⟩, hx, hpos⟩
    refine ⟨a, b, ?_, ?_, mem_antidiagonal.1 hx⟩
    · by_contra h
      rw [vonMangoldt_eq_zero_iff.2 h, zero_mul] at hpos
      exact lt_irrefl _ hpos
    · by_contra h
      rw [vonMangoldt_eq_zero_iff.2 h, mul_zero] at hpos
      exact lt_irrefl _ hpos
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨(a, b), mem_antidiagonal.2 hab,
      mul_pos (vonMangoldt_pos_iff.2 ha) (vonMangoldt_pos_iff.2 hb)⟩

/-- `r N > 0` iff `N` is a sum of two primes. -/
theorem r_pos_iff (N : ℕ) : 0 < r N ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  unfold r
  rw [card_pos]
  constructor
  · rintro ⟨⟨p, q⟩, hx⟩
    obtain ⟨h, hp, hq⟩ := mem_primePairs.1 hx
    exact ⟨p, q, hp, hq, h⟩
  · rintro ⟨p, q, hp, hq, h⟩
    exact ⟨(p, q), mem_primePairs.2 ⟨h, hp, hq⟩⟩

/-- `rθ N > 0` iff `N` is a sum of two primes. -/
theorem rθ_pos_iff (N : ℕ) : 0 < rθ N ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  rw [rθ_eq_sum_vonMangoldt,
    sum_pos_iff_of_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg]
  constructor
  · rintro ⟨⟨p, q⟩, hx, -⟩
    obtain ⟨h, hp, hq⟩ := mem_primePairs.1 hx
    exact ⟨p, q, hp, hq, h⟩
  · rintro ⟨p, q, hp, hq, h⟩
    exact ⟨(p, q), mem_primePairs.2 ⟨h, hp, hq⟩,
      mul_pos (vonMangoldt_pos_iff.2 hp.isPrimePow) (vonMangoldt_pos_iff.2 hq.isPrimePow)⟩

/-- Goldbach's conjecture is equivalent to positivity of `rθ` at every even `N > 2`. -/
theorem goldbach_iff_rθ_pos :
    GoldbachConjecture ↔ ∀ N : ℕ, 2 < N → Even N → 0 < rθ N := by
  simp only [GoldbachConjecture, rθ_pos_iff]

/-- Goldbach's conjecture is equivalent to positivity of `r` at every even `N > 2`. -/
theorem goldbach_iff_r_pos :
    GoldbachConjecture ↔ ∀ N : ℕ, 2 < N → Even N → 0 < r N := by
  simp only [GoldbachConjecture, r_pos_iff]

/-! ## Quantitative comparisons -/

/-- `rθ N ≤ rΛ N`: the prime pairs are part of the von Mangoldt sum. -/
theorem rθ_le_rΛ (N : ℕ) : rθ N ≤ rΛ N := by
  rw [rθ_eq_sum_vonMangoldt]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun _ _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/-- Goldbach's conjecture implies positivity of the von Mangoldt-weighted count.
(The converse is NOT claimed: `rΛ N > 0` only gives two prime powers.) -/
theorem GoldbachConjecture.rΛ_pos (h : GoldbachConjecture) :
    ∀ N : ℕ, 2 < N → Even N → 0 < rΛ N := fun N h2 he =>
  lt_of_lt_of_le (goldbach_iff_rθ_pos.1 h N h2 he) (rθ_le_rΛ N)

theorem log_le_log_of_le_nat {m N : ℕ} (h : m ≤ N) : Real.log m ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-- `rθ N ≤ (log N)² · r N`. -/
theorem rθ_le_log_sq_mul_r (N : ℕ) : rθ N ≤ Real.log N ^ 2 * r N := by
  have : ∀ x ∈ primePairs N, Real.log x.1 * Real.log x.2 ≤ Real.log N ^ 2 := by
    intro x hx
    obtain ⟨h, -, -⟩ := mem_primePairs.1 hx
    rw [sq]
    exact mul_le_mul (log_le_log_of_le_nat (by omega)) (log_le_log_of_le_nat (by omega))
      (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  calc rθ N ≤ ∑ _x ∈ primePairs N, Real.log N ^ 2 := sum_le_sum this
    _ = Real.log N ^ 2 * r N := by rw [sum_const, nsmul_eq_mul, mul_comm]; rfl

/-- `(log 2)² · r N ≤ rθ N`. -/
theorem log_two_sq_mul_r_le_rθ (N : ℕ) : Real.log 2 ^ 2 * r N ≤ rθ N := by
  have h0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have key : ∀ p : ℕ, p.Prime → Real.log 2 ≤ Real.log p := fun p hp =>
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have : ∀ x ∈ primePairs N, Real.log 2 ^ 2 ≤ Real.log x.1 * Real.log x.2 := by
    intro x hx
    obtain ⟨-, h1, h2⟩ := mem_primePairs.1 hx
    rw [sq]
    exact mul_le_mul (key _ h1) (key _ h2) h0 (h0.trans (key _ h1))
  calc Real.log 2 ^ 2 * r N = ∑ _x ∈ primePairs N, Real.log 2 ^ 2 := by
        rw [sum_const, nsmul_eq_mul, mul_comm]; rfl
    _ ≤ rθ N := sum_le_sum this

/-! ## The contribution of proper prime powers -/

theorem mem_properPrimePowers {N m : ℕ} :
    m ∈ properPrimePowers N ↔ m ≤ N ∧ IsPrimePow m ∧ ¬ m.Prime := by
  simp only [properPrimePowers, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨⟨h'.1.one_lt.le, h⟩, h'⟩

/-- A proper prime power `m ≤ N` is `p ^ k` with `p` prime, `2 ≤ p ≤ √N`, `2 ≤ k ≤ log₂ N`. -/
theorem exists_of_mem_properPrimePowers {N m : ℕ} (hm : m ∈ properPrimePowers N) :
    ∃ p k : ℕ, p.Prime ∧ p ≤ Nat.sqrt N ∧ 2 ≤ k ∧ k ≤ Nat.log 2 N ∧ p ^ k = m := by
  obtain ⟨hmN, hpp, hnp⟩ := mem_properPrimePowers.1 hm
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 hpp
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    subst this
    exact hnp (by simpa using hp)
  refine ⟨p, k, hp, ?_, hk2, ?_, rfl⟩
  · rw [Nat.le_sqrt, ← sq]
    exact (Nat.pow_le_pow_right hp.pos hk2).trans hmN
  · exact Nat.le_log_of_pow_le (by norm_num)
      ((Nat.pow_le_pow_left hp.two_le k).trans hmN)

/-- There are at most `√N · log₂ N` proper prime powers up to `N`. -/
theorem card_properPrimePowers_le (N : ℕ) :
    (properPrimePowers N).card ≤ Nat.sqrt N * Nat.log 2 N := by
  have hsub : properPrimePowers N ⊆
      (Icc 2 (Nat.sqrt N) ×ˢ Icc 2 (Nat.log 2 N)).image fun x => x.1 ^ x.2 := by
    intro m hm
    obtain ⟨p, k, hp, hps, hk2, hkl, rfl⟩ := exists_of_mem_properPrimePowers hm
    exact mem_image.2 ⟨(p, k), mem_product.2 ⟨mem_Icc.2 ⟨hp.two_le, hps⟩,
      mem_Icc.2 ⟨hk2, hkl⟩⟩, rfl⟩
  calc (properPrimePowers N).card
      ≤ (Icc 2 (Nat.sqrt N) ×ˢ Icc 2 (Nat.log 2 N)).card :=
        (card_le_card hsub).trans card_image_le
    _ = (Nat.sqrt N + 1 - 2) * (Nat.log 2 N + 1 - 2) := by
        rw [card_product, Nat.card_Icc, Nat.card_Icc]
    _ ≤ Nat.sqrt N * Nat.log 2 N := Nat.mul_le_mul (by omega) (by omega)

/-- `Λ m ≤ log N` for `m ≤ N`. -/
theorem vonMangoldt_le_log_of_le {m N : ℕ} (h : m ≤ N) : Λ m ≤ Real.log N :=
  vonMangoldt_le_log.trans (log_le_log_of_le_nat h)

/-- `Λ m ≤ (log N) / 2` for a proper prime power `m ≤ N`. -/
theorem vonMangoldt_le_half_log {m N : ℕ} (hm : m ∈ properPrimePowers N) :
    Λ m ≤ Real.log N / 2 := by
  obtain ⟨p, k, hp, hps, hk2, -, rfl⟩ := exists_of_mem_properPrimePowers hm
  rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  have h1 : p ^ 2 ≤ N := by rw [sq]; exact Nat.le_sqrt.1 hps
  have h2 : Real.log ((p ^ 2 : ℕ) : ℝ) ≤ Real.log N := log_le_log_of_le_nat h1
  rw [Nat.cast_pow, Real.log_pow] at h2
  push_cast at h2
  linarith

/-- The number of `(m, n)` with `m + n = N` and `m` in a set `Q ⊆ ℕ` is at most `|Q|`. -/
theorem card_filter_fst_le (N : ℕ) (Q : Finset ℕ) :
    ((antidiagonal N).filter fun x => x.1 ∈ Q).card ≤ Q.card := by
  refine card_le_card_of_injOn Prod.fst (fun x hx => (mem_filter.1 hx).2) ?_
  intro x hx y hy hxy
  have h1 := mem_antidiagonal.1 (mem_filter.1 hx).1
  have h2 := mem_antidiagonal.1 (mem_filter.1 hy).1
  ext
  · exact hxy
  · have : x.1 = y.1 := hxy
    omega

theorem card_filter_snd_le (N : ℕ) (Q : Finset ℕ) :
    ((antidiagonal N).filter fun x => x.2 ∈ Q).card ≤ Q.card := by
  refine card_le_card_of_injOn Prod.snd (fun x hx => (mem_filter.1 hx).2) ?_
  intro x hx y hy hxy
  have h1 := mem_antidiagonal.1 (mem_filter.1 hx).1
  have h2 := mem_antidiagonal.1 (mem_filter.1 hy).1
  ext
  · have : x.2 = y.2 := hxy
    omega
  · exact hxy

/-- The non-prime contribution to `rΛ` is bounded by `(log N)² · #{proper prime powers ≤ N}`. -/
theorem rΛ_sub_rθ_le_card (N : ℕ) :
    rΛ N - rθ N ≤ Real.log N ^ 2 * (properPrimePowers N).card := by
  classical
  set L := Real.log N with hL
  set Q := properPrimePowers N with hQ
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg N
  have hsplit : rΛ N - rθ N
      = ∑ x ∈ (antidiagonal N).filter (fun x => ¬ (x.1.Prime ∧ x.2.Prime)), Λ x.1 * Λ x.2 := by
    rw [rθ_eq_sum_vonMangoldt, rΛ, primePairs,
      ← sum_filter_add_sum_filter_not (antidiagonal N) (fun x => x.1.Prime ∧ x.2.Prime)]
    ring
  have hterm : ∀ x ∈ (antidiagonal N).filter (fun x => ¬ (x.1.Prime ∧ x.2.Prime)),
      Λ x.1 * Λ x.2 ≤ (if x.1 ∈ Q then L ^ 2 / 2 else 0) + (if x.2 ∈ Q then L ^ 2 / 2 else 0) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_filter.1 hx
    have hsum := mem_antidiagonal.1 hx1
    have h1N : x.1 ≤ N := by omega
    have h2N : x.2 ≤ N := by omega
    have hnn : (0 : ℝ) ≤ (if x.1 ∈ Q then L ^ 2 / 2 else 0) + (if x.2 ∈ Q then L ^ 2 / 2 else 0) := by
      split_ifs <;> positivity
    by_cases hp1 : IsPrimePow x.1
    swap
    · rw [vonMangoldt_eq_zero_iff.2 hp1, zero_mul]; exact hnn
    by_cases hp2 : IsPrimePow x.2
    swap
    · rw [vonMangoldt_eq_zero_iff.2 hp2, mul_zero]; exact hnn
    by_cases hq1 : x.1.Prime
    · have hq2 : ¬ x.2.Prime := fun h => hx2 ⟨hq1, h⟩
      have hmem : x.2 ∈ Q := mem_properPrimePowers.2 ⟨h2N, hp2, hq2⟩
      have ha := vonMangoldt_le_log_of_le h1N
      have hb := vonMangoldt_le_half_log hmem
      have : Λ x.1 * Λ x.2 ≤ L * (L / 2) :=
        mul_le_mul ha hb vonMangoldt_nonneg hL0
      rw [ite_eq_left hmem]
      have : (0 : ℝ) ≤ if x.1 ∈ Q then L ^ 2 / 2 else 0 := by split_ifs <;> positivity
      nlinarith
    · have hmem : x.1 ∈ Q := mem_properPrimePowers.2 ⟨h1N, hp1, hq1⟩
      have ha := vonMangoldt_le_half_log hmem
      have hb := vonMangoldt_le_log_of_le h2N
      have : Λ x.1 * Λ x.2 ≤ (L / 2) * L :=
        mul_le_mul ha hb vonMangoldt_nonneg (by positivity)
      rw [ite_eq_left hmem]
      have : (0 : ℝ) ≤ if x.2 ∈ Q then L ^ 2 / 2 else 0 := by split_ifs <;> positivity
      nlinarith
  have hc1 : ∑ x ∈ antidiagonal N, (if x.1 ∈ Q then L ^ 2 / 2 else 0) ≤ L ^ 2 / 2 * Q.card := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_filter_fst_le N Q) (by positivity)
  have hc2 : ∑ x ∈ antidiagonal N, (if x.2 ∈ Q then L ^ 2 / 2 else 0) ≤ L ^ 2 / 2 * Q.card := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_filter_snd_le N Q) (by positivity)
  calc rΛ N - rθ N
      = ∑ x ∈ (antidiagonal N).filter (fun x => ¬ (x.1.Prime ∧ x.2.Prime)), Λ x.1 * Λ x.2 := hsplit
    _ ≤ ∑ x ∈ (antidiagonal N).filter (fun x => ¬ (x.1.Prime ∧ x.2.Prime)),
          ((if x.1 ∈ Q then L ^ 2 / 2 else 0) + (if x.2 ∈ Q then L ^ 2 / 2 else 0)) :=
        sum_le_sum hterm
    _ ≤ ∑ x ∈ antidiagonal N,
          ((if x.1 ∈ Q then L ^ 2 / 2 else 0) + (if x.2 ∈ Q then L ^ 2 / 2 else 0)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun _ _ _ => by split_ifs <;> positivity
    _ = ∑ x ∈ antidiagonal N, (if x.1 ∈ Q then L ^ 2 / 2 else 0)
          + ∑ x ∈ antidiagonal N, (if x.2 ∈ Q then L ^ 2 / 2 else 0) := sum_add_distrib
    _ ≤ L ^ 2 / 2 * Q.card + L ^ 2 / 2 * Q.card := add_le_add hc1 hc2
    _ = L ^ 2 * Q.card := by ring

/-- **Explicit bound for the prime-power error term**:
`rΛ N - rθ N ≤ ⌊√N⌋ · ⌊log₂ N⌋ · (log N)²`. -/
theorem rΛ_sub_rθ_le (N : ℕ) :
    rΛ N - rθ N ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) * Real.log N ^ 2 := by
  have h := rΛ_sub_rθ_le_card N
  have hc : ((properPrimePowers N).card : ℝ) ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) := by
    exact_mod_cast card_properPrimePowers_le N
  have := mul_le_mul_of_nonneg_left hc (sq_nonneg (Real.log N))
  linarith

/-- The same bound with the real square root and real logarithm:
`rΛ N - rθ N ≤ √N · (log N)³ / log 2`. -/
theorem rΛ_sub_rθ_le_real (N : ℕ) :
    rΛ N - rθ N ≤ Real.sqrt N * Real.log N ^ 3 / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have h2 : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
    have := Real.natLog_le_logb N 2
    simpa [Real.logb] using this
  have h3 : (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) ≤ Real.sqrt N * (Real.log N / Real.log 2) :=
    mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  calc rΛ N - rθ N ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) * Real.log N ^ 2 := rΛ_sub_rθ_le N
    _ ≤ Real.sqrt N * (Real.log N / Real.log 2) * Real.log N ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    _ = Real.sqrt N * Real.log N ^ 3 / Real.log 2 := by ring

/-- **Honest analytic criterion**: if the von Mangoldt-weighted count exceeds the explicit
prime-power error term, then `N` is a sum of two primes. -/
theorem sum_two_primes_of_rΛ_gt {N : ℕ}
    (h : (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) * Real.log N ^ 2 < rΛ N) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  rw [← rθ_pos_iff]
  have := rΛ_sub_rθ_le N
  linarith

/-- The (open, unproved) hypothesis `HardyLittlewoodLowerBound` implies Goldbach's conjecture. -/
theorem goldbach_of_hardyLittlewoodLowerBound (h : HardyLittlewoodLowerBound) :
    GoldbachConjecture := fun N h2 he => sum_two_primes_of_rΛ_gt (h N h2 he)

/-! ## Classical reductions and reformulations -/

/-- Ternary Goldbach statement: every odd `N > 5` is a sum of three primes.
(This is a theorem of Helfgott, 2013; it is NOT proved here unconditionally.) -/
def TernaryGoldbach : Prop :=
  ∀ N : ℕ, 5 < N → Odd N → ∃ p q s : ℕ, p.Prime ∧ q.Prime ∧ s.Prime ∧ p + q + s = N

/-- The Goldbach–Euler three-prime form: every integer `N > 5` is a sum of three primes. -/
def ThreePrimes : Prop :=
  ∀ N : ℕ, 5 < N → ∃ p q s : ℕ, p.Prime ∧ q.Prime ∧ s.Prime ∧ p + q + s = N

/-- Prime-centred form: every `n ≥ 2` is the midpoint of two primes `n - d`, `n + d`
(`d = 0` allowed, i.e. `n` itself prime). -/
def PrimeCentered : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ d : ℕ, d ≤ n ∧ (n - d).Prime ∧ (n + d).Prime

/-- Binary Goldbach implies ternary Goldbach. -/
theorem goldbach_implies_ternary (h : GoldbachConjecture) : TernaryGoldbach := by
  intro N h5 hodd
  obtain ⟨k, rfl⟩ := hodd
  obtain ⟨p, q, hp, hq, hpq⟩ := h (2 * k + 1 - 3) (by omega) ⟨k - 1, by omega⟩
  exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩

/-- Binary Goldbach is equivalent to: every integer `> 5` is a sum of three primes. -/
theorem goldbach_iff_three_primes : GoldbachConjecture ↔ ThreePrimes := by
  constructor
  · intro h N h5
    rcases Nat.even_or_odd N with he | ho
    · obtain ⟨k, rfl⟩ := he
      obtain ⟨p, q, hp, hq, hpq⟩ := h (k + k - 2) (by omega) ⟨k - 1, by omega⟩
      exact ⟨p, q, 2, hp, hq, Nat.prime_two, by omega⟩
    · exact goldbach_implies_ternary h N h5 ho
  · intro h N h2 he
    have h7 : 5 < N + 2 := by
      obtain ⟨e, rfl⟩ := he
      omega
    obtain ⟨p, q, s, hp, hq, hs, hsum⟩ := h (N + 2) h7
    -- one of the three primes is even, hence equal to 2
    have key : p = 2 ∨ q = 2 ∨ s = 2 := by
      by_contra hne
      rw [not_or, not_or] at hne
      obtain ⟨a, ha⟩ := hp.eq_two_or_odd'.resolve_left hne.1
      obtain ⟨b, hb⟩ := hq.eq_two_or_odd'.resolve_left hne.2.1
      obtain ⟨c, hc⟩ := hs.eq_two_or_odd'.resolve_left hne.2.2
      obtain ⟨e, he'⟩ := he
      omega
    rcases key with rfl | rfl | rfl
    · exact ⟨q, s, hq, hs, by omega⟩
    · exact ⟨p, s, hp, hs, by omega⟩
    · exact ⟨p, q, hp, hq, by omega⟩

/-- Binary Goldbach is equivalent to the prime-centred form. -/
theorem goldbach_iff_primeCentered : GoldbachConjecture ↔ PrimeCentered := by
  constructor
  · intro h n hn
    obtain ⟨p, q, hp, hq, hpq⟩ := h (2 * n) (by omega) ⟨n, by omega⟩
    rcases le_total p q with hle | hle
    · refine ⟨n - p, by omega, ?_, ?_⟩
      · rwa [show n - (n - p) = p by omega]
      · rwa [show n + (n - p) = q by omega]
    · refine ⟨n - q, by omega, ?_, ?_⟩
      · rwa [show n - (n - q) = q by omega]
      · rwa [show n + (n - q) = p by omega]
  · intro h N h2 he
    obtain ⟨n, rfl⟩ := he
    obtain ⟨d, hd, h1, h2'⟩ := h n (by omega)
    exact ⟨n - d, n + d, h1, h2', by omega⟩

/-! ## Numerical verification by kernel computation

This is **numerical evidence only** (and a tiny fraction of the `4·10¹⁸` range verified by
Oliveira e Silva, Herzog and Pardi); it is no progress towards the general statement. -/

/-- `noDiv n k = true` iff no `d ∈ [2, k + 1]` with `d * d ≤ n` divides `n`. -/
def noDiv (n : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => noDiv n k && (n < (k + 2) * (k + 2) || n % (k + 2) != 0)

theorem noDiv_spec {n : ℕ} : ∀ {k : ℕ}, noDiv n k = true →
    ∀ d, 2 ≤ d → d ≤ k + 1 → d * d ≤ n → ¬ d ∣ n
  | 0, _, d, h2, hd, _ => by omega
  | k + 1, h, d, h2, hd, hdn => by
    simp only [noDiv, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at h
    rcases Nat.lt_or_ge d (k + 2) with hlt | hge
    · exact noDiv_spec h.1 d h2 (by omega) hdn
    · have hd' : d = k + 2 := by omega
      subst hd'
      rcases h.2 with h' | h'
      · omega
      · exact fun hdvd => h' (Nat.mod_eq_zero_of_dvd hdvd)

/-- Trial-division primality test with divisor bound `K + 1`; only claims primality when
`n < (K + 2)²`. -/
def isPrimeB (K n : ℕ) : Bool :=
  decide (2 ≤ n) && decide (n < (K + 2) * (K + 2)) && noDiv n K

theorem isPrimeB_spec {K n : ℕ} (h : isPrimeB K n = true) : n.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h2, hK⟩, hnd⟩ := h
  refine Nat.prime_def_le_sqrt.2 ⟨h2, fun m hm2 hms => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.1 hms
  refine noDiv_spec hnd m hm2 ?_ hmm
  by_contra hlt
  have : (K + 2) * (K + 2) ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `findPair K N j = true` iff some `p ∈ [1, j]` has `p` and `N - p` passing the primality
test. -/
def findPair (K N : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => findPair K N j || (isPrimeB K (j + 1) && isPrimeB K (N - (j + 1)))

theorem findPair_spec {K N : ℕ} : ∀ {j : ℕ}, findPair K N j = true →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N
  | 0, h => by simp [findPair] at h
  | j + 1, h => by
    simp only [findPair, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact findPair_spec h
    · have hq := isPrimeB_spec h2
      have := hq.pos
      exact ⟨j + 1, N - (j + 1), isPrimeB_spec h1, hq, by omega⟩

/-- `checkFrom K J a M = true` iff `findPair` succeeds for the `M` even numbers
`a, a + 2, …, a + 2 (M - 1)`. -/
def checkFrom (K J a : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkFrom K J a m && findPair K (a + 2 * m) J

theorem checkFrom_spec {K J a : ℕ} : ∀ {M : ℕ}, checkFrom K J a M = true →
    ∀ i, i < M → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = a + 2 * i
  | 0, _, i, hi => by omega
  | m + 1, h, i, hi => by
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact checkFrom_spec h.1 i hlt
    · have : i = m := by omega
      subst this
      exact findPair_spec h.2

end Goldbach

namespace Goldbach

/-- The bound up to which Goldbach's conjecture is verified in this file. -/
def goldbachBound : ℕ := 1000

theorem check_goldbachBound : checkFrom 30 500 4 499 = true := by decide +kernel

/-- **Numerical evidence** (not progress on the general statement): Goldbach's conjecture holds
for every even `N` with `2 < N ≤ goldbachBound`. -/
theorem goldbach_upTo_bound (N : ℕ) (h2 : 2 < N) (he : Even N) (hN : N ≤ goldbachBound) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  obtain ⟨k, rfl⟩ := he
  have hN' : k + k ≤ 1000 := hN
  have := checkFrom_spec check_goldbachBound (k - 2) (by omega)
  rwa [show 4 + 2 * (k - 2) = k + k by omega] at this

end Goldbach
