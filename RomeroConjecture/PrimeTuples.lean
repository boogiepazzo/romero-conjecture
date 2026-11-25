import Mathlib

/-!
# The Hardy–Littlewood prime `k`-tuples conjecture (von Mangoldt form)

**STATUS: IN PROGRESS / NOT YET SOLVED.**  The prime `k`-tuples conjecture is an OPEN problem for
every `k ≥ 2` (already `k = 2`, `H = {0, 2}` contains the twin prime conjecture).  This file does
**not** prove it and does not claim to.  It contains a faithful formal *statement* of the
quantitative conjecture and of its qualitative form, and machine-checked *partial* results:
elementary facts about admissibility, the necessity of admissibility, convergence and positivity
of the singular series, the bound for the prime-power contribution, and implications between
open statements.  None of this is progress towards the conjecture itself.

## Statement

A finite set of shifts `H ⊂ ℕ`, `|H| = k`, is *admissible* if for every prime `p` the number
`ν_H(p)` of residue classes mod `p` occupied by `H` is `< p`.

> **Quantitative form** (`HardyLittlewoodTuples`).  For every admissible `H` with `k ≥ 2`,
> `∑_{n ≤ x} ∏_{h ∈ H} Λ(n + h) ∼ 𝔖(H) · x`,
> `𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^{-k}`.
>
> **Qualitative form** (`PrimeTuplesConjecture`).  For every nonempty admissible `H` there are
> infinitely many `n` with `n + h` prime for all `h ∈ H`.

## Attribution, dating and status (literature check, November 2026; uncertainty preserved)

* Quantitative form: G. H. Hardy and J. E. Littlewood, *Some problems of 'Partitio Numerorum';
  III: On the expression of a number as a sum of primes*, Acta Math. 44 (1923) 1–70
  ("Conjecture B" for pairs, the general `k`-tuple statement later in the paper; now usually called
  the *first Hardy–Littlewood conjecture*).  They state it for the counting function
  `π_H(x) ∼ 𝔖(H) ∫_2^x dt / log^k t`; the von Mangoldt form used here is the standard modern
  equivalent (by partial summation plus the prime-power bound proved below as
  `tupleSum_le_primeTupleSum_add`).  **That equivalence is not formalized here.**  We did not
  consult the primary source for the exact numbering/wording.
* Qualitative form: the special case of *Dickson's conjecture* for the monic forms `n + h`.
  L. E. Dickson, *A new extension of Dirichlet's theorem on prime numbers*, Messenger of Math. 33,
  155–161; the volume is dated 1904 in most citations, while Wikipedia says the conjecture was
  proposed in 1903 — we leave the year as "1903/04".  Dickson treats general linear forms
  `a_i n + b_i`.
* Generalizations: Schinzel–Sierpiński, Acta Arith. 4 (1958) (Hypothesis H, polynomials);
  Bateman–Horn, Math. Comp. 16 (1962) (quantitative Hypothesis H).  Twin primes and de Polignac's
  conjecture (1849) are special cases / consequences (see below for which form of Polignac).
* Incompatibility with the "second Hardy–Littlewood conjecture" `π(x+y) ≤ π(x) + π(y)`:
  D. Hensley and I. Richards, *Primes in intervals*, Acta Arith. 25 (1973/74) 375–391, and
  I. Richards, Bull. AMS 80 (1974) 419–438: the qualitative `k`-tuples conjecture contradicts it
  (there are admissible tuples in an interval of length `y` with more than `π(y)` elements).  The
  first conjecture is the one generally believed.
* P. X. Gallagher, *On the distribution of primes in short intervals*, Mathematika 23 (1976):
  a uniform form of the conjecture implies Poisson statistics for primes in intervals of length
  `λ log x`; the key input is that `𝔖` has mean value `1` over `k`-tuples.
* Partial results towards the *qualitative* form (none formalized here):
  Goldston–Pintz–Yıldırım (Ann. of Math. 2009): `liminf (p_{n+1}-p_n)/log p_n = 0`;
  Y. Zhang (Ann. of Math. 2014; announced 2013): bounded gaps (`< 7·10⁷`), i.e. for large `k`
  every admissible `k`-tuple contains two primes infinitely often;
  J. Maynard (Ann. of Math. 181 (2015) 383–413) and, independently, T. Tao (unpublished, 2013):
  for every `m` there is `k_m` such that for every admissible `k`-tuple with `k ≥ k_m`, at least
  `m` of the `n + h_i` are simultaneously prime for infinitely many `n`;
  Polymath8b (Res. Math. Sci. 2014): `liminf (p_{n+1} - p_n) ≤ 246`.
  No single admissible `k`-tuple with `k ≥ 2` is known to be all-prime infinitely often.
  Upper bounds of the conjectured order (with a worse constant) follow from sieve methods.
* The only proved case of the asymptotic for an admissible tuple is `k = 1` (the prime number
  theorem).  As of late 2026 the conjecture is, to our knowledge, open for all `k ≥ 2`.  Claimed
  proofs of the twin prime conjecture continue to appear on preprint servers (e.g. several
  2026 postings on arXiv/Zenodo/Cambridge Open Engage); we found no evidence that any has been
  accepted by the community.

## What is proved in this file (all machine-checked, no `sorry`, no extra axioms)

* `ν` and admissibility: `ν_le_card`, `ν_le_self`, `ν_le_min`, `ν_mono`,
  `ν_eq_card_of_diff_lt` / `ν_eq_card_of_sup_lt` (`ν_H(p) = k` once `p` exceeds all differences),
  `ν_image_add` and `admissible_image_add` (translation invariance), `Admissible.subset`,
  `admissible_iff_forall_le_card` (only primes `p ≤ k` matter), a `Decidable (Admissible H)`
  instance, and kernel-checked (`decide`) examples: `{0,2}`, `{0,2,6}`, `{0,4,6}`, `{0,2,6,8}`,
  `{0,2,6,8,12}`, `{0,4,6,10,12,16}`, `{0,6,12,18}` admissible; `{0,2,4}`, `{0,1}`,
  `{0,2,6,8,12,14}` not.  `admissible_pair_even`: `{0, 2m}` is admissible.
* Necessity of admissibility: `exists_dvd_of_ν_ge`, `exists_eq_prime_of_not_admissible`,
  `le_card_of_not_admissible` (if `H` is not admissible and all `n + h` are prime then `n ≤ k`),
  `finite_of_not_admissible`, `admissible_of_infinite`.
* Trivial bound: `tupleSum_le_mul_log_pow` (`tupleSum H x ≤ x · log(x + max H)^k`, `x ≥ 1`).
* Prime powers: `tupleSum_le_primeTupleSum_add` — for nonempty `H`, `x ≥ 1`,
  `primeTupleSum H x ≤ tupleSum H x ≤ primeTupleSum H x + 2k √(x + max H) log(x + max H)^k`,
  where `primeTupleSum` only counts `n` with all `n + h` prime (uses mathlib's
  `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`).
* `tendsto_tupleSum_div_zero_of_finite`: finitely many prime tuples ⇒ `tupleSum H x = o(x)`.
* Singular series: `summable_localFactor_sub_one`, `multipliable_localFactor`,
  `hasProd_singularSeries` (the Euler product converges absolutely for **every** `H`, so the
  `tprod` in the definition never takes its junk value), `abs_localFactor_sub_one_le`
  (`|factor_p - 1| ≤ k² 2^k / p²` for `p > max H`), `localFactor_pos`, `localFactor_eq_zero`,
  **`singularSeries_pos`** (`𝔖 H > 0` for admissible `H`), `singularSeries_eq_zero`
  (`𝔖 H = 0` otherwise), `singularSeries_pos_iff`, `singularSeries_empty`,
  `singularSeries_singleton` (`𝔖 {h} = 1`), `localFactor_twin_two` (`= 2`),
  `localFactor_twin_odd` (`= 1 - 1/(p-1)²`).
* Consistency of the modelling: `hardyLittlewoodAsymptotic_empty` (`k = 0`),
  `hardyLittlewoodAsymptotic_of_not_admissible` (the asymptotic is a *theorem*, with limit `0`,
  for non-admissible `H`), hence `hardyLittlewoodTuples_iff` (the admissibility hypothesis may
  be dropped from the statement).
* Implications between OPEN statements (conditional results only):
  `infinite_of_asymptotic`, **`HardyLittlewoodTuples.primeTuples`** (quantitative ⇒
  qualitative, with genuine primes, not prime powers), `PrimeTuplesConjecture.twinPrime`,
  `PrimeTuplesConjecture.weakPolignac`, `PrimeTuplesConjecture.infinite_iff`,
  `HardyLittlewoodTuples.twinPrime`, `HardyLittlewoodTuples.weakPolignac`,
  `PolignacConjecture.weakPolignac`, `PolignacConjecture.twinPrime`.

## What is NOT proved (stated only, as `def … : Prop`)

* `HardyLittlewoodTuples`, `PrimeTuplesConjecture`, `TwinPrimeConjecture`,
  `WeakPolignacConjecture`, `PolignacConjecture` — all open.
* `PrimeNumberTheoremForm` (the case `k = 1`) — a theorem (1896), but not proved here and not
  used.
* **Polignac.**  De Polignac's conjecture is usually stated for *consecutive* primes
  (`PolignacConjecture`).  What is proved here from the qualitative `k`-tuples conjecture is only
  the weak form (`WeakPolignacConjecture`: `p`, `p + 2m` both prime, not necessarily
  consecutive).  The consecutive form should also follow from the qualitative conjecture by a
  covering argument (enlarge `{0, 2m}` to an admissible tuple whose extra shifts force, for each
  `0 < j < 2m`, a fixed prime `q_j > 2m` to divide `n + j`); this is only a sketch, it is
  **neither formalized nor carefully checked here**, and no implication to `PolignacConjecture`
  is claimed.
* The equivalence of the von Mangoldt form with Hardy and Littlewood's original `π`-count form,
  any numerical value of `𝔖`, the product formula `𝔖 {0,2} = 2 ∏_{p>2} (1 - 1/(p-1)²)` as a
  single identity (only the local factors are computed), and all the analytic theorems quoted
  above (PNT, GPY, Zhang, Maynard–Tao, Polymath8b, Gallagher, Hensley–Richards).

## Modelling choices

* Tuples are `Finset ℕ` of shifts (so shifts are distinct and non-negative; by
  `admissible_image_add` nothing is lost up to translation).  `k = H.card`.
* `tupleSum H x = ∑_{1 ≤ n ≤ ⌊x⌋} ∏_{h ∈ H} Λ(n + h)`; the asymptotic is expressed as
  `tupleSum H x / x → 𝔖 H` as `x → ∞` (real `x`).
* `𝔖 H` is a `tprod` over `Nat.Primes`.  Mathlib's `∏'` returns `1` for non-multipliable
  families; this is irrelevant here because multipliability is proved for all `H`.
* `HardyLittlewoodTuples` is stated for `2 ≤ H.card`.  The case `k = 1` is the prime number
  theorem (`PrimeNumberTheoremForm`), `k = 0` is trivial (`hardyLittlewoodAsymptotic_empty`).
  Including `k = 1` would make the statement "PNT ∧ conjecture"; we keep them apart.
* The quantitative conjecture here has no error term and no uniformity in `H`; the forms used by
  Gallagher and in Montgomery–Soundararajan-type applications need uniformity in `H` and are
  strictly stronger.
-/

open Finset ArithmeticFunction Filter Topology Chebyshev

namespace PrimeTuples

/-! ## Definitions -/

/-- `ν H p`: the number of residue classes modulo `p` occupied by the shifts `H`. -/
def ν (H : Finset ℕ) (p : ℕ) : ℕ := (H.image (· % p)).card

/-- A tuple of shifts `H` is *admissible* if for every prime `p` it misses at least one residue
class modulo `p`. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ν H p < p

/-- The von Mangoldt-weighted count of `n ≤ x` with all `n + h` (`h ∈ H`) prime powers:
`∑_{1 ≤ n ≤ x} ∏_{h ∈ H} Λ(n + h)`. -/
noncomputable def tupleSum (H : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ∏ h ∈ H, Λ (n + h)

/-- The local factor at `p` of the singular series: `(1 - ν_H(p)/p) (1 - 1/p)^{-k}`, `k = |H|`. -/
noncomputable def localFactor (H : Finset ℕ) (p : ℕ) : ℝ :=
  (1 - (ν H p : ℝ) / p) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- The Hardy–Littlewood singular series `𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^{-k}`, as an
(unconditional) infinite product `∏'` over the primes.  See `multipliable_localFactor`,
`hasProd_singularSeries`: the product does converge (absolutely) for every `H`, so no junk value
is involved. -/
noncomputable def singularSeries (H : Finset ℕ) : ℝ := ∏' p : Nat.Primes, localFactor H p

@[inherit_doc] scoped notation "𝔖" => singularSeries

/-- **Hardy–Littlewood prime `k`-tuples conjecture** (OPEN; von Mangoldt form), for `k ≥ 2`:
for every admissible `H` with `|H| ≥ 2`,
`∑_{n ≤ x} ∏_{h ∈ H} Λ(n + h) ∼ 𝔖(H) · x`. -/
def HardyLittlewoodTuples : Prop :=
  ∀ H : Finset ℕ, 2 ≤ H.card → Admissible H →
    Tendsto (fun x : ℝ => tupleSum H x / x) atTop (𝓝 (𝔖 H))

/-- The same asymptotic for a single tuple `H`. -/
def HardyLittlewoodAsymptotic (H : Finset ℕ) : Prop :=
  Tendsto (fun x : ℝ => tupleSum H x / x) atTop (𝓝 (𝔖 H))

/-- The case `k = 1` of the asymptotic, which is (equivalent to) the prime number theorem
`ψ(x) ∼ x`.  A theorem (Hadamard, de la Vallée Poussin 1896), but NOT proved in this file. -/
def PrimeNumberTheoremForm : Prop :=
  ∀ h : ℕ, HardyLittlewoodAsymptotic {h}

/-- **Prime `k`-tuples conjecture, qualitative form** (OPEN; Dickson's conjecture for the monic
linear forms `n + h`): for every nonempty admissible `H` there are infinitely many `n` with all
`n + h`, `h ∈ H`, prime. -/
def PrimeTuplesConjecture : Prop :=
  ∀ H : Finset ℕ, Admissible H → H.Nonempty → {n : ℕ | ∀ h ∈ H, (n + h).Prime}.Infinite

/-- **Twin prime conjecture** (OPEN). -/
def TwinPrimeConjecture : Prop := {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite

/-- **Weak Polignac** (OPEN): every positive even number `2m` is the difference of two primes
in infinitely many ways (the primes need not be consecutive). -/
def WeakPolignacConjecture : Prop :=
  ∀ m : ℕ, 1 ≤ m → {p : ℕ | p.Prime ∧ (p + 2 * m).Prime}.Infinite

/-- **Polignac's conjecture** (OPEN; de Polignac 1849), in its usual form: every positive even
number `2m` occurs infinitely often as a gap between *consecutive* primes. -/
def PolignacConjecture : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    {p : ℕ | p.Prime ∧ (p + 2 * m).Prime ∧ ∀ q, p < q → q < p + 2 * m → ¬q.Prime}.Infinite

/-! ## Elementary facts about `ν` and admissibility -/

theorem ν_le_card (H : Finset ℕ) (p : ℕ) : ν H p ≤ H.card := card_image_le

theorem ν_le_self (H : Finset ℕ) {p : ℕ} (hp : 0 < p) : ν H p ≤ p := by
  have : H.image (· % p) ⊆ range p := by
    intro r hr
    obtain ⟨h, -, rfl⟩ := mem_image.1 hr
    exact mem_range.2 (Nat.mod_lt _ hp)
  simpa [ν] using card_le_card this

theorem ν_le_min (H : Finset ℕ) {p : ℕ} (hp : 0 < p) : ν H p ≤ min H.card p :=
  le_min (ν_le_card H p) (ν_le_self H hp)

theorem ν_mono {H H' : Finset ℕ} (h : H ⊆ H') (p : ℕ) : ν H p ≤ ν H' p :=
  card_le_card (image_subset_image h)

@[simp] theorem ν_empty (p : ℕ) : ν ∅ p = 0 := by simp [ν]

@[simp] theorem ν_singleton (h p : ℕ) : ν {h} p = 1 := by simp [ν]

theorem ν_pos {H : Finset ℕ} (hH : H.Nonempty) (p : ℕ) : 0 < ν H p :=
  card_pos.2 (hH.image _)

/-- If all differences of elements of `H` are smaller than `p`, the elements of `H` are pairwise
incongruent mod `p`, so `ν H p = |H|`. -/
theorem ν_eq_card_of_diff_lt {H : Finset ℕ} {p : ℕ} (h : ∀ a ∈ H, ∀ b ∈ H, a < b + p) :
    ν H p = H.card := by
  refine card_image_of_injOn fun a ha b hb hab => ?_
  have hab' : a ≡ b [MOD p] := hab
  rcases le_total a b with hle | hle
  · have hd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).1 hab'
    have hlt : b - a < p := by have := h b hb a ha; omega
    have := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  · have hd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).1 hab'.symm
    have hlt : a - b < p := by have := h a ha b hb; omega
    have := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega

/-- For `p` larger than every shift, `ν H p = |H|`. -/
theorem ν_eq_card_of_sup_lt {H : Finset ℕ} {p : ℕ} (h : H.sup id < p) : ν H p = H.card :=
  ν_eq_card_of_diff_lt fun a ha b _ => by
    have : a ≤ H.sup id := le_sup (f := id) ha
    omega

/-- `ν` is invariant under translation of the tuple. -/
theorem ν_image_add (H : Finset ℕ) (a p : ℕ) : ν (H.image (· + a)) p = ν H p := by
  unfold ν
  have : (H.image (· + a)).image (· % p) = (H.image (· % p)).image (fun r => (r + a) % p) := by
    simp only [image_image]
    refine image_congr fun h _ => ?_
    simp [Function.comp, Nat.add_mod]
  rw [this]
  refine card_image_of_injOn fun r hr s hs hrs => ?_
  obtain ⟨h, -, rfl⟩ := mem_image.1 (mem_coe.1 hr)
  obtain ⟨h', -, rfl⟩ := mem_image.1 (mem_coe.1 hs)
  have h1 : h % p + a ≡ h' % p + a [MOD p] := hrs
  have h2 : h % p ≡ h' % p [MOD p] := Nat.ModEq.add_right_cancel' a h1
  simpa [Nat.ModEq] using h2

/-- Admissibility is translation invariant. -/
theorem admissible_image_add (H : Finset ℕ) (a : ℕ) :
    Admissible (H.image (· + a)) ↔ Admissible H := by
  simp [Admissible, ν_image_add]

/-- Subsets of admissible tuples are admissible. -/
theorem Admissible.subset {H H' : Finset ℕ} (h' : Admissible H') (h : H ⊆ H') : Admissible H :=
  fun p hp => (ν_mono h p).trans_lt (h' p hp)

/-- Admissibility only needs to be checked at the primes `p ≤ |H|`. -/
theorem admissible_iff_forall_le_card (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → ν H p < p := by
  refine ⟨fun h p hp _ => h p hp, fun h p hp => ?_⟩
  rcases le_or_gt p H.card with hle | hlt
  · exact h p hp hle
  · exact (ν_le_card H p).trans_lt hlt

/-- Finite form of the admissibility test, used for the `Decidable` instance. -/
theorem forall_mem_range_iff_admissible (H : Finset ℕ) :
    (∀ p ∈ range (H.card + 1), p.Prime → ν H p < p) ↔ Admissible H := by
  rw [admissible_iff_forall_le_card]
  refine forall_congr' fun p => ?_
  rw [mem_range, Nat.lt_succ_iff]
  tauto

instance (H : Finset ℕ) : Decidable (Admissible H) :=
  decidable_of_iff _ (forall_mem_range_iff_admissible H)

theorem admissible_empty : Admissible ∅ := fun p hp => by simpa using hp.pos

theorem admissible_singleton (h : ℕ) : Admissible {h} := fun p hp => by simpa using hp.one_lt

/-- `{0, 2m}` is admissible for `m ≥ 1`... and in fact for every `m`. -/
theorem admissible_pair_even (m : ℕ) : Admissible {0, 2 * m} := by
  rw [admissible_iff_forall_le_card]
  intro p hp hle
  have hc : ({0, 2 * m} : Finset ℕ).card ≤ 2 := card_insert_le _ _ |>.trans (by simp)
  have hp2 : p = 2 := le_antisymm (hle.trans hc) hp.two_le
  subst hp2
  have : ({0, 2 * m} : Finset ℕ).image (· % 2) = {0} := by
    ext r; simp
  simp [ν, this]

/-! ### Examples (kernel-checked by `decide`) -/

example : Admissible {0, 2} := by decide
example : Admissible {0, 2, 6} := by decide
example : Admissible {0, 4, 6} := by decide
example : Admissible {0, 2, 6, 8} := by decide
example : Admissible {0, 2, 6, 8, 12} := by decide
example : Admissible {0, 4, 6, 10, 12, 16} := by decide
example : Admissible {0, 6, 12, 18} := by decide
example : ¬Admissible {0, 2, 4} := by decide
example : ¬Admissible {0, 1} := by decide
example : ¬Admissible {0, 2, 6, 8, 12, 14} := by decide

/-! ## Necessity of admissibility -/

/-- If `ν H p = p` (all residue classes are occupied), then for every `n` some `n + h` is
divisible by `p`. -/
theorem exists_dvd_of_ν_ge {H : Finset ℕ} {p : ℕ} (hp : 0 < p) (hν : p ≤ ν H p) (n : ℕ) :
    ∃ h ∈ H, p ∣ n + h := by
  have hsub : H.image (· % p) ⊆ range p := by
    intro r hr
    obtain ⟨h, -, rfl⟩ := mem_image.1 hr
    exact mem_range.2 (Nat.mod_lt _ hp)
  have heq : H.image (· % p) = range p := eq_of_subset_of_card_le hsub (by simpa [ν] using hν)
  have hmem : (p - n % p) % p ∈ H.image (· % p) := by
    rw [heq]; exact mem_range.2 (Nat.mod_lt _ hp)
  obtain ⟨h, hh, hmod⟩ := mem_image.1 hmem
  refine ⟨h, hh, ?_⟩
  have hlt := Nat.mod_lt n hp
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod, Nat.add_mod_mod]
  have : n % p + (p - n % p) = p := by omega
  rw [this, Nat.mod_self]

/-- **Necessity of admissibility, explicit form.**  If `H` is not admissible and all `n + h`
(`h ∈ H`) are prime, then some `n + h` is a prime `p ≤ |H|`; in particular `n ≤ |H|`. -/
theorem exists_eq_prime_of_not_admissible {H : Finset ℕ} (hH : ¬Admissible H) {n : ℕ}
    (hn : ∀ h ∈ H, (n + h).Prime) : ∃ h ∈ H, n + h ≤ H.card := by
  simp only [Admissible, not_forall, not_lt] at hH
  obtain ⟨p, hp, hν⟩ := hH
  obtain ⟨h, hh, hdvd⟩ := exists_dvd_of_ν_ge hp.pos hν n
  refine ⟨h, hh, ?_⟩
  have : p = n + h := ((Nat.prime_dvd_prime_iff_eq hp (hn h hh)).1 hdvd)
  exact this ▸ hν.trans (ν_le_card H p)

theorem le_card_of_not_admissible {H : Finset ℕ} (hH : ¬Admissible H) {n : ℕ}
    (hn : ∀ h ∈ H, (n + h).Prime) : n ≤ H.card := by
  obtain ⟨h, -, hle⟩ := exists_eq_prime_of_not_admissible hH hn
  omega

/-- **Necessity of admissibility.**  If `H` is not admissible, only finitely many `n` have all
`n + h` prime (indeed all such `n` are `≤ |H|`). -/
theorem finite_of_not_admissible {H : Finset ℕ} (hH : ¬Admissible H) :
    {n : ℕ | ∀ h ∈ H, (n + h).Prime}.Finite :=
  (Set.finite_Iic H.card).subset fun _ hn => le_card_of_not_admissible hH hn

/-- Hence the admissibility hypothesis in the qualitative conjecture is exactly right: the
conclusion of `PrimeTuplesConjecture` for a nonempty `H` forces `H` to be admissible. -/
theorem admissible_of_infinite {H : Finset ℕ}
    (h : {n : ℕ | ∀ h ∈ H, (n + h).Prime}.Infinite) : Admissible H :=
  by_contra fun hH => h (finite_of_not_admissible hH)

/-! ## Consequences of the qualitative conjecture -/

theorem PrimeTuplesConjecture.weakPolignac (h : PrimeTuplesConjecture) :
    WeakPolignacConjecture := by
  intro m _
  have := h {0, 2 * m} (admissible_pair_even m) (by simp)
  refine this.mono fun n hn => ?_
  exact ⟨by simpa using hn 0 (by simp), hn (2 * m) (by simp)⟩

theorem WeakPolignacConjecture.twinPrime (h : WeakPolignacConjecture) : TwinPrimeConjecture := by
  simpa [TwinPrimeConjecture] using h 1 le_rfl

theorem PrimeTuplesConjecture.twinPrime (h : PrimeTuplesConjecture) : TwinPrimeConjecture :=
  h.weakPolignac.twinPrime

/-- The usual (consecutive-primes) Polignac conjecture implies the weak form. -/
theorem PolignacConjecture.weakPolignac (h : PolignacConjecture) : WeakPolignacConjecture :=
  fun m hm => (h m hm).mono (by rintro p ⟨h1, h2, -⟩; exact ⟨h1, h2⟩)

/-- For gap `2` the two forms of Polignac coincide: both are the twin prime conjecture. -/
theorem PolignacConjecture.twinPrime (h : PolignacConjecture) : TwinPrimeConjecture :=
  h.weakPolignac.twinPrime

/-! ## The trivial upper bound -/

theorem tupleSum_nonneg (H : Finset ℕ) (x : ℝ) : 0 ≤ tupleSum H x :=
  sum_nonneg fun _ _ => prod_nonneg fun _ _ => vonMangoldt_nonneg

theorem prod_vonMangoldt_le_pow {H' : Finset ℕ} {M N n : ℕ} (hH' : ∀ h ∈ H', h ≤ M)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    ∏ h ∈ H', Λ (n + h) ≤ Real.log ((N + M : ℕ) : ℝ) ^ H'.card := by
  rw [← prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => vonMangoldt_nonneg) fun h hh => ?_
  refine vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
  · exact_mod_cast (by omega : 0 < n + h)
  · exact_mod_cast (by have := hH' h hh; omega : n + h ≤ N + M)

/-- **Trivial bound**: `∑_{n ≤ x} ∏_{h ∈ H} Λ(n+h) ≤ x · log(x + max H)^k` for `x ≥ 1`. -/
theorem tupleSum_le_mul_log_pow (H : Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    tupleSum H x ≤ x * Real.log (x + (H.sup id : ℕ)) ^ H.card := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hN : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.2 hx
  have hL0 : 0 ≤ Real.log ((⌊x⌋₊ + H.sup id : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hLL : Real.log ((⌊x⌋₊ + H.sup id : ℕ) : ℝ) ≤ Real.log (x + (H.sup id : ℕ)) := by
    refine Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊ + H.sup id)) ?_
    push_cast; linarith
  calc tupleSum H x
      ≤ ∑ _n ∈ Icc 1 ⌊x⌋₊, Real.log ((⌊x⌋₊ + H.sup id : ℕ) : ℝ) ^ H.card :=
        sum_le_sum fun n hn => prod_vonMangoldt_le_pow (fun h hh => le_sup (f := id) hh)
          (mem_Icc.1 hn).1 (mem_Icc.1 hn).2
    _ = ⌊x⌋₊ * Real.log ((⌊x⌋₊ + H.sup id : ℕ) : ℝ) ^ H.card := by simp
    _ ≤ x * Real.log (x + (H.sup id : ℕ)) ^ H.card :=
        mul_le_mul hfl (pow_le_pow_left₀ hL0 hLL _) (pow_nonneg hL0 _) hx0

/-! ## The contribution of proper prime powers is `O(√x log^k x)` -/

/-- von Mangoldt restricted to non-primes (i.e. supported on proper prime powers). -/
noncomputable def vonMangoldtNonPrime (m : ℕ) : ℝ := if ¬m.Prime then Λ m else 0

theorem vonMangoldtNonPrime_nonneg (m : ℕ) : 0 ≤ vonMangoldtNonPrime m := by
  unfold vonMangoldtNonPrime
  split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl

theorem sum_vonMangoldtNonPrime (N : ℕ) :
    ∑ m ∈ Ioc 0 N, vonMangoldtNonPrime m = ψ N - θ N := by
  rw [psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]; rfl

theorem sum_vonMangoldtNonPrime_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Ioc 0 N, vonMangoldtNonPrime m ≤ 2 * √(N : ℝ) * Real.log N := by
  rw [sum_vonMangoldtNonPrime]
  exact (le_abs_self _).trans (abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hN))

theorem prod_vonMangoldt_le_ite_add {H : Finset ℕ} {M N n : ℕ} (hM : ∀ h ∈ H, h ≤ M)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    ∏ h ∈ H, Λ (n + h) ≤ (if ∀ h ∈ H, (n + h).Prime then ∏ h ∈ H, Λ (n + h) else 0)
      + Real.log ((N + M : ℕ) : ℝ) ^ (H.card - 1) * ∑ h ∈ H, vonMangoldtNonPrime (n + h) := by
  have hL : 0 ≤ Real.log ((N + M : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h2 : 0 ≤ Real.log ((N + M : ℕ) : ℝ) ^ (H.card - 1)
      * ∑ h ∈ H, vonMangoldtNonPrime (n + h) :=
    mul_nonneg (pow_nonneg hL _) (sum_nonneg fun _ _ => vonMangoldtNonPrime_nonneg _)
  split_ifs with hall
  · linarith
  · push Not at hall
    obtain ⟨h0, hh0, hnot⟩ := hall
    rw [zero_add, ← mul_prod_erase H _ hh0]
    have e1 : Λ (n + h0) = vonMangoldtNonPrime (n + h0) := by simp [vonMangoldtNonPrime, hnot]
    have e2 : ∏ h ∈ H.erase h0, Λ (n + h) ≤ Real.log ((N + M : ℕ) : ℝ) ^ (H.card - 1) := by
      have := prod_vonMangoldt_le_pow (H' := H.erase h0) (M := M)
        (fun h hh => hM h (mem_of_mem_erase hh)) hn1 hnN
      rwa [card_erase_of_mem hh0] at this
    calc Λ (n + h0) * ∏ h ∈ H.erase h0, Λ (n + h)
        ≤ vonMangoldtNonPrime (n + h0) * Real.log ((N + M : ℕ) : ℝ) ^ (H.card - 1) := by
          rw [e1]; exact mul_le_mul_of_nonneg_left e2 (vonMangoldtNonPrime_nonneg _)
      _ ≤ (∑ h ∈ H, vonMangoldtNonPrime (n + h)) * Real.log ((N + M : ℕ) : ℝ) ^ (H.card - 1) :=
          mul_le_mul_of_nonneg_right
            (single_le_sum (fun i _ => vonMangoldtNonPrime_nonneg (n + i)) hh0) (pow_nonneg hL _)
      _ = _ := mul_comm _ _

theorem sum_shift_vonMangoldtNonPrime_le {M N h : ℕ} (hh : h ≤ M) :
    ∑ n ∈ Icc 1 N, vonMangoldtNonPrime (n + h) ≤ ∑ m ∈ Ioc 0 (N + M), vonMangoldtNonPrime m := by
  have hinj : Set.InjOn (· + h) (Icc 1 N : Set ℕ) := fun a _ b _ hab => by simpa using hab
  rw [← sum_image (f := vonMangoldtNonPrime) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldtNonPrime_nonneg _
  intro m hm
  obtain ⟨n, hn, rfl⟩ := mem_image.1 hm
  have := mem_Icc.1 hn
  exact mem_Ioc.2 ⟨by omega, by omega⟩

/-- The von Mangoldt-weighted count over `n ≤ N` exceeds the part coming from genuine prime
tuples by at most `2 k √(N+M) log^k (N+M)` (`M` any bound for the shifts). -/
theorem sum_prod_vonMangoldt_le {H : Finset ℕ} (hH : H.Nonempty) {M N : ℕ}
    (hM : ∀ h ∈ H, h ≤ M) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, ∏ h ∈ H, Λ (n + h) ≤
      ∑ n ∈ Icc 1 N with ∀ h ∈ H, (n + h).Prime, ∏ h ∈ H, Λ (n + h)
      + 2 * H.card * √((N + M : ℕ) : ℝ) * Real.log ((N + M : ℕ) : ℝ) ^ H.card := by
  set L := Real.log ((N + M : ℕ) : ℝ) with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have hk : H.card ≠ 0 := card_ne_zero.2 hH
  have hinner : ∑ n ∈ Icc 1 N, ∑ h ∈ H, vonMangoldtNonPrime (n + h)
      ≤ H.card * (2 * √((N + M : ℕ) : ℝ) * L) := by
    rw [sum_comm]
    calc ∑ h ∈ H, ∑ n ∈ Icc 1 N, vonMangoldtNonPrime (n + h)
        ≤ ∑ _h ∈ H, 2 * √((N + M : ℕ) : ℝ) * L :=
          sum_le_sum fun h hh => (sum_shift_vonMangoldtNonPrime_le (hM h hh)).trans
            (sum_vonMangoldtNonPrime_le (by omega))
      _ = H.card * (2 * √((N + M : ℕ) : ℝ) * L) := by simp
  calc ∑ n ∈ Icc 1 N, ∏ h ∈ H, Λ (n + h)
      ≤ ∑ n ∈ Icc 1 N, ((if ∀ h ∈ H, (n + h).Prime then ∏ h ∈ H, Λ (n + h) else 0)
          + L ^ (H.card - 1) * ∑ h ∈ H, vonMangoldtNonPrime (n + h)) :=
        sum_le_sum fun n hn => prod_vonMangoldt_le_ite_add hM (mem_Icc.1 hn).1 (mem_Icc.1 hn).2
    _ = ∑ n ∈ Icc 1 N with ∀ h ∈ H, (n + h).Prime, ∏ h ∈ H, Λ (n + h)
          + L ^ (H.card - 1) * ∑ n ∈ Icc 1 N, ∑ h ∈ H, vonMangoldtNonPrime (n + h) := by
        rw [sum_add_distrib, sum_filter, mul_sum]
    _ ≤ ∑ n ∈ Icc 1 N with ∀ h ∈ H, (n + h).Prime, ∏ h ∈ H, Λ (n + h)
          + L ^ (H.card - 1) * (H.card * (2 * √((N + M : ℕ) : ℝ) * L)) := by
        gcongr
    _ = _ := by
        rw [← pow_sub_one_mul hk L]; ring

/-- The part of `tupleSum` coming from genuine prime tuples:
`∑_{n ≤ x, all n+h prime} ∏_{h ∈ H} log(n+h)`. -/
noncomputable def primeTupleSum (H : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊ with ∀ h ∈ H, (n + h).Prime, ∏ h ∈ H, Real.log ((n + h : ℕ) : ℝ)

theorem primeTupleSum_eq (H : Finset ℕ) (x : ℝ) :
    primeTupleSum H x = ∑ n ∈ Icc 1 ⌊x⌋₊ with ∀ h ∈ H, (n + h).Prime, ∏ h ∈ H, Λ (n + h) :=
  sum_congr rfl fun _ hn => prod_congr rfl fun h hh =>
    (vonMangoldt_apply_prime ((mem_filter.1 hn).2 h hh)).symm

theorem primeTupleSum_le_tupleSum (H : Finset ℕ) (x : ℝ) : primeTupleSum H x ≤ tupleSum H x := by
  rw [primeTupleSum_eq]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun _ _ _ => prod_nonneg fun _ _ => vonMangoldt_nonneg

/-- **Prime powers contribute `O(√x log^k x)`.**  For nonempty `H` and `x ≥ 1`,
`tupleSum H x ≤ primeTupleSum H x + 2 k √(x + max H) · log(x + max H)^k`. -/
theorem tupleSum_le_primeTupleSum_add {H : Finset ℕ} (hH : H.Nonempty) {x : ℝ} (hx : 1 ≤ x) :
    tupleSum H x ≤ primeTupleSum H x
      + 2 * H.card * √(x + (H.sup id : ℕ)) * Real.log (x + (H.sup id : ℕ)) ^ H.card := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hN : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.2 hx
  have hL0 : 0 ≤ Real.log ((⌊x⌋₊ + H.sup id : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hcast : ((⌊x⌋₊ + H.sup id : ℕ) : ℝ) ≤ x + (H.sup id : ℕ) := by push_cast; linarith
  have hLL : Real.log ((⌊x⌋₊ + H.sup id : ℕ) : ℝ) ≤ Real.log (x + (H.sup id : ℕ)) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊ + H.sup id)) hcast
  rw [primeTupleSum_eq]
  refine (sum_prod_vonMangoldt_le hH (fun h hh => le_sup (f := id) hh) hN).trans ?_
  gcongr

/-! ## Finitely many prime tuples ⇒ `tupleSum H x = o(x)` -/

theorem tendsto_log_pow_div_sqrt (k : ℕ) :
    Tendsto (fun y : ℝ => Real.log y ^ k / √y) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr fun y => ?_
  rw [Real.rpow_natCast, Real.sqrt_eq_rpow]

/-- If only finitely many `n` have all `n + h` prime, then `tupleSum H x / x → 0`. -/
theorem tendsto_tupleSum_div_zero_of_finite {H : Finset ℕ} (hH : H.Nonempty)
    (hfin : {n : ℕ | ∀ h ∈ H, (n + h).Prime}.Finite) :
    Tendsto (fun x : ℝ => tupleSum H x / x) atTop (𝓝 0) := by
  set M : ℝ := ((H.sup id : ℕ) : ℝ) with hMdef
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  set C : ℝ := ∑ n ∈ hfin.toFinset, ∏ h ∈ H, Real.log ((n + h : ℕ) : ℝ) with hC
  have hCle : ∀ x, primeTupleSum H x ≤ C := fun x => by
    refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
      fun _ _ _ => prod_nonneg fun _ _ => Real.log_natCast_nonneg _
    exact hfin.mem_toFinset.2 (mem_filter.1 hn).2
  set F : ℝ → ℝ := fun x => C / x + 2 * H.card *
    (Real.log (x + M) ^ H.card / √(x + M) * (1 + M / x)) with hF
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => C / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun x : ℝ => Real.log (x + M) ^ H.card / √(x + M)) atTop (𝓝 0) :=
      (tendsto_log_pow_div_sqrt H.card).comp (tendsto_atTop_add_const_right _ M tendsto_id)
    have h3 : Tendsto (fun x : ℝ => 1 + M / x) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    have := h1.add ((h2.mul h3).const_mul (2 * (H.card : ℝ)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hFlim
    (Eventually.of_forall fun x => ?_) ?_
  · by_cases hx : 0 ≤ x
    · exact div_nonneg (tupleSum_nonneg H x) hx
    · have : tupleSum H x = 0 := by
        simp [tupleSum, Nat.floor_of_nonpos (le_of_not_ge hx)]
      simp [this]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < x + M := by linarith
    have hs0 : 0 < √(x + M) := Real.sqrt_pos.2 hy0
    have hss : √(x + M) * √(x + M) = x + M := Real.mul_self_sqrt hy0.le
    have hb := (tupleSum_le_primeTupleSum_add hH hx).trans (add_le_add_left (hCle x) _)
    rw [div_le_iff₀ hx0]
    refine hb.trans (le_of_eq ?_)
    have e : 1 + M / x = √(x + M) * √(x + M) / x := by rw [hss]; field_simp
    simp only [hF, e]
    field_simp
    ring

/-- **Quantitative ⇒ qualitative (single tuple).**  If the Hardy–Littlewood asymptotic holds
for a nonempty `H` whose singular series is positive, then infinitely many `n` have all `n + h`
(`h ∈ H`) *prime* (not merely prime powers). -/
theorem infinite_of_asymptotic {H : Finset ℕ} (hH : H.Nonempty) (hpos : 0 < 𝔖 H)
    (h : HardyLittlewoodAsymptotic H) : {n : ℕ | ∀ h ∈ H, (n + h).Prime}.Infinite := by
  intro hfin
  have := tendsto_nhds_unique h (tendsto_tupleSum_div_zero_of_finite hH hfin)
  exact hpos.ne' this

/-! ## The singular series -/

theorem localFactor_eq (H : Finset ℕ) (p : ℕ) :
    localFactor H p = (1 - (ν H p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card := by
  rw [localFactor, zpow_neg, zpow_natCast, ← div_eq_mul_inv]

theorem localFactor_pos {H : Finset ℕ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [localFactor_eq]
  refine div_pos ?_ (pow_pos ?_ _)
  · rw [sub_pos, div_lt_one hp0]; exact_mod_cast hH p hp
  · rw [sub_pos, div_lt_one hp0]; exact hp1

/-- At an obstructing prime (all residue classes occupied) the local factor vanishes. -/
theorem localFactor_eq_zero {H : Finset ℕ} {p : ℕ} (hp : 0 < p) (hν : p ≤ ν H p) :
    localFactor H p = 0 := by
  have : ν H p = p := le_antisymm (ν_le_self H hp) hν
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp [localFactor, this, hp0]

theorem localFactor_empty (p : ℕ) : localFactor ∅ p = 1 := by simp [localFactor]

theorem localFactor_singleton (h : ℕ) {p : ℕ} (hp : p.Prime) : localFactor {h} p = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have : (1 - 1 / (p : ℝ)) ≠ 0 := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; exact hp1
    linarith
  have this' : 1 - (p : ℝ)⁻¹ ≠ 0 := by simpa using this
  simp [localFactor_eq, this']

theorem pow_one_sub_le (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) ^ k ≤ 1 - k * t + (k : ℝ) ^ 2 * t ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ 1 - t := by linarith
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc (1 - t) ^ (k + 1) = (1 - t) ^ k * (1 - t) := pow_succ _ _
      _ ≤ (1 - k * t + (k : ℝ) ^ 2 * t ^ 2) * (1 - t) := mul_le_mul_of_nonneg_right ih h1
      _ ≤ 1 - (k + 1 : ℕ) * t + ((k + 1 : ℕ) : ℝ) ^ 2 * t ^ 2 := by
          push_cast
          have h3 : 0 ≤ (k : ℝ) ^ 2 * t ^ 3 := by positivity
          have h4 : 0 ≤ ((k : ℝ) + 1) * t ^ 2 := by positivity
          nlinarith

/-- For a prime `p` exceeding all shifts, `|localFactor H p - 1| ≤ k² 2^k / p²`. -/
theorem abs_localFactor_sub_one_le {H : Finset ℕ} {p : ℕ} (hp : p.Prime) (hsup : H.sup id < p) :
    |localFactor H p - 1| ≤ (H.card : ℝ) ^ 2 * 2 ^ H.card * ((p : ℝ) ^ 2)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set t : ℝ := 1 / p with ht
  have ht0 : 0 ≤ t := by positivity
  have ht12 : t ≤ 1 / 2 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hp2
  set k := H.card with hk
  have hb : (1 - (ν H p : ℝ) / p) = 1 - k * t := by
    rw [ν_eq_card_of_sup_lt hsup, ht]; ring
  have ha_lo : (1 / 2 : ℝ) ^ k ≤ (1 - t) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have ha_pos : 0 < (1 - t) ^ k := lt_of_lt_of_le (by positivity) ha_lo
  have hbern : 1 - k * t ≤ (1 - t) ^ k := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith) k
    calc 1 - k * t = 1 + k * -t := by ring
      _ ≤ (1 + -t) ^ k := this
      _ = (1 - t) ^ k := by ring_nf
  have hup := pow_one_sub_le k ht0 (by linarith : t ≤ 1)
  rw [localFactor_eq, hb, div_sub_one ha_pos.ne', abs_div, abs_of_pos ha_pos,
    abs_of_nonpos (by linarith), div_le_iff₀ ha_pos]
  have e : ((p : ℝ) ^ 2)⁻¹ = t ^ 2 := by rw [ht]; field_simp
  rw [e]
  have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  calc -(1 - k * t - (1 - t) ^ k) ≤ (k : ℝ) ^ 2 * t ^ 2 := by linarith
    _ = (k : ℝ) ^ 2 * 2 ^ k * t ^ 2 * (1 / 2 : ℝ) ^ k := by linear_combination -(k:ℝ)^2 * t^2 * h2
    _ ≤ (k : ℝ) ^ 2 * 2 ^ k * t ^ 2 * (1 - t) ^ k :=
        mul_le_mul_of_nonneg_left ha_lo (by positivity)

/-- `∑_p |localFactor H p - 1| < ∞`: the Euler product for `𝔖 H` converges absolutely. -/
theorem summable_localFactor_sub_one (H : Finset ℕ) :
    Summable fun p : Nat.Primes => localFactor H p - 1 := by
  have hg : Summable fun p : Nat.Primes =>
      (H.card : ℝ) ^ 2 * 2 ^ H.card * (((p : ℕ) : ℝ) ^ 2)⁻¹ :=
    ((Real.summable_nat_pow_inv.2 one_lt_two).comp_injective
      Nat.Primes.coe_nat_injective).mul_left _
  refine hg.of_norm_bounded_eventually ?_
  have hfin : {p : Nat.Primes | (p : ℕ) ≤ H.sup id}.Finite :=
    (Set.finite_Iic (H.sup id)).preimage Nat.Primes.coe_nat_injective.injOn
  refine hfin.subset fun p hp => ?_
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Real.norm_eq_abs] at hp ⊢
  by_contra hlt
  exact hp (abs_localFactor_sub_one_le p.2 (not_le.1 hlt))

/-- The singular series product is (unconditionally) convergent, for every `H`. -/
theorem multipliable_localFactor (H : Finset ℕ) :
    Multipliable fun p : Nat.Primes => localFactor H p := by
  have := Real.multipliable_one_add_of_summable (summable_localFactor_sub_one H)
  simpa using this

theorem hasProd_singularSeries (H : Finset ℕ) :
    HasProd (fun p : Nat.Primes => localFactor H p) (𝔖 H) :=
  (multipliable_localFactor H).hasProd

/-- **The singular series of an admissible tuple is positive.** -/
theorem singularSeries_pos {H : Finset ℕ} (hH : Admissible H) : 0 < 𝔖 H := by
  have hs : Summable fun p : Nat.Primes => Real.log (localFactor H p) := by
    have := Real.summable_log_one_add_of_summable (summable_localFactor_sub_one H)
    simpa using this
  rw [singularSeries, ← Real.rexp_tsum_eq_tprod (fun p => localFactor_pos hH p.2) hs]
  exact Real.exp_pos _

/-- The singular series of a non-admissible tuple vanishes. -/
theorem singularSeries_eq_zero {H : Finset ℕ} (hH : ¬Admissible H) : 𝔖 H = 0 := by
  simp only [Admissible, not_forall, not_lt] at hH
  obtain ⟨p, hp, hν⟩ := hH
  exact tprod_of_exists_eq_zero ⟨⟨p, hp⟩, localFactor_eq_zero hp.pos hν⟩

theorem singularSeries_pos_iff (H : Finset ℕ) : 0 < 𝔖 H ↔ Admissible H :=
  ⟨fun h => by_contra fun hH => h.ne' (singularSeries_eq_zero hH), singularSeries_pos⟩

@[simp] theorem singularSeries_empty : 𝔖 ∅ = 1 := by
  simp [singularSeries, localFactor_empty]

/-- For `k = 1` every local factor is `1`, so `𝔖 {h} = 1` (consistent with the PNT). -/
@[simp] theorem singularSeries_singleton (h : ℕ) : 𝔖 {h} = 1 := by
  rw [singularSeries, tprod_congr (fun p : Nat.Primes => localFactor_singleton h p.2), tprod_one]

/-- Twin primes: the local factor at `2` is `2`. -/
theorem localFactor_twin_two : localFactor {0, 2} 2 = 2 := by
  have h1 : ν {0, 2} 2 = 1 := by decide
  have h2 : ({0, 2} : Finset ℕ).card = 2 := by decide
  rw [localFactor_eq, h1, h2]; norm_num

/-- Twin primes: the local factor at an odd prime `p` is `1 - 1/(p-1)²`; hence
`𝔖 {0,2} = 2 ∏_{p > 2} (1 - 1/(p-1)²)`, twice the twin prime constant. -/
theorem localFactor_twin_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    localFactor {0, 2} p = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have h2 : ({0, 2} : Finset ℕ).card = 2 := by decide
  have h1 : ν {0, 2} p = 2 := by
    rw [ν_eq_card_of_sup_lt (by simpa using hlt), h2]
  have hp' : (2 : ℝ) < p := by exact_mod_cast hlt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [localFactor_eq, h1, h2]
  field_simp
  ring

/-! ## Consistency checks and the main implications -/

/-- Sanity check: for the empty tuple the asymptotic holds trivially (`⌊x⌋ / x → 1 = 𝔖 ∅`). -/
theorem hardyLittlewoodAsymptotic_empty : HardyLittlewoodAsymptotic ∅ := by
  simpa [HardyLittlewoodAsymptotic, tupleSum] using tendsto_nat_floor_div_atTop (R := ℝ)

/-- **The asymptotic is a theorem for non-admissible tuples**: there `𝔖 H = 0` and
`tupleSum H x = o(x)` (all but boundedly many of the contributing `n` involve a proper prime
power).  So the admissibility hypothesis in `HardyLittlewoodTuples` only removes a proved
case. -/
theorem hardyLittlewoodAsymptotic_of_not_admissible {H : Finset ℕ} (hH : ¬Admissible H) :
    HardyLittlewoodAsymptotic H := by
  have hne : H.Nonempty := by
    rw [nonempty_iff_ne_empty]; rintro rfl; exact hH admissible_empty
  rw [HardyLittlewoodAsymptotic, singularSeries_eq_zero hH]
  exact tendsto_tupleSum_div_zero_of_finite hne (finite_of_not_admissible hH)

/-- The case `k = 1` of the qualitative statement is Euclid's theorem. -/
theorem infinite_shifted_primes (h : ℕ) : {n : ℕ | (n + h).Prime}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + h + 1)
  exact ⟨p - h, by simpa [Nat.sub_add_cancel (by omega : h ≤ p)] using hp, by omega⟩

/-- **Quantitative ⇒ qualitative.**  The Hardy–Littlewood asymptotic (for `k ≥ 2`) implies the
qualitative prime `k`-tuples conjecture.  Unconditional implication between two OPEN
statements; uses `singularSeries_pos` and the `O(√x log^k x)` bound for prime powers. -/
theorem HardyLittlewoodTuples.primeTuples (hHL : HardyLittlewoodTuples) :
    PrimeTuplesConjecture := by
  intro H hadm hne
  rcases Nat.lt_or_ge H.card 2 with hlt | hge
  · have hc : H.card = 1 := by have := card_pos.2 hne; omega
    obtain ⟨h, rfl⟩ := card_eq_one.1 hc
    simpa using infinite_shifted_primes h
  · exact infinite_of_asymptotic hne (singularSeries_pos hadm) (hHL H hge hadm)

theorem HardyLittlewoodTuples.twinPrime (h : HardyLittlewoodTuples) : TwinPrimeConjecture :=
  h.primeTuples.twinPrime

theorem HardyLittlewoodTuples.weakPolignac (h : HardyLittlewoodTuples) :
    WeakPolignacConjecture :=
  h.primeTuples.weakPolignac

/-- By `hardyLittlewoodAsymptotic_of_not_admissible`, the admissibility hypothesis in the
quantitative conjecture can be dropped: the non-admissible case is a theorem. -/
theorem hardyLittlewoodTuples_iff :
    HardyLittlewoodTuples ↔ ∀ H : Finset ℕ, 2 ≤ H.card → HardyLittlewoodAsymptotic H :=
  ⟨fun h H hc => by
    by_cases hH : Admissible H
    · exact h H hc hH
    · exact hardyLittlewoodAsymptotic_of_not_admissible hH,
   fun h H hc _ => h H hc⟩

/-- Under the qualitative conjecture, admissibility exactly characterizes the nonempty tuples
that are all-prime infinitely often. -/
theorem PrimeTuplesConjecture.infinite_iff (h : PrimeTuplesConjecture) {H : Finset ℕ}
    (hH : H.Nonempty) : {n : ℕ | ∀ h ∈ H, (n + h).Prime}.Infinite ↔ Admissible H :=
  ⟨admissible_of_infinite, fun ha => h H ha hH⟩

end PrimeTuples

/-! ## Axiom audit -/

#print axioms PrimeTuples.admissible_iff_forall_le_card
#print axioms PrimeTuples.admissible_image_add
#print axioms PrimeTuples.le_card_of_not_admissible
#print axioms PrimeTuples.finite_of_not_admissible
#print axioms PrimeTuples.tupleSum_le_mul_log_pow
#print axioms PrimeTuples.tupleSum_le_primeTupleSum_add
#print axioms PrimeTuples.tendsto_tupleSum_div_zero_of_finite
#print axioms PrimeTuples.multipliable_localFactor
#print axioms PrimeTuples.singularSeries_pos
#print axioms PrimeTuples.singularSeries_pos_iff
#print axioms PrimeTuples.singularSeries_singleton
#print axioms PrimeTuples.localFactor_twin_two
#print axioms PrimeTuples.localFactor_twin_odd
#print axioms PrimeTuples.hardyLittlewoodAsymptotic_of_not_admissible
#print axioms PrimeTuples.hardyLittlewoodTuples_iff
#print axioms PrimeTuples.infinite_of_asymptotic
#print axioms PrimeTuples.HardyLittlewoodTuples.primeTuples
#print axioms PrimeTuples.PrimeTuplesConjecture.twinPrime
#print axioms PrimeTuples.PrimeTuplesConjecture.weakPolignac
#print axioms PrimeTuples.PrimeTuplesConjecture.infinite_iff
#print axioms PrimeTuples.HardyLittlewoodTuples.twinPrime
