/-
# A criterion for Jeśmanowicz' conjecture, every `n ≥ 1`: `g = 2^r`, `f`, `f ± g` prime powers

STATUS: IN PROGRESS / NOT YET SOLVED

(The status line refers to Jeśmanowicz' conjecture as a whole, which is OPEN and is NOT
proved here; see `RomeroConjecture/Jesmanowicz.lean` for the statement
`Jesmanowicz.JesmanowiczConjecture`. This file proves it for one explicitly described family
of primitive triples, for every `n ≥ 1`.)

## What IS proved in this file (machine-checked, no `sorry`, no extra axioms)

### The general theorem

* `jesmanowiczFor_of_criterion` :
  ```
  theorem jesmanowiczFor_of_criterion {r f : ℕ} (hr : 2 ≤ r) (hf : IsPrimePow f)
      (hu : IsPrimePow (f - 2 ^ r)) (hv : IsPrimePow (f + 2 ^ r)) (h8 : (f - 2 ^ r) % 8 = 3)
      (n : ℕ) (hn : 0 < n) :
      JesmanowiczFor (f ^ 2 - (2 ^ r) ^ 2) (2 * f * 2 ^ r) (f ^ 2 + (2 ^ r) ^ 2) n
  ```
  In words: let `g = 2^r`, `r ≥ 2`, and let `f > g` be such that the three numbers
  `f - g`, `f`, `f + g` are prime powers and `f - g ≡ 3 (mod 8)`. Then for the primitive
  Pythagorean triple `(a, b, c) = (f² - g², 2fg, f² + g²)` and EVERY `n ≥ 1` the only
  solution in positive integers of `(a n)^x + (b n)^y = (c n)^z` is `x = y = z = 2`.
  The theorem is UNCONDITIONAL: the primitive case `n = 1` is proved here too
  (`CritData.primitive`), it is not an input.
  (`jesmanowiczFor_of_criterion_swap` : legs swapped;
  `isPrimitivePythagorean_of_criterion` : the triple is a primitive Pythagorean triple.)
  The hypotheses force `f ≡ 3 (mod 4)` and `f - g ≡ f + g ≡ 3 (mod 8)`; all three primes
  involved are `≡ 3 (mod 4)` and the two primes of `a` are `≡ 3 (mod 8)`.
* `CritData.jesmanowiczFor` : the same statement with the primes named
  (`f = ℓ^j`, `f - g = p₁^s`, `f + g = p₂^t`); the structure `CritData` bundles the hypotheses.
* `jesmanowiczFor_two_pow_add_three` : the sub-family `f - g = 3`: if `r ≥ 2` and `2^r + 3`,
  `2^(r+1) + 3` are both prime, the conjecture holds for all `n ≥ 1` for
  `(3 (2^(r+1) + 3), 2^(r+1) (2^r + 3), (2^r + 3)² + 2^(2r))`.

### The pieces (each fully proved, each of independent use)

* `CritData.primitive` : `n = 1`, i.e. `a^x + b^y = c^z ⇒ x = y = z = 2`.
* `CritData.no_y_lt_z_lt_x`, `CritData.no_x_lt_z_lt_y` : for `n > 1` the two configurations
  `y < z < x` and `x < z < y` are impossible (the remaining ones are excluded for every
  primitive triple by `IsSolution.strict_cases_of_one_lt`, `JesmanowiczDemjanenko.lean`).
* `CritData.sq_add_ne` : `D⁴ + b^y N = (c^Z)²` is impossible for `y > 2Z`, `N ≥ 1`, `D` odd
  and prime to `f` (NO hypothesis on `N`: this is why the cofactor `n` plays no role).
* `crit_pow_dvd_sq_sub` : a prime power `v = p^t` with `v² > c` cannot divide
  `(c^w)² - B²` to a power `> 2w` (`p ∤ 2B`, `B < c^w`).
* `crit_pow_sub_pow_two` : if `(s + D)^X - s^X` is a power of `2` (`s` odd, `D ≥ 4` even,
  `X ≥ 1`) then `X = 1`.

### Instances (all UNCONDITIONAL, all `n ≥ 1`; none is conditional on `n = 1`)

The first two re-derive the results of `JesmanowiczNew.lean`; the other 22 are further
triples. `(a, b, c)` — `(f, g)`:
  * `(33, 56, 65)` — `(f, g) = (7, 2^2)`, `f - g = 3`, `f + g = 11`
  * `(57, 176, 185)` — `(f, g) = (11, 2^3)`, `f - g = 3`, `f + g = 19`
  * `(297, 304, 425)` — `(f, g) = (19, 2^3)`, `f - g = 11`, `f + g = 3^3`
  * `(513, 184, 545)` — `(f, g) = (23, 2^2)`, `f - g = 19`, `f + g = 3^3`
  * `(473, 864, 985)` — `(f, g) = (3^3, 2^4)`, `f - g = 11`, `f + g = 43`
  * `(1593, 1376, 2105)` — `(f, g) = (43, 2^4)`, `f - g = 3^3`, `f + g = 59`
  * `(393, 8576, 8585)` — `(f, g) = (67, 2^6)`, `f - g = 3`, `f + g = 131`
  * `(43497, 13504, 45545)` — `(f, g) = (211, 2^5)`, `f - g = 179`, `f + g = 3^5`
  * `(51273, 7264, 51785)` — `(f, g) = (227, 2^4)`, `f - g = 211`, `f + g = 3^5`
  * `(54953, 31104, 63145)` — `(f, g) = (3^5, 2^6)`, `f - g = 179`, `f + g = 307`
  * `(303993, 2381824, 2401145)` — `(f, g) = (1163, 2^10)`, `f - g = 139`, `f + g = 3^7`
  * `(443097, 134660096, 134660825)` — `(f, g) = (8219, 2^13)`, `f - g = 3^3`, `f + g = 16411`
  * `(64934217, 188268544, 199151945)` — `(f, g) = (11491, 2^13)`, `f - g = 3299`, `f + g = 3^9`
  * `(118985033, 644972544, 655855945)` — `(f, g) = (3^9, 2^14)`, `f - g = 3299`, `f + g = 36067`
  * `(196617, 2147680256, 2147680265)` — `(f, g) = (32771, 2^15)`, `f - g = 3`, `f + g = 65539`
  * `(19771553817, 9462022144, 21919037465)` — `(f, g) = (144379, 2^15)`, `f - g = 111611`, `f + g = 3^11`
  * `(21026541897, 570394935296, 570782355785)` — `(f, g) = (543971, 2^19)`, `f - g = 3^9`, `f + g = 1068259`
  * `(2541865824233, 204073344, 2541865832425)` — `(f, g) = (3^13, 2^6)`, `f - g = 1594259`, `f + g = 1594387`
  * `(2541891337497, 25509296, 2541891337625)` — `(f, g) = (1594331, 2^3)`, `f - g = 3^13`, `f + g = 1594339`
  * `(2542069901673, 204081536, 2542069909865)` — `(f, g) = (1594387, 2^6)`, `f - g = 3^13`, `f + g = 1594451`
  * `(205891132094393, 459165024, 205891132094905)` — `(f, g) = (3^15, 2^4)`, `f - g = 14348891`, `f + g = 14348923`
  * `(206126224586937, 235226710016, 206126358804665)` — `(f, g) = (14357099, 2^13)`, `f - g = 3^15`, `f + g = 14365291`
  * `(207771872032953, 1889329872896, 207780461967545)` — `(f, g) = (14414443, 2^16)`, `f - g = 3^15`, `f + g = 14479979`
  * `(16676123783451273, 1057882660864, 16676123817005705)` — `(f, g) = (129136067, 2^12)`, `f - g = 129131971`, `f + g = 3^17`

## Proof outline (elementary; worked out by the formalizer, not transcribed from a paper)

Notation: `g = 2^r`, `u = f - g = p₁^s`, `v = f + g = p₂^t`, `f = ℓ^j`, `a = u v`,
`b = 2^(r+1) ℓ^j`, `c = f² + g²`. Then `u ≡ v ≡ p₁ ≡ p₂ ≡ 3 (mod 8)`, `ℓ ≡ 3 (mod 4)`, `j` odd,
`c ≡ 1 (mod 8)`, `c ≡ 2g² (mod a)`, `c ≡ g² (mod ℓ)`, `f ≡ g (mod p₁)`, `f ≡ -g (mod p₂)`.
Write `χ_p` for the quadratic character mod `p`; `χ_{p_i}(2) = χ_{p_i}(-1) = -1`, hence
`χ_{p_i}(c) = -1`, and `χ_ℓ(-1) = -1`.

* `n = 1`. Mod `ℓ`: `(-g²)^x ≡ g^(2z)`, so `x` is even. Mod `p₂`: `(-2g²)^y ≡ (2g²)^z` and
  `χ(-2) = 1`, so `z` is even. Mod `p₁`: `(2g²)^y ≡ (2g²)^z`, so `y` is even. With
  `x = 2X`, `y = 2Y`, `z = 2Z`, `A = c^Z`, `B = a^X` (both `≡ 1 mod 4`), `d = (A - B)/2`:
  `d (B + d) = 2^(2(r+1)Y - 2) f^(2Y)` with `B + d` odd forces `d = T²`, `B + d = f^(2Y)`,
  `T = 2^((r+1)Y - 1)`. So `a^X = (f^Y - T)(f^Y + T)` with coprime factors, and
  `u^X = p₁^(sX)`, `v^X = p₂^(tX)` each divide one factor. The only possibilities are
  `(f^Y - T, f^Y + T) = (u^X, v^X)` or `(1, a^X)`; in both a difference `w^X - s^X` of
  `X`-th powers of odd numbers with `w - s ≥ 4` is a power of two, which forces `X = 1`
  (`crit_pow_sub_pow_two`: for even `X` two powers of two `≥ 4` would add up to `2·odd`; for
  odd `X` the cofactor `(w^X - s^X)/(w - s)` is odd). Then `Y = 1` in the first case and a
  size contradiction (or `u = 1`) in the second.
* `n > 1`, `y < z < x` (so `rad(n) ∣ b`). Cancel `n^y`: `a^x n^(x-z) + q = c^z`,
  `q n^(z-y) = b^y`, `gcd(q, n) = 1`, hence `q ∈ {1, f^y, 2^((r+1)y)}` (`crit_split`).
  Reducing mod `p₁` and `p₂` and applying `χ`: `q = 1` gives `z` even; `q = f^y` gives
  `(±(-1)^r)^y = (-1)^z` for both signs, so `y` and `z` are even; `q = 2^((r+1)y)` gives
  `(r+1)y ≡ z (mod 2)`, and `n = ℓ^k`, `k(z - y) = jy` with `j` odd then forces `z` and
  `(r+1)y` even. So `q = B²`, `z = 2w`, and `v^x = p₂^(tx)` divides `(c^w - B)(c^w + B)`
  with `x > 2w`: impossible, since it divides one factor and `v² > c`
  (`crit_pow_dvd_sq_sub`).
* `n > 1`, `x < z < y` (so `rad(n) ∣ a`). Cancel `n^x`: `q + b^y n^(y-z) = c^z`,
  `q n^(z-x) = a^x`, `gcd(q, n) = 1`, hence `q ∈ {1, u^x, v^x}`, and some `π ∈ {p₁, p₂}`
  divides `n` but not `q`. Mod `8`: `q ≡ 1`, so `x` is even if `q ≠ 1`; mod `π`:
  `χ_π(q) = 1 = (-1)^z`, so `z` is even; mod `16`: `q ≡ 1`, so `4 ∣ x` if `q ≠ 1`. Hence
  `q = D⁴` with `D` odd, prime to `f`, `z = 2Z`, and `D⁴ + b^y N = (c^Z)²` with `y > 2Z`.
  With `d = (c^Z - D²)/2`: `2^((r+1)y - 2) ∣ d`, and `ℓ^(jy) ∣ d` is impossible by size
  (`b^y ≥ 2 c^Z`), so `ℓ ∣ D² + d`, i.e. `c^Z ≡ -D² (mod ℓ)`; as `c ≡ g² (mod ℓ)` this makes
  `-1` a square mod `ℓ ≡ 3 (mod 4)`: contradiction (`CritData.sq_add_ne`).

## How large is the family? (numerical search, NOT formalized)

Among `f - g`, `f`, `f + g` exactly one is divisible by `3` (as `3 ∤ g`), so one of them is a
power of `3`: the family consists of `(f, g) = (2^r + 3^s, 2^r)`, `(3^j, 2^r)` and
`(3^t - 2^r, 2^r)` with the other two numbers prime powers and `f - g ≡ 3 (mod 8)`. A search
(Miller–Rabin, script in the session scratch area, not in the repository) found
`12` pairs with `f < 10^4`, `17` with `f < 10^6`, `24` with `f < 10^9`, `30` with `f < 10^12`,
and `54` pairs in the box `r ≤ 150`, exponent of `3` at most `100`. The family is thin
(prime-triple type conditions); whether it is infinite is not known to me and nothing about
that is claimed. Only the 24 pairs with `f < 2·10^8` are instantiated below (larger
primes exceed what `norm_num` certifies comfortably in the kernel); the theorem applies to
the others as soon as primality certificates are supplied.

## Novelty assessment (read this before citing the result as new)

REFEREE UPDATE (2026-11-26, after a dedicated adversarial literature check; supersedes the text
below where they disagree).
* The `n = 1` half of the criterion is KNOWN: T. Miyazaki, "On the conjecture of Jeśmanowicz
  concerning Pythagorean triples", Bull. Aust. Math. Soc. 80 (2009) 413-422, Theorem 1.4 (if
  m² − n² has no prime factor ≡ 1 mod 4, m − n has a prime factor ≡ 3 mod 8 and m ≢ 1 mod 4, the
  primitive conjecture holds). Every pair of this file satisfies those hypotheses, and Miyazaki
  does not need the prime-power assumptions. His Example 2.12 states the cases (33,56,65) and
  (57,176,185) explicitly. His proof uses Darmon–Merel (via Cao–Dong); the proof here is
  elementary, which is a difference of method only.
* For `n > 1`, Le 1999 / Yang–Fu 2015 already settle every `n` whose radical divides neither `a`
  nor `b`. The possibly new content of this file is therefore exactly: `n > 1` with
  rad(n) ∣ a or rad(n) ∣ b, for this family.
* That remaining `n > 1` statement, and the all-`n` statement for each instance with c > 101,
  were NOT FOUND after two referee passes (surveys arXiv:1706.05480 and arXiv:1808.06557, about
  100 OpenAlex and 159 zbMATH records, citing-paper lists, exact-equation searches in English and
  Chinese). Papers on the mirror shape (f a power of 2: Feng–Luo 2022, Fan–Luo 2023, Guan 2021)
  do not apply. Several paywalled or Chinese-language sources could not be read, so this is not
  a certificate of novelty.


Claim made here, and nothing stronger: **the general theorem and its instances other than
those listed as known below were NOT FOUND in the literature that was searched (see the issue
log of the project and the novelty paragraph of `JesmanowiczNew.lean`); a separate referee
pass is re-doing the literature search.** "New" means "not found", not "certified new".

* None of the instantiated `(f, g)` is in the list of pairs settled for all `n` in the
  Le–Scott–Styer survey (arXiv:1808.06557, §2.2): `(2^k, 1)`, `(6,1)`, `(10,1)`, `(12,1)`,
  `(14,1)`, `(5,2)`, `(7,2)`, `(49,2)`, `(9,2)`, `(11,2)`, `(8,3)`, `(9,4)`, `(g+1, g)` for
  `g = 2,…,7, 10, 17, 19, 25, 28, 45`, and the Mersenne/Fermat-prime families. (The Fermat
  family `(2^k + 1, 2^k)` has `f - g = 1` and is NOT covered by the criterion, which needs
  `f - g ≡ 3 (mod 8)`.)
* The case `n = 1` of every instance with `a ≤ 10^6` or `b ≤ 10^6` is covered by Styer's
  computation (arXiv:2402.04428); the `n = 1` part of the criterion is therefore not new for
  those triples as a statement, though the proof here is a general hand proof.
* Known general theorems that the result RESEMBLES and that I am aware of (not re-read for
  this file): Miyazaki (2015) — a leg a power of `2` — and the Fermat-number results of
  Tang–Yang, Deng, Tang–Weng, Yang–Fu (`(2^k + 1, 2^k)`, `g = 1`); Deng–Cohen (1998) and
  Deng (2014) / Yang–Fu (2015) — the reduction to `rad(n) ∣ a` or `rad(n) ∣ b` used here;
  Yuan–Han (Acta Arith. 2018) and Han–Yuan — criteria in terms of `f`, `g` with
  congruence conditions modulo `8`/`16` on prime factors of `f ± g` (as far as I recall for
  `2 ∥ fg`, whereas here `4 ∣ g`); Feng–Luo (2022), Fan–Luo (2023), Guan (2021) — triples
  with `f` a power of `2` and `f ± g` prime powers (here instead `g` is the power of `2`);
  Miyazaki–Yuan–Wu and Fujita–Miyazaki — `n = 1` under congruence conditions. A theorem in
  one of these papers (or in the poorly indexed Chinese-language literature) that covers the
  present family under a formulation I did not recognize cannot be excluded.
* The method is the standard one (cofactor analysis, quadratic characters, difference of
  squares, size comparison). What may be new is the observation that for this shape of
  `(f, g)` everything closes up uniformly, in particular that the final contradiction in the
  case `x < z < y` (`-1` a square mod `ℓ`) does not depend on the cofactor `n` at all.
* Honest confidence: "probably not previously stated in this form; mathematically an
  elementary but non-trivial uniformization of the two ad-hoc proofs in
  `JesmanowiczNew.lean`".

## What is NOT proved / what failed

* Jeśmanowicz' conjecture itself (OPEN). Infinitude of the family.
* Weakening "prime power" for `f - g`: with three or more prime-power components in `a` the
  mod-`8` bookkeeping for the cofactor `q` in the case `x < z < y` necessarily leaves a
  unitary divisor `m ≡ 1 (mod 8)` of `a` (or contradictory Legendre conditions mod `f`), for
  which the parity of `x` cannot be forced by this method; `f + g` must be a prime power for
  the size argument in the case `y < z < x`; `f` must be a prime power for both.
* `r = 1` (`g = 2`), `f ≡ 1 (mod 4)`, or `f - g ≡ 7 (mod 8)`: not covered.
-/
import RomeroConjecture.Jesmanowicz
import RomeroConjecture.JesmanowiczAllN
import RomeroConjecture.JesmanowiczFamilies
import RomeroConjecture.JesmanowiczDemjanenko

namespace Jesmanowicz

/-! ## Elementary residue lemmas -/

theorem crit_pow_mod_eight_of_three (m x : ℕ) (hm : m % 8 = 3) :
    (x % 2 = 0 → m ^ x % 8 = 1) ∧ (x % 2 = 1 → m ^ x % 8 = 3) := by
  induction x with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.mul_mod, hm]; omega

theorem crit_pow_mod_sixteen_of_nine (m X : ℕ) (hm : m % 16 = 9) :
    (X % 2 = 0 → m ^ X % 16 = 1) ∧ (X % 2 = 1 → m ^ X % 16 = 9) := by
  induction X with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.mul_mod, hm]; omega

theorem crit_pow_mod_four_of_three (m x : ℕ) (hm : m % 4 = 3) :
    (x % 2 = 0 → m ^ x % 4 = 1) ∧ (x % 2 = 1 → m ^ x % 4 = 3) := by
  induction x with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.mul_mod, hm]; omega

/-- If a power `p ^ k` is `≡ 3 (mod 8)` then so is `p`. -/
theorem crit_mod_eight_of_pow {p k : ℕ} (h : p ^ k % 8 = 3) : p % 8 = 3 := by
  have key : ∀ k, p ^ k % 8 = 1 ∨ p ^ k % 8 = p % 8 ∨ p ^ k % 2 = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : p ^ (k + 1) % 8 = (p ^ k % 8) * (p % 8) % 8 := by rw [pow_succ, Nat.mul_mod]
      have h2 : p ^ (k + 1) % 2 = (p ^ k % 2) * (p % 2) % 2 := by rw [pow_succ, Nat.mul_mod]
      have h3 : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
      rcases ih with ih | ih | ih
      · rw [ih] at h1; omega
      · rw [ih] at h1
        obtain ⟨m, hm⟩ : ∃ m, m = p % 8 := ⟨_, rfl⟩
        rw [← hm] at h1 h3 ⊢
        interval_cases m <;> omega
      · rw [ih] at h2; omega
  rcases key k with h1 | h1 | h1 <;> omega

/-- If a power `p ^ k` is `≡ 3 (mod 4)` then `p ≡ 3 (mod 4)` and `k` is odd. -/
theorem crit_mod_four_of_pow {p k : ℕ} (h : p ^ k % 4 = 3) : p % 4 = 3 ∧ k % 2 = 1 := by
  have key : ∀ k, p ^ k % 4 = 1 ∨ p ^ k % 4 = p % 4 ∨ p ^ k % 2 = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : p ^ (k + 1) % 4 = (p ^ k % 4) * (p % 4) % 4 := by rw [pow_succ, Nat.mul_mod]
      have h2 : p ^ (k + 1) % 2 = (p ^ k % 2) * (p % 2) % 2 := by rw [pow_succ, Nat.mul_mod]
      have h3 : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rcases ih with ih | ih | ih
      · rw [ih] at h1; omega
      · rw [ih] at h1
        obtain ⟨m, hm⟩ : ∃ m, m = p % 4 := ⟨_, rfl⟩
        rw [← hm] at h1 h3 ⊢
        interval_cases m <;> omega
      · rw [ih] at h2; omega
  have hp : p % 4 = 3 := by rcases key k with h1 | h1 | h1 <;> omega
  have := crit_pow_mod_four_of_three p k hp
  omega

theorem crit_four_dvd_two_pow {i : ℕ} (h : 4 ≤ 2 ^ i) : 2 ^ i % 4 = 0 := by
  rcases i with _ | _ | i
  · norm_num at h
  · norm_num at h
  · rw [pow_succ, pow_succ]; omega

theorem crit_neg_one_pow_parity {m n : ℕ} (h : (-1 : ℤ) ^ m = (-1) ^ n) : m % 2 = n % 2 := by
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn
  · rw [Nat.even_iff] at hm hn; omega
  · rw [hm.neg_one_pow, hn.neg_one_pow] at h; norm_num at h
  · rw [hm.neg_one_pow, hn.neg_one_pow] at h; norm_num at h
  · rw [Nat.odd_iff] at hm hn; omega

theorem crit_even_of_neg_one_pow {z : ℕ} (h : (-1 : ℤ) ^ z = 1) : z % 2 = 0 :=
  Nat.even_iff.1 ((neg_one_pow_eq_one_iff_even (by norm_num)).1 h)

/-! ## Quadratic characters modulo primes `≡ 3 (mod 8)` / `≡ 3 (mod 4)` -/

theorem crit_qc_two {p : ℕ} [Fact p.Prime] (hp : p % 8 = 3) :
    quadraticChar (ZMod p) 2 = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, ZMod.exists_sq_eq_two_iff (by intro h; omega)]
  omega

theorem crit_qc_neg_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, ZMod.exists_sq_eq_neg_one_iff]
  omega

theorem crit_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem crit_qc_two_pow {p : ℕ} [Fact p.Prime] (hp : p % 8 = 3) (m : ℕ) :
    quadraticChar (ZMod p) ((2 : ZMod p) ^ m) = (-1) ^ m := by
  rw [map_pow, crit_qc_two hp]

theorem crit_qc_c_pow {p : ℕ} [Fact p.Prime] (hp : p % 8 = 3) {γ : ZMod p} (hγ : γ ≠ 0)
    (z : ℕ) : quadraticChar (ZMod p) ((2 * γ ^ 2) ^ z) = (-1) ^ z := by
  rw [map_pow, map_mul, crit_qc_two hp, quadraticChar_sq_one' hγ, mul_one]

/-! ## Three arithmetic lemmas -/

/-- If `q * N = P^e₁ * Q^e₂` with `P`, `Q` prime and no prime of `{P, Q}` divides both `q` and
`N`, then `N = 1`, or `(q, N) = (P^e₁, Q^e₂)`, or `(q, N) = (Q^e₂, P^e₁)`, or `q = 1`. -/
theorem crit_split {P Q e₁ e₂ q N : ℕ} (hP : P.Prime) (hQ : Q.Prime)
    (h : P ^ e₁ * Q ^ e₂ = N * q) (hPq : P ∣ q → ¬ P ∣ N) (hQq : Q ∣ q → ¬ Q ∣ N) :
    N = 1 ∨ (q = P ^ e₁ ∧ N = Q ^ e₂) ∨ (q = Q ^ e₂ ∧ N = P ^ e₁) ∨ q = 1 := by
  have copP : ∀ m : ℕ, ¬ P ∣ m → ∀ i, Nat.Coprime (P ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hP).2 hm)
  have copQ : ∀ m : ℕ, ¬ Q ∣ m → ∀ i, Nat.Coprime (Q ^ i) m := fun m hm i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hQ).2 hm)
  have hqd : q ∣ P ^ e₁ * Q ^ e₂ := ⟨N, by rw [h, mul_comm]⟩
  have hNd : N ∣ P ^ e₁ * Q ^ e₂ := ⟨q, h⟩
  by_cases hPq' : P ∣ q <;> by_cases hQq' : Q ∣ q
  · left
    have hc : Nat.Coprime (P ^ e₁ * Q ^ e₂) N :=
      Nat.Coprime.mul_left (copP _ (hPq hPq') _) (copQ _ (hQq hQq') _)
    exact Nat.Coprime.eq_one_of_dvd hc.symm hNd
  · right; left
    have h1 : P ^ e₁ ∣ q :=
      (copP _ (hPq hPq') e₁).dvd_of_dvd_mul_left ⟨Q ^ e₂, by rw [← h]⟩
    have h2 : q ∣ P ^ e₁ := (copQ _ hQq' e₂).symm.dvd_of_dvd_mul_right hqd
    have hqe : q = P ^ e₁ := Nat.dvd_antisymm h2 h1
    refine ⟨hqe, ?_⟩
    have hpos : 0 < P ^ e₁ := pow_pos hP.pos _
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [mul_comm (Q ^ e₂), h, hqe]
  · right; right; left
    have h1 : Q ^ e₂ ∣ q :=
      (copQ _ (hQq hQq') e₂).dvd_of_dvd_mul_left ⟨P ^ e₁, by rw [← h, mul_comm]⟩
    have h2 : q ∣ Q ^ e₂ := (copP _ hPq' e₁).symm.dvd_of_dvd_mul_left hqd
    have hqe : q = Q ^ e₂ := Nat.dvd_antisymm h2 h1
    refine ⟨hqe, ?_⟩
    have hpos : 0 < Q ^ e₂ := pow_pos hQ.pos _
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h, hqe]
  · right; right; right
    have hc : Nat.Coprime (P ^ e₁ * Q ^ e₂) q :=
      Nat.Coprime.mul_left (copP _ hPq' _) (copQ _ hQq' _)
    exact Nat.Coprime.eq_one_of_dvd hc.symm hqd

/-- A prime power `v = p^t` with `v² > c` cannot divide `(c^w)² - B²` to a power `> 2w`
(`p` odd, `p ∤ B`, `B < c^w`). -/
theorem crit_pow_dvd_sq_sub {p t v c x w B : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hv : v = p ^ t)
    (hv2 : 2 ≤ v) (hcv : c < v ^ 2) (hB : ¬ p ∣ B) (hBA : B < c ^ w)
    (h : v ^ x ∣ (c ^ w) ^ 2 - B ^ 2) : x ≤ 2 * w := by
  have hlt : 2 * c ^ w ≤ v ^ (2 * w + 1) := by
    calc 2 * c ^ w ≤ v * (v ^ 2) ^ w := Nat.mul_le_mul hv2 (Nat.pow_le_pow_left hcv.le w)
      _ = v ^ (2 * w + 1) := by ring
  obtain ⟨A, hA⟩ : ∃ A, A = c ^ w := ⟨_, rfl⟩
  rw [← hA] at hBA h hlt
  obtain ⟨D, rfl⟩ : ∃ D, A = B + D := ⟨A - B, by omega⟩
  have e : (B + D) ^ 2 - B ^ 2 = D * (2 * B + D) := by
    have : (B + D) ^ 2 = B ^ 2 + D * (2 * B + D) := by ring
    omega
  rw [e, hv, ← pow_mul] at h
  have hle : p ^ (t * x) ≤ 2 * B + D := by
    rcases prime_pow_dvd_or hp h (by
      rintro ⟨h1, h2⟩
      have h3 : p ∣ 2 * B := (Nat.dvd_add_left h1).1 h2
      rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
      · exact hp2 h4
      · exact hB h4) with h1 | h1
    · exact (Nat.le_of_dvd (by omega) h1).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h1
  rw [pow_mul, ← hv] at hle
  have h5 : v ^ x < v ^ (2 * w + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by omega)).1 h5
  omega

theorem crit_pow_gap (s D k : ℕ) : s ^ (k + 1) + (s + D) ^ k * D ≤ (s + D) ^ (k + 1) := by
  have h1 : s ^ k ≤ (s + D) ^ k := Nat.pow_le_pow_left (by omega) k
  have h2 : s ^ k * s ≤ (s + D) ^ k * s := Nat.mul_le_mul_right s h1
  have e1 : s ^ (k + 1) = s ^ k * s := by ring
  have e2 : (s + D) ^ (k + 1) = (s + D) ^ k * s + (s + D) ^ k * D := by ring
  omega

/-- `(s + D)^(2k+1) - s^(2k+1)` is `D` times an odd number when `s` is odd and `D` even. -/
theorem crit_odd_pow_sub (s D k : ℕ) (hs : s % 2 = 1) (hD : D % 2 = 0) :
    ∃ o, o % 2 = 1 ∧ (s + D) ^ (2 * k + 1) = s ^ (2 * k + 1) + D * o := by
  induction k with
  | zero => exact ⟨1, by norm_num, by ring⟩
  | succ k ih =>
    obtain ⟨o, ho, he⟩ := ih
    refine ⟨(2 * s + D) * s ^ (2 * k + 1) + o * (s + D) ^ 2, ?_, ?_⟩
    · have h1 : (s + D) ^ 2 % 2 = 1 := by
        rw [Nat.pow_mod]; have : (s + D) % 2 = 1 := by omega
        rw [this]
      have h2 : (o * (s + D) ^ 2) % 2 = 1 := by rw [Nat.mul_mod, ho, h1]
      have h3 : ((2 * s + D) * s ^ (2 * k + 1)) % 2 = 0 := by
        rw [Nat.mul_mod]; have : (2 * s + D) % 2 = 0 := by omega
        rw [this]; simp
      omega
    · have e1 : (s + D) ^ (2 * (k + 1) + 1) = (s + D) ^ (2 * k + 1) * (s + D) ^ 2 := by ring
      rw [e1, he]; ring

/-- If `(s + D)^X - s^X` is a power of two (`s` odd, `D ≥ 4` even, `X ≥ 1`) then `X = 1`. -/
theorem crit_pow_sub_pow_two {s D X m : ℕ} (hs : s % 2 = 1) (hD2 : D % 2 = 0) (hD : 4 ≤ D)
    (hX : 0 < X) (h : (s + D) ^ X = s ^ X + 2 ^ m) : X = 1 := by
  have hs0 : 0 < s := by omega
  rcases Nat.mod_two_eq_zero_or_one X with hX2 | hX2
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, X = 2 * (k + 1) := ⟨X / 2 - 1, by omega⟩
    rw [pow_mul' (s + D), pow_mul' s] at h
    have hgap := crit_pow_gap s D k
    have h1 : 1 ≤ (s + D) ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : D ≤ (s + D) ^ k * D := Nat.le_mul_of_pos_left _ h1
    have hNodd : s ^ (k + 1) % 2 = 1 := by rw [Nat.pow_mod, hs]; simp
    obtain ⟨N, hN⟩ : ∃ N, N = s ^ (k + 1) := ⟨_, rfl⟩
    rw [← hN] at h hgap hNodd
    obtain ⟨E, hE⟩ : ∃ E, (s + D) ^ (k + 1) = N + E := ⟨(s + D) ^ (k + 1) - N, by omega⟩
    rw [hE] at h
    have hE4 : 4 ≤ E := by omega
    have hfac : E * (2 * N + E) = 2 ^ m := by
      have : (N + E) ^ 2 = N ^ 2 + E * (2 * N + E) := by ring
      omega
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hfac)
    obtain ⟨i', -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hfac)
    have h4 := crit_four_dvd_two_pow (i := i) (by omega)
    have h4' := crit_four_dvd_two_pow (i := i') (by omega)
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, X = 2 * k + 1 := ⟨X / 2, by omega⟩
    obtain ⟨o, ho, he⟩ := crit_odd_pow_sub s D k hs hD2
    have hfac : D * o = 2 ^ m := by omega
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hfac)
    have ho1 : o = 1 := by
      rcases i with _ | i
      · simpa using hi
      · rw [hi, pow_succ] at ho; omega
    rw [ho1, mul_one] at he
    by_contra hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hgap := crit_pow_gap s D (2 * (k' + 1))
    have h1 : 2 ≤ (s + D) ^ (2 * (k' + 1)) :=
      le_trans (by omega) (Nat.le_self_pow (by omega) (s + D))
    have h2 : 2 * D ≤ (s + D) ^ (2 * (k' + 1)) * D := Nat.mul_le_mul_right D h1
    omega

/-! ## The hypotheses of the criterion -/

/-- The data of the criterion: `g = 2^r` with `r ≥ 2`, `f = ℓ^j`, `u = f - g = p₁^s`,
`v = f + g = p₂^t` with `ℓ`, `p₁`, `p₂` prime, `u ≡ 3 (mod 8)`, and
`(a, b, c) = (f² - g², 2fg, f² + g²)` (written `a = u v`). -/
structure CritData (r j s t ℓ p₁ p₂ f g u v a b c : ℕ) : Prop where
  hr : 2 ≤ r
  hℓ : ℓ.Prime
  hp₁ : p₁.Prime
  hp₂ : p₂.Prime
  hg : g = 2 ^ r
  hf : f = ℓ ^ j
  hu : u = p₁ ^ s
  hv : v = p₂ ^ t
  hfu : f = u + g
  hvf : v = f + g
  hu8 : u % 8 = 3
  ha : a = u * v
  hb : b = 2 * f * g
  hc : c = f ^ 2 + g ^ 2

namespace CritData

variable {r j s t ℓ p₁ p₂ f g u v a b c : ℕ}

section
variable (S : CritData r j s t ℓ p₁ p₂ f g u v a b c)
include S

theorem four_dvd_g : ∃ k, g = 4 * k := by
  obtain ⟨m, hm⟩ : ∃ m, r = m + 2 := ⟨r - 2, by have := S.hr; omega⟩
  exact ⟨2 ^ m, by rw [S.hg, hm]; ring⟩

theorem g_pos : 0 < g := by rw [S.hg]; positivity

theorem v8 : v % 8 = 3 := by
  obtain ⟨k, hk⟩ := S.four_dvd_g
  have := S.hu8; have := S.hfu; have := S.hvf
  omega

theorem f4 : f % 4 = 3 := by
  obtain ⟨k, hk⟩ := S.four_dvd_g
  have := S.hu8; have := S.hfu
  omega

theorem c8 : c % 8 = 1 := by
  obtain ⟨k, hk⟩ := S.four_dvd_g
  obtain ⟨m, hm⟩ : ∃ m, f = 4 * m + 3 := ⟨f / 4, by have := S.f4; omega⟩
  have e : (4 * m + 3) ^ 2 + (4 * k) ^ 2 = 8 * (2 * m ^ 2 + 3 * m + 1 + 2 * k ^ 2) + 1 := by ring
  rw [S.hc, hm, hk, e]; omega

theorem csq16 : c ^ 2 % 16 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, c = 8 * k + 1 := ⟨c / 8, by have := S.c8; omega⟩
  have e : (8 * k + 1) ^ 2 = 16 * (4 * k ^ 2 + k) + 1 := by ring
  rw [hk, e]; omega

theorem a8 : a % 8 = 1 := by
  rw [S.ha, Nat.mul_mod, S.hu8, S.v8]

theorem ℓ4 : ℓ % 4 = 3 := (crit_mod_four_of_pow (by rw [← S.hf]; exact S.f4)).1

theorem j_odd : j % 2 = 1 := (crit_mod_four_of_pow (by rw [← S.hf]; exact S.f4)).2

theorem p₁8 : p₁ % 8 = 3 := crit_mod_eight_of_pow (by rw [← S.hu]; exact S.hu8)

theorem p₂8 : p₂ % 8 = 3 := crit_mod_eight_of_pow (by rw [← S.hv]; exact S.v8)

theorem b_eq : b = 2 ^ (r + 1) * ℓ ^ j := by rw [S.hb, S.hg, ← S.hf]; ring

theorem a_eq (x : ℕ) : a ^ x = p₁ ^ (s * x) * p₂ ^ (t * x) := by
  rw [S.ha, S.hu, S.hv, mul_pow, ← pow_mul, ← pow_mul]

theorem uv_eq : u * v + g ^ 2 = f ^ 2 := by rw [S.hvf, S.hfu]; ring

theorem a_add : a + g ^ 2 = f ^ 2 := by rw [S.ha]; exact S.uv_eq

theorem v_eq : v = u + 2 * g := by have := S.hfu; have := S.hvf; omega

theorem f_pos : 0 < f := by have := S.f4; omega

theorem c_lt : c < v ^ 2 := by
  have e : (f + g) ^ 2 = f ^ 2 + g ^ 2 + 2 * (f * g) := by ring
  have : 0 < f * g := Nat.mul_pos S.f_pos S.g_pos
  rw [S.hc, S.hvf, e]; omega

theorem c_le_b_sq : c ≤ b ^ 2 := by
  have h1 : f ^ 2 ≤ f ^ 2 * g ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos S.g_pos 2)
  have h2 : g ^ 2 ≤ f ^ 2 * g ^ 2 := Nat.le_mul_of_pos_left _ (pow_pos S.f_pos 2)
  have e : (2 * f * g) ^ 2 = 4 * (f ^ 2 * g ^ 2) := by ring
  rw [S.hc, S.hb, e]; omega

theorem two_le_b : 2 ≤ b := by
  have : 0 < f * g := Nat.mul_pos S.f_pos S.g_pos
  rw [S.hb, mul_assoc]; omega

theorem b_pos : 0 < b := by have := S.two_le_b; omega

theorem two_mul_c_pow_le {Z y : ℕ} (hy : 2 * Z < y) : 2 * c ^ Z ≤ b ^ y := by
  calc 2 * c ^ Z ≤ b * (b ^ 2) ^ Z :=
        Nat.mul_le_mul S.two_le_b (Nat.pow_le_pow_left S.c_le_b_sq Z)
    _ = b ^ (2 * Z + 1) := by ring
    _ ≤ b ^ y := Nat.pow_le_pow_right S.b_pos (by omega)

/-! ### Coprimality -/

theorem cop_u2 : Nat.Coprime u 2 :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    (by have := S.hu8; omega))

theorem cop_ug : Nat.Coprime u g := by rw [S.hg]; exact Nat.Coprime.pow_right r S.cop_u2

theorem cop_uf : Nat.Coprime u f := by rw [S.hfu]; simpa using S.cop_ug

theorem cop_uv : Nat.Coprime u v := by
  rw [S.v_eq]; simpa using Nat.Coprime.mul_right S.cop_u2 S.cop_ug

theorem cop_v2 : Nat.Coprime v 2 :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    (by have := S.v8; omega))

theorem cop_vg : Nat.Coprime v g := by rw [S.hg]; exact Nat.Coprime.pow_right r S.cop_v2

theorem cop_vf : Nat.Coprime v f := by
  have hgf : Nat.Coprime g f := by rw [S.hfu]; simpa using S.cop_ug.symm
  rw [S.hvf]; simpa using hgf

theorem cop_ab : Nat.Coprime a b := by
  rw [S.ha, S.hb]
  exact Nat.Coprime.mul_left
    (Nat.Coprime.mul_right (Nat.Coprime.mul_right S.cop_u2 S.cop_uf) S.cop_ug)
    (Nat.Coprime.mul_right (Nat.Coprime.mul_right S.cop_v2 S.cop_vf) S.cop_vg)

theorem a_pos : 0 < a := by have := S.a8; omega

theorem c_pos : 0 < c := by have := S.c8; omega

theorem pyth : a ^ 2 + b ^ 2 = c ^ 2 := by
  rw [S.ha, S.hb, S.hc, S.hvf, S.hfu]; ring

/-- The triple is a primitive Pythagorean triple. -/
theorem prim : IsPrimitivePythagorean a b c :=
  ⟨S.a_pos, S.b_pos, S.c_pos, S.cop_ab, S.pyth⟩

theorem not_dvd_c {π : ℕ} (hπ : π.Prime) (h : π ∣ a ∨ π ∣ b) : ¬ π ∣ c := by
  intro hc
  have hc2 : π ∣ a ^ 2 + b ^ 2 := by rw [S.pyth]; exact dvd_pow hc (by norm_num)
  have hab : π ∣ a ∧ π ∣ b := by
    rcases h with h | h
    · exact ⟨h, hπ.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow h (by norm_num))).1 hc2)⟩
    · exact ⟨hπ.dvd_of_dvd_pow ((Nat.dvd_add_left (dvd_pow h (by norm_num))).1 hc2), h⟩
  have h1 : π ∣ Nat.gcd a b := Nat.dvd_gcd hab.1 hab.2
  rw [Nat.Coprime.gcd_eq_one S.cop_ab] at h1
  exact hπ.ne_one (Nat.dvd_one.1 h1)

theorem ℓ_dvd_f : ℓ ∣ f := by
  rw [S.hf]; exact dvd_pow_self ℓ (by have := S.j_odd; omega)

theorem s_ne : s ≠ 0 := by
  rintro rfl
  have := S.hu8; rw [S.hu] at this; norm_num at this

theorem t_ne : t ≠ 0 := by
  rintro rfl
  have := S.v8; rw [S.hv] at this; norm_num at this

theorem p₁_dvd_u : p₁ ∣ u := by rw [S.hu]; exact dvd_pow_self p₁ S.s_ne

theorem p₂_dvd_v : p₂ ∣ v := by rw [S.hv]; exact dvd_pow_self p₂ S.t_ne

theorem ℓ_dvd_b : ℓ ∣ b := by rw [S.hb]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left S.ℓ_dvd_f 2) g

theorem p₁_dvd_a : p₁ ∣ a := by rw [S.ha]; exact Dvd.dvd.mul_right S.p₁_dvd_u v

theorem p₂_dvd_a : p₂ ∣ a := by rw [S.ha]; exact Dvd.dvd.mul_left S.p₂_dvd_v u

omit S in
theorem not_dvd_of_cop {π x y : ℕ} (hπ : π.Prime) (hx : π ∣ x) (hc : Nat.Coprime x y) :
    ¬ π ∣ y := by
  intro hy
  have h1 : π ∣ Nat.gcd x y := Nat.dvd_gcd hx hy
  rw [Nat.Coprime.gcd_eq_one hc] at h1
  exact hπ.ne_one (Nat.dvd_one.1 h1)

theorem ℓ_not_dvd_u : ¬ ℓ ∣ u := not_dvd_of_cop S.hℓ S.ℓ_dvd_f S.cop_uf.symm

theorem ℓ_not_dvd_v : ¬ ℓ ∣ v := not_dvd_of_cop S.hℓ S.ℓ_dvd_f S.cop_vf.symm

theorem ℓ_not_dvd_a : ¬ ℓ ∣ a := not_dvd_of_cop S.hℓ S.ℓ_dvd_b S.cop_ab.symm

theorem p₁_not_dvd_v : ¬ p₁ ∣ v := not_dvd_of_cop S.hp₁ S.p₁_dvd_u S.cop_uv

theorem p₂_not_dvd_u : ¬ p₂ ∣ u := not_dvd_of_cop S.hp₂ S.p₂_dvd_v S.cop_uv.symm

theorem p₂_not_dvd_f : ¬ p₂ ∣ f := not_dvd_of_cop S.hp₂ S.p₂_dvd_v S.cop_vf

theorem p₂_not_dvd_two : ¬ p₂ ∣ 2 := not_dvd_of_cop S.hp₂ S.p₂_dvd_v S.cop_v2

/-! ### Reductions modulo the primes dividing `a` -/

theorem cast_g_ne_zero {π : ℕ} [Fact π.Prime] (hπ : π % 4 = 3) : (g : ZMod π) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, S.hg]
  intro h
  have h2 := (Fact.out : π.Prime).dvd_of_dvd_pow h
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem cast_g {π : ℕ} [Fact π.Prime] : (g : ZMod π) = 2 ^ r := by
  rw [S.hg]; push_cast; rfl

theorem cast_c {π : ℕ} [Fact π.Prime] (hπ : π ∣ a) : (c : ZMod π) = 2 * (g : ZMod π) ^ 2 := by
  have h1 : ((a + g ^ 2 : ℕ) : ZMod π) = ((f ^ 2 : ℕ) : ZMod π) := by rw [S.a_add]
  push_cast at h1
  rw [(ZMod.natCast_eq_zero_iff a π).2 hπ, zero_add] at h1
  rw [S.hc]; push_cast; rw [← h1]; ring

/-- If `π ∣ a` and `a^x w + q = c^z` with `x > 0`, then `q ≡ (2 g²)^z (mod π)`. -/
theorem cast_eq_of_dvd_a {π x w q z : ℕ} [Fact π.Prime] (hπ : π ∣ a) (hx : 0 < x)
    (h : a ^ x * w + q = c ^ z) : (q : ZMod π) = (2 * (g : ZMod π) ^ 2) ^ z := by
  have h1 := congrArg (Nat.cast : ℕ → ZMod π) h
  push_cast at h1
  rw [(ZMod.natCast_eq_zero_iff a π).2 hπ, zero_pow (by omega), zero_mul, zero_add,
    S.cast_c hπ] at h1
  exact h1

/-! ### The core of the case `x < z < y` -/

/-- `D⁴ + b^y N = (c^Z)²` is impossible for `y > 2Z`, `N ≥ 1`, `D` odd and prime to `f`:
the factor `f^y` must divide `c^Z + D²`, which makes `-1` a square modulo `ℓ ≡ 3 (mod 4)`. -/
theorem sq_add_ne {D y Z N : ℕ} (hD : D % 2 = 1) (hℓD : ¬ ℓ ∣ D) (hN : 0 < N)
    (hy : 2 * Z < y) (h : (D ^ 2) ^ 2 + b ^ y * N = (c ^ Z) ^ 2) : False := by
  have hc4 : c ^ Z % 4 = 1 := by
    have h1 : c % 4 = 1 := by have := S.c8; omega
    rw [Nat.pow_mod, h1]; simp
  have hB4 : D ^ 2 % 4 = 1 := sq_mod_four_of_odd hD
  have hsize := S.two_mul_c_pow_le hy
  have hcast : (c : ZMod ℓ) = (g : ZMod ℓ) ^ 2 := by
    rw [S.hc]; push_cast
    rw [(ZMod.natCast_eq_zero_iff f ℓ).2 S.ℓ_dvd_f]; ring
  obtain ⟨A, hA⟩ : ∃ A, A = c ^ Z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = D ^ 2 := ⟨_, rfl⟩
  rw [← hA, ← hB] at h
  rw [← hA] at hc4 hsize
  rw [← hB] at hB4
  have hbpos : 0 < b ^ y * N := Nat.mul_pos (pow_pos S.b_pos y) hN
  have hBA : B < A := by
    by_contra hle
    have : A ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨d, hd⟩ : ∃ d, A = B + 2 * d := ⟨(A - B) / 2, by omega⟩
  have hdpos : 0 < d := by omega
  have hy0 : 0 < y := by omega
  have hj0 : 0 < j := by have := S.j_odd; omega
  obtain ⟨E, hE⟩ : ∃ E, (r + 1) * y = E + 2 := ⟨(r + 1) * y - 2, by
    have : 3 * 1 ≤ (r + 1) * y := Nat.mul_le_mul (by have := S.hr; omega) hy0
    omega⟩
  have e_b : b ^ y = 4 * (2 ^ E * ℓ ^ (j * y)) := by
    rw [S.b_eq, mul_pow, ← pow_mul, ← pow_mul, hE]; ring
  have hfac : d * (B + d) = 2 ^ E * ℓ ^ (j * y) * N := by
    have e1 : (B + 2 * d) ^ 2 = B ^ 2 + 4 * (d * (B + d)) := by ring
    have e2 : 4 * (2 ^ E * ℓ ^ (j * y)) * N = 4 * (2 ^ E * ℓ ^ (j * y) * N) := by ring
    rw [hd, e1, e_b, e2] at h
    omega
  have hP : 2 ^ E ∣ d := by
    have hc : Nat.Coprime (2 ^ E) (B + d) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    exact hc.dvd_of_dvd_mul_right ⟨ℓ ^ (j * y) * N, by rw [hfac]; ring⟩
  have hQ : ℓ ^ (j * y) ∣ d ∨ ℓ ^ (j * y) ∣ B + d :=
    prime_pow_dvd_or S.hℓ ⟨2 ^ E * N, by rw [hfac]; ring⟩ (by
      rintro ⟨h1, h2⟩
      have h3 : ℓ ∣ B := (Nat.dvd_add_left h1).1 h2
      rw [hB] at h3
      exact hℓD (S.hℓ.dvd_of_dvd_pow h3))
  rcases hQ with hQ | hQ
  · have hc2ℓ : Nat.Coprime (2 ^ E) (ℓ ^ (j * y)) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two S.hℓ).2
        (by have := S.ℓ4; omega))
    have h1 := Nat.le_of_dvd hdpos (hc2ℓ.mul_dvd_of_dvd_of_dvd hP hQ)
    omega
  · have := Fact.mk S.hℓ
    have hℓBd : ℓ ∣ B + d := (dvd_pow_self ℓ (Nat.mul_pos hj0 hy0).ne').trans hQ
    have h0 : ((B + d : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hℓBd
    have hAB : (A : ZMod ℓ) = -(B : ZMod ℓ) := by
      have h1 : (A : ZMod ℓ) = ((B + 2 * d : ℕ) : ZMod ℓ) := by rw [hd]
      push_cast at h1 h0
      rw [h1]; linear_combination 2 * h0
    rw [hA, hB] at hAB
    push_cast at hAB
    rw [hcast] at hAB
    have hD0 : (D : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h1 : IsSquare (-(D : ZMod ℓ) ^ 2) := ⟨(g : ZMod ℓ) ^ Z, by rw [← hAB]; ring⟩
    have h2 : IsSquare ((D : ZMod ℓ) ^ 2) := ⟨D, sq _⟩
    have h3 := h1.div h2
    rw [neg_div, div_self (pow_ne_zero 2 hD0)] at h3
    have := ZMod.exists_sq_eq_neg_one_iff.1 h3
    exact this S.ℓ4

/-- Common core of the case `x < z < y`: `m^x + b^y M = c^z` with `z < y` is impossible when
`m ≡ 3 (mod 8)` is prime to `f` and some prime `π ≡ 3 (mod 8)` dividing `a` divides `M` but
not `m`. (`x = 0` is allowed and covers the cofactor `1`.) -/
theorem xzy_core {m π x z y M : ℕ} (hπ : π.Prime) (hπ8 : π % 8 = 3) (hπa : π ∣ a)
    (hm8 : m % 8 = 3) (hπm : ¬ π ∣ m) (hℓm : ¬ ℓ ∣ m) (hπM : π ∣ M) (hM : 0 < M)
    (hz : 0 < z) (hzy : z < y) (h : m ^ x + b ^ y * M = c ^ z) : False := by
  have h16 : ∃ K, b ^ y * M = 16 * K := by
    obtain ⟨k, hk⟩ := S.four_dvd_g
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
    refine ⟨4 * (f * k) ^ 2 * b ^ y' * M, ?_⟩
    have hb' : b = 8 * (f * k) := by rw [S.hb, hk]; ring
    have e : b ^ (y' + 2) = b ^ y' * b ^ 2 := by ring
    rw [e]; nth_rewrite 2 [hb']; ring
  obtain ⟨K, hK⟩ := h16
  have hc8 : c ^ z % 8 = 1 := by rw [Nat.pow_mod, S.c8]; simp
  have hx2 : x % 2 = 0 := by
    have := crit_pow_mod_eight_of_three m x hm8
    omega
  have := Fact.mk hπ
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  have hm0 : (m : ZMod π) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hz2 : z % 2 = 0 := by
    have hcast : (m : ZMod π) ^ (2 * X) = (c : ZMod π) ^ z := by
      have h1 := congrArg (Nat.cast : ℕ → ZMod π) h
      push_cast at h1
      rw [(ZMod.natCast_eq_zero_iff M π).2 hπM, mul_zero, add_zero] at h1
      exact h1
    have h1 : quadraticChar (ZMod π) ((m : ZMod π) ^ (2 * X)) = 1 := by
      rw [pow_mul']
      exact quadraticChar_sq_one' (pow_ne_zero X hm0)
    rw [hcast, S.cast_c hπa, crit_qc_c_pow hπ8 (S.cast_g_ne_zero (by omega)) z] at h1
    exact crit_even_of_neg_one_pow h1
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  have hc16 : c ^ (2 * Z) % 16 = 1 := by rw [pow_mul, Nat.pow_mod, S.csq16]; simp
  have hm16 : m ^ 2 % 16 = 9 := by
    obtain ⟨k, hk⟩ : ∃ k, m = 8 * k + 3 := ⟨m / 8, by omega⟩
    have e : (8 * k + 3) ^ 2 = 16 * (4 * k ^ 2 + 3 * k) + 9 := by ring
    rw [hk, e]; omega
  have hX2 : X % 2 = 0 := by
    have h1 := crit_pow_mod_sixteen_of_nine (m ^ 2) X hm16
    rw [pow_mul] at h
    omega
  obtain ⟨X', rfl⟩ : ∃ X', X = 2 * X' := ⟨X / 2, by omega⟩
  refine S.sq_add_ne (D := m ^ X') (y := y) (Z := Z) (N := M) ?_ ?_ hM (by omega) ?_
  · rw [Nat.pow_mod]
    have : m % 2 = 1 := by omega
    rw [this]; simp
  · exact fun hd => hℓm (S.hℓ.dvd_of_dvd_pow hd)
  · rw [← pow_mul' c, ← h]; ring

/-- Case `x < z < y` (after cancelling `n^x`); `z = x + β`, `y = z + α`. -/
theorem no_x_lt_z_lt_y {n x α β : ℕ} (hn : 1 < n) (hx : 0 < x) (hα : 0 < α) (hβ : 0 < β)
    (h : a ^ x + b ^ (x + β + α) * n ^ (β + α) = c ^ (x + β) * n ^ β) : False := by
  have hnb : n ^ β ∣ a ^ x := by
    have h1 : n ^ β ∣ b ^ (x + β + α) * n ^ (β + α) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ β ∣ a ^ x + b ^ (x + β + α) * n ^ (β + α) := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_left h1).1 h2
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ β := by positivity
  have h' : q + b ^ (x + β + α) * n ^ α = c ^ (x + β) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (c ^ (x + β)), ← h]; ring
  have hnpow : 1 < n ^ β := Nat.one_lt_pow (by omega) hn
  have hnα : 0 < n ^ α := by positivity
  have hna : ∀ p, p ∣ n → p ∣ b ^ (x + β + α) * n ^ α := fun p hp =>
    Dvd.dvd.mul_left (hp.trans (dvd_pow_self n (by omega))) _
  have hqn : ∀ π, π.Prime → π ∣ a → π ∣ q → ¬ π ∣ n ^ β := fun π hπ hπa hπq hπn => by
    have h1 : π ∣ c ^ (x + β) := by
      rw [← h']; exact dvd_add hπq (hna π (hπ.dvd_of_dvd_pow hπn))
    exact S.not_dvd_c hπ (Or.inl hπa) (hπ.dvd_of_dvd_pow h1)
  -- some prime of `a` divides `n`
  have hprime : p₁ ∣ n ∨ p₂ ∣ n := by
    have hmf : n.minFac.Prime := Nat.minFac_prime (by omega)
    have h1 : n.minFac ∣ a ^ x :=
      ((Nat.minFac_dvd n).trans (dvd_pow_self n (by omega))).trans ⟨q, hq⟩
    have h2 : n.minFac ∣ u * v := by rw [← S.ha]; exact hmf.dvd_of_dvd_pow h1
    rcases (Nat.Prime.dvd_mul hmf).1 h2 with h3 | h3
    · left
      rw [S.hu] at h3
      have := (Nat.prime_dvd_prime_iff_eq hmf S.hp₁).1 (hmf.dvd_of_dvd_pow h3)
      rw [← this]; exact Nat.minFac_dvd n
    · right
      rw [S.hv] at h3
      have := (Nat.prime_dvd_prime_iff_eq hmf S.hp₂).1 (hmf.dvd_of_dvd_pow h3)
      rw [← this]; exact Nat.minFac_dvd n
  have hdvdα : ∀ π, π ∣ n → π ∣ n ^ α := fun π hπ => hπ.trans (dvd_pow_self n (by omega))
  have hdvdβ : ∀ π, π ∣ n → π ∣ n ^ β := fun π hπ => hπ.trans (dvd_pow_self n (by omega))
  rcases crit_split S.hp₁ S.hp₂ ((S.a_eq x).symm.trans hq)
    (hqn p₁ S.hp₁ S.p₁_dvd_a) (hqn p₂ S.hp₂ S.p₂_dvd_a) with h1 | ⟨hqe, -⟩ | ⟨hqe, -⟩ | hqe
  · omega
  · -- `q = u^x`, so `p₂ ∣ n`
    have hp₁q : p₁ ∣ q := by
      rw [hqe]; exact dvd_pow_self p₁ (Nat.mul_ne_zero S.s_ne hx.ne')
    have hp₂n : p₂ ∣ n := by
      rcases hprime with h1 | h1
      · exact absurd (hdvdβ _ h1) (hqn p₁ S.hp₁ S.p₁_dvd_a hp₁q)
      · exact h1
    rw [hqe, pow_mul, ← S.hu] at h'
    exact S.xzy_core S.hp₂ S.p₂8 S.p₂_dvd_a S.hu8 S.p₂_not_dvd_u S.ℓ_not_dvd_u
      (hdvdα _ hp₂n) hnα (by omega) (by omega) h'
  · -- `q = v^x`, so `p₁ ∣ n`
    have hp₂q : p₂ ∣ q := by
      rw [hqe]; exact dvd_pow_self p₂ (Nat.mul_ne_zero S.t_ne hx.ne')
    have hp₁n : p₁ ∣ n := by
      rcases hprime with h1 | h1
      · exact h1
      · exact absurd (hdvdβ _ h1) (hqn p₂ S.hp₂ S.p₂_dvd_a hp₂q)
    rw [hqe, pow_mul, ← S.hv] at h'
    exact S.xzy_core S.hp₁ S.p₁8 S.p₁_dvd_a S.v8 S.p₁_not_dvd_v S.ℓ_not_dvd_v
      (hdvdα _ hp₁n) hnα (by omega) (by omega) h'
  · -- `q = 1`
    rw [hqe] at h'
    rcases hprime with h1 | h1
    · exact S.xzy_core (m := v) (x := 0) (z := x + β) (y := x + β + α) S.hp₁ S.p₁8 S.p₁_dvd_a S.v8 S.p₁_not_dvd_v
        S.ℓ_not_dvd_v (hdvdα _ h1) hnα (by omega) (by omega) (by rw [pow_zero]; exact h')
    · exact S.xzy_core (m := u) (x := 0) (z := x + β) (y := x + β + α) S.hp₂ S.p₂8 S.p₂_dvd_a S.hu8 S.p₂_not_dvd_u
        S.ℓ_not_dvd_u (hdvdα _ h1) hnα (by omega) (by omega) (by rw [pow_zero]; exact h')

/-! ### The case `y < z < x` -/

/-- Case `y < z < x` (after cancelling `n^y`); `z = y + β`, `x = z + α`. -/
theorem no_y_lt_z_lt_x {n y α β : ℕ} (hn : 1 < n) (hy : 0 < y) (hα : 0 < α) (hβ : 0 < β)
    (h : a ^ (y + β + α) * n ^ (β + α) + b ^ y = c ^ (y + β) * n ^ β) : False := by
  have hnb : n ^ β ∣ b ^ y := by
    have h1 : n ^ β ∣ a ^ (y + β + α) * n ^ (β + α) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ β ∣ a ^ (y + β + α) * n ^ (β + α) + b ^ y := by
      rw [h]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_right h1).1 h2
  obtain ⟨q, hq⟩ := hnb
  have hpos : 0 < n ^ β := by positivity
  have h' : a ^ (y + β + α) * n ^ α + q = c ^ (y + β) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_add, ← hq, mul_comm _ (c ^ (y + β)), ← h]; ring
  have hnpow : 1 < n ^ β := Nat.one_lt_pow (by omega) hn
  have hprodpos : 0 < a ^ (y + β + α) * n ^ α :=
    Nat.mul_pos (pow_pos S.a_pos _) (by positivity)
  have hna : ∀ p, p ∣ n → p ∣ a ^ (y + β + α) * n ^ α := fun p hp =>
    Dvd.dvd.mul_left (hp.trans (dvd_pow_self n (by omega))) _
  have hqn : ∀ π, π.Prime → π ∣ b → π ∣ q → ¬ π ∣ n ^ β := fun π hπ hπb hπq hπn => by
    have h1 : π ∣ c ^ (y + β) := by
      rw [← h']; exact dvd_add (hna π (hπ.dvd_of_dvd_pow hπn)) hπq
    exact S.not_dvd_c hπ (Or.inr hπb) (hπ.dvd_of_dvd_pow h1)
  have h2b : 2 ∣ b := by rw [S.hb, mul_assoc]; exact Dvd.intro _ rfl
  have e_b : b ^ y = 2 ^ ((r + 1) * y) * ℓ ^ (j * y) := by
    rw [S.b_eq, mul_pow, ← pow_mul, ← pow_mul]
  have := Fact.mk S.hp₁
  have hg₁ : (g : ZMod p₁) ≠ 0 := S.cast_g_ne_zero (by have := S.p₁8; omega)
  have hcast₁ : (q : ZMod p₁) = (2 * (g : ZMod p₁) ^ 2) ^ (y + β) :=
    S.cast_eq_of_dvd_a S.p₁_dvd_a (by omega) h'
  -- conclusion once `z = y + β` is even and `q` is a square
  have hfin : ∀ w B, y + β = 2 * w → q = B ^ 2 → ¬ p₂ ∣ B → False := by
    intro w B hw hB hBp
    have e : (c ^ w) ^ 2 = c ^ (y + β) := by rw [hw]; ring
    have e2 : (c ^ w) ^ 2 - B ^ 2 = a ^ (y + β + α) * n ^ α := by
      rw [e, ← hB, ← h']; omega
    have hd : v ^ (y + β + α) ∣ (c ^ w) ^ 2 - B ^ 2 :=
      ⟨u ^ (y + β + α) * n ^ α, by rw [e2, S.ha]; ring⟩
    have hBA : B < c ^ w := by
      by_contra hle
      have h1 : (c ^ w) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [e, ← hB] at h1
      omega
    have := crit_pow_dvd_sq_sub S.hp₂ S.p₂_not_dvd_two S.hv (by have := S.v8; omega) S.c_lt
      hBp hBA hd
    omega
  rcases crit_split Nat.prime_two S.hℓ (e_b.symm.trans hq)
    (hqn 2 Nat.prime_two h2b) (hqn ℓ S.hℓ S.ℓ_dvd_b) with h1 | ⟨hqe, hN⟩ | ⟨hqe, -⟩ | hqe
  · omega
  · -- `q = 2^((r+1)y)`, `n^β = ℓ^(jy)`
    have hnℓ : n ∣ ℓ ^ (j * y) := by rw [← hN]; exact dvd_pow_self n (by omega)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow S.hℓ).1 hnℓ
    have hkβ : k * β = j * y := by
      rw [← pow_mul] at hN
      exact Nat.pow_right_injective S.hℓ.two_le hN
    have hpar : ((r + 1) * y) % 2 = (y + β) % 2 := by
      have h1 := congrArg (quadraticChar (ZMod p₁)) hcast₁
      rw [hqe] at h1
      push_cast at h1
      rw [crit_qc_two_pow S.p₁8, crit_qc_c_pow S.p₁8 hg₁] at h1
      exact crit_neg_one_pow_parity h1
    have hboth : (y + β) % 2 = 0 ∧ ((r + 1) * y) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one y with hy0 | hy1
      · have h1 : ((r + 1) * y) % 2 = 0 := by
          obtain ⟨Y, rfl⟩ : ∃ Y, y = 2 * Y := ⟨y / 2, by omega⟩
          rw [show (r + 1) * (2 * Y) = 2 * ((r + 1) * Y) by ring]; omega
        omega
      · have h1 : Odd (k * β) := by
          rw [hkβ]
          exact Nat.odd_mul.2 ⟨Nat.odd_iff.2 S.j_odd, Nat.odd_iff.2 hy1⟩
        have h2 := Nat.odd_iff.1 (Nat.odd_mul.1 h1).2
        omega
    obtain ⟨E, hE⟩ : ∃ E, (r + 1) * y = 2 * E := ⟨(r + 1) * y / 2, by omega⟩
    refine hfin ((y + β) / 2) (2 ^ E) (by omega) (by rw [hqe, hE, pow_mul']) ?_
    exact fun hd => S.p₂_not_dvd_two (S.hp₂.dvd_of_dvd_pow hd)
  · -- `q = f^y`
    have := Fact.mk S.hp₂
    have hg₂ : (g : ZMod p₂) ≠ 0 := S.cast_g_ne_zero (by have := S.p₂8; omega)
    have hcast₂ : (q : ZMod p₂) = (2 * (g : ZMod p₂) ^ 2) ^ (y + β) :=
      S.cast_eq_of_dvd_a S.p₂_dvd_a (by omega) h'
    have hqf : q = f ^ y := by rw [hqe, S.hf, pow_mul]
    have hf₁ : (f : ZMod p₁) = (g : ZMod p₁) := by
      rw [S.hfu]; push_cast
      rw [(ZMod.natCast_eq_zero_iff u p₁).2 S.p₁_dvd_u, zero_add]
    have hf₂ : (f : ZMod p₂) = -(g : ZMod p₂) := by
      have h1 : ((f + g : ℕ) : ZMod p₂) = 0 := by
        rw [← S.hvf]; exact (ZMod.natCast_eq_zero_iff v p₂).2 S.p₂_dvd_v
      push_cast at h1
      linear_combination h1
    have hχ₁ : quadraticChar (ZMod p₁) (g : ZMod p₁) = (-1) ^ r := by
      rw [S.cast_g, crit_qc_two_pow S.p₁8]
    have hχ₂ : quadraticChar (ZMod p₂) (g : ZMod p₂) = (-1) ^ r := by
      rw [S.cast_g, crit_qc_two_pow S.p₂8]
    have h1 : ((-1 : ℤ) ^ r) ^ y = (-1) ^ (y + β) := by
      have h1 := congrArg (quadraticChar (ZMod p₁)) hcast₁
      rw [hqf] at h1
      push_cast at h1
      rw [hf₁, map_pow, hχ₁, crit_qc_c_pow S.p₁8 hg₁] at h1
      exact h1
    have h2 : (-(-1 : ℤ) ^ r) ^ y = (-1) ^ (y + β) := by
      have h2 := congrArg (quadraticChar (ZMod p₂)) hcast₂
      rw [hqf] at h2
      push_cast at h2
      rw [hf₂, map_pow, neg_eq_neg_one_mul (g : ZMod p₂), map_mul,
        crit_qc_neg_one (by have := S.p₂8; omega), hχ₂, crit_qc_c_pow S.p₂8 hg₂] at h2
      rw [neg_eq_neg_one_mul]; exact h2
    have hE : ((-1 : ℤ) ^ r) ^ y ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
    have h3 : (-1 : ℤ) ^ y * ((-1) ^ r) ^ y = 1 * ((-1) ^ r) ^ y := by
      rw [← neg_pow, h2, h1, one_mul]
    have h4 : (-1 : ℤ) ^ y = 1 := mul_right_cancel₀ hE h3
    have hy2 : y % 2 = 0 := crit_even_of_neg_one_pow h4
    have hz2 : (y + β) % 2 = 0 := by
      rw [← pow_mul, mul_comm, pow_mul, h4, one_pow] at h1
      exact crit_even_of_neg_one_pow h1.symm
    obtain ⟨Y, rfl⟩ : ∃ Y, y = 2 * Y := ⟨y / 2, by omega⟩
    refine hfin ((2 * Y + β) / 2) (f ^ Y) (by omega) (by rw [hqf, pow_mul']) ?_
    exact fun hd => S.p₂_not_dvd_f (S.hp₂.dvd_of_dvd_pow hd)
  · -- `q = 1`
    have hz2 : (y + β) % 2 = 0 := by
      have h1 := congrArg (quadraticChar (ZMod p₁)) hcast₁
      rw [hqe] at h1
      push_cast at h1
      rw [map_one, crit_qc_c_pow S.p₁8 hg₁] at h1
      exact crit_even_of_neg_one_pow h1.symm
    refine hfin ((y + β) / 2) 1 (by omega) (by rw [hqe]; norm_num) ?_
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := S.p₂8
    omega

/-! ### The primitive case `n = 1` -/

/-- The primitive equation `a^x + b^y = c^z` has only the solution `(2, 2, 2)`. -/
theorem primitive {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : a ^ x + b ^ y = c ^ z) : x = 2 ∧ y = 2 ∧ z = 2 := by
  have hj0 : 0 < j := by have := S.j_odd; omega
  -- `x` is even (mod `ℓ`)
  have hx2 : x % 2 = 0 := by
    have := Fact.mk S.hℓ
    have hℓ4 := S.ℓ4
    have hg0 : (g : ZMod ℓ) ≠ 0 := S.cast_g_ne_zero hℓ4
    have hf0 : (f : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff f ℓ).2 S.ℓ_dvd_f
    have hb0 : (b : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff b ℓ).2 S.ℓ_dvd_b
    have hc' : (c : ZMod ℓ) = (g : ZMod ℓ) ^ 2 := by
      rw [S.hc]; push_cast; rw [hf0]; ring
    have ha' : (a : ZMod ℓ) = -1 * (g : ZMod ℓ) ^ 2 := by
      have h1 : ((a + g ^ 2 : ℕ) : ZMod ℓ) = ((f ^ 2 : ℕ) : ZMod ℓ) := by rw [S.a_add]
      push_cast at h1
      rw [hf0] at h1
      linear_combination h1
    have h1 := congrArg (Nat.cast : ℕ → ZMod ℓ) h
    push_cast at h1
    rw [hb0, zero_pow (by omega), add_zero, ha', hc'] at h1
    have h2 := congrArg (quadraticChar (ZMod ℓ)) h1
    rw [map_pow, map_pow, map_mul, crit_qc_neg_one hℓ4, quadraticChar_sq_one' hg0, mul_one,
      one_pow] at h2
    exact crit_even_of_neg_one_pow h2
  -- `z` is even (mod `p₂`)
  have hz2 : z % 2 = 0 := by
    have := Fact.mk S.hp₂
    have hp8 := S.p₂8
    have hg0 : (g : ZMod p₂) ≠ 0 := S.cast_g_ne_zero (by omega)
    have ha0 : (a : ZMod p₂) = 0 := (ZMod.natCast_eq_zero_iff a p₂).2 S.p₂_dvd_a
    have hf₂ : (f : ZMod p₂) = -(g : ZMod p₂) := by
      have h1 : ((f + g : ℕ) : ZMod p₂) = 0 := by
        rw [← S.hvf]; exact (ZMod.natCast_eq_zero_iff v p₂).2 S.p₂_dvd_v
      push_cast at h1
      linear_combination h1
    have hb' : (b : ZMod p₂) = -1 * (2 * (g : ZMod p₂) ^ 2) := by
      rw [S.hb]; push_cast; rw [hf₂]; ring
    have h1 := congrArg (Nat.cast : ℕ → ZMod p₂) h
    push_cast at h1
    rw [ha0, zero_pow (by omega), zero_add, hb', S.cast_c S.p₂_dvd_a] at h1
    have h2 := congrArg (quadraticChar (ZMod p₂)) h1
    rw [crit_qc_c_pow hp8 hg0, map_pow, map_mul, crit_qc_neg_one (by omega), map_mul,
      crit_qc_two hp8, quadraticChar_sq_one' hg0] at h2
    norm_num at h2
    exact crit_even_of_neg_one_pow h2.symm
  -- `y ≡ z (mod 2)` (mod `p₁`)
  have hy2 : y % 2 = 0 := by
    have := Fact.mk S.hp₁
    have hp8 := S.p₁8
    have hg0 : (g : ZMod p₁) ≠ 0 := S.cast_g_ne_zero (by omega)
    have ha0 : (a : ZMod p₁) = 0 := (ZMod.natCast_eq_zero_iff a p₁).2 S.p₁_dvd_a
    have hf₁ : (f : ZMod p₁) = (g : ZMod p₁) := by
      rw [S.hfu]; push_cast
      rw [(ZMod.natCast_eq_zero_iff u p₁).2 S.p₁_dvd_u, zero_add]
    have hb' : (b : ZMod p₁) = 2 * (g : ZMod p₁) ^ 2 := by
      rw [S.hb]; push_cast; rw [hf₁]; ring
    have h1 := congrArg (Nat.cast : ℕ → ZMod p₁) h
    push_cast at h1
    rw [ha0, zero_pow (by omega), zero_add, hb', S.cast_c S.p₁_dvd_a] at h1
    have h2 := congrArg (quadraticChar (ZMod p₁)) h1
    rw [crit_qc_c_pow hp8 hg0, crit_qc_c_pow hp8 hg0] at h2
    have := crit_neg_one_pow_parity h2
    omega
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, y = 2 * Y := ⟨y / 2, by omega⟩
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  have hX : 0 < X := by omega
  have hY : 0 < Y := by omega
  -- it suffices to prove `X = 1` and `Y = 1`
  suffices hXY : X = 1 ∧ Y = 1 by
    obtain ⟨rfl, rfl⟩ := hXY
    have h1 : c ^ (2 * Z) = c ^ 2 := by rw [← h, ← S.pyth]
    have hc2 : 2 ≤ c := by
      have h3 := pow_pos S.f_pos 2
      have h4 := pow_pos S.g_pos 2
      have h5 := S.hc
      clear * - h3 h4 h5
      omega
    have h2 : 2 * Z = 2 := Nat.pow_right_injective hc2 h1
    clear * - h2
    omega
  rw [pow_mul' a, pow_mul' c] at h
  have hA4 : c ^ Z % 4 = 1 := by
    have h1 : c % 4 = 1 := by have := S.c8; omega
    rw [Nat.pow_mod, h1]; simp
  have hB4 : a ^ X % 4 = 1 := by
    have h1 : a % 4 = 1 := by have := S.a8; omega
    rw [Nat.pow_mod, h1]; simp
  have hBpos : 0 < a ^ X := pow_pos S.a_pos X
  have hbpos : 0 < b ^ (2 * Y) := pow_pos S.b_pos _
  have hBA : a ^ X < c ^ Z := by
    by_contra hle
    have : (c ^ Z) ^ 2 ≤ (a ^ X) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨A, hA⟩ : ∃ A, A = c ^ Z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = a ^ X := ⟨_, rfl⟩
  rw [← hA, ← hB] at h hBA
  rw [← hA] at hA4
  rw [← hB] at hB4 hBpos
  obtain ⟨d, hd⟩ : ∃ d, A = B + 2 * d := ⟨(A - B) / 2, by omega⟩
  have hdpos : 0 < d := by omega
  -- `(r + 1) Y = E + 1`, `T = 2^E`
  obtain ⟨E, hE⟩ : ∃ E, (r + 1) * Y = E + 2 := ⟨(r + 1) * Y - 2, by
    have : 3 * 1 ≤ (r + 1) * Y := Nat.mul_le_mul (by have := S.hr; omega) hY
    omega⟩
  obtain ⟨T, hT⟩ : ∃ T, T = 2 ^ (E + 1) := ⟨_, rfl⟩
  have hT2 : T % 2 = 0 := by rw [hT, pow_succ]; omega
  have hTpos : 0 < T := by rw [hT]; positivity
  have e_b : b ^ (2 * Y) = 4 * (T ^ 2 * (f ^ Y) ^ 2) := by
    rw [S.b_eq, mul_pow, ← pow_mul, hT, S.hf, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
      show (r + 1) * (2 * Y) = 2 * ((r + 1) * Y) by ring, hE]
    ring
  have hfac : d * (B + d) = T ^ 2 * (f ^ Y) ^ 2 := by
    have e1 : (B + 2 * d) ^ 2 = B ^ 2 + 4 * (d * (B + d)) := by ring
    rw [hd, e1, e_b] at h
    omega
  have hT2e : T ^ 2 = 2 ^ (2 * (E + 1)) := by rw [hT, ← pow_mul']
  have hf2e : (f ^ Y) ^ 2 = ℓ ^ (j * Y * 2) := by rw [S.hf]; ring
  have hP : T ^ 2 ∣ d := by
    have hc : Nat.Coprime (T ^ 2) (B + d) := by
      rw [hT2e]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    exact hc.dvd_of_dvd_mul_right ⟨(f ^ Y) ^ 2, hfac⟩
  have hQ : (f ^ Y) ^ 2 ∣ d ∨ (f ^ Y) ^ 2 ∣ B + d := by
    rw [hf2e]
    refine prime_pow_dvd_or S.hℓ ⟨T ^ 2, by rw [hfac, hf2e]; ring⟩ ?_
    rintro ⟨h1, h2⟩
    have h3 : ℓ ∣ B := (Nat.dvd_add_left h1).1 h2
    rw [hB] at h3
    exact S.ℓ_not_dvd_a (S.hℓ.dvd_of_dvd_pow h3)
  have hcTf : Nat.Coprime (T ^ 2) ((f ^ Y) ^ 2) := by
    rw [hT2e, hf2e]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two S.hℓ).2
      (by have := S.ℓ4; omega))
  have hfYpos : 0 < (f ^ Y) ^ 2 := pow_pos (pow_pos S.f_pos Y) 2
  have hT2pos : 0 < T ^ 2 := pow_pos hTpos 2
  have hBd : B + T ^ 2 = (f ^ Y) ^ 2 := by
    rcases hQ with hQ | hQ
    · exfalso
      obtain ⟨-, h2⟩ := eq_of_mul_eq_of_dvd (P := T ^ 2 * (f ^ Y) ^ 2) (Q := 1)
        (d := d) (s := B + d) (Nat.mul_pos hT2pos hfYpos) (by norm_num)
        (by rw [mul_one]; exact hfac) (hcTf.mul_dvd_of_dvd_of_dvd hP hQ) (one_dvd _)
      omega
    · obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd hT2pos hfYpos hfac hP hQ
      omega
  -- `f^Y = T + P`, `P (P + 2T) = a^X`
  have hTf : T < f ^ Y := by
    by_contra hle
    have : (f ^ Y) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨P, hPdef⟩ : ∃ P, f ^ Y = T + P := ⟨f ^ Y - T, by omega⟩
  have hPpos : 0 < P := by omega
  have hPQ : P * (P + 2 * T) = u ^ X * v ^ X := by
    have e1 : (T + P) ^ 2 = T ^ 2 + P * (P + 2 * T) := by ring
    have e2 : B = u ^ X * v ^ X := by rw [hB, S.ha, mul_pow]
    rw [hPdef, e1] at hBd
    omega
  have hfodd : f ^ Y % 2 = 1 := by
    have h1 : f % 2 = 1 := by have := S.f4; omega
    rw [Nat.pow_mod, h1]; simp
  have hPodd : P % 2 = 1 := by omega
  have hcPQ : Nat.Coprime P (P + 2 * T) := by
    have h1 : Nat.Coprime P (2 * T) := by
      have e : 2 * T = 2 ^ (E + 2) := by rw [hT]; ring
      rw [e]
      exact Nat.Coprime.pow_right _ (Nat.Coprime.symm
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)))
    simpa using h1
  have hnot : ∀ π : ℕ, π.Prime → ¬ (π ∣ P ∧ π ∣ P + 2 * T) := fun π hπ ⟨h1, h2⟩ =>
    not_dvd_of_cop hπ h1 hcPQ h2
  have huX : u ^ X ∣ P ∨ u ^ X ∣ P + 2 * T := by
    rw [S.hu, ← pow_mul]
    exact prime_pow_dvd_or S.hp₁ ⟨v ^ X, by rw [hPQ, S.hu, ← pow_mul]⟩ (hnot p₁ S.hp₁)
  have hvX : v ^ X ∣ P ∨ v ^ X ∣ P + 2 * T := by
    rw [S.hv, ← pow_mul]
    exact prime_pow_dvd_or S.hp₂ ⟨u ^ X, by rw [hPQ, S.hv, ← pow_mul]; ring⟩ (hnot p₂ S.hp₂)
  have hcuvX : Nat.Coprime (u ^ X) (v ^ X) := Nat.Coprime.pow _ _ S.cop_uv
  have huXpos : 0 < u ^ X := pow_pos (by have := S.hu8; omega) X
  have hvXpos : 0 < v ^ X := pow_pos (by have := S.v8; omega) X
  have hg4 : 4 ≤ g := by
    obtain ⟨k, hk⟩ := S.four_dvd_g
    have := S.g_pos
    omega
  have hTm : 2 * T = 2 ^ (E + 2) := by rw [hT]; ring
  rcases huX with huX | huX <;> rcases hvX with hvX | hvX
  · -- both divide `P`: impossible
    exfalso
    have h1 := Nat.le_of_dvd hPpos (hcuvX.mul_dvd_of_dvd_of_dvd huX hvX)
    rw [← hPQ] at h1
    have h2 : P * 2 ≤ P * (P + 2 * T) := Nat.mul_le_mul_left P (by omega)
    omega
  · -- `P = u^X`, `P + 2T = v^X`
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd huXpos hvXpos hPQ huX hvX
    have h3 : (u + 2 * g) ^ X = u ^ X + 2 ^ (E + 2) := by
      rw [← S.v_eq, ← h2, ← h1, hTm]
    have hX1 := crit_pow_sub_pow_two (by have := S.hu8; omega) (by omega) (by omega) hX h3
    refine ⟨hX1, ?_⟩
    rw [hX1, pow_one] at h1 h2
    have h4 : f ^ Y = f ^ 1 := by
      rw [pow_one, hPdef]
      have := S.hfu; have := S.v_eq
      omega
    exact Nat.pow_right_injective (by have := S.f4; omega : 2 ≤ f) h4
  · -- `P = v^X`, `P + 2T = u^X`: impossible since `u ≤ v`
    exfalso
    have hPQ' : P * (P + 2 * T) = v ^ X * u ^ X := by rw [hPQ, mul_comm]
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd hvXpos huXpos hPQ' hvX huX
    have h3 : u ^ X ≤ v ^ X := Nat.pow_le_pow_left (by have := S.v_eq; omega) X
    omega
  · -- `P = 1`, `P + 2T = a^X`
    exfalso
    have hPQ' : P * (P + 2 * T) = 1 * (u ^ X * v ^ X) := by rw [hPQ, one_mul]
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_dvd (by norm_num) (Nat.mul_pos huXpos hvXpos) hPQ'
      (one_dvd _) (hcuvX.mul_dvd_of_dvd_of_dvd huX hvX)
    have e2 : u ^ X * v ^ X = a ^ X := by rw [S.ha, mul_pow]
    rw [e2] at h2
    have ha8 := S.a8
    have ha9 : 9 ≤ a := by
      have h3 : 3 * 3 ≤ u * v :=
        Nat.mul_le_mul (by have := S.hu8; omega) (by have := S.v8; omega)
      rw [S.ha]; omega
    obtain ⟨D, hDdef⟩ : ∃ D, a = 1 + D := ⟨a - 1, by omega⟩
    have h3 : (1 + D) ^ X = 1 ^ X + 2 ^ (E + 2) := by
      rw [← hDdef, ← h2, h1, one_pow, hTm]
    have hX1 := crit_pow_sub_pow_two (by norm_num) (by omega) (by omega) hX h3
    rw [hX1, pow_one] at h2
    -- `2 f^Y = a + 1`
    have h5 : 2 * f ^ Y = a + 1 := by omega
    have hadd := S.a_add
    rcases Nat.lt_or_ge Y 2 with hY2 | hY2
    · obtain rfl : Y = 1 := by omega
      rw [pow_one] at h5 hPdef
      -- `f = T + 1` with `T = g`
      have hTg : T = g := by
        rw [hT, S.hg]
        have : r + 1 = E + 2 := by omega
        have : r = E + 1 := by omega
        rw [this]
      have := S.hfu; have := S.hu8
      omega
    · have h6 : f ^ 2 ≤ f ^ Y := Nat.pow_le_pow_right S.f_pos hY2
      have := pow_pos S.g_pos 2
      omega

/-! ### The criterion -/

/-- **The criterion, all `n ≥ 1`.** -/
theorem jesmanowiczFor (n : ℕ) (hn : 0 < n) : JesmanowiczFor a b c n := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  swap
  · obtain rfl : n = 1 := by omega
    intro x y z hs
    obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
    exact S.primitive hx hy hz h
  intro x y z hs
  rcases hs.strict_cases_of_one_lt S.prim hn1 with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · -- `x < z < y`
    exfalso
    obtain ⟨hx, hy, hz, heq⟩ := hs
    obtain ⟨β, rfl⟩ : ∃ β, z = x + β := ⟨z - x, by omega⟩
    obtain ⟨α, rfl⟩ : ∃ α, y = x + β + α := ⟨y - (x + β), by omega⟩
    refine S.no_x_lt_z_lt_y (n := n) (x := x) (α := α) (β := β) hn1 hx
      (by omega) (by omega) ?_
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ x by positivity)
    calc n ^ x * (a ^ x + b ^ (x + β + α) * n ^ (β + α))
        = (a * n) ^ x + (b * n) ^ (x + β + α) := by ring
      _ = (c * n) ^ (x + β) := heq
      _ = n ^ x * (c ^ (x + β) * n ^ β) := by ring
  · -- `y < z < x`
    exfalso
    obtain ⟨hx, hy, hz, heq⟩ := hs
    obtain ⟨β, rfl⟩ : ∃ β, z = y + β := ⟨z - y, by omega⟩
    obtain ⟨α, rfl⟩ : ∃ α, x = y + β + α := ⟨x - (y + β), by omega⟩
    refine S.no_y_lt_z_lt_x (n := n) (y := y) (α := α) (β := β) hn1 hy
      (by omega) (by omega) ?_
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ y by positivity)
    calc n ^ y * (a ^ (y + β + α) * n ^ (β + α) + b ^ y)
        = (a * n) ^ (y + β + α) + (b * n) ^ y := by ring
      _ = (c * n) ^ (y + β) := heq
      _ = n ^ y * (c ^ (y + β) * n ^ β) := by ring

end

end CritData

/-! ## The criterion in closed form -/

/-- **Main theorem (criterion for Jeśmanowicz' conjecture, every `n ≥ 1`).**
Let `g = 2^r` with `r ≥ 2` and let `f > g` be such that `f`, `f - g` and `f + g` are prime
powers and `f - g ≡ 3 (mod 8)`. Then for the primitive Pythagorean triple
`(a, b, c) = (f² - g², 2fg, f² + g²)` and every `n ≥ 1`, the only solution in positive
integers of `(a n)^x + (b n)^y = (c n)^z` is `x = y = z = 2`. -/
theorem jesmanowiczFor_of_criterion {r f : ℕ} (hr : 2 ≤ r) (hf : IsPrimePow f)
    (hu : IsPrimePow (f - 2 ^ r)) (hv : IsPrimePow (f + 2 ^ r)) (h8 : (f - 2 ^ r) % 8 = 3)
    (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor (f ^ 2 - (2 ^ r) ^ 2) (2 * f * 2 ^ r) (f ^ 2 + (2 ^ r) ^ 2) n := by
  obtain ⟨ℓ, j, hℓ, -, hfe⟩ := (isPrimePow_nat_iff _).1 hf
  obtain ⟨p₁, s, hp₁, -, hue⟩ := (isPrimePow_nat_iff _).1 hu
  obtain ⟨p₂, t, hp₂, -, hve⟩ := (isPrimePow_nat_iff _).1 hv
  have hfu : f = (f - 2 ^ r) + 2 ^ r := by omega
  have S : CritData r j s t ℓ p₁ p₂ f (2 ^ r) (f - 2 ^ r) (f + 2 ^ r)
      ((f - 2 ^ r) * (f + 2 ^ r)) (2 * f * 2 ^ r) (f ^ 2 + (2 ^ r) ^ 2) :=
    ⟨hr, hℓ, hp₁, hp₂, rfl, hfe.symm, hue.symm, hve.symm, hfu, rfl, h8, rfl, rfl, rfl⟩
  have e : f ^ 2 - (2 ^ r) ^ 2 = (f - 2 ^ r) * (f + 2 ^ r) := by
    have := S.uv_eq
    omega
  rw [e]
  exact S.jesmanowiczFor n hn

/-- The same with the legs swapped. -/
theorem jesmanowiczFor_of_criterion_swap {r f : ℕ} (hr : 2 ≤ r) (hf : IsPrimePow f)
    (hu : IsPrimePow (f - 2 ^ r)) (hv : IsPrimePow (f + 2 ^ r)) (h8 : (f - 2 ^ r) % 8 = 3)
    (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor (2 * f * 2 ^ r) (f ^ 2 - (2 ^ r) ^ 2) (f ^ 2 + (2 ^ r) ^ 2) n :=
  jesmanowiczFor_swap.1 (jesmanowiczFor_of_criterion hr hf hu hv h8 n hn)

/-- The primitive Pythagorean triple attached to the criterion. -/
theorem isPrimitivePythagorean_of_criterion {r f : ℕ} (hr : 2 ≤ r) (hf : IsPrimePow f)
    (hu : IsPrimePow (f - 2 ^ r)) (hv : IsPrimePow (f + 2 ^ r)) (h8 : (f - 2 ^ r) % 8 = 3) :
    IsPrimitivePythagorean (f ^ 2 - (2 ^ r) ^ 2) (2 * f * 2 ^ r) (f ^ 2 + (2 ^ r) ^ 2) := by
  obtain ⟨ℓ, j, hℓ, -, hfe⟩ := (isPrimePow_nat_iff _).1 hf
  obtain ⟨p₁, s, hp₁, -, hue⟩ := (isPrimePow_nat_iff _).1 hu
  obtain ⟨p₂, t, hp₂, -, hve⟩ := (isPrimePow_nat_iff _).1 hv
  have hfu : f = (f - 2 ^ r) + 2 ^ r := by omega
  have S : CritData r j s t ℓ p₁ p₂ f (2 ^ r) (f - 2 ^ r) (f + 2 ^ r)
      ((f - 2 ^ r) * (f + 2 ^ r)) (2 * f * 2 ^ r) (f ^ 2 + (2 ^ r) ^ 2) :=
    ⟨hr, hℓ, hp₁, hp₂, rfl, hfe.symm, hue.symm, hve.symm, hfu, rfl, h8, rfl, rfl, rfl⟩
  have e : f ^ 2 - (2 ^ r) ^ 2 = (f - 2 ^ r) * (f + 2 ^ r) := by
    have := S.uv_eq
    omega
  rw [e]
  exact S.prim

/-- **The sub-family `f - g = 3`.** If `r ≥ 2` and both `2^r + 3` and `2^(r+1) + 3` are prime,
then Jeśmanowicz' conjecture holds, for every `n ≥ 1`, for the triple
`(3 (2^(r+1) + 3), 2^(r+1) (2^r + 3), (2^r + 3)² + 2^(2r))`
(`r = 2, 3, 6, 15` give `(33, 56, 65)`, `(57, 176, 185)`, `(393, 8576, 8585)`,
`(196617, 2147680256, 2147680265)`). -/
theorem jesmanowiczFor_two_pow_add_three {r : ℕ} (hr : 2 ≤ r) (h1 : (2 ^ r + 3).Prime)
    (h2 : (2 ^ (r + 1) + 3).Prime) (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor (3 * (2 ^ (r + 1) + 3)) (2 ^ (r + 1) * (2 ^ r + 3))
      ((2 ^ r + 3) ^ 2 + (2 ^ r) ^ 2) n := by
  have S : CritData r 1 1 1 (2 ^ r + 3) 3 (2 ^ (r + 1) + 3) (2 ^ r + 3) (2 ^ r) 3
      (2 ^ (r + 1) + 3) (3 * (2 ^ (r + 1) + 3)) (2 ^ (r + 1) * (2 ^ r + 3))
      ((2 ^ r + 3) ^ 2 + (2 ^ r) ^ 2) :=
    ⟨hr, h1, Nat.prime_three, h2, rfl, (pow_one _).symm, (pow_one _).symm, (pow_one _).symm,
      by ring, by ring, by norm_num, rfl, by ring, rfl⟩
  exact S.jesmanowiczFor n hn

/-! ## Instances

All of the following are unconditional (the case `n = 1` is part of the criterion). -/

/-- `(f, g) = (7, 2^2)`, `f - g = 3`, `f + g = 11`. -/
theorem crit_jesmanowiczFor_33_56_65 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 33 56 65 n :=
  jesmanowiczFor_of_criterion (r := 2) (f := 7) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 7))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 3))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11))
    (by norm_num) n hn

/-- `(f, g) = (11, 2^3)`, `f - g = 3`, `f + g = 19`. -/
theorem crit_jesmanowiczFor_57_176_185 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 57 176 185 n :=
  jesmanowiczFor_of_criterion (r := 3) (f := 11) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 3))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 19))
    (by norm_num) n hn

/-- `(f, g) = (19, 2^3)`, `f - g = 11`, `f + g = 3^3`. -/
theorem crit_jesmanowiczFor_297_304_425 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 297 304 425 n :=
  jesmanowiczFor_of_criterion (r := 3) (f := 19) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 19))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11))
    ((isPrimePow_nat_iff _).2 ⟨3, 3, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

/-- `(f, g) = (23, 2^2)`, `f - g = 19`, `f + g = 3^3`. -/
theorem crit_jesmanowiczFor_513_184_545 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 513 184 545 n :=
  jesmanowiczFor_of_criterion (r := 2) (f := 23) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 23))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 19))
    ((isPrimePow_nat_iff _).2 ⟨3, 3, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

/-- `(f, g) = (3^3, 2^4)`, `f - g = 11`, `f + g = 43`. -/
theorem crit_jesmanowiczFor_473_864_985 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 473 864 985 n :=
  jesmanowiczFor_of_criterion (r := 4) (f := 27) (by norm_num)
    ((isPrimePow_nat_iff _).2 ⟨3, 3, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 43))
    (by norm_num) n hn

/-- `(f, g) = (43, 2^4)`, `f - g = 3^3`, `f + g = 59`. -/
theorem crit_jesmanowiczFor_1593_1376_2105 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 1593 1376 2105 n :=
  jesmanowiczFor_of_criterion (r := 4) (f := 43) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 43))
    ((isPrimePow_nat_iff _).2 ⟨3, 3, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 59))
    (by norm_num) n hn

/-- `(f, g) = (67, 2^6)`, `f - g = 3`, `f + g = 131`. -/
theorem crit_jesmanowiczFor_393_8576_8585 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 393 8576 8585 n :=
  jesmanowiczFor_of_criterion (r := 6) (f := 67) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 67))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 3))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 131))
    (by norm_num) n hn

/-- `(f, g) = (211, 2^5)`, `f - g = 179`, `f + g = 3^5`. -/
theorem crit_jesmanowiczFor_43497_13504_45545 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 43497 13504 45545 n :=
  jesmanowiczFor_of_criterion (r := 5) (f := 211) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 211))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 179))
    ((isPrimePow_nat_iff _).2 ⟨3, 5, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

/-- `(f, g) = (227, 2^4)`, `f - g = 211`, `f + g = 3^5`. -/
theorem crit_jesmanowiczFor_51273_7264_51785 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 51273 7264 51785 n :=
  jesmanowiczFor_of_criterion (r := 4) (f := 227) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 227))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 211))
    ((isPrimePow_nat_iff _).2 ⟨3, 5, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

/-- `(f, g) = (3^5, 2^6)`, `f - g = 179`, `f + g = 307`. -/
theorem crit_jesmanowiczFor_54953_31104_63145 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 54953 31104 63145 n :=
  jesmanowiczFor_of_criterion (r := 6) (f := 243) (by norm_num)
    ((isPrimePow_nat_iff _).2 ⟨3, 5, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 179))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 307))
    (by norm_num) n hn

/-- `(f, g) = (1163, 2^10)`, `f - g = 139`, `f + g = 3^7`. -/
theorem crit_jesmanowiczFor_303993_2381824_2401145 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 303993 2381824 2401145 n :=
  jesmanowiczFor_of_criterion (r := 10) (f := 1163) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1163))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 139))
    ((isPrimePow_nat_iff _).2 ⟨3, 7, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

/-- `(f, g) = (8219, 2^13)`, `f - g = 3^3`, `f + g = 16411`. -/
theorem crit_jesmanowiczFor_443097_134660096_134660825 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 443097 134660096 134660825 n :=
  jesmanowiczFor_of_criterion (r := 13) (f := 8219) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 8219))
    ((isPrimePow_nat_iff _).2 ⟨3, 3, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 16411))
    (by norm_num) n hn

/-- `(f, g) = (11491, 2^13)`, `f - g = 3299`, `f + g = 3^9`. -/
theorem crit_jesmanowiczFor_64934217_188268544_199151945 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 64934217 188268544 199151945 n :=
  jesmanowiczFor_of_criterion (r := 13) (f := 11491) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11491))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 3299))
    ((isPrimePow_nat_iff _).2 ⟨3, 9, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

/-- `(f, g) = (3^9, 2^14)`, `f - g = 3299`, `f + g = 36067`. -/
theorem crit_jesmanowiczFor_118985033_644972544_655855945 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 118985033 644972544 655855945 n :=
  jesmanowiczFor_of_criterion (r := 14) (f := 19683) (by norm_num)
    ((isPrimePow_nat_iff _).2 ⟨3, 9, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 3299))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 36067))
    (by norm_num) n hn

/-- `(f, g) = (32771, 2^15)`, `f - g = 3`, `f + g = 65539`. -/
theorem crit_jesmanowiczFor_196617_2147680256_2147680265 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 196617 2147680256 2147680265 n :=
  jesmanowiczFor_of_criterion (r := 15) (f := 32771) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 32771))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 3))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 65539))
    (by norm_num) n hn

/-- `(f, g) = (144379, 2^15)`, `f - g = 111611`, `f + g = 3^11`. -/
theorem crit_jesmanowiczFor_19771553817_9462022144_21919037465 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 19771553817 9462022144 21919037465 n :=
  jesmanowiczFor_of_criterion (r := 15) (f := 144379) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 144379))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 111611))
    ((isPrimePow_nat_iff _).2 ⟨3, 11, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

/-- `(f, g) = (543971, 2^19)`, `f - g = 3^9`, `f + g = 1068259`. -/
theorem crit_jesmanowiczFor_21026541897_570394935296_570782355785 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 21026541897 570394935296 570782355785 n :=
  jesmanowiczFor_of_criterion (r := 19) (f := 543971) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 543971))
    ((isPrimePow_nat_iff _).2 ⟨3, 9, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1068259))
    (by norm_num) n hn

/-- `(f, g) = (3^13, 2^6)`, `f - g = 1594259`, `f + g = 1594387`. -/
theorem crit_jesmanowiczFor_2541865824233_204073344_2541865832425 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 2541865824233 204073344 2541865832425 n :=
  jesmanowiczFor_of_criterion (r := 6) (f := 1594323) (by norm_num)
    ((isPrimePow_nat_iff _).2 ⟨3, 13, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1594259))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1594387))
    (by norm_num) n hn

/-- `(f, g) = (1594331, 2^3)`, `f - g = 3^13`, `f + g = 1594339`. -/
theorem crit_jesmanowiczFor_2541891337497_25509296_2541891337625 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 2541891337497 25509296 2541891337625 n :=
  jesmanowiczFor_of_criterion (r := 3) (f := 1594331) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1594331))
    ((isPrimePow_nat_iff _).2 ⟨3, 13, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1594339))
    (by norm_num) n hn

/-- `(f, g) = (1594387, 2^6)`, `f - g = 3^13`, `f + g = 1594451`. -/
theorem crit_jesmanowiczFor_2542069901673_204081536_2542069909865 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 2542069901673 204081536 2542069909865 n :=
  jesmanowiczFor_of_criterion (r := 6) (f := 1594387) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1594387))
    ((isPrimePow_nat_iff _).2 ⟨3, 13, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 1594451))
    (by norm_num) n hn

/-- `(f, g) = (3^15, 2^4)`, `f - g = 14348891`, `f + g = 14348923`. -/
theorem crit_jesmanowiczFor_205891132094393_459165024_205891132094905 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 205891132094393 459165024 205891132094905 n :=
  jesmanowiczFor_of_criterion (r := 4) (f := 14348907) (by norm_num)
    ((isPrimePow_nat_iff _).2 ⟨3, 15, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 14348891))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 14348923))
    (by norm_num) n hn

/-- `(f, g) = (14357099, 2^13)`, `f - g = 3^15`, `f + g = 14365291`. -/
theorem crit_jesmanowiczFor_206126224586937_235226710016_206126358804665 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 206126224586937 235226710016 206126358804665 n :=
  jesmanowiczFor_of_criterion (r := 13) (f := 14357099) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 14357099))
    ((isPrimePow_nat_iff _).2 ⟨3, 15, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 14365291))
    (by norm_num) n hn

/-- `(f, g) = (14414443, 2^16)`, `f - g = 3^15`, `f + g = 14479979`. -/
theorem crit_jesmanowiczFor_207771872032953_1889329872896_207780461967545 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 207771872032953 1889329872896 207780461967545 n :=
  jesmanowiczFor_of_criterion (r := 16) (f := 14414443) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 14414443))
    ((isPrimePow_nat_iff _).2 ⟨3, 15, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 14479979))
    (by norm_num) n hn

/-- `(f, g) = (129136067, 2^12)`, `f - g = 129131971`, `f + g = 3^17`. -/
theorem crit_jesmanowiczFor_16676123783451273_1057882660864_16676123817005705 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 16676123783451273 1057882660864 16676123817005705 n :=
  jesmanowiczFor_of_criterion (r := 12) (f := 129136067) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 129136067))
    (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 129131971))
    ((isPrimePow_nat_iff _).2 ⟨3, 17, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) n hn

end Jesmanowicz

#print axioms Jesmanowicz.jesmanowiczFor_of_criterion
#print axioms Jesmanowicz.jesmanowiczFor_of_criterion_swap
#print axioms Jesmanowicz.isPrimitivePythagorean_of_criterion
#print axioms Jesmanowicz.CritData.jesmanowiczFor
#print axioms Jesmanowicz.CritData.primitive
#print axioms Jesmanowicz.CritData.no_y_lt_z_lt_x
#print axioms Jesmanowicz.CritData.no_x_lt_z_lt_y
#print axioms Jesmanowicz.CritData.sq_add_ne
#print axioms Jesmanowicz.jesmanowiczFor_two_pow_add_three
#print axioms Jesmanowicz.crit_jesmanowiczFor_33_56_65
#print axioms Jesmanowicz.crit_jesmanowiczFor_57_176_185
#print axioms Jesmanowicz.crit_jesmanowiczFor_297_304_425
#print axioms Jesmanowicz.crit_jesmanowiczFor_513_184_545
#print axioms Jesmanowicz.crit_jesmanowiczFor_473_864_985
#print axioms Jesmanowicz.crit_jesmanowiczFor_1593_1376_2105
#print axioms Jesmanowicz.crit_jesmanowiczFor_393_8576_8585
#print axioms Jesmanowicz.crit_jesmanowiczFor_43497_13504_45545
#print axioms Jesmanowicz.crit_jesmanowiczFor_51273_7264_51785
#print axioms Jesmanowicz.crit_jesmanowiczFor_54953_31104_63145
#print axioms Jesmanowicz.crit_jesmanowiczFor_303993_2381824_2401145
#print axioms Jesmanowicz.crit_jesmanowiczFor_443097_134660096_134660825
#print axioms Jesmanowicz.crit_jesmanowiczFor_64934217_188268544_199151945
#print axioms Jesmanowicz.crit_jesmanowiczFor_118985033_644972544_655855945
#print axioms Jesmanowicz.crit_jesmanowiczFor_196617_2147680256_2147680265
#print axioms Jesmanowicz.crit_jesmanowiczFor_19771553817_9462022144_21919037465
#print axioms Jesmanowicz.crit_jesmanowiczFor_21026541897_570394935296_570782355785
#print axioms Jesmanowicz.crit_jesmanowiczFor_2541865824233_204073344_2541865832425
#print axioms Jesmanowicz.crit_jesmanowiczFor_2541891337497_25509296_2541891337625
#print axioms Jesmanowicz.crit_jesmanowiczFor_2542069901673_204081536_2542069909865
#print axioms Jesmanowicz.crit_jesmanowiczFor_205891132094393_459165024_205891132094905
#print axioms Jesmanowicz.crit_jesmanowiczFor_206126224586937_235226710016_206126358804665
#print axioms Jesmanowicz.crit_jesmanowiczFor_207771872032953_1889329872896_207780461967545
#print axioms Jesmanowicz.crit_jesmanowiczFor_16676123783451273_1057882660864_16676123817005705
