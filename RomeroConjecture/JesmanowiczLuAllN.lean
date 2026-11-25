/-
# Jeśmanowicz' conjecture, non-primitive case (`n > 1`), for Lu's family `(4k² - 1, 4k, 4k² + 1)`

STATUS: IN PROGRESS / NOT YET SOLVED

(The status line refers to Jeśmanowicz' conjecture as a whole, which is OPEN and is NOT proved
here; see `RomeroConjecture/Jesmanowicz.lean` for the statement
`Jesmanowicz.JesmanowiczConjecture`. This file proves it only for the special triples and
special cases listed below. A proof for ALL `k` and ALL `n` in Lu's family was NOT obtained.)

Throughout, `a = 4k² - 1 = (2k - 1)(2k + 1)`, `b = 4k`, `c = 4k² + 1 = a + 2`, and the equation
is `(a n)^x + (b n)^y = (c n)^z` in positive integers.

## What IS proved in this file (machine-checked, no `sorry`, no extra axioms)

Main results:

* `lu_no_solution_x_lt_z_lt_y` (**Theorem B**): if `k ≡ 2 (mod 4)` and `2k - 1`, `2k + 1` are
  both prime powers (e.g. twin primes), then for every `n > 1` there is no solution with
  `x < z < y`.
  `lu_no_solution_x_lt_z_lt_y_of_twin_primes` is the special case of twin primes.
* `lu_no_solution_y_lt_z_lt_x` (**Theorem A**): if `k = 2 p^α` with `p` an odd prime, `α` odd,
  `p^α ≢ 1 (mod 8)` and `p^α ≠ 3`, then for every `n > 1` there is no solution with `y < z < x`.
  (No hypothesis on `2k ± 1` here.)
* `jesmanowiczFor_lu_of_two_mul_prime_pow` (**Main theorem**): under the hypotheses of both
  Theorem A and Theorem B, Jeśmanowicz' conjecture holds for `(4k² - 1, 4k, 4k² + 1)` and
  EVERY `n ≥ 1`. (Uses Lu's theorem `jesmanowiczFor_lu` for `n = 1` and the strict reduction
  `IsSolution.strict_cases_of_one_lt` for `n > 1`, both proved elsewhere in this project.)
* `jesmanowiczFor_783_56_785` (`k = 14`, `2k ± 1 = 27, 29`): the conjecture for
  `(783, 56, 785)` and every `n ≥ 1`.
* `jesmanowiczFor_11663_216_11665` (`k = 54`, `2k ± 1 = 107, 109`): the conjecture for
  `(11663, 216, 11665)` and every `n ≥ 1`.

WARNING about the scope of the main theorem: its hypotheses are very restrictive. One of
`4p^α - 1, 4p^α, 4p^α + 1` is divisible by `3`, so apart from `p = 3` one of `2k ± 1` must be a
power of `3`. The only `k` we know to satisfy all hypotheses are `k = 14` and `k = 54`
(`k = 6` satisfies everything except `p^α ≠ 3`). So the "family" theorem amounts, as far as we
know, to the two triples above; Theorems A and B separately apply to many more `k`
(Theorem B to every twin-prime pair `(2k-1, 2k+1)` with `k ≡ 2 (mod 4)`: `k = 2, 6, 30, 54,
90, 114, …`; Theorem A to `k = 10, 14, 22, 26, 38, 46, 54, 58, …`).

Key lemmas (valid in more generality, each fully proved):

* `lu_no_sq` (all `k ≥ 1`): there are no `x > 2v`, `N ≥ 1`, `B` with
  `a^x N + B² = c^(2v)`. (Difference of squares: `a^x` would split as `u^x w^x` with
  `u w = a` and `u, w ≤ 2k`, impossible.) Consequently, in the case `y < z < x`, `z` even and
  cofactor of `b^y` a perfect square cannot both happen — for every `k`.
* `lu_sq_add_bound` (all even `k`): if `X ≡ ±1 (mod 2k)` and `X² + (4k)^y N = c^(2v)`, `N ≥ 1`,
  then `y ≤ 2v`. (Difference of squares: one factor is `≡ 2 (mod 2k)`, so the other is
  divisible by `(4k)^y / 2`.)
* `two_pow_parity_of_mod_eight`, `even_of_sq_modEq_two_pow`: parity of exponents of `2`
  modulo `M ≡ 3, 5 (mod 8)` via the Jacobi symbol `(2/M) = -1`.
* `lu_caseB_core`, `lu_caseB_pow`, `pow_mod_of_sq_mod_eq_one`, `modEq_two_pow_of_eq`,
  `mod_eight_of_pow_mod_eight`, `coprime_add_two_of_odd`, `sq_ne_prime_pow_odd`: auxiliary.

## Proof outline

Let `n > 1`. By the strict reduction only `x < z < y` and `y < z < x` remain.

*Case `x < z < y` (Theorem B).* Cancel `n^x`: `a^x + b^y n^(y-x) = c^z n^(z-x)`, so
`a^x = n^(z-x) q` with `gcd(q, n) = 1` and `q + b^y n^(y-z) = c^z`. Since `2k - 1 = p^s` and
`2k + 1 = r^t` are prime powers, `q ∈ {1, (2k-1)^x, (2k+1)^x}` and some prime `π ∈ {p, r}`
divides `n`; `k ≡ 2 (mod 4)` forces `π ≡ 3, 5 (mod 8)`. Modulo `4k`: `q ≡ 1`, which forces
`x` even when `q ≠ 1` (as `(2k ± 1)² ≡ 1` but `2k ± 1 ≢ 1 (mod 4k)`). So `q = Y²` with
`Y ≡ ±1 (mod 2k)`. Modulo `π`: `Y² ≡ c^z ≡ 2^z`, and `(2/π) = -1` gives `z` even. Then
`lu_sq_add_bound` gives `y ≤ z`, a contradiction.

*Case `y < z < x` (Theorem A).* Cancel `n^y`: `b^y = n^(z-y) q`, `gcd(q, n) = 1`,
`a^x n^(x-z) + q = c^z`. With `b = 8P`, `P = p^α`: `q ∈ {1, P^y, 8^y}`. Modulo
`M = 2k - 1 = 4P - 1 ≡ 3 (mod 8)` we have `c ≡ 2` and `4P ≡ 1`, so `q ≡ 2^z (mod M)` yields:
`z` even if `q = 1` or `q = P^y`; `y ≡ z (mod 2)` if `q = 8^y`.
 - `q = 1`: `lu_no_sq` with `B = 1`.
 - `q = 8^y`: if `y, z` are even, `lu_no_sq`; if both odd, `n^(z-y) = P^y` is a square, but
   `P^y = p^(αy)` with `αy` odd.
 - `q = P^y`: if `y` is even, `lu_no_sq`. If `y` is odd, then `n = 2^t`, `t (z-y) = 3y`, `t` odd;
   modulo `8`, `P^y ≡ P ≢ 1 ≡ c^z` forces `t (x-z) ≤ 2`, so `t = 1`, `x - z ∈ {1, 2}`; modulo `P`
   (`a ≡ -1`, `c ≡ 1`) this gives `P ∣ 3`, contradicting `P ≥ 5`.

## Novelty assessment (read the caveat)

CAVEAT. "Apparently new" below means only: NOT FOUND in the sources listed here, after a
limited search (about a dozen web searches / documents, November 2026). It is NOT a certified
novelty claim. The literature on this conjecture is large and partly in Chinese-language
journals that we could not search; the methods used here (cofactor classification, Jacobi
symbols, difference of squares, congruences) are the standard elementary methods of that
literature, so an equivalent or stronger statement may well exist. A specialist should check
before any claim of originality is made.

Sources checked:
 1. G. Soydan, M. Demirci, I. N. Cangul, A. Togbé, "On the conjecture of Jeśmanowicz",
    arXiv:1706.05480 (survey, 2017), Section 3 (non-primitive triples).
 2. M.-H. Le, R. Scott, R. Styer, "A survey on the ternary purely exponential Diophantine
    equation a^x + b^y = c^z", arXiv:1808.06557 (2018), Section 2.2 (non-primitive cases).
 3. V. T. Nguyen, V. K. Nguyen, P. H. Quy, "A note on Jeśmanowicz' conjecture for non-primitive
    Pythagorean triples", arXiv:2102.10921 (2021) (family `(u² - 4, 4u, u² + 4)`, `u` prime).
 4. N. Fan, J. Luo, "On the conjecture of Jeśmanowicz", AIMS Math. 8 (2023), 14232–14252
    (and Feng–Luo 2022 cited there): odd leg `p^k q^l` with
    `p^k = 2^(m₁) - a^(m₂)`, `q^l = 2^(m₁) + a^(m₂)`, `a ≡ ±3 (mod 8)`.
 5. M. Tang, J.-X. Weng, "Jeśmanowicz' conjecture with Fermat numbers", arXiv:1304.0514.
 6. A. Ghadermarzi, arXiv:2010.07705; Han–Yuan, arXiv:1903.00121 (on Ma–Chen 2017); abstract of
    Yuan–Han, Acta Arith. 184 (2018) — these concern the primitive case or other families.
 7. Web searches for the specific triples `(783, 56, 785)`, `(11663, 216, 11665)` and for
    "non-primitive", "4k²-1 / m²-1, 2m, m²+1", "twin primes / prime powers" (no hits).
 The papers of Deng–Cohen 1998, Le 1999, Yang–Tang 2012, Tang–Yang 2013, Deng 2014, Miyazaki
 2015, Yang–Fu 2015, Ma–Wu 2015, Sun–Cheng 2015 were NOT read directly; their results are
 quoted from the surveys 1 and 2.

What those sources report for `n > 1` in Lu's family (`f = 2k`, `g = 1` in the notation of 2):
 * `k = 2^s` (all `s ≥ 0`): Deng–Cohen 1998 (`k = 1`), Yang–Tang 2012 (`k = 2`), Tang–Yang 2013,
   Deng 2014, Tang–Weng 2014, and in general X.-W. Zhang–W.-P. Zhang 2014 and Miyazaki 2015
   (conjecture true when a leg is a power of `2`).
 * Single triples: `k = 3` (Yang–Weng), `k = 5` (Soydan–Demirci–Cangul–Togbé), `k = 6` (B.-L.
   Liu), `k = 7` (Ling–Weng).
 * Ma–Wu 2015 / Sun–Cheng 2015: true if `P(4k² - 1) ∣ n`; and if `k = p^α` with `p ≡ 3 (mod 4)`
   prime and `P(n) ∤ 4k² - 1` (this settles the case `y < z < x` for those ODD `k`).
 * Le 1999 / Yang–Fu 2015: the general classification of exceptional solutions
   (`x < z < y` with `P(n) ∣ a`, or `y < z < x` with `P(n) ∣ b`).

Classification of the results of this file:
 * `lu_no_sq`, `lu_sq_add_bound` and the helper lemmas: standard techniques, NOT claimed new.
 * Theorem B (`lu_no_solution_x_lt_z_lt_y`): for `k = 2` and `k = 6` it is contained in known
   theorems (Yang–Tang; Liu). As a general statement (all `k ≡ 2 (mod 4)` with `2k ± 1` prime
   powers) it was not found in the sources above; source 4 treats an analogous but different
   family. APPARENTLY NEW (moderate confidence at best).
 * Theorem A (`lu_no_solution_y_lt_z_lt_x`): the published results found concern
   `k = p^α` (`p ≡ 3 mod 4`), not `k = 2 p^α`. APPARENTLY NEW as stated (moderate confidence at
   best); for `k = 6` the conclusion is known (Liu) but our theorem excludes `p^α = 3`.
 * `jesmanowiczFor_783_56_785` and `jesmanowiczFor_11663_216_11665` (and the main theorem that
   yields them): these two triples do not appear in the lists of settled non-primitive cases
   in sources 1–2, and no paper on them was found. APPARENTLY NEW (moderate confidence; a
   post-2018 or non-indexed paper on `(783, 56, 785)` cannot be excluded).

## What is NOT proved

* Jeśmanowicz' conjecture itself (OPEN), and the conjecture for all `k`, all `n` in Lu's family.
* The case `x < z < y` when `k` is odd or `4 ∣ k`, or when `2k ± 1` are not prime powers.
* The case `y < z < x` for `k` not of the form in Theorem A (in particular `p^α ≡ 1 (mod 8)`,
  `α` even, `k` odd, `4 ∣ k`), and the excluded value `p^α = 3` (`k = 6`, known by Liu).
* Re-formalizations of Miyazaki 2015 (`k = 2^s`) and of Ma–Wu 2015 were NOT carried out.
-/
import RomeroConjecture.Jesmanowicz
import RomeroConjecture.JesmanowiczAllN
import RomeroConjecture.JesmanowiczFamilies
import RomeroConjecture.JesmanowiczDemjanenko

namespace Jesmanowicz

open NumberTheorySymbols

/-! ### Elementary helpers -/

/-- If `r² ≡ 1 (mod m)` then `r^w ≡ 1` for even `w` and `r^w ≡ r` for odd `w`. -/
theorem pow_mod_of_sq_mod_eq_one {r m : ℕ} (hm : 1 < m) (h : r ^ 2 % m = 1) (w : ℕ) :
    (w % 2 = 0 → r ^ w % m = 1) ∧ (w % 2 = 1 → r ^ w % m = r % m) := by
  induction w with
  | zero => exact ⟨fun _ => by simp [Nat.mod_eq_of_lt hm], fun h => by omega⟩
  | succ w ih =>
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rw [pow_succ, Nat.mul_mod, ih.2 (by omega), ← Nat.mul_mod, ← sq, h]
    · rw [pow_succ, Nat.mul_mod, ih.1 (by omega), one_mul, Nat.mod_mod]

/-- If `M ≡ 3, 5 (mod 8)` (so that `2` is a quadratic non-residue in the sense of the
Jacobi symbol) and `2^e ≡ 2^f (mod M)`, then `e ≡ f (mod 2)`. -/
theorem two_pow_parity_of_mod_eight {M e f : ℕ} (hM : M % 8 = 3 ∨ M % 8 = 5)
    (h : 2 ^ e ≡ 2 ^ f [MOD M]) : e % 2 = f % 2 := by
  have hodd : Odd M := Nat.odd_iff.2 (by omega)
  have hJ : J(2 | M) = -1 := by
    rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
    simp only [show ¬ (M % 2 = 0) by omega, show ¬ (M % 8 = 1 ∨ M % 8 = 7) by omega, ite_false]
  have h1 : J((2 : ℤ) ^ e | M) = J((2 : ℤ) ^ f | M) := by
    apply jacobiSym.mod_left'
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at this
    exact this
  rw [jacobiSym.pow_left, jacobiSym.pow_left, hJ] at h1
  rcases Nat.even_or_odd e with he | he <;> rcases Nat.even_or_odd f with hf | hf
  · rw [Nat.even_iff] at he hf; omega
  · rw [he.neg_one_pow, hf.neg_one_pow] at h1; norm_num at h1
  · rw [he.neg_one_pow, hf.neg_one_pow] at h1; norm_num at h1
  · rw [Nat.odd_iff] at he hf; omega

/-- If `M ≡ 3, 5 (mod 8)`, `gcd(Y, M) = 1` and `Y² ≡ 2^f (mod M)`, then `f` is even. -/
theorem even_of_sq_modEq_two_pow {M Y f : ℕ} (hM : M % 8 = 3 ∨ M % 8 = 5)
    (hc : Nat.Coprime Y M) (h : Y ^ 2 ≡ 2 ^ f [MOD M]) : f % 2 = 0 := by
  have hodd : Odd M := Nat.odd_iff.2 (by omega)
  have hJ : J(2 | M) = -1 := by
    rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
    simp only [show ¬ (M % 2 = 0) by omega, show ¬ (M % 8 = 1 ∨ M % 8 = 7) by omega, ite_false]
  have h1 : J((Y : ℤ) ^ 2 | M) = J((2 : ℤ) ^ f | M) := by
    apply jacobiSym.mod_left'
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at this
    exact this
  have hg : (Y : ℤ).gcd (M : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hc
  rw [jacobiSym.sq_one' hg, jacobiSym.pow_left, hJ] at h1
  rcases Nat.even_or_odd f with hf | hf
  · rw [Nat.even_iff] at hf; exact hf
  · rw [hf.neg_one_pow] at h1; norm_num at h1

/-! ### The difference-of-squares lemma for the case `y < z < x` -/

/-- **Key lemma A.** Let `a = 4k² - 1`. There are no `x > 2v`, `N ≥ 1`, `B` with
`a^x N + B² = (a + 2)^(2v)`. -/
theorem lu_no_sq {k a x v N B : ℕ} (hk : 0 < k) (ha : a + 1 = 4 * k ^ 2) (hx : 2 * v < x)
    (hN : 0 < N) (h : a ^ x * N + B ^ 2 = (a + 2) ^ (2 * v)) : False := by
  have hk2 : 0 < k ^ 2 := by positivity
  have ha3 : 3 ≤ a := by omega
  have hxpos : 0 < x := by omega
  set C := (a + 2) ^ v with hC
  have hCpos : 0 < C := by positivity
  have hC2 : (a + 2) ^ (2 * v) = C ^ 2 := by rw [hC, ← pow_mul, Nat.mul_comm v 2]
  rw [hC2] at h
  have hpos : 0 < a ^ x * N := by positivity
  have hBC : B < C := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
  obtain ⟨d, hd⟩ : ∃ d, C = B + d := ⟨C - B, by omega⟩
  have hdpos : 0 < d := by omega
  have hprod : d * (2 * B + d) = a ^ x * N := by
    have : (B + d) ^ 2 = B ^ 2 + d * (2 * B + d) := by ring
    rw [hd, this] at h; omega
  -- `a` is odd and coprime to `a + 2`
  have haodd : a % 2 = 1 := by omega
  have hcop2 : Nat.Coprime a 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  have hcopc : Nat.Coprime a (a + 2) := by
    simpa using hcop2
  have hcop : Nat.Coprime (a ^ x) (2 * C) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hcop2 (Nat.Coprime.pow_right _ hcopc))
  set U₁ := Nat.gcd (a ^ x) d with hU₁
  set U₂ := Nat.gcd (a ^ x) (2 * B + d) with hU₂
  have hU12 : Nat.Coprime U₁ U₂ := by
    have h1 : Nat.gcd U₁ U₂ ∣ a ^ x := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have h2 : Nat.gcd U₁ U₂ ∣ 2 * C := by
      have e : 2 * C = d + (2 * B + d) := by omega
      rw [e]
      exact Dvd.dvd.add ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
        ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hmul : U₁ * U₂ = a ^ x := by
    apply Nat.dvd_antisymm
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hU12 (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    · have h1 : Nat.gcd (a ^ x) (d * (2 * B + d)) ∣ U₁ * U₂ := gcd_mul_dvd_mul_gcd _ _ _
      have h2 : Nat.gcd (a ^ x) (d * (2 * B + d)) = a ^ x :=
        Nat.gcd_eq_left (hprod ▸ Dvd.intro _ rfl)
      rwa [h2] at h1
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 hU12) hmul
  obtain ⟨w, hw⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 hU12.symm)
    (show U₂ * U₁ = a ^ x by rw [mul_comm]; exact hmul)
  have huw : u * w = a := by
    have : (u * w) ^ x = a ^ x := by rw [mul_pow, ← hu, ← hw, hmul]
    exact Nat.pow_left_injective (by omega) this
  -- size bounds
  have hbound : ∀ t : ℕ, t ^ x < 2 * C → t ≤ 2 * k := by
    intro t ht
    by_contra hlt
    have ht1 : 2 * k + 1 ≤ t := by omega
    have ht2 : a + 2 ≤ t ^ 2 := by nlinarith
    have h3 : C ≤ (t ^ 2) ^ v := Nat.pow_le_pow_left ht2 v
    have h4 : t ^ (2 * v + 1) ≤ t ^ x := Nat.pow_le_pow_right (by omega) (by omega)
    have h5 : t ^ (2 * v + 1) = (t ^ 2) ^ v * t := by rw [pow_succ, pow_mul]
    have h6 : (t ^ 2) ^ v * 3 ≤ (t ^ 2) ^ v * t := Nat.mul_le_mul_left _ (by omega)
    omega
  have hU1le : U₁ ≤ d := Nat.le_of_dvd hdpos (Nat.gcd_dvd_right _ _)
  have hU2le : U₂ ≤ 2 * B + d := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have hu' : u ≤ 2 * k := hbound u (by rw [← hu]; omega)
  have hw' : w ≤ 2 * k := hbound w (by rw [← hw]; omega)
  rcases Nat.lt_or_ge u (2 * k) with hlt | hge
  · have : u * w ≤ (2 * k - 1) * (2 * k) := Nat.mul_le_mul (by omega) hw'
    have e : (2 * k - 1) * (2 * k) + 2 * k = 4 * k ^ 2 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [this]; ring
    omega
  · have hu2 : u = 2 * k := by omega
    rw [hu2] at huw
    have : (2 * k * w) % 2 = 0 := by rw [mul_assoc]; exact Nat.mul_mod_right _ _
    omega

/-! ### The difference-of-squares lemma for the case `x < z < y` -/

/-- **Key lemma B.** Let `k` be even and `X ≡ ±1 (mod 2k)`. If
`X² + (4k)^y N = (4k² + 1)^(2v)` with `N ≥ 1`, then `y ≤ 2v`. -/
theorem lu_sq_add_bound {k X v y N : ℕ} (hk : 0 < k) (hk2 : k % 2 = 0)
    (hX : X % (2 * k) = 1 ∨ X % (2 * k) = 2 * k - 1) (hN : 0 < N)
    (h : X ^ 2 + (4 * k) ^ y * N = (4 * k ^ 2 + 1) ^ (2 * v)) : y ≤ 2 * v := by
  have hk2' : 2 ≤ k := by omega
  set C := (4 * k ^ 2 + 1) ^ v with hC
  have hCpos : 0 < C := by positivity
  have hC2 : (4 * k ^ 2 + 1) ^ (2 * v) = C ^ 2 := by rw [hC, ← pow_mul, Nat.mul_comm v 2]
  rw [hC2] at h
  have hCmod : C % (2 * k) = 1 := by
    have h1 : (4 * k ^ 2 + 1) % (2 * k) = 1 := by
      have : 4 * k ^ 2 + 1 = 1 + 2 * k * (2 * k) := by ring
      rw [this, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hC, Nat.pow_mod, h1, one_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have hpos : 0 < (4 * k) ^ y * N := by positivity
  have hXC : X < C := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
  obtain ⟨d, hd⟩ : ∃ d, C = X + d := ⟨C - X, by omega⟩
  have hdpos : 0 < d := by omega
  have hprod : d * (2 * X + d) = (4 * k) ^ y * N := by
    have : (X + d) ^ 2 = X ^ 2 + d * (2 * X + d) := by ring
    rw [hd, this] at h; omega
  -- one of the two factors is `≡ 2 (mod 2k)`
  have key : ∀ σ τ : ℕ, σ % (2 * k) = 2 → 0 < τ → τ < 2 * C → σ * τ = (4 * k) ^ y * N →
      y ≤ 2 * v := by
    intro σ τ hσ hτ hτC hστ
    obtain ⟨j, hj⟩ : ∃ j, σ = 2 * (k * j + 1) := by
      refine ⟨σ / (2 * k), ?_⟩
      have := Nat.div_add_mod σ (2 * k)
      rw [hσ] at this
      linarith
    have hc1 : Nat.Coprime (k * j + 1) k := by
      rw [Nat.coprime_comm, add_comm]
      exact (Nat.coprime_add_mul_left_right k 1 j).2 (Nat.coprime_one_right k)
    have hc2 : Nat.Coprime (k * j + 1) 4 := by
      apply coprime_four_of_not_two_dvd
      intro h2
      obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i := ⟨k / 2, by omega⟩
      have : (2 * i * j + 1) % 2 = 1 := by
        rw [mul_assoc]; omega
      omega
    have hc : Nat.Coprime (k * j + 1) ((4 * k) ^ y) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.mul_right hc2 hc1)
    have hdvd : (4 * k) ^ y ∣ (k * j + 1) * (2 * τ) := by
      refine ⟨N, ?_⟩
      rw [← hστ, hj]; ring
    have hdvd2 : (4 * k) ^ y ∣ 2 * τ := (Nat.Coprime.dvd_mul_left hc.symm).1 hdvd
    have hle : (4 * k) ^ y ≤ 2 * τ := Nat.le_of_dvd (by omega) hdvd2
    by_contra hlt
    have h1 : (4 * k) ^ (2 * v + 1) ≤ (4 * k) ^ y := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (4 * k) ^ (2 * v + 1) = ((4 * k) ^ 2) ^ v * (4 * k) := by rw [pow_succ, pow_mul]
    have h3 : C ≤ ((4 * k) ^ 2) ^ v := Nat.pow_le_pow_left (by nlinarith) v
    have h4 : ((4 * k) ^ 2) ^ v * 4 ≤ ((4 * k) ^ 2) ^ v * (4 * k) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hXlt : X % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  have hdmod : (X + d) % (2 * k) = 1 := by rw [← hd]; exact hCmod
  rcases hX with hX1 | hX1
  · -- `X ≡ 1`: `2X + d ≡ 2`
    refine key (2 * X + d) d ?_ hdpos (by omega) (by rw [mul_comm]; exact hprod)
    have e : (2 * X + d) % (2 * k) = (X % (2 * k) + (X + d) % (2 * k)) % (2 * k) := by
      rw [← Nat.add_mod]; congr 1; ring
    rw [e, hX1, hdmod]
    exact Nat.mod_eq_of_lt (by omega)
  · -- `X ≡ -1`: `d ≡ 2`
    refine key d (2 * X + d) ?_ (by omega) (by omega) hprod
    have e : (X + d) % (2 * k) = (X % (2 * k) + d % (2 * k)) % (2 * k) := Nat.add_mod _ _ _
    rw [e, hX1] at hdmod
    have hdlt : d % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
    have h1 := Nat.div_add_mod (2 * k - 1 + d % (2 * k)) (2 * k)
    rw [hdmod] at h1
    have h2 : (2 * k - 1 + d % (2 * k)) / (2 * k) ≤ 1 := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have h3 : 2 * k * ((2 * k - 1 + d % (2 * k)) / (2 * k)) = 0 ∨
        2 * k * ((2 * k - 1 + d % (2 * k)) / (2 * k)) = 2 * k := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h0 | h0 <;> rw [h0] <;> simp
    omega

/-! ### More helpers -/

/-- From `S + q = (a + 2)^z` with `M ∣ a` and `M ∣ S` we get `q ≡ 2^z (mod M)`. -/
theorem modEq_two_pow_of_eq {M a S q z : ℕ} (hMa : M ∣ a) (hS : M ∣ S)
    (h : S + q = (a + 2) ^ z) : q ≡ 2 ^ z [MOD M] := by
  have h1 : (a + 2) ^ z ≡ 2 ^ z [MOD M] := by
    simpa using ((Nat.modEq_zero_iff_dvd.2 hMa).add_right 2).pow z
  have h3 : S + q ≡ q [MOD M] := by
    simpa using (Nat.modEq_zero_iff_dvd.2 hS).add_right q
  rw [h] at h3
  exact h3.symm.trans h1

/-- If `p^s ≡ 3, 5 (mod 8)` then `p ≡ 3, 5 (mod 8)`. -/
theorem mod_eight_of_pow_mod_eight {p s : ℕ} (h : p ^ s % 8 = 3 ∨ p ^ s % 8 = 5) :
    p % 8 = 3 ∨ p % 8 = 5 := by
  have hodd : p % 2 = 1 := by
    by_contra hp
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp at h
    · have h2 : 2 ∣ p ^ s := (Nat.dvd_of_mod_eq_zero (by omega)).trans (dvd_pow_self p (by omega))
      omega
  have hsq : p ^ 2 % 8 = 1 := by
    have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rw [Nat.pow_mod]
    rcases h8 with h8 | h8 | h8 | h8 <;> rw [h8]
  have := pow_mod_of_sq_mod_eq_one (by norm_num : 1 < 8) hsq s
  rcases Nat.mod_two_eq_zero_or_one s with hs | hs
  · have := this.1 hs; omega
  · have := this.2 hs; omega

/-- `gcd(a, a + 2) = 1` for odd `a`. -/
theorem coprime_add_two_of_odd {a : ℕ} (ha : a % 2 = 1) : Nat.Coprime a (a + 2) := by
  have hcop2 : Nat.Coprime a 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  simpa using hcop2

/-- A perfect square is not an odd power of a prime. -/
theorem sq_ne_prime_pow_odd {p e N : ℕ} (hp : p.Prime) (he : e % 2 = 1) (h : N ^ 2 = p ^ e) :
    False := by
  have h1 := congrArg (fun m => m.factorization p) h
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization_self, mul_one] at h1
  omega

/-! ### The case `x < z < y` -/

/-- Core of the case `x < z < y`: `π` is a prime factor of `n` and of `a = 4k² - 1` with
`π ≡ 3, 5 (mod 8)`, the cofactor is a square `Y²` with `Y ≡ ±1 (mod 2k)`, `k` even. -/
theorem lu_caseB_core {k a n π Y y z j : ℕ} (hk : 0 < k) (hk2 : k % 2 = 0)
    (ha : a + 1 = 4 * k ^ 2) (hπ8 : π % 8 = 3 ∨ π % 8 = 5) (hπn : π ∣ n) (hπa : π ∣ a)
    (hY : Y % (2 * k) = 1 ∨ Y % (2 * k) = 2 * k - 1) (hcop : Nat.Coprime Y π)
    (hj : 0 < j) (hn : 0 < n) (hy : z < y)
    (h : Y ^ 2 + (4 * k) ^ y * n ^ j = (a + 2) ^ z) : False := by
  have hmod : Y ^ 2 ≡ 2 ^ z [MOD π] :=
    modEq_two_pow_of_eq hπa (Dvd.dvd.mul_left (hπn.trans (dvd_pow_self n hj.ne')) _)
      (by rw [add_comm]; exact h)
  have hz := even_of_sq_modEq_two_pow hπ8 hcop hmod
  obtain ⟨v, rfl⟩ : ∃ v, z = 2 * v := ⟨z / 2, by omega⟩
  have hc : a + 2 = 4 * k ^ 2 + 1 := by omega
  rw [hc] at h
  have := lu_sq_add_bound hk hk2 hY (by positivity) h
  omega

/-- The case `x < z < y` when the cofactor is `X₀^x` with `X₀ = 2k ± 1`. -/
theorem lu_caseB_pow {k a n π X₀ x i j : ℕ} (hk : 0 < k) (hk2 : k % 2 = 0)
    (ha : a + 1 = 4 * k ^ 2) (hπ8 : π % 8 = 3 ∨ π % 8 = 5) (hπn : π ∣ n) (hπa : π ∣ a)
    (hsq : X₀ ^ 2 % (4 * k) = 1) (h1 : 1 < X₀) (h4 : X₀ < 4 * k)
    (hX : X₀ % (2 * k) = 1 ∨ X₀ % (2 * k) = 2 * k - 1) (hcop : Nat.Coprime X₀ π)
    (hj : 0 < j) (hn : 0 < n)
    (h : X₀ ^ x + (4 * k) ^ (x + i + j) * n ^ j = (a + 2) ^ (x + i)) : False := by
  have hk2' : 2 ≤ k := by omega
  -- `x` is even
  have hxmod : X₀ ^ x % (4 * k) = 1 := by
    have hc : (a + 2) ^ (x + i) % (4 * k) = 1 := by
      have e : a + 2 = 1 + 4 * k * k := by
        have : 4 * k * k = 4 * k ^ 2 := by ring
        omega
      rw [Nat.pow_mod, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 1 < 4 * k),
        one_pow, Nat.mod_eq_of_lt (by omega : 1 < 4 * k)]
    have hT : (4 * k) ^ (x + i + j) * n ^ j % (4 * k) = 0 :=
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _)
    rw [← h, Nat.add_mod, hT, add_zero, Nat.mod_mod] at hc
    exact hc
  have hpw := pow_mod_of_sq_mod_eq_one (by omega : 1 < 4 * k) hsq x
  have hxe : x % 2 = 0 := by
    by_contra hxo
    have := hpw.2 (by omega)
    rw [hxmod, Nat.mod_eq_of_lt h4] at this
    omega
  obtain ⟨w, rfl⟩ : ∃ w, x = 2 * w := ⟨x / 2, by omega⟩
  have hsq2 : X₀ ^ 2 % (2 * k) = 1 := by
    have := Nat.mod_mod_of_dvd (X₀ ^ 2) (show 2 * k ∣ 4 * k from ⟨2, by ring⟩)
    rw [hsq, Nat.mod_eq_of_lt (by omega : 1 < 2 * k)] at this
    exact this.symm
  have hY : X₀ ^ w % (2 * k) = 1 ∨ X₀ ^ w % (2 * k) = 2 * k - 1 := by
    have := pow_mod_of_sq_mod_eq_one (by omega : 1 < 2 * k) hsq2 w
    rcases Nat.mod_two_eq_zero_or_one w with hw | hw
    · exact Or.inl (this.1 hw)
    · rw [this.2 hw]; exact hX
  refine lu_caseB_core (Y := X₀ ^ w) (y := 2 * w + i + j) (z := 2 * w + i) hk hk2 ha hπ8 hπn hπa hY
    (Nat.Coprime.pow_left _ hcop) hj hn (by omega) ?_
  rw [← pow_mul, mul_comm w 2]
  exact h

/-- **Theorem B (case `x < z < y`).** Let `k ≡ 2 (mod 4)` and suppose `2k - 1` and `2k + 1`
are both prime powers. Then for `n > 1` the equation
`((4k²-1) n)^x + (4k n)^y = ((4k²+1) n)^z` has no solution with `x < z < y`. -/
theorem lu_no_solution_x_lt_z_lt_y {k n x y z : ℕ} (hk4 : k % 4 = 2)
    (hA : IsPrimePow (2 * k - 1)) (hB : IsPrimePow (2 * k + 1)) (hn : 1 < n)
    (hs : IsSolution (4 * k ^ 2 - 1) (4 * k) (4 * k ^ 2 + 1) n x y z)
    (hxz : x < z) (hzy : z < y) : False := by
  have hk : 0 < k := by omega
  have hkk : 0 < k ^ 2 := by positivity
  obtain ⟨hx, hy, hz, heq⟩ := hs
  obtain ⟨A, hAe⟩ : ∃ A, A + 1 = 2 * k := ⟨2 * k - 1, by omega⟩
  rw [show 2 * k - 1 = A by omega] at hA
  rw [show 2 * k + 1 = A + 2 by omega] at hB
  obtain ⟨a, ha⟩ : ∃ a, a + 1 = 4 * k ^ 2 := ⟨4 * k ^ 2 - 1, by omega⟩
  have haA : a = A * (A + 2) := by
    have h1 : (A + 1) ^ 2 = a + 1 := by rw [hAe, ha]; ring
    have h2 : (A + 1) ^ 2 = A * (A + 2) + 1 := by ring
    omega
  rw [show 4 * k ^ 2 - 1 = a by omega, show 4 * k ^ 2 + 1 = a + 2 by omega] at heq
  obtain ⟨i, rfl⟩ : ∃ i, z = x + i := ⟨z - x, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, y = x + i + j := ⟨y - (x + i), by omega⟩
  have hi : 0 < i := by omega
  have hj : 0 < j := by omega
  have hn0 : 0 < n := by omega
  have hc : a ^ x + (4 * k) ^ (x + i + j) * n ^ (i + j) = (a + 2) ^ (x + i) * n ^ i := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ x by positivity)
    calc n ^ x * (a ^ x + (4 * k) ^ (x + i + j) * n ^ (i + j))
        = (a * n) ^ x + (4 * k * n) ^ (x + i + j) := by ring
      _ = ((a + 2) * n) ^ (x + i) := heq
      _ = n ^ x * ((a + 2) ^ (x + i) * n ^ i) := by rw [mul_pow, pow_add n]; ring
  have hnd : n ^ i ∣ a ^ x := by
    have h1 : n ^ i ∣ (4 * k) ^ (x + i + j) * n ^ (i + j) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ i ∣ a ^ x + (4 * k) ^ (x + i + j) * n ^ (i + j) := by
      rw [hc]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_left h1).1 h2
  obtain ⟨q, hq⟩ := hnd
  have h' : q + (4 * k) ^ (x + i + j) * n ^ j = (a + 2) ^ (x + i) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ i by positivity)
    rw [mul_add, ← hq, mul_comm _ ((a + 2) ^ (x + i)), ← hc]; ring
  have hcop_ac : Nat.Coprime a (a + 2) := coprime_add_two_of_odd (by omega)
  have hcn : Nat.Coprime (a + 2) n :=
    Nat.Coprime.coprime_dvd_right ((dvd_pow_self n hi.ne').trans ⟨q, hq⟩)
      (Nat.Coprime.pow_right x hcop_ac.symm)
  have hqn : Nat.Coprime q n := by
    have h1 : Nat.gcd q n ∣ (a + 2) ^ (x + i) := by
      rw [← h']
      exact Dvd.dvd.add (Nat.gcd_dvd_left _ _)
        (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (dvd_pow_self n hj.ne')) _)
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left _ hcn) h1 (Nat.gcd_dvd_right _ _)
  obtain ⟨p, s, hp, hs, hps⟩ := (isPrimePow_nat_iff _).1 hA
  obtain ⟨r, t, hr, ht, hrt⟩ := (isPrimePow_nat_iff _).1 hB
  have hp8 : p % 8 = 3 ∨ p % 8 = 5 := mod_eight_of_pow_mod_eight (by rw [hps]; omega)
  have hr8 : r % 8 = 3 ∨ r % 8 = 5 := mod_eight_of_pow_mod_eight (by rw [hrt]; omega)
  have hpA : p ∣ A := hps ▸ dvd_pow_self p (by omega)
  have hrB : r ∣ A + 2 := hrt ▸ dvd_pow_self r (by omega)
  have hpa : p ∣ a := haA ▸ Dvd.dvd.mul_right hpA _
  have hra : r ∣ a := haA ▸ Dvd.dvd.mul_left hrB _
  have hk2 : k % 2 = 0 := by omega
  have hAmod : A % (2 * k) = 2 * k - 1 := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hBmod : (A + 2) % (2 * k) = 1 := by
    rw [show A + 2 = 2 * k + 1 by omega, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hAsq : A ^ 2 % (4 * k) = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hAm : A = 2 * m + 1 := by omega
    have e : A ^ 2 = 1 + 4 * (m + 1) * m := by rw [hAm]; ring
    rw [e, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hBsq : (A + 2) ^ 2 % (4 * k) = 1 := by
    have e : (A + 2) ^ 2 = 1 + 4 * k * (k + 1) := by
      rw [show A + 2 = 2 * k + 1 by omega]; ring
    rw [e, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hax : a ^ x = A ^ x * (A + 2) ^ x := by rw [haA, mul_pow]
  have dich : ∀ {ℓ e : ℕ}, ℓ.Prime → ℓ ∣ n ∨ Nat.Coprime (ℓ ^ e) n := fun {ℓ e} hℓ =>
    (em (ℓ ∣ n)).imp id (fun h => Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 h))
  rcases dich (e := s) hp with hpn | hAn <;> rcases dich (e := t) hr with hrn | hBn
  · -- both primes divide `n`: the cofactor is `1`
    have h1 : Nat.Coprime q A := by
      rw [← hps]; exact Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right hpn hqn)
    have h2 : Nat.Coprime q (A + 2) := by
      rw [← hrt]; exact Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right hrn hqn)
    have h3 : Nat.Coprime q (a ^ x) := by
      rw [haA]; exact Nat.Coprime.pow_right _ (Nat.Coprime.mul_right h1 h2)
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd h3 ⟨n ^ i, by rw [hq]; ring⟩
    subst hq1
    refine lu_caseB_core (Y := 1) (y := x + i + j) hk hk2 ha hp8 hpn hpa
      (Or.inl (Nat.mod_eq_of_lt (by omega))) (Nat.coprime_one_left _) hj hn0 (by omega) ?_
    rw [one_pow]; exact h'
  · -- `p ∣ n`, `gcd(2k+1, n) = 1`: the cofactor is `(2k+1)^x`
    rw [hrt] at hBn
    have h1 : Nat.Coprime q (A ^ x) := by
      rw [← hps]
      exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right hpn hqn))
    have h2 : q ∣ (A + 2) ^ x :=
      Nat.Coprime.dvd_of_dvd_mul_right h1 ⟨n ^ i, by rw [mul_comm, ← hax, hq]; ring⟩
    have h3 : (A + 2) ^ x ∣ q :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow _ _ hBn)
        ⟨A ^ x, by rw [← hq, hax]; ring⟩
    have hqe : q = (A + 2) ^ x := Nat.dvd_antisymm h2 h3
    rw [hqe] at h'
    exact lu_caseB_pow hk hk2 ha hp8 hpn hpa hBsq (by omega) (by omega) (Or.inl hBmod)
      (Nat.Coprime.coprime_dvd_right hpn hBn) hj hn0 h'
  · -- `r ∣ n`, `gcd(2k-1, n) = 1`: the cofactor is `(2k-1)^x`
    rw [hps] at hAn
    have h1 : Nat.Coprime q ((A + 2) ^ x) := by
      rw [← hrt]
      exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right hrn hqn))
    have h2 : q ∣ A ^ x :=
      Nat.Coprime.dvd_of_dvd_mul_right h1 ⟨n ^ i, by rw [← hax, hq]; ring⟩
    have h3 : A ^ x ∣ q :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow _ _ hAn)
        ⟨(A + 2) ^ x, by rw [← hq, hax]⟩
    have hqe : q = A ^ x := Nat.dvd_antisymm h2 h3
    rw [hqe] at h'
    have hA3 : 3 ≤ A := by omega
    exact lu_caseB_pow hk hk2 ha hr8 hrn hra hAsq (by omega) (by omega) (Or.inr hAmod)
      (Nat.Coprime.coprime_dvd_right hrn hAn) hj hn0 h'
  · -- `gcd(a, n) = 1`: impossible since `n^i ∣ a^x`
    rw [hps] at hAn; rw [hrt] at hBn
    have h1 : Nat.Coprime (n ^ i) (a ^ x) := by
      rw [haA]
      exact Nat.Coprime.pow _ _ (Nat.Coprime.mul_right hAn.symm hBn.symm)
    have h2 : n ^ i = 1 := Nat.Coprime.eq_one_of_dvd h1 ⟨q, hq⟩
    rcases Nat.pow_eq_one.1 h2 with h3 | h3 <;> omega

/-! ### The case `y < z < x` -/

set_option maxHeartbeats 1000000 in
/-- **Theorem A (case `y < z < x`).** Let `k = 2 p^α` with `p` an odd prime, `α` odd,
`p^α ≢ 1 (mod 8)` and `p^α ≠ 3`. Then for `n > 1` the equation
`((4k²-1) n)^x + (4k n)^y = ((4k²+1) n)^z` has no solution with `y < z < x`. -/
theorem lu_no_solution_y_lt_z_lt_x {p α k n x y z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hα : α % 2 = 1) (hk : k = 2 * p ^ α) (hP8 : p ^ α % 8 ≠ 1) (hP3 : p ^ α ≠ 3) (hn : 1 < n)
    (hs : IsSolution (4 * k ^ 2 - 1) (4 * k) (4 * k ^ 2 + 1) n x y z)
    (hyz : y < z) (hzx : z < x) : False := by
  obtain ⟨P, hP⟩ : ∃ P, P = p ^ α := ⟨_, rfl⟩
  rw [← hP] at hk hP8 hP3
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hPodd : P % 2 = 1 := by rw [hP, Nat.pow_mod, hpodd]; simp
  have hP5 : 5 ≤ P := by omega
  have hk0 : 0 < k := by omega
  have hkk : 0 < k ^ 2 := by positivity
  obtain ⟨hx, hy, hz, heq⟩ := hs
  obtain ⟨a, ha⟩ : ∃ a, a + 1 = 4 * k ^ 2 := ⟨4 * k ^ 2 - 1, by omega⟩
  rw [show 4 * k ^ 2 - 1 = a by omega, show 4 * k ^ 2 + 1 = a + 2 by omega] at heq
  obtain ⟨M, hM⟩ : ∃ M, M + 1 = 4 * P := ⟨4 * P - 1, by omega⟩
  have hM8 : M % 8 = 3 := by omega
  have haM : a = M * (M + 2) := by
    have h1 : (M + 1) ^ 2 = a + 1 := by rw [hM, ha, hk]; ring
    have h2 : (M + 1) ^ 2 = M * (M + 2) + 1 := by ring
    omega
  have hMa : M ∣ a := ⟨M + 2, haM⟩
  have hbe : 4 * k = 8 * P := by omega
  have haP : a + 1 = P * (16 * P) := by rw [ha, hk]; ring
  obtain ⟨i, rfl⟩ : ∃ i, z = y + i := ⟨z - y, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, x = y + i + j := ⟨x - (y + i), by omega⟩
  have hi : 0 < i := by omega
  have hj : 0 < j := by omega
  have hn0 : 0 < n := by omega
  have hc : a ^ (y + i + j) * n ^ (i + j) + (4 * k) ^ y = (a + 2) ^ (y + i) * n ^ i := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ y by positivity)
    calc n ^ y * (a ^ (y + i + j) * n ^ (i + j) + (4 * k) ^ y)
        = (a * n) ^ (y + i + j) + (4 * k * n) ^ y := by ring
      _ = ((a + 2) * n) ^ (y + i) := heq
      _ = n ^ y * ((a + 2) ^ (y + i) * n ^ i) := by rw [mul_pow, pow_add n]; ring
  have hnd : n ^ i ∣ (4 * k) ^ y := by
    have h1 : n ^ i ∣ a ^ (y + i + j) * n ^ (i + j) :=
      Dvd.dvd.mul_left (pow_dvd_pow n (by omega)) _
    have h2 : n ^ i ∣ a ^ (y + i + j) * n ^ (i + j) + (4 * k) ^ y := by
      rw [hc]; exact Dvd.intro_left _ rfl
    exact (Nat.dvd_add_right h1).1 h2
  obtain ⟨q, hq⟩ := hnd
  have h' : a ^ (y + i + j) * n ^ j + q = (a + 2) ^ (y + i) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ i by positivity)
    rw [mul_add, ← hq, mul_comm _ ((a + 2) ^ (y + i)), ← hc]; ring
  have hbc : Nat.Coprime (4 * k) (a + 2) := by
    have e : a + 2 = 1 + 4 * k * k := by
      have : 4 * k * k = 4 * k ^ 2 := by ring
      omega
    rw [e]
    exact (Nat.coprime_add_mul_left_right (4 * k) 1 k).2 (Nat.coprime_one_right _)
  have hcn : Nat.Coprime (a + 2) n :=
    Nat.Coprime.coprime_dvd_right ((dvd_pow_self n hi.ne').trans ⟨q, hq⟩)
      (Nat.Coprime.pow_right y hbc.symm)
  have hqn : Nat.Coprime q n := by
    have h1 : Nat.gcd q n ∣ (a + 2) ^ (y + i) := by
      rw [← h']
      exact Dvd.dvd.add
        (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (dvd_pow_self n hj.ne')) _)
        (Nat.gcd_dvd_left _ _)
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left _ hcn) h1 (Nat.gcd_dvd_right _ _)
  have hby : (4 * k) ^ y = 8 ^ y * P ^ y := by rw [hbe, mul_pow]
  have e8 : (8 : ℕ) ^ y = 2 ^ (3 * y) := by rw [pow_mul]; norm_num
  have hqmod : q ≡ 2 ^ (y + i) [MOD M] :=
    modEq_two_pow_of_eq hMa (Dvd.dvd.mul_right (hMa.trans (dvd_pow_self a (by omega))) _) h'
  have hPsq8 : P ^ 2 % 8 = 1 := by
    have h8 : P % 8 = 1 ∨ P % 8 = 3 ∨ P % 8 = 5 ∨ P % 8 = 7 := by omega
    rw [Nat.pow_mod]
    rcases h8 with h8 | h8 | h8 | h8 <;> rw [h8]
  -- the cofactor `q = 1`
  have caseOne : q = 1 → False := by
    intro hq1
    rw [hq1] at hqmod h'
    have hpar := two_pow_parity_of_mod_eight (Or.inl hM8)
      (show 2 ^ 0 ≡ 2 ^ (y + i) [MOD M] by simpa using hqmod)
    obtain ⟨v, hv⟩ : ∃ v, y + i = 2 * v := ⟨(y + i) / 2, by omega⟩
    rw [hv] at h'
    exact lu_no_sq (B := 1) (x := 2 * v + j) (v := v) hk0 ha (by omega) (show 0 < n ^ j by positivity)
      (by rw [one_pow]; exact h')
  -- the cofactor `q = 8^y` (`n` odd)
  have caseEight : q = 8 ^ y → n ^ i = P ^ y → False := by
    intro hq8 hni
    rw [hq8] at hqmod h'
    rw [e8] at hqmod
    have hpar := two_pow_parity_of_mod_eight (Or.inl hM8) hqmod
    rcases Nat.mod_two_eq_zero_or_one y with hye | hyo
    · obtain ⟨u, hu⟩ : ∃ u, y = 2 * u := ⟨y / 2, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, y + i = 2 * v := ⟨(y + i) / 2, by omega⟩
      have e : (8 : ℕ) ^ y = (8 ^ u) ^ 2 := by rw [hu, ← pow_mul, Nat.mul_comm u 2]
      rw [e, hv] at h'
      exact lu_no_sq (x := 2 * v + j) (v := v) hk0 ha (by omega) (show 0 < n ^ j by positivity) h'
    · obtain ⟨i', hi'⟩ : ∃ i', i = 2 * i' := ⟨i / 2, by omega⟩
      have e1 : (n ^ i') ^ 2 = p ^ (α * y) := by
        rw [← pow_mul, Nat.mul_comm i' 2, ← hi', hni, hP, ← pow_mul]
      exact sq_ne_prime_pow_odd hp (by rw [Nat.mul_mod, hα, hyo]) e1
  -- the cofactor `q = P^y` (`n` a power of `2`)
  have caseP : q = P ^ y → n ^ i = 8 ^ y → False := by
    intro hqP hni
    rw [hqP] at hqmod h'
    have h4P : (4 * P) ^ y ≡ 1 [MOD M] := by
      have : 4 * P ≡ 1 [MOD M] := by
        rw [← hM]; simp
      simpa using this.pow y
    have h5 : 2 ^ (2 * y + (y + i)) ≡ 2 ^ 0 [MOD M] := by
      have e : 2 ^ (2 * y + (y + i)) = 4 ^ y * 2 ^ (y + i) := by
        rw [pow_add, pow_mul]; norm_num
      have h6 : 4 ^ y * 2 ^ (y + i) ≡ 4 ^ y * P ^ y [MOD M] := (hqmod.symm).mul_left _
      rw [e, pow_zero]
      exact h6.trans (by rw [← mul_pow]; exact h4P)
    have hpar := two_pow_parity_of_mod_eight (Or.inl hM8) h5
    obtain ⟨v, hv⟩ : ∃ v, y + i = 2 * v := ⟨(y + i) / 2, by omega⟩
    rcases Nat.mod_two_eq_zero_or_one y with hye | hyo
    · obtain ⟨u, hu⟩ : ∃ u, y = 2 * u := ⟨y / 2, by omega⟩
      have e : P ^ y = (P ^ u) ^ 2 := by rw [hu, ← pow_mul, Nat.mul_comm u 2]
      rw [e, hv] at h'
      exact lu_no_sq (x := 2 * v + j) (v := v) hk0 ha (by omega) (show 0 < n ^ j by positivity) h'
    · -- `y` odd: `n = 2^t`
      have hn2 : n ∣ 2 ^ (3 * y) := by
        rw [← e8, ← hni]; exact dvd_pow_self n hi.ne'
      obtain ⟨t, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn2
      have hti : t * i = 3 * y := by
        have : (2 : ℕ) ^ (t * i) = 2 ^ (3 * y) := by rw [pow_mul, hni, e8]
        exact Nat.pow_right_injective (le_refl 2) this
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | h
        · simp at hn
        · exact h
      have hio : i % 2 = 1 := by omega
      have hto : t % 2 = 1 := by
        have : (t * i) % 2 = 1 := by rw [hti]; omega
        rw [Nat.mul_mod, hio] at this
        omega
      have hPy8 : P ^ y % 8 = P % 8 :=
        (pow_mod_of_sq_mod_eq_one (by norm_num) hPsq8 y).2 hyo
      have hc8 : (a + 2) ^ (y + i) % 8 = 1 := by
        have e : a + 2 = 1 + 8 * (2 * P ^ 2) := by
          have : P * (16 * P) = 8 * (2 * P ^ 2) := by ring
          omega
        rw [Nat.pow_mod, e, Nat.add_mul_mod_self_left]; simp
      have hT : t * j ≤ 2 := by
        by_contra hlt
        have h8 : 8 ∣ (2 ^ t) ^ j := by
          rw [← pow_mul]
          exact (show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 (by omega)
        have : (a ^ (y + i + j) * (2 ^ t) ^ j + P ^ y) % 8 = P % 8 := by
          rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left h8 _), zero_add,
            Nat.mod_mod, hPy8]
        rw [h', hc8] at this
        omega
      have ht1 : t = 1 := by
        rcases Nat.lt_or_ge t 2 with h | h
        · omega
        · have h3 : 3 ≤ t := by omega
          have := Nat.mul_le_mul h3 hj
          omega
      subst ht1
      have hj2 : j = 1 ∨ j = 2 := by omega
      have hcP : (a + 2) ^ (y + i) ≡ 1 [MOD P] := by
        have : a + 2 ≡ 1 [MOD P] := by
          have e : a + 2 = 1 + P * (16 * P) := by omega
          rw [e]
          simp
        simpa using this.pow (y + i)
      have hPa1 : P ∣ a + 1 := ⟨16 * P, haP⟩
      have hP3' : ¬ P ∣ 3 := by
        intro h3
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      rcases hj2 with rfl | rfl
      · -- `x = z + 1` is odd
        have hxodd : Odd (y + i + 1) := by rw [Nat.odd_iff]; omega
        have hd : a + 1 ∣ a ^ (y + i + 1) + 1 := by
          simpa using hxodd.nat_add_dvd_pow_add_pow a 1
        have hd' : P ∣ a ^ (y + i + 1) + 1 := hPa1.trans hd
        have h3 : P ∣ (a + 2) ^ (y + i) + 2 := by
          have e : (a + 2) ^ (y + i) + 2 = 2 * (a ^ (y + i + 1) + 1) + P ^ y := by
            rw [← h']; ring
          rw [e]
          exact Dvd.dvd.add (Dvd.dvd.mul_left hd' _) (dvd_pow_self P (by omega))
        have h4 : (a + 2) ^ (y + i) + 2 ≡ 1 + 2 [MOD P] := hcP.add_right 2
        exact hP3' (Nat.modEq_zero_iff_dvd.1 (h4.symm.trans (Nat.modEq_zero_iff_dvd.2 h3)))
      · -- `x = z + 2` is even
        have ha1 : a + 1 ≡ 0 [MOD P] := Nat.modEq_zero_iff_dvd.2 hPa1
        have hasq : a ^ 2 ≡ 1 [MOD P] := by
          have e : a ^ 2 + (a + 1) = (a + 1) * a + 1 := by ring
          have h1 : a ^ 2 + (a + 1) ≡ a ^ 2 [MOD P] := by simpa using ha1.add_left (a ^ 2)
          have h2 : (a + 1) * a + 1 ≡ 1 [MOD P] := by
            simpa using (ha1.mul_right a).add_right 1
          exact h1.symm.trans (e ▸ h2)
        have hax : a ^ (y + i + 2) ≡ 1 [MOD P] := by
          have e : a ^ (y + i + 2) = (a ^ 2) ^ (v + 1) := by
            rw [← pow_mul, hv]; ring_nf
          rw [e]; simpa using hasq.pow (v + 1)
        have hPP : P ^ y ≡ 0 [MOD P] := Nat.modEq_zero_iff_dvd.2 (dvd_pow_self P (by omega))
        have h3 : a ^ (y + i + 2) * (2 ^ 1) ^ 2 + P ^ y ≡ 1 * (2 ^ 1) ^ 2 + 0 [MOD P] :=
          (hax.mul_right _).add hPP
        rw [h'] at h3
        have h4 : 1 ≡ 4 [MOD P] := hcP.symm.trans (by simpa using h3)
        exact hP3' ((Nat.modEq_iff_dvd' (by norm_num)).1 h4)
  -- classification of the cofactor
  have hpP : ∀ m : ℕ, Nat.Coprime m p → Nat.Coprime m (P ^ y) := fun m hm => by
    rw [hP]; exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ hm)
  by_cases h2n : 2 ∣ n
  · have hq2 : Nat.Coprime q 2 := Nat.Coprime.coprime_dvd_right h2n hqn
    have hq8 : Nat.Coprime q (8 ^ y) :=
      show Nat.Coprime q ((2 ^ 3) ^ y) from
        Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ hq2)
    by_cases hpn : p ∣ n
    · have hqP : Nat.Coprime q (P ^ y) := hpP q (Nat.Coprime.coprime_dvd_right hpn hqn)
      have hqb : Nat.Coprime q ((4 * k) ^ y) := by
        rw [hby]; exact Nat.Coprime.mul_right hq8 hqP
      exact caseOne (Nat.Coprime.eq_one_of_dvd hqb ⟨n ^ i, by rw [hq]; ring⟩)
    · have hPn : Nat.Coprime (P ^ y) (n ^ i) := by
        rw [hP]
        exact Nat.Coprime.pow _ _
          (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn))
      have h1 : P ^ y ∣ q :=
        Nat.Coprime.dvd_of_dvd_mul_left hPn ⟨8 ^ y, by rw [← hq, hby]; ring⟩
      have h2 : q ∣ P ^ y :=
        Nat.Coprime.dvd_of_dvd_mul_left hq8 ⟨n ^ i, by rw [mul_comm q, ← hq, hby]⟩
      have hqe : q = P ^ y := Nat.dvd_antisymm h2 h1
      have hni : n ^ i = 8 ^ y := by
        have : n ^ i * P ^ y = 8 ^ y * P ^ y := by rw [← hby, hq, hqe]
        exact Nat.eq_of_mul_eq_mul_right (by positivity) this
      exact caseP hqe hni
  · have h8n : Nat.Coprime (8 ^ y) (n ^ i) :=
      show Nat.Coprime ((2 ^ 3) ^ y) (n ^ i) from
        Nat.Coprime.pow _ _
          (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2n))
    have h1 : 8 ^ y ∣ q :=
      Nat.Coprime.dvd_of_dvd_mul_left h8n ⟨P ^ y, by rw [← hq, hby]⟩
    have hpn : p ∣ n := by
      obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      have hℓb : ℓ ∣ 8 ^ y * P ^ y := by
        rw [← hby]; exact (hℓn.trans (dvd_pow_self n hi.ne')).trans ⟨q, hq⟩
      rcases (Nat.Prime.dvd_mul hℓ).1 hℓb with h | h
      · rw [e8] at h
        have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h)
        subst this; exact absurd hℓn h2n
      · have hℓP := hℓ.dvd_of_dvd_pow h
        rw [hP] at hℓP
        have := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow hℓP)
        subst this; exact hℓn
    have hqP : Nat.Coprime q (P ^ y) := hpP q (Nat.Coprime.coprime_dvd_right hpn hqn)
    have h2 : q ∣ 8 ^ y :=
      Nat.Coprime.dvd_of_dvd_mul_right hqP ⟨n ^ i, by rw [mul_comm q, ← hq, hby]⟩
    have hqe : q = 8 ^ y := Nat.dvd_antisymm h2 h1
    have hni : n ^ i = P ^ y := by
      have : n ^ i * 8 ^ y = P ^ y * 8 ^ y := by rw [mul_comm (P ^ y), ← hby, hq, hqe]
      exact Nat.eq_of_mul_eq_mul_right (by positivity) this
    exact caseEight hqe hni

/-- Theorem B for twin primes `2k - 1`, `2k + 1` with `k ≡ 2 (mod 4)`. -/
theorem lu_no_solution_x_lt_z_lt_y_of_twin_primes {k n x y z : ℕ} (hk4 : k % 4 = 2)
    (hA : (2 * k - 1).Prime) (hB : (2 * k + 1).Prime) (hn : 1 < n)
    (hs : IsSolution (4 * k ^ 2 - 1) (4 * k) (4 * k ^ 2 + 1) n x y z)
    (hxz : x < z) (hzy : z < y) : False :=
  lu_no_solution_x_lt_z_lt_y hk4 hA.isPrimePow hB.isPrimePow hn hs hxz hzy

/-! ### Main theorems -/

/-- **Main theorem.** Let `k = 2 p^α` with `p` an odd prime, `α` odd, `p^α ≢ 1 (mod 8)`,
`p^α ≠ 3`, and suppose that `2k - 1` and `2k + 1` are both prime powers. Then Jeśmanowicz'
conjecture holds for the triple `(4k² - 1, 4k, 4k² + 1)` and every `n ≥ 1`. -/
theorem jesmanowiczFor_lu_of_two_mul_prime_pow {p α k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hα : α % 2 = 1) (hk : k = 2 * p ^ α) (hP8 : p ^ α % 8 ≠ 1) (hP3 : p ^ α ≠ 3)
    (hA : IsPrimePow (2 * k - 1)) (hB : IsPrimePow (2 * k + 1)) (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor (4 * k ^ 2 - 1) (4 * k) (4 * k ^ 2 + 1) n := by
  have hk1 : 1 ≤ k := by
    have : 0 < p ^ α := pow_pos hp.pos _
    omega
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with h1 | h1
  · rw [← h1]; exact jesmanowiczFor_lu k hk1
  intro x y z hs
  rcases hs.strict_cases_of_one_lt (isPrimitivePythagorean_lu k hk1) h1 with h | ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact h
  · exfalso
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    have hPodd : p ^ α % 2 = 1 := by rw [Nat.pow_mod, hpodd]; simp
    exact lu_no_solution_x_lt_z_lt_y (by omega) hA hB h1 hs h2 h3
  · exact (lu_no_solution_y_lt_z_lt_x hp hp2 hα hk hP8 hP3 h1 hs h2 h3).elim

/-- **New instance `k = 14`.** Jeśmanowicz' conjecture holds for `(783, 56, 785)` and every
`n ≥ 1`. -/
theorem jesmanowiczFor_783_56_785 (n : ℕ) (hn : 0 < n) : JesmanowiczFor 783 56 785 n := by
  have h := jesmanowiczFor_lu_of_two_mul_prime_pow (p := 7) (α := 1) (k := 14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ((isPrimePow_nat_iff _).2 ⟨3, 3, by norm_num, by norm_num, by norm_num⟩)
    (Nat.Prime.isPrimePow (by norm_num)) n hn
  norm_num at h
  exact h

/-- **New instance `k = 54`.** Jeśmanowicz' conjecture holds for `(11663, 216, 11665)` and
every `n ≥ 1`. -/
theorem jesmanowiczFor_11663_216_11665 (n : ℕ) (hn : 0 < n) :
    JesmanowiczFor 11663 216 11665 n := by
  have h := jesmanowiczFor_lu_of_two_mul_prime_pow (p := 3) (α := 3) (k := 54)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Nat.Prime.isPrimePow (by norm_num)) (Nat.Prime.isPrimePow (by norm_num)) n hn
  norm_num at h
  exact h

/-! ### Axiom audit -/

#print axioms lu_no_sq
#print axioms lu_sq_add_bound
#print axioms lu_no_solution_x_lt_z_lt_y
#print axioms lu_no_solution_x_lt_z_lt_y_of_twin_primes
#print axioms lu_no_solution_y_lt_z_lt_x
#print axioms jesmanowiczFor_lu_of_two_mul_prime_pow
#print axioms jesmanowiczFor_783_56_785
#print axioms jesmanowiczFor_11663_216_11665

end Jesmanowicz
