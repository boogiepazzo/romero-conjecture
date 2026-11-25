/-
# Jeśmanowicz' conjecture: the family `c = b + 1` (partial) and the strict reduction for `n > 1`

STATUS: IN PROGRESS / NOT YET SOLVED

(The status line refers to Jeśmanowicz' conjecture as a whole, which is OPEN and is NOT
proved here; see `RomeroConjecture/Jesmanowicz.lean` for the statement
`Jesmanowicz.JesmanowiczConjecture`.)

Everything in this file is a RE-FORMALIZATION OF KNOWN RESULTS; nothing here is new
mathematics. In particular Dem'janenko's theorem (the conjecture for all triples with
`c = b + 1`, `n = 1`) is a known theorem of 1965, but this file proves it only PARTIALLY
(see below); the full theorem is stated as `DemjanenkoFamily : Prop` and is NOT proved.

## What IS proved in this file (machine-checked, no `sorry`, no extra axioms)

### Part A. The strict form of the reduction for `n > 1` (complete)

* `IsPrimitivePythagorean.not_pow_succ_dvd` : for a primitive triple and `x ≥ 1`,
  `b^(x+1) ∤ c^x - a^x`.
* `IsSolution.z_ne_x_of_lt`, `IsSolution.z_ne_y_of_lt` : for a primitive triple and every
  `n ≥ 1`, a solution of `(a n)^x + (b n)^y = (c n)^z` with `x < y` has `z ≠ x`
  (resp. with `y < x` has `z ≠ y`).
* `IsSolution.strict_cases_of_one_lt` : for a primitive triple and `n > 1`, every solution
  is `(2, 2, 2)`, or has `x < z < y`, or has `y < z < x`. This is the form stated in the
  literature (attributed to M.-J. Deng, Bull. Aust. Math. Soc. 89 (2014), and
  H. Yang – R.-Q. Fu, J. Number Theory 156 (2015)); it sharpens
  `IsSolution.cases_of_one_lt` of `JesmanowiczFamilies.lean`, which had `≤` on one side.

### Part B. The family `c = b + 1`, i.e. `(a, b, c) = (2k+1, 2k(k+1), 2k(k+1)+1)`, `n = 1`
### (PARTIAL: the case `y = 1` is settled only under a hypothesis on `k`)

* `isPrimitivePythagorean_demjanenko` : these are primitive Pythagorean triples.
* `dem_y_ge_two`, `demjanenko_eq_two_of_two_le_y` : for EVERY `k ≥ 1`, a solution of
  `a^x + b^y = c^z` with `y ≥ 2` is `(2, 2, 2)`.
* `jesmanowiczFor_demjanenko_iff` : for every `k ≥ 1`, `JesmanowiczFor a b c 1` is
  equivalent to the insolubility of `a^x + b = c^z` (the case `y = 1`).
* `dem_y_one` : a solution of `a^x + b = c^z` forces `4 ∣ x`, `z ≡ 1 (mod 4)` and every
  prime factor of `a = 2k + 1` to be `≡ 1 (mod 8)`.
* `jesmanowiczFor_demjanenko_of_prime_factor` : `JesmanowiczFor a b c 1` holds whenever
  `2k + 1` has a prime factor `p ≢ 1 (mod 8)`.
* `jesmanowiczFor_demjanenko_of_not_four_dvd` (and `…_swap_…`) : `JesmanowiczFor a b c 1`
  holds whenever `4 ∤ k`.
  (These two statements are the ones the survey arXiv:1706.05480 attributes to
  V. D. Podyspanin, Izv. Vyssh. Uchebn. Zaved. Mat. 1962; earlier partial results are due to
  Ko Chao.)
* `demjanenkoFamily_iff_residual` : Dem'janenko's full theorem `DemjanenkoFamily` is
  equivalent to the explicit residual statement `DemjanenkoResidual` (no solution of
  `a^x + b = c^z` when `4 ∣ k` and all prime factors of `2k + 1` are `≡ 1 (mod 8)`).
* Examples: `jesmanowiczFor_9_40_41_one`, `jesmanowiczFor_11_60_61_one`,
  `jesmanowiczFor_13_84_85_one`, `jesmanowiczFor_15_112_113_one`.

## What is NOT proved

* Jeśmanowicz' conjecture itself (OPEN).
* Dem'janenko's theorem for the whole family: `DemjanenkoFamily` and `DemjanenkoResidual`
  are only `def … : Prop`. What is missing is exactly the equation `a^x + b = c^z`
  (`y = 1`) when `4 ∣ k` and every prime factor of `2k + 1` is `≡ 1 (mod 8)`; the smallest
  uncovered triple is `(17, 144, 145)` (`k = 8`). Historically this is the hard case
  (Ko 1958–1964, Ko–Sun 1964, Podyspanin 1962 obtained congruence conditions on `k`;
  Dem'janenko 1965 completed it). The formalizer did not find a proof of this case and
  could not access Dem'janenko's paper.
* Any member of the family for `n > 1` other than `(3, 4, 5)` and `(5, 12, 13)` (which are
  in the other files); `(7, 24, 25)` and `(8, 15, 17)` for `n > 1` were not attempted.

## Proof outlines (all elementary)

* `not_pow_succ_dvd`. If `x` is odd, `c^x - a^x ≡ a^(x-1) (c - a) (mod b²)` (because
  `b² = c² - a²` divides `c^(x-1) - a^(x-1)`), so `b² ∣ c - a`, impossible as
  `0 < c - a < b²`. If `x = 2j`, lifting the exponent at a prime `p ∣ b` (mathlib's
  `Nat.multiplicity_pow_sub_pow` for `(c²)^j - (a²)^j` if `b` is odd, and
  `Nat.multiplicity_pow_two_sub_pow` if `b` is even) gives
  `v_p(c^x - a^x) ≤ 2 v_p(b) + v_p(x)`, whereas `v_p(x) < x`.
  Then `z = x < y` gives `a^x + b^y n^(y-x) = c^x`, so `b^(x+1) ∣ c^x - a^x`.
* Family `c = b + 1`; put `q = k + 1`, so `a = 2k + 1 = 2q - 1`, `b = 2kq`, `c = b + 1`,
  `a² = 2b + 1 = 2c - 1`.
  - mod `b` (`dem_x_even`): `c ≡ 1`, `a² ≡ 1`, `a ≢ 1`, so `x = 2X`.
  - mod `c` (`dem_parity`): `a² ≡ -1`, `b ≡ -1`, so `X + y` is odd.
  - mod `b²` (`dem_mod_sq`, binomial congruence): `b^y ≡ (z - 2X) b`; hence `z` is even
    if `y ≥ 2` (`dem_z_even`), and `z ≡ 2X + 1 (mod 4)` if `y = 1`.
  - `y ≥ 2`, `z = 2Z`: `(c^Z - a^X)(c^Z + a^X) = (2kq)^y`. If `X` were even, `c^Z + a^X`
    would be `≡ 2 (mod b)`, forcing it to be `2`. So `X` is odd, `y` is even, and
    (`dem_split`) `{c^Z - a^X, c^Z + a^X} = {2 k^y, 2^(y-1) q^y}` for `k` odd, resp.
    `{2^(y-1) k^y, 2 q^y}` for `k` even. For `y = 2` this gives `X = Z = 1`. For `y ≥ 4`
    and `k` even, `a^X = q^y - 2^(y-2) k^y ≤ 0` once `k ≥ 4` (`k = 2` is `(5, 12, 13)`).
    For `y = 2v ≥ 4` and `k` odd (`dem_absurd`): `a^X = U² - V²` with `U = 2^(v-1) q^v`,
    `V = k^v`, so `U - V = a₁^X`, `U + V = a₂^X`, `a₁ a₂ = a`; from
    `2V = a₂^X - a₁^X ≥ 2 X a₁^(X-1)` one gets `a₁ > X`, hence `a > X²`; but mod `q²` the
    equation gives `q ∣ 2 (X - v)` and `X > v`, hence `2X ≥ q + 4`: contradiction.
  - `y = 1` (`dem_y_one`): `X` is even and `z ≡ 1 (mod 4)`; modulo a prime `p ∣ a`,
    `c ≡ -b`, so `b = c^z` gives `(b^((z-1)/4))^4 = -1` in `ZMod p`, an element of order
    `8`, whence `8 ∣ p - 1`.

## Sources and honesty statement

* All proofs in this file were worked out by the formalizer; none is a transcription of a
  published proof.
* Sources actually consulted in this session:
  - G. Soydan, M. Demirci, I. N. Cangül, A. Togbé, "On the conjecture of Jeśmanowicz",
    arXiv:1706.05480 (survey): only its historical account of the family
    `(2n+1, 2n(n+1), 2n(n+1)+1)` (Ko, Podyspanin, Ko–Sun, Dem'janenko) and bibliography.
  - T. Miyazaki's doctoral thesis (Tokyo Metropolitan University repository,
    `tokyo-metro-u.repo.nii.ac.jp/record/2119`), Chapter 1 (proofs that the conjecture
    holds if `a ≡ ±1 (mod b)` or `c ≡ 1 (mod b)`). That chapter explicitly ASSUMES
    Dem'janenko's theorem (it treats only `c > b + 1`), so it contains no proof of the case
    `c = b + 1`. Its skeleton for `y > 1` (the splitting of `c^Z ± a^X`, then
    `a^X = k² - l²` with `k ± l` coprime `X`-th powers) coincides with the one used here;
    the formalizer had reached that skeleton before reading it, but found the concluding
    contradiction only afterwards. That conclusion (a Bernoulli-type size estimate against
    a congruence mod `q²`) differs in detail from the thesis (2-adic bound on `y` against a
    congruence `X ≡ Z`), but is in the same spirit and should not be regarded as
    independent of it.
  - Web-search result snippets (bibliographic data only).
* NOT consulted (could not be accessed or not attempted): Dem'janenko's 1965 paper (Izv.
  Vysš. Učebn. Zaved. Matematika 1965, no. 5, 52–56; mathnet.ru refused the download),
  Podyspanin (1962), Ko's papers, T. Miyazaki, J. Number Theory 133 (2013) (journal
  version), the survey of Le–Scott–Styer (arXiv:1808.06557), arXiv:2102.10921, Deng (2014),
  Yang–Fu (2015). The attributions of Part A to Deng and Yang–Fu are taken from the header
  of `JesmanowiczFamilies.lean`; the attribution of the `4 ∤ k` / prime-factor criterion to
  Podyspanin is taken from the survey arXiv:1706.05480 (which states it for the family
  without giving the proof).
-/
import RomeroConjecture.Jesmanowicz
import RomeroConjecture.JesmanowiczAllN
import RomeroConjecture.JesmanowiczFamilies

namespace Jesmanowicz

/-! ### Part A. The strict reduction for `n > 1` -/

/-- In a primitive Pythagorean triple a leg is smaller than the hypotenuse. -/
theorem IsPrimitivePythagorean.left_lt_hyp {a b c : ℕ} (h : IsPrimitivePythagorean a b c) :
    a < c := by
  obtain ⟨ha, hb, hc, -, hp⟩ := h
  nlinarith

/-- **Key divisibility lemma.** For a primitive Pythagorean triple and `x ≥ 1`,
`b^(x+1)` does not divide `c^x - a^x`. (For odd `x` this is elementary; for even `x` it is
lifting the exponent at a prime factor of `b`.) -/
theorem IsPrimitivePythagorean.not_pow_succ_dvd {a b c x : ℕ}
    (h : IsPrimitivePythagorean a b c) (hx : 0 < x) : ¬ b ^ (x + 1) ∣ c ^ x - a ^ x := by
  intro hdvd
  have hac := h.left_lt_hyp
  have hb2 := h.two_le_right
  have hpar := h.legs_parity
  have hcodd := h.c_odd
  have hnr := fun p hpp hpc => (isPrimitivePythagorean_swap.1 h).not_dvd_left (p := p) hpp hpc
  obtain ⟨ha, hb, hc, hcop, hp⟩ := h
  have hpowlt : a ^ x < c ^ x := Nat.pow_lt_pow_left hac (by omega)
  have hN : c ^ x - a ^ x ≠ 0 := by omega
  rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
  swap
  · -- `x` odd: `c^x - a^x ≡ a^(x-1) (c - a) (mod b²)`, and `0 < c - a < b²`
    obtain ⟨j, rfl⟩ : ∃ j, x = 2 * j + 1 := ⟨x / 2, by omega⟩
    have h1 : (b : ℤ) ^ 2 ∣ (c : ℤ) ^ (2 * j + 1) - (a : ℤ) ^ (2 * j + 1) := by
      have h0 : b ^ 2 ∣ c ^ (2 * j + 1) - a ^ (2 * j + 1) :=
        (pow_dvd_pow b (by omega)).trans hdvd
      have h0' := Int.natCast_dvd_natCast.2 h0
      rw [Nat.cast_sub hpowlt.le] at h0'
      exact_mod_cast h0'
    have h2 : (b : ℤ) ^ 2 ∣ ((c : ℤ) ^ 2) ^ j - ((a : ℤ) ^ 2) ^ j := by
      have e : (b : ℤ) ^ 2 = (c : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
        have := hp; zify at this; linarith
      rw [e]; exact sub_dvd_pow_sub_pow _ _ j
    have h3 : (b : ℤ) ^ 2 ∣ (a : ℤ) ^ (2 * j) * ((c : ℤ) - a) := by
      have := dvd_sub h1 (Dvd.dvd.mul_left h2 (c : ℤ))
      convert this using 1; ring
    obtain ⟨d, rfl⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
    have h4 : b ^ 2 ∣ a ^ (2 * j) * d := by
      have h5 : (b : ℤ) ^ 2 ∣ ((a ^ (2 * j) * d : ℕ) : ℤ) := by
        push_cast at h3 ⊢
        convert h3 using 2; ring
      exact_mod_cast h5
    have h5 : b ^ 2 ∣ d := (Nat.Coprime.pow 2 (2 * j) hcop.symm).dvd_of_dvd_mul_left h4
    have h6 := Nat.le_of_dvd (by omega) h5
    nlinarith
  · obtain ⟨j, rfl⟩ : ∃ j, x = 2 * j := ⟨x / 2, by omega⟩
    have hj : 0 < j := by omega
    rcases hpar with ⟨ha2, hb1⟩ | ⟨ha1, hb0⟩
    · -- `b` odd: lifting the exponent at an odd prime `p ∣ b`, for `(c²)^j - (a²)^j`
      obtain ⟨p, hpp, hpb⟩ := Nat.exists_prime_and_dvd (show b ≠ 1 by omega)
      have : Fact p.Prime := ⟨hpp⟩
      have hpodd : Odd p := hpp.odd_of_ne_two (by rintro rfl; omega)
      have hpc : ¬ p ∣ c ^ 2 := fun hd => hnr p hpp (hpp.dvd_of_dvd_pow hd) hpb
      have hsq : c ^ 2 - a ^ 2 = b ^ 2 := by omega
      have hlte := Nat.multiplicity_pow_sub_pow hpodd
        (Nat.pow_lt_pow_left hac (by norm_num : 2 ≠ 0))
        (by rw [hsq]; exact Dvd.dvd.pow hpb (by norm_num)) hpc (n := j) (by omega)
      rw [hsq, Nat.multiplicity_pow, ← pow_mul, ← pow_mul] at hlte
      have he : 1 ≤ multiplicity p b :=
        (multiplicity_dvd_iff_le (by omega)).1 (by simpa using hpb)
      have hle : (2 * j + 1) * multiplicity p b ≤ multiplicity p (c ^ (2 * j) - a ^ (2 * j)) := by
        rw [← Nat.multiplicity_pow]
        exact (multiplicity_dvd_iff_le hN).1 ((pow_multiplicity_dvd _ _).trans hdvd)
      have hlt := multiplicity_lt_self (p := p) hj
      obtain ⟨e, he'⟩ : ∃ e, multiplicity p b = e + 1 := ⟨multiplicity p b - 1, by omega⟩
      rw [he'] at hle hlte
      nlinarith [Nat.le_mul_of_pos_left e hj]
    · -- `b` even: lifting the exponent at `2`
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hlte := Nat.multiplicity_pow_two_sub_pow hac (by omega : 2 ∣ c - a)
        (by omega : ¬ 2 ∣ c) (n := 2 * j) (by omega) ⟨j, by ring⟩
      have hmul : multiplicity 2 (c + a) + multiplicity 2 (c - a) = 2 * multiplicity 2 b := by
        rw [← Nat.multiplicity_mul (by omega) (by omega), ← Nat.multiplicity_pow]
        congr 1
        obtain ⟨d, rfl⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
        rw [Nat.add_sub_cancel_left]; nlinarith
      have he : 1 ≤ multiplicity 2 b :=
        (multiplicity_dvd_iff_le (by omega)).1 (by simpa using Nat.dvd_of_mod_eq_zero hb0)
      have hle : (2 * j + 1) * multiplicity 2 b ≤ multiplicity 2 (c ^ (2 * j) - a ^ (2 * j)) := by
        rw [← Nat.multiplicity_pow]
        exact (multiplicity_dvd_iff_le hN).1 ((pow_multiplicity_dvd _ _).trans hdvd)
      have hlt := multiplicity_lt_self (p := 2) (show 0 < 2 * j by omega)
      obtain ⟨e, he'⟩ : ∃ e, multiplicity 2 b = e + 1 := ⟨multiplicity 2 b - 1, by omega⟩
      rw [he'] at hle hmul
      nlinarith [Nat.le_mul_of_pos_left e hj]

/-- For a primitive triple and any `n ≥ 1`, a solution with `x < y` has `z ≠ x`. -/
theorem IsSolution.z_ne_x_of_lt {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 0 < n) (hs : IsSolution a b c n x y z) (hxy : x < y) : z ≠ x := by
  intro hzx
  rw [hzx] at hs
  obtain ⟨hx, hy, -, heq⟩ := hs
  obtain ⟨j, rfl⟩ : ∃ j, y = x + j := ⟨y - x, by omega⟩
  have h1 : a ^ x + b ^ (x + j) * n ^ j = c ^ x := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < n ^ x by positivity)
    calc n ^ x * (a ^ x + b ^ (x + j) * n ^ j) = (a * n) ^ x + (b * n) ^ (x + j) := by ring
      _ = (c * n) ^ x := heq
      _ = n ^ x * c ^ x := by ring
  refine h.not_pow_succ_dvd hx (x := x) ?_
  have h2 : c ^ x - a ^ x = b ^ (x + j) * n ^ j := by omega
  rw [h2]
  exact Dvd.dvd.mul_right (pow_dvd_pow b (by omega)) _

/-- The symmetric statement: a solution with `y < x` has `z ≠ y`. -/
theorem IsSolution.z_ne_y_of_lt {a b c n x y z : ℕ} (h : IsPrimitivePythagorean a b c)
    (hn : 0 < n) (hs : IsSolution a b c n x y z) (hyx : y < x) : z ≠ y :=
  (isSolution_swap.1 hs).z_ne_x_of_lt (isPrimitivePythagorean_swap.1 h) hn hyx

/-- **Strict reduction for `n > 1`** (the form stated in the literature). For a primitive
triple and `n > 1`, every solution of `(a n)^x + (b n)^y = (c n)^z` is `(2, 2, 2)`, or has
`x < z < y`, or has `y < z < x`. -/
theorem IsSolution.strict_cases_of_one_lt {a b c n x y z : ℕ}
    (h : IsPrimitivePythagorean a b c) (hn : 1 < n) (hs : IsSolution a b c n x y z) :
    (x = 2 ∧ y = 2 ∧ z = 2) ∨ (x < z ∧ z < y) ∨ (y < z ∧ z < x) := by
  rcases hs.cases_of_one_lt h hn with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1
  · have := hs.z_ne_x_of_lt h (by omega) (by omega)
    exact Or.inr (Or.inl ⟨by omega, h2⟩)
  · have := hs.z_ne_y_of_lt h (by omega) (by omega)
    exact Or.inr (Or.inr ⟨by omega, h2⟩)

/-! ### Part B. The family `c = b + 1`: `(2k+1, 2k(k+1), 2k(k+1)+1)`, `n = 1` -/

/-- The triples with `c = b + 1` are primitive Pythagorean triples. -/
theorem isPrimitivePythagorean_demjanenko (k : ℕ) (hk : 1 ≤ k) :
    IsPrimitivePythagorean (2 * k + 1) (2 * k * (k + 1)) (2 * k * (k + 1) + 1) := by
  refine ⟨by omega, Nat.mul_pos (by omega) (by omega), by omega, ?_, by ring⟩
  show Nat.gcd (2 * k + 1) (2 * k * (k + 1)) = 1
  have h1 : Nat.gcd (2 * k + 1) (2 * k * (k + 1)) ∣ 2 * (2 * k * (k + 1)) :=
    (Nat.gcd_dvd_right _ _).mul_left 2
  have h2 : Nat.gcd (2 * k + 1) (2 * k * (k + 1)) ∣ 1 + 2 * (2 * k * (k + 1)) := by
    have e : 1 + 2 * (2 * k * (k + 1)) = (2 * k + 1) * (2 * k + 1) := by ring
    rw [e]; exact (Nat.gcd_dvd_left _ _).mul_right _
  exact Nat.dvd_one.1 ((Nat.dvd_add_left h1).1 h2)

theorem int_dvd_one_add_pow_sub_one (u : ℤ) (n : ℕ) : u ∣ (1 + u) ^ n - 1 := by
  have := sub_dvd_pow_sub_pow (1 + u) 1 n
  simpa using this

theorem exists_add_one_pow_eq (m n : ℕ) : ∃ u, (m + 1) ^ n = 1 + m * u := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih
    exact ⟨u * m + u + 1, by rw [pow_succ, hu]; ring⟩

theorem coprime_one_add_mul (m t : ℕ) : Nat.Coprime (1 + m * t) m := by
  have h1 : Nat.gcd (1 + m * t) m ∣ m * t := (Nat.gcd_dvd_right _ _).mul_right t
  exact Nat.dvd_one.1 ((Nat.dvd_add_left h1).1 (Nat.gcd_dvd_left _ _))

theorem coprime_of_add_mul_eq {D q w m : ℕ} (h : D + q * w = 1 + q * m) : Nat.Coprime D q := by
  have h1 : Nat.gcd D q ∣ D + q * w :=
    dvd_add (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).mul_right w)
  rw [h] at h1
  have h2 : Nat.gcd D q ∣ q * m := (Nat.gcd_dvd_right _ _).mul_right m
  exact Nat.dvd_one.1 ((Nat.dvd_add_left h2).1 h1)

theorem coprime_of_eq_two_add_mul {k S m : ℕ} (hk : k % 2 = 1) (h : S = 2 + k * m) :
    Nat.Coprime k S := by
  have h1 : Nat.gcd k S ∣ 2 + k * m := by rw [← h]; exact Nat.gcd_dvd_right _ _
  have h2 : Nat.gcd k S ∣ k * m := (Nat.gcd_dvd_left _ _).mul_right m
  have h3 : Nat.gcd k S ∣ 2 := (Nat.dvd_add_left h2).1 h1
  rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h4 | h4
  · exact h4
  · exfalso
    have h5 : Nat.gcd k S ∣ k := Nat.gcd_dvd_left _ _
    rw [h4] at h5
    omega

/-- Bernoulli-type inequality: `m^(n+1) + 2 (n+1) m^n ≤ (m+2)^(n+1)`. -/
theorem pow_add_le_add_two_pow (m n : ℕ) :
    m ^ (n + 1) + 2 * (n + 1) * m ^ n ≤ (m + 2) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := Nat.mul_le_mul_left (m + 2) ih
    calc m ^ (n + 1 + 1) + 2 * (n + 1 + 1) * m ^ (n + 1)
        ≤ (m + 2) * (m ^ (n + 1) + 2 * (n + 1) * m ^ n) := by
          have e : (m + 2) * (m ^ (n + 1) + 2 * (n + 1) * m ^ n)
              = m ^ (n + 1 + 1) + 2 * (n + 1 + 1) * m ^ (n + 1) + 4 * (n + 1) * m ^ n := by ring
          rw [e]; exact Nat.le_add_right _ _
      _ ≤ (m + 2) * (m + 2) ^ (n + 1) := h1
      _ = (m + 2) ^ (n + 1 + 1) := by ring

/-- Splitting lemma for the factorisation `(c^Z - a^X)(c^Z + a^X) = b^y`. -/
theorem dem_split {P Q D S y : ℕ} (hP : P % 2 = 1) (hD : Nat.Coprime D (2 * Q))
    (hS : Nat.Coprime P S) (h : 2 * D * S = (2 * P * Q) ^ y) :
    D = P ^ y ∧ 2 * S = (2 * Q) ^ y := by
  have e : (2 * P * Q) ^ y = P ^ y * (2 * Q) ^ y := by rw [← mul_pow]; congr 1; ring
  rw [e] at h
  have hP2 : Nat.Coprime P 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  have h1 : P ^ y ∣ D := by
    have h2 : P ^ y ∣ 2 * D * S := Dvd.intro _ h.symm
    have h3 : P ^ y ∣ 2 * D := (Nat.Coprime.pow_left y hS).dvd_of_dvd_mul_right h2
    exact (Nat.Coprime.pow_left y hP2).dvd_of_dvd_mul_left h3
  have h4 : D ∣ P ^ y := by
    have h5 : D ∣ P ^ y * (2 * Q) ^ y := ⟨2 * S, by rw [← h]; ring⟩
    exact (Nat.Coprime.pow_right y hD).dvd_of_dvd_mul_right h5
  have hDe := Nat.dvd_antisymm h4 h1
  refine ⟨hDe, ?_⟩
  have hpos : 0 < P ^ y := by
    have : 0 < P := by omega
    positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h, hDe]; ring

/-- Mod `b`: the exponent `x` is even. -/
theorem dem_x_even {k x y z : ℕ} (hk : 0 < k) (hy : 0 < y)
    (h : (2 * k + 1) ^ x + (2 * k * (k + 1)) ^ y = (2 * k * (k + 1) + 1) ^ z) :
    x % 2 = 0 := by
  by_contra hxo
  obtain ⟨j, rfl⟩ : ∃ j, x = 2 * j + 1 := ⟨x / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = 2 * (k : ℤ) * (k + 1) := ⟨_, rfl⟩
  have hZ : (2 * (k : ℤ) + 1) ^ (2 * j + 1) + b ^ y = (1 + b) ^ z := by
    rw [hb, add_comm 1]; exact_mod_cast h
  have h1 : b ∣ (1 + b) ^ z - 1 := int_dvd_one_add_pow_sub_one b z
  have h2 : b ∣ ((2 * (k : ℤ) + 1) ^ 2) ^ j - 1 := by
    have e : (2 * (k : ℤ) + 1) ^ 2 = 1 + 2 * b := by rw [hb]; ring
    rw [e]; exact (Dvd.intro_left 2 rfl).trans (int_dvd_one_add_pow_sub_one (2 * b) j)
  have h3 : b ∣ b ^ y := dvd_pow_self b (by omega)
  have h4 : b ∣ 2 * (k : ℤ) := by
    have := dvd_sub (dvd_sub h1 h3) (Dvd.dvd.mul_left h2 (2 * (k : ℤ) + 1))
    convert this using 1
    rw [← hZ, pow_succ, pow_mul]; ring
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  have h5 := Int.le_of_dvd (by linarith) h4
  rw [hb] at h5; nlinarith

/-- Mod `c`: writing `x = 2X`, the exponents `X` and `y` have opposite parities. -/
theorem dem_parity {k X y z : ℕ} (hk : 0 < k) (hz : 0 < z)
    (h : (2 * k + 1) ^ (2 * X) + (2 * k * (k + 1)) ^ y = (2 * k * (k + 1) + 1) ^ z) :
    (X + y) % 2 = 1 := by
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = 2 * (k : ℤ) * (k + 1) := ⟨_, rfl⟩
  have hZ : ((2 * (k : ℤ) + 1) ^ 2) ^ X + b ^ y = (b + 1) ^ z := by
    rw [hb, ← pow_mul]; exact_mod_cast h
  have ha2 : (2 * (k : ℤ) + 1) ^ 2 = 2 * b + 1 := by rw [hb]; ring
  rw [ha2] at hZ
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  have hb4 : 4 ≤ b := by rw [hb]; nlinarith
  have hcz : b + 1 ∣ (b + 1) ^ z := dvd_pow_self _ (by omega)
  by_contra hpar
  have hc2 : b + 1 ∣ 2 := by
    rcases Nat.mod_two_eq_zero_or_one X with hX | hX
    · obtain ⟨i, rfl⟩ : ∃ i, X = 2 * i := ⟨X / 2, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, y = 2 * j := ⟨y / 2, by omega⟩
      have h1 : b + 1 ∣ ((2 * b + 1) ^ 2) ^ i - 1 := by
        have := sub_dvd_pow_sub_pow ((2 * b + 1) ^ 2) 1 i
        rw [one_pow] at this
        exact dvd_trans (⟨4 * b, by ring⟩ : b + 1 ∣ (2 * b + 1) ^ 2 - 1) this
      have h2 : b + 1 ∣ (b ^ 2) ^ j - 1 := by
        have := sub_dvd_pow_sub_pow (b ^ 2) 1 j
        rw [one_pow] at this
        exact dvd_trans (⟨b - 1, by ring⟩ : b + 1 ∣ b ^ 2 - 1) this
      have := dvd_sub hcz (dvd_add h1 h2)
      convert this using 1
      rw [← hZ, pow_mul, pow_mul]; ring
    · obtain ⟨j, hj⟩ : ∃ j, y = 2 * j + 1 := ⟨y / 2, by omega⟩
      have h1 : b + 1 ∣ (2 * b + 1) ^ X + 1 := by
        have := Odd.add_dvd_pow_add_pow (2 * b + 1) 1 (Nat.odd_iff.2 hX)
        rw [one_pow] at this
        exact dvd_trans (⟨2, by ring⟩ : b + 1 ∣ 2 * b + 1 + 1) this
      have h2 : b + 1 ∣ b ^ y + 1 := by
        have := Odd.add_dvd_pow_add_pow b 1 (Nat.odd_iff.2 (show y % 2 = 1 by omega))
        rwa [one_pow] at this
      have := dvd_sub (dvd_add h1 h2) hcz
      convert this using 1
      rw [← hZ]; ring
  have := Int.le_of_dvd (by norm_num) hc2
  omega

/-- Mod `b²` (binomial congruence): `b² ∣ b^y - (z - 2X) b`. -/
theorem dem_mod_sq {k X y z : ℕ}
    (h : (2 * k + 1) ^ (2 * X) + (2 * k * (k + 1)) ^ y = (2 * k * (k + 1) + 1) ^ z) :
    (2 * (k : ℤ) * (k + 1)) ^ 2 ∣
      (2 * (k : ℤ) * (k + 1)) ^ y - ((z : ℤ) - 2 * X) * (2 * (k : ℤ) * (k + 1)) := by
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = 2 * (k : ℤ) * (k + 1) := ⟨_, rfl⟩
  have hZ : ((2 * (k : ℤ) + 1) ^ 2) ^ X + b ^ y = (1 + b) ^ z := by
    rw [hb, ← pow_mul, add_comm 1]; exact_mod_cast h
  have ha2 : (2 * (k : ℤ) + 1) ^ 2 = 1 + 2 * b := by rw [hb]; ring
  rw [ha2] at hZ
  rw [← hb]
  have h1 := int_sq_dvd_one_add_pow_sub b z
  have h2 := int_sq_dvd_one_add_pow_sub (2 * b) X
  have h2' : b ^ 2 ∣ (1 + 2 * b) ^ X - 1 - X * (2 * b) :=
    dvd_trans (⟨4, by ring⟩ : b ^ 2 ∣ (2 * b) ^ 2) h2
  have := dvd_sub h1 h2'
  convert this using 1
  linear_combination hZ

/-- If `y ≥ 2` then `z` is even. -/
theorem dem_z_even {k X y z : ℕ} (hk : 0 < k) (hy : 2 ≤ y)
    (h : (2 * k + 1) ^ (2 * X) + (2 * k * (k + 1)) ^ y = (2 * k * (k + 1) + 1) ^ z) :
    z % 2 = 0 := by
  have hmod := dem_mod_sq h
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = 2 * (k : ℤ) * (k + 1) := ⟨_, rfl⟩
  rw [← hb] at hmod
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  have hbpos : 0 < b := by rw [hb]; nlinarith
  have h1 : b ^ 2 ∣ b ^ y := pow_dvd_pow b hy
  have h2 : b ^ 2 ∣ ((z : ℤ) - 2 * X) * b := by
    have := dvd_sub h1 hmod
    simpa using this
  obtain ⟨q, hq⟩ := h2
  have h3 : (z : ℤ) - 2 * X = b * q :=
    mul_right_cancel₀ hbpos.ne' (by linear_combination hq)
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = (k : ℤ) * (k + 1) * q := ⟨_, rfl⟩
  have h4 : (z : ℤ) - 2 * X = 2 * w := by rw [h3, hb, hw]; ring
  omega

/-- The "large `y`" case for odd `k` is contradictory (it does not use the parity of `k`):
with `q = k + 1`, there is no relation `(2k+1)^X + (k^v)² = (q (2q)^(v-1))²` with `X` odd
and `v = w + 2 ≥ 2`. -/
theorem dem_absurd {k X w : ℕ} (hk : 0 < k) (hX : X % 2 = 1)
    (h : (2 * k + 1) ^ X + (k ^ (w + 2)) ^ 2 = ((k + 1) * (2 * (k + 1)) ^ (w + 1)) ^ 2) :
    False := by
  obtain ⟨q, hq⟩ : ∃ q, q = k + 1 := ⟨_, rfl⟩
  rw [← hq] at h
  have hq2 : 2 ≤ q := by omega
  obtain ⟨T, hT⟩ : ∃ T, T = q ^ (w + 2) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = k ^ (w + 2) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = q * (2 * q) ^ (w + 1) := ⟨_, rfl⟩
  -- (ii) the congruence `q ∣ 2 (X - v)` (mod `q²`)
  have hcong : (q : ℤ) ∣ 2 * ((X : ℤ) - (w + 2 : ℕ)) := by
    have hZ : (2 * (k : ℤ) + 1) ^ X + ((k : ℤ) ^ (w + 2)) ^ 2
        = ((q : ℤ) * (2 * q) ^ (w + 1)) ^ 2 := by exact_mod_cast h
    have hkq : (k : ℤ) = q - 1 := by rw [hq]; push_cast; ring
    have e1 : (2 * (k : ℤ) + 1) ^ X = -((1 + -(2 * (q : ℤ))) ^ X) := by
      rw [← Odd.neg_pow (Nat.odd_iff.2 hX), hkq]; congr 1; ring
    have e2 : ((k : ℤ) ^ (w + 2)) ^ 2 = (1 + -(q : ℤ)) ^ (2 * (w + 2)) := by
      have e3 : (k : ℤ) ^ 2 = (1 + -(q : ℤ)) ^ 2 := by rw [hkq]; ring
      rw [pow_mul, ← e3]; ring
    have h1 := int_sq_dvd_one_add_pow_sub (-(2 * (q : ℤ))) X
    have h1' : (q : ℤ) ^ 2 ∣ (1 + -(2 * (q : ℤ))) ^ X - 1 - X * -(2 * (q : ℤ)) :=
      dvd_trans (⟨4, by ring⟩ : (q : ℤ) ^ 2 ∣ (-(2 * (q : ℤ))) ^ 2) h1
    have h2 := int_sq_dvd_one_add_pow_sub (-(q : ℤ)) (2 * (w + 2))
    rw [neg_sq] at h2
    have h3 : (q : ℤ) ^ 2 ∣ ((q : ℤ) * (2 * q) ^ (w + 1)) ^ 2 :=
      ⟨((2 * (q : ℤ)) ^ (w + 1)) ^ 2, by ring⟩
    have h4 : (q : ℤ) ^ 2 ∣ (q : ℤ) * (2 * ((X : ℤ) - (w + 2 : ℕ))) := by
      have := dvd_add (dvd_sub h3 h2) h1'
      convert this using 1
      rw [← hZ, e1, e2]; push_cast; ring
    obtain ⟨r, hr⟩ := h4
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact ⟨r, mul_left_cancel₀ hq0 (by linear_combination hr)⟩
  rw [← hV, ← hU] at h
  have hVpos : 0 < V := by rw [hV]; positivity
  have hVT : V < T := by rw [hV, hT]; exact Nat.pow_lt_pow_left (by omega) (by omega)
  have hTU : 2 * T ≤ U := by
    have e : U = 2 ^ (w + 1) * T := by rw [hU, hT, mul_pow]; ring
    have h2 : 2 ^ 1 ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [e]; exact Nat.mul_le_mul_right T (by simpa using h2)
  have h2U : 2 * U = (2 * q) ^ (w + 2) := by rw [hU]; ring
  -- (i) `X > v`
  have hXv : w + 2 < X := by
    by_contra hle
    have h1 : (2 * k + 1) ^ X ≤ (2 * k + 1) ^ (w + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (2 * k + 1) ^ (w + 2) ≤ (2 * q) ^ (w + 2) := Nat.pow_le_pow_left (by omega) _
    have h3 : (2 * q) ^ (w + 2) ≤ T * T := by
      rw [mul_pow, hT]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq2 _)
    have h4 : (2 * T) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hTU 2
    have h5 : V ^ 2 < T ^ 2 := Nat.pow_lt_pow_left hVT (by norm_num)
    have h6 := Nat.zero_le (T ^ 2)
    linarith
  -- (iii) factorisation `(U - V)(U + V) = a^X` into coprime `X`-th powers
  obtain ⟨E, hE⟩ : ∃ E, U = V + E := ⟨U - V, by omega⟩
  have hEpos : 0 < E := by omega
  have hfac : E * (2 * V + E) = (2 * k + 1) ^ X := by rw [hE] at h; linarith
  have hcopE : Nat.Coprime E (2 * V + E) := by
    apply Nat.coprime_of_dvd
    intro p hpp hpE hpS
    have hpa : p ∣ 2 * k + 1 :=
      hpp.dvd_of_dvd_pow (hfac ▸ Dvd.dvd.mul_right hpE _)
    have hp2U : p ∣ (2 * q) ^ (w + 2) := by
      rw [← h2U, hE]
      have e : 2 * (V + E) = (2 * V + E) + E := by ring
      rw [e]; exact dvd_add hpS hpE
    have hp2q : p ∣ 2 * q := hpp.dvd_of_dvd_pow hp2U
    have h1 : p ∣ 1 := by
      have e : 2 * q = (2 * k + 1) + 1 := by omega
      rw [e] at hp2q
      exact (Nat.dvd_add_right hpa).1 hp2q
    exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨a1, ha1⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 hcopE) hfac
  obtain ⟨a2, ha2⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 hcopE.symm)
    (by rw [mul_comm]; exact hfac)
  have hX0 : X ≠ 0 := by omega
  have hprod : a1 * a2 = 2 * k + 1 := by
    have h1 : (a1 * a2) ^ X = (2 * k + 1) ^ X := by rw [mul_pow, ← ha1, ← ha2, hfac]
    exact Nat.pow_left_injective hX0 h1
  have hlt12 : a1 < a2 := by
    have h1 : a1 ^ X < a2 ^ X := by rw [← ha1, ← ha2]; omega
    exact lt_of_pow_lt_pow_left₀ X (Nat.zero_le _) h1
  have ha2ge : a1 + 2 ≤ a2 := by
    by_contra hlt
    obtain rfl : a2 = a1 + 1 := by omega
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self a1
    omega
  -- (iv) sizes
  obtain ⟨X', rfl⟩ : ∃ X', X = X' + 1 := ⟨X - 1, by omega⟩
  have hB := pow_add_le_add_two_pow a1 X'
  have hB2 : (a1 + 2) ^ (X' + 1) ≤ a2 ^ (X' + 1) := Nat.pow_le_pow_left ha2ge _
  have hV1 : (X' + 1) * a1 ^ X' ≤ V := by linarith [hB, hB2, ha1, ha2]
  have hV2 : (X' + 1) * E ≤ a1 * V := by
    have e : (X' + 1) * E = a1 * ((X' + 1) * a1 ^ X') := by rw [ha1]; ring
    rw [e]; exact Nat.mul_le_mul_left a1 hV1
  have ha1X : X' + 1 < a1 := by
    by_contra hle
    have h1 : a1 * V ≤ (X' + 1) * V := Nat.mul_le_mul_right V (by omega)
    have h2 : (X' + 1) * (2 * V + 2) ≤ (X' + 1) * U := Nat.mul_le_mul_left _ (by omega)
    rw [hE] at h2
    linarith
  have hXq : q + 2 * (w + 2) ≤ 2 * (X' + 1) := by
    have hpos : (0 : ℤ) < 2 * (((X' + 1 : ℕ) : ℤ) - (w + 2 : ℕ)) := by
      have h1 : ((w + 2 : ℕ) : ℤ) < ((X' + 1 : ℕ) : ℤ) := by exact_mod_cast hXv
      linarith
    have h2 := Int.le_of_dvd hpos hcong
    push_cast at h2; omega
  have hprod2 : (X' + 2) * (X' + 4) ≤ a1 * a2 := Nat.mul_le_mul (by omega) (by omega)
  rw [hprod] at hprod2
  have h7 := Nat.mul_le_mul (show q + 6 ≤ 2 * X' + 4 by omega) (show q + 10 ≤ 2 * X' + 8 by omega)
  have h8 := Nat.zero_le (q ^ 2)
  linarith

/-- **The family `c = b + 1`, case `y ≥ 2`.** For `k ≥ 1`, every solution of
`(2k+1)^x + (2k(k+1))^y = (2k(k+1)+1)^z` with `y ≥ 2` is `(2, 2, 2)`. -/
theorem dem_y_ge_two {k x y z : ℕ} (hk : 0 < k) (hx : 0 < x) (hy : 2 ≤ y) (hz : 0 < z)
    (h : (2 * k + 1) ^ x + (2 * k * (k + 1)) ^ y = (2 * k * (k + 1) + 1) ^ z) :
    x = 2 ∧ y = 2 ∧ z = 2 := by
  rcases eq_or_ne k 2 with rfl | hk2
  · exact jesmanowicz_5_12_13 hx (by omega) hz (by norm_num at h; exact h)
  have hxe := dem_x_even hk (by omega) h
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  have hpar := dem_parity hk hz h
  have hze := dem_z_even hk hy h
  obtain ⟨Z, rfl⟩ : ∃ Z, z = 2 * Z := ⟨z / 2, by omega⟩
  have hXpos : 0 < X := by omega
  have hZpos : 0 < Z := by omega
  obtain ⟨q, hq⟩ : ∃ q, q = k + 1 := ⟨_, rfl⟩
  rw [← hq] at h
  have hq2 : 2 ≤ q := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = (2 * k + 1) ^ X := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = (2 * k * q + 1) ^ Z := ⟨_, rfl⟩
  have hAC : A ^ 2 + (2 * k * q) ^ y = C ^ 2 := by
    rw [hA, hC, ← pow_mul', ← pow_mul']; exact h
  obtain ⟨r, hr⟩ : ∃ r, k * q = 2 * r := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self k
    exact ⟨r, by rw [hq, hr]; ring⟩
  obtain ⟨u, hu⟩ := exists_add_one_pow_eq (2 * k * q) Z
  rw [← hC] at hu
  have hbpos : 0 < (2 * k * q) ^ y := by
    have : 0 < q := by omega
    positivity
  have hApos : 0 < A := by rw [hA]; positivity
  have hAltC : A < C := by
    by_contra hle
    have : C ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hbase : 5 ≤ 2 * k * q + 1 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) hq2
    omega
  have hCgt : 5 ≤ C := by
    rw [hC]; exact hbase.trans (Nat.le_self_pow (by omega) _)
  -- `X` is odd
  have hXodd : X % 2 = 1 := by
    by_contra hXe
    obtain ⟨i, rfl⟩ : ∃ i, X = 2 * i := ⟨X / 2, by omega⟩
    obtain ⟨v, hv⟩ := exists_add_one_pow_eq (4 * k * q) i
    have hAv : A = 1 + 4 * k * q * v := by
      rw [hA, pow_mul, ← hv]; congr 1; rw [hq]; ring
    obtain ⟨D, hD⟩ : ∃ D, C = A + D := ⟨C - A, by omega⟩
    have hfac : D * (2 * A + D) = (2 * k * q) ^ y := by rw [hD] at hAC; linarith
    have hS : 2 * A + D = 2 * (1 + (k * q) * (2 * v + u)) := by
      have e : 2 * A + D = A + C := by omega
      rw [e, hAv, hu]; ring
    have hdvd : 1 + (k * q) * (2 * v + u) ∣ (2 * (k * q)) ^ y := by
      have h1 : 2 * A + D ∣ (2 * k * q) ^ y := Dvd.intro_left _ hfac
      rw [hS, mul_assoc 2 k q] at h1
      exact (Dvd.intro_left 2 rfl).trans h1
    have hcop : Nat.Coprime (1 + (k * q) * (2 * v + u)) (2 * (k * q)) := by
      apply Nat.Coprime.mul_right
      · rw [hr, mul_assoc]
        exact coprime_one_add_mul 2 _
      · exact coprime_one_add_mul _ _
    have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right y hcop) hdvd
    have h0 : (k * q) * (2 * v + u) = 0 := by omega
    have hkq0 : k * q ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hu0 : u = 0 := by
      rcases Nat.mul_eq_zero.1 h0 with h' | h'
      · exact absurd h' hkq0
      · omega
    rw [hu0] at hu
    omega
  have hyeven : y % 2 = 0 := by omega
  obtain ⟨v', rfl⟩ : ∃ v', y = 2 * (v' + 1) := ⟨y / 2 - 1, by omega⟩
  obtain ⟨vA, hvA⟩ := exists_add_one_pow_eq (2 * k) X
  rw [← hA] at hvA
  obtain ⟨w, hw⟩ : ∃ w, A + 1 = 2 * q * w := by
    have h1 := Odd.nat_add_dvd_pow_add_pow (2 * k + 1) 1 (Nat.odd_iff.2 hXodd)
    rw [one_pow, ← hA] at h1
    obtain ⟨w, hw⟩ := h1
    exact ⟨w, by rw [hw, hq]; ring⟩
  obtain ⟨D, hD⟩ : ∃ D, C = A + D := ⟨C - A, by omega⟩
  have hfac : D * (2 * A + D) = (2 * k * q) ^ (2 * (v' + 1)) := by
    rw [hD] at hAC; linarith
  have hu' : C = 1 + 2 * (k * q * u) := by rw [hu]; ring
  have hvA' : A = 1 + 2 * (k * vA) := by rw [hvA]; ring
  obtain ⟨D0, hD0⟩ : ∃ D0, D = 2 * D0 := ⟨D / 2, by omega⟩
  have hrel : D0 + q * w = 1 + q * (k * u) := by linarith [hu, hw, hD, hD0]
  have hSrel : 2 * A + D = 2 + k * (2 * vA + 2 * q * u) := by linarith [hu, hvA, hD]
  -- conclusion once `A` and `C` are identified
  have hfin : A = 2 * k + 1 → C = 2 * k * q + 1 → X = 1 ∧ Z = 1 := by
    intro hA1 hC1
    have hX1 : X = 1 := Nat.pow_right_injective (show 2 ≤ 2 * k + 1 by omega)
      (by show (2 * k + 1) ^ X = (2 * k + 1) ^ 1; rw [pow_one, ← hA]; exact hA1)
    have hZ1 : Z = 1 := Nat.pow_right_injective (show 2 ≤ 2 * k * q + 1 by omega)
      (by show (2 * k * q + 1) ^ Z = (2 * k * q + 1) ^ 1; rw [pow_one, ← hC]; exact hC1)
    exact ⟨hX1, hZ1⟩
  rcases Nat.mod_two_eq_zero_or_one k with hke | hko
  · -- `k` even, `q` odd: `C + A = 2 q^y`, `C - A = 2^(y-1) k^y`
    have hqodd : q % 2 = 1 := by omega
    have hS' : A + D0 = 1 + k * (vA + q * u) := by linarith [hSrel, hD0]
    have hfac' : 2 * (A + D0) * D = (2 * q * k) ^ (2 * (v' + 1)) := by
      have e : 2 * q * k = 2 * k * q := by ring
      rw [e, ← hfac, hD0]; ring
    have hDcop : Nat.Coprime (A + D0) (2 * k) := by
      rw [hS']
      apply Nat.Coprime.mul_right
      · obtain ⟨k1, hk1⟩ : ∃ k1, k = 2 * k1 := ⟨k / 2, by omega⟩
        have e : 1 + k * (vA + q * u) = 1 + 2 * (k1 * (vA + q * u)) := by
          rw [hk1]; ring
        rw [e]; exact coprime_one_add_mul 2 _
      · exact coprime_one_add_mul _ _
    have hScop : Nat.Coprime q D := by
      rw [hD0]
      apply Nat.Coprime.mul_right
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
      · exact (coprime_of_add_mul_eq hrel).symm
    obtain ⟨h1, h2⟩ := dem_split hqodd hDcop hScop hfac'
    rcases Nat.eq_zero_or_pos v' with rfl | hv'
    · norm_num at h1 h2
      subst hq
      have hA1 : A = 2 * k + 1 := by linarith
      have hC1 : C = 2 * k * (k + 1) + 1 := by linarith
      obtain ⟨hX1, hZ1⟩ := hfin hA1 hC1
      exact ⟨by omega, by norm_num, by omega⟩
    · exfalso
      have hk4 : 4 ≤ k := by omega
      have e1 : 2 * q ^ 2 ≤ (2 * k) ^ 2 := by
        have h5 := Nat.mul_le_mul_right k hk4
        rw [hq]; linarith
      have e2 : (2 * q ^ 2) ^ (v' + 1) ≤ ((2 * k) ^ 2) ^ (v' + 1) := Nat.pow_le_pow_left e1 _
      have e3 : 2 ^ 2 ≤ 2 ^ (v' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e4 : 4 * q ^ (2 * (v' + 1)) ≤ (2 * k) ^ (2 * (v' + 1)) := by
        calc 4 * q ^ (2 * (v' + 1)) ≤ 2 ^ (v' + 1) * q ^ (2 * (v' + 1)) :=
              Nat.mul_le_mul_right _ (by simpa using e3)
          _ = (2 * q ^ 2) ^ (v' + 1) := by rw [mul_pow, ← pow_mul]
          _ ≤ ((2 * k) ^ 2) ^ (v' + 1) := e2
          _ = (2 * k) ^ (2 * (v' + 1)) := by rw [← pow_mul]
      linarith
  · -- `k` odd, `q` even: `C - A = 2 k^y`, `C + A = 2^(y-1) q^y`
    have hD0odd : D0 % 2 = 1 := by
      obtain ⟨q1, hq1⟩ : ∃ q1, q = 2 * q1 := ⟨q / 2, by omega⟩
      have hC4 : C = 1 + 4 * (r * u) := by
        rw [hu, show 2 * k * q * u = 2 * (k * q) * u by ring, hr]; ring
      have hA4 : A + 1 = 4 * (q1 * w) := by rw [hw, hq1]; ring
      omega
    have hD0cop : Nat.Coprime D0 (2 * q) := by
      apply Nat.Coprime.mul_right
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
      · exact coprime_of_add_mul_eq hrel
    have hkS : Nat.Coprime k (2 * A + D) := coprime_of_eq_two_add_mul hko hSrel
    have hfac' : 2 * D0 * (2 * A + D) = (2 * k * q) ^ (2 * (v' + 1)) := by
      rw [← hfac, hD0]
    obtain ⟨h1, h2⟩ := dem_split hko hD0cop hkS hfac'
    rcases Nat.eq_zero_or_pos v' with rfl | hv'
    · norm_num at h1 h2
      subst hq
      have hA1 : A = 2 * k + 1 := by linarith
      have hC1 : C = 2 * k * (k + 1) + 1 := by linarith
      obtain ⟨hX1, hZ1⟩ := hfin hA1 hC1
      exact ⟨by omega, by norm_num, by omega⟩
    · exfalso
      obtain ⟨w', rfl⟩ : ∃ w', v' = w' + 1 := ⟨v' - 1, by omega⟩
      refine dem_absurd (k := k) (X := X) (w := w') hk hXodd ?_
      rw [← hq, ← hA]
      have e5 : (2 * q) ^ (2 * (w' + 1 + 1)) = 4 * (q * (2 * q) ^ (w' + 1)) ^ 2 := by ring
      have e6 : k ^ (2 * (w' + 1 + 1)) = (k ^ (w' + 2)) ^ 2 := by ring
      rw [e5] at h2
      rw [e6] at h1
      linarith

/-- **The family `c = b + 1`, case `y = 1`: necessary conditions.** If
`(2k+1)^x + 2k(k+1) = (2k(k+1)+1)^z` with `k, x, z ≥ 1`, then `4 ∣ x`, `z ≡ 1 (mod 4)` and
every prime factor of `2k + 1` is `≡ 1 (mod 8)`. -/
theorem dem_y_one {k x z : ℕ} (hk : 0 < k) (hx : 0 < x) (hz : 0 < z)
    (h : (2 * k + 1) ^ x + 2 * k * (k + 1) = (2 * k * (k + 1) + 1) ^ z) :
    x % 4 = 0 ∧ z % 4 = 1 ∧ ∀ p : ℕ, p.Prime → p ∣ 2 * k + 1 → p % 8 = 1 := by
  have h' : (2 * k + 1) ^ x + (2 * k * (k + 1)) ^ 1 = (2 * k * (k + 1) + 1) ^ z := by
    rw [pow_one]; exact h
  have hxe := dem_x_even hk (by norm_num) h'
  obtain ⟨X, rfl⟩ : ∃ X, x = 2 * X := ⟨x / 2, by omega⟩
  have hpar := dem_parity hk hz h'
  have hmod := dem_mod_sq h'
  have hz4 : z % 4 = 1 := by
    obtain ⟨b, hb⟩ : ∃ b : ℤ, b = 2 * (k : ℤ) * (k + 1) := ⟨_, rfl⟩
    rw [← hb, pow_one] at hmod
    have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
    have hbpos : 0 < b := by rw [hb]; nlinarith
    obtain ⟨q, hq⟩ := hmod
    have h3 : 1 - ((z : ℤ) - 2 * X) = b * q :=
      mul_right_cancel₀ hbpos.ne' (by linear_combination hq)
    obtain ⟨r, hr⟩ := Int.even_mul_succ_self (k : ℤ)
    obtain ⟨w, hw⟩ : ∃ w : ℤ, w = r * q := ⟨_, rfl⟩
    have h4 : 1 - ((z : ℤ) - 2 * X) = 4 * w := by
      rw [h3, hb, hw, mul_assoc 2, hr]; ring
    omega
  refine ⟨by omega, hz4, ?_⟩
  intro p hpp hpa
  obtain ⟨m, rfl⟩ : ∃ m, z = 4 * m + 1 := ⟨z / 4, by omega⟩
  have := Fact.mk hpp
  have hcast : ((2 * k + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpa
  have hE : (((2 * k + 1) ^ (2 * X) + 2 * k * (k + 1) : ℕ) : ZMod p)
      = ((2 * k * (k + 1) + 1) ^ (4 * m + 1) : ℕ) := by rw [h]
  push_cast at hE hcast
  obtain ⟨B, hB⟩ : ∃ B : ZMod p, B = 2 * (k : ZMod p) * (k + 1) := ⟨_, rfl⟩
  rw [← hB] at hE
  have h2B : 2 * B + 1 = 0 := by
    have e : 2 * B + 1 = (2 * (k : ZMod p) + 1) ^ 2 := by rw [hB]; ring
    rw [e, hcast]; ring
  have hB1 : B + 1 = -B := by linear_combination h2B
  rw [hcast, zero_pow (by omega), zero_add, hB1] at hE
  have hBne : B ≠ 0 := by
    intro h0
    rw [h0] at h2B
    simp at h2B
  have h4 : (B ^ m) ^ 4 = -1 := by
    have h5 : B * ((B ^ m) ^ 4 + 1) = 0 := by
      have e : (-B) ^ (4 * m + 1) = -(B * (B ^ m) ^ 4) := by
        rw [Odd.neg_pow ⟨2 * m, by ring⟩]; ring
      rw [e] at hE; linear_combination hE
    rcases mul_eq_zero.1 h5 with h0 | h0
    · exact absurd h0 hBne
    · linear_combination h0
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨r, hr⟩ := hpa
    omega
  have hne : (-1 : ZMod p) ≠ 1 := by
    have : Fact (2 < p) := ⟨lt_of_le_of_ne hpp.two_le (Ne.symm hp2)⟩
    exact ZMod.neg_one_ne_one
  have hord : orderOf (B ^ m) = 2 ^ (2 + 1) :=
    orderOf_eq_prime_pow (by norm_num; rw [h4]; exact hne)
      (by
        have e : (B ^ m) ^ 2 ^ (2 + 1) = ((B ^ m) ^ 4) ^ 2 := by ring
        rw [e, h4]; ring)
  have hdvd : orderOf (B ^ m) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one (pow_ne_zero m hBne)
  rw [hord] at hdvd
  obtain ⟨r, hr⟩ := hdvd
  have := hpp.two_le
  omega

/-- If every prime factor of `n` is `≡ 1 (mod 8)` then `n ≡ 1 (mod 8)`. -/
theorem mod_eight_eq_one_of_prime_factors (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 8 = 1) : n % 8 = 1 := by
  induction n using Nat.recOnMul with
  | zero => have := h 2 Nat.prime_two (dvd_zero 2); omega
  | one => rfl
  | prime p hp => exact h p hp dvd_rfl
  | mul a b iha ihb =>
    have ha := iha (fun p hp hpa => h p hp (hpa.mul_right b))
    have hb := ihb (fun p hp hpb => h p hp (hpb.mul_left a))
    rw [Nat.mul_mod, ha, hb]

/-- **Family `c = b + 1`, `n = 1`: every solution with `y ≥ 2` is `(2, 2, 2)`**
(valid for every `k ≥ 1`). -/
theorem demjanenko_eq_two_of_two_le_y (k : ℕ) (hk : 1 ≤ k) {x y z : ℕ}
    (hs : IsSolution (2 * k + 1) (2 * k * (k + 1)) (2 * k * (k + 1) + 1) 1 x y z)
    (hy : 2 ≤ y) : x = 2 ∧ y = 2 ∧ z = 2 := by
  obtain ⟨hx, -, hz, h⟩ := isSolution_one.1 hs
  exact dem_y_ge_two hk hx hy hz h

/-- **Reduction of the family `c = b + 1` to the case `y = 1`** (valid for every `k ≥ 1`):
Jeśmanowicz' statement for `(2k+1, 2k(k+1), 2k(k+1)+1)`, `n = 1`, is equivalent to the
insolubility of `(2k+1)^x + 2k(k+1) = (2k(k+1)+1)^z`. -/
theorem jesmanowiczFor_demjanenko_iff (k : ℕ) (hk : 1 ≤ k) :
    JesmanowiczFor (2 * k + 1) (2 * k * (k + 1)) (2 * k * (k + 1) + 1) 1 ↔
      ¬ ∃ x z : ℕ, 0 < x ∧ 0 < z ∧
        (2 * k + 1) ^ x + 2 * k * (k + 1) = (2 * k * (k + 1) + 1) ^ z := by
  constructor
  · rintro hJ ⟨x, z, hx, hz, h⟩
    have := hJ x 1 z (isSolution_one.2 ⟨hx, by norm_num, hz, by rw [pow_one]; exact h⟩)
    omega
  · intro hno x y z hs
    obtain ⟨hx, hy, hz, h⟩ := isSolution_one.1 hs
    rcases Nat.lt_or_ge y 2 with hlt | hge
    · exfalso
      obtain rfl : y = 1 := by omega
      exact hno ⟨x, z, hx, hz, by rw [pow_one] at h; exact h⟩
    · exact dem_y_ge_two hk hx hge hz h

/-- **PARTIAL result for the family `c = b + 1`, `n = 1`.** If `2k + 1` has a prime factor
`p ≢ 1 (mod 8)`, then Jeśmanowicz' statement holds for `(2k+1, 2k(k+1), 2k(k+1)+1)`. -/
theorem jesmanowiczFor_demjanenko_of_prime_factor (k : ℕ) (hk : 1 ≤ k) (p : ℕ)
    (hpp : p.Prime) (hpa : p ∣ 2 * k + 1) (hp8 : p % 8 ≠ 1) :
    JesmanowiczFor (2 * k + 1) (2 * k * (k + 1)) (2 * k * (k + 1) + 1) 1 := by
  rw [jesmanowiczFor_demjanenko_iff k hk]
  rintro ⟨x, z, hx, hz, h⟩
  exact hp8 ((dem_y_one hk hx hz h).2.2 p hpp hpa)

/-- **PARTIAL result for the family `c = b + 1`, `n = 1`.** If `4 ∤ k`, then Jeśmanowicz'
statement holds for `(2k+1, 2k(k+1), 2k(k+1)+1)`. -/
theorem jesmanowiczFor_demjanenko_of_not_four_dvd (k : ℕ) (hk : 1 ≤ k) (h4 : ¬ 4 ∣ k) :
    JesmanowiczFor (2 * k + 1) (2 * k * (k + 1)) (2 * k * (k + 1) + 1) 1 := by
  rw [jesmanowiczFor_demjanenko_iff k hk]
  rintro ⟨x, z, hx, hz, h⟩
  have := mod_eight_eq_one_of_prime_factors (2 * k + 1) (dem_y_one hk hx hz h).2.2
  omega

/-- The same with the legs swapped. -/
theorem jesmanowiczFor_demjanenko_swap_of_not_four_dvd (k : ℕ) (hk : 1 ≤ k) (h4 : ¬ 4 ∣ k) :
    JesmanowiczFor (2 * k * (k + 1)) (2 * k + 1) (2 * k * (k + 1) + 1) 1 :=
  jesmanowiczFor_swap.1 (jesmanowiczFor_demjanenko_of_not_four_dvd k hk h4)

/-- Dem'janenko's theorem (1965) for the whole family `c = b + 1`, `n = 1`.
This is a KNOWN theorem but it is **NOT PROVED in this file**; it is only stated. -/
def DemjanenkoFamily : Prop :=
  ∀ k : ℕ, 1 ≤ k → JesmanowiczFor (2 * k + 1) (2 * k * (k + 1)) (2 * k * (k + 1) + 1) 1

/-- The residual statement that is **NOT PROVED in this file**: for `4 ∣ k` such that every
prime factor of `2k + 1` is `≡ 1 (mod 8)`, the equation `(2k+1)^x + 2k(k+1) = (2k(k+1)+1)^z`
has no solution. (The smallest such `k` is `8`, i.e. the triple `(17, 144, 145)`.) -/
def DemjanenkoResidual : Prop :=
  ∀ k x z : ℕ, 0 < k → 4 ∣ k → (∀ p : ℕ, p.Prime → p ∣ 2 * k + 1 → p % 8 = 1) →
    0 < x → 0 < z → (2 * k + 1) ^ x + 2 * k * (k + 1) ≠ (2 * k * (k + 1) + 1) ^ z

/-- What is proved here reduces Dem'janenko's theorem exactly to `DemjanenkoResidual`. -/
theorem demjanenkoFamily_iff_residual : DemjanenkoFamily ↔ DemjanenkoResidual := by
  constructor
  · intro hF k x z hk _ _ hx hz h
    exact (jesmanowiczFor_demjanenko_iff k hk).1 (hF k hk) ⟨x, z, hx, hz, h⟩
  · intro hR k hk
    rw [jesmanowiczFor_demjanenko_iff k hk]
    rintro ⟨x, z, hx, hz, h⟩
    have hc := (dem_y_one hk hx hz h).2.2
    have h8 := mod_eight_eq_one_of_prime_factors (2 * k + 1) hc
    exact hR k x z hk (by omega) hc hx hz h

/-! ### Some explicit members of the family (`n = 1`) -/

/-- `(9, 40, 41)` (`k = 4`; here `4 ∣ k`, but `3 ∣ 9` and `3 ≢ 1 (mod 8)`). -/
theorem jesmanowiczFor_9_40_41_one : JesmanowiczFor 9 40 41 1 := by
  have := jesmanowiczFor_demjanenko_of_prime_factor 4 (by norm_num) 3 (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `(11, 60, 61)` (`k = 5`). -/
theorem jesmanowiczFor_11_60_61_one : JesmanowiczFor 11 60 61 1 := by
  have := jesmanowiczFor_demjanenko_of_not_four_dvd 5 (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `(13, 84, 85)` (`k = 6`). -/
theorem jesmanowiczFor_13_84_85_one : JesmanowiczFor 13 84 85 1 := by
  have := jesmanowiczFor_demjanenko_of_not_four_dvd 6 (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `(15, 112, 113)` (`k = 7`). -/
theorem jesmanowiczFor_15_112_113_one : JesmanowiczFor 15 112 113 1 := by
  have := jesmanowiczFor_demjanenko_of_not_four_dvd 7 (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-! ### Axiom audit -/

#print axioms IsPrimitivePythagorean.not_pow_succ_dvd
#print axioms IsSolution.z_ne_x_of_lt
#print axioms IsSolution.z_ne_y_of_lt
#print axioms IsSolution.strict_cases_of_one_lt
#print axioms isPrimitivePythagorean_demjanenko
#print axioms dem_absurd
#print axioms dem_y_ge_two
#print axioms dem_y_one
#print axioms demjanenko_eq_two_of_two_le_y
#print axioms jesmanowiczFor_demjanenko_iff
#print axioms jesmanowiczFor_demjanenko_of_prime_factor
#print axioms jesmanowiczFor_demjanenko_of_not_four_dvd
#print axioms jesmanowiczFor_demjanenko_swap_of_not_four_dvd
#print axioms demjanenkoFamily_iff_residual
#print axioms jesmanowiczFor_9_40_41_one
#print axioms jesmanowiczFor_11_60_61_one
#print axioms jesmanowiczFor_13_84_85_one
#print axioms jesmanowiczFor_15_112_113_one

end Jesmanowicz
