/-
# Jeśmanowicz' conjecture: the family `c = b + 1` and the strict reduction for `n > 1`

STATUS: IN PROGRESS / NOT YET SOLVED
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

end Jesmanowicz
