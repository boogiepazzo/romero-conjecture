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

end Jesmanowicz
