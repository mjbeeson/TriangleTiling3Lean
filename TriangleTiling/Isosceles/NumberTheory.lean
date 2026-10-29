/-
Number-theoretic facts from Section 4 ("Some Number-Theoretic Facts") of
M. Beeson, *Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:sumsofsquares` is `sumsofsquares`,
`lemma:doublesquares` is `doublesquares`, `lemma:rationalsquares` is `rationalsquares`.
-/
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.SumTwoSquares

namespace TriangleTiling

/-- **Lemma `lemma:sumsofsquares`** (Hardy and Wright, Theorem 366). A natural number `n` is a
sum of two squares if and only if every prime `q ≡ 3 (mod 4)` occurs in `n` to an even power;
equivalently, the squarefree part of `n` is divisible by no prime of the form `4k + 3`.
This is Mathlib's `Nat.eq_sq_add_sq_iff`. -/
theorem sumsofsquares (n : ℕ) :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) :=
  Nat.eq_sq_add_sq_iff

/-- **Lemma `lemma:doublesquares`.** An integer `N` is a sum of two squares
if and only if `2N` is a sum of two squares.

The proof follows the paper: `(p-q)^2 + (p+q)^2 = 2(p^2+q^2)` gives one direction;
for the other, `x^2 + y^2 = 2N` forces `x + y` to be even, and then
`((x-y)/2)^2 + ((x+y)/2)^2 = N`. -/
theorem doublesquares (N : ℤ) :
    (∃ p q : ℤ, N = p ^ 2 + q ^ 2) ↔ (∃ x y : ℤ, 2 * N = x ^ 2 + y ^ 2) := by
  constructor
  · rintro ⟨p, q, rfl⟩
    exact ⟨p - q, p + q, by ring⟩
  · rintro ⟨x, y, h⟩
    -- `(x + y)^2 = 2N + 2xy` is even, so `x + y` is even.
    have hsq : Even ((x + y) ^ 2) := ⟨N + x * y, by linear_combination -h⟩
    obtain ⟨u, hu⟩ := (Int.even_pow' two_ne_zero).mp hsq
    -- With `x + y = 2u`, take `(x+y)/2 = u` and `(x-y)/2 = u - y`.
    refine ⟨u - y, u, ?_⟩
    have hx : x = 2 * u - y := by linarith
    subst hx
    linarith

/-- **Lemma `lemma:rationalsquares`.** If the integer `n` is a sum of two rational squares, then
it is a sum of two integer squares.

The proof is the paper's: clearing denominators, `d² n` is a sum of two integer squares, so by
`lemma:sumsofsquares` every prime `q ≡ 3 (mod 4)` occurs in `d² n`, hence in `n`, to an even
power. -/
theorem rationalsquares (n : ℕ) (x y : ℚ) (h : (n : ℚ) = x ^ 2 + y ^ 2) :
    ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  set d := x.den * y.den with hd
  have hd0 : d ≠ 0 := by positivity
  -- `d² n = (x.num · y.den)² + (y.num · x.den)²`.
  set a := (x.num * y.den).natAbs
  set b := (y.num * x.den).natAbs
  have hm : d ^ 2 * n = a ^ 2 + b ^ 2 := by
    have hq : ((d : ℚ)) ^ 2 * n = ((x.num * y.den : ℤ) : ℚ) ^ 2 + ((y.num * x.den : ℤ) : ℚ) ^ 2 := by
      have hx : x * x.den = x.num := Rat.mul_den_eq_num x
      have hy : y * y.den = y.num := Rat.mul_den_eq_num y
      rw [h, hd]; push_cast
      rw [← hx, ← hy]; ring
    have hz : ((d : ℤ)) ^ 2 * n = (x.num * y.den) ^ 2 + (y.num * x.den) ^ 2 := by
      exact_mod_cast hq
    have ha : ((a : ℤ)) ^ 2 = (x.num * y.den) ^ 2 := Int.natAbs_sq _
    have hb : ((b : ℤ)) ^ 2 = (y.num * x.den) ^ 2 := Int.natAbs_sq _
    have : ((d ^ 2 * n : ℕ) : ℤ) = ((a ^ 2 + b ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [hz, ha, hb]
    exact_mod_cast this
  have hcrit := (sumsofsquares (d ^ 2 * n)).mp ⟨a, b, hm⟩
  refine (sumsofsquares n).mpr fun q hq h3 => ?_
  haveI := Fact.mk (Nat.prime_of_mem_primeFactors hq)
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hq).2.2
  have hmq : q ∈ (d ^ 2 * n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
      dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hq) _,
      mul_ne_zero (pow_ne_zero _ hd0) hn0⟩
  have he := hcrit q hmq h3
  rw [padicValNat.mul (pow_ne_zero _ hd0) hn0, padicValNat.pow _ hd0] at he
  exact (Nat.even_add.mp he).mp (even_two_mul _)

end TriangleTiling
