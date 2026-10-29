/-
`lemma:euler` (Section 4 of M. Beeson, *Tilings of an isosceles triangle*):
if `θ = 2πm/n` with `m, n` coprime and `cos θ` satisfies a nonzero rational polynomial of degree
at most `2`, then `n ∈ {1, 2, 3, 4, 5, 6, 8, 10, 12}`; if `sin θ` does too, then `n` is not `5` or
`10`.

The paper quotes Niven (`cos θ` has degree `φ(n)/2`). Here the first part comes from the
irreducibility of cyclotomic polynomials: `ζ = e^{iθ}` is a root of `(2X)² P((X² + 1)/(2X))`, of
degree at most `4`, so `φ(n) ≤ 4`. The second part reduces to the first, since
`sin θ = cos (π/2 - θ)` and `π/2 - θ` has denominator `20` when `n` is `5` or `10`.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.ComputeDegree

namespace TriangleTiling

open Polynomial Real

/-- **Small totients.** If `φ(n) ≤ 4` then `n` is one of `1, 2, 3, 4, 5, 6, 8, 10, 12`. -/
theorem totient_le_four {n : ℕ} (hn : 0 < n) (h : Nat.totient n ≤ 4) :
    n ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12} : Finset ℕ) := by
  have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr hn
  have hdvd : ∀ d, d ∣ n → Nat.totient d ≤ 4 := fun d hd =>
    (Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hd)).trans h
  have h120 : n ∣ 120 := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases k with _ | k
    · simp
    have hb := hdvd _ hpk
    rw [Nat.totient_prime_pow hp (Nat.succ_pos k), Nat.succ_sub_one] at hb
    have hp2 := hp.two_le
    have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
    have hp5 : p ≤ 5 := by
      have := le_trans (Nat.le_mul_of_pos_left (p - 1) hpk1) hb
      omega
    interval_cases p
    · have hk : k ≤ 2 := by
        by_contra hk
        push Not at hk
        have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        omega
      interval_cases k <;> norm_num
    · have hk : k = 0 := by
        by_contra hk
        have : 3 ≤ 3 ^ k := by
          calc 3 = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hk)
        omega
      subst hk; norm_num
    · exact absurd hp (by decide)
    · have hk : k = 0 := by
        by_contra hk
        have : 5 ≤ 5 ^ k := by
          calc 5 = 5 ^ 1 := by norm_num
            _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hk)
        omega
      subst hk; norm_num
  have hmem : n ∈ Nat.divisors 120 := Nat.mem_divisors.mpr ⟨h120, by norm_num⟩
  rw [show Nat.divisors 120 = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} by
    decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> first | decide | (exfalso; revert h; decide)

/-- `cos θ` with `θ = 2πm/n`, in terms of `ζ = e^{iθ}`: `2 cos θ · ζ = ζ² + 1`. -/
theorem cos_mul_zeta (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) * (2 * Complex.exp (θ * Complex.I)) =
      Complex.exp (θ * Complex.I) ^ 2 + 1 := by
  have hE : Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [Complex.ofReal_cos, Complex.cos]
  calc (Complex.exp (↑θ * Complex.I) + Complex.exp (-↑θ * Complex.I)) / 2 *
        (2 * Complex.exp (↑θ * Complex.I))
      = Complex.exp (↑θ * Complex.I) ^ 2 +
          Complex.exp (-↑θ * Complex.I) * Complex.exp (↑θ * Complex.I) := by ring
    _ = _ := by rw [hE]

/-- A polynomial of degree at most `2` evaluates to `p₀ + p₁ x + p₂ x²`. -/
theorem aeval_quadratic {S : Type*} [CommRing S] [Algebra ℚ S] {P : ℚ[X]} (hdeg : P.natDegree ≤ 2)
    (x : S) : aeval x P = algebraMap ℚ S (P.coeff 0) + algebraMap ℚ S (P.coeff 1) * x +
      algebraMap ℚ S (P.coeff 2) * x ^ 2 := by
  rw [aeval_eq_sum_range' (n := 3) (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [Algebra.smul_def, pow_zero, mul_one, pow_one]

/-- **Lemma `lemma:euler`, first part.** If `θ = 2πm/n` with `m, n` coprime and `cos θ` is a root
of a nonzero rational polynomial of degree at most `2`, then `n` is one of
`1, 2, 3, 4, 5, 6, 8, 10, 12`. -/
theorem euler {m n : ℕ} (hn : 0 < n) (hmn : m.Coprime n) {P : ℚ[X]} (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 2) (hroot : aeval (Real.cos (2 * π * m / n)) P = 0) :
    n ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12} : Finset ℕ) := by
  apply totient_le_four hn
  set θ : ℝ := 2 * π * m / n
  set ζ : ℂ := Complex.exp (θ * Complex.I)
  have hprim : IsPrimitiveRoot ζ n := by
    have := Complex.isPrimitiveRoot_exp_of_coprime m n hn.ne' hmn
    convert this using 2
    simp only [θ]
    push_cast
    ring
  set p0 := P.coeff 0
  set p1 := P.coeff 1
  set p2 := P.coeff 2
  set Q : ℚ[X] := C p2 * X ^ 4 + C (2 * p1) * X ^ 3 + C (4 * p0 + 2 * p2) * X ^ 2 +
    C (2 * p1) * X + C p2
  -- `Q` is not zero: else so is `P`.
  have hQ0 : Q ≠ 0 := by
    intro hQ
    have c4 := congrArg (coeff · 4) hQ
    have c3 := congrArg (coeff · 3) hQ
    have c2 := congrArg (coeff · 2) hQ
    simp only [Q, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c4 c3 c2
    norm_num at c4 c3 c2
    apply hP
    ext i
    rcases Nat.lt_or_ge i 3 with hi | hi
    · interval_cases i
      · simp only [coeff_zero]; linarith
      · simp only [coeff_zero]; exact c3
      · simp only [coeff_zero]; exact c4
    · simp only [coeff_zero]; exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hQdeg : Q.natDegree ≤ 4 := by
    simp only [Q]
    compute_degree
  -- `ζ` is a root of `Q`.
  have hc := cos_mul_zeta θ
  have hPc := hroot
  rw [aeval_quadratic hdeg] at hPc
  have hPc' : ((p0 : ℝ) : ℂ) + (p1 : ℂ) * (Real.cos θ : ℂ) + (p2 : ℂ) * (Real.cos θ : ℂ) ^ 2 = 0 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hPc
    simp only [eq_ratCast, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ratCast, Complex.ofReal_zero] at this
    simpa using this
  have hQζ : aeval ζ Q = 0 := by
    simp only [Q, map_add, map_mul, aeval_C, aeval_X, map_pow, eq_ratCast]
    push_cast
    linear_combination (4 * ζ ^ 2) * hPc' - (2 * (p1 : ℂ) * ζ +
      (p2 : ℂ) * (2 * (Real.cos θ : ℂ) * ζ + ζ ^ 2 + 1)) * hc
  have hdvd := minpoly.dvd ℚ ζ hQζ
  rw [← cyclotomic_eq_minpoly_rat hprim hn] at hdvd
  have := natDegree_le_of_dvd hdvd hQ0
  rw [natDegree_cyclotomic] at this
  omega

/-- Reducing the numerator of `2πm/n` modulo `n`. -/
theorem sin_mod (m n : ℕ) (hn : 0 < n) :
    Real.sin (2 * π * m / n) = Real.sin (2 * π * (m % n : ℕ) / n) := by
  have hm : (m : ℝ) = (m % n : ℕ) + n * (m / n : ℕ) := by exact_mod_cast (Nat.mod_add_div m n).symm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc Real.sin (2 * π * m / n)
      = Real.sin (2 * π * (m % n : ℕ) / n + (m / n : ℕ) * (2 * π)) := by
        congr 1; rw [hm]; field_simp
    _ = _ := Real.sin_add_nat_mul_two_pi _ _

theorem coprime_mod {m n : ℕ} (h : m.Coprime n) : (m % n).Coprime n := by
  unfold Nat.Coprime at h ⊢
  rw [← Nat.gcd_rec n m, Nat.gcd_comm]; exact h

/-- **Lemma `lemma:euler`, second part.** If moreover `sin θ` is a root of a nonzero rational
polynomial of degree at most `2`, then `n` is one of `1, 2, 3, 4, 6, 8, 12`. -/
theorem euler_sin {m n : ℕ} (hn : 0 < n) (hmn : m.Coprime n) {P R : ℚ[X]} (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 2) (hroot : aeval (Real.cos (2 * π * m / n)) P = 0) (hR : R ≠ 0)
    (hRdeg : R.natDegree ≤ 2) (hRroot : aeval (Real.sin (2 * π * m / n)) R = 0) :
    n ∈ ({1, 2, 3, 4, 6, 8, 12} : Finset ℕ) := by
  have h1 := euler hn hmn hP hdeg hroot
  -- `sin θ` as a cosine of an angle with denominator `20` is impossible.
  have key : ∀ k : ℕ, k.Coprime 20 →
      Real.sin (2 * π * m / n) = Real.cos (2 * π * k / ((20 : ℕ) : ℝ)) → False := by
    intro k hk he
    rw [he] at hRroot
    have := euler (by norm_num) hk hR hRdeg hRroot
    revert this; decide
  have hred := sin_mod m n hn
  have hcop := coprime_mod hmn
  have hlt : m % n < n := Nat.mod_lt _ hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 ⊢
  rcases h1 with h | h | h | h | h | h | h | h | h <;> subst h <;> (try simp)
  · -- `n = 5`
    set r := m % 5
    interval_cases r
    · exact absurd hcop (by decide)
    · exact (key 1 (by decide) (by rw [hred, ← Real.cos_pi_div_two_sub]; congr 1; push_cast; ring))
    · exact (key 3 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 7 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 11 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
  · -- `n = 10`
    set r := m % 10
    interval_cases r
    all_goals first
      | exact absurd hcop (by decide)
      | skip
    · exact (key 3 (by decide) (by rw [hred, ← Real.cos_pi_div_two_sub]; congr 1; push_cast; ring))
    · exact (key 1 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 9 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 13 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))

end TriangleTiling
