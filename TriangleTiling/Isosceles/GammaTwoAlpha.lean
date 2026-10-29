/-
Results about the tile with `γ = 2α`, from Section 10 ("On the Number of Tiles Required
when γ = 2α") of M. Beeson, *Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:twoalphatiles` is `twoalphatiles`,
`lemma:luthar` is `luthar`, `lemma:edgerelations` is `edgerelations`.

The paper's hypothesis "the sides of a triangle with angles `(α, β, 2α)`" is used here
through its consequences `c² = a² + ab` (`lemma:twoalphatiles`) and the triangle
inequality `b < a + c`.
-/
import Erdos634.Gamma2Alpha
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Geometry.Euclidean.Triangle

namespace TriangleTiling

open EuclideanGeometry

section Geometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The strict triangle inequality for three non-collinear points. -/
theorem dist_lt_dist_add_dist_of_not_collinear {A B C : P}
    (h : ¬ Collinear ℝ ({A, B, C} : Set P)) : dist A C < dist A B + dist B C := by
  rcases (dist_triangle A B C).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (dist_add_dist_eq_iff.mp h'.symm).collinear h

/-- **Lemma `lemma:twoalphatiles`.** Let `ABC` be a nondegenerate triangle with sides
`a = |BC|`, `b = |CA|`, `c = |AB|` opposite the angles `α = ∠BAC`, `β`, `γ = ∠ACB`.
Then `γ = 2α` if and only if `c² = a² + ab`.

The paper states the forward direction for integer sides; here the sides are arbitrary reals,
and the converse (used in `lemma:luthar`) is included. The proof uses the law of cosines at
`A` and at `C` rather than the law of sines: with `x = cos α`, `y = cos γ`,
`b c² (a² + b² - c²) - a (b² + c² - a²)² + 2 a b² c² = 2 a b² c² (y - 2x² + 1)`,
and the left side factors as `(a + b) (c² - a² - ab) ((b - a)² - c²)`, whose last factor is
negative by the strict triangle inequality. -/
theorem twoalphatiles {A B C : P} {a b c : ℝ} (hABC : AffineIndependent ℝ ![A, B, C])
    (ha : dist B C = a) (hb : dist C A = b) (hc : dist A B = c) :
    ∠ A C B = 2 * ∠ B A C ↔ c ^ 2 = a ^ 2 + a * b := by
  have hcol := affineIndependent_iff_not_collinear_set.mp hABC
  -- The three strict triangle inequalities.
  have t1 := dist_lt_dist_add_dist_of_not_collinear hcol
  have t2 := dist_lt_dist_add_dist_of_not_collinear (A := B) (B := A) (C := C)
    (by rwa [Set.insert_comm])
  have t3 := dist_lt_dist_add_dist_of_not_collinear (A := A) (B := C) (C := B)
    (by rwa [Set.pair_comm])
  rw [dist_comm A C, hb, hc, ha] at t1
  rw [dist_comm B A, hc, ha, dist_comm A C, hb] at t2
  rw [hc, dist_comm A C, hb, dist_comm C B, ha] at t3
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  -- The law of cosines at `A` and at `C`.
  set x := Real.cos (∠ B A C) with hx
  set y := Real.cos (∠ A C B) with hy
  have hα : 2 * b * c * x = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := law_cos B A C
    rw [ha, dist_comm B A, hc, hb, ← hx] at this
    linear_combination this
  have hγ : 2 * a * b * y = a ^ 2 + b ^ 2 - c ^ 2 := by
    have := law_cos A C B
    rw [hc, dist_comm A C, hb, ha, ← hy] at this
    linear_combination this
  -- The key identity linking `y - (2x² - 1)` with the factored polynomial.
  have key : (a + b) * (c ^ 2 - a ^ 2 - a * b) * ((b - a) ^ 2 - c ^ 2)
      = 2 * a * b ^ 2 * c ^ 2 * (y - (2 * x ^ 2 - 1)) := by
    linear_combination (-(b * c ^ 2)) * hγ + (a * ((b ^ 2 + c ^ 2 - a ^ 2) + 2 * b * c * x)) * hα
  have hneg : (b - a) ^ 2 - c ^ 2 < 0 := by nlinarith
  constructor
  · intro h
    have hy2 : y - (2 * x ^ 2 - 1) = 0 := by
      rw [hy, h, Real.cos_two_mul]; ring
    rw [hy2, mul_zero] at key
    have hab : a + b ≠ 0 := by positivity
    rcases mul_eq_zero.mp key with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hab
      · linarith
    · linarith
  · intro h
    have hy2 : y - (2 * x ^ 2 - 1) = 0 := by
      have : 2 * a * b ^ 2 * c ^ 2 * (y - (2 * x ^ 2 - 1)) = 0 := by
        rw [← key]; simp [show c ^ 2 - a ^ 2 - a * b = 0 by linarith]
      rcases mul_eq_zero.mp this with h1 | h1
      · exfalso; have : 0 < 2 * a * b ^ 2 * c ^ 2 := by positivity
        linarith
      · exact h1
    -- `cos α > 0`, so `α < π/2` and both `γ` and `2α` lie in `[0, π]`.
    have hx0 : 0 < x := by
      have : 0 < 2 * b * c * x := by rw [hα]; nlinarith
      have : 0 < 2 * b * c := by positivity
      exact pos_of_mul_pos_right ‹0 < 2 * b * c * x› this.le
    have hαle : ∠ B A C ≤ Real.pi / 2 := by
      by_contra hcon
      push Not at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon.le
        (by linarith [angle_le_pi B A C, Real.pi_pos])
      linarith
    apply Real.injOn_cos ⟨angle_nonneg A C B, angle_le_pi A C B⟩
      ⟨by linarith [angle_nonneg B A C], by linarith⟩
    rw [Real.cos_two_mul, ← hx, ← hy]
    linarith

end Geometry

/-- **Lemma `lemma:luthar`**, arithmetic form. Let `a, b, c` be natural numbers with no common
factor. Then `a, b, c` are the sides of a nondegenerate triangle (strict triangle inequalities)
with `c² = a² + ab` if and only if `(a, b, c) = (k², m² - k², mk)` for some relatively prime
`k, m` with `2k > m > k`.

By `lemma:twoalphatiles`, `c² = a² + ab` is what "the triangle has angles `(α, β, 2α)`"
amounts to for the sides; the angle form of the lemma follows from this one once that link is
formalized. The forward direction uses Bonfioli's `gamma2alpha_param`, which is the paper's
first paragraph of the proof (`a` and `a + b` are coprime and their product is a square). -/
theorem luthar (a b c : ℕ) :
    (Nat.gcd (Nat.gcd a b) c = 1 ∧ c ^ 2 = a ^ 2 + a * b ∧
      a < b + c ∧ b < a + c ∧ c < a + b) ↔
    ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ m < 2 * k ∧
      a = k ^ 2 ∧ b = m ^ 2 - k ^ 2 ∧ c = k * m := by
  constructor
  · rintro ⟨hcop, hc, h1, h2, h3⟩
    have hb : 0 < b := by omega
    obtain ⟨k, m, hkm_cop, hkm, rfl, rfl, rfl⟩ := gamma2alpha_param a b c hb hc hcop
    refine ⟨k, m, hkm_cop, hkm, ?_, rfl, rfl, rfl⟩
    -- `b < a + c` reads `(m - k)(m + k) < k(m + k)`, so `m - k < k`.
    have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
    zify [hle] at h2
    have : (m : ℤ) < 2 * k := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg (sub_nonneg.mpr hcon) (by positivity : (0 : ℤ) ≤ m + k)]
    exact_mod_cast this
  · rintro ⟨k, m, hkm_cop, hkm, hm2k, rfl, rfl, rfl⟩
    have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
    have hkmZ : (k : ℤ) < m := by exact_mod_cast hkm
    have hm2kZ : (m : ℤ) < 2 * k := by exact_mod_cast hm2k
    have hk0 : (0 : ℤ) ≤ k := by positivity
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- A common divisor of `k²` and `m² - k²` divides `m²`, and `k², m²` are coprime.
      set d := Nat.gcd (Nat.gcd (k ^ 2) (m ^ 2 - k ^ 2)) (k * m)
      have hda : d ∣ k ^ 2 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
      have hdb : d ∣ m ^ 2 - k ^ 2 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
      have hdm : d ∣ m ^ 2 := by
        have := Nat.dvd_add hdb hda
        rwa [Nat.sub_add_cancel hle] at this
      have := Nat.dvd_gcd hda hdm
      rw [(Nat.Coprime.pow 2 2 hkm_cop).gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    · zify [hle]; ring
    · -- `a < b + c`: `m² + km - 2k² = (m - k)(m + 2k) > 0`.
      zify [hle]
      nlinarith [mul_pos (sub_pos.mpr hkmZ) (by omega : (0 : ℤ) < m + 2 * k)]
    · -- `b < a + c`: `2k² + km - m² = (2k - m)(k + m) > 0`.
      zify [hle]
      nlinarith [mul_pos (sub_pos.mpr hm2kZ) (by omega : (0 : ℤ) < k + m)]
    · -- `c < a + b`: `m² - km = m(m - k) > 0`.
      zify [hle]
      nlinarith [mul_pos (by omega : (0 : ℤ) < m) (sub_pos.mpr hkmZ)]

/-! ### The three cases of `lemma:edgerelations`, in terms of `(k, m)`

With `(a, b, c) = (k², m² - k², km)`, `k, m` coprime, `k ≥ 2` and `k < m`
(`lemma:luthar`). -/

/-- Case (i): `km = p k² + q (m² - k²)` has no solution with `p, q ≥ 0`. -/
theorem edgerelations_i (k m p q : ℤ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m) (hcop : IsCoprime k m)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : k * m = p * k ^ 2 + q * (m ^ 2 - k ^ 2)) : False := by
  -- Reducing modulo `k`: `k ∣ q m²`, hence `k ∣ q`.
  have hdvd : k ∣ q * m ^ 2 := ⟨m - p * k + q * k, by linear_combination -h⟩
  have hkq : k ∣ q := (hcop.pow_right (n := 2)).dvd_of_dvd_mul_right hdvd
  rcases hq.eq_or_lt with rfl | hq
  · -- `q = 0` gives `m = pk`, so `k ∣ m`, impossible for coprime `k, m` with `k ≥ 2`.
    have hm : m = k * p := by
      have : k * m = k * (k * p) := by linear_combination h
      exact mul_left_cancel₀ (by omega) this
    have hu := hcop.isUnit_of_dvd' (dvd_refl k) ⟨p, hm⟩
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
  · -- `q ≥ k`, so `km ≥ k (m² - k²) ≥ k (m + k) > km`.
    have hqk : k ≤ q := Int.le_of_dvd hq hkq
    have hb : m + k ≤ m ^ 2 - k ^ 2 := by nlinarith
    have h1 : k * (m + k) ≤ q * (m ^ 2 - k ^ 2) :=
      mul_le_mul hqk hb (by omega) (by omega)
    nlinarith

/-- Case (ii): `m² - k² = p k² + q km` has no integer solution `p, q` at all. -/
theorem edgerelations_ii (k m p q : ℤ) (hk : 2 ≤ k) (hcop : IsCoprime k m)
    (h : m ^ 2 - k ^ 2 = p * k ^ 2 + q * (k * m)) : False := by
  -- Reducing modulo `k`: `k ∣ m²`, so `k` is a unit.
  have hdvd : k ∣ m ^ 2 := ⟨k + p * k + q * m, by linear_combination h⟩
  have hu := (hcop.pow_right (n := 2)).isUnit_of_dvd' (dvd_refl k) hdvd
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega

/-- Case (iii): `k² = p (m² - k²) + q km` has no solution with `p, q ≥ 0`. -/
theorem edgerelations_iii (k m p q : ℤ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m) (hcop : IsCoprime k m)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : k ^ 2 = p * (m ^ 2 - k ^ 2) + q * (k * m)) : False := by
  -- Reducing modulo `m`: `m ∣ (p + 1) k²`, hence `m ∣ p + 1`, so `p ≥ m - 1 ≥ k`.
  have hdvd : m ∣ (p + 1) * k ^ 2 := ⟨p * m + q * k, by linear_combination h⟩
  have hmp : m ∣ p + 1 := (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right hdvd
  have hpk : k ≤ p := by have := Int.le_of_dvd (by omega) hmp; omega
  -- Then `k² ≥ p (m² - k²) ≥ k (m + k) > k²`.
  have hb : m + k ≤ m ^ 2 - k ^ 2 := by nlinarith
  have h1 : k * (m + k) ≤ p * (m ^ 2 - k ^ 2) :=
    mul_le_mul hpk hb (by omega) (by omega)
  have h2 : 0 ≤ q * (k * m) := mul_nonneg hq (mul_nonneg (by omega) (by omega))
  nlinarith

/-- **Lemma `lemma:edgerelations`.** Let `(a, b, c)` be integers with no common factor that
are the sides of a triangle with angles `(α, β, 2α)`, so that `c² = a² + ab` and `b < a + c`.
Then there are no nonnegative integers `p, q` with

* (i) `c = pa + qb`,
* (ii) `b = pa + qc` (indeed, not even with `p, q` allowed to be negative),
* (iii) `a = pb + qc`. -/
theorem edgerelations (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (htri : b < a + c)
    (hc : c ^ 2 = a ^ 2 + a * b) (hcop : Nat.gcd (Nat.gcd a b) c = 1) :
    (¬ ∃ p q : ℕ, c = p * a + q * b) ∧
    (¬ ∃ p q : ℤ, (b : ℤ) = p * a + q * c) ∧
    (¬ ∃ p q : ℕ, a = p * b + q * c) := by
  -- `lemma:luthar` (Bonfioli's `gamma2alpha_param`): `(a, b, c) = (k², m² - k², km)`.
  obtain ⟨k, m, hkm_cop, hkm, rfl, rfl, rfl⟩ := gamma2alpha_param a b c hb hc hcop
  have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
  have hcopZ : IsCoprime (k : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hkm_cop
  -- The triangle inequality `b < a + c` gives `m < 2k`; together with `0 < k < m`, `k ≥ 2`.
  have htriZ : (m : ℤ) ^ 2 - k ^ 2 < k ^ 2 + k * m := by
    have := htri; zify [hle] at this; linarith
  have h2k : (m : ℤ) < 2 * k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk0 : (0 : ℤ) < k := by
    have : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
    exact_mod_cast this
  have hkmZ : (k : ℤ) + 1 ≤ m := by exact_mod_cast hkm
  have hk2 : (2 : ℤ) ≤ k := by omega
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨p, q, h⟩
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub hle] at h'
    exact edgerelations_i k m p q hk2 hkmZ hcopZ (by positivity) (by positivity)
      (by linear_combination h')
  · rintro ⟨p, q, h⟩
    push_cast [Nat.cast_sub hle] at h
    exact edgerelations_ii k m p q hk2 hcopZ (by linear_combination h)
  · rintro ⟨p, q, h⟩
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub hle] at h'
    exact edgerelations_iii k m p q hk2 hkmZ hcopZ (by positivity) (by positivity)
      (by linear_combination h')

end TriangleTiling
