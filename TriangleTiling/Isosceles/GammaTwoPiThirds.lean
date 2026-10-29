/-
Results about the tile with `γ = 2π/3`, from Section 11 ("Tilings of an Isosceles Triangle by a
Tile (α, β, 2π/3)") of M. Beeson, *Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:relprime` is `relprime`, and `lemma:2b+a` is
`two_b_add_a` (a Lean name cannot contain `+`).

A triangle with angles `(α, β, 2π/3)` and sides `(a, b, c)` satisfies `c² = a² + b² + ab`
(law of cosines, since `cos(2π/3) = -1/2`); these lemmas take that equation as hypothesis.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace TriangleTiling

/-- A prime dividing two of `a, b, c` with `c² = a² + b² + ab` divides the third. -/
theorem relprime_aux {a b c p : ℕ} (hp : p.Prime) (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    (p ∣ a → p ∣ b → p ∣ c) ∧ (p ∣ a → p ∣ c → p ∣ b) ∧ (p ∣ b → p ∣ c → p ∣ a) := by
  refine ⟨fun ha hb => ?_, fun ha hc => ?_, fun hb hc => ?_⟩
  · apply hp.dvd_of_dvd_pow (n := 2)
    rw [h]
    exact Nat.dvd_add (Nat.dvd_add (dvd_pow ha two_ne_zero) (dvd_pow hb two_ne_zero))
      (Dvd.dvd.mul_right ha b)
  · apply hp.dvd_of_dvd_pow (n := 2)
    have h' : c ^ 2 = (a ^ 2 + a * b) + b ^ 2 := by rw [h]; ring
    have hc2 : p ∣ c ^ 2 := dvd_pow hc two_ne_zero
    rw [h'] at hc2
    exact (Nat.dvd_add_right (Nat.dvd_add (dvd_pow ha two_ne_zero)
      (Dvd.dvd.mul_right ha b))).mp hc2
  · apply hp.dvd_of_dvd_pow (n := 2)
    have h' : c ^ 2 = (b ^ 2 + a * b) + a ^ 2 := by rw [h]; ring
    have hc2 : p ∣ c ^ 2 := dvd_pow hc two_ne_zero
    rw [h'] at hc2
    exact (Nat.dvd_add_right (Nat.dvd_add (dvd_pow hb two_ne_zero)
      (Dvd.dvd.mul_left hb a))).mp hc2

/-- **Lemma `lemma:relprime`.** If `c² = a² + b² + ab` and `a, b, c` have no common factor,
then `a, b, c` are pairwise relatively prime. -/
theorem relprime {a b c : ℕ} (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c := by
  -- A prime dividing all three divides `gcd (gcd a b) c = 1`.
  have hall : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ b → p ∣ c → False := by
    intro p hp ha hb hc
    have : p ∣ Nat.gcd (Nat.gcd a b) c := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc
    rw [hcop] at this
    exact hp.not_dvd_one this
  refine ⟨Nat.coprime_of_dvd fun p hp ha hb => ?_, Nat.coprime_of_dvd fun p hp hb hc => ?_,
    Nat.coprime_of_dvd fun p hp ha hc => ?_⟩
  · exact hall p hp ha hb ((relprime_aux hp h).1 ha hb)
  · exact hall p hp ((relprime_aux hp h).2.2 hb hc) hb hc
  · exact hall p hp ha ((relprime_aux hp h).2.1 ha hc) hc

/-- **Lemma `lemma:2b+a`.** Let `a, b, c` be integers with no common factor that are the sides
of a triangle with angles `(α, β, 2π/3)`, so `c² = a² + b² + ab`. Then `2b + a` is relatively
prime to `b` and to `c`, and to `a` except that, when `a` is even, `2` divides both `a` and
`2b + a`: the common divisors of `2b + a` and `a` divide `2`. -/
theorem two_b_add_a {a b c : ℕ} (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.Coprime (2 * b + a) b ∧ Nat.Coprime (2 * b + a) c ∧ Nat.gcd (2 * b + a) a ∣ 2 := by
  obtain ⟨hab, hbc, hac⟩ := relprime h hcop
  refine ⟨Nat.coprime_of_dvd fun p hp h1 hb => ?_, Nat.coprime_of_dvd fun p hp h1 hc => ?_, ?_⟩
  · -- `p ∣ 2b + a` and `p ∣ b` give `p ∣ a`.
    have ha : p ∣ a := (Nat.dvd_add_right (Dvd.dvd.mul_left hb 2)).mp h1
    exact hp.not_dvd_one (hab ▸ Nat.dvd_gcd ha hb)
  · -- `4c² = (2b + a)² + 3a²`, so `p ∣ 3a²`.
    have key : 4 * c ^ 2 = (2 * b + a) ^ 2 + 3 * a ^ 2 := by rw [h]; ring
    have h4 : p ∣ (2 * b + a) ^ 2 + 3 * a ^ 2 := key ▸ Dvd.dvd.mul_left (dvd_pow hc two_ne_zero) 4
    have h3a : p ∣ 3 * a ^ 2 := (Nat.dvd_add_right (dvd_pow h1 two_ne_zero)).mp h4
    rcases (Nat.Prime.dvd_mul hp).mp h3a with h3 | ha2
    · -- `p = 3`: then `9 ∣ 3a²`, so `3 ∣ a`, contradicting `gcd(a, c) = 1`.
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      subst hp3
      have h9 : 3 * 3 ∣ 3 * a ^ 2 := by
        have e1 : 3 * 3 ∣ (2 * b + a) ^ 2 := by rw [sq]; exact Nat.mul_dvd_mul h1 h1
        have e2 : 3 * 3 ∣ 4 * c ^ 2 :=
          Dvd.dvd.mul_left (by rw [sq]; exact Nat.mul_dvd_mul hc hc) 4
        rw [key] at e2
        exact (Nat.dvd_add_right e1).mp e2
      have ha : 3 ∣ a := Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9)
      exact Nat.prime_three.not_dvd_one (hac ▸ Nat.dvd_gcd ha hc)
    · -- `p ∣ a`: then `p ∣ 2b`, so `p = 2` (then `2 ∣ a, c`) or `p ∣ b` (then `p ∣ a, b`).
      have ha := hp.dvd_of_dvd_pow ha2
      have h2b : p ∣ 2 * b := (Nat.dvd_add_left ha).mp h1
      rcases (Nat.Prime.dvd_mul hp).mp h2b with h2 | hb
      · exact hp.not_dvd_one (hac ▸ Nat.dvd_gcd ha hc)
      · exact hp.not_dvd_one (hab ▸ Nat.dvd_gcd ha hb)
  · -- `d = gcd(2b + a, a)` divides `2b` and is coprime to `b`, so `d ∣ 2`.
    have hda : Nat.gcd (2 * b + a) a ∣ a := Nat.gcd_dvd_right _ _
    have hd2b : Nat.gcd (2 * b + a) a ∣ 2 * b :=
      (Nat.dvd_add_left hda).mp (Nat.gcd_dvd_left _ _)
    have hdb : Nat.Coprime (Nat.gcd (2 * b + a) a) b := Nat.Coprime.coprime_dvd_left hda hab
    exact hdb.dvd_of_dvd_mul_right hd2b

end TriangleTiling
