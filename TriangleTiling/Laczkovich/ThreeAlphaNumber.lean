/-
The number theory of the tiling equation `N + M² = 2K²` (M. Beeson, *Triangle tiling: the case
3α + 2β = π*, arXiv 1206.2229v4): `lemma:6902` and `lemma:normtheorem`; and of the second tiling equation: `lemma:Msquared` and
`theorem:solvingsecond`.

Statements not yet checked with Beeson. "A square times a product of distinct primes" is
`N = r² q` with `q` squarefree, as in `theorem:tilingequation` (ii).

This file is in the Laczkovich library only because Bonfioli's `lemma36` (which is `lemma:6902`)
imports all of Mathlib.
-/
import Erdos634.Draft.BeesonRowL36

namespace TriangleTiling.ThreeAlpha

/-- **Lemma `lemma:6902`.** If the tiling equation `N = 2K² - M²` is solvable in integers, then `N`
is a square times a product of distinct primes, each of which is either `2` or of the form
`8n ± 1`. -/
theorem lemma6902 (N : ℕ) (h : ∃ M K : ℤ, (N : ℤ) = 2 * K ^ 2 - M ^ 2) :
    ∃ r q : ℕ, N = r ^ 2 * q ∧ Squarefree q ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, 1, by simp, squarefree_one, fun p hp h1 => absurd (Nat.le_of_dvd one_pos h1)
      (by have := hp.two_le; omega)⟩
  obtain ⟨M, K, hMK⟩ := h
  refine Erdos634.BeesonRow.lemma36 N M.natAbs K.natAbs hN ?_
  rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
  linarith

/-- Integers of the form `x² - 2y²`. -/
def NormRep (n : ℤ) : Prop := ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = n

theorem NormRep.mul {m n : ℤ} (hm : NormRep m) (hn : NormRep n) : NormRep (m * n) := by
  obtain ⟨x, y, rfl⟩ := hm
  obtain ⟨u, v, rfl⟩ := hn
  exact ⟨x * u + 2 * y * v, x * v + y * u, by ring⟩

theorem NormRep.neg {n : ℤ} (h : NormRep n) : NormRep (-n) := by
  obtain ⟨x, y, rfl⟩ := h
  exact ⟨x + 2 * y, x + y, by ring⟩

theorem NormRep.sq (f : ℤ) : NormRep (f ^ 2) := ⟨f, 0, by ring⟩

theorem NormRep.two : NormRep 2 := ⟨2, 1, by norm_num⟩

/-- `x² = 2y²` only for `x = y = 0`. -/
theorem eq_zero_of_sq_eq_two_sq {x y : ℤ} (h : x ^ 2 = 2 * y ^ 2) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy; simp at h; exact ⟨h, rfl⟩
  exfalso
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  set q : ℚ := (x : ℚ) / y
  have hq : (q : ℝ) = (x : ℝ) / y := by simp only [q]; push_cast; rfl
  have hq2 : (q : ℝ) ^ 2 = 2 := by
    rw [hq, div_pow, div_eq_iff (by positivity)]
    exact_mod_cast h
  have hs : ((|q| : ℚ) : ℝ) = Real.sqrt 2 := by
    rw [← hq2, Real.sqrt_sq_eq_abs, Rat.cast_abs]
  exact irrational_sqrt_two ⟨|q|, hs⟩

/-- **Thue's lemma**, for a square root of `2` mod `p`: a prime `p ≡ ±1 (mod 8)` is `-(x² - 2y²)`. -/
theorem NormRep.prime {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 1 ∨ p % 8 = 7) : NormRep (p : ℤ) := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_two_iff hp2).mpr h8
  set m := Nat.sqrt p
  have hm : m * m ≤ p := Nat.sqrt_le p
  have hm' : p < (m + 1) * (m + 1) := Nat.lt_succ_sqrt p
  -- Pigeonhole on the `(m + 1)²` pairs `(u, v)`, mapped to `u - a v` in `ZMod p`.
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    simp only [ZMod.card, Fintype.card_prod, Fintype.card_fin]; exact hm'
  obtain ⟨⟨u, v⟩, ⟨u', v'⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun w : Fin (m + 1) × Fin (m + 1) => ((w.1 : ℕ) : ZMod p) - a * ((w.2 : ℕ) : ZMod p)) hcard
  simp only at heq
  set x : ℤ := (u : ℤ) - u'
  set y : ℤ := (v : ℤ) - v'
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h0
    push Not at h0
    apply hne
    have h1 : (u : ℕ) = u' := by omega
    have h2 : (v : ℕ) = v' := by omega
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hxa : (x : ZMod p) = (y : ZMod p) * a := by
    simp only [x, y, Int.cast_sub, Int.cast_natCast]
    linear_combination heq
  have hdvd : (p : ℤ) ∣ x ^ 2 - 2 * y ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxa]
    have : (2 : ZMod p) = a * a := ha
    rw [this]; ring
  have hu := u.isLt
  have hu' := u'.isLt
  have hv := v.isLt
  have hv' := v'.isLt
  have hx2 : x ^ 2 ≤ (m : ℤ) ^ 2 := by
    have h1 : |x| ≤ m := by
      rw [abs_le]; constructor <;> simp only [x] <;> omega
    nlinarith [abs_nonneg x, sq_abs x]
  have hy2 : y ^ 2 ≤ (m : ℤ) ^ 2 := by
    have h1 : |y| ≤ m := by
      rw [abs_le]; constructor <;> simp only [y] <;> omega
    nlinarith [abs_nonneg y, sq_abs y]
  have hmp : (m : ℤ) ^ 2 < p := by
    have : m * m ≠ p := by
      intro h
      have hmd : m ∣ p := ⟨m, h.symm⟩
      have := hp.one_lt
      rcases hp.eq_one_or_self_of_dvd m hmd with h1 | h1
      · rw [h1] at h; omega
      · rw [h1] at h; nlinarith
    have : m * m < p := lt_of_le_of_ne hm this
    rw [pow_two]; exact_mod_cast this
  obtain ⟨t, ht⟩ := hdvd
  have ht0 : t ≠ 0 := by
    rintro rfl
    have := eq_zero_of_sq_eq_two_sq (by linarith : x ^ 2 = 2 * y ^ 2)
    rcases hxy with h | h
    · exact h this.1
    · exact h this.2
  have hpos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have htm : t = -1 := by
    have h1 : (p : ℤ) * t < p := by nlinarith
    have h2 : -(2 * p : ℤ) < p * t := by nlinarith
    have h3 : t < 1 := by nlinarith
    have h4 : -2 < t := by nlinarith
    omega
  have : NormRep (-(p : ℤ)) := ⟨x, y, by rw [ht, htm]; ring⟩
  simpa using this.neg

/-- A square times a product of distinct primes `2` or `8n ± 1` is `x² - 2y²`. -/
theorem NormRep.of_form {N : ℕ} (h : ∃ r q : ℕ, N = r ^ 2 * q ∧ Squarefree q ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7) : NormRep (N : ℤ) := by
  obtain ⟨r, q, rfl, hsf, hp⟩ := h
  push_cast
  refine (NormRep.sq r).mul ?_
  rw [← Nat.prod_primeFactors_of_squarefree hsf]
  push_cast
  apply Finset.prod_induction _ NormRep (fun _ _ => NormRep.mul) ⟨1, 0, by ring⟩
  intro p hpq
  have hpp := Nat.prime_of_mem_primeFactors hpq
  rcases hp p hpp (Nat.dvd_of_mem_primeFactors hpq) with rfl | h8
  · exact NormRep.two
  · exact NormRep.prime hpp h8

/-- **Lemma `lemma:normtheorem`.** Suppose `N` is a square times a product of distinct primes, each
of which is either `2` or of the form `8n ± 1`. Then the tiling equation `N + M² = 2K²` has a
solution in integers. If moreover `N` is neither a square nor twice a square, then it has a
solution in positive integers `M` and `K` with `M < K`. -/
theorem normtheorem (N : ℕ) (h : ∃ r q : ℕ, N = r ^ 2 * q ∧ Squarefree q ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7) :
    (∃ M K : ℤ, (N : ℤ) + M ^ 2 = 2 * K ^ 2) ∧
      (¬ IsSquare N → ¬ (∃ r : ℕ, N = 2 * r ^ 2) →
        ∃ M K : ℕ, 0 < M ∧ M < K ∧ N + M ^ 2 = 2 * K ^ 2) := by
  have hsol : ∃ M K : ℤ, (N : ℤ) + M ^ 2 = 2 * K ^ 2 := by
    obtain ⟨x, y, hxy⟩ := (NormRep.of_form h).neg
    exact ⟨x, y, by linarith⟩
  refine ⟨hsol, fun hsq htw => ?_⟩
  -- A solution with `M > 0` (and `K ≥ 0`), `M` minimal.
  have hex : ∃ M : ℕ, 0 < M ∧ ∃ K : ℕ, (N : ℤ) + (M : ℤ) ^ 2 = 2 * (K : ℤ) ^ 2 := by
    obtain ⟨M, K, hMK⟩ := hsol
    refine ⟨M.natAbs, ?_, K.natAbs, ?_⟩
    · rcases Nat.eq_zero_or_pos M.natAbs with h0 | h0
      · exfalso; apply htw
        refine ⟨K.natAbs, ?_⟩
        have : M = 0 := Int.natAbs_eq_zero.mp h0
        subst this
        have : ((N : ℤ)) = 2 * (K.natAbs : ℤ) ^ 2 := by rw [Int.natCast_natAbs, sq_abs]; linarith
        exact_mod_cast this
      · exact h0
    · rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]; exact hMK
  classical
  set M := Nat.find hex
  obtain ⟨hM0, K, hMK⟩ := Nat.find_spec hex
  have hmin : ∀ M' : ℕ, M' < M → ¬ (0 < M' ∧ ∃ K : ℕ, (N : ℤ) + (M' : ℤ) ^ 2 = 2 * (K : ℤ) ^ 2) :=
    fun M' h => Nat.find_min hex h
  have hN0 : (0 : ℤ) < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exact absurd ⟨0, by simp [h0]⟩ hsq
    · exact_mod_cast h0
  set Mz : ℤ := (M : ℤ)
  set Kz : ℤ := (K : ℤ)
  have hMpos : (0 : ℤ) < Mz := Int.natCast_pos.mpr hM0
  have hK0 : (0 : ℤ) ≤ Kz := by positivity
  have hM2K : Mz < 2 * Kz := by nlinarith
  have h2M3K : 2 * Mz < 3 * Kz := by nlinarith
  -- `3M - 4K ≤ 0`, by minimality.
  have h34 : 3 * Mz - 4 * Kz ≤ 0 := by
    by_contra hpos
    push Not at hpos
    apply hmin (3 * Mz - 4 * Kz).toNat (by omega)
    refine ⟨by omega, (3 * Kz - 2 * Mz).natAbs, ?_⟩
    rw [Int.natCast_natAbs, sq_abs, Int.toNat_of_nonneg hpos.le]
    linear_combination hMK
  by_cases hlt : Mz < Kz
  · refine ⟨M, K, hM0, by omega, ?_⟩
    have : ((N + M ^ 2 : ℕ) : ℤ) = ((2 * K ^ 2 : ℕ) : ℤ) := by push_cast; exact hMK
    exact_mod_cast this
  push Not at hlt
  -- `(4K - 3M, 3K - 2M)`.
  set M' := 4 * Kz - 3 * Mz
  set K' := 3 * Kz - 2 * Mz
  have hsol' : (N : ℤ) + M' ^ 2 = 2 * K' ^ 2 := by simp only [M', K']; linear_combination hMK
  have hM'0 : M' ≠ 0 := by
    intro h0
    apply htw
    have h0' : 4 * Kz - 3 * Mz = 0 := h0
    obtain ⟨u, hu⟩ : (4 : ℤ) ∣ Mz := by omega
    refine ⟨u.natAbs, ?_⟩
    have : (N : ℤ) = 2 * (u.natAbs : ℤ) ^ 2 := by
      rw [Int.natCast_natAbs, sq_abs]
      have hK : Kz = 3 * u := by omega
      rw [hu, hK] at hMK; linarith
    exact_mod_cast this
  have hM'K' : M' ≠ K' := by
    intro h0
    apply hsq
    refine ⟨K'.natAbs, ?_⟩
    have : (N : ℤ) = (K'.natAbs : ℤ) * K'.natAbs := by
      rw [Int.natCast_natAbs, ← pow_two, sq_abs]; rw [h0] at hsol'; linarith
    exact_mod_cast this
  refine ⟨M'.toNat, K'.toNat, by omega, by omega, ?_⟩
  have : ((N + M'.toNat ^ 2 : ℕ) : ℤ) = ((2 * K'.toNat ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    exact hsol'
  exact_mod_cast this

/-- `(1 - s)²(2 + s)² < (2 - s²)(3 - s²)` for `0 < s < 1`. -/
theorem second_rhs_gt_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (1 - s) ^ 2 * (2 + s) ^ 2 < (2 - s ^ 2) * (3 - s ^ 2) := by
  have h1 : 0 < 1 - s := by linarith
  have h2 : 0 < (1 - s) * (2 + s) := by positivity
  nlinarith [mul_pos hs0 h2]

/-- **Lemma `lemma:Msquared`.** If the second tiling equation
`N / M² = (2 - s²)(3 - s²) / ((1 - s)²(2 + s)²)` has a solution with `0 < s < 1`, then `M² < N`. -/
theorem Msquared {N : ℕ} {M : ℤ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (h : (N : ℝ) / (M : ℝ) ^ 2 = (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2)) :
    M ^ 2 < N := by
  have hlt := second_rhs_gt_one hs0 hs1
  have hD : 0 < (1 - s) ^ 2 * (2 + s) ^ 2 := by
    have : 0 < 1 - s := by linarith
    positivity
  have hR : 1 < (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2) := by
    rw [lt_div_iff₀ hD]; linarith
  rw [← h] at hR
  have hM : (M : ℝ) ^ 2 ≠ 0 := by
    intro h0; rw [h0, div_zero] at hR; linarith
  have hM2 : 0 < (M : ℝ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hM)
  rw [lt_div_iff₀ hM2, one_mul] at hR
  exact_mod_cast hR

/-- A solution `(M, s)` of the second tiling equation with `s` rational, `0 < s < 1`. -/
def SecondSol (N : ℕ) (M : ℤ) (s : ℚ) : Prop :=
  0 < s ∧ s < 1 ∧ (N : ℚ) / (M : ℚ) ^ 2 = (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2)

/-- The test of a candidate `(M, s)`, with the equation cleared of denominators. -/
def secondTest (N M : ℕ) (s : ℚ) : Bool :=
  decide (0 < M ∧ 0 < s ∧ s < 1 ∧
    (N : ℚ) * ((1 - s) ^ 2 * (2 + s) ^ 2) = (M : ℚ) ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)))

/-- The candidates: `0 < M` with `M² < N`, and `s = e/f` with `f ∣ N - M²` and `0 ≤ e < f`. -/
def secondCandidates (N : ℕ) : List (ℕ × ℚ) :=
  (List.range N).flatMap fun M =>
    if 0 < M ∧ M ^ 2 < N then
      ((List.range (N - M ^ 2 + 1)).filter (fun f => 0 < f ∧ (N - M ^ 2) % f = 0)).flatMap
        fun f : ℕ => (List.range f).map fun e : ℕ => (M, (e : ℚ) / f)
    else []

/-- The algorithm of `theorem:solvingsecond`. -/
def secondSolver (N : ℕ) : Option (ℕ × ℚ) :=
  (secondCandidates N).find? fun x => secondTest N x.1 x.2

theorem secondTest_iff {N M : ℕ} {s : ℚ} : secondTest N M s = true ↔ 0 < M ∧ SecondSol N M s := by
  unfold secondTest SecondSol
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨hM, hs0, hs1, h⟩
    have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hD : (1 - s) ^ 2 * (2 + s) ^ 2 ≠ 0 := by
      have : 0 < 1 - s := by linarith
      positivity
    refine ⟨hM, hs0, hs1, ?_⟩
    push_cast
    rw [div_eq_div_iff (by positivity) hD]
    linear_combination h
  · rintro ⟨hM, hs0, hs1, h⟩
    have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hD : (1 - s) ^ 2 * (2 + s) ^ 2 ≠ 0 := by
      have : 0 < 1 - s := by linarith
      positivity
    refine ⟨hM, hs0, hs1, ?_⟩
    push_cast at h
    rw [div_eq_div_iff (by positivity) hD] at h
    linear_combination h

/-- **Theorem `theorem:solvingsecond`.** There is an algorithm that proceeds from input `N` to
termination, and at termination either produces a solution `(M, s)` of the second tiling
equation with `s` rational, or reports that no such solution exists.

The algorithm is `secondSolver` (a terminating Lean function); a solution has `0 < s < 1`
(`SecondSol`). It searches `0 < M`, `M² < N` (`lemma:Msquared`) and `s = e/f` with `f ∣ N - M²`
and `0 ≤ e < f` (rational root theorem for the leading coefficient `N - M²`). -/
theorem solvingsecond (N : ℕ) :
    (∀ M : ℕ, ∀ s : ℚ, secondSolver N = some (M, s) → SecondSol N M s) ∧
      (secondSolver N = none → ∀ (M : ℤ) (s : ℚ), ¬ SecondSol N M s) := by
  constructor
  · intro M s h
    have := List.find?_some h
    exact (secondTest_iff.mp this).2
  · intro h M s hsol
    rw [secondSolver, List.find?_eq_none] at h
    obtain ⟨hs0, hs1, heq⟩ := hsol
    -- Normalize `M ≥ 0`.
    set M₀ := M.natAbs
    have hM2 : (((M₀ : ℤ)) : ℚ) ^ 2 = (M : ℚ) ^ 2 := by
      simp only [M₀, Int.natCast_natAbs, Int.cast_abs, sq_abs]
    have hsol₀ : SecondSol N M₀ s := ⟨hs0, hs1, by rw [hM2]; exact heq⟩
    have hlt : M₀ ^ 2 < N := by
      have := Msquared (N := N) (M := (M₀ : ℤ)) (s := (s : ℝ)) (by exact_mod_cast hs0)
        (by exact_mod_cast hs1) (by
          have e := congrArg (fun q : ℚ => (q : ℝ)) hsol₀.2.2
          push_cast at e; exact e)
      exact_mod_cast this
    have hM0 : 0 < M₀ := by
      rcases Nat.eq_zero_or_pos M₀ with h0 | h0
      · exfalso
        have hD : 0 < (1 - s) ^ 2 * (2 + s) ^ 2 := by
          have : 0 < 1 - s := by linarith
          positivity
        have hpos : 0 < (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2) :=
          div_pos (by nlinarith) hD
        rw [← hsol₀.2.2, h0] at hpos
        simp at hpos
      · exact h0
    have htest : secondTest N M₀ s = true := secondTest_iff.mpr ⟨hM0, hsol₀⟩
    -- The cleared equation, and `s = e/f` in lowest terms.
    have hc := (decide_eq_true_iff.mp htest).2.2.2
    set e : ℤ := s.num
    set f : ℕ := s.den
    have hf : (0 : ℚ) < f := by exact_mod_cast s.den_pos
    have hse : s = (e : ℚ) / f := (Rat.num_div_den s).symm
    have he : 0 < e := Rat.num_pos.mpr hs0
    have hef : e < f := by
      have := Rat.num_lt_denom_iff.mpr hs1
      exact this
    rw [hse] at hc
    field_simp at hc
    have hZ : ((N : ℤ) - (M₀ : ℤ) ^ 2) * e ^ 4 = (f : ℤ) * (-(2 * N * e ^ 3) -
        (5 * (M₀ : ℤ) ^ 2 - 3 * N) * e ^ 2 * f + 4 * N * e * f ^ 2 - (4 * N - 6 * (M₀ : ℤ) ^ 2) * f ^ 3) := by
      have : ((((N : ℤ) - (M₀ : ℤ) ^ 2) * e ^ 4 : ℤ) : ℚ) = (((f : ℤ) * (-(2 * N * e ^ 3) -
          (5 * (M₀ : ℤ) ^ 2 - 3 * N) * e ^ 2 * f + 4 * N * e * f ^ 2 -
          (4 * N - 6 * (M₀ : ℤ) ^ 2) * f ^ 3) : ℤ) : ℚ) := by
        push_cast
        linear_combination hc
      exact_mod_cast this
    have hcop : IsCoprime (f : ℤ) (e ^ 4) := by
      apply IsCoprime.pow_right
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact s.reduced
    have hdvd : (f : ℤ) ∣ (N : ℤ) - (M₀ : ℤ) ^ 2 := hcop.dvd_of_dvd_mul_right ⟨_, hZ⟩
    have hdvd' : f ∣ N - M₀ ^ 2 := by
      have : ((N - M₀ ^ 2 : ℕ) : ℤ) = (N : ℤ) - (M₀ : ℤ) ^ 2 := by push_cast [hlt.le]; ring
      rw [← this] at hdvd
      exact_mod_cast hdvd
    have hfle : f ≤ N - M₀ ^ 2 := Nat.le_of_dvd (by omega) hdvd'
    -- So `(M₀, s)` is a candidate, and it passes the test.
    have hmem : (M₀, s) ∈ secondCandidates N := by
      unfold secondCandidates
      rw [List.mem_flatMap]
      refine ⟨M₀, List.mem_range.mpr (by nlinarith), ?_⟩
      rw [if_pos ⟨hM0, hlt⟩, List.mem_flatMap]
      refine ⟨f, ?_, ?_⟩
      · rw [List.mem_filter, List.mem_range]
        exact ⟨by omega, by simp only [decide_eq_true_eq]; exact ⟨s.den_pos, Nat.mod_eq_zero_of_dvd hdvd'⟩⟩
      · refine List.mem_map.mpr ⟨e.toNat, List.mem_range.mpr (by omega), Prod.ext rfl ?_⟩
        have he' : ((e.toNat : ℕ) : ℚ) = (e : ℚ) := by
          have := Int.toNat_of_nonneg he.le
          exact_mod_cast this
        simp only
        rw [he', ← hse]
    exact absurd htest (by simpa using h _ hmem)

end TriangleTiling.ThreeAlpha
