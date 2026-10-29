/-
Arithmetic for the not-prime theorems of M. Beeson, *Triangle tiling: the case 3α + 2β = π*
(arXiv 1206.2229v4), and a count used to exclude `N = 2`.
-/
import Mathlib
import TriangleTiling.ThreeAlpha.ARelation

namespace TriangleTiling.ThreeAlpha

/-- Squares mod 8, for the case `2k² - m² = u²`. -/
theorem zmod8_a : ∀ m u k : ZMod 8, m ^ 2 + u ^ 2 = 2 * k ^ 2 → ¬ (4 * m = 0 ∧ 4 * k = 0) →
    m ^ 2 = 1 ∧ k ^ 2 = 1 := by decide

theorem zmod8_b : ∀ n w : ZMod 8, n * w ^ 2 = 2 → n = 2 := by decide

theorem zmod3_a : ∀ u m : ZMod 3, u ^ 2 + m ^ 2 = 0 → u = 0 ∧ m = 0 := by decide

/-- `3k² - m²` is not a square when `gcd (m, k) = 1`. -/
theorem not_sq_3 {m k u : ℤ} (hcop : IsCoprime m k) (h : 3 * k ^ 2 - m ^ 2 = u ^ 2) : False := by
  have h3 : ((u : ZMod 3)) ^ 2 + (m : ZMod 3) ^ 2 = 0 := by
    have := congrArg (fun x : ℤ => (x : ZMod 3)) h
    push_cast at this
    have e3 : (3 : ZMod 3) = 0 := by decide
    rw [e3] at this
    linear_combination -this
  obtain ⟨hu, hm⟩ := zmod3_a _ _ h3
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hu hm
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨m', rfl⟩ := hm
  push_cast at h hcop
  have hk : (3 : ℤ) ∣ k ^ 2 := ⟨u' ^ 2 + m' ^ 2, by linarith⟩
  have hk' : (3 : ℤ) ∣ k := Int.prime_three.dvd_of_dvd_pow hk
  have := hcop.isUnit_of_dvd' (⟨m', rfl⟩ : (3 : ℤ) ∣ 3 * m') hk'
  rw [Int.isUnit_iff] at this
  omega

/-- **Arithmetic of `theorem:notprime2`.** If `N` is prime, `M ≠ 0`, `m/k` is in lowest terms with
`0 < m < k`, and `N (k - m)²(2k + m)² = M² (2k² - m²)(3k² - m²)`, then `N = 2`. -/
theorem notprime2_arith {N : ℕ} {M m k : ℤ} (hN : N.Prime) (hM : M ≠ 0) (hm : 0 < m) (hmk : m < k)
    (hcop : IsCoprime m k)
    (heq : (N : ℤ) * ((k - m) * (2 * k + m)) ^ 2 = M ^ 2 * ((2 * k ^ 2 - m ^ 2) * (3 * k ^ 2 - m ^ 2))) :
    N = 2 := by
  set X := (k - m) * (2 * k + m)
  set Y₁ := 2 * k ^ 2 - m ^ 2
  set Y₂ := 3 * k ^ 2 - m ^ 2
  have hX : 0 < X := mul_pos (by linarith) (by linarith)
  have hY₁ : 0 < Y₁ := by nlinarith
  have hY₂ : 0 < Y₂ := by nlinarith
  have hNz : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hN
  have hN0 : (0 : ℤ) < N := by exact_mod_cast hN.pos
  -- Cancel `g = gcd (M, X)`.
  obtain ⟨g, M', X', hg, hgcd, hMg, hXg⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left X hM)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have heq' : (N : ℤ) * X' ^ 2 = M' ^ 2 * (Y₁ * Y₂) := by
    rw [hMg, hXg] at heq
    have : ((g : ℤ) ^ 2) * ((N : ℤ) * X' ^ 2) = ((g : ℤ) ^ 2) * (M' ^ 2 * (Y₁ * Y₂)) := by
      linear_combination heq
    exact mul_left_cancel₀ (pow_ne_zero 2 hg0) this
  have hcopMX : IsCoprime (M' ^ 2) (X' ^ 2) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hgcd).pow
  have hM'N : M' ^ 2 ∣ (N : ℤ) := by
    have : M' ^ 2 ∣ (N : ℤ) * X' ^ 2 := ⟨Y₁ * Y₂, heq'⟩
    exact hcopMX.dvd_of_dvd_mul_right this
  have hM'1 : M' ^ 2 = 1 := by
    have hnat : M'.natAbs ^ 2 ∣ N := by
      have := Int.natAbs_dvd_natAbs.mpr hM'N
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at this
    rcases hN.eq_one_or_self_of_dvd _ hnat with h1 | h1
    · have : ((M'.natAbs ^ 2 : ℕ) : ℤ) = 1 := by rw [h1]; rfl
      rw [← Int.natAbs_sq]; exact_mod_cast this
    · exfalso
      have hd : M'.natAbs ∣ N := ⟨M'.natAbs, by rw [← h1]; ring⟩
      rcases hN.eq_one_or_self_of_dvd _ hd with h2 | h2
      · rw [h2] at h1; exact hN.one_lt.ne (by simpa using h1)
      · rw [h2] at h1
        have : N * N = N * 1 := by rw [mul_one]; nlinarith [h1]
        have := Nat.eq_of_mul_eq_mul_left hN.pos this
        exact hN.one_lt.ne this.symm
  rw [hM'1, one_mul] at heq'
  -- `Y₁` and `Y₂` are coprime.
  have hcop2 : IsCoprime (m ^ 2) (k ^ 2) := hcop.pow
  have hY₁k : IsCoprime Y₁ (k ^ 2) := by
    have : Y₁ = -m ^ 2 + k ^ 2 * 2 := by simp only [Y₁]; ring
    rw [this]
    exact (IsCoprime.add_mul_left_left_iff).mpr hcop2.neg_left
  have hY12 : IsCoprime Y₁ Y₂ := by
    have : Y₂ = k ^ 2 + Y₁ * 1 := by simp only [Y₁, Y₂]; ring
    rw [this]
    exact (IsCoprime.add_mul_left_right_iff).mpr hY₁k
  have hdvd : (N : ℤ) ∣ Y₁ * Y₂ := ⟨X' ^ 2, heq'.symm⟩
  rcases hNz.dvd_or_dvd hdvd with ⟨v, hv⟩ | ⟨v, hv⟩
  · -- `N ∣ Y₁`: then `Y₂` is a square, impossible.
    exfalso
    have hvY : v * Y₂ = X' ^ 2 := by
      have : (N : ℤ) * (v * Y₂) = (N : ℤ) * X' ^ 2 := by rw [heq', hv]; ring
      exact mul_left_cancel₀ hN0.ne' this
    have hc : IsCoprime Y₂ v := by
      have : IsCoprime Y₂ Y₁ := hY12.symm
      rw [hv] at this
      exact this.of_mul_right_right
    obtain ⟨u, hu | hu⟩ := Int.sq_of_isCoprime hc (by rw [mul_comm]; exact hvY)
    · exact not_sq_3 hcop hu
    · nlinarith [sq_nonneg u]
  · -- `N ∣ Y₂`: `Y₁ = u²`, `Y₂ = N w²`.
    have hvY : Y₁ * v = X' ^ 2 := by
      have : (N : ℤ) * (Y₁ * v) = (N : ℤ) * X' ^ 2 := by rw [heq', hv]; ring
      exact mul_left_cancel₀ hN0.ne' this
    have hc1 : IsCoprime Y₁ v := by
      have := hY12; rw [hv] at this; exact this.of_mul_right_right
    obtain ⟨u, hu | hu⟩ := Int.sq_of_isCoprime hc1 hvY
    swap
    · nlinarith [sq_nonneg u]
    have hv0 : 0 < v := by
      by_contra h0; push Not at h0
      have : Y₂ ≤ 0 := by rw [hv]; exact mul_nonpos_of_nonneg_of_nonpos hN0.le h0
      linarith
    obtain ⟨w, hw | hw⟩ := Int.sq_of_isCoprime hc1.symm (by rw [mul_comm]; exact hvY)
    swap
    · nlinarith [sq_nonneg w]
    -- Mod 8.
    have e1 : ((m : ZMod 8)) ^ 2 + (u : ZMod 8) ^ 2 = 2 * (k : ZMod 8) ^ 2 := by
      have := congrArg (fun x : ℤ => (x : ZMod 8)) hu
      simp only [Y₁] at this
      push_cast at this
      linear_combination -this
    have e2 : 3 * ((k : ZMod 8)) ^ 2 - (m : ZMod 8) ^ 2 = (N : ZMod 8) * (w : ZMod 8) ^ 2 := by
      have := congrArg (fun x : ℤ => (x : ZMod 8)) (hv.trans (by rw [hw]))
      simp only [Y₂] at this
      push_cast at this
      exact this
    have hne : ¬ (4 * (m : ZMod 8) = 0 ∧ 4 * (k : ZMod 8) = 0) := by
      rintro ⟨h1, h2⟩
      have h1' : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; exact h1
      have h2' : ((4 * k : ℤ) : ZMod 8) = 0 := by push_cast; exact h2
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1' h2'
      have hm2 : (2 : ℤ) ∣ m := by obtain ⟨t, ht⟩ := h1'; push_cast at ht; exact ⟨t, by linarith⟩
      have hk2 : (2 : ℤ) ∣ k := by obtain ⟨t, ht⟩ := h2'; push_cast at ht; exact ⟨t, by linarith⟩
      have := hcop.isUnit_of_dvd' hm2 hk2
      rw [Int.isUnit_iff] at this
      omega
    obtain ⟨hm1, hk1⟩ := zmod8_a _ _ _ e1 hne
    rw [hm1, hk1] at e2
    have hN8 := zmod8_b _ _ (by rw [← e2]; decide)
    have h8 : N % 8 = 2 := by rw [← ZMod.val_natCast, hN8]; rfl
    have : 2 ∣ N := by omega
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hN).mp this).symm

open Erdos634.Geometry Erdos634.BeesonColoring in
open Classical in
/-- **At least three tiles**: the three `α` angles at the corners of `ABC` (`lemma:shapes`) belong
to different tiles, since a tile has only one `α` corner. -/
theorem three_le_N {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β)) : 3 ≤ N := by
  obtain ⟨-, h3, -⟩ := shapes_irr D hirr hrel h hns
  let S : Fin 3 → Finset (Fin N) := fun k =>
    {i | ∃ l, (D.tile i).pts l = D.target.pts k ∧ (D.tile i).angleAt l = α}
  have hS : ∀ k, anglesAt D k α = (S k).card := fun k => rfl
  have hdisj : (Set.univ : Set (Fin 3)).PairwiseDisjoint S := by
    intro k _ k' _ hkk'
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    obtain ⟨l, hl, hla⟩ := hi
    obtain ⟨l', hl', hla'⟩ := hi'
    have := tile_angle_inj D hirr hrel h i (hla.trans hla'.symm)
    subst this
    exact hkk' (D.target.indep.injective (hl.symm.trans hl'))
  have hcard := Finset.card_biUnion (s := Finset.univ) (t := S) (fun k _ k' _ hk => hdisj
    (Set.mem_univ k) (Set.mem_univ k') hk)
  have hle := Finset.card_le_univ (Finset.univ.biUnion S)
  rw [Fintype.card_fin, hcard] at hle
  simp only [← hS] at hle
  omega

theorem zmod8_c : ∀ m k : ZMod 8, ¬ (4 * m = 0 ∧ 4 * k = 0) → 4 * (m + k) = 0 →
    4 ∣ (3 * k ^ 2 - m ^ 2).val → False := by decide

/-- **Arithmetic of `theorem:notprime4`.** If `N (m + k)² = M² (3k² - m²)` with `gcd (m, k) = 1`,
`0 < m < k`, then `m + k ∣ M`. -/
theorem notprime4_arith {N M m k : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (heq : N * (m + k) ^ 2 = M ^ 2 * (3 * k ^ 2 - m ^ 2)) : (m + k) ∣ M := by
  set d := m + k
  set Y := 3 * k ^ 2 - m ^ 2
  have hd0 : d ≠ 0 := by simp only [d]; omega
  -- Common divisors of `d` and `Y` divide `2`.
  have hdk : IsCoprime d k := by
    have : d = m + k * 1 := by simp only [d]; ring
    rw [this]; exact (IsCoprime.add_mul_left_left_iff).mpr hcop
  have hcomm : ∀ t : ℤ, t ∣ d → t ∣ Y → t ∣ 2 := by
    intro t htd htY
    have h2k : t ∣ 2 * k ^ 2 := by
      have : 2 * k ^ 2 = Y - d * (2 * k - d) := by simp only [Y, d]; ring
      rw [this]; exact dvd_sub htY (dvd_mul_of_dvd_left htd _)
    have htk : IsCoprime t (k ^ 2) := (hdk.of_isCoprime_of_dvd_left htd).pow_right
    exact htk.dvd_of_dvd_mul_right h2k
  -- Cancel `g = gcd (M, d)`.
  by_cases hM : M = 0
  · rw [hM]; exact dvd_zero _
  obtain ⟨g, M', d', hg, hgcd, hMg, hdg⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left d hM)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have heq' : N * d' ^ 2 = M' ^ 2 * Y := by
    rw [hMg, hdg] at heq
    have : ((g : ℤ) ^ 2) * (N * d' ^ 2) = ((g : ℤ) ^ 2) * (M' ^ 2 * Y) := by linear_combination heq
    exact mul_left_cancel₀ (pow_ne_zero 2 hg0) this
  have hcop' : IsCoprime (d' ^ 2) (M' ^ 2) := ((Int.isCoprime_iff_gcd_eq_one.mpr hgcd).symm).pow
  have hd'Y : d' ^ 2 ∣ Y := hcop'.dvd_of_dvd_mul_left ⟨N, by rw [← heq']; ring⟩
  have hd'd : d' ∣ d := ⟨g, by rw [hdg]⟩
  have hd'2 : d' ∣ 2 := hcomm d' hd'd (dvd_trans (dvd_pow_self d' two_ne_zero) hd'Y)
  have hd'1 : d' = 1 ∨ d' = -1 := by
    have hle : d'.natAbs ∣ 2 := by
      have := Int.natAbs_dvd_natAbs.mpr hd'2; simpa using this
    have h2 : d'.natAbs = 1 ∨ d'.natAbs = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hle with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases h2 with h | h
    · exact Int.natAbs_eq_iff.mp h |>.imp (by simp) (by simp)
    · exfalso
      -- `d` even: `m, k` odd, so `Y ≡ 2 (mod 8)`, but `4 ∣ Y`.
      have h4 : (4 : ℤ) ∣ Y := by
        have : (4 : ℤ) = d' ^ 2 := by
          rcases Int.natAbs_eq_iff.mp h with e | e <;> rw [e] <;> norm_num
        rw [this]; exact hd'Y
      have h2d : (2 : ℤ) ∣ d := by
        have : (2 : ℤ) ∣ d' := by
          rcases Int.natAbs_eq_iff.mp h with e | e <;> rw [e] <;> norm_num
        exact dvd_trans this hd'd
      have hne : ¬ (4 * (m : ZMod 8) = 0 ∧ 4 * (k : ZMod 8) = 0) := by
        rintro ⟨h1, h2⟩
        have h1' : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; exact h1
        have h2' : ((4 * k : ℤ) : ZMod 8) = 0 := by push_cast; exact h2
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1' h2'
        have hm2 : (2 : ℤ) ∣ m := by obtain ⟨t, ht⟩ := h1'; push_cast at ht; exact ⟨t, by linarith⟩
        have hk2 : (2 : ℤ) ∣ k := by obtain ⟨t, ht⟩ := h2'; push_cast at ht; exact ⟨t, by linarith⟩
        have := hcop.isUnit_of_dvd' hm2 hk2
        rw [Int.isUnit_iff] at this; omega
      have hd8 : 4 * ((m : ZMod 8) + k) = 0 := by
        obtain ⟨t, ht⟩ := h2d
        have : ((d : ℤ) : ZMod 8) = ((2 * t : ℤ) : ZMod 8) := by rw [ht]
        simp only [d] at this
        push_cast at this
        rw [this]
        have : (8 : ZMod 8) = 0 := by decide
        linear_combination (t : ZMod 8) * this
      apply zmod8_c _ _ hne hd8
      obtain ⟨t, ht⟩ := h4
      have : ((3 * (k : ZMod 8) ^ 2 - (m : ZMod 8) ^ 2)) = 4 * (t : ZMod 8) := by
        have := congrArg (fun x : ℤ => (x : ZMod 8)) ht
        simp only [Y] at this; push_cast at this; exact this
      rw [this]
      have : ∀ x : ZMod 8, 4 ∣ (4 * x).val := by decide
      exact this _
  rcases hd'1 with h | h
  · rw [hdg, h, one_mul] at *; exact ⟨M', by rw [hMg]; ring⟩
  · exact ⟨-M', by rw [hMg, hdg, h]; ring⟩

/-- **Arithmetic of `theorem:notprime3`.** With `N` prime, `s = m/k = (N - M²)/(N + M²)` in lowest
terms, and the base `Y = M(k + m)m = p mk + q(k² - m²) + r k²` (in units of the tile, `r ≥ 1`),
there is a contradiction. -/
theorem notprime3_arith {N : ℕ} {M m k p q r : ℤ} (hN : N.Prime) (hM : 0 < M) (hm : 0 < m)
    (hmk : m < k) (hcop : IsCoprime m k) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 1 ≤ r)
    (h1 : ((N : ℤ) + M ^ 2) * m = ((N : ℤ) - M ^ 2) * k)
    (h2 : M * (k + m) * m = p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2) : False := by
  have hk : 0 < k := by linarith
  -- `N + M² = k u`, `N - M² = m u`.
  have hkd : k ∣ ((N : ℤ) + M ^ 2) := by
    have : k ∣ ((N : ℤ) + M ^ 2) * m := ⟨(N : ℤ) - M ^ 2, by rw [h1]; ring⟩
    exact hcop.symm.dvd_of_dvd_mul_right this
  obtain ⟨u, hu⟩ := hkd
  have hu' : (N : ℤ) - M ^ 2 = m * u := by
    have : k * ((N : ℤ) - M ^ 2) = k * (m * u) := by linear_combination (-1) * h1 + m * hu
    exact mul_left_cancel₀ hk.ne' this
  have hN2 : (2 : ℤ) ≤ N := by exact_mod_cast hN.two_le
  have hu0 : 0 < u := by
    have : (0 : ℤ) < k * u := by rw [← hu]; positivity
    exact pos_of_mul_pos_right this hk.le
  have hNM : (M : ℤ) ^ 2 < N := by have : 0 < m * u := mul_pos hm hu0; linarith
  -- `gcd (N, M²) = 1`, so `u ∣ 2`.
  have hcopN : IsCoprime (N : ℤ) (M ^ 2) := by
    have hnd : ¬ N ∣ M.natAbs ^ 2 := by
      intro hd
      have hdM : N ∣ M.natAbs := hN.dvd_of_dvd_pow hd
      have h0 : 0 < M.natAbs := Int.natAbs_pos.mpr hM.ne'
      have := Nat.le_of_dvd h0 hdM
      have hsq : (M.natAbs : ℤ) ^ 2 = M ^ 2 := Int.natAbs_sq M
      have : (N : ℤ) ≤ M.natAbs := by exact_mod_cast this
      nlinarith
    have := (Nat.Prime.coprime_iff_not_dvd hN).mpr hnd
    have := Nat.isCoprime_iff_coprime.mpr this
    push_cast at this
    rwa [sq_abs] at this
  obtain ⟨x, y, hxy⟩ := hcopN
  have hu2 : u ∣ 2 := by
    have e : (2 : ℤ) = x * (u * (k + m)) + y * (u * (k - m)) := by
      have hs : u * (k + m) = 2 * N := by linear_combination -hu - hu'
      have hd : u * (k - m) = 2 * M ^ 2 := by linear_combination -hu + hu'
      rw [hs, hd]; linear_combination -2 * hxy
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
      (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  have hu12 : u ≤ 2 := Int.le_of_dvd (by norm_num) hu2
  -- `k - m ≥ M²`.
  have hkm : M ^ 2 ≤ k - m := by
    have hd : u * (k - m) = 2 * M ^ 2 := by linear_combination -hu + hu'
    nlinarith
  -- `q ≡ -M (mod k)`, so `q ≥ k - M`.
  have hqM : k ∣ M + q := by
    have : k ∣ (M + q) * m ^ 2 := ⟨p * m + q * k + r * k - M * m, by linear_combination h2⟩
    exact hcop.symm.pow_right.dvd_of_dvd_mul_right this
  obtain ⟨t, ht⟩ := hqM
  have ht1 : 1 ≤ t := by
    by_contra h0; push Not at h0
    have : k * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (by omega)
    linarith
  have hqk : k - M ≤ q := by nlinarith
  -- The contradiction.
  have hkm2 : 0 < k ^ 2 - m ^ 2 := by nlinarith
  have hkey : (k - M) * (k ^ 2 - m ^ 2) - M * m * (k + m) = k * (k + m) * (k - m - M) := by ring
  have hpos : 0 ≤ k * (k + m) * (k - m - M) := by
    apply mul_nonneg (by positivity)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hqk hkm2.le, mul_nonneg hp (mul_pos hm hk).le]

/-- **Arithmetic of `theorem:notprime5`.** If `N (k - m) = j²(m + k)(2k² - m²)` with `0 < m < k`
coprime and `j > 0`, then `N` is not prime: `2k² - m²` is a proper divisor. -/
theorem notprime5_arith {N : ℕ} {j m k : ℤ} (hN : N.Prime) (hj : 0 < j) (hm : 0 < m)
    (hmk : m < k) (hcop : IsCoprime m k)
    (h : (N : ℤ) * (k - m) = j ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2)) : False := by
  have hc1 : IsCoprime m (k - m) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u + v, v, by linear_combination huv⟩
  obtain ⟨u, v, huv⟩ := hc1.pow_left (m := 2)
  have hc2 : IsCoprime (2 * k ^ 2 - m ^ 2) (k - m) :=
    ⟨u, v - 2 * u * (k + m), by linear_combination huv⟩
  have hd : (2 * k ^ 2 - m ^ 2) ∣ (N : ℤ) :=
    hc2.dvd_of_dvd_mul_right ⟨j ^ 2 * (m + k), by rw [h]; ring⟩
  have hd1 : 1 < 2 * k ^ 2 - m ^ 2 := by nlinarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have hdN : 2 * k ^ 2 - m ^ 2 < (N : ℤ) := by
    have hkm : 0 < k - m := by linarith
    have : (2 * k ^ 2 - m ^ 2) * (k - m) < (N : ℤ) * (k - m) := by
      have e1 : k - m < j ^ 2 * (m + k) := by nlinarith
      rw [h, mul_comm (2 * k ^ 2 - m ^ 2)]
      exact mul_lt_mul_of_pos_right e1 (by linarith)
    exact lt_of_mul_lt_mul_right this hkm.le
  have hd' : (2 * k ^ 2 - m ^ 2).natAbs ∣ N := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa using this
  rcases hN.eq_one_or_self_of_dvd _ hd' with e | e <;> omega

section Corners

open Erdos634.Geometry Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
  (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
  (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β))
include hirr hrel h hns

/-- **The tiles at a corner** with angle `pα + qβ`: `p` with their `α`, `q` with their `β` there. -/
theorem corner_counts (k : Fin 3) {p q : ℕ} (hk : D.target.angleAt k = p * α + q * β) :
    vcount D k α = p ∧ vcount D k β = q ∧ tilesAt D k = p + q := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, -⟩
  · exact absurd hs hns
  have hc := corner_eq D hirr hrel h hz k
  rw [hk] at hc
  obtain ⟨e1, e2⟩ := indep hirr hrel hc.symm
  exact ⟨e1, e2, by rw [tilesAt_eq D hirr hrel h k (hz k), e1, e2]⟩

omit hirr hrel h hns in
open Classical in
/-- The one tile at `B`, when there is one, has an edge on `AB`. -/
theorem atB_onAB (h1 : tilesAt D 1 = 1) {i₀ : Fin N} (hi₀ : TileAt D 1 i₀) : AtBOnAB D i₀ := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1) := hcov
  obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov' (V := D.target.pts 1) (Or.inr rfl)
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    rw [← hcov']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have heq : e.1 = i₀ := by
    have hmem : ∀ i, TileAt D 1 i → i ∈ ({i | TileAt D 1 i} : Finset (Fin N)) := fun i hi => by
      simp [hi]
    have h1' : ({i | TileAt D 1 i} : Finset (Fin N)).card = 1 := h1
    have he1 : TileAt D 1 e.1 := by
      rcases hV with h' | h'
      · exact ⟨_, h'⟩
      · exact ⟨_, h'⟩
    exact Finset.card_le_one.mp h1'.le _ (hmem _ he1) _ (hmem _ hi₀)
  subst heq
  rcases hV with h' | h'
  · exact ⟨e.2, e.2 + 1, fin3_ne_add_one e.2, h', hsub (right_mem_segment ℝ _ _)⟩
  · exact ⟨e.2 + 1, e.2, (fin3_ne_add_one e.2).symm, h', hsub (left_mem_segment ℝ _ _)⟩

omit hirr hrel h hns in
/-- Some tile has a vertex at `B` and an edge on `AB`. -/
theorem exists_atB_onAB : ∃ i, AtBOnAB D i := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1) := hcov
  obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov' (V := D.target.pts 1) (Or.inr rfl)
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    rw [← hcov']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  refine ⟨e.1, ?_⟩
  rcases hV with h' | h'
  · exact ⟨e.2, e.2 + 1, fin3_ne_add_one e.2, h', hsub (right_mem_segment ℝ _ _)⟩
  · exact ⟨e.2 + 1, e.2, (fin3_ne_add_one e.2).symm, h', hsub (left_mem_segment ℝ _ _)⟩

open Classical in
/-- **The edges on a side of `ABC`**: `|side j| = p a + q b + r c` with `p, q, r` the numbers of
`a`, `b`, `c` edges on it, and `r ≥ 1` (the pigeonhole on the `γ` angles). -/
theorem side_decomp (j : Fin 3) :
    ∃ p q r : ℕ, 1 ≤ r ∧ dist (D.target.pts j) (D.target.pts (j + 1)) = p * a + q * b + r * c := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, -⟩
  · exact absurd hs hns
  have hsep := anglesSep D hirr hrel h
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.toDissection.side_walk j
  -- Edge lengths by type.
  have hlen : ∀ e : Fin N × Fin 3, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = (if edgeType D α e then a else 0) + (if edgeType D β e then b else 0) +
        (if edgeType D (2 * α + β) e then c else 0) := by
    intro e
    obtain ⟨ρ, h0, l0, h1, l1, h2, l2⟩ := tile_threeAlpha D h e.1
    have hd : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = (D.tile e.1).oppLen (e.2 + 2) := by
      unfold Tri.oppLen
      rw [(by decide : ∀ x : Fin 3, x + 2 + 1 = x) e.2,
        (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) e.2]
    have ht : ∀ x, edgeType D x e ↔ (D.tile e.1).angleAt (e.2 + 2) = x := by
      intro x; unfold edgeType; rw [localAngle_pts]
    simp only [ht]
    rw [hd]
    obtain ⟨u, hu⟩ := ρ.surjective (e.2 + 2)
    rw [← hu]
    have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
    fin_cases u
    · simp [h0, l0, hαβ, show α ≠ 2 * α + β by intro e; linarith]
    · simp [h1, l1, hαβ.symm, show β ≠ 2 * α + β by intro e; linarith]
    · simp [h2, l2, show 2 * α + β ≠ α by intro e; linarith, show 2 * α + β ≠ β by intro e; linarith]
  refine ⟨(part.filter (edgeType D α)).card, (part.filter (edgeType D β)).card,
    (part.filter (edgeType D (2 * α + β))).card, ?_, ?_⟩
  · -- A `c` edge on the side.
    have htwo : ∀ i : Fin 3, ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
        (Finset.univ.filter fun jj => (D.tile jj).localAngle P = 2 * α + β).card ≤ 1 := by
      intro i P hP
      change angleCount D P (2 * α + β) ≤ 1
      by_cases hPc : P ∈ Set.range D.target.pts
      · obtain ⟨m, rfl⟩ := hPc
        rw [show angleCount D (D.target.pts m) (2 * α + β) = 0 from hz m]; omega
      · obtain ⟨e1, -⟩ := side_counts D hirr hrel h (tri_side_subset_frontier D.target i hP) hPc
        omega
    have hγv : 2 * α + β = tileα D ∨ 2 * α + β = tileβ D ∨ 2 * α + β = tileγ D :=
      (tile_vals D hirr hrel h _).2 (Or.inr (Or.inr rfl))
    obtain ⟨ec, hec, hθc⟩ := side_has_edge_sep D hsep _ hγv j part hcov hdisj
      (fun e _ _ => ne_of_angleCount_zero D (hz j) e.1)
      (fun e _ _ => ne_of_angleCount_zero D (hz (j + 1)) e.1) (htwo j)
    exact Finset.card_pos.mpr ⟨ec, Finset.mem_filter.mpr ⟨hec, hθc⟩⟩
  · rw [← hsum, Finset.sum_congr rfl fun e _ => hlen e, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const, add_zero, nsmul_eq_mul, mul_zero]

end Corners

end TriangleTiling.ThreeAlpha
