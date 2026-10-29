/-
Direction classes (in the proof of `theorem:isosceles2`).

Let `θ` be an angle that is not a rational multiple of `π`, and `ω = e^{iθ}`. The group generated
by `ω` and `-1` acts on the nonzero complex numbers, and `ω^i (-1)^j` determines `j` modulo `2`.
Choosing a representative in each orbit, we get a class `Cls z` (a parity) with
`Cls (-z) ↔ ¬ Cls z` and `Cls (ω z) ↔ Cls z`.

Applied with `θ = 4α` to the squared directions of tile edges, this is the paper's class
`i + j mod 2` of the direction `θ₀ + iα + jπ/2`, but it needs no connectivity argument: the
representatives are chosen orbit by orbit.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace TriangleTiling.DirClass

open Complex

variable (θ : ℝ)

/-- `ω = e^{iθ}`. -/
noncomputable def ω : ℂ := Complex.exp (θ * Complex.I)

/-- The orbit of `z` under `ω` and `-1`. -/
def Orbit (z : ℂ) : Set ℂ := {w | ∃ i j : ℤ, w = ω θ ^ i * (-1) ^ j * z}

/-- A representative of the orbit of `z`, depending only on the orbit. -/
noncomputable def rep (z : ℂ) : ℂ := Classical.epsilon (· ∈ Orbit θ z)

/-- The class of `z`: `z = ω^i (-1)^j · rep z` with `j` even. -/
def Cls (z : ℂ) : Prop := ∃ i j : ℤ, Even j ∧ z = ω θ ^ i * (-1) ^ j * rep θ z

theorem ω_ne : ω θ ≠ 0 := Complex.exp_ne_zero _

theorem neg_one_ne : (-1 : ℂ) ≠ 0 := neg_ne_zero.mpr one_ne_zero

theorem mem_orbit_self (z : ℂ) : z ∈ Orbit θ z := ⟨0, 0, by simp⟩

theorem orbit_eq {z w : ℂ} (h : w ∈ Orbit θ z) : Orbit θ w = Orbit θ z := by
  obtain ⟨i, j, rfl⟩ := h
  ext v
  constructor
  · rintro ⟨i', j', rfl⟩
    refine ⟨i' + i, j' + j, ?_⟩
    rw [zpow_add₀ (ω_ne θ), zpow_add₀ neg_one_ne]; ring
  · rintro ⟨i', j', rfl⟩
    refine ⟨i' - i, j' - j, ?_⟩
    rw [zpow_sub₀ (ω_ne θ), zpow_sub₀ neg_one_ne]
    field_simp [ω_ne θ, neg_one_ne]

theorem rep_mem (z : ℂ) : rep θ z ∈ Orbit θ z :=
  Classical.epsilon_spec (p := (· ∈ Orbit θ z)) ⟨z, mem_orbit_self θ z⟩

theorem rep_eq {z w : ℂ} (h : w ∈ Orbit θ z) : rep θ w = rep θ z := by
  unfold rep; rw [orbit_eq θ h]

theorem exists_rep (z : ℂ) : ∃ i j : ℤ, z = ω θ ^ i * (-1) ^ j * rep θ z := by
  obtain ⟨i, j, h⟩ := rep_mem θ z
  refine ⟨-i, -j, ?_⟩
  rw [h, zpow_neg, zpow_neg]
  field_simp [zpow_ne_zero i (ω_ne θ), zpow_ne_zero j neg_one_ne]

theorem rep_ne {z : ℂ} (hz : z ≠ 0) : rep θ z ≠ 0 := by
  obtain ⟨i, j, h⟩ := rep_mem θ z
  rw [h]
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero i (ω_ne θ)) (zpow_ne_zero j neg_one_ne)) hz

/-- `ω^i (-1)^j` determines `j` modulo `2`. -/
theorem parity_unique (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) {i j i' j' : ℤ}
    (h : ω θ ^ i * (-1) ^ j * z = ω θ ^ i' * (-1) ^ j' * z) : Even (j - j') := by
  have h1 : ω θ ^ (i - i') = (-1) ^ (j' - j) := by
    rw [zpow_sub₀ (ω_ne θ), zpow_sub₀ neg_one_ne]
    have h2 := mul_right_cancel₀ hz h
    field_simp [zpow_ne_zero i' (ω_ne θ), zpow_ne_zero j neg_one_ne]
    linear_combination h2
  have hm1 : (-1 : ℂ) = Complex.exp (Real.pi * Complex.I) := by
    rw [Complex.exp_pi_mul_I]
  rw [ω, ← Complex.exp_int_mul, hm1, ← Complex.exp_int_mul,
    Complex.exp_eq_exp_iff_exists_int] at h1
  obtain ⟨k, hk⟩ := h1
  have hk' : ((i - i' : ℤ) : ℝ) * θ = ((j' - j : ℤ) + 2 * k : ℝ) * Real.pi := by
    have := congrArg Complex.im hk
    simp at this
    push_cast
    linarith
  by_cases hi : i - i' = 0
  · rw [hi] at hk'
    simp at hk'
    have : (j' - j : ℤ) + 2 * k = 0 := by exact_mod_cast hk'.symm.symm
    exact ⟨k, by omega⟩
  · exfalso
    apply hθ
    refine ⟨((j' - j : ℤ) + 2 * k : ℚ) / (i - i' : ℤ), ?_⟩
    have hi' : ((i - i' : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
    push_cast at hk' hi' ⊢
    field_simp
    linarith

/-- The class of `z`, read off from any representation `z = ω^i (-1)^j · rep z`. -/
theorem cls_iff (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) {i j : ℤ}
    (h : z = ω θ ^ i * (-1) ^ j * rep θ z) : Cls θ z ↔ Even j := by
  constructor
  · rintro ⟨i1, j1, hj1, h1⟩
    have := parity_unique θ hθ (rep_ne θ hz) (h1.symm.trans h)
    have : j = j1 - (j1 - j) := by ring
    rw [this]; exact hj1.sub ‹_›
  · exact fun hj => ⟨i, j, hj, h⟩

/-- **Multiplying by `ω^i (-1)^j` changes the class by `j`.** -/
theorem cls_mul (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) (i j : ℤ) :
    Cls θ (ω θ ^ i * (-1) ^ j * z) ↔ (Cls θ z ↔ Even j) := by
  have hw : ω θ ^ i * (-1) ^ j * z ∈ Orbit θ z := ⟨i, j, rfl⟩
  have hw0 : ω θ ^ i * (-1) ^ j * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero i (ω_ne θ)) (zpow_ne_zero j neg_one_ne)) hz
  obtain ⟨i0, j0, h0⟩ := exists_rep θ z
  have hw' : ω θ ^ i * (-1) ^ j * z =
      ω θ ^ (i + i0) * (-1) ^ (j + j0) * rep θ (ω θ ^ i * (-1) ^ j * z) := by
    rw [rep_eq θ hw, zpow_add₀ (ω_ne θ), zpow_add₀ neg_one_ne]
    conv_lhs => rw [h0]
    ring
  rw [cls_iff θ hθ hw0 hw', cls_iff θ hθ hz h0, Int.even_add]
  tauto

theorem cls_neg (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) :
    Cls θ (-z) ↔ ¬ Cls θ z := by
  have := cls_mul θ hθ hz 0 1
  simp only [zpow_zero, zpow_one, one_mul, neg_one_mul] at this
  rw [this]
  simp

theorem cls_mul_ω (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) :
    Cls θ (ω θ * z) ↔ Cls θ z := by
  have := cls_mul θ hθ hz 1 0
  simp only [zpow_one, zpow_zero, mul_one] at this
  rw [this]
  simp

theorem cls_mul_ω_inv (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) :
    Cls θ ((ω θ)⁻¹ * z) ↔ Cls θ z := by
  have := cls_mul θ hθ hz (-1) 0
  simp only [zpow_neg, zpow_one, zpow_zero, mul_one] at this
  rw [this]
  simp

end TriangleTiling.DirClass
