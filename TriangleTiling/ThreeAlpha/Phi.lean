/-
The functions `Φ₁`, `Φ₂` of Section 5 ("A new invariant") of M. Beeson, *Triangle tiling: the
case 3α + 2β = π* (arXiv 1206.2229v4): `lemma:Phiproperties` and `lemma:Phicancellation`.

`lemma:Phiproperties` uses `δ/π ∉ ℚ` (`lemma:incommensurable`), here a hypothesis. Directions are
measured from a base direction `θ₀`; `Φ₁`, `Φ₂` are `0` off the coset `θ₀ + ℤδ + ℤπ`.
-/
import TriangleTiling.ThreeAlpha.Defs
import Erdos634.Draft.FluxCancel

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry


section Eval

variable {δ : ℝ} (hδ : ¬ ∃ q : ℚ, δ = (q : ℝ) * Real.pi)
include hδ

/-- The coordinates `(n, ε)` of a direction are unique, `ε` modulo `2`. -/
theorem coset_eq {θ₀ : Real.Angle} {n m e f : ℤ}
    (h : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) = θ₀ + ((m * δ + f * Real.pi : ℝ) : Real.Angle)) :
    n = m ∧ Even (e - f) := by
  have h' := add_left_cancel h
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h'
  obtain ⟨k, hk⟩ := h'
  have hπ := Real.pi_pos
  by_cases hnm : n = m
  · subst hnm
    refine ⟨rfl, k, ?_⟩
    have : ((e - f : ℤ) : ℝ) = ((k + k : ℤ) : ℝ) := by
      push_cast
      have : ((e : ℝ) - f) * Real.pi = (k + k) * Real.pi := by linarith
      exact mul_right_cancel₀ hπ.ne' this
    exact_mod_cast this
  · exfalso
    apply hδ
    have hd : ((n : ℝ) - m) ≠ 0 := fun e0 => hnm (by exact_mod_cast sub_eq_zero.mp e0)
    refine ⟨(2 * k - (e - f)) / (n - m), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination hk

omit hδ in
theorem coe_add_two_pi_mul' (x : ℝ) (t : ℤ) :
    ((x + (t + t : ℤ) * Real.pi : ℝ) : Real.Angle) = (x : Real.Angle) := by
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  exact ⟨t, by push_cast; ring⟩

/-- `Φ₁(θ₀ + nδ + επ) = (-1)^ε`, for every integer `ε`. -/
theorem phi1_eval (θ₀ : Real.Angle) (n e : ℤ) :
    Phi1 δ θ₀ (θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)) = ((e.negOnePow : ℤ) : ℝ) := by
  unfold Phi1
  rcases Int.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hang : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) = θ₀ + ((n * δ : ℝ) : Real.Angle) := by
      subst ht; rw [coe_add_two_pi_mul' (n * δ) t]
    rw [if_pos ⟨n, hang⟩, Int.negOnePow_even _ ⟨t, ht⟩]
    simp
  · have hodd : ¬ ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ : ℝ) : Real.Angle) := by
      rintro ⟨m, hm⟩
      have := coset_eq hδ (m := m) (f := 0) (by rw [hm]; simp)
      rw [sub_zero] at this
      exact (Int.not_even_iff_odd.mpr ⟨t, ht⟩) this.2
    have hang : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((n * δ + Real.pi : ℝ) : Real.Angle) := by
      subst ht
      have : (n : ℝ) * δ + ((2 * t + 1 : ℤ) : ℝ) * Real.pi
          = (n * δ + Real.pi) + ((t + t : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [this, coe_add_two_pi_mul' _ t]
    rw [if_neg hodd, if_pos ⟨n, hang⟩, Int.negOnePow_odd _ ⟨t, ht⟩]
    simp

/-- `Φ₂(θ₀ + nδ + επ) = (-1)^(n+ε)`, for every integer `ε`. -/
theorem phi2_eval (θ₀ : Real.Angle) (n e : ℤ) :
    Phi2 δ θ₀ (θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)) = (((n + e).negOnePow : ℤ) : ℝ) := by
  unfold Phi2
  rcases Int.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hex : ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ : ℝ) : Real.Angle) := ⟨n, by subst ht; rw [coe_add_two_pi_mul' (n * δ) t]⟩
    rw [dif_pos hex]
    set m := hex.choose with hmdef
    have hc : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) = θ₀ + ((m * δ : ℝ) : Real.Angle) :=
      hex.choose_spec
    have hm := (coset_eq hδ (m := m) (f := 0) (by rw [hc]; simp)).1
    rw [← hm, Int.negOnePow_add, Int.negOnePow_even e ⟨t, ht⟩, mul_one]
  · have hodd : ¬ ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ : ℝ) : Real.Angle) := by
      rintro ⟨m, hm⟩
      have := coset_eq hδ (m := m) (f := 0) (by rw [hm]; simp)
      rw [sub_zero] at this
      exact (Int.not_even_iff_odd.mpr ⟨t, ht⟩) this.2
    have hex : ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ + Real.pi : ℝ) : Real.Angle) := ⟨n, by
      subst ht
      have : (n : ℝ) * δ + ((2 * t + 1 : ℤ) : ℝ) * Real.pi
          = (n * δ + Real.pi) + ((t + t : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [this, coe_add_two_pi_mul' _ t]⟩
    rw [dif_neg hodd, dif_pos hex]
    set m := hex.choose with hmdef
    have hc : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ + Real.pi : ℝ) : Real.Angle) := hex.choose_spec
    have hm := (coset_eq hδ (m := m) (f := 1) (by rw [hc]; simp)).1
    rw [← hm, Int.negOnePow_add, Int.negOnePow_odd e ⟨t, ht⟩]
    push_cast
    ring

omit hδ in
/-- Off the coset `θ₀ + ℤδ + ℤπ`, `Φ₁ = Φ₂ = 0`. -/
theorem phi_off {θ₀ θ : Real.Angle}
    (h : ¬ ∃ n e : ℤ, θ = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)) :
    Phi1 δ θ₀ θ = 0 ∧ Phi2 δ θ₀ θ = 0 := by
  have h1 : ¬ ∃ m : ℤ, θ = θ₀ + ((m * δ : ℝ) : Real.Angle) := by
    rintro ⟨m, hm⟩; exact h ⟨m, 0, by rw [hm]; simp⟩
  have h2 : ¬ ∃ m : ℤ, θ = θ₀ + ((m * δ + Real.pi : ℝ) : Real.Angle) := by
    rintro ⟨m, hm⟩; exact h ⟨m, 1, by rw [hm]; simp⟩
  unfold Phi1 Phi2
  rw [if_neg h1, if_neg h2, dif_neg h1, dif_neg h2]
  exact ⟨rfl, rfl⟩

end Eval

/-- **Lemma `lemma:Phiproperties`.** `Φ₁` and `Φ₂` take the values `±1` and satisfy
`Φ(θ + π) = -Φ(θ)`, `Φ(-θ) = Φ(θ)` (directions measured from `θ₀`); and they are the only two
functions on directions with values `±1` and `Φ(θ + π) = -Φ(θ)` whose tile value is independent,
up to sign, of the placement of the tile.

The last clause is stated as in its proof: writing `Φ(nδ + επ) = (-1)^ε χ(n)` with `χ(0) = 1`,
a placed tile has value `(-1)^ε (a χ(n) + b χ(n+1) + c χ(n+3))` (`lemma:Phitile`); if its absolute
value does not depend on `n`, then `χ = 1` (`Φ₁`) or `χ(n) = (-1)^n` (`Φ₂`). -/
theorem Phiproperties {δ : ℝ} (hδ : ¬ ∃ q : ℚ, δ = (q : ℝ) * Real.pi) (θ₀ : Real.Angle) :
    (∀ n ε : ℤ, (ε = 0 ∨ ε = 1) →
      (Phi1 δ θ₀ (θ₀ + ((n * δ + ε * Real.pi : ℝ) : Real.Angle)) = 1 ∨
        Phi1 δ θ₀ (θ₀ + ((n * δ + ε * Real.pi : ℝ) : Real.Angle)) = -1) ∧
      (Phi2 δ θ₀ (θ₀ + ((n * δ + ε * Real.pi : ℝ) : Real.Angle)) = 1 ∨
        Phi2 δ θ₀ (θ₀ + ((n * δ + ε * Real.pi : ℝ) : Real.Angle)) = -1)) ∧
    (∀ θ : Real.Angle, Phi1 δ θ₀ (θ + Real.pi) = - Phi1 δ θ₀ θ ∧
      Phi2 δ θ₀ (θ + Real.pi) = - Phi2 δ θ₀ θ) ∧
    (∀ θ : Real.Angle, Phi1 δ θ₀ (θ₀ - (θ - θ₀)) = Phi1 δ θ₀ θ ∧
      Phi2 δ θ₀ (θ₀ - (θ - θ₀)) = Phi2 δ θ₀ θ) ∧
    (∀ (a b c : ℝ) (χ : ℤ → ℝ), 0 < a → 0 < b → 0 < c → a ≠ b → b ≠ c → a ≠ c →
      a < b + c → b < a + c → c < a + b → (∀ n, χ n = 1 ∨ χ n = -1) → χ 0 = 1 →
      (∀ n, |a * χ n + b * χ (n + 1) + c * χ (n + 3)| = |a * χ 0 + b * χ 1 + c * χ 3|) →
      (∀ n, χ n = 1) ∨ (∀ n, χ n = (-1) ^ n)) := by
  -- Shifting a point of the coset, or reflecting it in `θ₀`, stays in the coset.
  have shift : ∀ (θ : Real.Angle) (x : ℝ), (∃ n e : ℤ, θ + x = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)) →
      (∀ n e : ℤ, ∃ n' e' : ℤ, ((n * δ + e * Real.pi - x : ℝ) : Real.Angle)
        = ((n' * δ + e' * Real.pi : ℝ) : Real.Angle)) →
      ∃ n e : ℤ, θ = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) := by
    rintro θ x ⟨n, e, h⟩ hx
    obtain ⟨n', e', h'⟩ := hx n e
    refine ⟨n', e', ?_⟩
    rw [← h', Real.Angle.coe_sub, ← add_sub_assoc, ← h]
    abel
  refine ⟨fun n e _ => ?_, fun θ => ?_, fun θ => ?_, ?_⟩
  · rw [phi1_eval hδ, phi2_eval hδ]
    constructor
    · rcases Int.units_eq_one_or e.negOnePow with h | h <;> simp [h]
    · rcases Int.units_eq_one_or (n + e).negOnePow with h | h <;> simp [h]
  · by_cases hθ : ∃ n e : ℤ, θ = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
    · obtain ⟨n, e, rfl⟩ := hθ
      have : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) + (Real.pi : Real.Angle)
          = θ₀ + ((n * δ + ((e + 1 : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
        rw [add_assoc, ← Real.Angle.coe_add]; push_cast; ring_nf
      rw [this, phi1_eval hδ, phi1_eval hδ, phi2_eval hδ, phi2_eval hδ, ← add_assoc,
        Int.negOnePow_succ, Int.negOnePow_succ]
      push_cast
      exact ⟨rfl, rfl⟩
    · have hθ' : ¬ ∃ n e : ℤ, θ + Real.pi = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) := by
        intro h
        exact hθ (shift θ Real.pi h fun n e => ⟨n, e - 1, by push_cast; ring_nf⟩)
      rw [(phi_off hθ).1, (phi_off hθ).2, (phi_off hθ').1, (phi_off hθ').2]
      simp
  · by_cases hθ : ∃ n e : ℤ, θ = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
    · obtain ⟨n, e, rfl⟩ := hθ
      have : θ₀ - (θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) - θ₀)
          = θ₀ + ((((-n : ℤ) : ℝ) * δ + ((-e : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
        have e' : (((-n : ℤ) : ℝ) * δ + ((-e : ℤ) : ℝ) * Real.pi : ℝ) = -(n * δ + e * Real.pi) := by
          push_cast; ring
        rw [add_sub_cancel_left, e', Real.Angle.coe_neg, sub_eq_add_neg]
      rw [this, phi1_eval hδ, phi1_eval hδ, phi2_eval hδ, phi2_eval hδ, Int.negOnePow_neg,
        show -n + -e = -(n + e) by ring, Int.negOnePow_neg]
      exact ⟨rfl, rfl⟩
    · have hθ' : ¬ ∃ n e : ℤ, θ₀ - (θ - θ₀) = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) := by
        rintro ⟨n, e, h⟩
        apply hθ
        refine ⟨-n, -e, ?_⟩
        have : θ = θ₀ - (θ₀ - (θ - θ₀) - θ₀) := by abel
        have e' : (((-n : ℤ) : ℝ) * δ + ((-e : ℤ) : ℝ) * Real.pi : ℝ) = -(n * δ + e * Real.pi) := by
          push_cast; ring
        rw [this, h, add_sub_cancel_left, e', Real.Angle.coe_neg, sub_eq_add_neg]
      rw [(phi_off hθ).1, (phi_off hθ).2, (phi_off hθ').1, (phi_off hθ').2]
      exact ⟨rfl, rfl⟩
  · intro a b c χ ha hb hc hab hbc hac t1 t2 t3 hχ h0 hconst
    -- The absolute tile value determines `(χ n, χ (n+1), χ (n+3))` up to sign.
    have key : ∀ n, χ (n + 1) = χ 1 * χ n := by
      intro n
      have h := hconst n
      rw [h0] at h
      rcases hχ n with e1 | e1 <;> rcases hχ (n + 1) with e2 | e2 <;>
        rcases hχ (n + 3) with e3 | e3 <;> rcases hχ 1 with u | u <;> rcases hχ 3 with w | w <;>
        simp only [e1, e2, e3, u, w] at h ⊢ <;>
        first
        | (exfalso
           rcases abs_eq_abs.mp h with e | e <;>
             first
             | linarith
             | (apply hab; linarith)
             | (apply hbc; linarith)
             | (apply hac; linarith))
        | norm_num
    have hu : χ 1 * χ 1 = 1 := by rcases hχ 1 with u | u <;> rw [u] <;> norm_num
    have hne : χ 1 ≠ 0 := by rcases hχ 1 with u | u <;> rw [u] <;> norm_num
    have hpow : ∀ n : ℤ, χ n = χ 1 ^ n := by
      intro n
      refine Int.induction_on n ?_ ?_ ?_
      · simp [h0]
      · intro k ih
        rw [key, ih, zpow_add_one₀ hne, mul_comm]
      · intro k ih
        have h1 := key (-(k : ℤ) - 1)
        rw [show -(k : ℤ) - 1 + 1 = -k by ring, ih] at h1
        rw [zpow_sub_one₀ hne]
        have hinv : (χ 1)⁻¹ = χ 1 := by rcases hχ 1 with u | u <;> rw [u] <;> norm_num
        rw [hinv]
        linear_combination (-(χ 1)) * h1 - (χ (-(k : ℤ) - 1)) * hu
    rcases hχ 1 with u | u
    · left; intro n; rw [hpow, u, one_zpow]
    · right; intro n; rw [hpow, u]

/-- **Lemma `lemma:Phicancellation`.** Let `ABC` be tiled by the tiles `t₁, …, t_N`. Then for
`i = 1, 2`, `Φᵢ(∂ABC) = Σⱼ Φᵢ(tⱼ)`.

The hypothesis `δ/π ∉ ℚ` (`lemma:incommensurable`) makes `Φᵢ(θ + π) = -Φᵢ(θ)`
(`lemma:Phiproperties`), on which the cancellation rests. -/
theorem Phicancellation {N : ℕ} (D : CongruentDissection N) {δ : ℝ}
    (hδ : ¬ ∃ q : ℚ, δ = (q : ℝ) * Real.pi) (θ₀ : Real.Angle) :
    PhiR (Phi1 δ θ₀) D.target = ∑ j, PhiR (Phi1 δ θ₀) (D.tile j) ∧
      PhiR (Phi2 δ θ₀) D.target = ∑ j, PhiR (Phi2 δ θ₀) (D.tile j) := by
  have hodd : ∀ (Φ : Real.Angle → ℝ), (∀ θ : Real.Angle, Φ (θ + Real.pi) = - Φ θ) →
      ∀ d : Dir, (fun d : Dir => Φ d.angle) (Dir.neg d) = - (fun d : Dir => Φ d.angle) d := by
    intro Φ h d
    simp only [Dir.angle_neg]
    exact h _
  have hP := (Phiproperties hδ θ₀).2.1
  exact ⟨(D.flux_cancel _ (hodd _ fun θ => (hP θ).1)).symm,
    (D.flux_cancel _ (hodd _ fun θ => (hP θ).2)).symm⟩

end TriangleTiling.ThreeAlpha
