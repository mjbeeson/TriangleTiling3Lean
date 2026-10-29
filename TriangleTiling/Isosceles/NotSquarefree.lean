/-
"The non-primality of N", from Section 10 of M. Beeson,
*Tilings of an isosceles triangle*.

The paper first shows the tile is rational (`theorem:rationaltile`) and then assumes, after
scaling, that its sides are integers with no common factor. This file proves the theorem in that
case, as `notsquarefree_int`; `TriangleTiling.Isosceles.Scaling` removes the assumption, giving
`notsquarefree` as the paper states it.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`: target `ABC = target.pts 0, 1, 2`
with base `AC`; model tile with angles `α, β, γ` at `model.pts 0, 1, 2` and opposite sides
`a, b, c`.
-/
import TriangleTiling.Isosceles.QandR
import TriangleTiling.Isosceles.NotPrime

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

theorem fin3_add_two_add_one : ∀ k : Fin 3, k + 2 + 1 = k := by decide
theorem fin3_add_two_add_two : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide

/-- In a congruent copy, each corner has the angle and the opposite side of some corner of the
model. -/
theorem congruent_corner_opp {T U : Tri} (h : T.Congruent U) (k : Fin 3) :
    ∃ j : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) =
        cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) ∧
      dist (T.pts (k + 1)) (T.pts (k + 2)) = dist (U.pts (j + 1)) (U.pts (j + 2)) := by
  obtain ⟨σ, hσ⟩ := h.dist_eq
  refine ⟨σ k, ?_, ?_⟩
  · have hang : cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) =
        cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2))) :=
      angle_of_sss (hσ _ _) (hσ _ _) (hσ _ _)
        (T.indep.injective.ne (by fin_cases k <;> decide))
        (T.indep.injective.ne (by fin_cases k <;> decide))
    rw [hang]
    have h1 : σ (k + 1) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h2 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
    generalize σ k = j0 at h1 h2 h12 ⊢
    generalize σ (k + 1) = j1 at h1 h2 h12 ⊢
    generalize σ (k + 2) = j2 at h1 h2 h12 ⊢
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> simp at h1 h2 h12 ⊢ <;>
      first | rfl | exact angle_comm _ _ _
  · rw [hσ]
    have h1 : σ (k + 1) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h2 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
    generalize σ k = j0 at h1 h2 h12 ⊢
    generalize σ (k + 1) = j1 at h1 h2 h12 ⊢
    generalize σ (k + 2) = j2 at h1 h2 h12 ⊢
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> simp at h1 h2 h12 ⊢ <;>
      first | rfl | exact dist_comm _ _

/-- The side of a tile opposite its corner with angle `α`, `β` or `γ` has length `a`, `b` or
`c` respectively. -/
theorem opp_side_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (i : Fin N)
    (k : Fin 3) :
    ((D.tile i).localAngle ((D.tile i).pts k) = tileα D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 1) (D.model.pts 2)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileβ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 2) (D.model.pts 0)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileγ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 0) (D.model.pts 1)) := by
  obtain ⟨-, hinj⟩ := hsep
  obtain ⟨j, hang, hd⟩ := congruent_corner_opp (D.tiles_congruent i) k
  rw [Tri.localAngle_vertex, hang, hd]
  have e0 : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = tileα D := rfl
  have e1 : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = tileβ D := rfl
  have e2 : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = tileγ D := rfl
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  fin_cases j
  · refine ⟨fun _ => rfl, fun h => absurd (e0.symm.trans h) (ne 0 1 (by decide)),
      fun h => absurd (e0.symm.trans h) (ne 0 2 (by decide))⟩
  · refine ⟨fun h => absurd (e1.symm.trans h) (ne 1 0 (by decide)), fun _ => rfl,
      fun h => absurd (e1.symm.trans h) (ne 1 2 (by decide))⟩
  · refine ⟨fun h => absurd (e2.symm.trans h) (ne 2 0 (by decide)),
      fun h => absurd (e2.symm.trans h) (ne 2 1 (by decide)), fun _ => rfl⟩

theorem opp_side {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (i : Fin N) (k : Fin 3) :
    ((D.tile i).localAngle ((D.tile i).pts k) = tileα D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 1) (D.model.pts 2)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileβ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 2) (D.model.pts 0)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileγ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 0) (D.model.pts 1)) :=
  opp_side_sep D (anglesSep_of_two_alpha D hγ hirr) i k

/-- A tile's angle at one of its own vertices is `α`, `β` or `γ`. -/
theorem localAngle_at_own_vertex_mem' {N : ℕ} (D : CongruentDissection N) (i : Fin N)
    (k : Fin 3) :
    (D.tile i).localAngle ((D.tile i).pts k) = tileα D ∨
    (D.tile i).localAngle ((D.tile i).pts k) = tileβ D ∨
    (D.tile i).localAngle ((D.tile i).pts k) = tileγ D := by
  rw [Tri.localAngle_vertex]
  obtain ⟨j, hj, -⟩ := congruent_corner_opp (D.tiles_congruent i) k
  rw [hj]
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **The walk equation of a side, by edge type.** If the tile edges on side `i` are `part`
(as in Bonfioli's `side_walk`), then the side has length `p a + q b + r c`, where `p, q, r`
count the edges opposite an `α`, `β`, `γ` corner. -/
theorem side_walk_counts_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (part : Finset (Fin N × Fin 3))
    (L : ℝ) (hsum : ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) :
    L = ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileα D).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileβ D).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileγ D).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  classical
  obtain ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := ne 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne 1 2 (by decide)
  have hpt : ∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D
        then dist (D.model.pts 1) (D.model.pts 2) else 0)
      + (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D
        then dist (D.model.pts 2) (D.model.pts 0) else 0)
      + (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D
        then dist (D.model.pts 0) (D.model.pts 1) else 0) := by
    intro e _
    have hsides := opp_side_sep D ⟨hv0, hinj⟩ e.1 (e.2 + 2)
    have e3 : e.2 + 2 + 1 = e.2 := fin3_add_two_add_one e.2
    have e4 : e.2 + 2 + 2 = e.2 + 1 := fin3_add_two_add_two e.2
    rw [e3, e4] at hsides
    have hmem := localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)
    rcases hmem with h | h | h
    · rw [if_pos h, if_neg (h ▸ hαβ), if_neg (h ▸ hαγ), hsides.1 h]; ring
    · rw [if_neg (h ▸ hαβ.symm), if_pos h, if_neg (h ▸ hβγ), hsides.2.1 h]; ring
    · rw [if_neg (h ▸ hαγ.symm), if_neg (h ▸ hβγ.symm), if_pos h, hsides.2.2 h]; ring
  rw [← hsum, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]

theorem side_walk_counts {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (part : Finset (Fin N × Fin 3))
    (L : ℝ) (hsum : ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) :
    L = ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileα D).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileβ D).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileγ D).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) :=
  side_walk_counts_sep D (anglesSep_of_two_alpha D hγ hirr) part L hsum

/-- A tile's corner angle at `kB` is the angle at `kB` between its other two vertices. -/
theorem corner_eq_of_two (T : Tri) (kB a₁ a₂ : Fin 3) (h₁ : a₁ ≠ kB) (h₂ : a₂ ≠ kB)
    (h₁₂ : a₁ ≠ a₂) :
    cornerAngle (T.pts (kB + 1)) (T.pts kB) (T.pts (kB + 2)) = ∠ (T.pts a₁) (T.pts kB) (T.pts a₂) := by
  fin_cases kB <;> fin_cases a₁ <;> fin_cases a₂ <;> simp at h₁ h₂ h₁₂ ⊢ <;>
    first | rfl | exact angle_comm _ _ _

/-- An edge with endpoint `B`: `B` is a vertex `kB` of the tile and the other endpoint is a
different vertex `a`. -/
theorem edge_endpoint (T : Tri) (j : Fin 3) {B : Plane}
    (h : T.pts j = B ∨ T.pts (j + 1) = B) :
    ∃ kB a : Fin 3, T.pts kB = B ∧ a ≠ kB ∧ T.pts a ∈ T.edge j := by
  rcases h with h | h
  · exact ⟨j, j + 1, h, (fin3_ne_add_one j).symm, right_mem_segment _ _ _⟩
  · exact ⟨j + 1, j, h, fin3_ne_add_one j, left_mem_segment _ _ _⟩

/-- **The apex.** At `B` one of the two equal sides has its tile at `B` without its `β` angle
there. (The paper says: renaming `A` and `C` if necessary, the tile with its `α` angle at `B` is
supported by `AB`.) Otherwise the single tile with its `β` angle at `B` would have edges along
both `BA` and `BC`, so its angle at `B` would be the whole angle `π - 2α` of `ABC`. -/
theorem beta_at_apex {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
    (part₀ part₁ : Finset (Fin N × Fin 3))
    (hcov₀ : (⋃ e ∈ part₀, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hcov₁ : (⋃ e ∈ part₁, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 1) (D.target.pts 2)) :
    (∀ e ∈ part₀, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        (D.tile e.1).localAngle (D.target.pts 1) ≠ tileβ D) ∨
    (∀ e ∈ part₁, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        (D.tile e.1).localAngle (D.target.pts 1) ≠ tileβ D) := by
  classical
  obtain ⟨hβ, -, -⟩ := angle_values D hγ hirr
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨e₁, he₁, hend₁, hβ₁⟩, ⟨e₂, he₂, hend₂, hβ₂⟩⟩ := hcon
  set B := D.target.pts 1
  -- The angle of `ABC` at `B` is `π - 2α`.
  have hTsum := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  have hBang : ∠ (D.target.pts 0) B (D.target.pts 2) = Real.pi - 2 * tileα D := by
    have : cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) =
        Real.pi - 2 * tileα D := by linarith
    rw [cornerAngle, angle_comm] at this; exact this
  -- Only one tile has its `β` angle at `B`.
  have hlocB : D.target.localAngle B = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  have rB := vertex_relations D hγ hirr _ (-2) 1 hlocB
  have hcnt : angleCount D B (tileβ D) ≤ 1 := by omega
  have hsame : e₁.1 = e₂.1 := by
    have := Finset.card_le_one.mp hcnt e₁.1 (by simp [hβ₁]) e₂.1 (by simp [hβ₂])
    exact this
  set t := D.tile e₁.1
  obtain ⟨kB, a₁, hkB, ha₁, hP⟩ := edge_endpoint t e₁.2 hend₁
  obtain ⟨kB', a₂, hkB', ha₂, hQ⟩ := edge_endpoint (D.tile e₂.1) e₂.2 hend₂
  rw [← hsame] at hkB' hQ
  have hkk : kB' = kB := t.indep.injective (hkB'.trans hkB.symm)
  rw [hkk] at ha₂
  -- `P = t.pts a₁` lies on `BA`, `Q = t.pts a₂` lies on `BC`.
  have hPseg : t.pts a₁ ∈ segment ℝ (D.target.pts 0) B := by
    rw [← hcov₀]; exact Set.mem_biUnion he₁ hP
  have hQseg : t.pts a₂ ∈ segment ℝ B (D.target.pts 2) := by
    rw [← hcov₁]; exact Set.mem_biUnion he₂ (hsame ▸ hQ)
  have hPB : t.pts a₁ ≠ B := fun h => ha₁ (t.indep.injective (h.trans hkB.symm))
  have hQB : t.pts a₂ ≠ B := fun h => ha₂ (t.indep.injective (h.trans hkB.symm))
  have hang : ∠ (t.pts a₁) B (t.pts a₂) = Real.pi - 2 * tileα D := by
    rw [(mem_segment_iff_wbtw.mp hPseg).symm.angle_eq_left _ hPB,
      (mem_segment_iff_wbtw.mp hQseg).angle_eq_right _ hQB, hBang]
  by_cases h12 : a₁ = a₂
  · -- `P = Q` would make the angle at `B` zero, so `α = π / 2`.
    subst h12
    rw [angle_self_of_ne hPB] at hang
    exact hirr ⟨1 / 2, by push_cast; linarith⟩
  · -- Otherwise `t` has angle `π - 2α` at `B`; but that angle is `β = π - 3α`.
    have hcorner := corner_eq_of_two t kB a₁ a₂ ha₁ ha₂ h12
    rw [hkB, hang] at hcorner
    have : t.localAngle B = Real.pi - 2 * tileα D := by
      rw [← hkB, Tri.localAngle_vertex, hkB]; exact hcorner
    rw [this, hβ] at hβ₁
    exact hirr ⟨0, by push_cast; linarith⟩

/-- The arithmetic of `theorem:notsquarefree`. With `b = m² - k² = N ℓ²`, a side relation
`N k ℓ = p k² + q b + r k m` with `q ≥ 1` and `r ≥ 1` is impossible: reducing mod `k` gives
`k ∣ q`, so `ℓ q b ≥ k b = ℓ (N k ℓ)`, leaving no room for `r k m > 0`. -/
theorem notsquarefree_arith (N k m ℓ p q r : ℕ) (hk : 0 < k) (hkm : k < m)
    (hcop : Nat.Coprime k m) (hb : N * ℓ ^ 2 = m ^ 2 - k ^ 2)
    (hX : N * k * ℓ = p * k ^ 2 + q * (m ^ 2 - k ^ 2) + r * (k * m)) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    False := by
  set b := m ^ 2 - k ^ 2 with hbdef
  have hk2m2 : k ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hkm two_ne_zero
  have hbm : b + k ^ 2 = m ^ 2 := by omega
  have hb0 : 0 < b := by omega
  have hℓ : 0 < ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · rw [h] at hb; simp at hb; omega
    · exact h
  -- `k ∣ q`.
  have hkq : k ∣ q := by
    have h1 : k ∣ q * b := by
      have h2 : k ∣ N * k * ℓ := ⟨N * ℓ, by ring⟩
      rw [hX, show p * k ^ 2 + q * b + r * (k * m) = (p * k ^ 2 + r * (k * m)) + q * b by ring]
        at h2
      exact (Nat.dvd_add_right ⟨p * k + r * m, by ring⟩).mp h2
    have h3 : k ∣ q * m ^ 2 := by
      rw [← hbm, mul_add]
      exact Nat.dvd_add h1 ⟨q * k, by ring⟩
    exact (Nat.Coprime.pow_right 2 hcop).dvd_of_dvd_mul_right h3
  have hqk : k ≤ q := Nat.le_of_dvd (by omega) hkq
  -- `k b = ℓ p k² + ℓ q b + ℓ r k m`, but `ℓ q b ≥ k b`.
  have hkb : k * b = ℓ * (p * k ^ 2) + ℓ * q * b + ℓ * r * (k * m) := by
    have : ℓ * (N * k * ℓ) = k * b := by rw [← hb]; ring
    rw [← this, hX]; ring
  have hge : k * b ≤ ℓ * q * b :=
    Nat.mul_le_mul_right b (le_trans hqk (Nat.le_mul_of_pos_left q hℓ))
  have hpos : 0 < ℓ * r * (k * m) :=
    Nat.mul_pos (Nat.mul_pos hℓ (by omega)) (Nat.mul_pos hk (by omega))
  omega

/-- **Theorem `theorem:notsquarefree`, for a tile with integer sides** (the general form is
`notsquarefree`). Let `ABC` be isosceles
with base angles `α`, `α` not a rational multiple of `π`, and `N`-tiled by a tile with angles
`(α, β, 2α)` and integer sides `(a, b, c)` with no common factor. Then `N` is not squarefree;
in particular `N` is not prime.

The paper proves the tile is rational (`theorem:rationaltile`) and then scales to integer sides;
that step needs the graphs `Γ` and is not yet formalized. The proof is the paper's: by
`lemma:notprimehelper`, `b = N ℓ²` and `|AB| = N k ℓ`; the side `AB` (or `BC`, for which the
paper renames `A` and `C`) gives `N k ℓ = p k² + q b + r k m` with `q, r ≥ 1`
(`lemma:qandrnotzero`), which is impossible. -/
theorem notsquarefree_int {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    ¬ Squarefree N := by
  classical
  intro hsq
  obtain ⟨-, hv0, hinj⟩ := angle_values D hγ hirr
  obtain ⟨ℓ, hbℓ⟩ := (notprimehelper D ha hb hc hcop hγ hA hC).2 hsq
  obtain ⟨hBC, -, hX2⟩ := areaequation_core D ha hb hc rfl rfl hγ hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1) with hXdef
  -- The tile as `(k², m² - k², km)` (`lemma:luthar`).
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  have m1' : a < b + c := by exact_mod_cast m1
  have m2' : b < c + a := by exact_mod_cast m2
  have m3' : c < a + b := by exact_mod_cast m3
  obtain ⟨k, m, hkm_cop, hkm, -, hak, hbk, hck⟩ :=
    (luthar a b c).mp ⟨hcop, hcab, m1', by omega, m3'⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hak; simp at hak; omega
    · exact h
  -- `X = N k ℓ`.
  have hX : X = (N * k * ℓ : ℕ) := by
    have hX0 : 0 ≤ X := dist_nonneg
    have hsq' : X ^ 2 = ((N * k * ℓ : ℕ) : ℝ) ^ 2 := by
      rw [hX2]
      have : (a : ℝ) * b = (k : ℝ) ^ 2 * (N * ℓ ^ 2) := by
        rw [hak, hbℓ]; push_cast; ring
      push_cast
      linear_combination (N : ℝ) * this
    exact (sq_eq_sq₀ hX0 (by positivity)).mp hsq'
  -- The angle counts at the corners.
  have hTsum := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  have hloc0 : D.target.localAngle (D.target.pts 0) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    push_cast; linarith
  have hloc1 : D.target.localAngle (D.target.pts 1) = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  have hloc2 : D.target.localAngle (D.target.pts 2) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    push_cast; linarith
  have r0 := vertex_relations D hγ hirr _ 1 0 hloc0
  have r1 := vertex_relations D hγ hirr _ (-2) 1 hloc1
  have r2 := vertex_relations D hγ hirr _ 1 0 hloc2
  have none : ∀ (P : Plane) (θ : ℝ), angleCount D P θ = 0 →
      ∀ i, (D.tile i).localAngle P ≠ θ := by
    intro P θ h i hi
    have : i ∈ Finset.univ.filter fun i => (D.tile i).localAngle P = θ := by simp [hi]
    rw [angleCount, Finset.card_eq_zero] at h
    rw [h] at this
    simp at this
  have hβ0 : angleCount D (D.target.pts 0) (tileβ D) = 0 := by omega
  have hγ0 : angleCount D (D.target.pts 0) (tileγ D) = 0 := by omega
  have hβ2 : angleCount D (D.target.pts 2) (tileβ D) = 0 := by omega
  have hγ2 : angleCount D (D.target.pts 2) (tileγ D) = 0 := by omega
  have hγ1 : angleCount D (D.target.pts 1) (tileγ D) = 0 := by
    have : angleCount D (D.target.pts 1) (tileβ D) ≤ 1 := by omega
    interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega
  -- The two equal sides, as chains of tile edges.
  obtain ⟨part₀, hcov₀, hdisj₀, hsum₀⟩ := D.toDissection.side_walk 0
  obtain ⟨part₁, hcov₁, hdisj₁, hsum₁⟩ := D.toDissection.side_walk 1
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  have h12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [h01] at hcov₀ hsum₀
  rw [h12] at hcov₁ hsum₁
  -- On a side with `q, r ≥ 1`, the arithmetic fails.
  have finish : ∀ (part : Finset (Fin N × Fin 3)),
      (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = X) →
      (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D) →
      (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D) → False := by
    intro part hsum ⟨eq, hq, hqβ⟩ ⟨er, hr, hrγ⟩
    have hw := side_walk_counts D hγ hirr part X hsum
    rw [ha, hb, hc, hX] at hw
    set p := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileα D).card
    set q := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileβ D).card
    set r := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D).card
    have hq1 : 1 ≤ q := Finset.card_pos.mpr ⟨eq, Finset.mem_filter.mpr ⟨hq, hqβ⟩⟩
    have hr1 : 1 ≤ r := Finset.card_pos.mpr ⟨er, Finset.mem_filter.mpr ⟨hr, hrγ⟩⟩
    have hwn : N * k * ℓ = p * a + q * b + r * c := by exact_mod_cast hw
    rw [hak, hbk, hck] at hwn
    rw [hbk] at hbℓ
    exact notsquarefree_arith N k m ℓ p q r hk0 hkm hkm_cop hbℓ.symm
      hwn hq1 hr1
  have htb := fun P (hP : P ∈ frontier D.target.carrier) => twobeta D hγ hirr hA hC hP
  rcases beta_at_apex D hγ hirr hA hC part₀ part₁ hcov₀ hcov₁ with hB | hB
  · -- Side `AB`.
    have hfr : ∀ P ∈ segment ℝ (D.target.pts 0) (D.target.pts 1),
        P ∈ frontier D.target.carrier := fun P hP => tri_side_subset_frontier D.target 0 hP
    refine finish part₀ hsum₀ ?_ ?_
    · exact side_has_edge D hγ hirr _ (Or.inl rfl) 0 part₀ hcov₀ hdisj₀
        (fun e _ _ => none _ _ hβ0 e.1) hB (fun P hP => (htb P (hfr P hP)).1)
    · exact side_has_edge D hγ hirr _ (Or.inr rfl) 0 part₀ hcov₀ hdisj₀
        (fun e _ _ => none _ _ hγ0 e.1) (fun e _ _ => none _ _ hγ1 e.1)
        (fun P hP => (htb P (hfr P hP)).2)
  · -- Side `BC`, of the same length.
    have hfr : ∀ P ∈ segment ℝ (D.target.pts 1) (D.target.pts 2),
        P ∈ frontier D.target.carrier := fun P hP => tri_side_subset_frontier D.target 1 hP
    refine finish part₁ (hsum₁.trans hBC) ?_ ?_
    · exact side_has_edge D hγ hirr _ (Or.inl rfl) 1 part₁ hcov₁ hdisj₁ hB
        (fun e _ _ => none _ _ hβ2 e.1) (fun P hP => (htb P (hfr P hP)).1)
    · exact side_has_edge D hγ hirr _ (Or.inr rfl) 1 part₁ hcov₁ hdisj₁
        (fun e _ _ => none _ _ hγ1 e.1) (fun e _ _ => none _ _ hγ2 e.1)
        (fun P hP => (htb P (hfr P hP)).2)

end TriangleTiling
