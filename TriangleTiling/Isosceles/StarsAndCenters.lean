/-
"Stars and centers", from Section 10 of M. Beeson, *Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:starsandcenters` is `starsandcenters`.

The paper classifies a vertex of the tiling by how many tiles have their `α`, `β`, `γ` angles
there. Here `vertexType D P = (#α, #β, #γ)` at `P`, counted with Bonfioli's `Tri.localAngle`.
With `γ = 2α` and `α ∉ ℚπ` the possible types are

* angle sum `π`: normal boundary vertex `(1,1,1)`, star `(3,1,0)`;
* angle sum `2π`: normal interior vertex `(2,2,2)`, center `(0,2,3)`,
  single interior star `(4,2,1)`, double interior star `(6,2,0)`.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`: target `ABC = target.pts 0, 1, 2`
with base `AC`; model tile with angles `α, β, γ` at `model.pts 0, 1, 2`.
-/
import TriangleTiling.Isosceles.TwoBeta
import Mathlib.Analysis.Normed.Affine.MazurUlam

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

section Defs

variable {N : ℕ} (D : CongruentDissection N)

/-- The angle `α` of the model tile, at `model.pts 0`. -/
noncomputable def tileα : ℝ := ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)
/-- The angle `β` of the model tile, at `model.pts 1`. -/
noncomputable def tileβ : ℝ := ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)
/-- The angle `γ` of the model tile, at `model.pts 2`. -/
noncomputable def tileγ : ℝ := ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)

/-- The number of tiles whose local angle at `P` is `θ`. -/
noncomputable def angleCount (P : Plane) (θ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => (D.tile i).localAngle P = θ).card

open Classical in
/-- The vertices of the tiling: all vertices of all tiles. -/
noncomputable def tilingVertices : Finset Plane :=
  Finset.univ.image fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2

/-- The type of a vertex: how many tiles have their `α`, `β`, `γ` angles there. -/
noncomputable def vertexType (P : Plane) : ℕ × ℕ × ℕ :=
  (angleCount D P (tileα D), angleCount D P (tileβ D), angleCount D P (tileγ D))

open Classical in
/-- The number of vertices of the tiling, other than `A`, `B`, `C`, of type `t`. -/
noncomputable def typeCount (t : ℕ × ℕ × ℕ) : ℕ :=
  ((tilingVertices D).filter fun P => P ∉ Set.range D.target.pts ∧ vertexType D P = t).card

end Defs

/-- Companion of `sum_eq_counts`: the number of terms is the sum of the value counts plus the
number of zeros. -/
theorem card_eq_counts {ι : Type*} [Fintype ι] [DecidableEq ℝ] (f : ι → ℝ) (v : Fin 5 → ℝ)
    (hv0 : ∀ j, v j ≠ 0) (hinj : Function.Injective v)
    (hf : ∀ i, (∃ j, f i = v j) ∨ f i = 0) :
    Fintype.card ι = ∑ j, (Finset.univ.filter fun i => f i = v j).card
      + (Finset.univ.filter fun i => f i = 0).card := by
  have hpt : ∀ i, (1 : ℕ) = (∑ j, if f i = v j then 1 else 0) + if f i = 0 then 1 else 0 := by
    intro i
    rcases hf i with ⟨j, hj⟩ | h0
    · rw [Finset.sum_eq_single j, if_pos hj, if_neg (by rw [hj]; exact hv0 j)]
      · intro k _ hkj; rw [if_neg]; rw [hj]; exact fun h => hkj (hinj h).symm
      · simp
    · rw [Finset.sum_eq_zero, if_pos h0]
      intro k _; rw [if_neg (fun h => hv0 k (h.symm.trans h0))]
  rw [← Finset.card_univ, Finset.card_eq_sum_ones, Finset.sum_congr rfl (fun i _ => hpt i),
    Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  · rw [Finset.card_filter]

/-- The angle facts used throughout: with `γ = 2α` and `α ∉ ℚπ`, the values
`α, β, γ, π, 2π` are distinct and nonzero, and `β = π - 3α`. -/
theorem angle_values {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) :
    tileβ D = Real.pi - 3 * tileα D ∧
    (∀ j, ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j ≠ 0) ∧
    Function.Injective ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] := by
  set α := tileα D
  set β := tileβ D
  set γ := tileγ D
  have hsum3 : α + β + γ = Real.pi := cornerAngle_sum D.model
  have hβ : β = Real.pi - 3 * α := by linarith
  have hne : ∀ p q : ℤ, p ≠ 0 → (p : ℝ) * α ≠ q * Real.pi := by
    intro p q hp h
    exact hp (angle_indep hirr p (-q) (by push_cast; linarith)).1
  have hpi := Real.pi_pos
  refine ⟨hβ, ?_, ?_⟩
  · intro j; fin_cases j
    · exact fun h => hne 1 0 one_ne_zero (by simp at h ⊢; linarith)
    · exact fun h => hne 3 1 (by norm_num) (by simp at h; push_cast; linarith)
    · exact fun h => hne 1 0 one_ne_zero (by simp at h; push_cast; linarith)
    · simp [hpi.ne']
    · simp [hpi.ne']
  · intro j k hjk
    fin_cases j <;> fin_cases k <;> simp at hjk ⊢
    all_goals first
      | exact hne 4 1 (by norm_num) (by push_cast; linarith)
      | exact hne 1 0 one_ne_zero (by push_cast; linarith)
      | exact hne 1 1 one_ne_zero (by push_cast; linarith)
      | exact hne 1 2 one_ne_zero (by push_cast; linarith)
      | exact hne 5 1 (by norm_num) (by push_cast; linarith)
      | exact hne 3 (-1) (by norm_num) (by push_cast; linarith)
      | exact hne 2 1 (by norm_num) (by push_cast; linarith)

/-- The arithmetic behind every vertex count: with `β = π - 3α`, `γ = 2α` and `α ∉ ℚπ`, a
relation `n₀ α + n₁ β + n₂ γ + n₃ π + n₄ (2π) = s α + t π` forces `n₀ - 3n₁ + 2n₂ = s` and
`n₁ + n₃ + 2n₄ = t`. -/
theorem counts_arith {α β γ : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hβ : β = Real.pi - 3 * α) (hγ : γ = 2 * α) (n₀ n₁ n₂ n₃ n₄ : ℕ) (s t : ℤ)
    (h : (n₀ : ℝ) * α + n₁ * β + n₂ * γ + n₃ * Real.pi + n₄ * (2 * Real.pi) = s * α + t * Real.pi) :
    (n₀ : ℤ) - 3 * n₁ + 2 * n₂ = s ∧ (n₁ : ℤ) + n₃ + 2 * n₄ = t := by
  subst hβ hγ
  have key : (((n₀ : ℤ) - 3 * n₁ + 2 * n₂ - s : ℤ) : ℝ) * α
      + (((n₁ : ℤ) + n₃ + 2 * n₄ - t : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linear_combination h
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega

/-- **The vertex relations.** At any point `P`, if the target's local angle there is
`s α + t π`, then the counts `n₀, …, n₄` of tiles with local angle `α, β, γ, π, 2π` at `P`
satisfy `n₀ - 3n₁ + 2n₂ = s` and `n₁ + n₃ + 2n₄ = t`. -/
theorem vertex_relations {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (P : Plane) (s t : ℤ)
    (hP : D.target.localAngle P = s * tileα D + t * Real.pi) :
    ((angleCount D P (tileα D) : ℤ) - 3 * angleCount D P (tileβ D)
        + 2 * angleCount D P (tileγ D) = s) ∧
    ((angleCount D P (tileβ D) : ℤ) + angleCount D P Real.pi
        + 2 * angleCount D P (2 * Real.pi) = t) := by
  obtain ⟨hβ, hv0, hinj⟩ := angle_values D hγ hirr
  have hf : ∀ i, (∃ j, (D.tile i).localAngle P =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ (D.tile i).localAngle P = 0 := by
    intro i
    rcases localAngle_mem D P i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle P) _ hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five, hP] at hcount
  have hcount' : (angleCount D P (tileα D) : ℝ) * tileα D
      + (angleCount D P (tileβ D) : ℝ) * tileβ D + (angleCount D P (tileγ D) : ℝ) * tileγ D
      + (angleCount D P Real.pi : ℝ) * Real.pi
      + (angleCount D P (2 * Real.pi) : ℝ) * (2 * Real.pi) = s * tileα D + t * Real.pi :=
    hcount.symm
  exact counts_arith hirr hβ hγ _ _ _ _ _ s t hcount'

/-- The local angle of the target at its corners: `α` at `A` and `C`, `π - 2α` at `B`. -/
theorem target_corner_angle {N : ℕ} (D : CongruentDissection N)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) (k : Fin 3) :
    ∃ s t : ℤ, ((s = 1 ∧ t = 0) ∨ (s = -2 ∧ t = 1)) ∧
      D.target.localAngle (D.target.pts k) = s * tileα D + t * Real.pi := by
  rw [Tri.localAngle_vertex]
  have hT := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  fin_cases k
  · refine ⟨1, 0, Or.inl ⟨rfl, rfl⟩, ?_⟩
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    push_cast; linarith
  · refine ⟨-2, 1, Or.inr ⟨rfl, rfl⟩, ?_⟩
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  · refine ⟨1, 0, Or.inl ⟨rfl, rfl⟩, ?_⟩
    show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    push_cast; linarith

/-- The values `α, β, γ, π, 2π` are distinct and nonzero (true for every tile considered here:
`γ = 2α` with `α ∉ ℚπ`, and the right-angled tiles with `α ∉ ℚπ`). -/
def AnglesSep {N : ℕ} (D : CongruentDissection N) : Prop :=
  (∀ j, ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j ≠ 0) ∧
    Function.Injective ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi]

theorem anglesSep_of_two_alpha {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) : AnglesSep D :=
  ⟨(angle_values D hγ hirr).2.1, (angle_values D hγ hirr).2.2⟩

/-- **Congruent triangles match corner angles under one permutation** (as in Bonfioli's
`Tri.Congruent.cornerAngle_perm`). -/
theorem corner_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ, fun k => ?_⟩
  have hmap : cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2)))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
    rw [← hf (k + 1), ← hf k, ← hf (k + 2)]
    rw [Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  have hidx : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  have hne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hne k
  rcases hidx (σ k) (σ (k + 1)) (σ (k + 2))
      (fun he => h1 (σ.injective he)) (fun he => h2 (σ.injective he))
      (fun he => h12 (σ.injective he)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact hmap
  · rw [← ha, ← hb]
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact hmap

/-- **Each tile has exactly one corner of each model angle**, when those angles are distinct (as in
Bonfioli's `Tri.Congruent.corner_count_eq_one`). -/
theorem tile_angle_count_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (i : Fin N) :
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileα D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileβ D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileγ D).card = 1 := by
  classical
  obtain ⟨σ, hperm⟩ := corner_perm (D.tiles_congruent i).symm
  set M := D.model
  have hm : ∀ k : Fin 3, cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2)) =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] (k.castLE (by norm_num)) := by
    intro k; fin_cases k <;> rfl
  have hdist : ∀ k l : Fin 3, cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2))
      = cornerAngle (M.pts (l + 1)) (M.pts l) (M.pts (l + 2)) → k = l := by
    intro k l h
    rw [hm, hm] at h
    exact Fin.castLE_injective _ (hsep.2 h)
  have hcount : ∀ k : Fin 3, (Finset.univ.filter fun j : Fin 3 =>
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        = cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2))).card = 1 := by
    intro k
    refine Finset.card_eq_one.mpr ⟨σ k, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      have h' := hperm (σ.symm j)
      rw [Equiv.apply_symm_apply] at h'
      have := hdist _ _ (h'.symm.trans hj)
      rw [← this, Equiv.apply_symm_apply]
    · intro hj; subst hj; exact hperm k
  exact ⟨hcount 0, hcount 1, hcount 2⟩

/-- Each tile has exactly one vertex with angle `α`, one with angle `β`, and one with angle `γ`. -/
theorem tile_angle_count {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (i : Fin N) :
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileα D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileβ D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileγ D).card = 1 := by
  obtain ⟨hβ, hv0, hinj⟩ := angle_values D hγ hirr
  set g := fun k : Fin 3 =>
    cornerAngle ((D.tile i).pts (k + 1)) ((D.tile i).pts k) ((D.tile i).pts (k + 2)) with hg
  have hgv : ∀ k, ∃ j, g k = ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j := by
    intro k
    obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm k
    refine ⟨k'.castLE (by norm_num), ?_⟩
    rw [hg]; simp only; rw [hk']
    fin_cases k' <;> rfl
  have hf : ∀ k, (∃ j, g k = ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ g k = 0 :=
    fun k => Or.inl (hgv k)
  have hsum := sum_eq_counts g _ hv0 hinj hf
  have hcard := card_eq_counts g _ hv0 hinj hf
  have h0 : (Finset.univ.filter fun k => g k = 0).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ hk
    obtain ⟨j, hj⟩ := hgv k
    exact hv0 j (hj ▸ hk)
  have hπ : ∑ k, g k = Real.pi := by
    rw [Fin.sum_univ_three]; exact cornerAngle_sum (D.tile i)
  rw [hπ, Fin.sum_univ_five] at hsum
  rw [Fin.sum_univ_five, h0, Fintype.card_fin] at hcard
  have hsum' : ((Finset.univ.filter fun k => g k = tileα D).card : ℝ) * tileα D
      + ((Finset.univ.filter fun k => g k = tileβ D).card : ℝ) * tileβ D
      + ((Finset.univ.filter fun k => g k = tileγ D).card : ℝ) * tileγ D
      + ((Finset.univ.filter fun k => g k = Real.pi).card : ℝ) * Real.pi
      + ((Finset.univ.filter fun k => g k = 2 * Real.pi).card : ℝ) * (2 * Real.pi)
      = Real.pi := hsum.symm
  have hcard' : 3 = (Finset.univ.filter fun k => g k = tileα D).card
      + (Finset.univ.filter fun k => g k = tileβ D).card
      + (Finset.univ.filter fun k => g k = tileγ D).card
      + (Finset.univ.filter fun k => g k = Real.pi).card
      + (Finset.univ.filter fun k => g k = 2 * Real.pi).card + 0 := hcard
  show (Finset.univ.filter fun k => g k = tileα D).card = 1 ∧
    (Finset.univ.filter fun k => g k = tileβ D).card = 1 ∧
    (Finset.univ.filter fun k => g k = tileγ D).card = 1
  clear hsum hcard
  generalize (Finset.univ.filter fun k => g k = tileα D).card = A at hsum' hcard' ⊢
  generalize (Finset.univ.filter fun k => g k = tileβ D).card = B at hsum' hcard' ⊢
  generalize (Finset.univ.filter fun k => g k = tileγ D).card = C at hsum' hcard' ⊢
  generalize (Finset.univ.filter fun k => g k = Real.pi).card = E at hsum' hcard'
  generalize (Finset.univ.filter fun k => g k = 2 * Real.pi).card = F at hsum' hcard'
  have hr := counts_arith hirr hβ hγ A B C E F 0 1 (by rw [hsum']; norm_num)
  obtain ⟨hr1, hr2⟩ := hr
  have hB : B ≤ 1 := by omega
  interval_cases B <;> omega

/-- For a value `θ` that is not `0`, `π` or `2π`, the points of `W` (containing all vertices of
tile `T`) where `T` has local angle `θ` are the vertices of `T` with corner angle `θ`. -/
theorem filter_localAngle_eq [DecidableEq Plane] (T : Tri) (W : Finset Plane)
    (hW : ∀ k, T.pts k ∈ W) (θ : ℝ) (h0 : θ ≠ 0) (hπ : θ ≠ Real.pi) (h2π : θ ≠ 2 * Real.pi) :
    W.filter (fun v => T.localAngle v = θ) =
      (Finset.univ.filter fun k : Fin 3 =>
        cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = θ).image T.pts := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩
    rcases Erdos634.PinPlumbing.localAngle_cases T v with ⟨j, hv, hval⟩ | h' | h' | h'
    · exact ⟨j, hval ▸ h, hv.symm⟩
    · exact absurd (h ▸ h') h2π
    · exact absurd (h ▸ h') hπ
    · exact absurd (h ▸ h') h0
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hW k, by rw [Tri.localAngle_vertex]; exact hk⟩

/-- Summed over a set of points containing all tile vertices, the number of `α` angles (or
`γ` angles) is `N`: each tile has exactly one. -/
theorem sum_angleCount [DecidableEq Plane] {N : ℕ} (D : CongruentDissection N)
    (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (W : Finset Plane) (hW : ∀ i k, (D.tile i).pts k ∈ W) (θ : ℝ)
    (hθ : θ = tileα D ∨ θ = tileγ D) :
    ∑ v ∈ W, angleCount D v θ = N := by
  obtain ⟨-, hv0, hinj⟩ := angle_values D hγ hirr
  have hθ0 : θ ≠ 0 ∧ θ ≠ Real.pi ∧ θ ≠ 2 * Real.pi := by
    rcases hθ with rfl | rfl
    · exact ⟨hv0 0, fun h => hinj.ne (show (0 : Fin 5) ≠ 3 by decide) h,
        fun h => hinj.ne (show (0 : Fin 5) ≠ 4 by decide) h⟩
    · exact ⟨hv0 2, fun h => hinj.ne (show (2 : Fin 5) ≠ 3 by decide) h,
        fun h => hinj.ne (show (2 : Fin 5) ≠ 4 by decide) h⟩
  simp only [angleCount, Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, (∑ v ∈ W, if (D.tile i).localAngle v = θ then 1 else 0) = 1 := by
    intro i
    rw [← Finset.card_filter, filter_localAngle_eq (D.tile i) W (hW i) θ hθ0.1 hθ0.2.1 hθ0.2.2,
      Finset.card_image_of_injective _ (D.tile i).indep.injective]
    rcases hθ with rfl | rfl
    · exact (tile_angle_count D hγ hirr i).1
    · exact (tile_angle_count D hγ hirr i).2.2
  rw [Finset.sum_congr rfl fun i _ => this i]
  simp

/-- **Lemma `lemma:starsandcenters`.** Let the isosceles triangle `ABC` with base angles `α`
be tiled by a tile with angles `(α, β, 2α)`, `α` not a rational multiple of `π`. Let `𝒞` be
the number of centers and `𝒮` the number of stars, counting double interior stars twice. Then
`𝒮 + 1 = 𝒞`. In particular there is at least one center.

Here a star is a vertex of type `(3,1,0)` (angle sum `π`), a single interior star has type
`(4,2,1)`, a double interior star `(6,2,0)`, and a center `(0,2,3)`; the vertices `A, B, C`
are not counted. The proof is the paper's excess count, with the weight `#α - #γ`: it is `3`
at a star, `-3` at a center, `3` and `6` at single and double interior stars, `0` at normal
vertices, and `1` at each of `A, B, C`; summed over all vertices it is `N - N = 0`. -/
theorem starsandcenters {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    typeCount D (0, 2, 3) = typeCount D (3, 1, 0) + typeCount D (4, 2, 1)
      + 2 * typeCount D (6, 2, 0) + 1 := by
  classical
  set TV := tilingVertices D
  set Cn : Finset Plane := Finset.univ.image D.target.pts
  set W := TV ∪ Cn with hWdef
  have hTV : ∀ i k, (D.tile i).pts k ∈ TV := fun i k =>
    Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩
  have hW : ∀ i k, (D.tile i).pts k ∈ W := fun i k => Finset.mem_union_left _ (hTV i k)
  -- The weight `#α - #γ` sums to `N - N = 0` over `W`.
  have hzero : ∑ v ∈ W, ((angleCount D v (tileα D) : ℤ) - angleCount D v (tileγ D)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 := sum_angleCount D hγ hirr W hW (tileα D) (Or.inl rfl)
    have h2 := sum_angleCount D hγ hirr W hW (tileγ D) (Or.inr rfl)
    have e1 : ∑ v ∈ W, (angleCount D v (tileα D) : ℤ) = N := by exact_mod_cast h1
    have e2 : ∑ v ∈ W, (angleCount D v (tileγ D) : ℤ) = N := by exact_mod_cast h2
    rw [e1, e2, sub_self]
  -- Split `W` into the corners and the rest.
  rw [← Finset.sum_filter_add_sum_filter_not W (fun v => v ∈ Set.range D.target.pts)] at hzero
  have hcorners : W.filter (fun v => v ∈ Set.range D.target.pts) = Cn := by
    ext v
    simp only [Finset.mem_filter, hWdef, Finset.mem_union, Cn, Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨Or.inr h, h⟩
  -- At each corner the weight is `1`.
  have hcornerw : ∀ v ∈ Cn,
      (angleCount D v (tileα D) : ℤ) - angleCount D v (tileγ D) = 1 := by
    intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨s, t, hst, hk⟩ := target_corner_angle D hA hC k
    have := vertex_relations D hγ hirr _ s t hk
    omega
  rw [hcorners, Finset.sum_congr rfl hcornerw, Finset.sum_const,
    Finset.card_image_of_injective _ D.target.indep.injective] at hzero
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hzero
  -- Away from the corners the weight is `3 · wt`.
  set R := W.filter (fun v => ¬ v ∈ Set.range D.target.pts) with hR
  let wt : Plane → ℤ := fun v =>
    (if vertexType D v = (3, 1, 0) then 1 else 0) + (if vertexType D v = (4, 2, 1) then 1 else 0)
    + (if vertexType D v = (6, 2, 0) then 2 else 0) - (if vertexType D v = (0, 2, 3) then 1 else 0)
  have hrest : ∀ v ∈ R,
      (angleCount D v (tileα D) : ℤ) - angleCount D v (tileγ D) = 3 * wt v := by
    intro v hv
    obtain ⟨hvW, hvc⟩ := Finset.mem_filter.mp hv
    -- `v` is a tile vertex, hence in the target, hence interior (`2π`) or on a side (`π`).
    have hvTV : v ∈ TV := by
      rcases Finset.mem_union.mp hvW with h | h
      · exact h
      · exact absurd (by obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨k, rfl⟩) hvc
    obtain ⟨⟨i, k⟩, -, rfl⟩ := Finset.mem_image.mp hvTV
    have hcar : (D.tile i).pts k ∈ D.target.carrier := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨i, subset_convexHull ℝ _ ⟨k, rfl⟩⟩
    have hrel : ∃ t : ℤ, (t = 1 ∨ t = 2) ∧
        D.target.localAngle ((D.tile i).pts k) = (0 : ℤ) * tileα D + t * Real.pi := by
      by_cases hint : (D.tile i).pts k ∈ interior D.target.carrier
      · exact ⟨2, Or.inr rfl, by rw [D.target.localAngle_interior hint]; push_cast; ring⟩
      · have hfr : (D.tile i).pts k ∈ frontier D.target.carrier :=
          ⟨subset_closure hcar, hint⟩
        exact ⟨1, Or.inl rfl, by rw [D.target.localAngle_frontier hfr hvc]; push_cast; ring⟩
    obtain ⟨t, ht, hloc⟩ := hrel
    have hr := vertex_relations D hγ hirr _ 0 t hloc
    simp only [wt, vertexType, Prod.mk.injEq]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hrest, ← Finset.mul_sum] at hzero
  -- `∑ wt` over `R` is `S₁ + S₂ + 2 S₃ - 𝒞`.
  have hcount : ∀ (t : ℕ × ℕ × ℕ) (c : ℤ),
      ∑ v ∈ R, (if vertexType D v = t then c else 0) = c * typeCount D t := by
    intro t c
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    unfold typeCount
    congr 1
    ext v
    simp only [Finset.mem_filter, hR, hWdef, Finset.mem_union, Cn, Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨⟨h | ⟨k, rfl⟩, hc⟩, ht⟩
      · exact ⟨h, hc, ht⟩
      · exact absurd ⟨k, rfl⟩ hc
    · rintro ⟨h, hc, ht⟩; exact ⟨⟨Or.inl h, hc⟩, ht⟩
  have hwt : ∑ v ∈ R, wt v = typeCount D (3, 1, 0) + typeCount D (4, 2, 1)
      + 2 * typeCount D (6, 2, 0) - typeCount D (0, 2, 3) := by
    simp only [wt, Finset.sum_sub_distrib, Finset.sum_add_distrib, hcount]
    ring
  rw [hwt] at hzero
  omega

/-- The last clause of `lemma:starsandcenters`: there is at least one center. -/
theorem starsandcenters_center {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    1 ≤ typeCount D (0, 2, 3) := by
  rw [starsandcenters D hγ hirr hA hC]
  omega

end TriangleTiling
