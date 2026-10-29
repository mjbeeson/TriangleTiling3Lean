/-
Types of vertices (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv 1206.2229v4):
`lemma:standardvertices`. Statement not yet checked by Beeson.

The type of a point `P` is `(n, k, j)`: the numbers of tiles with their `α`, `β`, `γ` at `P`.
The counts in (i) are over all vertices of the tiling (the corners of `ABC` have none of the types
counted, as their angles are less than `π`).
-/
import TriangleTiling.Laczkovich.ThreeAlpha
import TriangleTiling.ThreeAlpha.ARelation

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.BeesonColoring Set
open Erdos634.Draft.LaczFormal (TileAngles)

variable {N : ℕ} (D : CongruentDissection N)

/-- The local angle values at a point, and the type relation. -/
theorem type_relation {α β a b c : ℝ} (hirr : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) {P : Plane} (t : ℕ)
    (ht : D.target.localAngle P = t * Real.pi) :
    (angleCount D P α + 2 * angleCount D P (2 * α + β) + 3 * angleCount D P Real.pi +
        6 * angleCount D P (2 * Real.pi) : ℤ) = 3 * t ∧
      (angleCount D P β + angleCount D P (2 * α + β) + 2 * angleCount D P Real.pi +
        4 * angleCount D P (2 * Real.pi) : ℤ) = 2 * t := by
  have hs := counts_sum D hirr hrel h P
  rw [ht] at hs
  have e : (((angleCount D P α + 2 * angleCount D P (2 * α + β) + 3 * angleCount D P Real.pi +
        6 * angleCount D P (2 * Real.pi) : ℤ) - 3 * t : ℤ) : ℝ) * α +
      (((angleCount D P β + angleCount D P (2 * α + β) + 2 * angleCount D P Real.pi +
        4 * angleCount D P (2 * Real.pi) : ℤ) - 2 * t : ℤ) : ℝ) * β = 0 := by
    push_cast
    linear_combination hs + ((angleCount D P Real.pi : ℝ) + 2 * angleCount D P (2 * Real.pi) - t) *
      hrel
  obtain ⟨e1, e2⟩ := int_indep hirr hrel e
  omega

/-- The arithmetic of the vertex types. -/
theorem types_arith {x y z u w t : ℕ} (ht : t = 1 ∨ t = 2)
    (e1 : x + 2 * z + 3 * u + 6 * w = 3 * t) (e2 : y + z + 2 * u + 4 * w = 2 * t)
    (hp : 1 ≤ x + y + z) :
    (x = 3 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = 2 ∧ y = 2 ∧ z = 2) ∨
      (x = 6 ∧ y = 4 ∧ z = 0) ∨ (x = 4 ∧ y = 3 ∧ z = 1) ∨ (x = 0 ∧ y = 1 ∧ z = 3) := by
  have hw : w = 0 := by omega
  subst hw
  have hz : z ≤ 3 := by omega
  have hu : u ≤ 1 := by omega
  interval_cases z <;> interval_cases u <;> rcases ht with rfl | rfl <;> omega

open Classical in
/-- **Lemma `lemma:standardvertices`.** Suppose `3α + 2β = π`, triangle `ABC` is `N`-tiled by a
tile `T` with angles `(α, β, γ)`, and `ABC` is not similar to `T`. Then

(i) the number of centers is `N_C = 1 + N₁ + 2N₂ + N₃`, where `N₁`, `N₂`, `N₃` are the numbers of
vertices of types `(3,2,0)`, `(6,4,0)`, `(4,3,1)`; and

(ii) every vertex other than `A`, `B`, `C` has one of the types `(3,2,0)`, `(1,1,1)`, `(2,2,2)`,
`(6,4,0)`, `(4,3,1)`, `(0,1,3)`. -/
theorem standardvertices {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) :
    let V := D.vertexSet_finite.toFinset
    let ty := fun P => (angleCount D P α, angleCount D P β, angleCount D P γ)
    let cnt := fun t : ℕ × ℕ × ℕ => (V.filter fun P => ty P = t).card
    cnt (0, 1, 3) = 1 + cnt (3, 2, 0) + 2 * cnt (6, 4, 0) + cnt (4, 3, 1) ∧
      ∀ P ∈ D.vertexSet, P ∉ Set.range D.target.pts →
        ty P = (3, 2, 0) ∨ ty P = (1, 1, 1) ∨ ty P = (2, 2, 2) ∨ ty P = (6, 4, 0) ∨
          ty P = (4, 3, 1) ∨ ty P = (0, 1, 3) := by
  intro V ty cnt
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts D hrel hT
  subst hγ
  have hT' : TileAngles D α β (2 * α + β) := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hπ := Real.pi_pos
  have hne : ∀ x : Fin 5, ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] x ≠ 0 ∧
      ∀ y, x ≠ y → ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] x ≠
        ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] y := by
    obtain ⟨hv0, hinj⟩ := values_sep D hirr hrel h
    exact fun x => ⟨hv0 x, fun y hxy => hinj.ne hxy⟩
  have hα0 : α ≠ 0 := (hne 0).1
  have hαπ : α ≠ Real.pi := (hne 0).2 3 (by decide)
  have hα2π : α ≠ 2 * Real.pi := (hne 0).2 4 (by decide)
  have hγ0 : 2 * α + β ≠ 0 := (hne 2).1
  have hγπ : 2 * α + β ≠ Real.pi := (hne 2).2 3 (by decide)
  have hγ2π : 2 * α + β ≠ 2 * Real.pi := (hne 2).2 4 (by decide)
  -- A vertex carries some tile's corner.
  have hpos : ∀ P ∈ D.vertexSet, 1 ≤ angleCount D P α + angleCount D P β +
      angleCount D P (2 * α + β) := by
    intro P hP
    obtain ⟨i, l, hil⟩ : ∃ i l, (D.tile i).pts l = P := by
      simp only [Dissection.vertexSet, Set.mem_iUnion, Set.mem_singleton_iff] at hP
      obtain ⟨i, l, hl⟩ := hP
      exact ⟨i, l, hl.symm⟩
    have hv := localAngle_pts (D.tile i) l
    rw [hil] at hv
    rcases tile_angle_mem D h i l with e | e | e <;> rw [e] at hv
    · have := angleCount_pos D hv; omega
    · have := angleCount_pos D hv; omega
    · have := angleCount_pos D hv; omega
  -- (ii)
  have hii : ∀ P ∈ D.vertexSet, P ∉ Set.range D.target.pts →
      ty P = (3, 2, 0) ∨ ty P = (1, 1, 1) ∨ ty P = (2, 2, 2) ∨ ty P = (6, 4, 0) ∨
        ty P = (4, 3, 1) ∨ ty P = (0, 1, 3) := by
    intro P hP hPc
    have hcar : P ∈ D.target.carrier := by
      simp only [Dissection.vertexSet, Set.mem_iUnion, Set.mem_singleton_iff] at hP
      obtain ⟨i, l, rfl⟩ := hP
      have : (D.tile i).pts l ∈ (D.tile i).carrier := subset_convexHull ℝ _ ⟨l, rfl⟩
      rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨i, this⟩
    obtain ⟨t, ht, ht12⟩ : ∃ t : ℕ, D.target.localAngle P = t * Real.pi ∧ (t = 1 ∨ t = 2) := by
      by_cases hin : P ∈ interior D.target.carrier
      · exact ⟨2, by rw [Tri.localAngle_interior _ hin]; push_cast; ring, Or.inr rfl⟩
      · exact ⟨1, by rw [D.target.localAngle_frontier ⟨subset_closure hcar, hin⟩ hPc]; simp,
          Or.inl rfl⟩
    obtain ⟨e1, e2⟩ := type_relation D hirr hrel h t ht
    have hp := hpos P hP
    simp only [ty, Prod.mk.injEq]
    exact types_arith ht12 (by exact_mod_cast e1) (by exact_mod_cast e2) hp
  refine ⟨?_, hii⟩
  -- (i): count `α` corners minus `γ` corners over the vertices.
  have hone : ∀ (i : Fin N) {θ : ℝ} (l : Fin 3), (D.tile i).angleAt l = θ → θ ≠ 0 →
      θ ≠ Real.pi → θ ≠ 2 * Real.pi →
      (V.filter fun P => (D.tile i).localAngle P = θ) = {(D.tile i).pts l} := by
    intro i θ l hl h0 h1 h2
    ext P
    simp only [Finset.mem_filter, Finset.mem_singleton, V, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨-, hP⟩
      obtain ⟨l', hl', hθ⟩ := (localAngle_iff _ _ h0 h1 h2).mp hP
      rw [← hl', tile_angle_inj D hirr hrel h i (hθ.trans hl.symm)]
    · rintro rfl
      refine ⟨?_, (localAngle_pts _ l).trans hl⟩
      simp only [Dissection.vertexSet, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨i, l, rfl⟩
  have hsum : ∀ {θ : ℝ}, (θ = α ∨ θ = 2 * α + β) → θ ≠ 0 → θ ≠ Real.pi → θ ≠ 2 * Real.pi →
      ∑ P ∈ V, angleCount D P θ = N := by
    intro θ hθ h0 h1 h2
    unfold angleCount
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have : ∀ i : Fin N, ∑ P ∈ V, (if (D.tile i).localAngle P = θ then 1 else 0) = 1 := by
      intro i
      obtain ⟨ρ, h0', -, -, -, h2', -⟩ := tile_threeAlpha D h i
      rw [← Finset.card_filter]
      rcases hθ with rfl | rfl
      · rw [hone i (ρ 0) h0' h0 h1 h2]; rfl
      · rw [hone i (ρ 2) h2' h0 h1 h2]; rfl
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp
  have hzero : ∑ P ∈ V, ((angleCount D P α : ℤ) - angleCount D P (2 * α + β)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 := hsum (Or.inl rfl) hα0 hαπ hα2π
    have h2 := hsum (Or.inr rfl) hγ0 hγπ hγ2π
    have h1' : ∑ P ∈ V, (angleCount D P α : ℤ) = N := by exact_mod_cast h1
    have h2' : ∑ P ∈ V, (angleCount D P (2 * α + β) : ℤ) = N := by exact_mod_cast h2
    rw [h1', h2', sub_self]
  -- The corners.
  have hlt : ∀ k, D.target.angleAt k < Real.pi := by
    intro k
    have hs := D.target.angleAt_sum
    have h0 := D.target.angleAt_pos' 0
    have h1 := D.target.angleAt_pos' 1
    have h2 := D.target.angleAt_pos' 2
    fin_cases k <;> simp <;> linarith
  have hcs : ∀ k, (angleCount D (D.target.pts k) α : ℝ) * α +
      angleCount D (D.target.pts k) β * β +
      angleCount D (D.target.pts k) (2 * α + β) * (2 * α + β) +
      angleCount D (D.target.pts k) Real.pi * Real.pi +
      angleCount D (D.target.pts k) (2 * Real.pi) * (2 * Real.pi) = D.target.angleAt k := by
    intro k; rw [counts_sum D hirr hrel h, localAngle_pts]
  have hnn : ∀ (P : Plane) (θ : ℝ), (0 : ℝ) ≤ angleCount D P θ := fun _ _ => Nat.cast_nonneg _
  have hcornV : ∀ k, D.target.pts k ∈ D.vertexSet := by
    intro k
    by_contra hk
    have hz : ∀ θ, θ = α ∨ θ = β ∨ θ = 2 * α + β → angleCount D (D.target.pts k) θ = 0 := by
      intro θ hθ
      by_contra hc
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have h0 : θ ≠ 0 := by rcases hθ with rfl | rfl | rfl <;> [exact hα0; linarith; exact hγ0]
      have h1 : θ ≠ Real.pi := by rcases hθ with rfl | rfl | rfl <;> [exact hαπ; linarith; exact hγπ]
      have h2 : θ ≠ 2 * Real.pi := by
        rcases hθ with rfl | rfl | rfl <;> [exact hα2π; linarith; exact hγ2π]
      obtain ⟨l, hl, -⟩ := (localAngle_iff _ _ h0 h1 h2).mp hi
      apply hk
      simp only [Dissection.vertexSet, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨i, l, hl.symm⟩
    have e := hcs k
    rw [hz α (Or.inl rfl), hz β (Or.inr (Or.inl rfl)), hz _ (Or.inr (Or.inr rfl))] at e
    push_cast at e
    have hp := D.target.angleAt_pos' k
    have hl := hlt k
    rcases Nat.eq_zero_or_pos (angleCount D (D.target.pts k) Real.pi) with hu | hu <;>
      rcases Nat.eq_zero_or_pos (angleCount D (D.target.pts k) (2 * Real.pi)) with hw | hw
    · rw [hu, hw] at e; push_cast at e; linarith
    · have : (1 : ℝ) ≤ angleCount D (D.target.pts k) (2 * Real.pi) := by exact_mod_cast hw
      nlinarith [hnn (D.target.pts k) Real.pi]
    · have : (1 : ℝ) ≤ angleCount D (D.target.pts k) Real.pi := by exact_mod_cast hu
      nlinarith [hnn (D.target.pts k) (2 * Real.pi)]
    · have : (1 : ℝ) ≤ angleCount D (D.target.pts k) Real.pi := by exact_mod_cast hu
      nlinarith [hnn (D.target.pts k) (2 * Real.pi)]
  have hcγ : ∀ k, angleCount D (D.target.pts k) (2 * α + β) = 0 := by
    intro k
    by_contra hc
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨l, hl, hθ⟩ := (localAngle_iff _ _ hγ0 hγπ hγ2π).mp hi
    exact (nogamma D hrel hT' hns).1 k i l hl hθ
  have hcα : ∑ k, angleCount D (D.target.pts k) α = 3 := by
    exact (Finset.sum_congr rfl fun k _ => vcount_eq_anglesAt D k hα0 hαπ hα2π).trans
      (shapes D hrel hT' hns).2.1
  -- The corners have none of the counted types.
  have hnotc : ∀ k (t : ℕ × ℕ × ℕ), (t = (3, 2, 0) ∨ t = (6, 4, 0) ∨ t = (4, 3, 1) ∨ t = (0, 1, 3)) →
      ty (D.target.pts k) ≠ t := by
    intro k t ht he
    have e := hcs k
    have hl := hlt k
    have hu := hnn (D.target.pts k) Real.pi
    have hw := hnn (D.target.pts k) (2 * Real.pi)
    simp only [ty] at he
    rcases ht with rfl | rfl | rfl | rfl <;> simp only [Prod.mk.injEq] at he <;>
      obtain ⟨e1, e2, e3⟩ := he <;> rw [e1, e2, e3] at e <;> push_cast at e <;> nlinarith
  -- Split the vertices into corners and the rest.
  set f : Plane → ℤ := fun P => (angleCount D P α : ℤ) - angleCount D P (2 * α + β)
  set R := V.filter fun P => P ∉ Set.range D.target.pts
  have hsplit := Finset.sum_filter_add_sum_filter_not V (fun P => P ∈ Set.range D.target.pts) f
  have hC : V.filter (fun P => P ∈ Set.range D.target.pts) = Finset.univ.image D.target.pts := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, V,
      Set.Finite.mem_toFinset, Set.mem_range]
    constructor
    · rintro ⟨-, k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨hcornV k, k, rfl⟩
  have hCsum : ∑ P ∈ Finset.univ.image D.target.pts, f P = 3 := by
    rw [Finset.sum_image fun x _ y _ hxy => D.target.indep.injective hxy]
    simp only [f, hcγ, Nat.cast_zero, sub_zero]
    exact_mod_cast hcα
  have hRf : ∀ P ∈ R, f P = 3 * (if ty P = (3, 2, 0) then 1 else 0) +
      6 * (if ty P = (6, 4, 0) then 1 else 0) + 3 * (if ty P = (4, 3, 1) then 1 else 0) -
      3 * (if ty P = (0, 1, 3) then 1 else 0) := by
    intro P hP
    obtain ⟨hPV, hPc⟩ := Finset.mem_filter.mp hP
    have hPV' : P ∈ D.vertexSet := (Set.Finite.mem_toFinset _).mp hPV
    rcases hii P hPV' hPc with e | e | e | e | e | e <;>
      simp only [ty, Prod.mk.injEq] at e <;> obtain ⟨e1, e2, e3⟩ := e <;>
      simp [f, ty, e1, e2, e3]
  have hRsum : ∑ P ∈ R, f P = 3 * (R.filter fun P => ty P = (3, 2, 0)).card +
      6 * (R.filter fun P => ty P = (6, 4, 0)).card +
      3 * (R.filter fun P => ty P = (4, 3, 1)).card -
      3 * (R.filter fun P => ty P = (0, 1, 3)).card := by
    rw [Finset.sum_congr rfl hRf]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_boole]
  have hRcnt : ∀ t : ℕ × ℕ × ℕ, (t = (3, 2, 0) ∨ t = (6, 4, 0) ∨ t = (4, 3, 1) ∨ t = (0, 1, 3)) →
      (R.filter fun P => ty P = t) = V.filter fun P => ty P = t := by
    intro t ht
    ext P
    simp only [R, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hV, -⟩, he⟩; exact ⟨hV, he⟩
    · rintro ⟨hV, he⟩
      refine ⟨⟨hV, ?_⟩, he⟩
      rintro ⟨k, rfl⟩
      exact hnotc k t ht he
  rw [hC, hCsum, hRsum, hRcnt _ (Or.inl rfl), hRcnt _ (Or.inr (Or.inl rfl)),
    hRcnt _ (Or.inr (Or.inr (Or.inl rfl))), hRcnt _ (Or.inr (Or.inr (Or.inr rfl))), hzero] at hsplit
  simp only [cnt]
  omega

end TriangleTiling.ThreeAlpha
