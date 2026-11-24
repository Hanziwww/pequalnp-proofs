import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2702

def setX3 : Finset (Fin 11) := {3, 8, 9, 10}

def setX4 : Finset (Fin 11 × Fin 11) := {(1, 4), (2, 5), (6, 7)}

lemma x4_fst_not_mem_x3 : ∀ e ∈ setX4, e.1 ∉ setX3 := by
  intro e he
  simp only [setX4, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> decide

lemma x4_snd_not_mem_x3 : ∀ e ∈ setX4, e.2 ∉ setX3 := by
  intro e he
  simp only [setX4, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> decide

lemma x4_disjoint_ends :
    ∀ e1 ∈ setX4, ∀ e2 ∈ setX4,
      (e1.1 = e2.1 ∨ e1.1 = e2.2 ∨ e1.2 = e2.1 ∨ e1.2 = e2.2) → e1 = e2 := by
  intro e1 he1 e2 he2
  simp only [setX4, Finset.mem_insert, Finset.mem_singleton] at he1 he2
  rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl <;> decide

lemma main_proof (x1 : SimpleGraph (Fin 11)) [DecidableRel x1.Adj]
    (hedge : ∀ x5 x6 : Fin 11, x1.Adj x5 x6 →
      x5 ∈ setX3 ∨ x6 ∈ setX3 ∨ (x5, x6) ∈ setX4 ∨ (x6, x5) ∈ setX4)
    (x6 : Finset (Fin 11))
    (hmin : PEqualNP.MetaComplexity.NestedCover.IsMinCover x1 x6) :
    ∃ x8 ⊆ setX3,
      (∀ x9 ∈ setX3 \ x8, ∀ x11 ∈ setX3 \ x8, ¬x1.Adj x9 x11) ∧
        have x9 : Finset (Fin 11) := {x9 ∈ Finset.univ \ setX3 | ∃ x10 ∈ setX3 \ x8, x1.Adj x10 x9}
        have x10 : Finset (Fin 11 × Fin 11) := {x10 ∈ setX4 | x1.Adj x10.1 x10.2 ∧ x10.1 ∉ x9 ∧ x10.2 ∉ x9}
        x6.card = x8.card + x9.card + x10.card := by
  classical
  rcases hmin with ⟨hcov, hle⟩
  let x8 : Finset (Fin 11) := x6 ∩ setX3
  have hx8_sub : x8 ⊆ setX3 := Finset.inter_subset_right
  have hind : ∀ a ∈ setX3 \ x8, ∀ b ∈ setX3 \ x8, ¬x1.Adj a b := by
    intro a ha b hb hadj
    rw [Finset.mem_sdiff] at ha hb
    have hna : a ∉ x6 := fun h => ha.2 (Finset.mem_inter.mpr ⟨h, ha.1⟩)
    have hnb : b ∉ x6 := fun h => hb.2 (Finset.mem_inter.mpr ⟨h, hb.1⟩)
    rcases hcov hadj with h | h
    · exact hna h
    · exact hnb h
  let x9 : Finset (Fin 11) := {v ∈ Finset.univ \ setX3 | ∃ u ∈ setX3 \ x8, x1.Adj u v}
  let x10 : Finset (Fin 11 × Fin 11) := {e ∈ setX4 | x1.Adj e.1 e.2 ∧ e.1 ∉ x9 ∧ e.2 ∉ x9}
  refine ⟨x8, hx8_sub, hind, ?_⟩
  change x6.card = x8.card + x9.card + x10.card
  have hupper : x6.card ≤ x8.card + x9.card + x10.card := by
    let T' : Finset (Fin 11) := (x8 ∪ x9) ∪ x10.image Prod.fst
    have hcov' : x1.IsVertexCover (T' : Set (Fin 11)) := by
      intro u v hadj
      change u ∈ T' ∨ v ∈ T'
      by_cases hu3 : u ∈ setX3
      · by_cases hu8 : u ∈ x8
        · left; exact Finset.mem_union_left _ (Finset.mem_union_left _ hu8)
        · have hu_s : u ∈ setX3 \ x8 := Finset.mem_sdiff.mpr ⟨hu3, hu8⟩
          by_cases hv3 : v ∈ setX3
          · by_cases hv8 : v ∈ x8
            · right; exact Finset.mem_union_left _ (Finset.mem_union_left _ hv8)
            · exfalso
              exact hind u hu_s v (Finset.mem_sdiff.mpr ⟨hv3, hv8⟩) hadj
          · right
            have hv9 : v ∈ x9 := by
              simp only [x9, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
              exact ⟨hv3, u, ⟨hu3, hu8⟩, hadj⟩
            exact Finset.mem_union_left _ (Finset.mem_union_right _ hv9)
      · by_cases hv3 : v ∈ setX3
        · by_cases hv8 : v ∈ x8
          · right; exact Finset.mem_union_left _ (Finset.mem_union_left _ hv8)
          · left
            have hu9 : u ∈ x9 := by
              simp only [x9, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
              exact ⟨hu3, v, ⟨hv3, hv8⟩, hadj.symm⟩
            exact Finset.mem_union_left _ (Finset.mem_union_right _ hu9)
        · have he4 := hedge u v hadj
          rcases he4 with h | h | huv | hvu
          · exact False.elim (hu3 h)
          · exact False.elim (hv3 h)
          · by_cases hu9 : u ∈ x9
            · left; exact Finset.mem_union_left _ (Finset.mem_union_right _ hu9)
            · by_cases hv9 : v ∈ x9
              · right; exact Finset.mem_union_left _ (Finset.mem_union_right _ hv9)
              · left
                have hmem : (u, v) ∈ x10 := by
                  simp only [x10, Finset.mem_filter]
                  exact ⟨huv, hadj, hu9, hv9⟩
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, v), hmem, rfl⟩)
          · by_cases hv9 : v ∈ x9
            · right; exact Finset.mem_union_left _ (Finset.mem_union_right _ hv9)
            · by_cases hu9 : u ∈ x9
              · left; exact Finset.mem_union_left _ (Finset.mem_union_right _ hu9)
              · right
                have hmem : (v, u) ∈ x10 := by
                  simp only [x10, Finset.mem_filter]
                  exact ⟨hvu, hadj.symm, hv9, hu9⟩
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v, u), hmem, rfl⟩)
    have hc1 : x6.card ≤ T'.card := hle T' hcov'
    have hc2 : T'.card ≤ (x8 ∪ x9).card + (x10.image Prod.fst).card := Finset.card_union_le _ _
    have hc3 : (x8 ∪ x9).card ≤ x8.card + x9.card := Finset.card_union_le _ _
    have hc4 : (x10.image Prod.fst).card ≤ x10.card := Finset.card_image_le
    omega
  have hlower : x8.card + x9.card + x10.card ≤ x6.card := by
    let pick : Fin 11 × Fin 11 → Fin 11 := fun e => if e.1 ∈ x6 then e.1 else e.2
    let Mset : Finset (Fin 11) := x10.image pick
    have hx8_x6 : x8 ⊆ x6 := Finset.inter_subset_left
    have hx9_x6 : x9 ⊆ x6 := by
      intro v hv
      simp only [x9, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
      rcases hv.2 with ⟨u, hu_s, hadj⟩
      have hnu : u ∉ x6 := fun h => hu_s.2 (Finset.mem_inter.mpr ⟨h, hu_s.1⟩)
      rcases hcov hadj with h | h
      · exact False.elim (hnu h)
      · exact h
    have hM_x6 : Mset ⊆ x6 := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨e, he, rfl⟩
      simp only [x10, Finset.mem_filter] at he
      by_cases h1 : e.1 ∈ x6
      · simp [pick, h1]
      · simp only [pick, h1, ↓reduceIte]
        rcases hcov he.2.1 with h | h
        · exact False.elim (h1 h)
        · exact h
    have hd89 : Disjoint x8 x9 := by
      rw [Finset.disjoint_left]
      intro v hv8 hv9
      simp only [x9, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv9
      exact hv9.1 (hx8_sub hv8)
    have hd89M : Disjoint (x8 ∪ x9) Mset := by
      rw [Finset.disjoint_left]
      intro v hv89 hvM
      rcases Finset.mem_image.mp hvM with ⟨e, he, rfl⟩
      simp only [x10, Finset.mem_filter] at he
      rcases Finset.mem_union.mp hv89 with hv8 | hv9
      · have h3 : pick e ∈ setX3 := hx8_sub hv8
        by_cases h1 : e.1 ∈ x6
        · simp only [pick, h1, ↓reduceIte] at h3
          exact x4_fst_not_mem_x3 e he.1 h3
        · simp only [pick, h1, ↓reduceIte] at h3
          exact x4_snd_not_mem_x3 e he.1 h3
      · by_cases h1 : e.1 ∈ x6
        · simp only [pick, h1, ↓reduceIte] at hv9
          exact he.2.2.1 hv9
        · simp only [pick, h1, ↓reduceIte] at hv9
          exact he.2.2.2 hv9
    have hinj : Set.InjOn pick (x10 : Set (Fin 11 × Fin 11)) := by
      intro e1 he1 e2 he2 heq
      simp only [Finset.mem_coe, x10, Finset.mem_filter] at he1 he2
      apply x4_disjoint_ends e1 he1.1 e2 he2.1
      by_cases h1 : e1.1 ∈ x6 <;> by_cases h2 : e2.1 ∈ x6 <;>
        simp only [pick, h1, h2, ↓reduceIte] at heq
      · exact Or.inl heq
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr (Or.inl heq))
      · exact Or.inr (Or.inr (Or.inr heq))
    have hMcard : Mset.card = x10.card := Finset.card_image_of_injOn hinj
    have hsub : (x8 ∪ x9) ∪ Mset ⊆ x6 :=
      Finset.union_subset (Finset.union_subset hx8_x6 hx9_x6) hM_x6
    have hcard : ((x8 ∪ x9) ∪ Mset).card ≤ x6.card := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd89M, Finset.card_union_of_disjoint hd89, hMcard] at hcard
    exact hcard
  omega

end PEqualNP.Outside.L_meta_2702

theorem PEqualNP.Outside.L_meta_2702 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj],   have x3 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};   have x4 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};   (∀ (x5 x6 : Fin (11 : ℕ)), x1.Adj x5 x6 → x5 ∈ x3 ∨ x6 ∈ x3 ∨ (x5, x6) ∈ x4 ∨ (x6, x5) ∈ x4) →     ∀ (x6 : Finset (Fin (11 : ℕ))),       PEqualNP.MetaComplexity.NestedCover.IsMinCover x1 x6 →         ∃ x8 ⊆ x3,           (∀ x9 ∈ x3 \ x8, ∀ x11 ∈ x3 \ x8, ¬x1.Adj x9 x11) ∧             have x9 : Finset (Fin (11 : ℕ)) := {x9 ∈ Finset.univ \ x3 | ∃ x10 ∈ x3 \ x8, x1.Adj x10 x9};             have x10 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x10 ∈ x4 | x1.Adj x10.1 x10.2 ∧ x10.1 ∉ x9 ∧ x10.2 ∉ x9};             x6.card = x8.card + x9.card + x10.card :=
  fun x1 _ hedge x6 hmin => PEqualNP.Outside.L_meta_2702.main_proof x1 hedge x6 hmin
