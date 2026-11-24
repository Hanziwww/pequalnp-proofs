import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3527_17
    (hClean : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      3 ≤ E.card →
      (∀ (p1 p2 : Fin P) (l1 l2 : Fin L), p1 ≠ p2 → l1 ≠ l2 →
        ¬ ((p1, l1) ∈ E ∧ (p1, l2) ∈ E ∧ (p2, l1) ∈ E ∧ (p2, l2) ∈ E)) →
      have f : (Fin (P + L) → Bool) → Bool := fun x =>
        decide (∃ (p : Fin P) (l : Fin L), (p, l) ∈ E ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)
      have w : (Fin (P + L) → Bool) → ℕ → Bool := fun x k =>
        (C.wires (List.ofFn x)).getD k false
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ x : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C x = f x) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (P + L) D →
        (∀ x : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D x = f x) →
        C.size ≤ D.size) →
      (∀ (A : Finset (Fin P)) (B : Finset (Fin L)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) → C.size + 2 ≤ E.card + A.card + B.card) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ x : Fin (P + L) → Bool, f x = false → w x (P + L + j) = false) →
      False)
    (hDirtyOneHot : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      3 ≤ E.card →
      (∀ (p1 p2 : Fin P) (l1 l2 : Fin L), p1 ≠ p2 → l1 ≠ l2 →
        ¬ ((p1, l1) ∈ E ∧ (p1, l2) ∈ E ∧ (p2, l1) ∈ E ∧ (p2, l2) ∈ E)) →
      have f : (Fin (P + L) → Bool) → Bool := fun x =>
        decide (∃ (p : Fin P) (l : Fin L), (p, l) ∈ E ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)
      have w : (Fin (P + L) → Bool) → ℕ → Bool := fun x k =>
        (C.wires (List.ofFn x)).getD k false
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ x : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C x = f x) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (P + L) D →
        (∀ x : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D x = f x) →
        C.size ≤ D.size) →
      (∀ (A : Finset (Fin P)) (B : Finset (Fin L)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) → C.size + 2 ≤ E.card + A.card + B.card) →
      (∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ v : Fin (P + L), w (fun i => decide (i = v)) (P + L + j) = true) →
      False)
    (hDirtyNoOneHot : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      3 ≤ E.card →
      (∀ (p1 p2 : Fin P) (l1 l2 : Fin L), p1 ≠ p2 → l1 ≠ l2 →
        ¬ ((p1, l1) ∈ E ∧ (p1, l2) ∈ E ∧ (p2, l1) ∈ E ∧ (p2, l2) ∈ E)) →
      have f : (Fin (P + L) → Bool) → Bool := fun x =>
        decide (∃ (p : Fin P) (l : Fin L), (p, l) ∈ E ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)
      have w : (Fin (P + L) → Bool) → ℕ → Bool := fun x k =>
        (C.wires (List.ofFn x)).getD k false
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ x : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C x = f x) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (P + L) D →
        (∀ x : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D x = f x) →
        C.size ≤ D.size) →
      (∀ (A : Finset (Fin P)) (B : Finset (Fin L)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) → C.size + 2 ≤ E.card + A.card + B.card) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ v : Fin (P + L), w (fun i => decide (i = v)) (P + L + j) = false) →
      (∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ x : Fin (P + L) → Bool, f x = false ∧ w x (P + L + j) = true) →
      False) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → ∃ x15 ∈ x3, x15 ∉ x4 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), x16.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x16 ∧ ∀ (x17 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x16 x17 = Decidable.decide (∃ (x18 : Fin x1) (x19 : Fin x2), (x18, x19) ∈ x3.erase x15 ∧ x17 (Fin.castAdd x2 x18) = Bool.true ∧ x17 (Fin.natAdd x1 x19) = Bool.true) := by
  intro P L E M C0 G hG hnotAcyc hC4 hAO0 hComp0 hMsub hM1 hM2
  have hCycle : ∃ (v : Fin (P + L)) (c : G.Walk v v), c.IsCycle := by
    by_contra h
    exact hnotAcyc (fun v c hc => h ⟨v, c, hc⟩)
  obtain ⟨v0, cyc, hcyc⟩ := hCycle
  have hE3 : 3 ≤ E.card := by
    let toSym : Fin P × Fin L → Sym2 (Fin (P + L)) := fun e => s(Fin.castAdd L e.1, Fin.natAdd P e.2)
    have hedges_sub : ∀ s ∈ cyc.edges, s ∈ E.image toSym := by
      have hwalk : ∀ {a b : Fin (P + L)} (p : G.Walk a b), ∀ s ∈ p.edges, s ∈ E.image toSym :=
        fun p => SimpleGraph.Walk.rec
          (motive := fun _ _ q => ∀ s ∈ q.edges, s ∈ E.image toSym)
          (fun s hs => by cases hs)
          (fun hadj _ ih s hs => by
            simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hs
            rcases hs with rfl | hrest
            · obtain ⟨e, heE, heq⟩ := (hG _ _).mp hadj
              rw [Finset.mem_image]
              refine ⟨e, heE, ?_⟩
              rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rfl
              · exact Sym2.eq_swap
            · exact ih s hrest)
          p
      exact hwalk cyc
    have hlen_ge : 3 ≤ cyc.edges.length := by
      rw [SimpleGraph.Walk.length_edges]
      exact hcyc.three_le_length
    have hnodup : cyc.edges.Nodup := hcyc.edges_nodup
    have hcard_eq : cyc.edges.toFinset.card = cyc.edges.length := List.toFinset_card_of_nodup hnodup
    have hsub : cyc.edges.toFinset ⊆ E.image toSym := by
      intro s hs
      exact hedges_sub s (List.mem_toFinset.mp hs)
    have hle1 : cyc.edges.toFinset.card ≤ (E.image toSym).card := Finset.card_le_card hsub
    have hle2 : (E.image toSym).card ≤ E.card := Finset.card_image_le
    omega
  have hNotAllM : ∃ e ∈ E, e ∉ M := by
    by_contra h
    have hEsubM : ∀ e ∈ E, e ∈ M := fun e he => by
      by_contra hne
      exact h ⟨e, he, hne⟩
    have hTwoNbrs : ∃ u w1 w2 : Fin (P + L), G.Adj u w1 ∧ G.Adj u w2 ∧ w1 ≠ w2 := by
      have hstep : ∀ {x y : Fin (P + L)} (q : G.Walk x y) (a0 : Fin (P + L)),
          G.Adj a0 x → 1 ≤ q.length → (s(a0, x) :: q.edges).Nodup →
          ∃ u w1 w2 : Fin (P + L), G.Adj u w1 ∧ G.Adj u w2 ∧ w1 ≠ w2 :=
        fun q => SimpleGraph.Walk.rec
          (motive := fun x _ q => ∀ a0 : Fin (P + L), G.Adj a0 x → 1 ≤ q.length →
            (s(a0, x) :: q.edges).Nodup → ∃ u w1 w2 : Fin (P + L), G.Adj u w1 ∧ G.Adj u w2 ∧ w1 ≠ w2)
          (fun _ _ hlen _ => by simp only [SimpleGraph.Walk.length_nil] at hlen; omega)
          (fun {x z _} h2 _ _ a0 h1 _ hnd =>
            ⟨x, a0, z, h1.symm, h2, fun heq => by
              subst heq
              simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons, List.mem_cons] at hnd
              exact hnd.1 (Or.inl Sym2.eq_swap)⟩)
          q
      have hwalk2 : ∀ {a b : Fin (P + L)} (p : G.Walk a b),
          2 ≤ p.length → p.edges.Nodup →
          ∃ u w1 w2 : Fin (P + L), G.Adj u w1 ∧ G.Adj u w2 ∧ w1 ≠ w2 :=
        fun p => SimpleGraph.Walk.rec
          (motive := fun _ _ p => 2 ≤ p.length → p.edges.Nodup →
            ∃ u w1 w2 : Fin (P + L), G.Adj u w1 ∧ G.Adj u w2 ∧ w1 ≠ w2)
          (fun hlen _ => by simp only [SimpleGraph.Walk.length_nil] at hlen; omega)
          (fun {a0 u1 _} h1 rest _ hlen hnd => by
            simp only [SimpleGraph.Walk.length_cons] at hlen
            simp only [SimpleGraph.Walk.edges_cons] at hnd
            exact hstep rest a0 h1 (by omega) hnd)
          p
      exact hwalk2 cyc (by have := hcyc.three_le_length; omega) hcyc.edges_nodup
    obtain ⟨u1, w1, w2, h1, h2, hne_v⟩ := hTwoNbrs
    obtain ⟨e1, he1E, he1⟩ := (hG u1 w1).mp h1
    obtain ⟨e2, he2E, he2⟩ := (hG u1 w2).mp h2
    have he1M : e1 ∈ M := hEsubM e1 he1E
    have he2M : e2 ∈ M := hEsubM e2 he2E
    have hcast_ne (p : Fin P) (l : Fin L) : Fin.castAdd L p ≠ Fin.natAdd P l := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    rcases he1 with ⟨hu1a, hv0a⟩ | ⟨hv0a, hu1a⟩
    · rcases he2 with ⟨hu1b, hu2b⟩ | ⟨hu2b, hu1b⟩
      · have hp_eq : e1.1 = e2.1 := by
          have hvv := congrArg Fin.val (hu1a.symm.trans hu1b)
          simp only [Fin.val_castAdd] at hvv
          exact Fin.ext hvv
        have he_eq : e1 = e2 := hM1 e1 he1M e2 he2M hp_eq
        rw [hv0a, hu2b, he_eq] at hne_v
        exact hne_v rfl
      · exact hcast_ne e1.1 e2.2 (hu1a.symm.trans hu1b)
    · rcases he2 with ⟨hu1b, hu2b⟩ | ⟨hu2b, hu1b⟩
      · exact hcast_ne e2.1 e1.2 (hu1b.symm.trans hu1a)
      · have hl_eq : e1.2 = e2.2 := by
          have hvv := congrArg Fin.val (hu1a.symm.trans hu1b)
          simp only [Fin.val_natAdd] at hvv
          exact Fin.ext (by omega)
        have he_eq : e1 = e2 := hM2 e1 he1M e2 he2M hl_eq
        rw [hv0a, hu2b, he_eq] at hne_v
        exact hne_v rfl
  by_cases hHasCov : ∃ (A : Finset (Fin P)) (B : Finset (Fin L)),
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card ≤ C0.size + 1
  · obtain ⟨A, B, hcov, hsz⟩ := hHasCov
    obtain ⟨e0, he0E, he0M⟩ := hNotAllM
    let E' : Finset (Fin P × Fin L) := E.erase e0
    have hE'card : E'.card = E.card - 1 := Finset.card_erase_of_mem he0E
    let Ls : Fin P → Finset (Fin L) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E')
    let A' : Finset (Fin P) := A.filter (fun p => (Ls p).Nonempty)
    let Ps : Fin L → Finset (Fin P) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E' ∧ p ∉ A)
    let B' : Finset (Fin L) := B.filter (fun l => (Ps l).Nonempty)
    have hA'le : A'.card ≤ A.card := Finset.card_filter_le A _
    have hB'le : B'.card ≤ B.card := Finset.card_filter_le B _
    have hsumA : ∑ p ∈ A', (Ls p).card = (E'.filter fun e => e.1 ∈ A).card := by
      have hbi : E'.filter (fun e => e.1 ∈ A) =
          A'.biUnion (fun p => (Ls p).image (fun l => (p, l))) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, Ls, A']
        constructor
        · intro h
          obtain ⟨heE', heA⟩ := h
          exact ⟨e.1, ⟨heA, ⟨e.2, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact heE'⟩⟩,
            e.2, heE', Prod.eta e⟩
        · rintro ⟨p, ⟨hpA, _⟩, l, hpl, rfl⟩
          exact ⟨hpl, hpA⟩
      rw [hbi, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro p _
        exact (Finset.card_image_of_injective (Ls p) (fun l1 l2 h => (Prod.mk.inj h).2)).symm
      · intro p1 _ p2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e he1 he2
        rw [Finset.mem_image] at he1 he2
        obtain ⟨l1, _, rfl⟩ := he1
        obtain ⟨l2, _, heq⟩ := he2
        exact hne (Prod.mk.inj heq).1.symm
    have hsumB : ∑ l ∈ B', (Ps l).card = (E'.filter fun e => e.1 ∉ A).card := by
      have hbi : E'.filter (fun e => e.1 ∉ A) =
          B'.biUnion (fun l => (Ps l).image (fun p => (p, l))) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, Ps, B']
        constructor
        · intro h
          obtain ⟨heE', heNA⟩ := h
          have heB : e.2 ∈ B := by
            rcases hcov e (Finset.mem_of_mem_erase heE') with hA | hB
            · exact absurd hA heNA
            · exact hB
          exact ⟨e.2, ⟨heB, ⟨e.1, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨heE', heNA⟩⟩⟩,
            e.1, ⟨heE', heNA⟩, Prod.eta e⟩
        · rintro ⟨l, ⟨_, _⟩, p, ⟨hpl, hpNA⟩, rfl⟩
          exact ⟨hpl, hpNA⟩
      rw [hbi, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro l _
        exact (Finset.card_image_of_injective (Ps l) (fun p1 p2 h => (Prod.mk.inj h).1)).symm
      · intro l1 _ l2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e he1 he2
        rw [Finset.mem_image] at he1 he2
        obtain ⟨p1, _, rfl⟩ := he1
        obtain ⟨p2, _, heq⟩ := he2
        exact hne (Prod.mk.inj heq).2.symm
    have hsumTotal : (∑ p ∈ A', (Ls p).card) + (∑ l ∈ B', (Ps l).card) = E'.card := by
      rw [hsumA, hsumB]
      have hdisj : Disjoint (E'.filter fun e => e.1 ∈ A) (E'.filter fun e => e.1 ∉ A) := by
        rw [Finset.disjoint_left]
        intro e h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : (E'.filter fun e => e.1 ∈ A) ∪ (E'.filter fun e => e.1 ∉ A) = E' := by
        ext e
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hA : e.1 ∈ A
          · exact Or.inl ⟨h, hA⟩
          · exact Or.inr ⟨h, hA⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    let stars : List (ℕ × List ℕ) :=
      (A'.toList.map fun p => (p.val, (Ls p).toList.map fun l => P + l.val)) ++
      (B'.toList.map fun l => (P + l.val, (Ps l).toList.map fun p => p.val))
    have hstars_len : stars.length = A'.card + B'.card := by
      simp only [stars, List.length_append, List.length_map, Finset.length_toList]
    have hstars_sum : (stars.map fun s => s.2.length).sum = E'.card := by
      simp only [stars, List.map_append, List.sum_append, List.map_map]
      have h1 : (List.map ((fun s : ℕ × List ℕ => s.2.length) ∘ fun p : Fin P => (p.val, (Ls p).toList.map fun l => P + l.val)) A'.toList).sum =
          ∑ p ∈ A', (Ls p).card := by
        rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList]
        simp only [Multiset.map_coe, Multiset.sum_coe]
        congr 1
        apply List.map_congr_left
        intro p _
        simp only [Function.comp_apply, List.length_map, Finset.length_toList]
      have h2 : (List.map ((fun s : ℕ × List ℕ => s.2.length) ∘ fun l : Fin L => (P + l.val, (Ps l).toList.map fun p => p.val)) B'.toList).sum =
          ∑ l ∈ B', (Ps l).card := by
        rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList]
        simp only [Multiset.map_coe, Multiset.sum_coe]
        congr 1
        apply List.map_congr_left
        intro l _
        simp only [Function.comp_apply, List.length_map, Finset.length_toList]
      rw [h1, h2, hsumTotal]
    have hstars_ne : stars ≠ [] := by
      intro hemp
      rw [hemp] at hstars_sum
      simp only [List.map_nil, List.sum_nil] at hstars_sum
      omega
    have hstars_wf : ∀ s ∈ stars, s.1 < P + L ∧ s.2 ≠ [] ∧ ∀ u ∈ s.2, u < P + L := by
      intro s hs
      simp only [stars, List.mem_append, List.mem_map, Finset.mem_toList] at hs
      rcases hs with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · refine ⟨by omega, ?_, ?_⟩
        · intro hemp
          have hlen := congrArg List.length hemp
          simp only [List.length_map, Finset.length_toList, List.length_nil] at hlen
          have hne := (Finset.mem_filter.mp hp).2
          have hpos := Finset.card_pos.mpr hne
          omega
        · intro u hu
          rw [List.mem_map] at hu
          obtain ⟨l, _, rfl⟩ := hu
          omega
      · refine ⟨by omega, ?_, ?_⟩
        · intro hemp
          have hlen := congrArg List.length hemp
          simp only [List.length_map, Finset.length_toList, List.length_nil] at hlen
          have hne := (Finset.mem_filter.mp hl).2
          have hpos := Finset.card_pos.mpr hne
          omega
        · intro u hu
          rw [List.mem_map] at hu
          obtain ⟨p, _, rfl⟩ := hu
          omega
    have hstars_iff (x : Fin (P + L) → Bool) :
        (∃ s ∈ stars, (List.ofFn x).getD s.1 false = true ∧ ∃ u ∈ s.2, (List.ofFn x).getD u false = true) ↔
        (∃ (p : Fin P) (l : Fin L), (p, l) ∈ E' ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
      have hgetP (p : Fin P) : (List.ofFn x).getD p.val false = x (Fin.castAdd L p) := by
        have hlt : p.val < (List.ofFn x).length := by simp only [List.length_ofFn]; omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rfl
      have hgetL (l : Fin L) : (List.ofFn x).getD (P + l.val) false = x (Fin.natAdd P l) := by
        have hlt : P + l.val < (List.ofFn x).length := by simp only [List.length_ofFn]; omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rfl
      constructor
      · rintro ⟨s, hs, hs1, u, hu, hu1⟩
        simp only [stars, List.mem_append, List.mem_map, Finset.mem_toList] at hs
        rcases hs with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · rw [List.mem_map] at hu
          obtain ⟨l, hl, rfl⟩ := hu
          rw [Finset.mem_toList] at hl
          have hpl : (p, l) ∈ E' := (Finset.mem_filter.mp hl).2
          rw [hgetP p] at hs1
          rw [hgetL l] at hu1
          exact ⟨p, l, hpl, hs1, hu1⟩
        · rw [List.mem_map] at hu
          obtain ⟨p, hp, rfl⟩ := hu
          rw [Finset.mem_toList] at hp
          have hpl : (p, l) ∈ E' := (Finset.mem_filter.mp hp).2.1
          rw [hgetL l] at hs1
          rw [hgetP p] at hu1
          exact ⟨p, l, hpl, hu1, hs1⟩
      · rintro ⟨p, l, hpl, hxp, hxl⟩
        by_cases hpA : p ∈ A
        · have hlLs : l ∈ Ls p := Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩
          have hpA' : p ∈ A' := Finset.mem_filter.mpr ⟨hpA, ⟨l, hlLs⟩⟩
          refine ⟨(p.val, (Ls p).toList.map fun l' => P + l'.val), ?_, ?_, P + l.val, ?_, ?_⟩
          · simp only [stars, List.mem_append, List.mem_map, Finset.mem_toList]
            exact Or.inl ⟨p, hpA', rfl⟩
          · rw [hgetP p]; exact hxp
          · rw [List.mem_map]
            exact ⟨l, Finset.mem_toList.mpr hlLs, rfl⟩
          · rw [hgetL l]; exact hxl
        · have hlB : l ∈ B := by
            rcases hcov (p, l) (Finset.mem_of_mem_erase hpl) with h1 | h2
            · exact absurd h1 hpA
            · exact h2
          have hpPs : p ∈ Ps l := Finset.mem_filter.mpr ⟨Finset.mem_univ p, ⟨hpl, hpA⟩⟩
          have hlB' : l ∈ B' := Finset.mem_filter.mpr ⟨hlB, ⟨p, hpPs⟩⟩
          refine ⟨(P + l.val, (Ps l).toList.map fun p' => p'.val), ?_, ?_, p.val, ?_, ?_⟩
          · simp only [stars, List.mem_append, List.mem_map, Finset.mem_toList]
            exact Or.inr ⟨l, hlB', rfl⟩
          · rw [hgetL l]; exact hxl
          · rw [List.mem_map]
            exact ⟨p, Finset.mem_toList.mpr hpPs, rfl⟩
          · rw [hgetP p]; exact hxp
    let n : ℕ := P + L
    let step : List Bool → Gate → List Bool := fun ws g =>
      ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
    have hand_eval (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
      change (a && (b && true)) = (a && b)
      exact congrArg (a && ·) (Bool.and_true b)
    have hor_eval (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
      change (a || (b || false)) = (a || b)
      exact congrArg (a || ·) (Bool.or_false b)
    have getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
    have run_len (gs : List Gate) (ws : List Bool) : (run gs ws).length = ws.length + gs.length := by
      induction gs generalizing ws with
      | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
      | cons g rest ih =>
        simp only [run, List.foldl_cons] at ih ⊢
        rw [ih (step ws g)]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
    have run_append (gs1 gs2 : List Gate) (ws : List Bool) :
        run (gs1 ++ gs2) ws = run gs2 (run gs1 ws) := by
      simp only [run, List.foldl_append]
    have run_snoc (gs : List Gate) (g : Gate) (ws : List Bool) :
        run (gs ++ [g]) ws = step (run gs ws) g := by
      simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have run_keep (gs : List Gate) (ws : List Bool) :
        ∀ i < ws.length, (run gs ws).getD i false = ws.getD i false := by
      induction gs generalizing ws with
      | nil => intro i _; rfl
      | cons g rest ih =>
        intro i hi
        simp only [run, List.foldl_cons] at ih ⊢
        have hi' : i < (step ws g).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [ih (step ws g) i hi']
        exact List.getD_append _ _ _ _ hi
    let AO2List : List Gate → Prop := fun gs =>
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
      (∀ g ∈ gs, g.inputs.length = 2)
    have hAppend (gs : List Gate) (hgs : AO2List gs) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
        (a b : ℕ) (ha : a < n + gs.length) (hb : b < n + gs.length) :
        let g : Gate := ⟨op, [a, b]⟩
        AO2List (gs ++ [g]) ∧
        ∀ (x : Fin n → Bool),
          (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false =
            op.eval [(run gs (List.ofFn x)).getD a false, (run gs (List.ofFn x)).getD b false] := by
      intro g
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro g' hg'
        rw [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · exact hgs.1 g' hg'
        · exact hop
      · intro j hj i hi
        by_cases hltj : j < gs.length
        · rw [List.getD_append _ _ _ _ hltj] at hi
          exact hgs.2.1 j hltj i hi
        · have heq : j = gs.length := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hj
            omega
          subst heq
          rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero] at hi
          simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ha
          · exact hb
      · intro g' hg'
        rw [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · exact hgs.2.2 g' hg'
        · rfl
      · intro x
        rw [run_snoc]
        have hlen : (run gs (List.ofFn x)).length = n + gs.length := by
          rw [run_len, List.length_ofFn]
        dsimp only [step]
        rw [← hlen, getD_snoc_eq (run gs (List.ofFn x)) _]
        rfl
    have hFoldOr : ∀ (ws : List ℕ), ws ≠ [] →
        ∀ (gs : List Gate), AO2List gs → (∀ u ∈ ws, u < n + gs.length) →
        ∃ (extra : List Gate) (out : ℕ),
          let gs' := gs ++ extra
          AO2List gs' ∧
          extra.length = ws.length - 1 ∧
          out < n + gs'.length ∧
          ∀ x : Fin n → Bool,
            (run gs' (List.ofFn x)).getD out false = true ↔
              ∃ u ∈ ws, (run gs (List.ofFn x)).getD u false = true := by
      intro ws
      induction ws with
      | nil => intro hne; exact absurd rfl hne
      | cons u rest ih =>
        cases rest with
        | nil =>
          intro _ gs hgs hwu
          refine ⟨[], u, ?_, rfl, ?_, ?_⟩
          · simpa only [List.append_nil] using hgs
          · simpa only [List.append_nil] using hwu u List.mem_cons_self
          · intro x
            simp only [List.append_nil, List.mem_singleton, exists_eq_left]
        | cons v rest2 =>
          intro _ gs hgs hwu
          have hne' : v :: rest2 ≠ [] := List.cons_ne_nil v rest2
          have hwu' : ∀ w ∈ v :: rest2, w < n + gs.length := fun w hw => hwu w (List.mem_cons_of_mem u hw)
          obtain ⟨extra1, out1, hAO1, hlen1, hout1, hiff1⟩ := ih hne' gs hgs hwu'
          have hu_lt : u < n + (gs ++ extra1).length := by
            have := hwu u List.mem_cons_self
            simp only [List.length_append]
            omega
          have hstep := hAppend (gs ++ extra1) hAO1 GateOp.or (Or.inr rfl) u out1 hu_lt hout1
          refine ⟨extra1 ++ [⟨GateOp.or, [u, out1]⟩], n + (gs ++ extra1).length, ?_, ?_, ?_, ?_⟩
          · simpa only [List.append_assoc] using hstep.1
          · simp only [List.length_append, List.length_cons, List.length_nil] at hlen1 ⊢
            omega
          · simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          · intro x
            have hev := hstep.2 x
            rw [hor_eval] at hev
            have hassoc : gs ++ (extra1 ++ [⟨GateOp.or, [u, out1]⟩]) = (gs ++ extra1) ++ [⟨GateOp.or, [u, out1]⟩] :=
              (List.append_assoc gs extra1 _).symm
            rw [hassoc, hev, Bool.or_eq_true]
            have hu_keep : (run (gs ++ extra1) (List.ofFn x)).getD u false = (run gs (List.ofFn x)).getD u false := by
              rw [run_append]
              exact run_keep extra1 (run gs (List.ofFn x)) u (by rw [run_len, List.length_ofFn]; exact hwu u List.mem_cons_self)
            rw [hu_keep, hiff1 x]
            constructor
            · rintro (h1 | ⟨w, hw, hw1⟩)
              · exact ⟨u, List.mem_cons_self, h1⟩
              · exact ⟨w, List.mem_cons_of_mem u hw, hw1⟩
            · rintro ⟨w, hw, hw1⟩
              rw [List.mem_cons] at hw
              rcases hw with rfl | hw'
              · exact Or.inl hw1
              · exact Or.inr ⟨w, hw', hw1⟩
    have hBuildStars : ∀ (ss : List (ℕ × List ℕ)),
        (∀ s ∈ ss, s.1 < n ∧ s.2 ≠ [] ∧ ∀ u ∈ s.2, u < n) →
        ∀ (gs : List Gate), AO2List gs →
        ∃ (extra : List Gate) (outs : List ℕ),
          let gs' := gs ++ extra
          AO2List gs' ∧
          outs.length = ss.length ∧
          extra.length = (ss.map fun s => s.2.length).sum ∧
          (∀ w ∈ outs, w < n + gs'.length) ∧
          ∀ x : Fin n → Bool,
            (∃ w ∈ outs, (run gs' (List.ofFn x)).getD w false = true) ↔
              (∃ s ∈ ss, (List.ofFn x).getD s.1 false = true ∧ ∃ u ∈ s.2, (List.ofFn x).getD u false = true) := by
      intro ss
      induction ss with
      | nil =>
        intro _ gs hgs
        refine ⟨[], [], ?_, rfl, rfl, (fun w hw => by cases hw), ?_⟩
        · simpa only [List.append_nil] using hgs
        · intro x
          simp only [List.not_mem_nil, false_and, exists_false]
      | cons s rest ih =>
        intro hss gs hgs
        have hs := hss s List.mem_cons_self
        have hrest : ∀ s' ∈ rest, s'.1 < n ∧ s'.2 ≠ [] ∧ ∀ u ∈ s'.2, u < n :=
          fun s' hs' => hss s' (List.mem_cons_of_mem s hs')
        have hs2_lt : ∀ u ∈ s.2, u < n + gs.length := fun u hu => by have := hs.2.2 u hu; omega
        obtain ⟨extra1, orW, hAO1, hlen1, horW_lt, hiff1⟩ := hFoldOr s.2 hs.2.1 gs hgs hs2_lt
        have hs1_lt : s.1 < n + (gs ++ extra1).length := by
          have := hs.1
          simp only [List.length_append]
          omega
        have hstep := hAppend (gs ++ extra1) hAO1 GateOp.and (Or.inl rfl) s.1 orW hs1_lt horW_lt
        let andW : ℕ := n + (gs ++ extra1).length
        let gs2 : List Gate := (gs ++ extra1) ++ [⟨GateOp.and, [s.1, orW]⟩]
        obtain ⟨extra2, outs2, hAO2, hlen_outs2, hlen2, houts2_lt, hiff2⟩ := ih hrest gs2 hstep.1
        refine ⟨(extra1 ++ [⟨GateOp.and, [s.1, orW]⟩]) ++ extra2, andW :: outs2, ?_, ?_, ?_, ?_, ?_⟩
        · have hassoc : gs ++ ((extra1 ++ [⟨GateOp.and, [s.1, orW]⟩]) ++ extra2) = gs2 ++ extra2 := by
            simp only [gs2, List.append_assoc]
          rw [hassoc]
          exact hAO2
        · simp only [List.length_cons, hlen_outs2]
        · have hs2_pos : 1 ≤ s.2.length := List.length_pos_of_ne_nil hs.2.1
          simp only [List.length_append, List.length_cons, List.length_nil, List.map_cons, List.sum_cons] at hlen1 hlen2 ⊢
          omega
        · intro w hw
          have hassoc : gs ++ ((extra1 ++ [⟨GateOp.and, [s.1, orW]⟩]) ++ extra2) = gs2 ++ extra2 := by
            simp only [gs2, List.append_assoc]
          rw [hassoc]
          rw [List.mem_cons] at hw
          rcases hw with rfl | hw2
          · simp only [andW, gs2, List.length_append, List.length_cons, List.length_nil]
            omega
          · exact houts2_lt w hw2
        · intro x
          have hassoc : gs ++ ((extra1 ++ [⟨GateOp.and, [s.1, orW]⟩]) ++ extra2) = gs2 ++ extra2 := by
            simp only [gs2, List.append_assoc]
          rw [hassoc]
          have hand_keep : (run (gs2 ++ extra2) (List.ofFn x)).getD andW false =
              (run gs2 (List.ofFn x)).getD andW false := by
            rw [run_append]
            exact run_keep extra2 (run gs2 (List.ofFn x)) andW (by
              rw [run_len, List.length_ofFn]
              simp only [andW, gs2, List.length_append, List.length_cons, List.length_nil]
              omega)
          have hand_iff : (run gs2 (List.ofFn x)).getD andW false = true ↔
              (List.ofFn x).getD s.1 false = true ∧ ∃ u ∈ s.2, (List.ofFn x).getD u false = true := by
            have hev := hstep.2 x
            rw [hand_eval] at hev
            change (run gs2 (List.ofFn x)).getD andW false = true ↔ _
            rw [hev, Bool.and_eq_true, hiff1 x]
            have hs1_keep : (run (gs ++ extra1) (List.ofFn x)).getD s.1 false = (List.ofFn x).getD s.1 false :=
              run_keep (gs ++ extra1) (List.ofFn x) s.1 (by rw [List.length_ofFn]; exact hs.1)
            rw [hs1_keep]
            constructor
            · rintro ⟨h1, u, hu, hu1⟩
              have hu_keep : (run gs (List.ofFn x)).getD u false = (List.ofFn x).getD u false :=
                run_keep gs (List.ofFn x) u (by rw [List.length_ofFn]; exact hs.2.2 u hu)
              rw [hu_keep] at hu1
              exact ⟨h1, u, hu, hu1⟩
            · rintro ⟨h1, u, hu, hu1⟩
              have hu_keep : (run gs (List.ofFn x)).getD u false = (List.ofFn x).getD u false :=
                run_keep gs (List.ofFn x) u (by rw [List.length_ofFn]; exact hs.2.2 u hu)
              exact ⟨h1, u, hu, by rw [hu_keep]; exact hu1⟩
          constructor
          · rintro ⟨w, hw, hw1⟩
            rw [List.mem_cons] at hw
            rcases hw with rfl | hw2
            · rw [hand_keep, hand_iff] at hw1
              exact ⟨s, List.mem_cons_self, hw1⟩
            · obtain ⟨s', hs', hs'1⟩ := (hiff2 x).mp ⟨w, hw2, hw1⟩
              exact ⟨s', List.mem_cons_of_mem s hs', hs'1⟩
          · rintro ⟨s', hs', hs'1⟩
            rw [List.mem_cons] at hs'
            rcases hs' with rfl | hs'2
            · exact ⟨andW, List.mem_cons_self, by rw [hand_keep, hand_iff]; exact hs'1⟩
            · obtain ⟨w, hw, hw1⟩ := (hiff2 x).mpr ⟨s', hs'2, hs'1⟩
              exact ⟨w, List.mem_cons_of_mem andW hw, hw1⟩
    have hAO_nil : AO2List [] :=
      ⟨(fun g hg => by cases hg), (fun j hj => by simp only [List.length_nil] at hj; omega), (fun g hg => by cases hg)⟩
    obtain ⟨gs1, outs, hAO1, houts_len, hgs1_len, houts_lt, hiff_stars⟩ := hBuildStars stars hstars_wf [] hAO_nil
    simp only [List.nil_append] at hAO1 houts_lt hiff_stars
    have houts_ne : outs ≠ [] := by
      intro hemp
      rw [hemp] at houts_len
      simp only [List.length_nil] at houts_len
      have hpos : 0 < stars.length := List.length_pos_of_ne_nil hstars_ne
      omega
    obtain ⟨extraTop, finalOut, hAO2, hlenTop, _, hiffTop⟩ := hFoldOr outs houts_ne gs1 hAO1 houts_lt
    let D : Circuit := ⟨gs1 ++ extraTop, finalOut⟩
    have hD_size : D.size < C0.size := by
      change (gs1 ++ extraTop).length < C0.size
      rw [List.length_append, hgs1_len, hstars_sum, hlenTop, houts_len, hstars_len]
      have hpos_stars : 1 ≤ A'.card + B'.card := by
        rw [← hstars_len]
        exact List.length_pos_of_ne_nil hstars_ne
      omega
    have hD_AO : IsAO2 (P + L) D := hAO2
    have hD_comp : ∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) D x =
          decide (∃ (p : Fin P) (l : Fin L), (p, l) ∈ E' ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
      intro x
      change (run (gs1 ++ extraTop) (List.ofFn x)).getD finalOut false = _
      rw [Bool.eq_iff_iff, hiffTop x, hiff_stars x, hstars_iff x, decide_eq_true_eq]
    exact ⟨e0, he0E, he0M, D, hD_size, hD_AO, hD_comp⟩
  · exfalso
    have hBelow0 : ∀ (A : Finset (Fin P)) (B : Finset (Fin L)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) → C0.size + 2 ≤ E.card + A.card + B.card := by
      intro A B hcov
      by_contra hlt
      exact hHasCov ⟨A, B, hcov, by omega⟩
    let f : (Fin (P + L) → Bool) → Bool := fun x =>
      decide (∃ (p : Fin P) (l : Fin L), (p, l) ∈ E ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)
    have hMinSz : ∀ (k : ℕ) (C : Circuit), C.size ≤ k →
        IsAO2 (P + L) C → (∀ x : Fin (P + L) → Bool, circuitFun (P + L) C x = f x) →
        ∃ C1 : Circuit, C1.size ≤ C.size ∧ IsAO2 (P + L) C1 ∧
          (∀ x : Fin (P + L) → Bool, circuitFun (P + L) C1 x = f x) ∧
          ∀ D : Circuit, IsAO2 (P + L) D →
            (∀ x : Fin (P + L) → Bool, circuitFun (P + L) D x = f x) → C1.size ≤ D.size := by
      intro k
      induction k with
      | zero =>
        intro C hle hAO hComp
        exact ⟨C, Nat.le_refl _, hAO, hComp, fun D _ _ => by omega⟩
      | succ k ih =>
        intro C hle hAO hComp
        by_cases hmin : ∀ D : Circuit, IsAO2 (P + L) D →
            (∀ x : Fin (P + L) → Bool, circuitFun (P + L) D x = f x) → C.size ≤ D.size
        · exact ⟨C, Nat.le_refl _, hAO, hComp, hmin⟩
        · have hex : ∃ D : Circuit, IsAO2 (P + L) D ∧
              (∀ x : Fin (P + L) → Bool, circuitFun (P + L) D x = f x) ∧ D.size < C.size := by
            by_contra h
            exact hmin (fun D hDAO hDComp => by
              by_contra hlt
              exact h ⟨D, hDAO, hDComp, by omega⟩)
          obtain ⟨D, hDAO, hDComp, hlt⟩ := hex
          obtain ⟨C1, hle1, hAO1, hComp1, hmin1⟩ := ih D (by omega) hDAO hDComp
          exact ⟨C1, Nat.le_trans hle1 (Nat.le_of_lt hlt), hAO1, hComp1, hmin1⟩
    obtain ⟨C, hC_le, hAO, hComp, hMin⟩ := hMinSz C0.size C0 (Nat.le_refl _) hAO0 hComp0
    have hBelow : ∀ (A : Finset (Fin P)) (B : Finset (Fin L)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) → C.size + 2 ≤ E.card + A.card + B.card :=
      fun A B hcov => Nat.le_trans (by omega) (hBelow0 A B hcov)
    let w : (Fin (P + L) → Bool) → ℕ → Bool := fun x k => (C.wires (List.ofFn x)).getD k false
    by_cases hAllClean : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
        ∀ x : Fin (P + L) → Bool, f x = false → w x (P + L + j) = false
    · exact hClean P L E C hE3 hC4 hAO hComp hMin hBelow hAllClean
    · have hDirty : ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∃ x : Fin (P + L) → Bool, f x = false ∧ w x (P + L + j) = true := by
        by_contra h
        exact hAllClean (fun j g hj hand x hfx => by
          cases hval : w x (P + L + j)
          · rfl
          · exact absurd ⟨j, g, hj, hand, x, hfx, hval⟩ h)
      by_cases hOneHot : ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∃ v : Fin (P + L), w (fun i => decide (i = v)) (P + L + j) = true
      · exact hDirtyOneHot P L E C hE3 hC4 hAO hComp hMin hBelow hOneHot
      · have hNoOneHot : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
            ∀ v : Fin (P + L), w (fun i => decide (i = v)) (P + L + j) = false := by
          intro j g hj hand v
          cases hval : w (fun i => decide (i = v)) (P + L + j)
          · rfl
          · exact absurd ⟨j, g, hj, hand, v, hval⟩ hOneHot
        exact hDirtyNoOneHot P L E C hE3 hC4 hAO hComp hMin hBelow hNoOneHot hDirty
