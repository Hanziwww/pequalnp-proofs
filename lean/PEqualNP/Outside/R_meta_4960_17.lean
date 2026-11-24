import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4960_17
    (hRead1 : ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p1 p2 : Fin m, ∀ l1 l2 : Fin n, p1 ≠ p2 → l1 ≠ l2 → ¬((p1, l1) ∈ E ∧ (p1, l2) ∈ E ∧ (p2, l1) ∈ E ∧ (p2, l2) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (m + n) C →
      (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x = decide (∃ p : Fin m, ∃ l : Fin n, (p, l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) →
      PEqualNP.ReadK.IsReadK (m + n) C 1 →
      M ⊆ E → (∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b) → (∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) →
      E.card + M.card ≤ C.size + 1)
    (hCleanNested : ∃ c : ℕ, ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      E.Nonempty →
      (∀ p1 p2 : Fin m, ∀ l1 l2 : Fin n, p1 ≠ p2 → l1 ≠ l2 → ¬((p1, l1) ∈ E ∧ (p1, l2) ∈ E ∧ (p2, l1) ∈ E ∧ (p2, l2) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (m + n) C →
      (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x = decide (∃ p : Fin m, ∃ l : Fin n, (p, l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (m + n) D → (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) D x = PEqualNP.MetaComplexity.circuitFun (m + n) C x) → C.size ≤ D.size) →
      ¬ PEqualNP.ReadK.IsReadK (m + n) C 1 →
      (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin (m + n) → Bool, (C.wires (List.ofFn x)).getD (m + n + j) false = true → PEqualNP.MetaComplexity.circuitFun (m + n) C x = true) →
      M ⊆ E → (∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b) → (∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) →
      E.card + M.card ≤ C.size + 1 + c * (m + n + 1).sqrt)
    (hDirtyOneHot : ∃ c : ℕ, ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      E.Nonempty →
      (∀ p1 p2 : Fin m, ∀ l1 l2 : Fin n, p1 ≠ p2 → l1 ≠ l2 → ¬((p1, l1) ∈ E ∧ (p1, l2) ∈ E ∧ (p2, l1) ∈ E ∧ (p2, l2) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (m + n) C →
      (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x = decide (∃ p : Fin m, ∃ l : Fin n, (p, l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (m + n) D → (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) D x = PEqualNP.MetaComplexity.circuitFun (m + n) C x) → C.size ≤ D.size) →
      ¬ PEqualNP.ReadK.IsReadK (m + n) C 1 →
      (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ i : Fin (m + n), (C.wires (List.ofFn fun k : Fin (m + n) => decide (k = i))).getD (m + n + j) false = true) →
      M ⊆ E → (∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b) → (∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) →
      E.card + M.card ≤ C.size + 1 + c * (m + n + 1).sqrt)
    (hDirtyNoOneHot : ∃ c : ℕ, ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      E.Nonempty →
      (∀ p1 p2 : Fin m, ∀ l1 l2 : Fin n, p1 ≠ p2 → l1 ≠ l2 → ¬((p1, l1) ∈ E ∧ (p1, l2) ∈ E ∧ (p2, l1) ∈ E ∧ (p2, l2) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (m + n) C →
      (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x = decide (∃ p : Fin m, ∃ l : Fin n, (p, l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (m + n) D → (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) D x = PEqualNP.MetaComplexity.circuitFun (m + n) C x) → C.size ≤ D.size) →
      ¬ PEqualNP.ReadK.IsReadK (m + n) C 1 →
      (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ i : Fin (m + n), (C.wires (List.ofFn fun k : Fin (m + n) => decide (k = i))).getD (m + n + j) false = false) →
      (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x : Fin (m + n) → Bool, (C.wires (List.ofFn x)).getD (m + n + j) false = true ∧ PEqualNP.MetaComplexity.circuitFun (m + n) C x = false) →
      M ⊆ E → (∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b) → (∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) →
      E.card + M.card ≤ C.size + 1 + c * (m + n + 1).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 x5 : Finset (Fin x2 × Fin x3)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x7 x8 : Fin x2) (x9 x10 : Fin x3), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x4 ∧ (x7, x10) ∈ x4 ∧ (x8, x9) ∈ x4 ∧ (x8, x10) ∈ x4)) → PEqualNP.TopForm.IsAO2 (x2 + x3) x6 → (∀ (x9 : Fin (x2 + x3) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x3) x6 x9 = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x3), (x10, x11) ∈ x4 ∧ x9 (Fin.castAdd x3 x10) = Bool.true ∧ x9 (Fin.natAdd x2 x11) = Bool.true)) → x5 ⊆ x4 → (∀ x11 ∈ x5, ∀ x13 ∈ x5, x11.1 = x13.1 → x11 = x13) → (∀ x12 ∈ x5, ∀ x14 ∈ x5, x12.2 = x14.2 → x12 = x14) → x4.card + x5.card ≤ x6.size + (1 : ℕ) + x1 * (x2 + x3 + (1 : ℕ)).sqrt := by
  obtain ⟨c2, hc2⟩ := hCleanNested
  obtain ⟨c3, hc3⟩ := hDirtyOneHot
  obtain ⟨c4, hc4⟩ := hDirtyNoOneHot
  refine ⟨max (max c2 c3) c4, ?_⟩
  intro m n E M C hC4 hAO2 hComp hME hM1 hM2
  by_cases hEne : E.Nonempty
  · let P : Circuit → Prop := fun D =>
      IsAO2 (m + n) D ∧
      ∀ x : Fin (m + n) → Bool,
        circuitFun (m + n) D x =
          decide (∃ p : Fin m, ∃ l : Fin n, (p, l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)
    have hmin_ex : ∀ s : ℕ, (∃ D : Circuit, D.size = s ∧ P D) →
        ∃ C' : Circuit, C'.size ≤ s ∧ P C' ∧ ∀ D : Circuit, P D → C'.size ≤ D.size := by
      intro s
      induction s using Nat.strong_induction_on with
      | ind s ih =>
        intro h
        obtain ⟨D, hDs, hDP⟩ := h
        by_cases hmin : ∀ D' : Circuit, P D' → D.size ≤ D'.size
        · exact ⟨D, by omega, hDP, hmin⟩
        · have hex : ∃ D' : Circuit, P D' ∧ D'.size < D.size := by
            by_contra hno
            exact hmin (fun D' hD' => by
              by_contra hlt
              exact hno ⟨D', hD', by omega⟩)
          obtain ⟨D', hD'P, hD'lt⟩ := hex
          obtain ⟨C', hC'le, hC'P, hC'min⟩ := ih D'.size (by omega) ⟨D', rfl, hD'P⟩
          exact ⟨C', by omega, hC'P, hC'min⟩
    obtain ⟨C', hC'le, ⟨hC'AO2, hC'Comp⟩, hC'minP⟩ := hmin_ex C.size ⟨C, rfl, hAO2, hComp⟩
    have hC'min : ∀ D : Circuit, IsAO2 (m + n) D →
        (∀ x : Fin (m + n) → Bool, circuitFun (m + n) D x = circuitFun (m + n) C' x) →
        C'.size ≤ D.size := by
      intro D hDAO2 hDeq
      exact hC'minP D ⟨hDAO2, fun x => (hDeq x).trans (hC'Comp x)⟩
    by_cases hR : IsReadK (m + n) C' 1
    · have h1 := hRead1 m n E M C' hC4 hC'AO2 hC'Comp hR hME hM1 hM2
      omega
    · by_cases hClean : ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
          ∀ x : Fin (m + n) → Bool, (C'.wires (List.ofFn x)).getD (m + n + j) false = true →
            circuitFun (m + n) C' x = true
      · have h2 := hc2 m n E M C' hEne hC4 hC'AO2 hC'Comp hC'min hR hClean hME hM1 hM2
        have hc2_le : c2 ≤ max (max c2 c3) c4 := le_trans (le_max_left c2 c3) (le_max_left _ c4)
        have hmul : c2 * (m + n + 1).sqrt ≤ max (max c2 c3) c4 * (m + n + 1).sqrt :=
          Nat.mul_le_mul_right _ hc2_le
        omega
      · have hDirty : ∃ j < C'.gates.length, (gateAt C' j).op = GateOp.and ∧
            ∃ x : Fin (m + n) → Bool, (C'.wires (List.ofFn x)).getD (m + n + j) false = true ∧
              circuitFun (m + n) C' x = false := by
          by_contra hno
          apply hClean
          intro j hj hop x hwx
          cases hf : circuitFun (m + n) C' x with
          | true => rfl
          | false => exact False.elim (hno ⟨j, hj, hop, x, hwx, hf⟩)
        by_cases hOH : ∃ j < C'.gates.length, (gateAt C' j).op = GateOp.and ∧
            ∃ i : Fin (m + n), (C'.wires (List.ofFn fun k : Fin (m + n) => decide (k = i))).getD (m + n + j) false = true
        · have h3 := hc3 m n E M C' hEne hC4 hC'AO2 hC'Comp hC'min hR hOH hME hM1 hM2
          have hc3_le : c3 ≤ max (max c2 c3) c4 := le_trans (le_max_right c2 c3) (le_max_left _ c4)
          have hmul : c3 * (m + n + 1).sqrt ≤ max (max c2 c3) c4 * (m + n + 1).sqrt :=
            Nat.mul_le_mul_right _ hc3_le
          omega
        · have hNoOH : ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
              ∀ i : Fin (m + n), (C'.wires (List.ofFn fun k : Fin (m + n) => decide (k = i))).getD (m + n + j) false = false := by
            intro j hj hop i
            cases hw : (C'.wires (List.ofFn fun k : Fin (m + n) => decide (k = i))).getD (m + n + j) false with
            | false => rfl
            | true => exact False.elim (hOH ⟨j, hj, hop, i, hw⟩)
          have h4 := hc4 m n E M C' hEne hC4 hC'AO2 hC'Comp hC'min hR hNoOH hDirty hME hM1 hM2
          have hc4_le : c4 ≤ max (max c2 c3) c4 := le_max_right _ c4
          have hmul : c4 * (m + n + 1).sqrt ≤ max (max c2 c3) c4 * (m + n + 1).sqrt :=
            Nat.mul_le_mul_right _ hc4_le
          omega
  · have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEne
    have hM0 : M = ∅ := Finset.subset_empty.mp (hE0 ▸ hME)
    rw [hE0, hM0, Finset.card_empty]
    exact Nat.zero_le _
