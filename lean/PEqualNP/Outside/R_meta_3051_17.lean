import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_3051_17
    (hCleanUncovered :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
        300 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        have soundQ : (Fin (N + N) → Bool) → Prop := fun x =>
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q ∧
          ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
        have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun E =>
          PEqualNP.TopForm.IsAO2 (N + N) E ∧
          (∀ p l : Fin N, I p l →
            PEqualNP.MetaComplexity.circuitFun (N + N) E (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) ∧
          (∀ x : Fin (N + N) → Bool, soundQ x → PEqualNP.MetaComplexity.circuitFun (N + N) E x = false)
        ok D →
        (∀ E : PEqualNP.CircuitLowerBounds.Circuit, ok E → D.size ≤ E.size) →
        (∃ p l : Fin N, I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
          ∀ x : Fin (N + N) → Bool, soundQ x → PEqualNP.ReadTwo.wval D x (N + N + j) = false) →
        N * q ≤ 100 * D.size)
    (hDirtyOneHot :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
        300 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        have soundQ : (Fin (N + N) → Bool) → Prop := fun x =>
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q ∧
          ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
        have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun E =>
          PEqualNP.TopForm.IsAO2 (N + N) E ∧
          (∀ p l : Fin N, I p l →
            PEqualNP.MetaComplexity.circuitFun (N + N) E (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) ∧
          (∀ x : Fin (N + N) → Bool, soundQ x → PEqualNP.MetaComplexity.circuitFun (N + N) E x = false)
        ok D →
        (∀ E : PEqualNP.CircuitLowerBounds.Circuit, ok E → D.size ≤ E.size) →
        (∃ p l : Fin N, I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
          ∃ v : Fin (N + N), PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (N + N + j) = true) →
        N * q ≤ 100 * D.size)
    (hDirtyNoOneHot :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
        300 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        have soundQ : (Fin (N + N) → Bool) → Prop := fun x =>
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q ∧
          ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
        have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun E =>
          PEqualNP.TopForm.IsAO2 (N + N) E ∧
          (∀ p l : Fin N, I p l →
            PEqualNP.MetaComplexity.circuitFun (N + N) E (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) ∧
          (∀ x : Fin (N + N) → Bool, soundQ x → PEqualNP.MetaComplexity.circuitFun (N + N) E x = false)
        ok D →
        (∀ E : PEqualNP.CircuitLowerBounds.Circuit, ok E → D.size ≤ E.size) →
        (∃ p l : Fin N, I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
          ∀ v : Fin (N + N), PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (N + N + j) = false) →
        (∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
          ∃ x : Fin (N + N) → Bool, soundQ x ∧ PEqualNP.ReadTwo.wval D x (N + N + j) = true) →
        N * q ≤ 100 * D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I hdec origC hq hN hcard huniq hMono origTrue origFalse
  have hNpos : 0 < N := by
    have : 0 < q ^ 2 + q + 1 := Nat.succ_pos _
    omega
  have hNoC4 : ∀ (p1 p2 l1 l2 : Fin N), p1 ≠ p2 → l1 ≠ l2 → ¬ (I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
    intro p1 p2 l1 l2 hpne hlne h
    obtain ⟨l, _, hlu⟩ := huniq p1 p2 hpne
    have h1 := hlu l1 ⟨h.1, h.2.2.1⟩
    have h2 := hlu l2 ⟨h.2.1, h.2.2.2⟩
    exact hlne (h1.trans h2.symm)
  let E : Finset (Fin N × Fin N) := PEqualNP.ReadTwo.incid I
  have hmem_E (p l : Fin N) : (p, l) ∈ E ↔ I p l := by
    change (p, l) ∈ @Finset.filter (Fin N × Fin N) (fun e => I e.1 e.2) (Classical.decPred _) Finset.univ ↔ I p l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hEcard : E.card = N * (q + 1) := by
    have hbi : E = (Finset.univ : Finset (Fin N)).biUnion
        (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
      ext e
      simp only [hmem_E, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter]
      constructor
      · intro hI
        exact ⟨e.2, e.1, hI, Prod.eta e⟩
      · rintro ⟨l, p, hI, rfl⟩
        exact hI
    rw [hbi, Finset.card_biUnion]
    · have hsum : ∑ l : Fin N, ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card =
          ∑ _l : Fin N, (q + 1) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), ← Fintype.card_subtype]
        exact hcard l
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    · intro l1 _ l2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨p1, _, rfl⟩ := h1
      obtain ⟨p2, _, heq⟩ := h2
      exact hne (Prod.mk.inj heq).2.symm
  have hEempty : E ≠ ∅ := by
    intro hemp
    rw [hemp, Finset.card_empty] at hEcard
    have hpos : 0 < N * (q + 1) := Nat.mul_pos hNpos (Nat.succ_pos q)
    omega
  let n2 : ℕ := N + N
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
  have hand_eval1 (a : Bool) : GateOp.and.eval [a] = a := by change (a && true) = a; exact Bool.and_true a
  have hand_eval2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    change (a && (b && true)) = (a && b); exact congrArg (a && ·) (Bool.and_true b)
  have hor_eval1 (a : Bool) : GateOp.or.eval [a] = a := by change (a || false) = a; exact Bool.or_false a
  have hor_eval2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    change (a || (b || false)) = (a || b); exact congrArg (a || ·) (Bool.or_false b)
  have getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne (l : List Bool) (a : Bool) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j false = l.getD j false := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) false (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l false (n := j) (by omega)]
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
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n2 + j) ∧
    (∀ g ∈ gs, g.inputs.length = 2)
  have hNormMono : ∀ k ≤ origC.gates.length, ∃ gs : List Gate,
      gs.length ≤ k ∧ AO2List gs ∧
      ∀ i < n2 + k,
        (∃ c : Bool, ∀ x : Fin n2 → Bool, (run origC.gates (List.ofFn x)).getD i false = c) ∨
        (∃ w < n2 + gs.length, ∀ x : Fin n2 → Bool, (run origC.gates (List.ofFn x)).getD i false = (run gs (List.ofFn x)).getD w false) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Nat.le_refl 0,
        ⟨(fun g hg => by cases hg), (fun j hj => by simp only [List.length_nil] at hj; omega), (fun g hg => by cases hg)⟩, ?_⟩
      intro i hi
      refine Or.inr ⟨i, by simp only [List.length_nil]; omega, fun x => ?_⟩
      exact run_keep origC.gates (List.ofFn x) i (by simp only [List.length_ofFn]; omega)
    | succ k ih =>
      intro hk1
      obtain ⟨gs, hgs_len, hgs_AO, hmap⟩ := ih (by omega)
      let g : Gate := origC.gates[k]'(by omega)
      have hg_mem : g ∈ origC.gates := List.getElem_mem (by omega)
      have hgM := hMono g hg_mem
      have hwire_k (x : Fin n2 → Bool) :
          (run origC.gates (List.ofFn x)).getD (n2 + k) false =
            g.op.eval (g.inputs.map fun i => (run (origC.gates.take k) (List.ofFn x)).getD i false) := by
        have hsp : origC.gates = origC.gates.take k ++ [g] ++ origC.gates.drop (k + 1) := by
          have h2 : origC.gates.drop k = g :: origC.gates.drop (k + 1) := List.drop_eq_getElem_cons (by omega)
          calc origC.gates = origC.gates.take k ++ origC.gates.drop k := (List.take_append_drop k origC.gates).symm
            _ = origC.gates.take k ++ (g :: origC.gates.drop (k + 1)) := by rw [h2]
            _ = origC.gates.take k ++ [g] ++ origC.gates.drop (k + 1) := by rw [List.append_assoc, List.singleton_append]
        conv_lhs => rw [hsp, run_append, run_append]
        have hlen1 : (run (origC.gates.take k) (List.ofFn x)).length = n2 + k := by
          rw [run_len, List.length_ofFn, List.length_take]; omega
        have hlt2 : n2 + k < (run [g] (run (origC.gates.take k) (List.ofFn x))).length := by
          rw [run_len, hlen1, List.length_cons, List.length_nil]; omega
        rw [run_keep (origC.gates.drop (k + 1)) _ (n2 + k) hlt2]
        change (step (run (origC.gates.take k) (List.ofFn x)) g).getD (n2 + k) false = _
        dsimp only [step]
        rw [← hlen1, getD_snoc_eq (run (origC.gates.take k) (List.ofFn x)) _]
      have hMapIn (i : ℕ) :
          (∃ c : Bool, ∀ x : Fin n2 → Bool, (run (origC.gates.take k) (List.ofFn x)).getD i false = c) ∨
          (∃ w < n2 + gs.length, ∀ x : Fin n2 → Bool, (run (origC.gates.take k) (List.ofFn x)).getD i false = (run gs (List.ofFn x)).getD w false) := by
        by_cases hi : i < n2 + k
        · have hpre (x : Fin n2 → Bool) :
              (run (origC.gates.take k) (List.ofFn x)).getD i false = (run origC.gates (List.ofFn x)).getD i false := by
            have hsp : origC.gates = origC.gates.take k ++ origC.gates.drop k := (List.take_append_drop k origC.gates).symm
            conv_rhs => rw [hsp, run_append]
            exact (run_keep (origC.gates.drop k) (run (origC.gates.take k) (List.ofFn x)) i
              (by rw [run_len, List.length_ofFn, List.length_take]; omega)).symm
          rcases hmap i hi with ⟨c, hc⟩ | ⟨w, hw, hww⟩
          · exact Or.inl ⟨c, fun x => (hpre x).trans (hc x)⟩
          · exact Or.inr ⟨w, hw, fun x => (hpre x).trans (hww x)⟩
        · refine Or.inl ⟨false, fun x => ?_⟩
          exact List.getD_eq_default _ false (n := i) (by rw [run_len, List.length_ofFn, List.length_take]; omega)
      have hStepNo (hnew :
          (∃ c : Bool, ∀ x : Fin n2 → Bool, (run origC.gates (List.ofFn x)).getD (n2 + k) false = c) ∨
          (∃ w < n2 + gs.length, ∀ x : Fin n2 → Bool, (run origC.gates (List.ofFn x)).getD (n2 + k) false = (run gs (List.ofFn x)).getD w false)) :
          ∃ gs' : List Gate, gs'.length ≤ k + 1 ∧ AO2List gs' ∧
            ∀ i < n2 + (k + 1),
              (∃ c : Bool, ∀ x : Fin n2 → Bool, (run origC.gates (List.ofFn x)).getD i false = c) ∨
              (∃ w < n2 + gs'.length, ∀ x : Fin n2 → Bool, (run origC.gates (List.ofFn x)).getD i false = (run gs' (List.ofFn x)).getD w false) := by
        refine ⟨gs, by omega, hgs_AO, fun i hi => ?_⟩
        by_cases heq : i = n2 + k
        · subst heq; exact hnew
        · exact hmap i (by omega)
      have hlen2 : g.inputs.length ≤ 2 := hgM.2
      cases hin : g.inputs with
      | nil =>
        apply hStepNo
        refine Or.inl ⟨g.op.eval [], fun x => ?_⟩
        rw [hwire_k x, hin, List.map_nil]
      | cons i1 rest =>
        cases rest with
        | nil =>
          apply hStepNo
          have hev1 (x : Fin n2 → Bool) :
              (run origC.gates (List.ofFn x)).getD (n2 + k) false = (run (origC.gates.take k) (List.ofFn x)).getD i1 false := by
            rw [hwire_k x, hin, List.map_cons, List.map_nil]
            rcases hgM.1 with hop | hop
            · rw [hop]; exact hand_eval1 _
            · rw [hop]; exact hor_eval1 _
          rcases hMapIn i1 with ⟨c1, hc1⟩ | ⟨w1, hw1, hww1⟩
          · exact Or.inl ⟨c1, fun x => (hev1 x).trans (hc1 x)⟩
          · exact Or.inr ⟨w1, hw1, fun x => (hev1 x).trans (hww1 x)⟩
        | cons i2 rest2 =>
          cases rest2 with
          | nil =>
            rcases hMapIn i1 with ⟨c1, hc1⟩ | ⟨w1, hw1, hww1⟩
            · apply hStepNo
              rcases hgM.1 with hand | hor
              · cases c1
                · refine Or.inl ⟨false, fun x => ?_⟩
                  rw [hwire_k x, hand, hin, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hc1 x, Bool.false_and]
                · rcases hMapIn i2 with ⟨c2, hc2⟩ | ⟨w2, hw2, hww2⟩
                  · refine Or.inl ⟨c2, fun x => ?_⟩
                    rw [hwire_k x, hand, hin, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hc1 x, hc2 x, Bool.true_and]
                  · refine Or.inr ⟨w2, hw2, fun x => ?_⟩
                    rw [hwire_k x, hand, hin, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hc1 x, hww2 x, Bool.true_and]
              · cases c1
                · rcases hMapIn i2 with ⟨c2, hc2⟩ | ⟨w2, hw2, hww2⟩
                  · refine Or.inl ⟨c2, fun x => ?_⟩
                    rw [hwire_k x, hor, hin, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hc1 x, hc2 x, Bool.false_or]
                  · refine Or.inr ⟨w2, hw2, fun x => ?_⟩
                    rw [hwire_k x, hor, hin, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hc1 x, hww2 x, Bool.false_or]
                · refine Or.inl ⟨true, fun x => ?_⟩
                  rw [hwire_k x, hor, hin, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hc1 x, Bool.true_or]
            · rcases hMapIn i2 with ⟨c2, hc2⟩ | ⟨w2, hw2, hww2⟩
              · apply hStepNo
                rcases hgM.1 with hand | hor
                · cases c2
                  · refine Or.inl ⟨false, fun x => ?_⟩
                    rw [hwire_k x, hand, hin, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hc2 x, Bool.and_false]
                  · refine Or.inr ⟨w1, hw1, fun x => ?_⟩
                    rw [hwire_k x, hand, hin, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hww1 x, hc2 x, Bool.and_true]
                · cases c2
                  · refine Or.inr ⟨w1, hw1, fun x => ?_⟩
                    rw [hwire_k x, hor, hin, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hww1 x, hc2 x, Bool.or_false]
                  · refine Or.inl ⟨true, fun x => ?_⟩
                    rw [hwire_k x, hor, hin, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hc2 x, Bool.or_true]
              · let gNew : Gate := ⟨g.op, [w1, w2]⟩
                refine ⟨gs ++ [gNew], by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ⟨?_, ?_, ?_⟩, ?_⟩
                · intro g' hg'
                  rw [List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hgs_AO.1 g' hg'
                  · exact hgM.1
                · intro j hj i hi
                  by_cases hltj : j < gs.length
                  · rw [List.getD_append _ _ _ _ hltj] at hi
                    exact hgs_AO.2.1 j hltj i hi
                  · have heq : j = gs.length := by
                      simp only [List.length_append, List.length_cons, List.length_nil] at hj
                      omega
                    subst heq
                    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero] at hi
                    simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl
                    · exact hw1
                    · exact hw2
                · intro g' hg'
                  rw [List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hgs_AO.2.2 g' hg'
                  · rfl
                · intro i hi
                  by_cases heq : i = n2 + k
                  · subst heq
                    refine Or.inr ⟨n2 + gs.length, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
                    rw [hwire_k x, hin, List.map_cons, List.map_cons, List.map_nil, hww1 x, hww2 x, run_snoc]
                    have hlen_run : (run gs (List.ofFn x)).length = n2 + gs.length := by rw [run_len, List.length_ofFn]
                    dsimp only [step, gNew]
                    rw [← hlen_run, getD_snoc_eq (run gs (List.ofFn x)) _]
                    rfl
                  · rcases hmap i (by omega) with ⟨c, hc⟩ | ⟨w, hw, hww⟩
                    · exact Or.inl ⟨c, hc⟩
                    · refine Or.inr ⟨w, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
                      rw [hww x, run_snoc]
                      have hlen_run : (run gs (List.ofFn x)).length = n2 + gs.length := by rw [run_len, List.length_ofFn]
                      exact (getD_snoc_ne (run gs (List.ofFn x)) _ w (by omega)).symm
          | cons _ _ =>
            rw [hin] at hlen2
            simp only [List.length_cons] at hlen2
            omega
  obtain ⟨gs0, hgs0_len, hgs0_AO, hmap0⟩ := hNormMono origC.gates.length (Nat.le_refl _)
  have hOrig_false0 : circuitFun n2 origC (fun _ => false) = false := by
    have hcard0 : Fintype.card { l : Fin N // (fun _ : Fin n2 => false) (Fin.natAdd N l) = true } = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun l => by cases l.2⟩
    exact origFalse (fun _ => false) (by rw [hcard0]; omega) (by rintro ⟨_, _, _, h, _⟩; cases h)
  have hOrig_hasTrue : ∃ x : Fin n2 → Bool, circuitFun n2 origC x = true := by
    obtain ⟨⟨p0, l0⟩, hpl0⟩ := Finset.nonempty_iff_ne_empty.mpr hEempty
    exact ⟨fun i => decide (i = Fin.castAdd N p0 ∨ i = Fin.natAdd N l0), origTrue p0 l0 ((hmem_E p0 l0).mp hpl0)⟩
  have hOrig_out_lt : origC.output < n2 + origC.gates.length := by
    by_contra hge
    obtain ⟨xT, hxT⟩ := hOrig_hasTrue
    have h0 : circuitFun n2 origC xT = false := by
      change (run origC.gates (List.ofFn xT)).getD origC.output false = false
      exact List.getD_eq_default _ false (n := origC.output) (by rw [run_len, List.length_ofFn]; omega)
    rw [h0] at hxT; cases hxT
  have hD0_ex : ∃ D0 : Circuit, IsAO2 n2 D0 ∧ D0.size ≤ origC.size ∧
      ∀ x : Fin n2 → Bool, circuitFun n2 D0 x = circuitFun n2 origC x := by
    rcases hmap0 origC.output hOrig_out_lt with ⟨c, hc⟩ | ⟨w, _, hww⟩
    · exfalso
      cases c
      · obtain ⟨xT, hxT⟩ := hOrig_hasTrue
        have h0 : circuitFun n2 origC xT = false := hc xT
        rw [h0] at hxT; cases hxT
      · have h1 : circuitFun n2 origC (fun _ => false) = true := hc (fun _ => false)
        rw [h1] at hOrig_false0; cases hOrig_false0
    · refine ⟨⟨gs0, w⟩, hgs0_AO, hgs0_len, fun x => (hww x).symm⟩
  obtain ⟨D0, hD0_AO, hD0_sz, hD0_eq⟩ := hD0_ex
  let soundQ : (Fin n2 → Bool) → Prop := fun x =>
    Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q ∧
    ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
  let ok : Circuit → Prop := fun E =>
    IsAO2 n2 E ∧
    (∀ p l : Fin N, I p l → circuitFun n2 E (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) ∧
    (∀ x : Fin n2 → Bool, soundQ x → circuitFun n2 E x = false)
  have hD0_ok : ok D0 :=
    ⟨hD0_AO, fun p l hpl => (hD0_eq _).trans (origTrue p l hpl), fun x hx => (hD0_eq x).trans (origFalse x hx.1 hx.2)⟩
  have hmin_ex : ∀ k : ℕ, ∀ C0 : Circuit, C0.size ≤ k → ok C0 →
      ∃ C : Circuit, ok C ∧ C.size ≤ C0.size ∧ ∀ E : Circuit, ok E → C.size ≤ E.size := by
    intro k
    induction k with
    | zero =>
      intro C0 hle hok
      exact ⟨C0, hok, Nat.le_refl _, fun E _ => by omega⟩
    | succ k ih =>
      intro C0 hle hok
      by_cases hmin : ∀ E : Circuit, ok E → C0.size ≤ E.size
      · exact ⟨C0, hok, Nat.le_refl _, hmin⟩
      · have hexE : ∃ E : Circuit, ok E ∧ E.size < C0.size := by
          by_contra hno
          exact hmin (fun E hokE => by by_contra hlt; exact hno ⟨E, hokE, by omega⟩)
        obtain ⟨E1, hok1, hlt1⟩ := hexE
        obtain ⟨C, hokC, hleC, hminC⟩ := ih E1 (by omega) hok1
        exact ⟨C, hokC, Nat.le_trans hleC (Nat.le_of_lt hlt1), hminC⟩
  obtain ⟨C, hC_ok, hC_le_D0, hCmin⟩ := hmin_ex D0.size D0 (Nat.le_refl _) hD0_ok
  suffices hgoal : N * q ≤ 100 * C.size by
    exact Nat.le_trans hgoal (Nat.mul_le_mul_left 100 (Nat.le_trans hC_le_D0 hD0_sz))
  obtain ⟨hAO2, hTrueC, hFalseC⟩ := hC_ok
  have hRB : ReadsBack n2 C := hAO2.2.1
  by_cases hall : ∀ (p l : Fin N), I p l →
      ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn C j a b ∧
        PEqualNP.ReadTwo.orp C n2 (n2 + j) C.output ∧
        PEqualNP.ReadTwo.orp C n2 p.val a ∧
        PEqualNP.ReadTwo.orp C n2 (N + l.val) b
  · let OrPath : ℕ → ℕ → Prop := fun w target =>
      ∀ Q : ℕ → Prop,
        Q target →
        (∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
          ∀ a ∈ (gateAt C k).inputs, Q a → Q (n2 + k)) →
        Q w
    have orPath_refl (t : ℕ) : OrPath t t := fun _ h _ => h
    have orPath_step {k a t : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
        (ha : a ∈ (gateAt C k).inputs) (hp : OrPath a t) : OrPath (n2 + k) t :=
      fun Q ht hs => hs k hk hor a ha (hp Q ht hs)
    have orPath_trans {u v w : ℕ} (huv : OrPath u v) (hvw : OrPath v w) : OrPath u w :=
      fun Q hw hs => huv Q (hvw Q hw hs) hs
    have orPath_cases {w t : ℕ} (h : OrPath w t) :
        w = t ∨ ∃ k < C.gates.length, w = n2 + k ∧ (gateAt C k).op = GateOp.or ∧
          ∃ a ∈ (gateAt C k).inputs, OrPath a t := by
      apply h (fun x => x = t ∨ ∃ k < C.gates.length, x = n2 + k ∧ (gateAt C k).op = GateOp.or ∧
          ∃ a ∈ (gateAt C k).inputs, OrPath a t)
      · exact Or.inl rfl
      · intro k hk hor a ha hPa
        refine Or.inr ⟨k, hk, rfl, hor, a, ha, ?_⟩
        rcases hPa with rfl | ⟨k', hk', rfl, hor', a', ha', hp'⟩
        · exact orPath_refl _
        · exact orPath_step hk' hor' ha' hp'
    have orPath_parent {w t : ℕ} (h : OrPath w t) (hne : w ≠ t) :
        ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
          OrPath w (n2 + y) ∧ t ∈ (gateAt C y).inputs := by
      have hdisj : w = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
          OrPath w (n2 + y) ∧ t ∈ (gateAt C y).inputs := by
        apply h (fun x => x = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
            OrPath x (n2 + y) ∧ t ∈ (gateAt C y).inputs)
        · exact Or.inl rfl
        · intro k hk hor a ha hPa
          rcases hPa with rfl | ⟨y, hy, hory, hpy, hty⟩
          · exact Or.inr ⟨k, hk, hor, orPath_refl (n2 + k), ha⟩
          · exact Or.inr ⟨y, hy, hory, orPath_step hk hor ha hpy, hty⟩
      rcases hdisj with heq | hex
      · exact (hne heq).elim
      · exact hex
    have orp_to_orPath {t w : ℕ} (h : PEqualNP.ReadTwo.orp C n2 t w) : OrPath w t := by
      change Relation.ReflTransGen (fun a b => a < b ∧ ∃ j, b = n2 + j ∧ isOr C j ∧ a ∈ (gateAt C j).inputs) t w at h
      induction h with
      | refl => exact orPath_refl t
      | tail _ hstep ih =>
        obtain ⟨_, j, rfl, ⟨hj, hor⟩, ha⟩ := hstep
        exact orPath_step hj hor ha ih
    have wireVal_input (i : Fin n2) (x : Fin n2 → Bool) : wireVal n2 C i.val x = x i := by
      change (run C.gates (List.ofFn x)).getD i.val false = x i
      rw [run_keep C.gates (List.ofFn x) i.val (by simp only [List.length_ofFn]; exact i.isLt),
          List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
    have wireVal_gate (k : ℕ) (hk : k < C.gates.length) (x : Fin n2 → Bool) :
        wireVal n2 C (n2 + k) x =
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wireVal n2 C i x) := by
      change (run C.gates (List.ofFn x)).getD (n2 + k) false =
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (run C.gates (List.ofFn x)).getD i false)
      have hsplit : C.gates = C.gates.take k ++ [gateAt C k] ++ C.gates.drop (k + 1) := by
        have h1 : C.gates = C.gates.take (k + 1) ++ C.gates.drop (k + 1) :=
          (List.take_append_drop (k + 1) C.gates).symm
        conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hk]
        rfl
      let w0 := run (C.gates.take k) (List.ofFn x)
      have hw0_len : w0.length = n2 + k := by
        dsimp only [w0]; rw [run_len, List.length_ofFn, List.length_take]; omega
      have hw_lt : ∀ i < n2 + k, (run C.gates (List.ofFn x)).getD i false = w0.getD i false := by
        intro i hi
        conv_lhs => rw [← List.take_append_drop k C.gates, run_append]
        exact run_keep (C.gates.drop k) w0 i (by omega)
      conv_lhs => rw [hsplit, run_append, run_append]
      have hstep_len : (run [gateAt C k] w0).length = n2 + k + 1 := by
        rw [run_len, hw0_len, List.length_cons, List.length_nil]
      rw [run_keep (C.gates.drop (k + 1)) _ (n2 + k) (by change n2 + k < (run [gateAt C k] w0).length; omega)]
      change (step w0 (gateAt C k)).getD (n2 + k) false = _
      dsimp only [step]
      rw [← hw0_len, getD_snoc_eq w0 _]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (hw_lt i (hRB k hk i hi)).symm
    have wireVal_or_mem {k a : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
        (ha : a ∈ (gateAt C k).inputs) (x : Fin n2 → Bool) (hva : wireVal n2 C a x = true) :
        wireVal n2 C (n2 + k) x = true := by
      rw [wireVal_gate k hk x, hor]
      change ((gateAt C k).inputs.map fun i => wireVal n2 C i x).any id = true
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩
    have wireVal_and_pair {k a b : ℕ} (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and)
        (hin : (gateAt C k).inputs = [a, b]) (x : Fin n2 → Bool) :
        wireVal n2 C (n2 + k) x = (wireVal n2 C a x && wireVal n2 C b x) := by
      rw [wireVal_gate k hk x, hand, hin, List.map_cons, List.map_cons, List.map_nil]
      exact hand_eval2 _ _
    have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin n2 → Bool)
        (ht : wireVal n2 C t x = true) : wireVal n2 C w x = true := by
      apply hp (fun u => wireVal n2 C u x = true) ht
      intro k hk hor a ha hva
      exact wireVal_or_mem hk hor ha x hva
    have isAO2_gate_inputs {k : ℕ} (hk : k < C.gates.length) :
        ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a < n2 + k ∧ b < n2 + k := by
      have hmem : gateAt C k ∈ C.gates := by
        change C.gates.getD k ⟨GateOp.or, []⟩ ∈ C.gates
        rw [List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      have hlen := hAO2.2.2 (gateAt C k) hmem
      cases hin : (gateAt C k).inputs with
      | nil => rw [hin] at hlen; simp at hlen
      | cons a t1 =>
        cases t1 with
        | nil => rw [hin] at hlen; simp at hlen
        | cons b t2 =>
          cases t2 with
          | nil =>
            have ha := hAO2.2.1 k hk a (by rw [hin]; exact List.mem_cons_self)
            have hb := hAO2.2.1 k hk b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
            exact ⟨a, b, rfl, ha, hb⟩
          | cons _ _ => rw [hin] at hlen; simp at hlen
    let mergeStep : ∀ {α : Type} [DecidableEq α], Finset (Finset α) → α → α → Finset (Finset α) :=
      fun P u v =>
        let hit := P.filter (fun B => u ∈ B ∨ v ∈ B)
        let rest := P.filter (fun B => ¬ (u ∈ B ∨ v ∈ B))
        if hit.Nonempty then insert (hit.biUnion id) rest else P
    let IsPartition : ∀ {α : Type} [DecidableEq α], Finset α → Finset (Finset α) → Prop :=
      fun U P =>
        (∀ B ∈ P, B.Nonempty) ∧
        (∀ B1 ∈ P, ∀ B2 ∈ P, B1 ≠ B2 → Disjoint B1 B2) ∧
        P.biUnion id = U
    have partition_unique_block {α : Type} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
        (hP : IsPartition U P) {x : α} {B1 B2 : Finset α}
        (h1 : B1 ∈ P) (h2 : B2 ∈ P) (hx1 : x ∈ B1) (hx2 : x ∈ B2) : B1 = B2 := by
      by_contra hne
      exact Finset.disjoint_left.mp (hP.2.1 B1 h1 B2 h2 hne) hx1 hx2
    have partition_exists_block {α : Type} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
        (hP : IsPartition U P) {x : α} (hx : x ∈ U) : ∃ B ∈ P, x ∈ B := by
      rw [← hP.2.2, Finset.mem_biUnion] at hx
      obtain ⟨B, hB, hxB⟩ := hx
      exact ⟨B, hB, hxB⟩
    have mergeStep_props {α : Type} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
        (hP : IsPartition U P) {u v : α} (hu : u ∈ U) (hv : v ∈ U) :
        IsPartition U (mergeStep P u v) ∧
        P.card ≤ (mergeStep P u v).card + 1 ∧
        (∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ mergeStep P u v, x ∈ B ∧ y ∈ B) ∧
        (∃ B ∈ mergeStep P u v, u ∈ B ∧ v ∈ B) := by
      obtain ⟨Bu, hBuP, huBu⟩ := partition_exists_block hP hu
      obtain ⟨Bv, hBvP, hvBv⟩ := partition_exists_block hP hv
      let hit := P.filter (fun B => u ∈ B ∨ v ∈ B)
      let rest := P.filter (fun B => ¬ (u ∈ B ∨ v ∈ B))
      have hBu_hit : Bu ∈ hit := Finset.mem_filter.mpr ⟨hBuP, Or.inl huBu⟩
      have hBv_hit : Bv ∈ hit := Finset.mem_filter.mpr ⟨hBvP, Or.inr hvBv⟩
      have hhit_ne : hit.Nonempty := ⟨Bu, hBu_hit⟩
      have hhit_sub : hit ⊆ {Bu, Bv} := by
        intro B hB
        obtain ⟨hBP, hor⟩ := Finset.mem_filter.mp hB
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hor with huB | hvB
        · exact Or.inl (partition_unique_block hP hBP hBuP huB huBu)
        · exact Or.inr (partition_unique_block hP hBP hBvP hvB hvBv)
      have hhit_card : hit.card ≤ 2 :=
        (Finset.card_le_card hhit_sub).trans Finset.card_le_two
      have hmerge_eq : mergeStep P u v = insert (hit.biUnion id) rest := by
        dsimp only [mergeStep]
        simp only [hit, rest, hhit_ne, ↓reduceIte]
      have hnot_mem_rest : hit.biUnion id ∉ rest := by
        intro hmem
        have hno := (Finset.mem_filter.mp hmem).2
        apply hno
        exact Or.inl (Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩)
      have hdisj_hr : Disjoint hit rest := by
        rw [Finset.disjoint_left]
        intro B h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion_hr : hit ∪ rest = P := by
        ext B
        simp only [hit, rest, Finset.mem_union, Finset.mem_filter]
        tauto
      have hpart : IsPartition U (mergeStep P u v) := by
        rw [hmerge_eq]
        refine ⟨?_, ?_, ?_⟩
        · intro B hB
          rcases Finset.mem_insert.mp hB with rfl | hBr
          · exact ⟨u, Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩⟩
          · exact hP.1 B (Finset.mem_filter.mp hBr).1
        · intro B1 h1 B2 h2 hne
          rcases Finset.mem_insert.mp h1 with rfl | h1r <;>
            rcases Finset.mem_insert.mp h2 with rfl | h2r
          · exact (hne rfl).elim
          · rw [Finset.disjoint_left]
            intro x hx1 hx2
            obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx1
            have hB'P := (Finset.mem_filter.mp hB'h).1
            have hB2P := (Finset.mem_filter.mp h2r).1
            have heq := partition_unique_block hP hB'P hB2P hxB' hx2
            subst heq
            exact (Finset.mem_filter.mp h2r).2 (Finset.mem_filter.mp hB'h).2
          · rw [Finset.disjoint_left]
            intro x hx1 hx2
            obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx2
            have hB'P := (Finset.mem_filter.mp hB'h).1
            have hB1P := (Finset.mem_filter.mp h1r).1
            have heq := partition_unique_block hP hB'P hB1P hxB' hx1
            subst heq
            exact (Finset.mem_filter.mp h1r).2 (Finset.mem_filter.mp hB'h).2
          · exact hP.2.1 B1 (Finset.mem_filter.mp h1r).1 B2 (Finset.mem_filter.mp h2r).1 hne
        · rw [Finset.biUnion_insert]
          change hit.biUnion id ∪ rest.biUnion id = U
          ext x
          rw [← hP.2.2, ← hunion_hr]
          simp only [Finset.mem_union, Finset.mem_biUnion, id]
          constructor
          · rintro (⟨B, hB, hx⟩ | ⟨B, hB, hx⟩)
            · exact ⟨B, Or.inl hB, hx⟩
            · exact ⟨B, Or.inr hB, hx⟩
          · rintro ⟨B, hB | hB, hx⟩
            · exact Or.inl ⟨B, hB, hx⟩
            · exact Or.inr ⟨B, hB, hx⟩
      have hcard : P.card ≤ (mergeStep P u v).card + 1 := by
        rw [hmerge_eq, Finset.card_insert_of_notMem hnot_mem_rest, ← hunion_hr,
          Finset.card_union_of_disjoint hdisj_hr]
        omega
      have hmono : ∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ mergeStep P u v, x ∈ B ∧ y ∈ B := by
        rintro x y ⟨B, hBP, hxB, hyB⟩
        rw [hmerge_eq]
        by_cases hhit : u ∈ B ∨ v ∈ B
        · refine ⟨hit.biUnion id, Finset.mem_insert_self _ _, ?_, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨hBP, hhit⟩, hxB⟩
          · exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨hBP, hhit⟩, hyB⟩
        · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hBP, hhit⟩), hxB, hyB⟩
      have hpair : ∃ B ∈ mergeStep P u v, u ∈ B ∧ v ∈ B := by
        rw [hmerge_eq]
        exact ⟨hit.biUnion id, Finset.mem_insert_self _ _,
          Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩,
          Finset.mem_biUnion.mpr ⟨Bv, hBv_hit, hvBv⟩⟩
      exact ⟨hpart, hcard, hmono, hpair⟩
    have mergeFold_props {α : Type} [DecidableEq α] (U : Finset α) (pairs : List (α × α)) :
        ∀ (P : Finset (Finset α)),
          IsPartition U P →
          (∀ pr ∈ pairs, pr.1 ∈ U ∧ pr.2 ∈ U) →
          let Q := pairs.foldl (fun acc pr => mergeStep acc pr.1 pr.2) P
          IsPartition U Q ∧
          P.card ≤ pairs.length + Q.card ∧
          (∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ Q, x ∈ B ∧ y ∈ B) ∧
          (∀ pr ∈ pairs, ∃ B ∈ Q, pr.1 ∈ B ∧ pr.2 ∈ B) := by
      induction pairs with
      | nil =>
        intro P hP _
        exact ⟨hP, by simp, fun _ _ h => h, (fun _ h => by cases h)⟩
      | cons pr rest ih =>
        intro P hP hmem
        have hpr := hmem pr List.mem_cons_self
        have hrest : ∀ pr' ∈ rest, pr'.1 ∈ U ∧ pr'.2 ∈ U :=
          fun pr' h' => hmem pr' (List.mem_cons_of_mem _ h')
        obtain ⟨hP1, hcard1, hmono1, hpair1⟩ := mergeStep_props hP hpr.1 hpr.2
        obtain ⟨hQ, hcard2, hmono2, hpair2⟩ := ih (mergeStep P pr.1 pr.2) hP1 hrest
        refine ⟨hQ, by simp only [List.foldl_cons, List.length_cons]; omega,
          fun x y hxy => hmono2 x y (hmono1 x y hxy), ?_⟩
        intro pr' hpr'
        rcases List.mem_cons.mp hpr' with rfl | hrest'
        · exact hmono2 pr'.1 pr'.2 hpair1
        · exact hpair2 pr' hrest'
    have side_component_bound {X : Type} [Fintype X] [DecidableEq X]
        (wireOf : X → ℕ) (hwire_lt : ∀ x : X, wireOf x < n2)
        (hwire_inj : Function.Injective wireOf)
        (S_gates : Finset (Fin C.gates.length))
        (opWire : Fin C.gates.length → ℕ)
        (hnonempty : ∀ j ∈ S_gates, ∃ x : X, OrPath (opWire j) (wireOf x)) :
        let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
        let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
        let O_S : Finset (Fin C.gates.length) :=
          Finset.univ.filter (fun o =>
            (gateAt C o.val).op = GateOp.or ∧
            2 ≤ (reach (n2 + o.val)).card ∧
            ∃ j ∈ S_gates, OrPath (opWire j) (n2 + o.val))
        E_S.card ≤ O_S.card + S_gates.card := by
      let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
      let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
      let O_S : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun o =>
          (gateAt C o.val).op = GateOp.or ∧
          2 ≤ (reach (n2 + o.val)).card ∧
          ∃ j ∈ S_gates, OrPath (opWire j) (n2 + o.val))
      let pairOf (o : Fin C.gates.length) : Option (X × X) :=
        let a := (gateAt C o.val).inputs.getD 0 0
        let b := (gateAt C o.val).inputs.getD 1 0
        if h : (reach a).Nonempty ∧ (reach b).Nonempty then some (h.1.choose, h.2.choose) else none
      let pairs : List (X × X) := O_S.toList.filterMap pairOf
      have hpairs_len : pairs.length ≤ O_S.card := by
        have h1 := List.length_filterMap_le pairOf O_S.toList
        rw [Finset.length_toList] at h1
        exact h1
      have hpairs_in : ∀ pr ∈ pairs, pr.1 ∈ E_S ∧ pr.2 ∈ E_S := by
        intro pr hpr
        obtain ⟨o, ho_list, hpair_eq⟩ := List.mem_filterMap.mp hpr
        have ho : o ∈ O_S := Finset.mem_toList.mp ho_list
        obtain ⟨hor, _, j, hjS, hjo⟩ := (Finset.mem_filter.mp ho).2
        obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs o.isLt
        have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
        have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
        dsimp only [pairOf] at hpair_eq
        rw [ha_get, hb_get] at hpair_eq
        split_ifs at hpair_eq with hne
        injection hpair_eq with hpr_eq
        rw [← hpr_eq]
        have hu : hne.1.choose ∈ reach a := hne.1.choose_spec
        have hv : hne.2.choose ∈ reach b := hne.2.choose_spec
        have hua : OrPath a (wireOf hne.1.choose) := (Finset.mem_filter.mp hu).2
        have hvb : OrPath b (wireOf hne.2.choose) := (Finset.mem_filter.mp hv).2
        have ha_mem : a ∈ (gateAt C o.val).inputs := by rw [hab]; exact List.mem_cons_self
        have hb_mem : b ∈ (gateAt C o.val).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
        refine ⟨Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            orPath_trans hjo (orPath_step o.isLt hor ha_mem hua)⟩⟩,
          Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            orPath_trans hjo (orPath_step o.isLt hor hb_mem hvb)⟩⟩⟩
      let P0 : Finset (Finset X) := E_S.image (fun x => {x})
      have hP0_part : IsPartition E_S P0 := by
        refine ⟨?_, ?_, ?_⟩
        · intro B hB
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hB
          exact ⟨x, Finset.mem_singleton_self x⟩
        · intro B1 h1 B2 h2 hne
          obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨x2, _, rfl⟩ := Finset.mem_image.mp h2
          rw [Finset.disjoint_singleton]
          intro heq; subst heq; exact hne rfl
        · ext x
          simp only [P0, Finset.mem_biUnion, Finset.mem_image, id]
          constructor
          · rintro ⟨B, ⟨y, hy, rfl⟩, hx⟩
            rw [Finset.mem_singleton.mp hx]; exact hy
          · intro hx
            exact ⟨{x}, ⟨x, hx, rfl⟩, Finset.mem_singleton_self x⟩
      have hP0_card : P0.card = E_S.card := by
        rw [Finset.card_image_of_injective _ (fun a b h => Finset.singleton_injective h)]
      let Q := pairs.foldl (fun acc pr => mergeStep acc pr.1 pr.2) P0
      obtain ⟨hQ_part, hQ_card, _, hQ_pairs⟩ := mergeFold_props E_S pairs P0 hP0_part hpairs_in
      have hsame_wire : ∀ w : ℕ, (∃ j ∈ S_gates, OrPath (opWire j) w) →
          ∀ x1 ∈ reach w, ∀ x2 ∈ reach w, ∃ B ∈ Q, x1 ∈ B ∧ x2 ∈ B := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          rintro ⟨j, hjS, hjw⟩ x1 hx1 x2 hx2
          have hp1 : OrPath w (wireOf x1) := (Finset.mem_filter.mp hx1).2
          have hp2 : OrPath w (wireOf x2) := (Finset.mem_filter.mp hx2).2
          by_cases h12 : x1 = x2
          · subst h12
            have hx1E : x1 ∈ E_S := Finset.mem_biUnion.mpr ⟨j, hjS,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjw hp1⟩⟩
            obtain ⟨B, hBQ, hxB⟩ := partition_exists_block hQ_part hx1E
            exact ⟨B, hBQ, hxB, hxB⟩
          · have hne_w : wireOf x1 ≠ wireOf x2 := fun h => h12 (hwire_inj h)
            have hstep_ex : ∃ k < C.gates.length, w = n2 + k ∧ (gateAt C k).op = GateOp.or := by
              rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
              · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
                · exact (hne_w h2).elim
                · exact ⟨k, hk, hwk, hor⟩
              · exact ⟨k, hk, hwk, hor⟩
            obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
            let o : Fin C.gates.length := ⟨k, hk⟩
            have h2card : 2 ≤ (reach (n2 + o.val)).card := by
              rw [← hwk]
              exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
            have ho_mem : o ∈ O_S :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hor, h2card, j, hjS, hwk ▸ hjw⟩
            obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := isAO2_gate_inputs hk
            have ha_mem : a ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_self
            have hb_mem : b ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
            have hja : OrPath (opWire j) a :=
              orPath_trans hjw (hwk ▸ orPath_step hk hor ha_mem (orPath_refl a))
            have hjb : OrPath (opWire j) b :=
              orPath_trans hjw (hwk ▸ orPath_step hk hor hb_mem (orPath_refl b))
            have hsplit_x : ∀ x ∈ reach w, x ∈ reach a ∨ x ∈ reach b := by
              intro x hx
              have hpx : OrPath w (wireOf x) := (Finset.mem_filter.mp hx).2
              have hlt_x : wireOf x < n2 := hwire_lt x
              rcases orPath_cases hpx with hxeq | ⟨k', _, hwk', _, c, hc, hpc⟩
              · omega
              · have hkeq : k' = k := by omega
                subst hkeq
                rw [hab] at hc
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl
                · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
                · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
            rcases hsplit_x x1 hx1 with h1a | h1b <;> rcases hsplit_x x2 hx2 with h2a | h2b
            · exact ih a (by omega) ⟨j, hjS, hja⟩ x1 h1a x2 h2a
            · have hne_ab : (reach a).Nonempty ∧ (reach b).Nonempty := ⟨⟨x1, h1a⟩, ⟨x2, h2b⟩⟩
              have hpair_in : (hne_ab.1.choose, hne_ab.2.choose) ∈ pairs := by
                apply List.mem_filterMap.mpr
                refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
                dsimp only [pairOf]
                have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
                rw [ha_get, hb_get]; split_ifs; rfl
              obtain ⟨B1, hB1Q, hx1B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x1 h1a hne_ab.1.choose hne_ab.1.choose_spec
              obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
              obtain ⟨B3, hB3Q, hvB3, hx2B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x2 h2b
              have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
              have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
              subst h12B; subst h23B
              exact ⟨B1, hB1Q, hx1B1, hx2B3⟩
            · have hne_ab : (reach a).Nonempty ∧ (reach b).Nonempty := ⟨⟨x2, h2a⟩, ⟨x1, h1b⟩⟩
              have hpair_in : (hne_ab.1.choose, hne_ab.2.choose) ∈ pairs := by
                apply List.mem_filterMap.mpr
                refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
                dsimp only [pairOf]
                have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
                rw [ha_get, hb_get]; split_ifs; rfl
              obtain ⟨B1, hB1Q, hx2B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x2 h2a hne_ab.1.choose hne_ab.1.choose_spec
              obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
              obtain ⟨B3, hB3Q, hvB3, hx1B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x1 h1b
              have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
              have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
              subst h12B; subst h23B
              exact ⟨B1, hB1Q, hx1B3, hx2B1⟩
            · exact ih b (by omega) ⟨j, hjS, hjb⟩ x1 h1b x2 h2b
      let blk (j : Fin C.gates.length) : Finset X :=
        if hj : j ∈ S_gates then
          have hx : (hnonempty j hj).choose ∈ E_S :=
            Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnonempty j hj).choose_spec⟩⟩
          (partition_exists_block hQ_part hx).choose
        else ∅
      have hQ_sub : Q ⊆ S_gates.image blk := by
        intro B hBQ
        obtain ⟨x, hxB⟩ := hQ_part.1 B hBQ
        have hxE : x ∈ E_S := by
          rw [← hQ_part.2.2]
          exact Finset.mem_biUnion.mpr ⟨B, hBQ, hxB⟩
        obtain ⟨j, hjS, hxj⟩ := Finset.mem_biUnion.mp hxE
        refine Finset.mem_image.mpr ⟨j, hjS, ?_⟩
        let x0 := (hnonempty j hjS).choose
        have hx0j : x0 ∈ reach (opWire j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnonempty j hjS).choose_spec⟩
        obtain ⟨B', hB'Q, hxB', hx0B'⟩ := hsame_wire (opWire j) ⟨j, hjS, orPath_refl _⟩ x hxj x0 hx0j
        have hBB' := partition_unique_block hQ_part hBQ hB'Q hxB hxB'
        have hblk_spec : blk j ∈ Q ∧ x0 ∈ blk j := by
          dsimp only [blk]
          simp only [hjS, ↓reduceDIte]
          have hx0E : x0 ∈ E_S := Finset.mem_biUnion.mpr ⟨j, hjS, hx0j⟩
          exact (partition_exists_block hQ_part hx0E).choose_spec
        have hB'blk := partition_unique_block hQ_part hB'Q hblk_spec.1 hx0B' hblk_spec.2
        exact (hBB'.trans hB'blk).symm
      have hQ_le_S : Q.card ≤ S_gates.card :=
        (Finset.card_le_card hQ_sub).trans Finset.card_image_le
      change P0.card ≤ pairs.length + Q.card at hQ_card
      change E_S.card ≤ O_S.card + S_gates.card
      omega
    let pts (w : ℕ) : Finset (Fin N) := Finset.univ.filter (fun p => OrPath w p.val)
    let lns (w : ℕ) : Finset (Fin N) := Finset.univ.filter (fun l => OrPath w (N + l.val))
    have hno_pts_only (x : Fin n2 → Bool) (h0 : ∀ l : Fin N, x (Fin.natAdd N l) = false) :
        wireVal n2 C C.output x = false := by
      have hcard0 : Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } = 0 :=
        Fintype.card_eq_zero_iff.mpr ⟨fun l => by have hl := l.2; rw [h0 l.1] at hl; cases hl⟩
      have hnoE : ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
        rintro ⟨_, l, _, _, hl⟩; rw [h0 l] at hl; cases hl
      exact hFalseC x ⟨by omega, hnoE⟩
    have hno_lns_only2 (l1 l2 : Fin N) :
        wireVal n2 C C.output (fun i : Fin n2 => decide (i = Fin.natAdd N l1 ∨ i = Fin.natAdd N l2)) = false := by
      let x : Fin n2 → Bool := fun i => decide (i = Fin.natAdd N l1 ∨ i = Fin.natAdd N l2)
      have hcard2 : Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ 2 := by
        rw [Fintype.card_subtype]
        have hsub : Finset.univ.filter (fun l : Fin N => x (Fin.natAdd N l) = true) ⊆ {l1, l2} := by
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hl with h | h
          · exact Or.inl (Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega))
          · exact Or.inr (Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega))
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      have hnoE : ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
        rintro ⟨p, _, _, hp, _⟩
        simp only [x, decide_eq_true_eq] at hp
        rcases hp with h | h <;> (have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega)
      exact hFalseC x ⟨by omega, hnoE⟩
    have hedge_covered : ∀ p l : Fin N, (p, l) ∈ E →
        ∃ j : Fin C.gates.length, (gateAt C j.val).op = GateOp.and ∧
          OrPath C.output (n2 + j.val) ∧
          ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
            ((OrPath a p.val ∧ OrPath b (N + l.val)) ∨
             (OrPath a (N + l.val) ∧ OrPath b p.val)) := by
      intro p l hpl
      obtain ⟨j, a, b, handOn, htop, hpa, hlb⟩ := hall p l ((hmem_E p l).mp hpl)
      obtain ⟨⟨hjlt, hjand⟩, hor_ab⟩ := handOn
      obtain ⟨a0, b0, hab0, _, _⟩ := isAO2_gate_inputs hjlt
      have hin0 : in0 C j = a0 := by change (gateAt C j).inputs.getD 0 0 = a0; rw [hab0]; rfl
      have hin1 : in1 C j = b0 := by change (gateAt C j).inputs.getD 1 0 = b0; rw [hab0]; rfl
      refine ⟨⟨j, hjlt⟩, hjand, orp_to_orPath htop, a0, b0, hab0, ?_⟩
      rcases hor_ab with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
        exact Or.inl ⟨orp_to_orPath hpa, orp_to_orPath hlb⟩
      · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
        exact Or.inr ⟨orp_to_orPath hlb, orp_to_orPath hpa⟩
    let Tstar : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun j =>
        (gateAt C j.val).op = GateOp.and ∧
        OrPath C.output (n2 + j.val) ∧
        ∃ p l : Fin N, ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
          ((OrPath a p.val ∧ OrPath b (N + l.val)) ∨
           (OrPath a (N + l.val) ∧ OrPath b p.val)))
    let pWire (j : Fin C.gates.length) : ℕ :=
      let a := (gateAt C j.val).inputs.getD 0 0
      let b := (gateAt C j.val).inputs.getD 1 0
      if (pts a).Nonempty then a else b
    let lWire (j : Fin C.gates.length) : ℕ :=
      let a := (gateAt C j.val).inputs.getD 0 0
      let b := (gateAt C j.val).inputs.getD 1 0
      if (pts a).Nonempty then b else a
    let pSide (j : Fin C.gates.length) : Finset (Fin N) := pts (pWire j)
    let lSide (j : Fin C.gates.length) : Finset (Fin N) := lns (lWire j)
    have hTstar_props : ∀ j ∈ Tstar,
        (gateAt C j.val).op = GateOp.and ∧
        OrPath C.output (n2 + j.val) ∧
        (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
        lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
        (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) ∧
        ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
      intro j hj
      obtain ⟨hand, htop, p0, l0, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
      have ha_get : (gateAt C j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt C j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
      have hand_sound : ∀ x : Fin n2 → Bool,
          wireVal n2 C a x = true → wireVal n2 C b x = true → wireVal n2 C C.output x = true := by
        intro x hxa hxb
        apply orPath_sound htop x
        rw [wireVal_and_pair j.isLt hand hab x, hxa, hxb]
        rfl
      have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
        rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
        let x : Fin n2 → Bool := fun i => decide (i = Fin.castAdd N p1 ∨ i = Fin.castAdd N p2)
        have h1 : wireVal n2 C p1.val x = true := by
          have := wireVal_input (Fin.castAdd N p1) x; simpa [x] using this
        have h2 : wireVal n2 C p2.val x = true := by
          have := wireVal_input (Fin.castAdd N p2) x; simpa [x] using this
        have ht := hand_sound x (orPath_sound (Finset.mem_filter.mp hp1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hp2).2 x h2)
        have hf := hno_pts_only x (fun l => by
          simp only [x, decide_eq_false_iff_not]
          rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
        rw [ht] at hf; cases hf
      have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
        rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
        let x : Fin n2 → Bool := fun i => decide (i = Fin.natAdd N l1 ∨ i = Fin.natAdd N l2)
        have h1 : wireVal n2 C (N + l1.val) x = true := by
          have hv := wireVal_input (Fin.natAdd N l1) x
          rw [Fin.val_natAdd] at hv
          simpa only [x, true_or, decide_true] using hv
        have h2 : wireVal n2 C (N + l2.val) x = true := by
          have hv := wireVal_input (Fin.natAdd N l2) x
          rw [Fin.val_natAdd] at hv
          simpa only [x, or_true, decide_true] using hv
        have ht := hand_sound x (orPath_sound (Finset.mem_filter.mp hl1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hl2).2 x h2)
        have hf := hno_lns_only2 l1 l2
        rw [ht] at hf; cases hf
      have hbiclique : ∀ (p l : Fin N),
          ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → (p, l) ∈ E := by
        intro p l hpl
        let x : Fin n2 → Bool := fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
        have hxp : wireVal n2 C p.val x = true := by
          have hv := wireVal_input (Fin.castAdd N p) x
          rw [Fin.val_castAdd] at hv
          simpa only [x, true_or, decide_true] using hv
        have hxl : wireVal n2 C (N + l.val) x = true := by
          have hv := wireVal_input (Fin.natAdd N l) x
          rw [Fin.val_natAdd] at hv
          simpa only [x, or_true, decide_true] using hv
        have hout_t : wireVal n2 C C.output x = true := by
          rcases hpl with ⟨hpa, hlb⟩ | ⟨hpb, hla⟩
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hpa).2 x hxp)
              (orPath_sound (Finset.mem_filter.mp hlb).2 x hxl)
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hla).2 x hxl)
              (orPath_sound (Finset.mem_filter.mp hpb).2 x hxp)
        by_contra hnotE
        have hnotI : ¬ I p l := fun hI => hnotE ((hmem_E p l).mpr hI)
        have hcard1 : Fintype.card { l' : Fin N // x (Fin.natAdd N l') = true } ≤ 1 := by
          rw [Fintype.card_subtype]
          have hsub : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) ⊆ {l} := by
            intro l' hl'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl'
            simp only [Finset.mem_singleton]
            rcases hl' with h1 | h2
            · have := congrArg Fin.val h1; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
            · exact Fin.ext (by have := congrArg Fin.val h2; simp only [Fin.val_natAdd] at this; omega)
          exact (Finset.card_le_card hsub).trans (by simp only [Finset.card_singleton, Nat.le_refl])
        have hnoE : ¬ ∃ p' l' : Fin N, I p' l' ∧ x (Fin.castAdd N p') = true ∧ x (Fin.natAdd N l') = true := by
          rintro ⟨p', l', hI', hp', hl'⟩
          simp only [x, decide_eq_true_eq] at hp' hl'
          have hp_eq : p' = p := by
            rcases hp' with h1 | h2
            · exact Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h1)
            · have := congrArg Fin.val h2; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
          have hl_eq : l' = l := by
            rcases hl' with h1 | h2
            · have := congrArg Fin.val h1; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
            · exact Fin.ext (by have := congrArg Fin.val h2; simp only [Fin.val_natAdd] at this; omega)
          rw [hp_eq, hl_eq] at hI'
          exact hnotI hI'
        have hf : wireVal n2 C C.output x = false := hFalseC x ⟨by omega, hnoE⟩
        rw [hout_t] at hf; cases hf
      have hsides : (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
          lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
          (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) := by
        rcases hlr0 with ⟨hpa, hlb⟩ | ⟨hla, hpb⟩
        · have hpa_ne : (pts a).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩⟩
          have hlb_ne : (lns b).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlb⟩⟩
          have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
          have hlW : lWire j = b := by dsimp only [lWire]; simp only [ha_get, hb_get, hpa_ne, ↓reduceIte]
          have hla_em : lns a = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨h, hlb_ne⟩)
          have hpb_em : pts b = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_pts ⟨hpa_ne, h⟩)
          refine ⟨by simpa [pSide, hpW] using hpa_ne, by simpa [lSide, hlW] using hlb_ne,
            by rw [hpW]; exact hla_em, by rw [hlW]; exact hpb_em, ?_⟩
          intro p hp l hl
          rw [show pSide j = pts a by simp [pSide, hpW]] at hp
          rw [show lSide j = lns b by simp [lSide, hlW]] at hl
          exact hbiclique p l (Or.inl ⟨hp, hl⟩)
        · have hla_ne : (lns a).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩⟩
          have hpb_ne : (pts b).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩⟩
          have hpa_not : ¬ (pts a).Nonempty := fun h => hno_both_pts ⟨h, hpb_ne⟩
          have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
          have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
          have hlb_em : lns b = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨hla_ne, h⟩)
          have hpa_em : pts a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpa_not
          refine ⟨by simpa [pSide, hpW] using hpb_ne, by simpa [lSide, hlW] using hla_ne,
            by rw [hpW]; exact hlb_em, by rw [hlW]; exact hpa_em, ?_⟩
          intro p hp l hl
          rw [show pSide j = pts b by simp [pSide, hpW]] at hp
          rw [show lSide j = lns a by simp [lSide, hlW]] at hl
          exact hbiclique p l (Or.inr ⟨hp, hl⟩)
      have hstar : (pSide j).card = 1 ∨ (lSide j).card = 1 := by
        have hp1 : 1 ≤ (pSide j).card := Finset.card_pos.mpr hsides.1
        have hl1 : 1 ≤ (lSide j).card := Finset.card_pos.mpr hsides.2.1
        by_contra hneither
        have hp2 : 1 < (pSide j).card := by omega
        have hl2 : 1 < (lSide j).card := by omega
        obtain ⟨p1, hp1m, p2, hp2m, hpne⟩ := Finset.one_lt_card.mp hp2
        obtain ⟨l1, hl1m, l2, hl2m, hlne⟩ := Finset.one_lt_card.mp hl2
        exact hNoC4 p1 p2 l1 l2 hpne hlne
          ⟨(hmem_E p1 l1).mp (hsides.2.2.2.2 p1 hp1m l1 hl1m),
           (hmem_E p1 l2).mp (hsides.2.2.2.2 p1 hp1m l2 hl2m),
           (hmem_E p2 l1).mp (hsides.2.2.2.2 p2 hp2m l1 hl1m),
           (hmem_E p2 l2).mp (hsides.2.2.2.2 p2 hp2m l2 hl2m)⟩
      exact ⟨hand, htop, hsides.1, hsides.2.1, hsides.2.2.1, hsides.2.2.2.1, hsides.2.2.2.2, hstar⟩
    have hE_in_Tstar : ∀ p l : Fin N, (p, l) ∈ E → ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
      intro p l hpl
      obtain ⟨j, hand, htop, a, b, hab, hlr⟩ := hedge_covered p l hpl
      have hjT : j ∈ Tstar := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hand, htop, p, l, a, b, hab, hlr⟩
      have hprops := hTstar_props j hjT
      have ha_get : (gateAt C j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt C j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
      refine ⟨j, hjT, ?_⟩
      rcases hlr with ⟨hpa, hlb⟩ | ⟨hla, hpb⟩
      · have hpa_m : p ∈ pts a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩
        have hlb_m : l ∈ lns b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlb⟩
        have hpa_ne : (pts a).Nonempty := ⟨p, hpa_m⟩
        have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
        have hlW : lWire j = b := by dsimp only [lWire]; simp only [ha_get, hb_get, hpa_ne, ↓reduceIte]
        exact ⟨by simpa [pSide, hpW] using hpa_m, by simpa [lSide, hlW] using hlb_m⟩
      · have hla_m : l ∈ lns a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩
        have hpb_m : p ∈ pts b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩
        have hpa_not : ¬ (pts a).Nonempty := by
          intro hpa_ne
          have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
          have hlem := hprops.2.2.2.2.1
          rw [hpW] at hlem; rw [hlem] at hla_m; cases hla_m
        have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
        have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
        exact ⟨by simpa [pSide, hpW] using hpb_m, by simpa [lSide, hlW] using hla_m⟩
    let Tpt : Finset (Fin C.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
    let Tln : Finset (Fin C.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
    have hTpt_Tln_disj : Disjoint Tpt Tln := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hTpt_Tln_union : Tpt ∪ Tln = Tstar := by
      ext j; simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]; tauto
    have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
      rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
    let centerP (j : Fin C.gates.length) : Fin N :=
      if h : (pSide j).Nonempty then h.choose else (Finset.nonempty_iff_ne_empty.mpr hEempty).choose.1
    let centerL (j : Fin C.gates.length) : Fin N :=
      if h : (lSide j).Nonempty then h.choose else (Finset.nonempty_iff_ne_empty.mpr hEempty).choose.2
    have hcenterP_eq : ∀ j ∈ Tpt, ∀ p ∈ pSide j, p = centerP j := by
      intro j hj p hp
      have hjT := (Finset.mem_filter.mp hj).1
      have hcard1 := (Finset.mem_filter.mp hj).2
      have hne := (hTstar_props j hjT).2.2.1
      have hmem_c : centerP j ∈ pSide j := by
        dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
      exact Finset.card_le_one.mp (le_of_eq hcard1) p hp (centerP j) hmem_c
    have hcenterL_eq : ∀ j ∈ Tln, ∀ l ∈ lSide j, l = centerL j := by
      intro j hj l hl
      have hjT := (Finset.mem_filter.mp hj).1
      have hne1 := (Finset.mem_filter.mp hj).2
      have hprops := hTstar_props j hjT
      have hcard1 : (lSide j).card = 1 := by
        rcases hprops.2.2.2.2.2.2.2 with h | h
        · exact (hne1 h).elim
        · exact h
      have hne := hprops.2.2.2.1
      have hmem_c : centerL j ∈ lSide j := by
        dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
      exact Finset.card_le_one.mp (le_of_eq hcard1) l hl (centerL j) hmem_c
    have hcenterP_mem : ∀ j ∈ Tpt, centerP j ∈ pSide j := by
      intro j hj
      have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.1
      dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
    have hcenterL_mem : ∀ j ∈ Tln, centerL j ∈ lSide j := by
      intro j hj
      have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.2.1
      dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
    let A : Finset (Fin N) := Tpt.image centerP
    let B : Finset (Fin N) := Tln.image centerL
    let Otop : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        OrPath C.output (n2 + o.val) ∧
        ∃ a ∈ Tstar, OrPath (n2 + o.val) (n2 + a.val))
    have hOtop_disj_Tstar : Disjoint Otop Tstar := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      have hor := (Finset.mem_filter.mp h1).2.1
      have hand := (hTstar_props j h2).1
      rw [hor] at hand; cases hand
    have hTstar_le_Otop : Tstar.card ≤ Otop.card + 1 := by
      by_cases hle1 : Tstar.card ≤ 1
      · omega
      · have hlt : 1 < Tstar.card := by omega
        obtain ⟨a1, ha1, a2, ha2, hne12⟩ := Finset.one_lt_card.mp hlt
        have hop1 := (hTstar_props a1 ha1).2.1
        have hop2 := (hTstar_props a2 ha2).2.1
        have hroot_ex : ∃ root ∈ Otop, C.output = n2 + root.val := by
          rcases orPath_cases hop1 with heq1 | ⟨k, hk, hok, hork, _, _, _⟩
          · rcases orPath_cases hop2 with heq2 | ⟨k, hk, hok, hork, _, _, _⟩
            · have : a1.val = a2.val := by omega
              exact (hne12 (Fin.ext this)).elim
            · have : k = a1.val := by omega
              subst this
              have hand1 := (hTstar_props a1 ha1).1
              rw [hork] at hand1; cases hand1
          · refine ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hork,
              hok ▸ orPath_refl _, a1, ha1, hok ▸ hop1⟩, hok⟩
        obtain ⟨root, hrootO, hroot_eq⟩ := hroot_ex
        let H := Otop ∪ Tstar
        have hrootH : root ∈ H := Finset.mem_union_left _ hrootO
        have hH_card : H.card = Otop.card + Tstar.card :=
          Finset.card_union_of_disjoint hOtop_disj_Tstar
        have hpar_ex : ∀ x ∈ H.erase root, ∃ y ∈ Otop, n2 + x.val ∈ (gateAt C y.val).inputs := by
          intro x hx
          have hxne : x ≠ root := (Finset.mem_erase.mp hx).1
          have hxH : x ∈ H := (Finset.mem_erase.mp hx).2
          have hx_out : OrPath C.output (n2 + x.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.1
            · exact (hTstar_props x hT).2.1
          have hx_a : ∃ a ∈ Tstar, OrPath (n2 + x.val) (n2 + a.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.2
            · exact ⟨x, hT, orPath_refl _⟩
          have hne_out : C.output ≠ n2 + x.val := by
            rw [hroot_eq]; intro h; exact hxne (Fin.ext (by omega))
          obtain ⟨y, hy, hory, hpy, hxin⟩ := orPath_parent hx_out hne_out
          obtain ⟨a, haT, hxa⟩ := hx_a
          refine ⟨⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hory, hpy,
            a, haT, orPath_step hy hory hxin hxa⟩, hxin⟩
        let par (x : Fin C.gates.length) : Fin C.gates.length :=
          if hx : x ∈ H.erase root then (hpar_ex x hx).choose else root
        have hpar_mem : ∀ x ∈ H.erase root, par x ∈ Otop := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.1
        have hpar_in : ∀ x ∈ H.erase root, n2 + x.val ∈ (gateAt C (par x).val).inputs := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.2
        have hfiber_le2 : ∀ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ 2 := by
          intro y _
          let F := (H.erase root).filter (fun x => par x = y)
          have hsub : F.image (fun x : Fin C.gates.length => n2 + x.val) ⊆ (gateAt C y.val).inputs.toFinset := by
            intro w hw
            obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hw
            obtain ⟨hxH, hxy⟩ := Finset.mem_filter.mp hxF
            rw [List.mem_toFinset, ← hxy]
            exact hpar_in x hxH
          have hinj : Function.Injective (fun x : Fin C.gates.length => n2 + x.val) := by
            intro a b h; dsimp only at h; exact Fin.ext (by omega)
          have h1 : F.card = (F.image (fun x : Fin C.gates.length => n2 + x.val)).card :=
            (Finset.card_image_of_injective F hinj).symm
          have h2 : (F.image (fun x : Fin C.gates.length => n2 + x.val)).card ≤ ((gateAt C y.val).inputs.toFinset).card :=
            Finset.card_le_card hsub
          have h3 : ((gateAt C y.val).inputs.toFinset).card ≤ (gateAt C y.val).inputs.length :=
            List.toFinset_card_le _
          have h4 : (gateAt C y.val).inputs.length = 2 := by
            obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs y.isLt
            rw [hab]; rfl
          change F.card ≤ 2
          omega
        have hsum_eq : (H.erase root).card = ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card :=
          Finset.card_eq_sum_card_fiberwise (f := par) hpar_mem
        have hsum_le : ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ ∑ _y ∈ Otop, 2 :=
          Finset.sum_le_sum hfiber_le2
        simp only [Finset.sum_const, smul_eq_mul] at hsum_le
        have herase : (H.erase root).card + 1 = H.card := Finset.card_erase_add_one hrootH
        omega
    let Tpt_p (p : Fin N) : Finset (Fin C.gates.length) := Tpt.filter (fun j => centerP j = p)
    let E_p (p : Fin N) : Finset (Fin N) := (Tpt_p p).biUnion lSide
    let Obot_p (p : Fin N) : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        2 ≤ (lns (n2 + o.val)).card ∧
        ∃ j ∈ Tpt_p p, OrPath (lWire j) (n2 + o.val))
    let Tln_l (l : Fin N) : Finset (Fin C.gates.length) := Tln.filter (fun j => centerL j = l)
    let E_l (l : Fin N) : Finset (Fin N) := (Tln_l l).biUnion pSide
    let Obot_l (l : Fin N) : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        2 ≤ (pts (n2 + o.val)).card ∧
        ∃ j ∈ Tln_l l, OrPath (pWire j) (n2 + o.val))
    have hEp_bound : ∀ p ∈ A, (E_p p).card ≤ (Obot_p p).card + (Tpt_p p).card := by
      intro p _
      exact side_component_bound
        (fun l : Fin N => N + l.val) (fun l => by omega)
        (fun l1 l2 h => Fin.ext (by dsimp only at h; omega))
        (Tpt_p p) lWire
        (fun j hj => by
          obtain ⟨l, hl⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.2.1
          exact ⟨l, (Finset.mem_filter.mp hl).2⟩)
    have hEl_bound : ∀ l ∈ B, (E_l l).card ≤ (Obot_l l).card + (Tln_l l).card := by
      intro l _
      exact side_component_bound
        (fun p : Fin N => p.val) (fun p => by omega)
        (fun p1 p2 h => Fin.ext h)
        (Tln_l l) pWire
        (fun j hj => by
          obtain ⟨p, hp⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.1
          exact ⟨p, (Finset.mem_filter.mp hp).2⟩)
    have hObot_p_disj : Set.PairwiseDisjoint (A : Set (Fin N)) Obot_p := by
      intro p1 _ p2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro o h1 h2
      obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
      obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (lns (n2 + o.val)).card)
      have hj1pt := (Finset.mem_filter.mp hj1).1
      have hj1p := (Finset.mem_filter.mp hj1).2
      have hj2pt := (Finset.mem_filter.mp hj2).1
      have hj2p := (Finset.mem_filter.mp hj2).2
      have hp1_in : p1 ∈ pSide j1 := hj1p ▸ hcenterP_mem j1 hj1pt
      have hp2_in : p2 ∈ pSide j2 := hj2p ▸ hcenterP_mem j2 hj2pt
      have hl1_j1 : l1 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo1 (Finset.mem_filter.mp hl1).2⟩
      have hl2_j1 : l2 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo1 (Finset.mem_filter.mp hl2).2⟩
      have hl1_j2 : l1 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo2 (Finset.mem_filter.mp hl1).2⟩
      have hl2_j2 : l2 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo2 (Finset.mem_filter.mp hl2).2⟩
      have hpr1 := (hTstar_props j1 (Finset.mem_filter.mp hj1pt).1).2.2.2.2.2.2.1
      have hpr2 := (hTstar_props j2 (Finset.mem_filter.mp hj2pt).1).2.2.2.2.2.2.1
      exact hNoC4 p1 p2 l1 l2 hne hlne
        ⟨(hmem_E p1 l1).mp (hpr1 p1 hp1_in l1 hl1_j1),
         (hmem_E p1 l2).mp (hpr1 p1 hp1_in l2 hl2_j1),
         (hmem_E p2 l1).mp (hpr2 p2 hp2_in l1 hl1_j2),
         (hmem_E p2 l2).mp (hpr2 p2 hp2_in l2 hl2_j2)⟩
    have hObot_l_disj : Set.PairwiseDisjoint (B : Set (Fin N)) Obot_l := by
      intro l1 _ l2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro o h1 h2
      obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (pts (n2 + o.val)).card)
      have hj1ln := (Finset.mem_filter.mp hj1).1
      have hj1l := (Finset.mem_filter.mp hj1).2
      have hj2ln := (Finset.mem_filter.mp hj2).1
      have hj2l := (Finset.mem_filter.mp hj2).2
      have hl1_in : l1 ∈ lSide j1 := hj1l ▸ hcenterL_mem j1 hj1ln
      have hl2_in : l2 ∈ lSide j2 := hj2l ▸ hcenterL_mem j2 hj2ln
      have hp1_j1 : p1 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo1 (Finset.mem_filter.mp hp1).2⟩
      have hp2_j1 : p2 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo1 (Finset.mem_filter.mp hp2).2⟩
      have hp1_j2 : p1 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo2 (Finset.mem_filter.mp hp1).2⟩
      have hp2_j2 : p2 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjo2 (Finset.mem_filter.mp hp2).2⟩
      have hpr1 := (hTstar_props j1 (Finset.mem_filter.mp hj1ln).1).2.2.2.2.2.2.1
      have hpr2 := (hTstar_props j2 (Finset.mem_filter.mp hj2ln).1).2.2.2.2.2.2.1
      exact hNoC4 p1 p2 l1 l2 hpne hne
        ⟨(hmem_E p1 l1).mp (hpr1 p1 hp1_j1 l1 hl1_in),
         (hmem_E p1 l2).mp (hpr2 p1 hp1_j2 l2 hl2_in),
         (hmem_E p2 l1).mp (hpr1 p2 hp2_j1 l1 hl1_in),
         (hmem_E p2 l2).mp (hpr2 p2 hp2_j2 l2 hl2_in)⟩
    let ObotA := A.biUnion Obot_p
    let ObotB := B.biUnion Obot_l
    have hObotAB_disj : Disjoint ObotA ObotB := by
      rw [Finset.disjoint_left]
      intro o hA hB
      obtain ⟨p, _, hoA⟩ := Finset.mem_biUnion.mp hA
      obtain ⟨l, _, hoB⟩ := Finset.mem_biUnion.mp hB
      have hcard_l := (Finset.mem_filter.mp hoA).2.2.1
      obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (n2 + o.val)).card)
      obtain ⟨j, hj, hjo⟩ := (Finset.mem_filter.mp hoB).2.2.2
      have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      have hlem := (hTstar_props j hjT).2.2.2.2.1
      have hl0_in : l0 ∈ lns (pWire j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo (Finset.mem_filter.mp hl0).2⟩
      rw [hlem] at hl0_in; cases hl0_in
    let Obot := ObotA ∪ ObotB
    have hObot_card : Obot.card = (∑ p ∈ A, (Obot_p p).card) + (∑ l ∈ B, (Obot_l l).card) := by
      rw [Finset.card_union_of_disjoint hObotAB_disj,
        Finset.card_biUnion hObot_p_disj, Finset.card_biUnion hObot_l_disj]
    have hObot_disj_Tstar : Disjoint Obot Tstar := by
      rw [Finset.disjoint_left]
      intro o h1 h2
      have hand := (hTstar_props o h2).1
      rcases Finset.mem_union.mp h1 with hA | hB
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
        have hor := (Finset.mem_filter.mp ho).2.1
        rw [hor] at hand; cases hand
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
        have hor := (Finset.mem_filter.mp ho).2.1
        rw [hor] at hand; cases hand
    have hObot_disj_Otop : Disjoint Obot Otop := by
      rw [Finset.disjoint_left]
      intro o hbot htop
      have hop_out := (Finset.mem_filter.mp htop).2.2.1
      rcases Finset.mem_union.mp hbot with hA | hB
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
        have hcard_l := (Finset.mem_filter.mp ho).2.2.1
        obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (n2 + o.val)).card)
        have hop := orPath_trans hop_out (Finset.mem_filter.mp hl0).2
        let x : Fin n2 → Bool := fun i => decide (i = Fin.natAdd N l0 ∨ i = Fin.natAdd N l0)
        have hx_l : wireVal n2 C (N + l0.val) x = true := by
          have hv := wireVal_input (Fin.natAdd N l0) x
          rw [Fin.val_natAdd] at hv
          simpa only [x, true_or, decide_true] using hv
        have ht := orPath_sound hop x hx_l
        have hf := hno_lns_only2 l0 l0
        rw [ht] at hf; cases hf
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
        have hcard_p := (Finset.mem_filter.mp ho).2.2.1
        obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < (pts (n2 + o.val)).card)
        have hop := orPath_trans hop_out (Finset.mem_filter.mp hp0).2
        let x : Fin n2 → Bool := fun i => decide (i = Fin.castAdd N p0)
        have hx_p : wireVal n2 C p0.val x = true := by
          have := wireVal_input (Fin.castAdd N p0) x; simpa [x] using this
        have ht := orPath_sound hop x hx_p
        have hf := hno_pts_only x (fun l' => by
          simp only [x, decide_eq_false_iff_not]
          intro h; have := congrArg Fin.val h; simp at this; omega)
        rw [ht] at hf; cases hf
    have hTpt_sum : ∑ p ∈ A, (Tpt_p p).card = Tpt.card :=
      (Finset.card_eq_sum_card_fiberwise (f := centerP) (fun j hj => Finset.mem_image_of_mem centerP hj)).symm
    have hTln_sum : ∑ l ∈ B, (Tln_l l).card = Tln.card :=
      (Finset.card_eq_sum_card_fiberwise (f := centerL) (fun j hj => Finset.mem_image_of_mem centerL hj)).symm
    have hE_sub : E ⊆ A.biUnion (fun p => (E_p p).image (fun l => (p, l))) ∪
        B.biUnion (fun l => (E_l l).image (fun p => (p, l))) := by
      intro e he
      obtain ⟨j, hjT, hpj, hlj⟩ := hE_in_Tstar e.1 e.2 he
      by_cases h1 : (pSide j).card = 1
      · have hjpt : j ∈ Tpt := Finset.mem_filter.mpr ⟨hjT, h1⟩
        have hcp : centerP j = e.1 := (hcenterP_eq j hjpt e.1 hpj).symm
        apply Finset.mem_union_left
        refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_image.mpr ⟨j, hjpt, hcp⟩, ?_⟩
        refine Finset.mem_image.mpr ⟨e.2, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjpt, hcp⟩, hlj⟩, rfl⟩
      · have hjln : j ∈ Tln := Finset.mem_filter.mpr ⟨hjT, h1⟩
        have hcl : centerL j = e.2 := (hcenterL_eq j hjln e.2 hlj).symm
        apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_image.mpr ⟨j, hjln, hcl⟩, ?_⟩
        refine Finset.mem_image.mpr ⟨e.1, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjln, hcl⟩, hpj⟩, rfl⟩
    have hE_le_sum : E.card ≤ (∑ p ∈ A, (E_p p).card) + (∑ l ∈ B, (E_l l).card) := by
      calc E.card
          ≤ (A.biUnion (fun p => (E_p p).image (fun l => (p, l))) ∪
              B.biUnion (fun l => (E_l l).image (fun p => (p, l)))).card := Finset.card_le_card hE_sub
        _ ≤ (A.biUnion (fun p => (E_p p).image (fun l => (p, l)))).card +
              (B.biUnion (fun l => (E_l l).image (fun p => (p, l)))).card := Finset.card_union_le _ _
        _ ≤ (∑ p ∈ A, ((E_p p).image (fun l => (p, l))).card) +
              (∑ l ∈ B, ((E_l l).image (fun p => (p, l))).card) :=
            Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
        _ ≤ (∑ p ∈ A, (E_p p).card) + (∑ l ∈ B, (E_l l).card) :=
            Nat.add_le_add
              (Finset.sum_le_sum fun p _ => Finset.card_image_le)
              (Finset.sum_le_sum fun l _ => Finset.card_image_le)
    have hsum_A : ∑ p ∈ A, (E_p p).card ≤ (∑ p ∈ A, (Obot_p p).card) + Tpt.card := by
      calc ∑ p ∈ A, (E_p p).card
          ≤ ∑ p ∈ A, ((Obot_p p).card + (Tpt_p p).card) := Finset.sum_le_sum hEp_bound
        _ = (∑ p ∈ A, (Obot_p p).card) + (∑ p ∈ A, (Tpt_p p).card) := Finset.sum_add_distrib
        _ = (∑ p ∈ A, (Obot_p p).card) + Tpt.card := by rw [hTpt_sum]
    have hsum_B : ∑ l ∈ B, (E_l l).card ≤ (∑ l ∈ B, (Obot_l l).card) + Tln.card := by
      calc ∑ l ∈ B, (E_l l).card
          ≤ ∑ l ∈ B, ((Obot_l l).card + (Tln_l l).card) := Finset.sum_le_sum hEl_bound
        _ = (∑ l ∈ B, (Obot_l l).card) + (∑ l ∈ B, (Tln_l l).card) := Finset.sum_add_distrib
        _ = (∑ l ∈ B, (Obot_l l).card) + Tln.card := by rw [hTln_sum]
    have h3disj : Tstar.card + Obot.card + Otop.card ≤ C.size := by
      have hdisj1 : Disjoint (Tstar ∪ Obot) Otop := by
        rw [Finset.disjoint_union_left]
        exact ⟨hOtop_disj_Tstar.symm, hObot_disj_Otop⟩
      have hcard_u : ((Tstar ∪ Obot) ∪ Otop).card = Tstar.card + Obot.card + Otop.card := by
        rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hObot_disj_Tstar.symm]
      have hle : ((Tstar ∪ Obot) ∪ Otop).card ≤ (Finset.univ : Finset (Fin C.gates.length)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      simp only [Finset.card_univ, Fintype.card_fin] at hle
      change Tstar.card + Obot.card + Otop.card ≤ C.gates.length
      omega
    have hNq_plus : N * (q + 1) = N * q + N := Nat.mul_succ N q
    omega
  · have huncov : ∃ (p l : Fin N), I p l ∧
        ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn C j a b ∧
          PEqualNP.ReadTwo.orp C (N + N) (N + N + j) C.output ∧
          PEqualNP.ReadTwo.orp C (N + N) p.val a ∧
          PEqualNP.ReadTwo.orp C (N + N) (N + l.val) b := by
      by_contra hno
      apply hall
      intro p l hpl
      by_contra hnot
      exact hno ⟨p, l, hpl, hnot⟩
    by_cases hclean : ∀ j : ℕ, PEqualNP.ReadTwo.isAnd C j →
        ∀ x : Fin (N + N) → Bool, soundQ x → PEqualNP.ReadTwo.wval C x (N + N + j) = false
    · exact hCleanUncovered q N I C hq hN hcard huniq ⟨hAO2, hTrueC, hFalseC⟩ hCmin huncov hclean
    · have hdirty : ∃ j : ℕ, PEqualNP.ReadTwo.isAnd C j ∧
          ∃ x : Fin (N + N) → Bool, soundQ x ∧ PEqualNP.ReadTwo.wval C x (N + N + j) = true := by
        by_contra hno
        apply hclean
        intro j hj x hx0
        by_contra hne
        exact hno ⟨j, hj, x, hx0, Bool.eq_true_of_not_eq_false hne⟩
      by_cases honehot : ∃ j : ℕ, PEqualNP.ReadTwo.isAnd C j ∧
          ∃ v : Fin (N + N), PEqualNP.ReadTwo.wval C (fun i => decide (i = v)) (N + N + j) = true
      · exact hDirtyOneHot q N I C hq hN hcard huniq ⟨hAO2, hTrueC, hFalseC⟩ hCmin huncov honehot
      · have hno1 : ∀ j : ℕ, PEqualNP.ReadTwo.isAnd C j →
            ∀ v : Fin (N + N), PEqualNP.ReadTwo.wval C (fun i => decide (i = v)) (N + N + j) = false := by
          intro j hj v
          by_contra hne
          exact honehot ⟨j, hj, v, Bool.eq_true_of_not_eq_false hne⟩
        exact hDirtyNoOneHot q N I C hq hN hcard huniq ⟨hAO2, hTrueC, hFalseC⟩ hCmin huncov hno1 hdirty
