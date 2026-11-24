import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_5353_17
    (hOrUncoveredClean :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        350 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (L l).card = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        0 < D.size →
        D.output = N + N + (D.size - 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.size - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        PEqualNP.GenericRejection.RightOnIncidentPairs L D →
        have w : Finset (Fin N) → Finset (Fin N) → ℕ → Bool := fun A B i =>
          (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD i false
        (∀ A B : Finset (Fin N), B.card ≤ q →
          PEqualNP.GenericRejection.IsFalseInput L A B → w A B D.output = false) →
        (∃ p l : Fin N, p ∈ L l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
          ∀ A B : Finset (Fin N), B.card ≤ q →
            PEqualNP.GenericRejection.IsFalseInput L A B → w A B (N + N + j) = false) →
        N * q ≤ 100 * D.size)
    (hOrUncoveredDirty :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        350 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (L l).card = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        0 < D.size →
        D.output = N + N + (D.size - 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.size - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        PEqualNP.GenericRejection.RightOnIncidentPairs L D →
        have w : Finset (Fin N) → Finset (Fin N) → ℕ → Bool := fun A B i =>
          (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD i false
        (∀ A B : Finset (Fin N), B.card ≤ q →
          PEqualNP.GenericRejection.IsFalseInput L A B → w A B D.output = false) →
        (∃ p l : Fin N, p ∈ L l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
          ∃ A B : Finset (Fin N), B.card ≤ q ∧
            PEqualNP.GenericRejection.IsFalseInput L A B ∧ w A B (N + N + j) = true) →
        N * q ≤ 100 * D.size)
    (hAndBothDirtyOneHot :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        350 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (L l).card = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        0 < D.size →
        D.output = N + N + (D.size - 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.size - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.size - 1)).inputs = [a, b] →
        N + N ≤ a → N + N ≤ b →
        PEqualNP.GenericRejection.RightOnIncidentPairs L D →
        have w : Finset (Fin N) → Finset (Fin N) → ℕ → Bool := fun A B i =>
          (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD i false
        (∀ A B : Finset (Fin N), B.card ≤ q →
          PEqualNP.GenericRejection.IsFalseInput L A B → w A B D.output = false) →
        (∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧ w A B a = true) →
        (∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧ w A B b = true) →
        (∃ v : Fin N, w {v} ∅ a = true ∨ w ∅ {v} a = true ∨ w {v} ∅ b = true ∨ w ∅ {v} b = true) →
        N * q ≤ 100 * D.size)
    (hAndBothDirtyNoOneHot :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        350 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (L l).card = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        0 < D.size →
        D.output = N + N + (D.size - 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.size - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.size - 1)).inputs = [a, b] →
        N + N ≤ a → N + N ≤ b →
        PEqualNP.GenericRejection.RightOnIncidentPairs L D →
        have w : Finset (Fin N) → Finset (Fin N) → ℕ → Bool := fun A B i =>
          (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD i false
        (∀ A B : Finset (Fin N), B.card ≤ q →
          PEqualNP.GenericRejection.IsFalseInput L A B → w A B D.output = false) →
        (∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧ w A B a = true) →
        (∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧ w A B b = true) →
        (∀ v : Fin N, w {v} ∅ a = false ∧ w ∅ {v} a = false ∧ w {v} ∅ b = false ∧ w ∅ {v} b = false) →
        N * q ≤ 100 * D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (350 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      x2 + x2 ≤ x4.output →
      x4.output < x2 + x2 + x4.size →
      (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate),
        x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x14 x15 : Finset (Fin x2)),
        x15.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) →
      x2 * (x1 - (349 : ℕ)) ≤ (100 : ℕ) * x4.size - (349 : ℕ) * x2 := by
  classical
  intro q N L origC hq hN hcard huniq hOrigAO2 _ _ _ hOrigRight hOrigSound
  have hNpos : 0 < N := by
    have : 0 < q ^ 2 + q + 1 := Nat.succ_pos _
    omega
  have hNge2 : 2 ≤ N := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
    omega
  let n2 : ℕ := N + N
  let I : Fin N → Fin N → Prop := fun p l => p ∈ L l
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
    have hbi : E = (Finset.univ : Finset (Fin N)).biUnion (fun l => (L l).image (fun p => (p, l))) := by
      ext e
      simp only [hmem_E, I, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hI; exact ⟨e.2, e.1, hI, Prod.eta e⟩
      · rintro ⟨l, p, hI, rfl⟩; exact hI
    rw [hbi, Finset.card_biUnion]
    · have hsum : ∑ l : Fin N, ((L l).image (fun p => (p, l))).card = ∑ _l : Fin N, (q + 1) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
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
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
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
  have hinc_len (A B : Finset (Fin N)) : (PEqualNP.GenericRejection.incidenceInput A B).length = n2 := by
    change (List.ofFn (fun p : Fin N => decide (p ∈ A)) ++ List.ofFn (fun l : Fin N => decide (l ∈ B))).length = N + N
    simp only [List.length_append, List.length_ofFn]
  have hinc_get_p (A B : Finset (Fin N)) (p : Fin N) :
      (PEqualNP.GenericRejection.incidenceInput A B).getD p.val false = decide (p ∈ A) := by
    change (List.ofFn (fun p : Fin N => decide (p ∈ A)) ++ List.ofFn (fun l : Fin N => decide (l ∈ B))).getD p.val false = _
    rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact p.isLt)]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact p.isLt), List.getElem_ofFn]
  have hinc_get_l (A B : Finset (Fin N)) (l : Fin N) :
      (PEqualNP.GenericRejection.incidenceInput A B).getD (N + l.val) false = decide (l ∈ B) := by
    change (List.ofFn (fun p : Fin N => decide (p ∈ A)) ++ List.ofFn (fun l : Fin N => decide (l ∈ B))).getD (N + l.val) false = _
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact l.isLt), List.getElem_ofFn]
  let ptsOf : (Fin n2 → Bool) → Finset (Fin N) := fun x =>
    Finset.univ.filter (fun p => x (Fin.castAdd N p) = true)
  let lnsOf : (Fin n2 → Bool) → Finset (Fin N) := fun x =>
    Finset.univ.filter (fun l => x (Fin.natAdd N l) = true)
  have hofFn_eq_inc (x : Fin n2 → Bool) :
      List.ofFn x = PEqualNP.GenericRejection.incidenceInput (ptsOf x) (lnsOf x) := by
    apply List.ext_getElem
    · rw [List.length_ofFn, hinc_len]
    · intro i hi1 hi2
      have hi_n2 : i < n2 := by rw [List.length_ofFn] at hi1; exact hi1
      rw [List.getElem_ofFn]
      rw [← List.getD_eq_getElem _ false hi2]
      by_cases hlt : i < N
      · have h1 := hinc_get_p (ptsOf x) (lnsOf x) ⟨i, hlt⟩
        rw [h1]
        simp only [ptsOf, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfin : Fin.castAdd N ⟨i, hlt⟩ = ⟨i, hi_n2⟩ := Fin.ext rfl
        rw [hfin]
        cases x ⟨i, hi_n2⟩ <;> simp
      · have hiN : i - N < N := by omega
        have h1 := hinc_get_l (ptsOf x) (lnsOf x) ⟨i - N, hiN⟩
        have heq : N + (i - N) = i := by omega
        rw [heq] at h1
        rw [h1]
        simp only [lnsOf, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfin : Fin.natAdd N ⟨i - N, hiN⟩ = ⟨i, hi_n2⟩ := Fin.ext (by simp; omega)
        rw [hfin]
        cases x ⟨i, hi_n2⟩ <;> simp
  have hprefix_AO2 (D : Circuit) (hD : PEqualNP.TopForm.IsAO2 n2 D) (m : ℕ) (w : ℕ) :
      PEqualNP.TopForm.IsAO2 n2 ⟨D.gates.take m, w⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg; exact hD.1 g (List.mem_of_mem_take hg)
    · intro j hj i hi
      have hjm : j < m := by simp only [List.length_take] at hj; omega
      have hjD : j < D.gates.length := by simp only [List.length_take] at hj; omega
      have hg_eq : gateAt ⟨D.gates.take m, w⟩ j = gateAt D j := by
        change (D.gates.take m).getD j ⟨GateOp.or, []⟩ = D.gates.getD j ⟨GateOp.or, []⟩
        rw [List.getD_eq_getElem _ _ hj, List.getElem_take, List.getD_eq_getElem _ _ hjD]
      rw [hg_eq] at hi
      exact hD.2.1 j hjD i hi
    · intro g hg; exact hD.2.2 g (List.mem_of_mem_take hg)
  have hprefix_wire (D : Circuit) (m : ℕ) (xs : List Bool) (hxs : xs.length = n2) (i : ℕ) (hi : i < n2 + m)
      (hm : m ≤ D.gates.length) :
      (run (D.gates.take m) xs).getD i false = (run D.gates xs).getD i false := by
    have hsp : D.gates = D.gates.take m ++ D.gates.drop m := (List.take_append_drop m D.gates).symm
    conv_rhs => rw [hsp, run_append]
    have hlen : (run (D.gates.take m) xs).length = n2 + m := by
      rw [run_len, hxs, List.length_take]; omega
    exact (run_keep (D.gates.drop m) (run (D.gates.take m) xs) i (by omega)).symm
  have hgate_eval_at (D : Circuit) (hDAO2 : PEqualNP.TopForm.IsAO2 n2 D) (k : ℕ) (hk : k < D.gates.length)
      (xs : List Bool) (hxs : xs.length = n2) :
      (run D.gates xs).getD (n2 + k) false =
        (gateAt D k).op.eval ((gateAt D k).inputs.map fun i => (run D.gates xs).getD i false) := by
    have hsplit : D.gates = D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1) := by
      have h1 : D.gates = D.gates.take (k + 1) ++ D.gates.drop (k + 1) :=
        (List.take_append_drop (k + 1) D.gates).symm
      conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem D.gates ⟨GateOp.or, []⟩ hk]
      rfl
    let w0 := run (D.gates.take k) xs
    have hw0_len : w0.length = n2 + k := by
      dsimp only [w0]; rw [run_len, hxs, List.length_take]; omega
    have hw_lt : ∀ i < n2 + k, (run D.gates xs).getD i false = w0.getD i false := by
      intro i hi
      exact (hprefix_wire D k xs hxs i hi (by omega)).symm
    have hrun_split : run D.gates xs = run (D.gates.drop (k + 1)) (step w0 (gateAt D k)) := by
      have h1 : run D.gates xs = run (D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1)) xs :=
        congrArg (fun gs => run gs xs) hsplit
      rw [h1]
      dsimp only [run, w0]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv_lhs => rw [hrun_split]
    rw [run_keep _ _ (n2 + k) (by simp only [step, List.length_append, hw0_len, List.length_cons, List.length_nil]; omega)]
    dsimp only [step]
    rw [show n2 + k = w0.length from hw0_len.symm, getD_snoc_eq w0 _]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact (hw_lt i (hDAO2.2.1 k hk i hi)).symm
  have hgate_inputs (D : Circuit) (hDAO2 : PEqualNP.TopForm.IsAO2 n2 D) {k : ℕ} (hk : k < D.gates.length) :
      ∃ a b : ℕ, (gateAt D k).inputs = [a, b] ∧ a < n2 + k ∧ b < n2 + k := by
    have hmem : gateAt D k ∈ D.gates := by
      change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    have hlen := hDAO2.2.2 (gateAt D k) hmem
    cases hin : (gateAt D k).inputs with
    | nil => rw [hin] at hlen; simp at hlen
    | cons a t1 =>
      cases t1 with
      | nil => rw [hin] at hlen; simp at hlen
      | cons b t2 =>
        cases t2 with
        | nil =>
          have ha := hDAO2.2.1 k hk a (by rw [hin]; exact List.mem_cons_self)
          have hb := hDAO2.2.1 k hk b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          exact ⟨a, b, rfl, ha, hb⟩
        | cons _ _ => rw [hin] at hlen; simp at hlen
  have hRight_ge_n2 (D : Circuit) (hR : PEqualNP.GenericRejection.RightOnIncidentPairs L D) :
      n2 ≤ D.output := by
    by_contra hlt
    have hlt' : D.output < N + N := by omega
    by_cases hp : D.output < N
    · let p0 : Fin N := ⟨D.output, hp⟩
      let l0 : Fin N := ⟨0, hNpos⟩
      have hcard_l0 : 1 < (L l0).card := by rw [hcard l0]; omega
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp hcard_l0
      have hex_ne : ∃ p ∈ L l0, p ≠ p0 := by
        by_cases h1 : p1 = p0
        · exact ⟨p2, hp2, fun h2 => hpne (h1.trans h2.symm)⟩
        · exact ⟨p1, hp1, h1⟩
      obtain ⟨p, hpL, hne⟩ := hex_ne
      have ht := hR l0 p hpL
      change (run D.gates (PEqualNP.GenericRejection.incidenceInput {p} {l0})).getD D.output false = true at ht
      rw [run_keep D.gates _ D.output (by rw [hinc_len]; omega)] at ht
      have hg := hinc_get_p ({p} : Finset (Fin N)) ({l0} : Finset (Fin N)) p0
      change (PEqualNP.GenericRejection.incidenceInput {p} {l0}).getD D.output false = decide (p0 ∈ ({p} : Finset (Fin N))) at hg
      rw [hg, decide_eq_true_eq, Finset.mem_singleton] at ht
      exact hne ht.symm
    · let l0 : Fin N := ⟨D.output - N, by omega⟩
      let l1 : Fin N := if l0.val = 0 then ⟨1, by omega⟩ else ⟨0, hNpos⟩
      have hlne : l1 ≠ l0 := by
        dsimp only [l1]
        split_ifs with hz
        · intro h; have := congrArg Fin.val h; simp at this; omega
        · intro h; have := congrArg Fin.val h; simp at this; omega
      have hne_L : (L l1).Nonempty := Finset.card_pos.mp (by rw [hcard l1]; omega)
      obtain ⟨p, hpL⟩ := hne_L
      have ht := hR l1 p hpL
      change (run D.gates (PEqualNP.GenericRejection.incidenceInput {p} {l1})).getD D.output false = true at ht
      rw [run_keep D.gates _ D.output (by rw [hinc_len]; omega)] at ht
      have hg := hinc_get_l ({p} : Finset (Fin N)) ({l1} : Finset (Fin N)) l0
      have heq : N + l0.val = D.output := by dsimp only [l0]; omega
      rw [heq] at hg
      rw [hg, decide_eq_true_eq, Finset.mem_singleton] at ht
      exact hlne ht.symm
  have hRight_lt_end (D : Circuit) (hR : PEqualNP.GenericRejection.RightOnIncidentPairs L D) :
      D.output < n2 + D.gates.length := by
    by_contra hge
    let l0 : Fin N := ⟨0, hNpos⟩
    obtain ⟨p, hpL⟩ := Finset.card_pos.mp (by rw [hcard l0]; omega)
    have ht := hR l0 p hpL
    change (run D.gates (PEqualNP.GenericRejection.incidenceInput {p} {l0})).getD D.output false = true at ht
    have hdef := List.getD_eq_default (run D.gates (PEqualNP.GenericRejection.incidenceInput {p} {l0})) false
      (n := D.output) (by rw [run_len, hinc_len]; omega)
    rw [hdef] at ht; cases ht
  have hmain : ∀ s : ℕ, ∀ D : Circuit, D.size ≤ s →
      PEqualNP.TopForm.IsAO2 n2 D →
      PEqualNP.GenericRejection.RightOnIncidentPairs L D →
      (∀ A B : Finset (Fin N), B.card ≤ q →
        PEqualNP.GenericRejection.IsFalseInput L A B →
        D.eval (PEqualNP.GenericRejection.incidenceInput A B) = false) →
      N * q ≤ 100 * D.size := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro D hDsz hDAO2 hDRight hDSound
      have hge := hRight_ge_n2 D hDRight
      have hlt := hRight_lt_end D hDRight
      let k : ℕ := D.output - n2
      have hk_lt : k < D.gates.length := by omega
      have hout_eq : D.output = n2 + k := by omega
      by_cases htrunc : k + 1 < D.gates.length
      · let D' : Circuit := ⟨D.gates.take (k + 1), D.output⟩
        have hD'sz : D'.size < D.size := by
          change (D.gates.take (k + 1)).length < D.gates.length
          rw [List.length_take]; omega
        have hD'eq (A B : Finset (Fin N)) :
            D'.eval (PEqualNP.GenericRejection.incidenceInput A B) =
            D.eval (PEqualNP.GenericRejection.incidenceInput A B) := by
          change (run (D.gates.take (k + 1)) (PEqualNP.GenericRejection.incidenceInput A B)).getD D.output false =
            (run D.gates (PEqualNP.GenericRejection.incidenceInput A B)).getD D.output false
          exact hprefix_wire D (k + 1) _ (hinc_len A B) D.output (by omega) (by omega)
        have hres := ih D'.size (by omega) D' (Nat.le_refl _) (hprefix_AO2 D hDAO2 (k + 1) D.output)
          (fun l p hp => by rw [hD'eq]; exact hDRight l p hp)
          (fun A B hB hF => by rw [hD'eq]; exact hDSound A B hB hF)
        exact Nat.le_trans hres (Nat.mul_le_mul_left 100 (Nat.le_of_lt hD'sz))
      · have hDpos : 0 < D.size := by change 0 < D.gates.length; omega
        have hk_eq : k = D.size - 1 := by change k = D.gates.length - 1; omega
        have hout_last : D.output = N + N + (D.size - 1) := by omega
        obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := hgate_inputs D hDAO2 hk_lt
        have hg_mem : gateAt D k ∈ D.gates := by
          change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
          rw [List.getD_eq_getElem _ _ hk_lt]; exact List.getElem_mem hk_lt
        rcases hDAO2.1 (gateAt D k) hg_mem with hand | hor
        · let Da : Circuit := ⟨D.gates.take k, a⟩
          let Db : Circuit := ⟨D.gates.take k, b⟩
          have hDa_sz : Da.size < D.size := by
            change (D.gates.take k).length < D.gates.length; rw [List.length_take]; omega
          have hDb_sz : Db.size < D.size := by
            change (D.gates.take k).length < D.gates.length; rw [List.length_take]; omega
          have hDa_eq (A B : Finset (Fin N)) :
              Da.eval (PEqualNP.GenericRejection.incidenceInput A B) =
              (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD a false :=
            hprefix_wire D k _ (hinc_len A B) a ha_lt (by omega)
          have hDb_eq (A B : Finset (Fin N)) :
              Db.eval (PEqualNP.GenericRejection.incidenceInput A B) =
              (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD b false :=
            hprefix_wire D k _ (hinc_len A B) b hb_lt (by omega)
          have hD_and (A B : Finset (Fin N)) :
              D.eval (PEqualNP.GenericRejection.incidenceInput A B) =
              ((D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD a false &&
               (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD b false) := by
            change (run D.gates (PEqualNP.GenericRejection.incidenceInput A B)).getD D.output false = _
            rw [hout_eq, hgate_eval_at D hDAO2 k hk_lt _ (hinc_len A B), hand, hab]
            change [(D.wires _).getD a false, (D.wires _).getD b false].all id = _
            simp
          have hDa_right : PEqualNP.GenericRejection.RightOnIncidentPairs L Da := by
            intro l p hp
            have ht := hDRight l p hp
            rw [hD_and, Bool.and_eq_true] at ht
            rw [hDa_eq]; exact ht.1
          have hDb_right : PEqualNP.GenericRejection.RightOnIncidentPairs L Db := by
            intro l p hp
            have ht := hDRight l p hp
            rw [hD_and, Bool.and_eq_true] at ht
            rw [hDb_eq]; exact ht.2
          by_cases ha_sound : ∀ A B : Finset (Fin N), B.card ≤ q →
              PEqualNP.GenericRejection.IsFalseInput L A B →
              Da.eval (PEqualNP.GenericRejection.incidenceInput A B) = false
          · have hres := ih Da.size (by omega) Da (Nat.le_refl _) (hprefix_AO2 D hDAO2 k a) hDa_right ha_sound
            exact Nat.le_trans hres (Nat.mul_le_mul_left 100 (Nat.le_of_lt hDa_sz))
          · by_cases hb_sound : ∀ A B : Finset (Fin N), B.card ≤ q →
                PEqualNP.GenericRejection.IsFalseInput L A B →
                Db.eval (PEqualNP.GenericRejection.incidenceInput A B) = false
            · have hres := ih Db.size (by omega) Db (Nat.le_refl _) (hprefix_AO2 D hDAO2 k b) hDb_right hb_sound
              exact Nat.le_trans hres (Nat.mul_le_mul_left 100 (Nat.le_of_lt hDb_sz))
            · have ha_dirty : ∃ A B : Finset (Fin N), B.card ≤ q ∧
                  PEqualNP.GenericRejection.IsFalseInput L A B ∧
                  (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD a false = true := by
                by_contra hno
                apply ha_sound
                intro A B hB hF
                rw [hDa_eq]
                by_contra hne
                exact hno ⟨A, B, hB, hF, Bool.eq_true_of_not_eq_false hne⟩
              have hb_dirty : ∃ A B : Finset (Fin N), B.card ≤ q ∧
                  PEqualNP.GenericRejection.IsFalseInput L A B ∧
                  (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD b false = true := by
                by_contra hno
                apply hb_sound
                intro A B hB hF
                rw [hDb_eq]
                by_contra hne
                exact hno ⟨A, B, hB, hF, Bool.eq_true_of_not_eq_false hne⟩
              have ha_ge : N + N ≤ a := hRight_ge_n2 Da hDa_right
              have hb_ge : N + N ≤ b := hRight_ge_n2 Db hDb_right
              rw [hk_eq] at hand hab
              by_cases h1hot : ∃ v : Fin N,
                  (D.wires (PEqualNP.GenericRejection.incidenceInput {v} (∅ : Finset (Fin N)))).getD a false = true ∨
                  (D.wires (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {v})).getD a false = true ∨
                  (D.wires (PEqualNP.GenericRejection.incidenceInput {v} (∅ : Finset (Fin N)))).getD b false = true ∨
                  (D.wires (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {v})).getD b false = true
              · exact hAndBothDirtyOneHot q N L D a b hq hN hcard huniq hDAO2 hDpos hout_last hand hab
                  ha_ge hb_ge hDRight hDSound ha_dirty hb_dirty h1hot
              · have hno1 : ∀ v : Fin N,
                    (D.wires (PEqualNP.GenericRejection.incidenceInput {v} (∅ : Finset (Fin N)))).getD a false = false ∧
                    (D.wires (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {v})).getD a false = false ∧
                    (D.wires (PEqualNP.GenericRejection.incidenceInput {v} (∅ : Finset (Fin N)))).getD b false = false ∧
                    (D.wires (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {v})).getD b false = false := by
                  intro v
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · by_contra h; exact h1hot ⟨v, Or.inl (Bool.eq_true_of_not_eq_false h)⟩
                  · by_contra h; exact h1hot ⟨v, Or.inr (Or.inl (Bool.eq_true_of_not_eq_false h))⟩
                  · by_contra h; exact h1hot ⟨v, Or.inr (Or.inr (Or.inl (Bool.eq_true_of_not_eq_false h)))⟩
                  · by_contra h; exact h1hot ⟨v, Or.inr (Or.inr (Or.inr (Bool.eq_true_of_not_eq_false h)))⟩
                exact hAndBothDirtyNoOneHot q N L D a b hq hN hcard huniq hDAO2 hDpos hout_last hand hab
                  ha_ge hb_ge hDRight hDSound ha_dirty hb_dirty hno1
        · have hFalseD : ∀ x : Fin n2 → Bool,
              Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
              (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
              wireVal n2 D D.output x = false := by
            intro x hBq hnoE
            change D.eval (List.ofFn x) = false
            rw [hofFn_eq_inc x]
            apply hDSound (ptsOf x) (lnsOf x)
            · have hceq : (lnsOf x).card = Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } := by
                rw [Fintype.card_subtype]
              rw [hceq]; exact hBq
            · intro l hl
              rw [Finset.disjoint_left]
              intro p hpL hpA
              simp only [ptsOf, lnsOf, Finset.mem_filter, Finset.mem_univ, true_and] at hl hpA
              exact hnoE ⟨p, l, hpL, hpA, hl⟩
          by_cases hall : ∀ (p l : Fin N), I p l →
              ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
                PEqualNP.ReadTwo.orp D n2 (n2 + j) D.output ∧
                PEqualNP.ReadTwo.orp D n2 p.val a ∧
                PEqualNP.ReadTwo.orp D n2 (N + l.val) b
          · let OrPath : ℕ → ℕ → Prop := fun w target =>
              ∀ Q : ℕ → Prop,
                Q target →
                (∀ j < D.gates.length, (gateAt D j).op = GateOp.or →
                  ∀ u ∈ (gateAt D j).inputs, Q u → Q (n2 + j)) →
                Q w
            have orPath_refl (t : ℕ) : OrPath t t := fun _ h _ => h
            have orPath_step {j u t : ℕ} (hj : j < D.gates.length) (horj : (gateAt D j).op = GateOp.or)
                (hu : u ∈ (gateAt D j).inputs) (hp : OrPath u t) : OrPath (n2 + j) t :=
              fun Q ht hs => hs j hj horj u hu (hp Q ht hs)
            have orPath_trans {u v w : ℕ} (huv : OrPath u v) (hvw : OrPath v w) : OrPath u w :=
              fun Q hw hs => huv Q (hvw Q hw hs) hs
            have orPath_cases {w t : ℕ} (h : OrPath w t) :
                w = t ∨ ∃ j < D.gates.length, w = n2 + j ∧ (gateAt D j).op = GateOp.or ∧
                  ∃ u ∈ (gateAt D j).inputs, OrPath u t := by
              apply h (fun x => x = t ∨ ∃ j < D.gates.length, x = n2 + j ∧ (gateAt D j).op = GateOp.or ∧
                  ∃ u ∈ (gateAt D j).inputs, OrPath u t)
              · exact Or.inl rfl
              · intro j hj horj u hu hPu
                refine Or.inr ⟨j, hj, rfl, horj, u, hu, ?_⟩
                rcases hPu with rfl | ⟨j', hj', rfl, hor', u', hu', hp'⟩
                · exact orPath_refl _
                · exact orPath_step hj' hor' hu' hp'
            have orPath_parent {w t : ℕ} (h : OrPath w t) (hne : w ≠ t) :
                ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
                  OrPath w (n2 + y) ∧ t ∈ (gateAt D y).inputs := by
              have hdisj : w = t ∨ ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
                  OrPath w (n2 + y) ∧ t ∈ (gateAt D y).inputs := by
                apply h (fun x => x = t ∨ ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
                    OrPath x (n2 + y) ∧ t ∈ (gateAt D y).inputs)
                · exact Or.inl rfl
                · intro j hj horj u hu hPu
                  rcases hPu with rfl | ⟨y, hy, hory, hpy, hty⟩
                  · exact Or.inr ⟨j, hj, horj, orPath_refl (n2 + j), hu⟩
                  · exact Or.inr ⟨y, hy, hory, orPath_step hj horj hu hpy, hty⟩
              rcases hdisj with heq | hex
              · exact (hne heq).elim
              · exact hex
            have orp_to_orPath {t w : ℕ} (h : PEqualNP.ReadTwo.orp D n2 t w) : OrPath w t := by
              change Relation.ReflTransGen (fun u v => u < v ∧ ∃ j, v = n2 + j ∧ isOr D j ∧ u ∈ (gateAt D j).inputs) t w at h
              induction h with
              | refl => exact orPath_refl t
              | tail _ hstep ih =>
                obtain ⟨_, j, rfl, ⟨hj, horj⟩, hu⟩ := hstep
                exact orPath_step hj horj hu ih
            have wireVal_input (i : Fin n2) (x : Fin n2 → Bool) :
                wireVal n2 D i.val x = x i := by
              change (run D.gates (List.ofFn x)).getD i.val false = x i
              rw [run_keep D.gates (List.ofFn x) i.val (by simp [i.isLt])]
              rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
            have wireVal_or_mem {j u : ℕ} (hj : j < D.gates.length) (horj : (gateAt D j).op = GateOp.or)
                (hu : u ∈ (gateAt D j).inputs) (x : Fin n2 → Bool)
                (hvu : wireVal n2 D u x = true) :
                wireVal n2 D (n2 + j) x = true := by
              change (run D.gates (List.ofFn x)).getD (n2 + j) false = true
              rw [hgate_eval_at D hDAO2 j hj (List.ofFn x) (List.length_ofFn), horj]
              change ((gateAt D j).inputs.map fun i => wireVal n2 D i x).any id = true
              rw [List.any_eq_true]
              exact ⟨true, List.mem_map.mpr ⟨u, hu, hvu⟩, rfl⟩
            have wireVal_and_pair {j u v : ℕ} (hj : j < D.gates.length) (handj : (gateAt D j).op = GateOp.and)
                (hin : (gateAt D j).inputs = [u, v]) (x : Fin n2 → Bool) :
                wireVal n2 D (n2 + j) x = (wireVal n2 D u x && wireVal n2 D v x) := by
              change (run D.gates (List.ofFn x)).getD (n2 + j) false = _
              rw [hgate_eval_at D hDAO2 j hj (List.ofFn x) (List.length_ofFn), handj, hin]
              change [wireVal n2 D u x, wireVal n2 D v x].all id = (wireVal n2 D u x && wireVal n2 D v x)
              simp
            have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin n2 → Bool)
                (ht : wireVal n2 D t x = true) : wireVal n2 D w x = true := by
              apply hp (fun u => wireVal n2 D u x = true) ht
              intro j hj horj u hu hvu
              exact wireVal_or_mem hj horj hu x hvu
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
                obtain ⟨hBP, horB⟩ := Finset.mem_filter.mp hB
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases horB with huB | hvB
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
              have hcard_step : P.card ≤ (mergeStep P u v).card + 1 := by
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
              exact ⟨hpart, hcard_step, hmono, hpair⟩
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
                exact ⟨hP, by simp, fun _ _ h => h, fun _ h => by cases h⟩
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
                (S_gates : Finset (Fin D.gates.length))
                (opWire : Fin D.gates.length → ℕ)
                (hnonempty : ∀ j ∈ S_gates, ∃ x : X, OrPath (opWire j) (wireOf x)) :
                let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
                let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
                let O_S : Finset (Fin D.gates.length) :=
                  Finset.univ.filter (fun o =>
                    (gateAt D o.val).op = GateOp.or ∧
                    2 ≤ (reach (n2 + o.val)).card ∧
                    ∃ j ∈ S_gates, OrPath (opWire j) (n2 + o.val))
                E_S.card ≤ O_S.card + S_gates.card := by
              let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
              let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
              let O_S : Finset (Fin D.gates.length) :=
                Finset.univ.filter (fun o =>
                  (gateAt D o.val).op = GateOp.or ∧
                  2 ≤ (reach (n2 + o.val)).card ∧
                  ∃ j ∈ S_gates, OrPath (opWire j) (n2 + o.val))
              let pairOf (o : Fin D.gates.length) : Option (X × X) :=
                let u := (gateAt D o.val).inputs.getD 0 0
                let v := (gateAt D o.val).inputs.getD 1 0
                if h : (reach u).Nonempty ∧ (reach v).Nonempty then some (h.1.choose, h.2.choose) else none
              let pairs : List (X × X) := O_S.toList.filterMap pairOf
              have hpairs_len : pairs.length ≤ O_S.card := by
                have h1 := List.length_filterMap_le pairOf O_S.toList
                rw [Finset.length_toList] at h1
                exact h1
              have hpairs_in : ∀ pr ∈ pairs, pr.1 ∈ E_S ∧ pr.2 ∈ E_S := by
                intro pr hpr
                obtain ⟨o, ho_list, hpair_eq⟩ := List.mem_filterMap.mp hpr
                have ho : o ∈ O_S := Finset.mem_toList.mp ho_list
                obtain ⟨horo, _, j, hjS, hjo⟩ := (Finset.mem_filter.mp ho).2
                obtain ⟨u, v, huv, _, _⟩ := hgate_inputs D hDAO2 o.isLt
                have hu_get : (gateAt D o.val).inputs.getD 0 0 = u := by rw [huv]; rfl
                have hv_get : (gateAt D o.val).inputs.getD 1 0 = v := by rw [huv]; rfl
                dsimp only [pairOf] at hpair_eq
                rw [hu_get, hv_get] at hpair_eq
                split_ifs at hpair_eq with hne
                injection hpair_eq with hpr_eq
                rw [← hpr_eq]
                have hu : hne.1.choose ∈ reach u := hne.1.choose_spec
                have hv : hne.2.choose ∈ reach v := hne.2.choose_spec
                have hua : OrPath u (wireOf hne.1.choose) := (Finset.mem_filter.mp hu).2
                have hvb : OrPath v (wireOf hne.2.choose) := (Finset.mem_filter.mp hv).2
                have hu_mem : u ∈ (gateAt D o.val).inputs := by rw [huv]; exact List.mem_cons_self
                have hv_mem : v ∈ (gateAt D o.val).inputs := by rw [huv]; exact List.mem_cons_of_mem _ List.mem_cons_self
                refine ⟨Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                    orPath_trans hjo (orPath_step o.isLt horo hu_mem hua)⟩⟩,
                  Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                    orPath_trans hjo (orPath_step o.isLt horo hv_mem hvb)⟩⟩⟩
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
                rw [Finset.card_image_of_injective _ (fun x y h => Finset.singleton_injective h)]
              let Q := pairs.foldl (fun acc pr => mergeStep acc pr.1 pr.2) P0
              obtain ⟨hQ_part, hQ_card, _, hQ_pairs⟩ := mergeFold_props E_S pairs P0 hP0_part hpairs_in
              have hsame_wire : ∀ w : ℕ, (∃ j ∈ S_gates, OrPath (opWire j) w) →
                  ∀ x1 ∈ reach w, ∀ x2 ∈ reach w, ∃ B ∈ Q, x1 ∈ B ∧ x2 ∈ B := by
                intro w
                induction w using Nat.strong_induction_on with
                | ind w ihw =>
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
                    have hstep_ex : ∃ m < D.gates.length, w = n2 + m ∧ (gateAt D m).op = GateOp.or := by
                      rcases orPath_cases hp1 with rfl | ⟨m, hm, hwm, horm, _⟩
                      · rcases orPath_cases hp2 with h2 | ⟨m, hm, hwm, horm, _⟩
                        · exact (hne_w h2).elim
                        · exact ⟨m, hm, hwm, horm⟩
                      · exact ⟨m, hm, hwm, horm⟩
                    obtain ⟨m, hm, hwm, horm⟩ := hstep_ex
                    let o : Fin D.gates.length := ⟨m, hm⟩
                    have h2card : 2 ≤ (reach (n2 + o.val)).card := by
                      rw [← hwm]
                      exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
                    have ho_mem : o ∈ O_S :=
                      Finset.mem_filter.mpr ⟨Finset.mem_univ _, horm, h2card, j, hjS, hwm ▸ hjw⟩
                    obtain ⟨u, v, huv, hu_lt, hv_lt⟩ := hgate_inputs D hDAO2 hm
                    have hu_mem : u ∈ (gateAt D m).inputs := by rw [huv]; exact List.mem_cons_self
                    have hv_mem : v ∈ (gateAt D m).inputs := by rw [huv]; exact List.mem_cons_of_mem _ List.mem_cons_self
                    have hju : OrPath (opWire j) u :=
                      orPath_trans hjw (hwm ▸ orPath_step hm horm hu_mem (orPath_refl u))
                    have hjv : OrPath (opWire j) v :=
                      orPath_trans hjw (hwm ▸ orPath_step hm horm hv_mem (orPath_refl v))
                    have hsplit_x : ∀ x ∈ reach w, x ∈ reach u ∨ x ∈ reach v := by
                      intro x hx
                      have hpx : OrPath w (wireOf x) := (Finset.mem_filter.mp hx).2
                      have hlt_x : wireOf x < n2 := hwire_lt x
                      rcases orPath_cases hpx with hxeq | ⟨m', _, hwm', _, c, hc, hpc⟩
                      · omega
                      · have hmeq : m' = m := by omega
                        subst hmeq
                        rw [huv] at hc
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                        rcases hc with rfl | rfl
                        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
                        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
                    rcases hsplit_x x1 hx1 with h1u | h1v <;> rcases hsplit_x x2 hx2 with h2u | h2v
                    · exact ihw u (by omega) ⟨j, hjS, hju⟩ x1 h1u x2 h2u
                    · have hne_uv : (reach u).Nonempty ∧ (reach v).Nonempty := ⟨⟨x1, h1u⟩, ⟨x2, h2v⟩⟩
                      have hpair_in : (hne_uv.1.choose, hne_uv.2.choose) ∈ pairs := by
                        apply List.mem_filterMap.mpr
                        refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
                        dsimp only [pairOf]
                        have hu_get : (gateAt D o.val).inputs.getD 0 0 = u := by rw [huv]; rfl
                        have hv_get : (gateAt D o.val).inputs.getD 1 0 = v := by rw [huv]; rfl
                        rw [hu_get, hv_get]; split_ifs; rfl
                      obtain ⟨B1, hB1Q, hx1B1, huB1⟩ := ihw u (by omega) ⟨j, hjS, hju⟩ x1 h1u hne_uv.1.choose hne_uv.1.choose_spec
                      obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
                      obtain ⟨B3, hB3Q, hvB3, hx2B3⟩ := ihw v (by omega) ⟨j, hjS, hjv⟩ hne_uv.2.choose hne_uv.2.choose_spec x2 h2v
                      have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
                      have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
                      subst h12B; subst h23B
                      exact ⟨B1, hB1Q, hx1B1, hx2B3⟩
                    · have hne_uv : (reach u).Nonempty ∧ (reach v).Nonempty := ⟨⟨x2, h2u⟩, ⟨x1, h1v⟩⟩
                      have hpair_in : (hne_uv.1.choose, hne_uv.2.choose) ∈ pairs := by
                        apply List.mem_filterMap.mpr
                        refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
                        dsimp only [pairOf]
                        have hu_get : (gateAt D o.val).inputs.getD 0 0 = u := by rw [huv]; rfl
                        have hv_get : (gateAt D o.val).inputs.getD 1 0 = v := by rw [huv]; rfl
                        rw [hu_get, hv_get]; split_ifs; rfl
                      obtain ⟨B1, hB1Q, hx2B1, huB1⟩ := ihw u (by omega) ⟨j, hjS, hju⟩ x2 h2u hne_uv.1.choose hne_uv.1.choose_spec
                      obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
                      obtain ⟨B3, hB3Q, hvB3, hx1B3⟩ := ihw v (by omega) ⟨j, hjS, hjv⟩ hne_uv.2.choose hne_uv.2.choose_spec x1 h1v
                      have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
                      have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
                      subst h12B; subst h23B
                      exact ⟨B1, hB1Q, hx1B3, hx2B1⟩
                    · exact ihw v (by omega) ⟨j, hjS, hjv⟩ x1 h1v x2 h2v
              let blk (j : Fin D.gates.length) : Finset X :=
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
                wireVal n2 D D.output x = false := by
              have hcard0 : Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } = 0 :=
                Fintype.card_eq_zero_iff.mpr ⟨fun l => by have hl := l.2; rw [h0 l.1] at hl; cases hl⟩
              have hnoE : ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
                rintro ⟨_, l, _, _, hl⟩; rw [h0 l] at hl; cases hl
              exact hFalseD x (by omega) hnoE
            have hno_lns_only2 (l1 l2 : Fin N) :
                wireVal n2 D D.output (fun i : Fin n2 => decide (i = Fin.natAdd N l1 ∨ i = Fin.natAdd N l2)) = false := by
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
              exact hFalseD x (by omega) hnoE
            have hedge_covered : ∀ p l : Fin N, (p, l) ∈ E →
                ∃ j : Fin D.gates.length, (gateAt D j.val).op = GateOp.and ∧
                  OrPath D.output (n2 + j.val) ∧
                  ∃ u v : ℕ, (gateAt D j.val).inputs = [u, v] ∧
                    ((OrPath u p.val ∧ OrPath v (N + l.val)) ∨
                     (OrPath u (N + l.val) ∧ OrPath v p.val)) := by
              intro p l hpl
              obtain ⟨j, u, v, handOn, htop, hpu, hlv⟩ := hall p l ((hmem_E p l).mp hpl)
              obtain ⟨⟨hjlt, hjand⟩, hor_uv⟩ := handOn
              obtain ⟨u0, v0, huv0, _, _⟩ := hgate_inputs D hDAO2 hjlt
              have hin0 : in0 D j = u0 := by change (gateAt D j).inputs.getD 0 0 = u0; rw [huv0]; rfl
              have hin1 : in1 D j = v0 := by change (gateAt D j).inputs.getD 1 0 = v0; rw [huv0]; rfl
              refine ⟨⟨j, hjlt⟩, hjand, orp_to_orPath htop, u0, v0, huv0, ?_⟩
              rcases hor_uv with ⟨h0, h1⟩ | ⟨h0, h1⟩
              · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
                exact Or.inl ⟨orp_to_orPath hpu, orp_to_orPath hlv⟩
              · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
                exact Or.inr ⟨orp_to_orPath hlv, orp_to_orPath hpu⟩
            let Tstar : Finset (Fin D.gates.length) :=
              Finset.univ.filter (fun j =>
                (gateAt D j.val).op = GateOp.and ∧
                OrPath D.output (n2 + j.val) ∧
                ∃ p l : Fin N, ∃ u v : ℕ, (gateAt D j.val).inputs = [u, v] ∧
                  ((OrPath u p.val ∧ OrPath v (N + l.val)) ∨
                   (OrPath u (N + l.val) ∧ OrPath v p.val)))
            let pWire (j : Fin D.gates.length) : ℕ :=
              let u := (gateAt D j.val).inputs.getD 0 0
              let v := (gateAt D j.val).inputs.getD 1 0
              if (pts u).Nonempty then u else v
            let lWire (j : Fin D.gates.length) : ℕ :=
              let u := (gateAt D j.val).inputs.getD 0 0
              let v := (gateAt D j.val).inputs.getD 1 0
              if (pts u).Nonempty then v else u
            let pSide (j : Fin D.gates.length) : Finset (Fin N) := pts (pWire j)
            let lSide (j : Fin D.gates.length) : Finset (Fin N) := lns (lWire j)
            have hTstar_props : ∀ j ∈ Tstar,
                (gateAt D j.val).op = GateOp.and ∧
                OrPath D.output (n2 + j.val) ∧
                (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
                lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
                (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) ∧
                ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
              intro j hj
              obtain ⟨handj, htop, p0, l0, u, v, huv, hlr0⟩ := (Finset.mem_filter.mp hj).2
              have hu_get : (gateAt D j.val).inputs.getD 0 0 = u := by rw [huv]; rfl
              have hv_get : (gateAt D j.val).inputs.getD 1 0 = v := by rw [huv]; rfl
              have hand_sound : ∀ x : Fin n2 → Bool,
                  wireVal n2 D u x = true → wireVal n2 D v x = true → wireVal n2 D D.output x = true := by
                intro x hxu hxv
                apply orPath_sound htop x
                rw [wireVal_and_pair j.isLt handj huv x, hxu, hxv]
                rfl
              have hno_both_pts : ¬ ((pts u).Nonempty ∧ (pts v).Nonempty) := by
                rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
                let x : Fin n2 → Bool := fun i => decide (i = Fin.castAdd N p1 ∨ i = Fin.castAdd N p2)
                have h1 : wireVal n2 D p1.val x = true := by
                  have := wireVal_input (Fin.castAdd N p1) x; simpa [x] using this
                have h2 : wireVal n2 D p2.val x = true := by
                  have := wireVal_input (Fin.castAdd N p2) x; simpa [x] using this
                have ht := hand_sound x (orPath_sound (Finset.mem_filter.mp hp1).2 x h1)
                  (orPath_sound (Finset.mem_filter.mp hp2).2 x h2)
                have hf := hno_pts_only x (fun l => by
                  simp only [x, decide_eq_false_iff_not]
                  rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
                rw [ht] at hf; cases hf
              have hno_both_lns : ¬ ((lns u).Nonempty ∧ (lns v).Nonempty) := by
                rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
                let x : Fin n2 → Bool := fun i => decide (i = Fin.natAdd N l1 ∨ i = Fin.natAdd N l2)
                have h1 : wireVal n2 D (N + l1.val) x = true := by
                  have hv := wireVal_input (Fin.natAdd N l1) x
                  rw [Fin.val_natAdd] at hv
                  simpa only [x, true_or, decide_true] using hv
                have h2 : wireVal n2 D (N + l2.val) x = true := by
                  have hv := wireVal_input (Fin.natAdd N l2) x
                  rw [Fin.val_natAdd] at hv
                  simpa only [x, or_true, decide_true] using hv
                have ht := hand_sound x (orPath_sound (Finset.mem_filter.mp hl1).2 x h1)
                  (orPath_sound (Finset.mem_filter.mp hl2).2 x h2)
                have hf := hno_lns_only2 l1 l2
                rw [ht] at hf; cases hf
              have hbiclique : ∀ (p l : Fin N),
                  ((p ∈ pts u ∧ l ∈ lns v) ∨ (p ∈ pts v ∧ l ∈ lns u)) → (p, l) ∈ E := by
                intro p l hpl
                let x : Fin n2 → Bool := fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
                have hxp : wireVal n2 D p.val x = true := by
                  have hv := wireVal_input (Fin.castAdd N p) x
                  rw [Fin.val_castAdd] at hv
                  simpa only [x, true_or, decide_true] using hv
                have hxl : wireVal n2 D (N + l.val) x = true := by
                  have hv := wireVal_input (Fin.natAdd N l) x
                  rw [Fin.val_natAdd] at hv
                  simpa only [x, or_true, decide_true] using hv
                have hout_t : wireVal n2 D D.output x = true := by
                  rcases hpl with ⟨hpu, hlv⟩ | ⟨hpv, hlu⟩
                  · exact hand_sound x
                      (orPath_sound (Finset.mem_filter.mp hpu).2 x hxp)
                      (orPath_sound (Finset.mem_filter.mp hlv).2 x hxl)
                  · exact hand_sound x
                      (orPath_sound (Finset.mem_filter.mp hlu).2 x hxl)
                      (orPath_sound (Finset.mem_filter.mp hpv).2 x hxp)
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
                have hf : wireVal n2 D D.output x = false := hFalseD x (by omega) hnoE
                rw [hout_t] at hf; cases hf
              have hsides : (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
                  lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
                  (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) := by
                rcases hlr0 with ⟨hpu, hlv⟩ | ⟨hlu, hpv⟩
                · have hpu_ne : (pts u).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpu⟩⟩
                  have hlv_ne : (lns v).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlv⟩⟩
                  have hpW : pWire j = u := by dsimp only [pWire]; simp only [hu_get, hpu_ne, ↓reduceIte]
                  have hlW : lWire j = v := by dsimp only [lWire]; simp only [hu_get, hv_get, hpu_ne, ↓reduceIte]
                  have hlu_em : lns u = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨h, hlv_ne⟩)
                  have hpv_em : pts v = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_pts ⟨hpu_ne, h⟩)
                  refine ⟨by simpa [pSide, hpW] using hpu_ne, by simpa [lSide, hlW] using hlv_ne,
                    by rw [hpW]; exact hlu_em, by rw [hlW]; exact hpv_em, ?_⟩
                  intro p hp l hl
                  rw [show pSide j = pts u by simp [pSide, hpW]] at hp
                  rw [show lSide j = lns v by simp [lSide, hlW]] at hl
                  exact hbiclique p l (Or.inl ⟨hp, hl⟩)
                · have hlu_ne : (lns u).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlu⟩⟩
                  have hpv_ne : (pts v).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpv⟩⟩
                  have hpu_not : ¬ (pts u).Nonempty := fun h => hno_both_pts ⟨h, hpv_ne⟩
                  have hpW : pWire j = v := by dsimp only [pWire]; simp only [hu_get, hv_get, hpu_not, ↓reduceIte]
                  have hlW : lWire j = u := by dsimp only [lWire]; simp only [hu_get, hpu_not, ↓reduceIte]
                  have hlv_em : lns v = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨hlu_ne, h⟩)
                  have hpu_em : pts u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpu_not
                  refine ⟨by simpa [pSide, hpW] using hpv_ne, by simpa [lSide, hlW] using hlu_ne,
                    by rw [hpW]; exact hlv_em, by rw [hlW]; exact hpu_em, ?_⟩
                  intro p hp l hl
                  rw [show pSide j = pts v by simp [pSide, hpW]] at hp
                  rw [show lSide j = lns u by simp [lSide, hlW]] at hl
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
              exact ⟨handj, htop, hsides.1, hsides.2.1, hsides.2.2.1, hsides.2.2.2.1, hsides.2.2.2.2, hstar⟩
            have hE_in_Tstar : ∀ p l : Fin N, (p, l) ∈ E → ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
              intro p l hpl
              obtain ⟨j, handj, htop, u, v, huv, hlr⟩ := hedge_covered p l hpl
              have hjT : j ∈ Tstar := Finset.mem_filter.mpr ⟨Finset.mem_univ _, handj, htop, p, l, u, v, huv, hlr⟩
              have hprops := hTstar_props j hjT
              have hu_get : (gateAt D j.val).inputs.getD 0 0 = u := by rw [huv]; rfl
              have hv_get : (gateAt D j.val).inputs.getD 1 0 = v := by rw [huv]; rfl
              refine ⟨j, hjT, ?_⟩
              rcases hlr with ⟨hpu, hlv⟩ | ⟨hlu, hpv⟩
              · have hpu_m : p ∈ pts u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpu⟩
                have hlv_m : l ∈ lns v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlv⟩
                have hpu_ne : (pts u).Nonempty := ⟨p, hpu_m⟩
                have hpW : pWire j = u := by dsimp only [pWire]; simp only [hu_get, hpu_ne, ↓reduceIte]
                have hlW : lWire j = v := by dsimp only [lWire]; simp only [hu_get, hv_get, hpu_ne, ↓reduceIte]
                exact ⟨by simpa [pSide, hpW] using hpu_m, by simpa [lSide, hlW] using hlv_m⟩
              · have hlu_m : l ∈ lns u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlu⟩
                have hpv_m : p ∈ pts v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpv⟩
                have hpu_not : ¬ (pts u).Nonempty := by
                  intro hpu_ne
                  have hpW : pWire j = u := by dsimp only [pWire]; simp only [hu_get, hpu_ne, ↓reduceIte]
                  have hlem := hprops.2.2.2.2.1
                  rw [hpW] at hlem; rw [hlem] at hlu_m; cases hlu_m
                have hpW : pWire j = v := by dsimp only [pWire]; simp only [hu_get, hv_get, hpu_not, ↓reduceIte]
                have hlW : lWire j = u := by dsimp only [lWire]; simp only [hu_get, hpu_not, ↓reduceIte]
                exact ⟨by simpa [pSide, hpW] using hpv_m, by simpa [lSide, hlW] using hlu_m⟩
            let Tpt : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
            let Tln : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
            have hTpt_Tln_disj : Disjoint Tpt Tln := by
              rw [Finset.disjoint_left]
              intro j h1 h2
              exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
            have hTpt_Tln_union : Tpt ∪ Tln = Tstar := by
              ext j; simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]; tauto
            have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
              rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
            let centerP (j : Fin D.gates.length) : Fin N :=
              if h : (pSide j).Nonempty then h.choose else (Finset.nonempty_iff_ne_empty.mpr hEempty).choose.1
            let centerL (j : Fin D.gates.length) : Fin N :=
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
            let Tpt_p (p : Fin N) : Finset (Fin D.gates.length) := Tpt.filter (fun j => centerP j = p)
            let E_p (p : Fin N) : Finset (Fin N) := (Tpt_p p).biUnion lSide
            let Obot_p (p : Fin N) : Finset (Fin D.gates.length) :=
              Finset.univ.filter (fun o =>
                (gateAt D o.val).op = GateOp.or ∧
                2 ≤ (lns (n2 + o.val)).card ∧
                ∃ j ∈ Tpt_p p, OrPath (lWire j) (n2 + o.val))
            let Tln_l (l : Fin N) : Finset (Fin D.gates.length) := Tln.filter (fun j => centerL j = l)
            let E_l (l : Fin N) : Finset (Fin N) := (Tln_l l).biUnion pSide
            let Obot_l (l : Fin N) : Finset (Fin D.gates.length) :=
              Finset.univ.filter (fun o =>
                (gateAt D o.val).op = GateOp.or ∧
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
              have hando := (hTstar_props o h2).1
              rcases Finset.mem_union.mp h1 with hA | hB
              · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
                have horo := (Finset.mem_filter.mp ho).2.1
                rw [horo] at hando; cases hando
              · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
                have horo := (Finset.mem_filter.mp ho).2.1
                rw [horo] at hando; cases hando
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
            have h2disj : Tstar.card + Obot.card ≤ D.size := by
              have hcard_u : (Tstar ∪ Obot).card = Tstar.card + Obot.card :=
                Finset.card_union_of_disjoint hObot_disj_Tstar.symm
              have hle : (Tstar ∪ Obot).card ≤ (Finset.univ : Finset (Fin D.gates.length)).card :=
                Finset.card_le_card (Finset.subset_univ _)
              simp only [Finset.card_univ, Fintype.card_fin] at hle
              change Tstar.card + Obot.card ≤ D.gates.length
              omega
            have hNq_plus : N * (q + 1) = N * q + N := Nat.mul_succ N q
            omega
          · have huncov : ∃ p l : Fin N, p ∈ L l ∧
                ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
                  PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
                  PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
                  PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b := by
              by_contra hno
              apply hall
              intro p l hpl
              by_contra hnot
              exact hno ⟨p, l, hpl, hnot⟩
            rw [hk_eq] at hor
            by_cases hclean : ∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
                ∀ A B : Finset (Fin N), B.card ≤ q →
                  PEqualNP.GenericRejection.IsFalseInput L A B →
                  (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD (N + N + j) false = false
            · exact hOrUncoveredClean q N L D hq hN hcard huniq hDAO2 hDpos hout_last hor hDRight hDSound huncov hclean
            · have hdirty : ∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
                  ∃ A B : Finset (Fin N), B.card ≤ q ∧
                    PEqualNP.GenericRejection.IsFalseInput L A B ∧
                    (D.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD (N + N + j) false = true := by
                by_contra hno
                apply hclean
                intro j hj A B hB hF
                by_contra hne
                exact hno ⟨j, hj, A, B, hB, hF, Bool.eq_true_of_not_eq_false hne⟩
              exact hOrUncoveredDirty q N L D hq hN hcard huniq hDAO2 hDpos hout_last hor hDRight hDSound huncov hdirty
  have hNq : N * q ≤ 100 * origC.size := hmain origC.size origC (Nat.le_refl _) hOrigAO2 hOrigRight hOrigSound
  have hsplit_q : N * (q - 349) + 349 * N = N * q := by
    calc N * (q - 349) + 349 * N = N * (q - 349) + N * 349 := by rw [Nat.mul_comm 349 N]
      _ = N * ((q - 349) + 349) := (Nat.mul_add N (q - 349) 349).symm
      _ = N * q := by rw [Nat.sub_add_cancel (by omega)]
  exact Nat.le_sub_of_add_le (by rw [hsplit_q]; exact hNq)
