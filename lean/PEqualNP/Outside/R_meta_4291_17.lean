import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_4291_17
    (hAndOutPtDirty :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        100 * D.size < N * q →
        (∀ p l : Fin N, I p l →
          PEqualNP.MetaComplexity.circuitFun (N + N) D (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
        (∀ x : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
          (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) D x = false) →
        N + N ≤ D.output →
        PEqualNP.ReadTwo.isAnd D (D.output - (N + N)) →
        (∃ p l : Fin N, I p l ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∃ k0 : ℕ, ∃ l1 l2 : Fin N, PEqualNP.ReadTwo.isAnd D k0 ∧ l1 ≠ l2 ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l1)) (N + N + k0) = true ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l2)) (N + N + k0) = true) →
        (∃ k1 : ℕ, ∃ p1 : Fin N, PEqualNP.ReadTwo.isAnd D k1 ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.castAdd N p1)) (N + N + k1) = true) →
        False)
    (hAndOutPtClean :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        100 * D.size < N * q →
        (∀ p l : Fin N, I p l →
          PEqualNP.MetaComplexity.circuitFun (N + N) D (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
        (∀ x : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
          (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) D x = false) →
        N + N ≤ D.output →
        PEqualNP.ReadTwo.isAnd D (D.output - (N + N)) →
        (∃ p l : Fin N, I p l ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∃ k0 : ℕ, ∃ l1 l2 : Fin N, PEqualNP.ReadTwo.isAnd D k0 ∧ l1 ≠ l2 ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l1)) (N + N + k0) = true ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l2)) (N + N + k0) = true) →
        (∀ k1 : ℕ, PEqualNP.ReadTwo.isAnd D k1 →
          ∀ p1 : Fin N, PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.castAdd N p1)) (N + N + k1) = false) →
        False)
    (hOrOutPtDirty :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        100 * D.size < N * q →
        (∀ p l : Fin N, I p l →
          PEqualNP.MetaComplexity.circuitFun (N + N) D (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
        (∀ x : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
          (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) D x = false) →
        N + N ≤ D.output →
        PEqualNP.ReadTwo.isOr D (D.output - (N + N)) →
        (∃ p l : Fin N, I p l ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∃ k0 : ℕ, ∃ l1 l2 : Fin N, PEqualNP.ReadTwo.isAnd D k0 ∧ l1 ≠ l2 ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l1)) (N + N + k0) = true ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l2)) (N + N + k0) = true) →
        (∃ k1 : ℕ, ∃ p1 : Fin N, PEqualNP.ReadTwo.isAnd D k1 ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.castAdd N p1)) (N + N + k1) = true) →
        False)
    (hOrOutPtClean :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        PEqualNP.TopForm.IsAO2 (N + N) D →
        100 * D.size < N * q →
        (∀ p l : Fin N, I p l →
          PEqualNP.MetaComplexity.circuitFun (N + N) D (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
        (∀ x : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
          (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) D x = false) →
        N + N ≤ D.output →
        PEqualNP.ReadTwo.isOr D (D.output - (N + N)) →
        (∃ p l : Fin N, I p l ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + N + j) D.output ∧
            PEqualNP.ReadTwo.orp D (N + N) p.val a ∧
            PEqualNP.ReadTwo.orp D (N + N) (N + l.val) b) →
        (∃ k0 : ℕ, ∃ l1 l2 : Fin N, PEqualNP.ReadTwo.isAnd D k0 ∧ l1 ≠ l2 ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l1)) (N + N + k0) = true ∧
          PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.natAdd N l2)) (N + N + k0) = true) →
        (∀ k1 : ℕ, PEqualNP.ReadTwo.isAnd D k1 →
          ∀ p1 : Fin N, PEqualNP.ReadTwo.wval D (fun i => decide (i = Fin.castAdd N p1)) (N + N + k1) = false) →
        False) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (_ : Fin x2) => Bool.false) else (fun (_ : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Fin x2) (x22 : Fin x2), x21 ≠ x22 ∧ x21 ∈ x19 Bool.false (x12 + x20) ∧ x22 ∈ x19 Bool.false (x12 + x20) ∧ ¬∃ x23 < x12 + x20, ∃ x24 < x12 + x20, x19 Bool.false (x12 + x20) = x19 Bool.false x23 ∪ x19 Bool.false x24) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I hdec hq hN hcard huniq s o W
  dsimp only
  intro ho hWin hWgate hWpos hWneg hWit
  by_contra hlt_goal
  have hs_lt : 100 * s < N * q := by omega
  have hNpos : 0 < N := by
    have : 0 < q ^ 2 + q + 1 := Nat.succ_pos _
    omega
  let n2 : ℕ := N + N
  let e1 : Fin N → Fin N → Bool := fun a b => decide (b = a)
  let splitVec : (Fin n2 → Bool) → (Fin N → Bool) × (Fin N → Bool) :=
    fun x => (fun p => x (Fin.castAdd N p), fun l => x (Fin.natAdd N l))
  have hWmono : ∀ w < n2 + s, ∀ z1 z2 : (Fin N → Bool) × (Fin N → Bool),
      (∀ p : Fin N, z1.1 p = true → z2.1 p = true) →
      (∀ l : Fin N, z1.2 l = true → z2.2 l = true) →
      z1 ∈ W w → z2 ∈ W w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw z1 z2 hp hl hz1
      by_cases hwN : w < N
      · have heq := (hWin ⟨w, hwN⟩).1
        dsimp only at heq
        rw [heq] at hz1 ⊢
        exact hp ⟨w, hwN⟩ hz1
      · by_cases hw2 : w < n2
        · have hsub : N + (w - N) = w := by omega
          have heq := (hWin ⟨w - N, by omega⟩).2
          dsimp only at heq
          rw [hsub] at heq
          rw [heq] at hz1 ⊢
          exact hl ⟨w - N, by omega⟩ hz1
        · let j : ℕ := w - n2
          have hj : j < s := by omega
          have hwj : n2 + j = w := by omega
          obtain ⟨a, b, hmax, hmem⟩ := hWgate j hj
          have ha : a < w := by have := le_max_left a b; omega
          have hb : b < w := by have := le_max_right a b; omega
          rw [hwj] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with heq | heq | heq | heq
          · rw [heq] at hz1 ⊢
            rcases hz1 with h1 | h2
            · exact Or.inl (ih a ha (by omega) z1 z2 hp hl h1)
            · exact Or.inr (ih b hb (by omega) z1 z2 hp hl h2)
          · rw [heq] at hz1 ⊢
            exact ih a ha (by omega) z1 z2 hp hl hz1
          · rw [heq] at hz1; cases hz1
          · rw [heq] at hz1 ⊢
            exact ⟨ih a ha (by omega) z1 z2 hp hl hz1.1, ih b hb (by omega) z1 z2 hp hl hz1.2⟩
  have hWsoundQ : ∀ x : Fin n2 → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      splitVec x ∉ W o := by
    intro x hcq hnoE hmem
    let L : Fin N → Bool := fun l => x (Fin.natAdd N l)
    let Pav : Fin N → Bool := fun p => decide (¬ ∃ l : Fin N, I p l ∧ L l = true)
    have hp_le : ∀ p : Fin N, (splitVec x).1 p = true → Pav p = true := by
      intro p hp
      dsimp only [Pav]
      rw [decide_eq_true_eq]
      rintro ⟨l, hI, hl⟩
      exact hnoE ⟨p, l, hI, hp, hl⟩
    have hmon := hWmono o ho (splitVec x) (Pav, L) hp_le (fun _ h => h) hmem
    exact hWneg L hcq hmon
  obtain ⟨j0, hj0_lt, l1, l2, hl12_ne, hl1_in, hl2_in, hj0_not_union⟩ := hWit
  have hj0_ne_empty : W (n2 + j0) ≠ ∅ := by
    intro hem
    have h1 : (fun _ : Fin N => false, e1 l1) ∈ W (n2 + j0) := hl1_in
    rw [hem] at h1; cases h1
  have hj0_not_eq_union (a b : ℕ) (ha : a < n2 + j0) (hb : b < n2 + j0) :
      W (n2 + j0) ≠ W a ∪ W b := by
    intro heq
    apply hj0_not_union
    refine ⟨a, ha, b, hb, ?_⟩
    ext l
    change (fun _ : Fin N => false, e1 l) ∈ W (n2 + j0) ↔
      (fun _ : Fin N => false, e1 l) ∈ W a ∨ (fun _ : Fin N => false, e1 l) ∈ W b
    rw [heq]; rfl
  have hj0_not_eq_copy (a : ℕ) (ha : a < n2 + j0) : W (n2 + j0) ≠ W a := by
    intro heq
    apply hj0_not_eq_union a a ha ha
    rw [Set.union_self]; exact heq
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
  have hCompile : ∀ k ≤ s, ∃ gs : List Gate, gs.length ≤ k ∧ AO2List gs ∧
      (∀ i < n2 + k, W i = ∅ ∨
        ∃ w < n2 + gs.length, ∀ x : Fin n2 → Bool, (run gs (List.ofFn x)).getD w false = true ↔ splitVec x ∈ W i) ∧
      (j0 < k → ∃ k0 < gs.length, (gs.getD k0 ⟨GateOp.or, []⟩).op = GateOp.and ∧
        ∀ x : Fin n2 → Bool, (run gs (List.ofFn x)).getD (n2 + k0) false = true ↔ splitVec x ∈ W (n2 + j0)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Nat.le_refl 0,
        ⟨(fun _ h => by cases h), (fun _ h _ _ => by simp only [List.length_nil] at h; omega), (fun _ h => by cases h)⟩,
        ?_, (fun h => by omega)⟩
      intro i hi
      refine Or.inr ⟨i, by simp only [List.length_nil]; omega, fun x => ?_⟩
      have hlen : (List.ofFn x).length = n2 := List.length_ofFn
      have hget : (run [] (List.ofFn x)).getD i false = x ⟨i, by omega⟩ := by
        change (List.ofFn x).getD i false = x ⟨i, by omega⟩
        rw [List.getD_eq_getElem _ _ (by omega), List.getElem_ofFn]
      rw [hget]
      by_cases hiN : i < N
      · have h1 := (hWin ⟨i, hiN⟩).1
        dsimp only at h1
        rw [h1]
        change x ⟨i, by omega⟩ = true ↔ x (Fin.castAdd N ⟨i, hiN⟩) = true
        rfl
      · have hsub : N + (i - N) = i := by omega
        have h1 := (hWin ⟨i - N, by omega⟩).2
        dsimp only at h1
        rw [hsub] at h1
        rw [h1]
        change x ⟨i, by omega⟩ = true ↔ x (Fin.natAdd N ⟨i - N, by omega⟩) = true
        have hfeq : (⟨i, by omega⟩ : Fin n2) = Fin.natAdd N ⟨i - N, by omega⟩ := Fin.ext (by change i = N + (i - N); omega)
        rw [hfeq]
    | succ k ih =>
      intro hk1
      obtain ⟨gs, hgs_len, hgs_AO, hmap, hjk0⟩ := ih (by omega)
      obtain ⟨a, b, hmax, hcase⟩ := hWgate k (by omega)
      have ha : a < n2 + k := by have := le_max_left a b; omega
      have hb : b < n2 + k := by have := le_max_right a b; omega
      have hNoGate (hnew : W (n2 + k) = ∅ ∨
          ∃ w < n2 + gs.length, ∀ x : Fin n2 → Bool, (run gs (List.ofFn x)).getD w false = true ↔ splitVec x ∈ W (n2 + k))
          (hne : k ≠ j0) :
          ∃ gs' : List Gate, gs'.length ≤ k + 1 ∧ AO2List gs' ∧
            (∀ i < n2 + (k + 1), W i = ∅ ∨
              ∃ w < n2 + gs'.length, ∀ x : Fin n2 → Bool, (run gs' (List.ofFn x)).getD w false = true ↔ splitVec x ∈ W i) ∧
            (j0 < k + 1 → ∃ k0 < gs'.length, (gs'.getD k0 ⟨GateOp.or, []⟩).op = GateOp.and ∧
              ∀ x : Fin n2 → Bool, (run gs' (List.ofFn x)).getD (n2 + k0) false = true ↔ splitVec x ∈ W (n2 + j0)) := by
        refine ⟨gs, by omega, hgs_AO, fun i hi => ?_, fun hlt => hjk0 (by omega)⟩
        by_cases heq : i = n2 + k
        · subst heq; exact hnew
        · exact hmap i (by omega)
      have hAddGate (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (wa wb : ℕ)
          (hwa : wa < n2 + gs.length) (hwb : wb < n2 + gs.length)
          (hsem : ∀ x : Fin n2 → Bool,
            op.eval [(run gs (List.ofFn x)).getD wa false, (run gs (List.ofFn x)).getD wb false] = true ↔
              splitVec x ∈ W (n2 + k))
          (hj0_ok : k = j0 → op = GateOp.and) :
          ∃ gs' : List Gate, gs'.length ≤ k + 1 ∧ AO2List gs' ∧
            (∀ i < n2 + (k + 1), W i = ∅ ∨
              ∃ w < n2 + gs'.length, ∀ x : Fin n2 → Bool, (run gs' (List.ofFn x)).getD w false = true ↔ splitVec x ∈ W i) ∧
            (j0 < k + 1 → ∃ k0 < gs'.length, (gs'.getD k0 ⟨GateOp.or, []⟩).op = GateOp.and ∧
              ∀ x : Fin n2 → Bool, (run gs' (List.ofFn x)).getD (n2 + k0) false = true ↔ splitVec x ∈ W (n2 + j0)) := by
        let gnew : Gate := ⟨op, [wa, wb]⟩
        let gs' : List Gate := gs ++ [gnew]
        have hlen' : gs'.length = gs.length + 1 := by
          dsimp only [gs']; rw [List.length_append]; simp only [List.length_cons, List.length_nil]
        have hAO' : AO2List gs' := by
          refine ⟨?_, ?_, ?_⟩
          · intro g hg
            dsimp only [gs'] at hg; rw [List.mem_append, List.mem_singleton] at hg
            rcases hg with h1 | rfl
            · exact hgs_AO.1 g h1
            · exact hop
          · intro j hj u hu
            rw [hlen'] at hj
            by_cases hjlt : j < gs.length
            · dsimp only [gs'] at hu; rw [List.getD_append _ _ _ _ hjlt] at hu
              exact hgs_AO.2.1 j hjlt u hu
            · have hjeq : j = gs.length := by omega
              subst hjeq
              dsimp only [gs'] at hu
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero] at hu
              change u ∈ [wa, wb] at hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl <;> omega
          · intro g hg
            dsimp only [gs'] at hg; rw [List.mem_append, List.mem_singleton] at hg
            rcases hg with h1 | rfl
            · exact hgs_AO.2.2 g h1
            · rfl
        have hkeep' (w : ℕ) (hw : w < n2 + gs.length) (x : Fin n2 → Bool) :
            (run gs' (List.ofFn x)).getD w false = (run gs (List.ofFn x)).getD w false := by
          dsimp only [gs']
          rw [run_snoc]
          have hl : (run gs (List.ofFn x)).length = n2 + gs.length := by rw [run_len, List.length_ofFn]
          exact List.getD_append _ _ _ _ (by omega)
        have hnew_val (x : Fin n2 → Bool) :
            (run gs' (List.ofFn x)).getD (n2 + gs.length) false =
              op.eval [(run gs (List.ofFn x)).getD wa false, (run gs (List.ofFn x)).getD wb false] := by
          dsimp only [gs']
          rw [run_snoc]
          have hl : (run gs (List.ofFn x)).length = n2 + gs.length := by rw [run_len, List.length_ofFn]
          dsimp only [step]
          rw [← hl, getD_snoc_eq (run gs (List.ofFn x)) _]
          rfl
        refine ⟨gs', by omega, hAO', fun i hi => ?_, fun hlt => ?_⟩
        · by_cases heq : i = n2 + k
          · subst heq
            refine Or.inr ⟨n2 + gs.length, by omega, fun x => ?_⟩
            rw [hnew_val x]; exact hsem x
          · rcases hmap i (by omega) with hem | ⟨w, hw, hww⟩
            · exact Or.inl hem
            · refine Or.inr ⟨w, by omega, fun x => ?_⟩
              rw [hkeep' w hw x]; exact hww x
        · by_cases heq : k = j0
          · subst heq
            refine ⟨gs.length, by omega, ?_, fun x => ?_⟩
            · dsimp only [gs']
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
              exact hj0_ok rfl
            · rw [hnew_val x]; exact hsem x
          · obtain ⟨k0, hk0_lt, hk0_and, hk0_sem⟩ := hjk0 (by omega)
            refine ⟨k0, by omega, ?_, fun x => ?_⟩
            · dsimp only [gs']
              rw [List.getD_append _ _ _ _ hk0_lt]; exact hk0_and
            · rw [hkeep' (n2 + k0) (by omega) x]; exact hk0_sem x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcase
      rcases hcase with h_or | h_cp | h_em | h_and
      · have hne : k ≠ j0 := by intro h; subst h; exact hj0_not_eq_union a b ha hb h_or
        rcases hmap a ha with ha_em | ⟨wa, hwa, hwa_s⟩
        · have heq : W (n2 + k) = W b := by rw [h_or, ha_em, Set.empty_union]
          apply hNoGate _ hne
          rw [heq]; exact hmap b hb
        · rcases hmap b hb with hb_em | ⟨wb, hwb, hwb_s⟩
          · have heq : W (n2 + k) = W a := by rw [h_or, hb_em, Set.union_empty]
            apply hNoGate _ hne
            rw [heq]; exact Or.inr ⟨wa, hwa, hwa_s⟩
          · apply hAddGate GateOp.or (Or.inr rfl) wa wb hwa hwb _ (fun h => (hne h).elim)
            intro x
            change ((run gs (List.ofFn x)).getD wa false || ((run gs (List.ofFn x)).getD wb false || false)) = true ↔ _
            rw [Bool.or_false, Bool.or_eq_true, hwa_s x, hwb_s x, h_or]; rfl
      · have hne : k ≠ j0 := by intro h; subst h; exact hj0_not_eq_copy a ha h_cp
        apply hNoGate _ hne
        rw [h_cp]; exact hmap a ha
      · have hne : k ≠ j0 := by intro h; subst h; exact hj0_ne_empty h_em
        exact hNoGate (Or.inl h_em) hne
      · rcases hmap a ha with ha_em | ⟨wa, hwa, hwa_s⟩
        · have heq : W (n2 + k) = ∅ := by rw [h_and, ha_em, Set.empty_inter]
          have hne : k ≠ j0 := by intro h; subst h; exact hj0_ne_empty heq
          exact hNoGate (Or.inl heq) hne
        · rcases hmap b hb with hb_em | ⟨wb, hwb, hwb_s⟩
          · have heq : W (n2 + k) = ∅ := by rw [h_and, hb_em, Set.inter_empty]
            have hne : k ≠ j0 := by intro h; subst h; exact hj0_ne_empty heq
            exact hNoGate (Or.inl heq) hne
          · apply hAddGate GateOp.and (Or.inl rfl) wa wb hwa hwb _ (fun _ => rfl)
            intro x
            change ((run gs (List.ofFn x)).getD wa false && ((run gs (List.ofFn x)).getD wb false && true)) = true ↔ _
            rw [Bool.and_true, Bool.and_eq_true, hwa_s x, hwb_s x, h_and]; rfl
  obtain ⟨gs, hgs_len, hgs_AO, hmap_s, hjk0_s⟩ := hCompile s (Nat.le_refl s)
  have hWo_ne : W o ≠ ∅ := by
    intro hem
    let l0 : Fin N := ⟨0, hNpos⟩
    have hcpos : 0 < Fintype.card { p : Fin N // I p l0 } := by rw [hcard l0]; omega
    obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hcpos
    have h1 := hWpos p0 l0 hp0
    rw [hem] at h1; cases h1
  have hout_ex : ∃ out < n2 + gs.length,
      ∀ x : Fin n2 → Bool, (run gs (List.ofFn x)).getD out false = true ↔ splitVec x ∈ W o := by
    rcases hmap_s o ho with hem | hex
    · exact (hWo_ne hem).elim
    · exact hex
  obtain ⟨out, hout_lt, hout_sem⟩ := hout_ex
  let D : Circuit := ⟨gs, out⟩
  have hD_sz : 100 * D.size < N * q := by
    have h1 : D.size ≤ s := hgs_len
    omega
  have hD_AO : IsAO2 n2 D := ⟨hgs_AO.1, hgs_AO.2.1, hgs_AO.2.2⟩
  have hTrueD : ∀ p l : Fin N, I p l →
      circuitFun n2 D (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true := by
    intro p l hI
    change (run gs (List.ofFn fun i : Fin n2 => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l))).getD out false = true
    rw [hout_sem]
    have hsp : splitVec (fun i : Fin n2 => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = (e1 p, e1 l) := by
      apply Prod.ext
      · funext a
        dsimp only [splitVec, e1]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro (h | h)
          · exact Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h)
          · have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
        · intro h; subst h; exact Or.inl rfl
      · funext b
        dsimp only [splitVec, e1]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro (h | h)
          · have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
          · exact Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)
        · intro h; subst h; exact Or.inr rfl
    rw [hsp]
    exact hWpos p l hI
  have hFalseD : ∀ x : Fin n2 → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun n2 D x = false := by
    intro x hcq hnoE
    cases hval : circuitFun n2 D x with
    | false => rfl
    | true =>
      exfalso
      change (run gs (List.ofFn x)).getD out false = true at hval
      exact hWsoundQ x hcq hnoE ((hout_sem x).mp hval)
  have hout_ge : n2 ≤ D.output := by
    by_contra hlt
    change ¬ n2 ≤ out at hlt
    by_cases hltN : out < N
    · let p0 : Fin N := ⟨out, hltN⟩
      let x : Fin n2 → Bool := fun i => decide (i = Fin.castAdd N p0)
      have hcq : Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q := by
        have h0 : Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } = 0 :=
          Fintype.card_eq_zero_iff.mpr ⟨fun l => by
            have hl := l.2; simp only [x, decide_eq_true_eq] at hl
            have := congrArg Fin.val hl; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega⟩
        omega
      have hnoE : ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
        rintro ⟨_, l, _, _, hl⟩
        simp only [x, decide_eq_true_eq] at hl
        have := congrArg Fin.val hl; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      have hf := hFalseD x hcq hnoE
      have ht : circuitFun n2 D x = true := by
        change (run gs (List.ofFn x)).getD out false = true
        have h1 : out < (List.ofFn x).length := by simp only [List.length_ofFn]; omega
        rw [run_keep gs (List.ofFn x) out h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
        simp only [x, decide_eq_true_eq]; apply Fin.ext; rfl
      rw [ht] at hf; cases hf
    · let l0 : Fin N := ⟨out - N, by omega⟩
      let x : Fin n2 → Bool := fun i => decide (i = Fin.natAdd N l0)
      have hcq : Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q := by
        rw [Fintype.card_subtype]
        have hsub : Finset.univ.filter (fun l : Fin N => x (Fin.natAdd N l) = true) ⊆ {l0} := by
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl
          simp only [Finset.mem_singleton]
          exact Fin.ext (by have := congrArg Fin.val hl; simp only [Fin.val_natAdd] at this; omega)
        have hle : (Finset.univ.filter (fun l : Fin N => x (Fin.natAdd N l) = true)).card ≤ 1 := by
          simpa only [Finset.card_singleton] using Finset.card_le_card hsub
        omega
      have hnoE : ¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
        rintro ⟨p, _, _, hp, _⟩
        simp only [x, decide_eq_true_eq] at hp
        have := congrArg Fin.val hp; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      have hf := hFalseD x hcq hnoE
      have ht : circuitFun n2 D x = true := by
        change (run gs (List.ofFn x)).getD out false = true
        have h1 : out < (List.ofFn x).length := by simp only [List.length_ofFn]; omega
        rw [run_keep gs (List.ofFn x) out h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
        simp only [x, decide_eq_true_eq]; apply Fin.ext; change out = N + (out - N); omega
      rw [ht] at hf; cases hf
  obtain ⟨k0, hk0_lt, hk0_and, hk0_sem⟩ := hjk0_s hj0_lt
  have hk0_wit : ∃ k : ℕ, ∃ a b : Fin N, isAnd D k ∧ a ≠ b ∧
      wval D (fun i => decide (i = Fin.natAdd N a)) (n2 + k) = true ∧
      wval D (fun i => decide (i = Fin.natAdd N b)) (n2 + k) = true := by
    have hsp_l (l : Fin N) : splitVec (fun i : Fin n2 => decide (i = Fin.natAdd N l)) = (fun _ => false, e1 l) := by
      apply Prod.ext
      · funext p
        dsimp only [splitVec]
        rw [decide_eq_false_iff_not]
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      · funext l'
        dsimp only [splitVec, e1]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · intro h; exact Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)
        · intro h; subst h; rfl
    refine ⟨k0, l1, l2, ⟨hk0_lt, hk0_and⟩, hl12_ne, ?_, ?_⟩
    · change (run gs (List.ofFn fun i => decide (i = Fin.natAdd N l1))).getD (n2 + k0) false = true
      rw [hk0_sem, hsp_l l1]; exact hl1_in
    · change (run gs (List.ofFn fun i => decide (i = Fin.natAdd N l2))).getD (n2 + k0) false = true
      rw [hk0_sem, hsp_l l2]; exact hl2_in
  have hNoC4 : ∀ (p1 p2 l1 l2 : Fin N), p1 ≠ p2 → l1 ≠ l2 → ¬ (I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
    intro p1 p2 l1 l2 hpne hlne h
    obtain ⟨l, _, hlu⟩ := huniq p1 p2 hpne
    have h1 := hlu l1 ⟨h.1, h.2.2.1⟩
    have h2 := hlu l2 ⟨h.2.1, h.2.2.2⟩
    exact hlne (h1.trans h2.symm)
  have huncov : ∃ p l : Fin N, I p l ∧
      ¬ ∃ j a b : ℕ, andOn D j a b ∧
        orp D n2 (n2 + j) D.output ∧
        orp D n2 p.val a ∧
        orp D n2 (N + l.val) b := by
    by_contra hall_not
    have hall : ∀ p l : Fin N, I p l →
        ∃ j a b : ℕ, andOn D j a b ∧
          orp D n2 (n2 + j) D.output ∧
          orp D n2 p.val a ∧
          orp D n2 (N + l.val) b := by
      intro p l hpl
      by_contra hno
      exact hall_not ⟨p, l, hpl, hno⟩
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
        · intro hI; exact ⟨e.2, e.1, hI, Prod.eta e⟩
        · rintro ⟨l, p, hI, rfl⟩; exact hI
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
    have hRB : ReadsBack n2 D := hD_AO.2.1
    let OrPath : ℕ → ℕ → Prop := fun w target =>
      ∀ Q : ℕ → Prop,
        Q target →
        (∀ k < D.gates.length, (gateAt D k).op = GateOp.or →
          ∀ a ∈ (gateAt D k).inputs, Q a → Q (n2 + k)) →
        Q w
    have orPath_refl (t : ℕ) : OrPath t t := fun _ h _ => h
    have orPath_step {k a t : ℕ} (hk : k < D.gates.length) (hor : (gateAt D k).op = GateOp.or)
        (ha : a ∈ (gateAt D k).inputs) (hp : OrPath a t) : OrPath (n2 + k) t :=
      fun Q ht hs => hs k hk hor a ha (hp Q ht hs)
    have orPath_trans {u v w : ℕ} (huv : OrPath u v) (hvw : OrPath v w) : OrPath u w :=
      fun Q hw hs => huv Q (hvw Q hw hs) hs
    have orPath_cases {w t : ℕ} (h : OrPath w t) :
        w = t ∨ ∃ k < D.gates.length, w = n2 + k ∧ (gateAt D k).op = GateOp.or ∧
          ∃ a ∈ (gateAt D k).inputs, OrPath a t := by
      apply h (fun x => x = t ∨ ∃ k < D.gates.length, x = n2 + k ∧ (gateAt D k).op = GateOp.or ∧
          ∃ a ∈ (gateAt D k).inputs, OrPath a t)
      · exact Or.inl rfl
      · intro k hk hor a ha hPa
        refine Or.inr ⟨k, hk, rfl, hor, a, ha, ?_⟩
        rcases hPa with rfl | ⟨k', hk', rfl, hor', a', ha', hp'⟩
        · exact orPath_refl _
        · exact orPath_step hk' hor' ha' hp'
    have orp_to_orPath {t w : ℕ} (h : orp D n2 t w) : OrPath w t := by
      change Relation.ReflTransGen (fun a b => a < b ∧ ∃ j, b = n2 + j ∧ isOr D j ∧ a ∈ (gateAt D j).inputs) t w at h
      induction h with
      | refl => exact orPath_refl t
      | tail _ hstep ih =>
        obtain ⟨_, j, rfl, ⟨hj, hor⟩, ha⟩ := hstep
        exact orPath_step hj hor ha ih
    have wireVal_input (i : Fin n2) (x : Fin n2 → Bool) :
        wireVal n2 D i.val x = x i := by
      change (run D.gates (List.ofFn x)).getD i.val false = x i
      rw [run_keep D.gates (List.ofFn x) i.val (by simp only [List.length_ofFn]; exact i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
    have wireVal_gate (k : ℕ) (hk : k < D.gates.length) (x : Fin n2 → Bool) :
        wireVal n2 D (n2 + k) x =
          (gateAt D k).op.eval ((gateAt D k).inputs.map fun i => wireVal n2 D i x) := by
      change (run D.gates (List.ofFn x)).getD (n2 + k) false =
        (gateAt D k).op.eval ((gateAt D k).inputs.map fun i =>
          (run D.gates (List.ofFn x)).getD i false)
      have hsplit : D.gates = D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1) := by
        have h1 : D.gates = D.gates.take (k + 1) ++ D.gates.drop (k + 1) :=
          (List.take_append_drop (k + 1) D.gates).symm
        conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem D.gates ⟨GateOp.or, []⟩ hk]
        rfl
      let w0 := run (D.gates.take k) (List.ofFn x)
      have hw0_len : w0.length = n2 + k := by
        dsimp only [w0]; rw [run_len, List.length_ofFn, List.length_take]; omega
      have hw_lt : ∀ i < n2 + k, (run D.gates (List.ofFn x)).getD i false = w0.getD i false := by
        intro i hi
        change (D.gates.foldl step (List.ofFn x)).getD i false = w0.getD i false
        conv_lhs => rw [← List.take_append_drop k D.gates, List.foldl_append]
        exact run_keep (D.gates.drop k) w0 i (by omega)
      change (D.gates.foldl step (List.ofFn x)).getD (n2 + k) false = _
      conv_lhs => rw [hsplit, List.foldl_append, List.foldl_append]
      have hstep_len : (run [gateAt D k] w0).length = n2 + k + 1 := by
        rw [run_len]; simp only [List.length_cons, List.length_nil]; omega
      rw [run_keep (D.gates.drop (k + 1)) (run [gateAt D k] w0) (n2 + k) (by omega)]
      simp only [run, List.foldl_cons, List.foldl_nil, step]
      rw [← hw0_len, getD_snoc_eq w0 _]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (hw_lt i (hRB k hk i hi)).symm
    have wireVal_or_mem {k a : ℕ} (hk : k < D.gates.length) (hor : (gateAt D k).op = GateOp.or)
        (ha : a ∈ (gateAt D k).inputs) (x : Fin n2 → Bool)
        (hva : wireVal n2 D a x = true) :
        wireVal n2 D (n2 + k) x = true := by
      rw [wireVal_gate k hk x, hor]
      change ((gateAt D k).inputs.map fun i => wireVal n2 D i x).any id = true
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩
    have wireVal_and_pair {k a b : ℕ} (hk : k < D.gates.length) (hand : (gateAt D k).op = GateOp.and)
        (hin : (gateAt D k).inputs = [a, b]) (x : Fin n2 → Bool) :
        wireVal n2 D (n2 + k) x = (wireVal n2 D a x && wireVal n2 D b x) := by
      rw [wireVal_gate k hk x, hand, hin]
      change [wireVal n2 D a x, wireVal n2 D b x].all id = (wireVal n2 D a x && wireVal n2 D b x)
      simp
    have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin n2 → Bool)
        (ht : wireVal n2 D t x = true) : wireVal n2 D w x = true := by
      apply hp (fun u => wireVal n2 D u x = true) ht
      intro k hk hor a ha hva
      exact wireVal_or_mem hk hor ha x hva
    have isAO2_gate_inputs {k : ℕ} (hk : k < D.gates.length) :
        ∃ a b : ℕ, (gateAt D k).inputs = [a, b] ∧ a < n2 + k ∧ b < n2 + k := by
      have hmem : gateAt D k ∈ D.gates := by
        change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
        rw [List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      have hlen := hD_AO.2.2 (gateAt D k) hmem
      cases hin : (gateAt D k).inputs with
      | nil => rw [hin] at hlen; simp at hlen
      | cons a t1 =>
        cases t1 with
        | nil => rw [hin] at hlen; simp at hlen
        | cons b t2 =>
          cases t2 with
          | nil =>
            have ha := hD_AO.2.1 k hk a (by rw [hin]; exact List.mem_cons_self)
            have hb := hD_AO.2.1 k hk b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
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
        dsimp only [mergeStep]; simp only [hit, rest, hhit_ne, ↓reduceIte]
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
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hc : u ∈ B ∨ v ∈ B
          · exact Or.inl ⟨h, hc⟩
          · exact Or.inr ⟨h, hc⟩
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
        let a := (gateAt D o.val).inputs.getD 0 0
        let b := (gateAt D o.val).inputs.getD 1 0
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
        have ha_get : (gateAt D o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
        have hb_get : (gateAt D o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
        dsimp only [pairOf] at hpair_eq
        rw [ha_get, hb_get] at hpair_eq
        split_ifs at hpair_eq with hne
        injection hpair_eq with hpr_eq
        rw [← hpr_eq]
        have hu : hne.1.choose ∈ reach a := hne.1.choose_spec
        have hv : hne.2.choose ∈ reach b := hne.2.choose_spec
        have hua : OrPath a (wireOf hne.1.choose) := (Finset.mem_filter.mp hu).2
        have hvb : OrPath b (wireOf hne.2.choose) := (Finset.mem_filter.mp hv).2
        have ha_mem : a ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_self
        have hb_mem : b ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
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
            have hstep_ex : ∃ k < D.gates.length, w = n2 + k ∧ (gateAt D k).op = GateOp.or := by
              rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
              · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
                · exact (hne_w h2).elim
                · exact ⟨k, hk, hwk, hor⟩
              · exact ⟨k, hk, hwk, hor⟩
            obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
            let o : Fin D.gates.length := ⟨k, hk⟩
            have h2card : 2 ≤ (reach (n2 + o.val)).card := by
              rw [← hwk]
              exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
            have ho_mem : o ∈ O_S :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hor, h2card, j, hjS, hwk ▸ hjw⟩
            obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := isAO2_gate_inputs hk
            have ha_mem : a ∈ (gateAt D k).inputs := by rw [hab]; exact List.mem_cons_self
            have hb_mem : b ∈ (gateAt D k).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
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
                have ha_get : (gateAt D o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                have hb_get : (gateAt D o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
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
                have ha_get : (gateAt D o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                have hb_get : (gateAt D o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
                rw [ha_get, hb_get]; split_ifs; rfl
              obtain ⟨B1, hB1Q, hx2B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x2 h2a hne_ab.1.choose hne_ab.1.choose_spec
              obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
              obtain ⟨B3, hB3Q, hvB3, hx1B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x1 h1b
              have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
              have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
              subst h12B; subst h23B
              exact ⟨B1, hB1Q, hx1B3, hx2B1⟩
            · exact ih b (by omega) ⟨j, hjS, hjb⟩ x1 h1b x2 h2b
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
          ∃ a b : ℕ, (gateAt D j.val).inputs = [a, b] ∧
            ((OrPath a p.val ∧ OrPath b (N + l.val)) ∨
             (OrPath a (N + l.val) ∧ OrPath b p.val)) := by
      intro p l hpl
      obtain ⟨j, a, b, handOn, htop, hpa, hlb⟩ := hall p l ((hmem_E p l).mp hpl)
      obtain ⟨⟨hjlt, hjand⟩, hor_ab⟩ := handOn
      obtain ⟨a0, b0, hab0, _, _⟩ := isAO2_gate_inputs hjlt
      have hin0 : in0 D j = a0 := by change (gateAt D j).inputs.getD 0 0 = a0; rw [hab0]; rfl
      have hin1 : in1 D j = b0 := by change (gateAt D j).inputs.getD 1 0 = b0; rw [hab0]; rfl
      refine ⟨⟨j, hjlt⟩, hjand, orp_to_orPath htop, a0, b0, hab0, ?_⟩
      rcases hor_ab with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
        exact Or.inl ⟨orp_to_orPath hpa, orp_to_orPath hlb⟩
      · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
        exact Or.inr ⟨orp_to_orPath hlb, orp_to_orPath hpa⟩
    let Tstar : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun j =>
        (gateAt D j.val).op = GateOp.and ∧
        OrPath D.output (n2 + j.val) ∧
        ∃ p l : Fin N, ∃ a b : ℕ, (gateAt D j.val).inputs = [a, b] ∧
          ((OrPath a p.val ∧ OrPath b (N + l.val)) ∨
           (OrPath a (N + l.val) ∧ OrPath b p.val)))
    let pWire (j : Fin D.gates.length) : ℕ :=
      let a := (gateAt D j.val).inputs.getD 0 0
      let b := (gateAt D j.val).inputs.getD 1 0
      if (pts a).Nonempty then a else b
    let lWire (j : Fin D.gates.length) : ℕ :=
      let a := (gateAt D j.val).inputs.getD 0 0
      let b := (gateAt D j.val).inputs.getD 1 0
      if (pts a).Nonempty then b else a
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
      obtain ⟨hand, htop, p0, l0, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
      have ha_get : (gateAt D j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt D j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
      have hand_sound : ∀ x : Fin n2 → Bool,
          wireVal n2 D a x = true → wireVal n2 D b x = true → wireVal n2 D D.output x = true := by
        intro x hxa hxb
        apply orPath_sound htop x
        rw [wireVal_and_pair j.isLt hand hab x, hxa, hxb]
        rfl
      have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
        rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
        let x : Fin n2 → Bool := fun i => decide (i = Fin.castAdd N p1 ∨ i = Fin.castAdd N p2)
        have h1 : wireVal n2 D p1.val x = true := by
          have := wireVal_input (Fin.castAdd N p1) x; simpa [x] using this
        have h2 : wireVal n2 D p2.val x = true := by
          have := wireVal_input (Fin.castAdd N p2) x; simpa [x] using this
        have ht := hand_sound x
          (orPath_sound (Finset.mem_filter.mp hp1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hp2).2 x h2)
        have hf := hno_pts_only x (fun l => by
          simp only [x, decide_eq_false_iff_not]
          rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
        rw [ht] at hf; cases hf
      have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
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
        have ht := hand_sound x
          (orPath_sound (Finset.mem_filter.mp hl1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hl2).2 x h2)
        have hf := hno_lns_only2 l1 l2
        rw [ht] at hf; cases hf
      have hbiclique : ∀ (p l : Fin N),
          ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → (p, l) ∈ E := by
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
        have hf : wireVal n2 D D.output x = false := hFalseD x (by omega) hnoE
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
    have hE_in_Tstar : ∀ p l : Fin N, (p, l) ∈ E →
        ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
      intro p l hpl
      obtain ⟨j, hand, htop, a, b, hab, hlr⟩ := hedge_covered p l hpl
      have hjT : j ∈ Tstar :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hand, htop, p, l, a, b, hab, hlr⟩
      have hprops := hTstar_props j hjT
      have ha_get : (gateAt D j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt D j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
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
          rw [hpW] at hlem
          rw [hlem] at hla_m; cases hla_m
        have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
        have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
        exact ⟨by simpa [pSide, hpW] using hpb_m, by simpa [lSide, hlW] using hla_m⟩
    let Tpt : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
    let Tln : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
    have hTpt_Tln_disj : Disjoint Tpt Tln := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hTpt_Tln_union : Tpt ∪ Tln = Tstar := by
      ext j
      simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h1 : (pSide j).card = 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr ⟨h, h1⟩
    have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
      rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
    let centerP (j : Fin D.gates.length) : Fin N :=
      if h : (pSide j).Nonempty then h.choose else ⟨0, hNpos⟩
    let centerL (j : Fin D.gates.length) : Fin N :=
      if h : (lSide j).Nonempty then h.choose else ⟨0, hNpos⟩
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
      have hand := (hTstar_props o h2).1
      rcases Finset.mem_union.mp h1 with hA | hB
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
        have hor := (Finset.mem_filter.mp ho).2.1
        rw [hor] at hand; cases hand
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
        have hor := (Finset.mem_filter.mp ho).2.1
        rw [hor] at hand; cases hand
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
  have hout_idx_lt : D.output - n2 < D.gates.length := by
    change out - n2 < gs.length
    change n2 ≤ out at hout_ge
    omega
  have hout_mem : gateAt D (D.output - n2) ∈ D.gates := by
    change D.gates.getD (D.output - n2) ⟨GateOp.or, []⟩ ∈ D.gates
    rw [List.getD_eq_getElem _ _ hout_idx_lt]
    exact List.getElem_mem hout_idx_lt
  by_cases hpt : ∃ (k1 : ℕ) (p1 : Fin N), isAnd D k1 ∧
      wval D (fun i => decide (i = Fin.castAdd N p1)) (n2 + k1) = true
  · rcases hD_AO.1 _ hout_mem with hand_out | hor_out
    · exact hAndOutPtDirty q N I D hq hN hcard huniq hD_AO hD_sz hTrueD hFalseD
        hout_ge ⟨hout_idx_lt, hand_out⟩ huncov hk0_wit hpt
    · exact hOrOutPtDirty q N I D hq hN hcard huniq hD_AO hD_sz hTrueD hFalseD
        hout_ge ⟨hout_idx_lt, hor_out⟩ huncov hk0_wit hpt
  · have hpt_clean : ∀ k1 : ℕ, isAnd D k1 →
        ∀ p1 : Fin N, wval D (fun i => decide (i = Fin.castAdd N p1)) (n2 + k1) = false := by
      intro k1 hk1 p1
      cases hval : wval D (fun i => decide (i = Fin.castAdd N p1)) (n2 + k1) with
      | false => rfl
      | true => exact (hpt ⟨k1, p1, hk1, hval⟩).elim
    rcases hD_AO.1 _ hout_mem with hand_out | hor_out
    · exact hAndOutPtClean q N I D hq hN hcard huniq hD_AO hD_sz hTrueD hFalseD
        hout_ge ⟨hout_idx_lt, hand_out⟩ huncov hk0_wit hpt_clean
    · exact hOrOutPtClean q N I D hq hN hcard huniq hD_AO hD_sz hTrueD hFalseD
        hout_ge ⟨hout_idx_lt, hor_out⟩ huncov hk0_wit hpt_clean
