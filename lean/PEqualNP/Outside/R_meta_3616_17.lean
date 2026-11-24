import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_3616_17
    (hPureMono :
      have S : List ℕ := [3, 6, 12, 13, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 133, 138, 160, 200, 201, 208, 261, 264, 265, 276, 288, 320, 321, 385, 402]
      have P : List ℕ := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        1 ≤ C.gates.length →
        C.gates.length ≤ 14 →
        C.output = 8 + C.gates.length →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[j]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 9 + j) →
        (∀ m ∈ S, C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val)) = decide (m ∈ P)) →
        False)
    (hNeg0OnlyAnd :
      have S : List ℕ := [3, 6, 12, 13, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 133, 138, 160, 200, 201, 208, 261, 264, 265, 276, 288, 320, 321, 385, 402]
      have P : List ℕ := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        1 ≤ C.gates.length →
        C.gates.length ≤ 14 →
        C.output = 9 + C.gates.length →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[j]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 10 + j ∧ ¬ (a = 0 ∧ b = 9)) →
        (∀ m ∈ S, C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [!m.testBit 0]) = decide (m ∈ P)) →
        (∃ g ∈ C.gates, 9 ∈ g.inputs) →
        (∀ g ∈ C.gates, 9 ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        False)
    (hNeg0OnlyOr :
      have S : List ℕ := [3, 6, 12, 13, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 133, 138, 160, 200, 201, 208, 261, 264, 265, 276, 288, 320, 321, 385, 402]
      have P : List ℕ := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        1 ≤ C.gates.length →
        C.gates.length ≤ 14 →
        C.output = 9 + C.gates.length →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[j]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 10 + j ∧ ¬ (a = 0 ∧ b = 9)) →
        (∀ m ∈ S, C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [!m.testBit 0]) = decide (m ∈ P)) →
        (∃ g ∈ C.gates, 9 ∈ g.inputs) →
        (∀ g ∈ C.gates, 9 ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        False)
    (hNeg0Both :
      have S : List ℕ := [3, 6, 12, 13, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 133, 138, 160, 200, 201, 208, 261, 264, 265, 276, 288, 320, 321, 385, 402]
      have P : List ℕ := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        1 ≤ C.gates.length →
        C.gates.length ≤ 14 →
        C.output = 9 + C.gates.length →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[j]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 10 + j ∧ ¬ (a = 0 ∧ b = 9)) →
        (∀ m ∈ S, C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [!m.testBit 0]) = decide (m ∈ P)) →
        (∃ g ∈ C.gates, 9 ∈ g.inputs ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∃ g ∈ C.gates, 9 ∈ g.inputs ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        False) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (∀ (x7 : Fin x1), (x3 x7).1 < (10 : ℕ) + ↑x7 ∧ (x4 x7).1 < (10 : ℕ) + ↑x7) →     x5.1 < (10 : ℕ) + x1 →       x5.2 = Bool.false →         x1 ≤ (14 : ℕ) →           (have x11 : ℕ × Bool → Prop := fun (x11 : ℕ × Bool) => x11.2 = Bool.true → x11.1 = (0 : ℕ) ∨ x11.1 = (9 : ℕ);             x11 x5 ∧ ∀ (x12 : Fin x1), x11 (x3 x12) ∧ x11 (x4 x12)) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin (9 : ℕ)), x6 x12 ↑x13 = x12 x13) →               (∀ (x13 : Fin (9 : ℕ) → Bool), x6 x13 (9 : ℕ) = Bool.false) →                 (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin x1),                     have x16 : ℕ × Bool → Bool := fun (x16 : ℕ × Bool) => x6 x14 x16.1 ^^ x16.2;                     x6 x14 ((10 : ℕ) + ↑x15) = if x2 x15 = Bool.true then x16 (x3 x15) && x16 (x4 x15) else x16 (x3 x15) || x16 (x4 x15)) →                   (∀ x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (133 : ℕ), (138 : ℕ), (160 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (265 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (385 : ℕ), (402 : ℕ)],                       have x17 : Fin (9 : ℕ) → Bool := fun (x17 : Fin (9 : ℕ)) => x15.testBit ↑x17;                       (x6 x17 x5.1 ^^ x5.2) = Decidable.decide (x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ)])) →                     False := by
  intro x1 x2 x3 x4 x5 x6 hlt hx5_lt hx5_pol hx1_le hpol hbase9 hwire9 hgates hsep
  let S : List ℕ := [3, 6, 12, 13, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 133, 138, 160, 200, 201, 208, 261, 264, 265, 276, 288, 320, 321, 385, 402]
  let P : List ℕ := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321]
  have hConstFail : ∀ c : Bool, ∃ m ∈ S, c ≠ decide (m ∈ P) := by decide
  have hBaseFail : ∀ w < 10, ∃ m ∈ S,
      (if w < 9 then m.testBit w else !m.testBit 0) ≠ decide (m ∈ P) := by decide
  have hand_eval (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    change (a && (b && true)) = (a && b)
    exact congrArg (a && ·) (Bool.and_true b)
  have hor_eval (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    change (a || (b || false)) = (a || b)
    exact congrArg (a || ·) (Bool.or_false b)
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
  let inp : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0]
  have inp_len (x : Fin 9 → Bool) : (inp x).length = 10 := by
    simp only [inp, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne (l : List Bool) (a : Bool) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j false = l.getD j false := by
    by_cases hltj : j < l.length
    · exact List.getD_append _ _ _ _ hltj
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
  have inp_getD_lt (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
      (inp x).getD i false = x ⟨i, hi⟩ := by
    have hlt9 : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hi
    dsimp only [inp]
    rw [List.getD_append _ _ _ _ hlt9, List.getD_eq_getElem _ _ hlt9, List.getElem_ofFn]
  have inp_getD_9 (x : Fin 9 → Bool) : (inp x).getD 9 false = !x 0 := by
    dsimp only [inp]
    simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x) (!x 0)
  let CleanGates : List Gate → Prop := fun gs =>
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 10 + j ∧ ¬ (a = 0 ∧ b = 9)
  have hCompile : ∀ k ≤ x1, ∃ gs : List Gate,
      gs.length ≤ k ∧ CleanGates gs ∧
      ∀ i < 10 + k,
        (∃ c : Bool, ∀ x : Fin 9 → Bool, x6 x i = c) ∨
        (∃ w < 10 + gs.length, ∀ x : Fin 9 → Bool, x6 x i = (run gs (inp x)).getD w false) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Nat.le_refl 0, (fun j g hj => by cases hj), ?_⟩
      intro i hi
      by_cases hi9 : i < 9
      · refine Or.inr ⟨i, by simp only [List.length_nil]; omega, fun x => ?_⟩
        have h1 : x6 x i = x ⟨i, hi9⟩ := hbase9 x ⟨i, hi9⟩
        rw [h1]
        exact (inp_getD_lt x i hi9).symm
      · have hi_eq : i = 9 := by omega
        subst hi_eq
        exact Or.inl ⟨false, fun x => hwire9 x⟩
    | succ k ih =>
      intro hk1
      obtain ⟨gs, hgs_len, hgs_clean, hmap⟩ := ih (by omega)
      let jf : Fin x1 := ⟨k, hk1⟩
      have hLift (p : ℕ × Bool) (hp_lt : p.1 < 10 + k)
          (hp_pol : p.2 = true → p.1 = 0 ∨ p.1 = 9) :
          (∃ c : Bool, ∀ x : Fin 9 → Bool, (x6 x p.1 ^^ p.2) = c) ∨
          (∃ w < 10 + gs.length, ∀ x : Fin 9 → Bool, (x6 x p.1 ^^ p.2) = (run gs (inp x)).getD w false) := by
        cases hp2 : p.2
        · simpa only [Bool.xor_false] using hmap p.1 hp_lt
        · rcases hp_pol hp2 with h0 | h9
          · refine Or.inr ⟨9, by omega, fun x => ?_⟩
            rw [h0]
            have h0x : x6 x 0 = x 0 := hbase9 x 0
            rw [h0x, Bool.xor_true, run_keep gs (inp x) 9 (by rw [inp_len]; omega), inp_getD_9]
          · refine Or.inl ⟨true, fun x => ?_⟩
            rw [h9, hwire9 x]
            rfl
      have hL := hLift (x3 jf) (hlt jf).1 (hpol.2 jf).1
      have hR := hLift (x4 jf) (hlt jf).2 (hpol.2 jf).2
      have hStepSelf (hnew :
          (∃ c : Bool, ∀ x : Fin 9 → Bool, x6 x (10 + k) = c) ∨
          (∃ w < 10 + gs.length, ∀ x : Fin 9 → Bool, x6 x (10 + k) = (run gs (inp x)).getD w false)) :
          ∃ gs' : List Gate, gs'.length ≤ k + 1 ∧ CleanGates gs' ∧
            ∀ i < 10 + (k + 1),
              (∃ c : Bool, ∀ x : Fin 9 → Bool, x6 x i = c) ∨
              (∃ w < 10 + gs'.length, ∀ x : Fin 9 → Bool, x6 x i = (run gs' (inp x)).getD w false) := by
        refine ⟨gs, by omega, hgs_clean, fun i hi => ?_⟩
        by_cases heq : i = 10 + k
        · subst heq; exact hnew
        · exact hmap i (by omega)
      have hEvalK (x : Fin 9 → Bool) :
          x6 x (10 + k) =
            if x2 jf = true then
              (x6 x (x3 jf).1 ^^ (x3 jf).2) && (x6 x (x4 jf).1 ^^ (x4 jf).2)
            else
              (x6 x (x3 jf).1 ^^ (x3 jf).2) || (x6 x (x4 jf).1 ^^ (x4 jf).2) :=
        hgates x jf
      rcases hL with ⟨c1, hc1⟩ | ⟨u, hu, hwu⟩
      · rcases hR with ⟨c2, hc2⟩ | ⟨v, hv, hwv⟩
        · apply hStepSelf
          refine Or.inl ⟨if x2 jf = true then c1 && c2 else c1 || c2, fun x => ?_⟩
          rw [hEvalK x, hc1 x, hc2 x]
        · apply hStepSelf
          cases hop : x2 jf <;> cases c1
          · refine Or.inr ⟨v, hv, fun x => ?_⟩
            rw [hEvalK x, hop, hc1 x, hwv x]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
          · refine Or.inl ⟨true, fun x => ?_⟩
            rw [hEvalK x, hop, hc1 x]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_or]
          · refine Or.inl ⟨false, fun x => ?_⟩
            rw [hEvalK x, hop, hc1 x]
            simp only [↓reduceIte, Bool.false_and]
          · refine Or.inr ⟨v, hv, fun x => ?_⟩
            rw [hEvalK x, hop, hc1 x, hwv x]
            simp only [↓reduceIte, Bool.true_and]
      · rcases hR with ⟨c2, hc2⟩ | ⟨v, hv, hwv⟩
        · apply hStepSelf
          cases hop : x2 jf <;> cases c2
          · refine Or.inr ⟨u, hu, fun x => ?_⟩
            rw [hEvalK x, hop, hwu x, hc2 x]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false]
          · refine Or.inl ⟨true, fun x => ?_⟩
            rw [hEvalK x, hop, hc2 x]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_true]
          · refine Or.inl ⟨false, fun x => ?_⟩
            rw [hEvalK x, hop, hc2 x]
            simp only [↓reduceIte, Bool.and_false]
          · refine Or.inr ⟨u, hu, fun x => ?_⟩
            rw [hEvalK x, hop, hwu x, hc2 x]
            simp only [↓reduceIte, Bool.and_true]
        · by_cases huv : u = v
          · apply hStepSelf
            refine Or.inr ⟨u, hu, fun x => ?_⟩
            rw [hEvalK x, hwu x, hwv x, ← huv]
            cases x2 jf <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.and_self, Bool.or_self]
          · by_cases hcomp : (u = 0 ∧ v = 9) ∨ (u = 9 ∧ v = 0)
            · apply hStepSelf
              refine Or.inl ⟨!x2 jf, fun x => ?_⟩
              have hw0 : (run gs (inp x)).getD 0 false = x 0 := by
                rw [run_keep gs (inp x) 0 (by rw [inp_len]; omega), inp_getD_lt x 0 (by omega)]
                rfl
              have hw9 : (run gs (inp x)).getD 9 false = !x 0 := by
                rw [run_keep gs (inp x) 9 (by rw [inp_len]; omega), inp_getD_9]
              rw [hEvalK x, hwu x, hwv x]
              rcases hcomp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [hw0, hw9]
                cases x2 jf <;> cases x 0 <;> rfl
              · rw [hw0, hw9]
                cases x2 jf <;> cases x 0 <;> rfl
            · let a : ℕ := min u v
              let b : ℕ := max u v
              let g : Gate := ⟨if x2 jf = true then GateOp.and else GateOp.or, [a, b]⟩
              refine ⟨gs ++ [g], by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_, ?_⟩
              · intro j g' hj'
                by_cases hltj : j < gs.length
                · rw [List.getElem?_append_left hltj] at hj'
                  exact hgs_clean j g' hj'
                · by_cases heqj : j = gs.length
                  · subst heqj
                    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hj'
                    subst hj'
                    refine ⟨?_, a, b, rfl, by omega, by omega, ?_⟩
                    · dsimp only [g]
                      cases x2 jf
                      · exact Or.inr rfl
                      · exact Or.inl rfl
                    · intro h09
                      have ha0 := h09.1
                      have hb9 := h09.2
                      have hcases : (u = 0 ∧ v = 9) ∨ (u = 9 ∧ v = 0) := by omega
                      exact hcomp hcases
                  · rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at hj'
                    cases hj'
              · intro i hi
                by_cases heq : i = 10 + k
                · subst heq
                  refine Or.inr ⟨10 + gs.length, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
                  rw [run_snoc gs g (inp x)]
                  have hlen_run : (run gs (inp x)).length = 10 + gs.length := by
                    rw [run_len, inp_len]
                  have hsnoc : (step (run gs (inp x)) g).getD (10 + gs.length) false =
                      g.op.eval (g.inputs.map fun idx => (run gs (inp x)).getD idx false) := by
                    dsimp only [step]
                    rw [← hlen_run, getD_snoc_eq (run gs (inp x)) _]
                  rw [hsnoc, hEvalK x, hwu x, hwv x]
                  dsimp only [g, List.map]
                  have hpair :
                      ((if x2 jf = true then
                        (run gs (inp x)).getD u false && (run gs (inp x)).getD v false
                      else
                        (run gs (inp x)).getD u false || (run gs (inp x)).getD v false) =
                      (if x2 jf = true then
                        (run gs (inp x)).getD a false && (run gs (inp x)).getD b false
                      else
                        (run gs (inp x)).getD a false || (run gs (inp x)).getD b false)) := by
                    by_cases hle : u ≤ v
                    · have ha : a = u := Nat.min_eq_left hle
                      have hb : b = v := Nat.max_eq_right hle
                      rw [ha, hb]
                    · have ha : a = v := Nat.min_eq_right (by omega)
                      have hb : b = u := Nat.max_eq_left (by omega)
                      rw [ha, hb]
                      cases x2 jf
                      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_comm]
                      · simp only [↓reduceIte, Bool.and_comm]
                  rw [hpair]
                  cases x2 jf
                  · simp only [Bool.false_eq_true, ↓reduceIte, hor_eval]
                  · simp only [↓reduceIte, hand_eval]
                · rcases hmap i (by omega) with ⟨c, hc⟩ | ⟨w, hw, hww⟩
                  · exact Or.inl ⟨c, hc⟩
                  · refine Or.inr ⟨w, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
                    rw [hww x, run_snoc gs g (inp x)]
                    have hlen_run : (run gs (inp x)).length = 10 + gs.length := by
                      rw [run_len, inp_len]
                    have hne : w ≠ (run gs (inp x)).length := by omega
                    exact (getD_snoc_ne (run gs (inp x)) _ w hne).symm
  obtain ⟨gs, hgs_len, hgs_clean, hmap⟩ := hCompile x1 (Nat.le_refl x1)
  have hsep0 : ∀ m ∈ S, x6 (fun i : Fin 9 => m.testBit i.val) x5.1 = decide (m ∈ P) := by
    intro m hm
    have h := hsep m hm
    dsimp only at h
    rw [hx5_pol, Bool.xor_false] at h
    exact h
  rcases hmap x5.1 hx5_lt with ⟨c, hc⟩ | ⟨w, hw_lt, hww⟩
  · obtain ⟨m, hmS, hne⟩ := hConstFail c
    exact hne ((hc (fun i : Fin 9 => m.testBit i.val)).symm.trans (hsep0 m hmS))
  · by_cases hw10 : w < 10
    · obtain ⟨m, hmS, hne⟩ := hBaseFail w hw10
      have h1 := hww (fun i : Fin 9 => m.testBit i.val)
      rw [hsep0 m hmS] at h1
      rw [run_keep gs (inp (fun i : Fin 9 => m.testBit i.val)) w (by rw [inp_len]; exact hw10)] at h1
      by_cases hw9 : w < 9
      · rw [inp_getD_lt _ w hw9] at h1
        simp only [hw9, ↓reduceIte] at hne
        exact hne h1.symm
      · have hw_eq : w = 9 := by omega
        subst hw_eq
        rw [inp_getD_9] at h1
        simp only [Nat.lt_irrefl, ↓reduceIte] at hne
        exact hne h1.symm
    · let k0 : ℕ := w - 10
      have hk0_lt : k0 < gs.length := by omega
      let gs1 : List Gate := gs.take (k0 + 1)
      have hgs1_len : gs1.length = k0 + 1 := by
        simp only [gs1, List.length_take]
        omega
      let C : Circuit := ⟨gs1, 9 + gs1.length⟩
      have hC_ge1 : 1 ≤ C.gates.length := by change 1 ≤ gs1.length; omega
      have hC_le14 : C.gates.length ≤ 14 := by change gs1.length ≤ 14; omega
      have hC_out : C.output = 9 + C.gates.length := rfl
      have hC_clean : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 10 + j ∧ ¬ (a = 0 ∧ b = 9) := by
        intro j g hj
        change (gs.take (k0 + 1))[j]? = some g at hj
        by_cases hltj : j < k0 + 1
        · rw [List.getElem?_take_of_lt hltj] at hj
          exact hgs_clean j g hj
        · rw [List.getElem?_eq_none (by simp only [List.length_take]; omega)] at hj
          cases hj
      have hC_sep : ∀ m ∈ S,
          C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [!m.testBit 0]) = decide (m ∈ P) := by
        intro m hm
        let xm : Fin 9 → Bool := fun i => m.testBit i.val
        have h1 : x6 xm x5.1 = decide (m ∈ P) := hsep0 m hm
        have h2 : x6 xm x5.1 = (run gs (inp xm)).getD w false := hww xm
        have hsplit : gs = gs1 ++ gs.drop (k0 + 1) := (List.take_append_drop (k0 + 1) gs).symm
        have hw_eq : 9 + gs1.length = w := by omega
        have h3 : (run gs (inp xm)).getD w false = (run gs1 (inp xm)).getD w false := by
          conv_lhs => rw [hsplit, run_append]
          exact run_keep (gs.drop (k0 + 1)) (run gs1 (inp xm)) w (by rw [run_len, inp_len, hgs1_len]; omega)
        change (run gs1 (inp xm)).getD (9 + gs1.length) false = decide (m ∈ P)
        rw [hw_eq, ← h3, ← h2, h1]
      by_cases h9 : ∃ g ∈ C.gates, 9 ∈ g.inputs
      · by_cases hAnd9 : ∃ g ∈ C.gates, 9 ∈ g.inputs ∧ g.op = GateOp.and
        · by_cases hOr9 : ∃ g ∈ C.gates, 9 ∈ g.inputs ∧ g.op = GateOp.or
          · exact hNeg0Both C hC_ge1 hC_le14 hC_out hC_clean hC_sep hAnd9 hOr9
          · apply hNeg0OnlyAnd C hC_ge1 hC_le14 hC_out hC_clean hC_sep h9
            intro g hg hg9
            obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem hg
            have hcj := hC_clean j C.gates[j] (List.getElem?_eq_getElem hj_lt)
            rcases hcj.1 with hop | hop
            · exact hop
            · exact absurd ⟨C.gates[j], hg, hg9, hop⟩ hOr9
        · apply hNeg0OnlyOr C hC_ge1 hC_le14 hC_out hC_clean hC_sep h9
          intro g hg hg9
          obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem hg
          have hcj := hC_clean j C.gates[j] (List.getElem?_eq_getElem hj_lt)
          rcases hcj.1 with hop | hop
          · exact absurd ⟨C.gates[j], hg, hg9, hop⟩ hAnd9
          · exact hop
      · have hno9 : ∀ g ∈ C.gates, 9 ∉ g.inputs := fun g hg h9in => h9 ⟨g, hg, h9in⟩
        let drop9 : ℕ → ℕ := fun i => if i < 9 then i else i - 1
        have drop9_sim (gs' : List Gate) (hgs' : ∀ g ∈ gs', 9 ∉ g.inputs)
            (wA wB : List Bool) (hwA : 9 ≤ wA.length) (hwB : wB.length = wA.length + 1)
            (hrel : ∀ i, i ≠ 9 → wA.getD (drop9 i) false = wB.getD i false) :
            ∀ i, i ≠ 9 → (run (gs'.map fun g => ⟨g.op, g.inputs.map drop9⟩) wA).getD (drop9 i) false =
              (run gs' wB).getD i false := by
          induction gs' generalizing wA wB with
          | nil => exact hrel
          | cons g rest ih =>
            simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
            have hg9 : 9 ∉ g.inputs := hgs' g List.mem_cons_self
            have hinp : (g.inputs.map drop9).map (fun j => wA.getD j false) =
                g.inputs.map (fun i => wB.getD i false) := by
              rw [List.map_map]
              apply List.map_congr_left
              intro i hi
              exact hrel i (fun h => hg9 (h ▸ hi))
            let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
            have hstepA : step wA ⟨g.op, g.inputs.map drop9⟩ = wA ++ [b] := by
              dsimp only [step, b]; rw [hinp]
            rw [hstepA]
            apply ih (fun g' hg' => hgs' g' (List.mem_cons_of_mem g hg')) (wA ++ [b]) (step wB g)
            · simp only [List.length_append, List.length_cons, List.length_nil]; omega
            · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            · intro i hi9
              dsimp only [step]
              by_cases heq : i = wB.length
              · subst heq
                have hdr : drop9 wB.length = wA.length := by
                  dsimp only [drop9]
                  split
                  · omega
                  · omega
                rw [hdr, getD_snoc_eq wA b, getD_snoc_eq wB b]
              · have hdr_ne : drop9 i ≠ wA.length := by
                  dsimp only [drop9]
                  split
                  · omega
                  · omega
                rw [getD_snoc_ne wA b (drop9 i) hdr_ne, getD_snoc_ne wB b i heq]
                exact hrel i hi9
        let D : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map drop9⟩), 8 + C.gates.length⟩
        have hD_len : D.gates.length = C.gates.length := List.length_map _
        have hD_ge1 : 1 ≤ D.gates.length := by rw [hD_len]; exact hC_ge1
        have hD_le14 : D.gates.length ≤ 14 := by rw [hD_len]; exact hC_le14
        have hD_out : D.output = 8 + D.gates.length := by change 8 + C.gates.length = 8 + D.gates.length; rw [hD_len]
        have hD_clean : ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
            (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
            ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 9 + j := by
          intro j g hj
          change (C.gates.map fun g0 => ⟨g0.op, g0.inputs.map drop9⟩)[j]? = some g at hj
          rw [List.getElem?_map, Option.map_eq_some_iff] at hj
          obtain ⟨g0, hg0j, rfl⟩ := hj
          have hcj := hC_clean j g0 hg0j
          have hg0_mem : g0 ∈ C.gates := by
            have h1 := (List.getElem?_eq_some_iff).mp hg0j
            rw [← h1.2]
            exact List.getElem_mem h1.1
          have hg0_no9 : 9 ∉ g0.inputs := hno9 g0 hg0_mem
          obtain ⟨a, b, hab, hltab, hltb, _⟩ := hcj.2
          have ha9 : a ≠ 9 := fun h => hg0_no9 (by rw [hab, h]; exact List.mem_cons_self)
          have hb9 : b ≠ 9 := fun h => hg0_no9 (by rw [hab, h]; exact List.mem_cons_of_mem a List.mem_cons_self)
          refine ⟨hcj.1, drop9 a, drop9 b, by rw [hab]; rfl, ?_, ?_⟩
          · dsimp only [drop9]
            by_cases ha : a < 9 <;> by_cases hb : b < 9 <;> simp only [ha, hb, ↓reduceIte] <;> omega
          · dsimp only [drop9]
            by_cases hb : b < 9 <;> simp only [hb, ↓reduceIte] <;> omega
        have hD_sep : ∀ m ∈ S,
            D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val)) = decide (m ∈ P) := by
          intro m hm
          let xm : Fin 9 → Bool := fun i => m.testBit i.val
          have hbase : ∀ i, i ≠ 9 →
              (List.ofFn xm).getD (drop9 i) false = (List.ofFn xm ++ [!xm 0]).getD i false := by
            intro i hi9
            by_cases hi : i < 9
            · have hdr : drop9 i = i := by simp only [drop9, hi, ↓reduceIte]
              rw [hdr]
              exact (List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hi)).symm
            · have hdr : drop9 i = i - 1 := by simp only [drop9, hi, ↓reduceIte]
              rw [hdr,
                  List.getD_eq_default (List.ofFn xm) false (n := i - 1) (by simp only [List.length_ofFn]; omega),
                  List.getD_eq_default (List.ofFn xm ++ [!xm 0]) false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
          have hev := drop9_sim C.gates hno9 (List.ofFn xm) (List.ofFn xm ++ [!xm 0])
            (by simp only [List.length_ofFn]; omega)
            (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
            hbase C.output (by rw [hC_out]; omega)
          have hdr_out : drop9 C.output = 8 + C.gates.length := by
            dsimp only [drop9]
            rw [hC_out]
            have hnot : ¬ (9 + C.gates.length < 9) := by omega
            simp only [hnot, ↓reduceIte]
            omega
          rw [hdr_out] at hev
          change (run D.gates (List.ofFn xm)).getD (8 + C.gates.length) false = decide (m ∈ P)
          rw [hev]
          exact hC_sep m hm
        exact hPureMono D hD_ge1 hD_le14 hD_out hD_clean hD_sep
