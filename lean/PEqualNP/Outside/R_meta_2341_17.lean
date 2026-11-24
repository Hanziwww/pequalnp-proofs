import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadTwo

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2341_17
    (hCleanUncovered :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (p0 : Fin 13),
        have D7 : Finset (Fin 13) := {0, 1, 3, 9};
        have x8 : Fin 13 → Fin 13 → List Bool := fun p l =>
          (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l);
        have x9 : Finset (Fin 13) → List Bool := fun Q =>
          (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ D7);
        have isQuad : Finset (Fin 13) → Prop := fun Q => Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | p - l ∈ D7}.card ≤ 2;
        PEqualNP.TopForm.IsAO2 26 D →
        (∀ p l : Fin 13, p - l ∈ D7 → (p ≠ p0 ∨ l ≠ 0) → D.eval (x8 p l) = true) →
        (∀ Q : Finset (Fin 13), isQuad Q → D.eval (x9 Q) = false) →
        (∃ p l : Fin 13, p - l ∈ D7 ∧ (p ≠ p0 ∨ l ≠ 0) ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 26 p.val a ∧
            PEqualNP.ReadTwo.orp D 26 (13 + l.val) b) →
        (∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ Q : Finset (Fin 13), isQuad Q → (D.wires (x9 Q)).getD (26 + j) false = false) →
        63 ≤ D.size)
    (hDirtyOneHot :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (p0 : Fin 13),
        have D7 : Finset (Fin 13) := {0, 1, 3, 9};
        have x8 : Fin 13 → Fin 13 → List Bool := fun p l =>
          (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l);
        have x9 : Finset (Fin 13) → List Bool := fun Q =>
          (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ D7);
        have isQuad : Finset (Fin 13) → Prop := fun Q => Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | p - l ∈ D7}.card ≤ 2;
        PEqualNP.TopForm.IsAO2 26 D →
        (∀ p l : Fin 13, p - l ∈ D7 → (p ≠ p0 ∨ l ≠ 0) → D.eval (x8 p l) = true) →
        (∀ Q : Finset (Fin 13), isQuad Q → D.eval (x9 Q) = false) →
        (∃ p l : Fin 13, p - l ∈ D7 ∧ (p ≠ p0 ∨ l ≠ 0) ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 26 p.val a ∧
            PEqualNP.ReadTwo.orp D 26 (13 + l.val) b) →
        (∃ j g, D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ v : Fin 26, (D.wires (List.ofFn fun i : Fin 26 => decide (i = v))).getD (26 + j) false = true) →
        63 ≤ D.size)
    (hDirtyNoOneHot :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (p0 : Fin 13),
        have D7 : Finset (Fin 13) := {0, 1, 3, 9};
        have x8 : Fin 13 → Fin 13 → List Bool := fun p l =>
          (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l);
        have x9 : Finset (Fin 13) → List Bool := fun Q =>
          (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ D7);
        have isQuad : Finset (Fin 13) → Prop := fun Q => Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | p - l ∈ D7}.card ≤ 2;
        PEqualNP.TopForm.IsAO2 26 D →
        (∀ p l : Fin 13, p - l ∈ D7 → (p ≠ p0 ∨ l ≠ 0) → D.eval (x8 p l) = true) →
        (∀ Q : Finset (Fin 13), isQuad Q → D.eval (x9 Q) = false) →
        (∃ p l : Fin 13, p - l ∈ D7 ∧ (p ≠ p0 ∨ l ≠ 0) ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 26 p.val a ∧
            PEqualNP.ReadTwo.orp D 26 (13 + l.val) b) →
        (∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ v : Fin 26, (D.wires (List.ofFn fun i : Fin 26 => decide (i = v))).getD (26 + j) false = false) →
        (∃ j g, D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ Q : Finset (Fin 13), isQuad Q ∧ (D.wires (x9 Q)).getD (26 + j) false = true) →
        63 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro origC x2 x3 x4 hMono _hRB27 D7 x8 x9 isQuad hTrueOrig hFalseOrig
  let I : Fin 13 → Fin 13 → Prop := fun p l => p - l ∈ D7
  have hsub_shift : ∀ p l s : Fin 13, (p + s) - l = p - (l - s) := by decide
  have hadd_sub_shift : ∀ p l s : Fin 13, (p + s) - (l + s) = p - l := by decide
  have hsub_add_cancel : ∀ p s : Fin 13, (p - s) + s = p := by decide
  have hadd_sub_cancel : ∀ p s : Fin 13, (p + s) - s = p := by decide
  have hadd_inj (s : Fin 13) : Function.Injective (fun p : Fin 13 => p + s) := fun a b h => by
    have h1 := congrArg (· - s) h
    rw [hadd_sub_cancel a s, hadd_sub_cancel b s] at h1
    exact h1
  have hNoC4 : ∀ p1 p2 l1 l2 : Fin 13, p1 ≠ p2 → l1 ≠ l2 → ¬ (I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
    dsimp only [I, D7]; decide
  have hdegP : ∀ p : Fin 13, (Finset.univ.filter (fun l : Fin 13 => p - l ∈ D7)).card = 4 := by
    dsimp only [D7]; decide
  have hdegL : ∀ l : Fin 13, (Finset.univ.filter (fun p : Fin 13 => p - l ∈ D7)).card = 4 := by
    dsimp only [D7]; decide
  have hIcard : (Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ D7)).card = 52 := by
    dsimp only [D7]; decide
  have hQuadShift (Q : Finset (Fin 13)) (s : Fin 13) (hQ : isQuad Q) : isQuad (Q.image (· + s)) := by
    refine ⟨by rw [Finset.card_image_of_injective Q (hadd_inj s)]; exact hQ.1, ?_⟩
    intro l
    have hfilt : {p ∈ Q.image (· + s) | p - l ∈ D7} = {q ∈ Q | q - (l - s) ∈ D7}.image (· + s) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hmem⟩
        rw [hsub_shift q l s] at hmem
        exact ⟨q, ⟨hq, hmem⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hmem⟩, rfl⟩
        refine ⟨⟨q, hq, rfl⟩, ?_⟩
        rw [hsub_shift q l s]; exact hmem
    rw [hfilt, Finset.card_image_of_injective _ (hadd_inj s)]
    exact hQ.2 (l - s)
  let tbl2pts : List (Finset (Fin 13)) :=
    [{0, 1, 2, 5}, {0, 1, 2, 5}, {0, 1, 2, 5}, {0, 2, 3, 4}, {0, 1, 4, 6}, {0, 1, 2, 5},
     {0, 1, 2, 6}, {0, 1, 2, 7}, {0, 1, 4, 8}, {0, 2, 4, 9}, {0, 1, 5, 10}, {0, 1, 2, 11}, {0, 1, 4, 12}]
  have htbl2pts_ok : ∀ d : Fin 13, isQuad (tbl2pts.getD d.val ∅) ∧ (0 : Fin 13) ∈ tbl2pts.getD d.val ∅ ∧ d ∈ tbl2pts.getD d.val ∅ := by
    dsimp only [isQuad, D7, tbl2pts]; decide
  have hQuad_2pts (p1 p2 : Fin 13) : ∃ Q : Finset (Fin 13), isQuad Q ∧ p1 ∈ Q ∧ p2 ∈ Q := by
    obtain ⟨hQ, h0, hd⟩ := htbl2pts_ok (p2 - p1)
    refine ⟨(tbl2pts.getD (p2 - p1).val ∅).image (· + p1), hQuadShift _ p1 hQ, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨0, h0, zero_add p1⟩
    · exact Finset.mem_image.mpr ⟨p2 - p1, hd, hsub_add_cancel p2 p1⟩
  let tbl2lns : List (Finset (Fin 13)) :=
    [{2, 4, 5, 6}, {5, 6, 7, 11}, {4, 6, 7, 8}, {2, 5, 7, 8}, {2, 6, 8, 10}, {2, 4, 7, 11},
     {4, 5, 8, 10}, {2, 4, 5, 6}, {2, 5, 6, 10}, {2, 4, 6, 8}, {2, 4, 5, 8}, {2, 4, 5, 6}, {4, 5, 6, 10}]
  have htbl2lns_ok : ∀ d : Fin 13, isQuad (tbl2lns.getD d.val ∅) ∧
      (∀ q ∈ tbl2lns.getD d.val ∅, q - (0 : Fin 13) ∉ D7) ∧
      (∀ q ∈ tbl2lns.getD d.val ∅, q - d ∉ D7) := by
    dsimp only [isQuad, D7, tbl2lns]; decide
  have hQuad_2lns (l1 l2 : Fin 13) : ∃ Q : Finset (Fin 13), isQuad Q ∧
      (∀ p ∈ Q, p - l1 ∉ D7) ∧ (∀ p ∈ Q, p - l2 ∉ D7) := by
    obtain ⟨hQ, h0, hd⟩ := htbl2lns_ok (l2 - l1)
    refine ⟨(tbl2lns.getD (l2 - l1).val ∅).image (· + l1), hQuadShift _ l1 hQ, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have heq : (q + l1) - l1 = q - 0 := by rw [hadd_sub_cancel q l1]; exact (sub_zero q).symm
      rw [heq]; exact h0 q hq
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      rw [hsub_shift q l2 l1]; exact hd q hq
  let tblNon : List (Finset (Fin 13)) :=
    [{0, 1, 2, 5}, {0, 1, 2, 5}, {2, 4, 5, 6}, {0, 1, 2, 5}, {2, 4, 5, 6}, {2, 4, 5, 6},
     {2, 4, 5, 6}, {2, 4, 7, 8}, {2, 4, 5, 8}, {0, 1, 2, 5}, {2, 5, 6, 10}, {2, 4, 6, 11}, {2, 4, 5, 12}]
  have htblNon_ok : ∀ d : Fin 13, d ∉ D7 →
      isQuad (tblNon.getD d.val ∅) ∧ d ∈ tblNon.getD d.val ∅ ∧ ∀ q ∈ tblNon.getD d.val ∅, q ∉ D7 := by
    dsimp only [isQuad, D7, tblNon]; decide
  have hQuad_noninc (p l : Fin 13) (hni : p - l ∉ D7) : ∃ Q : Finset (Fin 13), isQuad Q ∧
      p ∈ Q ∧ ∀ q ∈ Q, q - l ∉ D7 := by
    obtain ⟨hQ, hd, hno⟩ := htblNon_ok (p - l) hni
    refine ⟨(tblNon.getD (p - l).val ∅).image (· + l), hQuadShift _ l hQ, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨p - l, hd, hsub_add_cancel p l⟩
    · intro q hq
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
      rw [hadd_sub_cancel q0 l]; exact hno q0 hq0
  have hQ0_quad : isQuad ({0, 1, 2, 5} : Finset (Fin 13)) := by dsimp only [isQuad, D7]; decide
  let concat26 : (Fin 13 → Bool) → (Fin 13 → Bool) → (Fin 26 → Bool) := fun f1 f2 i =>
    if h : i.val < 13 then f1 ⟨i.val, h⟩ else f2 ⟨i.val - 13, by omega⟩
  have hconcat_eq (f1 f2 : Fin 13 → Bool) :
      List.ofFn f1 ++ List.ofFn f2 = List.ofFn (concat26 f1 f2) := by
    apply List.ext_getElem
    · simp only [List.length_append, List.length_ofFn]
    · intro k hk1 hk2
      simp only [List.length_ofFn] at hk2
      rw [List.getElem_ofFn]
      dsimp only [concat26]
      by_cases hk : k < 13
      · rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hk), List.getElem_ofFn]
        simp only [hk, ↓reduceDIte]
      · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
        simp only [hk, ↓reduceDIte, List.length_ofFn]
  have hconcat_cast (f1 f2 : Fin 13 → Bool) (p : Fin 13) :
      concat26 f1 f2 (Fin.castAdd 13 p) = f1 p := by
    dsimp only [concat26]; simp only [Fin.val_castAdd, p.isLt, ↓reduceDIte]
  have hconcat_nat (f1 f2 : Fin 13 → Bool) (l : Fin 13) :
      concat26 f1 f2 (Fin.natAdd 13 l) = f2 l := by
    dsimp only [concat26]
    have hge : ¬ (13 + l.val < 13) := by omega
    simp only [Fin.val_natAdd, hge, ↓reduceDIte, Nat.add_sub_cancel_left]
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
      run (gs1 ++ gs2) ws = run gs2 (run gs1 ws) := List.foldl_append
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
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < 26 + j) ∧
    (∀ g ∈ gs, g.inputs.length = 2)
  have hNormMono : ∀ k ≤ origC.gates.length, ∃ gs : List Gate,
      gs.length ≤ k ∧ AO2List gs ∧
      ∀ i < 27 + k,
        (∃ c : Bool, ∀ x : Fin 26 → Bool, (run origC.gates (List.ofFn x ++ [x4])).getD i false = c) ∨
        (∃ w < 26 + gs.length, ∀ x : Fin 26 → Bool,
          (run origC.gates (List.ofFn x ++ [x4])).getD i false = (run gs (List.ofFn x)).getD w false) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Nat.le_refl 0,
        ⟨(fun g hg => by cases hg), (fun j hj => by simp only [List.length_nil] at hj; omega), (fun g hg => by cases hg)⟩, ?_⟩
      intro i hi
      by_cases hi26 : i < 26
      · refine Or.inr ⟨i, by simp only [List.length_nil]; omega, fun x => ?_⟩
        rw [run_keep origC.gates (List.ofFn x ++ [x4]) i (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
        exact List.getD_append (List.ofFn x) [x4] false i (by simp only [List.length_ofFn]; exact hi26)
      · have hi_eq : i = 26 := by omega
        subst hi_eq
        refine Or.inl ⟨x4, fun x => ?_⟩
        rw [run_keep origC.gates (List.ofFn x ++ [x4]) 26 (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
        have h26 : (List.ofFn x).length = 26 := List.length_ofFn
        simpa only [h26] using getD_snoc_eq (List.ofFn x) x4
    | succ k ih =>
      intro hk1
      obtain ⟨gs, hgs_len, hgs_AO, hmap⟩ := ih (by omega)
      let g : Gate := origC.gates[k]'(by omega)
      have hg_mem : g ∈ origC.gates := List.getElem_mem (by omega)
      have hgM := hMono g hg_mem
      have hlen27 (x : Fin 26 → Bool) : (List.ofFn x ++ [x4]).length = 27 := by
        simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hwire_k (x : Fin 26 → Bool) :
          (run origC.gates (List.ofFn x ++ [x4])).getD (27 + k) false =
            g.op.eval (g.inputs.map fun i => (run (origC.gates.take k) (List.ofFn x ++ [x4])).getD i false) := by
        have hsp : origC.gates = origC.gates.take k ++ [g] ++ origC.gates.drop (k + 1) := by
          have h2 : origC.gates.drop k = g :: origC.gates.drop (k + 1) := List.drop_eq_getElem_cons (by omega)
          calc origC.gates = origC.gates.take k ++ origC.gates.drop k := (List.take_append_drop k origC.gates).symm
            _ = origC.gates.take k ++ (g :: origC.gates.drop (k + 1)) := by rw [h2]
            _ = origC.gates.take k ++ [g] ++ origC.gates.drop (k + 1) := by rw [List.append_assoc, List.singleton_append]
        conv_lhs => rw [hsp, run_append, run_append]
        have hlen1 : (run (origC.gates.take k) (List.ofFn x ++ [x4])).length = 27 + k := by
          rw [run_len, hlen27 x, List.length_take]; omega
        have hlt2 : 27 + k < (run [g] (run (origC.gates.take k) (List.ofFn x ++ [x4]))).length := by
          rw [run_len, hlen1, List.length_cons, List.length_nil]; omega
        rw [run_keep (origC.gates.drop (k + 1)) _ (27 + k) hlt2]
        change (step (run (origC.gates.take k) (List.ofFn x ++ [x4])) g).getD (27 + k) false = _
        dsimp only [step]
        rw [← hlen1, getD_snoc_eq (run (origC.gates.take k) (List.ofFn x ++ [x4])) _]
      have hMapIn (i : ℕ) :
          (∃ c : Bool, ∀ x : Fin 26 → Bool, (run (origC.gates.take k) (List.ofFn x ++ [x4])).getD i false = c) ∨
          (∃ w < 26 + gs.length, ∀ x : Fin 26 → Bool,
            (run (origC.gates.take k) (List.ofFn x ++ [x4])).getD i false = (run gs (List.ofFn x)).getD w false) := by
        by_cases hi : i < 27 + k
        · have hpre (x : Fin 26 → Bool) :
              (run (origC.gates.take k) (List.ofFn x ++ [x4])).getD i false =
                (run origC.gates (List.ofFn x ++ [x4])).getD i false := by
            have hsp : origC.gates = origC.gates.take k ++ origC.gates.drop k := (List.take_append_drop k origC.gates).symm
            conv_rhs => rw [hsp, run_append]
            exact (run_keep (origC.gates.drop k) (run (origC.gates.take k) (List.ofFn x ++ [x4])) i
              (by rw [run_len, hlen27 x, List.length_take]; omega)).symm
          rcases hmap i hi with ⟨c, hc⟩ | ⟨w, hw, hww⟩
          · exact Or.inl ⟨c, fun x => (hpre x).trans (hc x)⟩
          · exact Or.inr ⟨w, hw, fun x => (hpre x).trans (hww x)⟩
        · refine Or.inl ⟨false, fun x => ?_⟩
          exact List.getD_eq_default _ false (n := i) (by rw [run_len, hlen27 x, List.length_take]; omega)
      have hStepNo (hnew :
          (∃ c : Bool, ∀ x : Fin 26 → Bool, (run origC.gates (List.ofFn x ++ [x4])).getD (27 + k) false = c) ∨
          (∃ w < 26 + gs.length, ∀ x : Fin 26 → Bool,
            (run origC.gates (List.ofFn x ++ [x4])).getD (27 + k) false = (run gs (List.ofFn x)).getD w false)) :
          ∃ gs' : List Gate, gs'.length ≤ k + 1 ∧ AO2List gs' ∧
            ∀ i < 27 + (k + 1),
              (∃ c : Bool, ∀ x : Fin 26 → Bool, (run origC.gates (List.ofFn x ++ [x4])).getD i false = c) ∨
              (∃ w < 26 + gs'.length, ∀ x : Fin 26 → Bool,
                (run origC.gates (List.ofFn x ++ [x4])).getD i false = (run gs' (List.ofFn x)).getD w false) := by
        refine ⟨gs, by omega, hgs_AO, fun i hi => ?_⟩
        by_cases heq : i = 27 + k
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
          have hev1 (x : Fin 26 → Bool) :
              (run origC.gates (List.ofFn x ++ [x4])).getD (27 + k) false =
                (run (origC.gates.take k) (List.ofFn x ++ [x4])).getD i1 false := by
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
                  by_cases heq : i = 27 + k
                  · subst heq
                    refine Or.inr ⟨26 + gs.length, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
                    rw [hwire_k x, hin, List.map_cons, List.map_cons, List.map_nil, hww1 x, hww2 x, run_snoc]
                    have hlen_run : (run gs (List.ofFn x)).length = 26 + gs.length := by rw [run_len, List.length_ofFn]
                    dsimp only [step, gNew]
                    rw [← hlen_run, getD_snoc_eq (run gs (List.ofFn x)) _]
                    rfl
                  · rcases hmap i (by omega) with ⟨c, hc⟩ | ⟨w, hw, hww⟩
                    · exact Or.inl ⟨c, hc⟩
                    · refine Or.inr ⟨w, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
                      rw [hww x, run_snoc]
                      have hlen_run : (run gs (List.ofFn x)).length = 26 + gs.length := by rw [run_len, List.length_ofFn]
                      exact (getD_snoc_ne (run gs (List.ofFn x)) _ w (by omega)).symm
          | cons _ _ =>
            rw [hin] at hlen2
            simp only [List.length_cons] at hlen2
            omega
  obtain ⟨gs0, hgs0_len, hgs0_AO, hmap0⟩ := hNormMono origC.gates.length (Nat.le_refl _)
  have hOrig_hasTrue : ∃ x : Fin 26 → Bool, origC.eval (List.ofFn x ++ [x4]) = true := by
    have hne : x2 + 1 ≠ x2 := by
      intro h; have := hadd_sub_cancel x2 1; rw [h] at this
      have h01 : (x2 - x2) = (0 : Fin 13) := sub_self x2
      have h10 : ∀ a : Fin 13, a + 1 ≠ a := by decide
      exact h10 x2 h
    have h0in : (x2 + 1) - (x2 + 1) ∈ D7 := by rw [sub_self]; dsimp only [D7]; decide
    have ht := hTrueOrig (x2 + 1) (x2 + 1) h0in (Or.inl hne)
    refine ⟨concat26 (fun i => decide (i = x2 + 1)) (fun i => decide (i = x2 + 1)), ?_⟩
    rw [← hconcat_eq (fun i : Fin 13 => decide (i = x2 + 1)) (fun i : Fin 13 => decide (i = x2 + 1))]
    exact ht
  have hOrig_hasFalse : ∃ x : Fin 26 → Bool, origC.eval (List.ofFn x ++ [x4]) = false := by
    have hf := hFalseOrig {0, 1, 2, 5} hQ0_quad
    refine ⟨concat26 (fun i => decide (i ∈ ({0, 1, 2, 5} : Finset (Fin 13))))
      (fun i => decide (∀ p ∈ ({0, 1, 2, 5} : Finset (Fin 13)), p - i ∉ D7)), ?_⟩
    rw [← hconcat_eq (fun i : Fin 13 => decide (i ∈ ({0, 1, 2, 5} : Finset (Fin 13))))
      (fun i : Fin 13 => decide (∀ p ∈ ({0, 1, 2, 5} : Finset (Fin 13)), p - i ∉ D7))]
    exact hf
  have hOrig_out_lt : origC.output < 27 + origC.gates.length := by
    by_contra hge
    obtain ⟨xT, hxT⟩ := hOrig_hasTrue
    have h0 : origC.eval (List.ofFn xT ++ [x4]) = false := by
      change (run origC.gates (List.ofFn xT ++ [x4])).getD origC.output false = false
      exact List.getD_eq_default _ false (n := origC.output)
        (by rw [run_len, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)
    rw [h0] at hxT; cases hxT
  have hD0_ex : ∃ D0 : Circuit, IsAO2 26 D0 ∧ D0.size ≤ origC.size ∧
      ∀ x : Fin 26 → Bool, D0.eval (List.ofFn x) = origC.eval (List.ofFn x ++ [x4]) := by
    rcases hmap0 origC.output hOrig_out_lt with ⟨c, hc⟩ | ⟨w, _, hww⟩
    · exfalso
      cases c
      · obtain ⟨xT, hxT⟩ := hOrig_hasTrue
        have h0 : origC.eval (List.ofFn xT ++ [x4]) = false := hc xT
        rw [h0] at hxT; cases hxT
      · obtain ⟨xF, hxF⟩ := hOrig_hasFalse
        have h1 : origC.eval (List.ofFn xF ++ [x4]) = true := hc xF
        rw [h1] at hxF; cases hxF
    · refine ⟨⟨gs0, w⟩, hgs0_AO, hgs0_len, fun x => (hww x).symm⟩
  obtain ⟨D0, hD0_AO, hD0_sz, hD0_eq⟩ := hD0_ex
  let sh : ℕ → ℕ := fun i =>
    if h1 : i < 13 then ((⟨i, h1⟩ : Fin 13) - x3).val
    else if h2 : i < 26 then 13 + ((⟨i - 13, by omega⟩ : Fin 13) - x3).val
    else i
  have hsh_lt26 (i : ℕ) (hi : i < 26) : sh i < 26 := by
    dsimp only [sh]
    by_cases h1 : i < 13
    · simp only [h1, ↓reduceDIte]; have := ((⟨i, h1⟩ : Fin 13) - x3).isLt; omega
    · simp only [h1, hi, ↓reduceDIte]; have := ((⟨i - 13, by omega⟩ : Fin 13) - x3).isLt; omega
  have hsh_ge26 (i : ℕ) (hi : 26 ≤ i) : sh i = i := by
    dsimp only [sh]
    have h1 : ¬ i < 13 := by omega
    have h2 : ¬ i < 26 := by omega
    simp only [h1, h2, ↓reduceDIte]
  let D : Circuit := ⟨D0.gates.map (fun g => Gate.mk g.op (g.inputs.map sh)), sh D0.output⟩
  have hD_sz : D.size ≤ origC.size := by
    change (D0.gates.map _).length ≤ origC.size
    rw [List.length_map]; exact hD0_sz
  suffices hgoal : 63 ≤ D.size by exact Nat.le_trans hgoal hD_sz
  have hD_AO : IsAO2 26 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact hD0_AO.1 g0 hg0
    · intro j hj u hu
      change j < (D0.gates.map _).length at hj
      rw [List.length_map] at hj
      have hget : D.gates.getD j ⟨GateOp.or, []⟩ =
          Gate.mk (D0.gates.getD j ⟨GateOp.or, []⟩).op ((D0.gates.getD j ⟨GateOp.or, []⟩).inputs.map sh) := by
        dsimp only [D]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
            List.getD_eq_getElem _ _ hj]
      change u ∈ (D.gates.getD j ⟨GateOp.or, []⟩).inputs at hu
      rw [hget] at hu; simp only [List.mem_map] at hu
      obtain ⟨i, hi, rfl⟩ := hu
      have hilt : i < 26 + j := hD0_AO.2.1 j hj i hi
      by_cases hi26 : i < 26
      · have := hsh_lt26 i hi26; omega
      · rw [hsh_ge26 i (by omega)]; exact hilt
    · intro g hg
      simp only [D, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [List.length_map]; exact hD0_AO.2.2 g0 hg0
  have remap_sh (gs : List Gate) (wA wB : List Bool)
      (hlen_w : wA.length = wB.length) (h26 : 26 ≤ wA.length)
      (hrel : ∀ i, wB.getD (sh i) false = wA.getD i false) :
      ∀ i, (run (gs.map fun g => Gate.mk g.op (g.inputs.map sh)) wB).getD (sh i) false =
        (run gs wA).getD i false := by
    induction gs generalizing wA wB with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hinp : (g.inputs.map sh).map (fun i => wB.getD i false) =
          g.inputs.map (fun i => wA.getD i false) := by
        rw [List.map_map]; apply List.map_congr_left
        intro i _; exact hrel i
      let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
      have hstepB : step wB (Gate.mk g.op (g.inputs.map sh)) = wB ++ [b] := by
        dsimp only [step, b]; rw [hinp]
      rw [hstepB]
      apply ih (step wA g) (wB ++ [b])
      · simp only [step, List.length_append, hlen_w, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        dsimp only [step]
        by_cases hi : i = wA.length
        · subst hi
          have hfi : sh wA.length = wB.length := by rw [hsh_ge26 wA.length h26, hlen_w]
          rw [hfi, getD_snoc_eq wB b, getD_snoc_eq wA b]
        · have hfi : sh i ≠ wB.length := by
            intro hfeq
            by_cases hlt : i < 26
            · have := hsh_lt26 i hlt; omega
            · have := hsh_ge26 i (by omega); omega
          rw [getD_snoc_ne wB b (sh i) hfi, getD_snoc_ne wA b i hi]
          exact hrel i
  have hD_eval_shift (f1 f2 : Fin 13 → Bool) :
      D.eval (List.ofFn f1 ++ List.ofFn f2) =
        D0.eval (List.ofFn (fun p => f1 (p - x3)) ++ List.ofFn (fun l => f2 (l - x3))) := by
    rw [hconcat_eq f1 f2, hconcat_eq (fun p => f1 (p - x3)) (fun l => f2 (l - x3))]
    let wB := List.ofFn (concat26 f1 f2)
    let wA := List.ofFn (concat26 (fun p => f1 (p - x3)) (fun l => f2 (l - x3)))
    have hrel0 : ∀ i, wB.getD (sh i) false = wA.getD i false := by
      intro i
      by_cases hi13 : i < 13
      · have hshi : sh i = ((⟨i, hi13⟩ : Fin 13) - x3).val := by
          dsimp only [sh]; simp only [hi13, ↓reduceDIte]
        have hltB : sh i < wB.length := by rw [hshi]; simp only [wB, List.length_ofFn]; have := ((⟨i, hi13⟩ : Fin 13) - x3).isLt; omega
        have hltA : i < wA.length := by simp only [wA, List.length_ofFn]; omega
        rw [List.getD_eq_getElem wB false hltB, List.getD_eq_getElem wA false hltA]
        dsimp only [wB, wA]
        rw [List.getElem_ofFn, List.getElem_ofFn]
        dsimp only [concat26]
        have hlt13 : sh i < 13 := by rw [hshi]; exact ((⟨i, hi13⟩ : Fin 13) - x3).isLt
        simp only [hlt13, hi13, ↓reduceDIte]
        congr 1; exact Fin.ext hshi
      · by_cases hi26 : i < 26
        · have hshi : sh i = 13 + ((⟨i - 13, by omega⟩ : Fin 13) - x3).val := by
            dsimp only [sh]; simp only [hi13, hi26, ↓reduceDIte]
          have hltB : sh i < wB.length := by rw [hshi]; simp only [wB, List.length_ofFn]; have := ((⟨i - 13, by omega⟩ : Fin 13) - x3).isLt; omega
          have hltA : i < wA.length := by simp only [wA, List.length_ofFn]; omega
          rw [List.getD_eq_getElem wB false hltB, List.getD_eq_getElem wA false hltA]
          dsimp only [wB, wA]
          rw [List.getElem_ofFn, List.getElem_ofFn]
          dsimp only [concat26]
          have hge13 : ¬ sh i < 13 := by rw [hshi]; omega
          simp only [hge13, hi13, ↓reduceDIte]
          congr 1; apply Fin.ext; dsimp only; rw [hshi]; omega
        · rw [hsh_ge26 i (by omega),
              List.getD_eq_default wB false (n := i) (by simp only [wB, List.length_ofFn]; omega),
              List.getD_eq_default wA false (n := i) (by simp only [wA, List.length_ofFn]; omega)]
    exact remap_sh D0.gates wA wB (by simp only [wA, wB, List.length_ofFn]) (by simp only [wA, List.length_ofFn]; exact Nat.le_refl _) hrel0 D0.output
  let p0 : Fin 13 := x2 - x3
  have hD_true : ∀ p l : Fin 13, p - l ∈ D7 → (p ≠ p0 ∨ l ≠ 0) → D.eval (x8 p l) = true := by
    intro p l hpl hne
    dsimp only [x8]
    rw [hD_eval_shift (fun i => decide (i = p)) (fun i => decide (i = l))]
    have hf1 : (fun i : Fin 13 => decide (i - x3 = p)) = (fun i : Fin 13 => decide (i = p + x3)) := by
      funext i; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
      constructor
      · intro h; rw [← h, hsub_add_cancel i x3]
      · intro h; rw [h, hadd_sub_cancel p x3]
    have hf2 : (fun i : Fin 13 => decide (i - x3 = l)) = (fun i : Fin 13 => decide (i = l + x3)) := by
      funext i; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
      constructor
      · intro h; rw [← h, hsub_add_cancel i x3]
      · intro h; rw [h, hadd_sub_cancel l x3]
    rw [hf1, hf2, hconcat_eq, hD0_eq, ← hconcat_eq (fun i : Fin 13 => decide (i = p + x3)) (fun i : Fin 13 => decide (i = l + x3))]
    have hpl' : (p + x3) - (l + x3) ∈ D7 := by rw [hadd_sub_shift p l x3]; exact hpl
    have hne' : p + x3 ≠ x2 ∨ l + x3 ≠ x3 := by
      rcases hne with hp | hl
      · exact Or.inl (fun h => hp (by dsimp only [p0]; rw [← h, hadd_sub_cancel p x3]))
      · exact Or.inr (fun h => hl (by have h1 := congrArg (· - x3) h; rw [hadd_sub_cancel l x3, sub_self] at h1; exact h1))
    exact hTrueOrig (p + x3) (l + x3) hpl' hne'
  have hD_false : ∀ Q : Finset (Fin 13), isQuad Q → D.eval (x9 Q) = false := by
    intro Q hQ
    dsimp only [x9]
    rw [hD_eval_shift (fun i => decide (i ∈ Q)) (fun i => decide (∀ q ∈ Q, q - i ∉ D7))]
    let Q' : Finset (Fin 13) := Q.image (· + x3)
    have hf1 : (fun i : Fin 13 => decide (i - x3 ∈ Q)) = (fun i : Fin 13 => decide (i ∈ Q')) := by
      funext i; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Q', Finset.mem_image]
      constructor
      · intro h; exact ⟨i - x3, h, hsub_add_cancel i x3⟩
      · rintro ⟨q, hq, rfl⟩; rw [hadd_sub_cancel q x3]; exact hq
    have hf2 : (fun i : Fin 13 => decide (∀ q ∈ Q, q - (i - x3) ∉ D7)) =
        (fun i : Fin 13 => decide (∀ q ∈ Q', q - i ∉ D7)) := by
      funext i; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Q', Finset.mem_image]
      constructor
      · intro h q hq; obtain ⟨q0, hq0, rfl⟩ := hq; rw [hsub_shift q0 i x3]; exact h q0 hq0
      · intro h q0 hq0; rw [← hsub_shift q0 i x3]; exact h (q0 + x3) ⟨q0, hq0, rfl⟩
    rw [hf1, hf2, hconcat_eq, hD0_eq, ← hconcat_eq (fun i : Fin 13 => decide (i ∈ Q')) (fun i : Fin 13 => decide (∀ q ∈ Q', q - i ∉ D7))]
    exact hFalseOrig Q' (hQuadShift Q x3 hQ)
  have hMonoD (wA wB : List Bool) (hlen : wA.length = wB.length)
      (hle : ∀ i, wA.getD i false = true → wB.getD i false = true) :
      D.eval wA = true → D.eval wB = true := by
    have hrun (gs : List Gate) (hgm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
        (vA vB : List Bool) (hl : vA.length = vB.length)
        (h : ∀ i, vA.getD i false = true → vB.getD i false = true) :
        ∀ i, (run gs vA).getD i false = true → (run gs vB).getD i false = true := by
      induction gs generalizing vA vB with
      | nil => exact h
      | cons g rest ih =>
        simp only [run, List.foldl_cons] at ih ⊢
        apply ih (fun g' hg' => hgm g' (List.mem_cons_of_mem g hg')) (step vA g) (step vB g)
        · simp only [step, List.length_append, hl, List.length_cons, List.length_nil]
        · intro i hi
          dsimp only [step] at hi ⊢
          by_cases heq : i = vA.length
          · subst heq
            rw [getD_snoc_eq vA _] at hi
            rw [hl, getD_snoc_eq vB _]
            rcases hgm g List.mem_cons_self with hop | hop
            · rw [hop] at hi ⊢
              change (g.inputs.map fun u => vA.getD u false).all id = true at hi
              change (g.inputs.map fun u => vB.getD u false).all id = true
              rw [List.all_eq_true] at hi ⊢
              intro b hb; simp only [List.mem_map] at hb
              obtain ⟨u, hu, rfl⟩ := hb
              exact h u (hi (vA.getD u false) (List.mem_map.mpr ⟨u, hu, rfl⟩))
            · rw [hop] at hi ⊢
              change (g.inputs.map fun u => vA.getD u false).any id = true at hi
              change (g.inputs.map fun u => vB.getD u false).any id = true
              rw [List.any_eq_true] at hi ⊢
              obtain ⟨b, hb, hbt⟩ := hi
              simp only [List.mem_map] at hb
              obtain ⟨u, hu, rfl⟩ := hb
              exact ⟨vB.getD u false, List.mem_map.mpr ⟨u, hu, rfl⟩, h u hbt⟩
          · have heq2 : i ≠ vB.length := by rw [← hl]; exact heq
            rw [getD_snoc_ne vA _ i heq] at hi
            rw [getD_snoc_ne vB _ i heq2]
            exact h i hi
    exact hrun D.gates hD_AO.1 wA wB hlen hle D.output
  by_cases hall : ∀ p l : Fin 13, p - l ∈ D7 → (p ≠ p0 ∨ l ≠ 0) →
      ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
        PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
        PEqualNP.ReadTwo.orp D 26 p.val a ∧
        PEqualNP.ReadTwo.orp D 26 (13 + l.val) b
  · classical
    let E : Finset (Fin 13 × Fin 13) :=
      (Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ D7)).erase (p0, 0)
    have hmem_E (p l : Fin 13) : (p, l) ∈ E ↔ I p l ∧ (p ≠ p0 ∨ l ≠ 0) := by
      simp only [E, I, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Prod.mk.injEq]
      tauto
    have hEcard : 51 ≤ E.card := by
      have h1 : E.card ≥ (Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ D7)).card - 1 := by
        dsimp only [E]
        by_cases hmem : (p0, (0 : Fin 13)) ∈ Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ D7)
        · have := Finset.card_erase_add_one hmem; omega
        · rw [Finset.erase_eq_of_notMem hmem]; omega
      omega
    have hEempty : E ≠ ∅ := by
      intro hemp; rw [hemp, Finset.card_empty] at hEcard; omega
    have hRB : ReadsBack 26 D := hD_AO.2.1
    let wv : ℕ → (Fin 26 → Bool) → Bool := fun w x => (run D.gates (List.ofFn x)).getD w false
    have hD_false_le (x : Fin 26 → Bool) (Q : Finset (Fin 13)) (hQ : isQuad Q)
        (hle : (∀ p : Fin 13, x (Fin.castAdd 13 p) = true → p ∈ Q) ∧
               (∀ l : Fin 13, x (Fin.natAdd 13 l) = true → ∀ q ∈ Q, q - l ∉ D7)) :
        wv D.output x = false := by
      by_contra ht
      have hxt : D.eval (List.ofFn x) = true := Bool.eq_true_of_not_eq_false ht
      have hxQ_len : (List.ofFn x).length = (x9 Q).length := by
        simp only [x9, List.length_append, List.length_ofFn]
      have hxQ_le : ∀ i, (List.ofFn x).getD i false = true → (x9 Q).getD i false = true := by
        intro i hi
        by_cases hi26 : i < 26
        · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hi26), List.getElem_ofFn] at hi
          dsimp only [x9]
          rw [hconcat_eq, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hi26), List.getElem_ofFn]
          dsimp only [concat26]
          by_cases hi13 : i < 13
          · simp only [hi13, ↓reduceDIte, decide_eq_true_eq]
            exact hle.1 ⟨i, hi13⟩ hi
          · simp only [hi13, ↓reduceDIte, decide_eq_true_eq]
            have heq : (⟨i, hi26⟩ : Fin (13 + 13)) = Fin.natAdd 13 ⟨i - 13, by omega⟩ := Fin.ext (by simp only [Fin.val_natAdd]; omega)
            rw [heq] at hi
            exact hle.2 ⟨i - 13, by omega⟩ hi
        · rw [List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega)] at hi
          cases hi
      have hQt := hMonoD (List.ofFn x) (x9 Q) hxQ_len hxQ_le hxt
      rw [hD_false Q hQ] at hQt; cases hQt
    have hno_pts2 (p1 p2 : Fin 13) :
        wv D.output (fun i : Fin 26 => decide (i = Fin.castAdd 13 p1 ∨ i = Fin.castAdd 13 p2)) = false := by
      obtain ⟨Q, hQ, hp1, hp2⟩ := hQuad_2pts p1 p2
      apply hD_false_le _ Q hQ
      refine ⟨?_, ?_⟩
      · intro p hp
        simp only [decide_eq_true_eq] at hp
        rcases hp with h | h
        · have := congrArg Fin.val h; simp only [Fin.val_castAdd] at this
          rw [show p = p1 from Fin.ext this]; exact hp1
        · have := congrArg Fin.val h; simp only [Fin.val_castAdd] at this
          rw [show p = p2 from Fin.ext this]; exact hp2
      · intro l hl
        simp only [decide_eq_true_eq] at hl
        rcases hl with h | h <;> (have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega)
    have hno_lns2 (l1 l2 : Fin 13) :
        wv D.output (fun i : Fin 26 => decide (i = Fin.natAdd 13 l1 ∨ i = Fin.natAdd 13 l2)) = false := by
      obtain ⟨Q, hQ, hl1, hl2⟩ := hQuad_2lns l1 l2
      apply hD_false_le _ Q hQ
      refine ⟨?_, ?_⟩
      · intro p hp
        simp only [decide_eq_true_eq] at hp
        rcases hp with h | h <;> (have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega)
      · intro l hl
        simp only [decide_eq_true_eq] at hl
        rcases hl with h | h
        · have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this
          rw [show l = l1 from Fin.ext (by omega)]; exact hl1
        · have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this
          rw [show l = l2 from Fin.ext (by omega)]; exact hl2
    have hno_noninc (p l : Fin 13) (hni : ¬ I p l) :
        wv D.output (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = false := by
      obtain ⟨Q, hQ, hpQ, hlQ⟩ := hQuad_noninc p l hni
      apply hD_false_le _ Q hQ
      refine ⟨?_, ?_⟩
      · intro p' hp'
        simp only [decide_eq_true_eq] at hp'
        rcases hp' with h | h
        · have := congrArg Fin.val h; simp only [Fin.val_castAdd] at this
          rw [show p' = p from Fin.ext this]; exact hpQ
        · have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      · intro l' hl'
        simp only [decide_eq_true_eq] at hl'
        rcases hl' with h | h
        · have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
        · have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this
          rw [show l' = l from Fin.ext (by omega)]; exact hlQ
    let OrPath : ℕ → ℕ → Prop := fun w target =>
      ∀ Q : ℕ → Prop,
        Q target →
        (∀ k < D.gates.length, (gateAt D k).op = GateOp.or →
          ∀ a ∈ (gateAt D k).inputs, Q a → Q (26 + k)) →
        Q w
    have orPath_refl (t : ℕ) : OrPath t t := fun _ h _ => h
    have orPath_step {k a t : ℕ} (hk : k < D.gates.length) (hor : (gateAt D k).op = GateOp.or)
        (ha : a ∈ (gateAt D k).inputs) (hp : OrPath a t) : OrPath (26 + k) t :=
      fun Q ht hs => hs k hk hor a ha (hp Q ht hs)
    have orPath_trans {u v w : ℕ} (huv : OrPath u v) (hvw : OrPath v w) : OrPath u w :=
      fun Q hw hs => huv Q (hvw Q hw hs) hs
    have orPath_cases {w t : ℕ} (h : OrPath w t) :
        w = t ∨ ∃ k < D.gates.length, w = 26 + k ∧ (gateAt D k).op = GateOp.or ∧
          ∃ a ∈ (gateAt D k).inputs, OrPath a t := by
      apply h (fun x => x = t ∨ ∃ k < D.gates.length, x = 26 + k ∧ (gateAt D k).op = GateOp.or ∧
          ∃ a ∈ (gateAt D k).inputs, OrPath a t)
      · exact Or.inl rfl
      · intro k hk hor a ha hPa
        refine Or.inr ⟨k, hk, rfl, hor, a, ha, ?_⟩
        rcases hPa with rfl | ⟨k', hk', rfl, hor', a', ha', hp'⟩
        · exact orPath_refl _
        · exact orPath_step hk' hor' ha' hp'
    have orPath_parent {w t : ℕ} (h : OrPath w t) (hne : w ≠ t) :
        ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
          OrPath w (26 + y) ∧ t ∈ (gateAt D y).inputs := by
      have hdisj : w = t ∨ ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
          OrPath w (26 + y) ∧ t ∈ (gateAt D y).inputs := by
        apply h (fun x => x = t ∨ ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
            OrPath x (26 + y) ∧ t ∈ (gateAt D y).inputs)
        · exact Or.inl rfl
        · intro k hk hor a ha hPa
          rcases hPa with rfl | ⟨y, hy, hory, hpy, hty⟩
          · exact Or.inr ⟨k, hk, hor, orPath_refl (26 + k), ha⟩
          · exact Or.inr ⟨y, hy, hory, orPath_step hk hor ha hpy, hty⟩
      rcases hdisj with heq | hex
      · exact (hne heq).elim
      · exact hex
    have orp_to_orPath {t w : ℕ} (h : PEqualNP.ReadTwo.orp D 26 t w) : OrPath w t := by
      change Relation.ReflTransGen (fun a b => a < b ∧ ∃ j, b = 26 + j ∧ isOr D j ∧ a ∈ (gateAt D j).inputs) t w at h
      induction h with
      | refl => exact orPath_refl t
      | tail _ hstep ih =>
        obtain ⟨_, j, rfl, ⟨hj, hor⟩, ha⟩ := hstep
        exact orPath_step hj hor ha ih
    have wv_input (i : Fin 26) (x : Fin 26 → Bool) : wv i.val x = x i := by
      dsimp only [wv]
      rw [run_keep D.gates (List.ofFn x) i.val (by simp only [List.length_ofFn]; exact i.isLt),
          List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
    have wv_gate (k : ℕ) (hk : k < D.gates.length) (x : Fin 26 → Bool) :
        wv (26 + k) x = (gateAt D k).op.eval ((gateAt D k).inputs.map fun i => wv i x) := by
      dsimp only [wv]
      have hsplit : D.gates = D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1) := by
        have h1 : D.gates = D.gates.take (k + 1) ++ D.gates.drop (k + 1) :=
          (List.take_append_drop (k + 1) D.gates).symm
        conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem D.gates ⟨GateOp.or, []⟩ hk]
        rfl
      let w0 := run (D.gates.take k) (List.ofFn x)
      have hw0_len : w0.length = 26 + k := by
        dsimp only [w0]; rw [run_len, List.length_ofFn, List.length_take]; omega
      have hw_lt : ∀ i < 26 + k, (run D.gates (List.ofFn x)).getD i false = w0.getD i false := by
        intro i hi
        conv_lhs => rw [← List.take_append_drop k D.gates, run_append]
        exact run_keep (D.gates.drop k) w0 i (by omega)
      conv_lhs => rw [hsplit, run_append, run_append]
      have hstep_len : (run [gateAt D k] w0).length = 26 + k + 1 := by
        rw [run_len, hw0_len, List.length_cons, List.length_nil]
      rw [run_keep (D.gates.drop (k + 1)) _ (26 + k) (by change 26 + k < (run [gateAt D k] w0).length; omega)]
      change (step w0 (gateAt D k)).getD (26 + k) false = _
      dsimp only [step]
      rw [← hw0_len, getD_snoc_eq w0 _]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (hw_lt i (hRB k hk i hi)).symm
    have wv_or_mem {k a : ℕ} (hk : k < D.gates.length) (hor : (gateAt D k).op = GateOp.or)
        (ha : a ∈ (gateAt D k).inputs) (x : Fin 26 → Bool) (hva : wv a x = true) :
        wv (26 + k) x = true := by
      rw [wv_gate k hk x, hor]
      change ((gateAt D k).inputs.map fun i => wv i x).any id = true
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩
    have wv_and_pair {k a b : ℕ} (hk : k < D.gates.length) (hand : (gateAt D k).op = GateOp.and)
        (hin : (gateAt D k).inputs = [a, b]) (x : Fin 26 → Bool) :
        wv (26 + k) x = (wv a x && wv b x) := by
      rw [wv_gate k hk x, hand, hin, List.map_cons, List.map_cons, List.map_nil]
      exact hand_eval2 _ _
    have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin 26 → Bool)
        (ht : wv t x = true) : wv w x = true := by
      apply hp (fun u => wv u x = true) ht
      intro k hk hor a ha hva
      exact wv_or_mem hk hor ha x hva
    have isAO2_gate_inputs {k : ℕ} (hk : k < D.gates.length) :
        ∃ a b : ℕ, (gateAt D k).inputs = [a, b] ∧ a < 26 + k ∧ b < 26 + k := by
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
      have hhit_card : hit.card ≤ 2 := (Finset.card_le_card hhit_sub).trans Finset.card_le_two
      have hmerge_eq : mergeStep P u v = insert (hit.biUnion id) rest := by
        dsimp only [mergeStep]; simp only [hit, rest, hhit_ne, ↓reduceIte]
      have hnot_mem_rest : hit.biUnion id ∉ rest := by
        intro hmem; apply (Finset.mem_filter.mp hmem).2
        exact Or.inl (Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩)
      have hdisj_hr : Disjoint hit rest := by
        rw [Finset.disjoint_left]; intro B h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion_hr : hit ∪ rest = P := by
        ext B; simp only [hit, rest, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hB, _⟩ | ⟨hB, _⟩) <;> exact hB
        · intro hB
          by_cases h : u ∈ B ∨ v ∈ B
          · exact Or.inl ⟨hB, h⟩
          · exact Or.inr ⟨hB, h⟩
      have hpart : IsPartition U (mergeStep P u v) := by
        rw [hmerge_eq]; refine ⟨?_, ?_, ?_⟩
        · intro B hB
          rcases Finset.mem_insert.mp hB with rfl | hBr
          · exact ⟨u, Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩⟩
          · exact hP.1 B (Finset.mem_filter.mp hBr).1
        · intro B1 h1 B2 h2 hne
          rcases Finset.mem_insert.mp h1 with rfl | h1r <;>
            rcases Finset.mem_insert.mp h2 with rfl | h2r
          · exact (hne rfl).elim
          · rw [Finset.disjoint_left]; intro x hx1 hx2
            obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx1
            have heq := partition_unique_block hP (Finset.mem_filter.mp hB'h).1 (Finset.mem_filter.mp h2r).1 hxB' hx2
            subst heq; exact (Finset.mem_filter.mp h2r).2 (Finset.mem_filter.mp hB'h).2
          · rw [Finset.disjoint_left]; intro x hx1 hx2
            obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx2
            have heq := partition_unique_block hP (Finset.mem_filter.mp hB'h).1 (Finset.mem_filter.mp h1r).1 hxB' hx1
            subst heq; exact (Finset.mem_filter.mp h1r).2 (Finset.mem_filter.mp hB'h).2
          · exact hP.2.1 B1 (Finset.mem_filter.mp h1r).1 B2 (Finset.mem_filter.mp h2r).1 hne
        · rw [Finset.biUnion_insert]
          change hit.biUnion id ∪ rest.biUnion id = U
          ext x; rw [← hP.2.2, ← hunion_hr]
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
          Finset.card_union_of_disjoint hdisj_hr]; omega
      have hmono : ∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ mergeStep P u v, x ∈ B ∧ y ∈ B := by
        rintro x y ⟨B, hBP, hxB, hyB⟩; rw [hmerge_eq]
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
      | nil => intro P hP _; exact ⟨hP, by simp, fun _ _ h => h, (fun _ h => by cases h)⟩
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
        (wireOf : X → ℕ) (hwire_lt : ∀ x : X, wireOf x < 26)
        (hwire_inj : Function.Injective wireOf)
        (S_gates : Finset (Fin D.gates.length))
        (opWire : Fin D.gates.length → ℕ)
        (hnonempty : ∀ j ∈ S_gates, ∃ x : X, OrPath (opWire j) (wireOf x)) :
        let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
        let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
        let O_S : Finset (Fin D.gates.length) :=
          Finset.univ.filter (fun o =>
            (gateAt D o.val).op = GateOp.or ∧
            2 ≤ (reach (26 + o.val)).card ∧
            ∃ j ∈ S_gates, OrPath (opWire j) (26 + o.val))
        E_S.card ≤ O_S.card + S_gates.card := by
      let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
      let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
      let O_S : Finset (Fin D.gates.length) :=
        Finset.univ.filter (fun o =>
          (gateAt D o.val).op = GateOp.or ∧
          2 ≤ (reach (26 + o.val)).card ∧
          ∃ j ∈ S_gates, OrPath (opWire j) (26 + o.val))
      let pairOf (o : Fin D.gates.length) : Option (X × X) :=
        let a := (gateAt D o.val).inputs.getD 0 0
        let b := (gateAt D o.val).inputs.getD 1 0
        if h : (reach a).Nonempty ∧ (reach b).Nonempty then some (h.1.choose, h.2.choose) else none
      let pairs : List (X × X) := O_S.toList.filterMap pairOf
      have hpairs_len : pairs.length ≤ O_S.card := by
        have h1 := List.length_filterMap_le pairOf O_S.toList
        rw [Finset.length_toList] at h1; exact h1
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
        have hua : OrPath a (wireOf hne.1.choose) := (Finset.mem_filter.mp hne.1.choose_spec).2
        have hvb : OrPath b (wireOf hne.2.choose) := (Finset.mem_filter.mp hne.2.choose_spec).2
        have ha_mem : a ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_self
        have hb_mem : b ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
        refine ⟨Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            orPath_trans hjo (orPath_step o.isLt hor ha_mem hua)⟩⟩,
          Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            orPath_trans hjo (orPath_step o.isLt hor hb_mem hvb)⟩⟩⟩
      let P0 : Finset (Finset X) := E_S.image (fun x => {x})
      have hP0_part : IsPartition E_S P0 := by
        refine ⟨?_, ?_, ?_⟩
        · intro B hB; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hB; exact ⟨x, Finset.mem_singleton_self x⟩
        · intro B1 h1 B2 h2 hne
          obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨x2, _, rfl⟩ := Finset.mem_image.mp h2
          rw [Finset.disjoint_singleton]; intro heq; subst heq; exact hne rfl
        · ext x; simp only [P0, Finset.mem_biUnion, Finset.mem_image, id]
          constructor
          · rintro ⟨B, ⟨y, hy, rfl⟩, hx⟩; rw [Finset.mem_singleton.mp hx]; exact hy
          · intro hx; exact ⟨{x}, ⟨x, hx, rfl⟩, Finset.mem_singleton_self x⟩
      have hP0_card : P0.card = E_S.card :=
        Finset.card_image_of_injective _ (fun a b h => Finset.singleton_injective h)
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
            have hstep_ex : ∃ k < D.gates.length, w = 26 + k ∧ (gateAt D k).op = GateOp.or := by
              rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
              · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
                · exact (hne_w h2).elim
                · exact ⟨k, hk, hwk, hor⟩
              · exact ⟨k, hk, hwk, hor⟩
            obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
            let o : Fin D.gates.length := ⟨k, hk⟩
            have h2card : 2 ≤ (reach (26 + o.val)).card := by
              rw [← hwk]; exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
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
              have hlt_x : wireOf x < 26 := hwire_lt x
              rcases orPath_cases hpx with hxeq | ⟨k', _, hwk', _, c, hc, hpc⟩
              · omega
              · have hkeq : k' = k := by omega
                subst hkeq; rw [hab] at hc
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
        have hxE : x ∈ E_S := by rw [← hQ_part.2.2]; exact Finset.mem_biUnion.mpr ⟨B, hBQ, hxB⟩
        obtain ⟨j, hjS, hxj⟩ := Finset.mem_biUnion.mp hxE
        refine Finset.mem_image.mpr ⟨j, hjS, ?_⟩
        let x0 := (hnonempty j hjS).choose
        have hx0j : x0 ∈ reach (opWire j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnonempty j hjS).choose_spec⟩
        obtain ⟨B', hB'Q, hxB', hx0B'⟩ := hsame_wire (opWire j) ⟨j, hjS, orPath_refl _⟩ x hxj x0 hx0j
        have hBB' := partition_unique_block hQ_part hBQ hB'Q hxB hxB'
        have hblk_spec : blk j ∈ Q ∧ x0 ∈ blk j := by
          dsimp only [blk]; simp only [hjS, ↓reduceDIte]
          have hx0E : x0 ∈ E_S := Finset.mem_biUnion.mpr ⟨j, hjS, hx0j⟩
          exact (partition_exists_block hQ_part hx0E).choose_spec
        have hB'blk := partition_unique_block hQ_part hB'Q hblk_spec.1 hx0B' hblk_spec.2
        exact (hBB'.trans hB'blk).symm
      have hQ_le_S : Q.card ≤ S_gates.card := (Finset.card_le_card hQ_sub).trans Finset.card_image_le
      change P0.card ≤ pairs.length + Q.card at hQ_card
      change E_S.card ≤ O_S.card + S_gates.card
      omega
    let pts (w : ℕ) : Finset (Fin 13) := Finset.univ.filter (fun p => OrPath w p.val)
    let lns (w : ℕ) : Finset (Fin 13) := Finset.univ.filter (fun l => OrPath w (13 + l.val))
    have hedge_covered : ∀ p l : Fin 13, (p, l) ∈ E →
        ∃ j : Fin D.gates.length, (gateAt D j.val).op = GateOp.and ∧
          OrPath D.output (26 + j.val) ∧
          ∃ a b : ℕ, (gateAt D j.val).inputs = [a, b] ∧
            ((OrPath a p.val ∧ OrPath b (13 + l.val)) ∨
             (OrPath a (13 + l.val) ∧ OrPath b p.val)) := by
      intro p l hpl
      obtain ⟨hI, hne⟩ := (hmem_E p l).mp hpl
      obtain ⟨j, a, b, handOn, htop, hpa, hlb⟩ := hall p l hI hne
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
        OrPath D.output (26 + j.val) ∧
        ∃ p l : Fin 13, ∃ a b : ℕ, (gateAt D j.val).inputs = [a, b] ∧
          ((OrPath a p.val ∧ OrPath b (13 + l.val)) ∨
           (OrPath a (13 + l.val) ∧ OrPath b p.val)))
    let pWire (j : Fin D.gates.length) : ℕ :=
      let a := (gateAt D j.val).inputs.getD 0 0
      let b := (gateAt D j.val).inputs.getD 1 0
      if (pts a).Nonempty then a else b
    let lWire (j : Fin D.gates.length) : ℕ :=
      let a := (gateAt D j.val).inputs.getD 0 0
      let b := (gateAt D j.val).inputs.getD 1 0
      if (pts a).Nonempty then b else a
    let pSide (j : Fin D.gates.length) : Finset (Fin 13) := pts (pWire j)
    let lSide (j : Fin D.gates.length) : Finset (Fin 13) := lns (lWire j)
    have hTstar_props : ∀ j ∈ Tstar,
        (gateAt D j.val).op = GateOp.and ∧
        OrPath D.output (26 + j.val) ∧
        (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
        lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
        (∀ p ∈ pSide j, ∀ l ∈ lSide j, I p l) ∧
        ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
      intro j hj
      obtain ⟨hand, htop, p10, l10, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
      have ha_get : (gateAt D j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt D j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
      have hand_sound : ∀ x : Fin 26 → Bool, wv a x = true → wv b x = true → wv D.output x = true := by
        intro x hxa hxb
        apply orPath_sound htop x
        rw [wv_and_pair j.isLt hand hab x, hxa, hxb]; rfl
      have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
        rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
        let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p1 ∨ i = Fin.castAdd 13 p2)
        have h1 : wv p1.val x = true := by have := wv_input (Fin.castAdd 13 p1) x; simpa [x] using this
        have h2 : wv p2.val x = true := by have := wv_input (Fin.castAdd 13 p2) x; simpa [x] using this
        have ht := hand_sound x (orPath_sound (Finset.mem_filter.mp hp1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hp2).2 x h2)
        have hf := hno_pts2 p1 p2
        rw [ht] at hf; cases hf
      have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
        rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
        let x : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l1 ∨ i = Fin.natAdd 13 l2)
        have h1 : wv (13 + l1.val) x = true := by
          have hv := wv_input (Fin.natAdd 13 l1) x
          rw [Fin.val_natAdd] at hv; simpa only [x, true_or, decide_true] using hv
        have h2 : wv (13 + l2.val) x = true := by
          have hv := wv_input (Fin.natAdd 13 l2) x
          rw [Fin.val_natAdd] at hv; simpa only [x, or_true, decide_true] using hv
        have ht := hand_sound x (orPath_sound (Finset.mem_filter.mp hl1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hl2).2 x h2)
        have hf := hno_lns2 l1 l2
        rw [ht] at hf; cases hf
      have hbiclique : ∀ p l : Fin 13, ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → I p l := by
        intro p l hpl
        let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
        have hxp : wv p.val x = true := by
          have hv := wv_input (Fin.castAdd 13 p) x
          rw [Fin.val_castAdd] at hv; simpa only [x, true_or, decide_true] using hv
        have hxl : wv (13 + l.val) x = true := by
          have hv := wv_input (Fin.natAdd 13 l) x
          rw [Fin.val_natAdd] at hv; simpa only [x, or_true, decide_true] using hv
        have hout_t : wv D.output x = true := by
          rcases hpl with ⟨hpa, hlb⟩ | ⟨hpb, hla⟩
          · exact hand_sound x (orPath_sound (Finset.mem_filter.mp hpa).2 x hxp)
              (orPath_sound (Finset.mem_filter.mp hlb).2 x hxl)
          · exact hand_sound x (orPath_sound (Finset.mem_filter.mp hla).2 x hxl)
              (orPath_sound (Finset.mem_filter.mp hpb).2 x hxp)
        by_contra hni
        have hf := hno_noninc p l hni
        rw [hout_t] at hf; cases hf
      have hsides : (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
          lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
          (∀ p ∈ pSide j, ∀ l ∈ lSide j, I p l) := by
        rcases hlr0 with ⟨hpa, hlb⟩ | ⟨hla, hpb⟩
        · have hpa_ne : (pts a).Nonempty := ⟨p10, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩⟩
          have hlb_ne : (lns b).Nonempty := ⟨l10, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlb⟩⟩
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
        · have hla_ne : (lns a).Nonempty := ⟨l10, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩⟩
          have hpb_ne : (pts b).Nonempty := ⟨p10, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩⟩
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
        obtain ⟨p1, hp1m, p2, hp2m, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (pSide j).card)
        obtain ⟨l1, hl1m, l2, hl2m, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (lSide j).card)
        exact hNoC4 p1 p2 l1 l2 hpne hlne
          ⟨hsides.2.2.2.2 p1 hp1m l1 hl1m, hsides.2.2.2.2 p1 hp1m l2 hl2m,
           hsides.2.2.2.2 p2 hp2m l1 hl1m, hsides.2.2.2.2 p2 hp2m l2 hl2m⟩
      exact ⟨hand, htop, hsides.1, hsides.2.1, hsides.2.2.1, hsides.2.2.2.1, hsides.2.2.2.2, hstar⟩
    have hE_in_Tstar : ∀ p l : Fin 13, (p, l) ∈ E → ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
      intro p l hpl
      obtain ⟨j, hand, htop, a, b, hab, hlr⟩ := hedge_covered p l hpl
      have hjT : j ∈ Tstar := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hand, htop, p, l, a, b, hab, hlr⟩
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
          rw [hpW] at hlem; rw [hlem] at hla_m; cases hla_m
        have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
        have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
        exact ⟨by simpa [pSide, hpW] using hpb_m, by simpa [lSide, hlW] using hla_m⟩
    let Tpt : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
    let Tln : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
    have hTpt_Tln_disj : Disjoint Tpt Tln := by
      rw [Finset.disjoint_left]; intro j h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hTpt_Tln_union : Tpt ∪ Tln = Tstar := by
      ext j; simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]; tauto
    have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
      rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
    let centerP (j : Fin D.gates.length) : Fin 13 :=
      if h : (pSide j).Nonempty then h.choose else 0
    let centerL (j : Fin D.gates.length) : Fin 13 :=
      if h : (lSide j).Nonempty then h.choose else 0
    have hcenterP_eq : ∀ j ∈ Tpt, ∀ p ∈ pSide j, p = centerP j := by
      intro j hj p hp
      have hjT := (Finset.mem_filter.mp hj).1
      have hcard1 := (Finset.mem_filter.mp hj).2
      have hne := (hTstar_props j hjT).2.2.1
      have hmem_c : centerP j ∈ pSide j := by dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
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
      have hmem_c : centerL j ∈ lSide j := by dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
      exact Finset.card_le_one.mp (le_of_eq hcard1) l hl (centerL j) hmem_c
    have hcenterP_mem : ∀ j ∈ Tpt, centerP j ∈ pSide j := by
      intro j hj
      have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.1
      dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
    have hcenterL_mem : ∀ j ∈ Tln, centerL j ∈ lSide j := by
      intro j hj
      have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.2.1
      dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
    let A : Finset (Fin 13) := Tpt.image centerP
    let B : Finset (Fin 13) := Tln.image centerL
    have hAB_le_Tstar : A.card + B.card ≤ Tstar.card := by
      have hA : A.card ≤ Tpt.card := Finset.card_image_le
      have hB : B.card ≤ Tln.card := Finset.card_image_le
      omega
    have hAB_cover : 13 ≤ A.card + B.card := by
      have hsub : E ⊆ A.biUnion (fun p => (Finset.univ.filter (fun l : Fin 13 => p - l ∈ D7)).image (fun l => (p, l))) ∪
          B.biUnion (fun l => (Finset.univ.filter (fun p : Fin 13 => p - l ∈ D7)).image (fun p => (p, l))) := by
        intro e he
        obtain ⟨j, hjT, hpj, hlj⟩ := hE_in_Tstar e.1 e.2 he
        have hIe : e.1 - e.2 ∈ D7 := ((hmem_E e.1 e.2).mp he).1
        by_cases h1 : (pSide j).card = 1
        · have hjpt : j ∈ Tpt := Finset.mem_filter.mpr ⟨hjT, h1⟩
          have hcp : centerP j = e.1 := (hcenterP_eq j hjpt e.1 hpj).symm
          apply Finset.mem_union_left
          refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_image.mpr ⟨j, hjpt, hcp⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIe⟩, rfl⟩
        · have hjln : j ∈ Tln := Finset.mem_filter.mpr ⟨hjT, h1⟩
          have hcl : centerL j = e.2 := (hcenterL_eq j hjln e.2 hlj).symm
          apply Finset.mem_union_right
          refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_image.mpr ⟨j, hjln, hcl⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIe⟩, rfl⟩
      have hle4 : E.card ≤ 4 * A.card + 4 * B.card := by
        calc E.card
            ≤ (A.biUnion (fun p => (Finset.univ.filter (fun l : Fin 13 => p - l ∈ D7)).image (fun l => (p, l))) ∪
                B.biUnion (fun l => (Finset.univ.filter (fun p : Fin 13 => p - l ∈ D7)).image (fun p => (p, l)))).card :=
              Finset.card_le_card hsub
          _ ≤ (A.biUnion (fun p => (Finset.univ.filter (fun l : Fin 13 => p - l ∈ D7)).image (fun l => (p, l)))).card +
                (B.biUnion (fun l => (Finset.univ.filter (fun p : Fin 13 => p - l ∈ D7)).image (fun p => (p, l)))).card :=
              Finset.card_union_le _ _
          _ ≤ (∑ p ∈ A, ((Finset.univ.filter (fun l : Fin 13 => p - l ∈ D7)).image (fun l => (p, l))).card) +
                (∑ l ∈ B, ((Finset.univ.filter (fun p : Fin 13 => p - l ∈ D7)).image (fun p => (p, l))).card) :=
              Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
          _ ≤ (∑ p ∈ A, (Finset.univ.filter (fun l : Fin 13 => p - l ∈ D7)).card) +
                (∑ l ∈ B, (Finset.univ.filter (fun p : Fin 13 => p - l ∈ D7)).card) :=
              Nat.add_le_add (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
                (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
          _ = (∑ _p ∈ A, 4) + (∑ _l ∈ B, 4) := by
              rw [Finset.sum_congr rfl (fun p _ => hdegP p), Finset.sum_congr rfl (fun l _ => hdegL l)]
          _ = 4 * A.card + 4 * B.card := by
              simp only [Finset.sum_const, smul_eq_mul]; omega
      omega
    let Otop : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt D o.val).op = GateOp.or ∧
        OrPath D.output (26 + o.val) ∧
        ∃ a ∈ Tstar, OrPath (26 + o.val) (26 + a.val))
    have hOtop_disj_Tstar : Disjoint Otop Tstar := by
      rw [Finset.disjoint_left]; intro j h1 h2
      have hor := (Finset.mem_filter.mp h1).2.1
      have hand := (hTstar_props j h2).1
      rw [hor] at hand; cases hand
    have hTstar_le_Otop : Tstar.card ≤ Otop.card + 1 := by
      by_cases hle1 : Tstar.card ≤ 1
      · omega
      · obtain ⟨a1, ha1, a2, ha2, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < Tstar.card)
        have hop1 := (hTstar_props a1 ha1).2.1
        have hop2 := (hTstar_props a2 ha2).2.1
        have hroot_ex : ∃ root ∈ Otop, D.output = 26 + root.val := by
          rcases orPath_cases hop1 with heq1 | ⟨k, hk, hok, hork, _, _, _⟩
          · rcases orPath_cases hop2 with heq2 | ⟨k, hk, hok, hork, _, _, _⟩
            · exact (hne12 (Fin.ext (by omega))).elim
            · have : k = a1.val := by omega
              subst this; have hand1 := (hTstar_props a1 ha1).1; rw [hork] at hand1; cases hand1
          · refine ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hork,
              hok ▸ orPath_refl _, a1, ha1, hok ▸ hop1⟩, hok⟩
        obtain ⟨root, hrootO, hroot_eq⟩ := hroot_ex
        let H := Otop ∪ Tstar
        have hrootH : root ∈ H := Finset.mem_union_left _ hrootO
        have hH_card : H.card = Otop.card + Tstar.card := Finset.card_union_of_disjoint hOtop_disj_Tstar
        have hpar_ex : ∀ x ∈ H.erase root, ∃ y ∈ Otop, 26 + x.val ∈ (gateAt D y.val).inputs := by
          intro x hx
          have hxne : x ≠ root := (Finset.mem_erase.mp hx).1
          have hxH : x ∈ H := (Finset.mem_erase.mp hx).2
          have hx_out : OrPath D.output (26 + x.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.1
            · exact (hTstar_props x hT).2.1
          have hx_a : ∃ a ∈ Tstar, OrPath (26 + x.val) (26 + a.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.2
            · exact ⟨x, hT, orPath_refl _⟩
          have hne_out : D.output ≠ 26 + x.val := by rw [hroot_eq]; intro h; exact hxne (Fin.ext (by omega))
          obtain ⟨y, hy, hory, hpy, hxin⟩ := orPath_parent hx_out hne_out
          obtain ⟨a, haT, hxa⟩ := hx_a
          refine ⟨⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hory, hpy,
            a, haT, orPath_step hy hory hxin hxa⟩, hxin⟩
        let par (x : Fin D.gates.length) : Fin D.gates.length :=
          if hx : x ∈ H.erase root then (hpar_ex x hx).choose else root
        have hpar_mem : ∀ x ∈ H.erase root, par x ∈ Otop := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.1
        have hpar_in : ∀ x ∈ H.erase root, 26 + x.val ∈ (gateAt D (par x).val).inputs := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.2
        have hfiber_le2 : ∀ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ 2 := by
          intro y _
          let F := (H.erase root).filter (fun x => par x = y)
          have hsub : F.image (fun x : Fin D.gates.length => 26 + x.val) ⊆ (gateAt D y.val).inputs.toFinset := by
            intro w hw
            obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hw
            obtain ⟨hxH, hxy⟩ := Finset.mem_filter.mp hxF
            rw [List.mem_toFinset, ← hxy]; exact hpar_in x hxH
          have hinj : Function.Injective (fun x : Fin D.gates.length => 26 + x.val) :=
            fun a b h => Fin.ext (by dsimp only at h; omega)
          have h1 : F.card = (F.image (fun x : Fin D.gates.length => 26 + x.val)).card :=
            (Finset.card_image_of_injective F hinj).symm
          have h2 : (F.image (fun x : Fin D.gates.length => 26 + x.val)).card ≤ ((gateAt D y.val).inputs.toFinset).card :=
            Finset.card_le_card hsub
          have h3 : ((gateAt D y.val).inputs.toFinset).card ≤ (gateAt D y.val).inputs.length :=
            List.toFinset_card_le _
          have h4 : (gateAt D y.val).inputs.length = 2 := by
            obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs y.isLt; rw [hab]; rfl
          change F.card ≤ 2; omega
        have hsum_eq : (H.erase root).card = ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card :=
          Finset.card_eq_sum_card_fiberwise (f := par) hpar_mem
        have hsum_le : ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ ∑ _y ∈ Otop, 2 :=
          Finset.sum_le_sum hfiber_le2
        simp only [Finset.sum_const, smul_eq_mul] at hsum_le
        have herase : (H.erase root).card + 1 = H.card := Finset.card_erase_add_one hrootH
        omega
    let Tpt_p (p : Fin 13) : Finset (Fin D.gates.length) := Tpt.filter (fun j => centerP j = p)
    let E_p (p : Fin 13) : Finset (Fin 13) := (Tpt_p p).biUnion lSide
    let Obot_p (p : Fin 13) : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt D o.val).op = GateOp.or ∧
        2 ≤ (lns (26 + o.val)).card ∧
        ∃ j ∈ Tpt_p p, OrPath (lWire j) (26 + o.val))
    let Tln_l (l : Fin 13) : Finset (Fin D.gates.length) := Tln.filter (fun j => centerL j = l)
    let E_l (l : Fin 13) : Finset (Fin 13) := (Tln_l l).biUnion pSide
    let Obot_l (l : Fin 13) : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt D o.val).op = GateOp.or ∧
        2 ≤ (pts (26 + o.val)).card ∧
        ∃ j ∈ Tln_l l, OrPath (pWire j) (26 + o.val))
    have hEp_bound : ∀ p ∈ A, (E_p p).card ≤ (Obot_p p).card + (Tpt_p p).card := by
      intro p _
      exact side_component_bound
        (fun l : Fin 13 => 13 + l.val) (fun l => by omega)
        (fun l1 l2 h => Fin.ext (by dsimp only at h; omega))
        (Tpt_p p) lWire
        (fun j hj => by
          obtain ⟨l, hl⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.2.1
          exact ⟨l, (Finset.mem_filter.mp hl).2⟩)
    have hEl_bound : ∀ l ∈ B, (E_l l).card ≤ (Obot_l l).card + (Tln_l l).card := by
      intro l _
      exact side_component_bound
        (fun p : Fin 13 => p.val) (fun p => by omega)
        (fun p1 p2 h => Fin.ext h)
        (Tln_l l) pWire
        (fun j hj => by
          obtain ⟨p, hp⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.1
          exact ⟨p, (Finset.mem_filter.mp hp).2⟩)
    have hObot_p_disj : Set.PairwiseDisjoint (A : Set (Fin 13)) Obot_p := by
      intro p1 _ p2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro o h1 h2
      obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
      obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (lns (26 + o.val)).card)
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
        ⟨hpr1 p1 hp1_in l1 hl1_j1, hpr1 p1 hp1_in l2 hl2_j1,
         hpr2 p2 hp2_in l1 hl1_j2, hpr2 p2 hp2_in l2 hl2_j2⟩
    have hObot_l_disj : Set.PairwiseDisjoint (B : Set (Fin 13)) Obot_l := by
      intro l1 _ l2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro o h1 h2
      obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (pts (26 + o.val)).card)
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
        ⟨hpr1 p1 hp1_j1 l1 hl1_in, hpr2 p1 hp1_j2 l2 hl2_in,
         hpr1 p2 hp2_j1 l1 hl1_in, hpr2 p2 hp2_j2 l2 hl2_in⟩
    let ObotA := A.biUnion Obot_p
    let ObotB := B.biUnion Obot_l
    have hObotAB_disj : Disjoint ObotA ObotB := by
      rw [Finset.disjoint_left]; intro o hA hB
      obtain ⟨p, _, hoA⟩ := Finset.mem_biUnion.mp hA
      obtain ⟨l, _, hoB⟩ := Finset.mem_biUnion.mp hB
      have hcard_l := (Finset.mem_filter.mp hoA).2.2.1
      obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (26 + o.val)).card)
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
      rw [Finset.disjoint_left]; intro o h1 h2
      have hand := (hTstar_props o h2).1
      rcases Finset.mem_union.mp h1 with hA | hB
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
        have hor := (Finset.mem_filter.mp ho).2.1; rw [hor] at hand; cases hand
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
        have hor := (Finset.mem_filter.mp ho).2.1; rw [hor] at hand; cases hand
    have hObot_disj_Otop : Disjoint Obot Otop := by
      rw [Finset.disjoint_left]; intro o hbot htop
      have hop_out := (Finset.mem_filter.mp htop).2.2.1
      rcases Finset.mem_union.mp hbot with hA | hB
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
        have hcard_l := (Finset.mem_filter.mp ho).2.2.1
        obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (26 + o.val)).card)
        have hop := orPath_trans hop_out (Finset.mem_filter.mp hl0).2
        let x : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l0 ∨ i = Fin.natAdd 13 l0)
        have hx_l : wv (13 + l0.val) x = true := by
          have hv := wv_input (Fin.natAdd 13 l0) x
          rw [Fin.val_natAdd] at hv; simpa only [x, true_or, decide_true] using hv
        have ht := orPath_sound hop x hx_l
        have hf := hno_lns2 l0 l0
        rw [ht] at hf; cases hf
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
        have hcard_p := (Finset.mem_filter.mp ho).2.2.1
        obtain ⟨p10, hp10⟩ := Finset.card_pos.mp (by omega : 0 < (pts (26 + o.val)).card)
        have hop := orPath_trans hop_out (Finset.mem_filter.mp hp10).2
        let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p10 ∨ i = Fin.castAdd 13 p10)
        have hx_p : wv p10.val x = true := by
          have hv := wv_input (Fin.castAdd 13 p10) x
          rw [Fin.val_castAdd] at hv; simpa only [x, true_or, decide_true] using hv
        have ht := orPath_sound hop x hx_p
        have hf := hno_pts2 p10 p10
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
            Nat.add_le_add (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
              (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
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
    have h3disj : Tstar.card + Obot.card + Otop.card ≤ D.size := by
      have hdisj1 : Disjoint (Tstar ∪ Obot) Otop := by
        rw [Finset.disjoint_union_left]; exact ⟨hOtop_disj_Tstar.symm, hObot_disj_Otop⟩
      have hcard_u : ((Tstar ∪ Obot) ∪ Otop).card = Tstar.card + Obot.card + Otop.card := by
        rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hObot_disj_Tstar.symm]
      have hle : ((Tstar ∪ Obot) ∪ Otop).card ≤ (Finset.univ : Finset (Fin D.gates.length)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      simp only [Finset.card_univ, Fintype.card_fin] at hle
      change Tstar.card + Obot.card + Otop.card ≤ D.gates.length
      omega
    omega
  · have huncov : ∃ p l : Fin 13, p - l ∈ D7 ∧ (p ≠ p0 ∨ l ≠ 0) ∧
        ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
          PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
          PEqualNP.ReadTwo.orp D 26 p.val a ∧
          PEqualNP.ReadTwo.orp D 26 (13 + l.val) b := by
      by_contra hno
      apply hall
      intro p l hpl hne
      by_contra hnot
      exact hno ⟨p, l, hpl, hne, hnot⟩
    by_cases hclean : ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
        ∀ Q : Finset (Fin 13), isQuad Q → (D.wires (x9 Q)).getD (26 + j) false = false
    · exact hCleanUncovered D p0 hD_AO hD_true hD_false huncov hclean
    · have hdirty : ∃ j g, D.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∃ Q : Finset (Fin 13), isQuad Q ∧ (D.wires (x9 Q)).getD (26 + j) false = true := by
        by_contra hno
        apply hclean
        intro j g hgj hgop Q hQ
        by_contra hne
        exact hno ⟨j, g, hgj, hgop, Q, hQ, Bool.eq_true_of_not_eq_false hne⟩
      by_cases honehot : ∃ j g, D.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∃ v : Fin 26, (D.wires (List.ofFn fun i : Fin 26 => decide (i = v))).getD (26 + j) false = true
      · exact hDirtyOneHot D p0 hD_AO hD_true hD_false huncov honehot
      · have hno1 : ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
            ∀ v : Fin 26, (D.wires (List.ofFn fun i : Fin 26 => decide (i = v))).getD (26 + j) false = false := by
          intro j g hgj hgop v
          by_contra hne
          exact honehot ⟨j, g, hgj, hgop, v, Bool.eq_true_of_not_eq_false hne⟩
        exact hDirtyNoOneHot D p0 hD_AO hD_true hD_false huncov hno1 hdirty
