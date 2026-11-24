import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4189_17
    (hNoExtra :
      have E : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]
      have F : (Fin 14 → Bool) → Prop := fun x =>
        ∃ p l : Fin 14, (E.getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true
      have cnt : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun C =>
        List.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op false true false (fun _ => false) false) C.gates
      have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        PEqualNP.MetaComplexity.Monotone2 D ∧
          ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ F x
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        ok D →
        (∀ D' : PEqualNP.CircuitLowerBounds.Circuit, ok D' → cnt D < cnt D' ∨ cnt D = cnt D' ∧ D.size ≤ D'.size) →
        19 ≤ cnt D)
    (hClean :
      have E : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]
      have F : (Fin 14 → Bool) → Prop := fun x =>
        ∃ p l : Fin 14, (E.getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true
      have cnt : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun C =>
        List.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op false true false (fun _ => false) false) C.gates
      have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        PEqualNP.MetaComplexity.Monotone2 C ∧
          ∀ x : Fin 14 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ F x
      have w : PEqualNP.CircuitLowerBounds.Circuit → (Fin 14 → Bool) → ℕ → Bool := fun C x k =>
        (C.wires (List.ofFn x ++ [x 0 || x 1])).getD k false
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        ok C →
        (∀ D : PEqualNP.CircuitLowerBounds.Circuit, ok D → cnt C < cnt D ∨ cnt C = cnt D ∧ C.size ≤ D.size) →
        (∃ g ∈ C.gates, 14 ∈ g.inputs) →
        (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ x : Fin 14 → Bool, ¬ F x → w C x (15 + j) = false) →
        19 ≤ cnt C)
    (hDirtyOneHot :
      have E : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]
      have F : (Fin 14 → Bool) → Prop := fun x =>
        ∃ p l : Fin 14, (E.getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true
      have cnt : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun C =>
        List.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op false true false (fun _ => false) false) C.gates
      have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        PEqualNP.MetaComplexity.Monotone2 C ∧
          ∀ x : Fin 14 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ F x
      have w : PEqualNP.CircuitLowerBounds.Circuit → (Fin 14 → Bool) → ℕ → Bool := fun C x k =>
        (C.wires (List.ofFn x ++ [x 0 || x 1])).getD k false
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        ok C →
        (∀ D : PEqualNP.CircuitLowerBounds.Circuit, ok D → cnt C < cnt D ∨ cnt C = cnt D ∧ C.size ≤ D.size) →
        (∃ g ∈ C.gates, 14 ∈ g.inputs) →
        (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ v : Fin 14, w C (fun i => decide (i = v)) (15 + j) = true) →
        19 ≤ cnt C)
    (hDirtyNoOneHot :
      have E : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]
      have F : (Fin 14 → Bool) → Prop := fun x =>
        ∃ p l : Fin 14, (E.getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true
      have cnt : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun C =>
        List.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op false true false (fun _ => false) false) C.gates
      have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        PEqualNP.MetaComplexity.Monotone2 C ∧
          ∀ x : Fin 14 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ F x
      have w : PEqualNP.CircuitLowerBounds.Circuit → (Fin 14 → Bool) → ℕ → Bool := fun C x k =>
        (C.wires (List.ofFn x ++ [x 0 || x 1])).getD k false
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        ok C →
        (∀ D : PEqualNP.CircuitLowerBounds.Circuit, ok D → cnt C < cnt D ∨ cnt C = cnt D ∧ C.size ≤ D.size) →
        (∃ g ∈ C.gates, 14 ∈ g.inputs) →
        (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ v : Fin 14, w C (fun i => decide (i = v)) (15 + j) = false) →
        (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ x : Fin 14 → Bool, ¬ F x ∧ w C x (15 + j) = true) →
        19 ≤ cnt C) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 (1 : Fin (14 : ℕ))]]) = Bool.true ↔ x2 x6)) → (19 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x7.op Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false) x4.gates := by
  dsimp only
  intro C0 hmono0 hbd0
  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let adj : ℕ → ℕ → Prop := fun a b =>
    (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a 0).testBit b = true
  let hasEdge : (Fin 14 → Bool) → Prop := fun x =>
    ∃ p l : Fin 14, adj p.val l.val ∧ x p = true ∧ x l = true
  let cnt : Circuit → ℕ := fun C =>
    List.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) C.gates
  let ok14 : Circuit → Prop := fun D =>
    Monotone2 D ∧ ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ hasEdge x
  let ok15 : Circuit → Prop := fun C =>
    Monotone2 C ∧ ∀ x : Fin 14 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ hasEdge x
  let w : Circuit → (Fin 14 → Bool) → ℕ → Bool := fun C x k =>
    (C.wires (List.ofFn x ++ [x 0 || x 1])).getD k false
  have hadj_iff : ∀ a b : Fin 14, (a.val, b.val) ∈ edges ↔ adj a.val b.val := by decide
  have hadj_bip : ∀ a b : Fin 14, adj a.val b.val → a.val < 7 ∧ 7 ≤ b.val := by decide
  have hhasEdge_iff (x : Fin 14 → Bool) :
      (∃ p l : Fin 14, (p.val, l.val) ∈ edges ∧ x p = true ∧ x l = true) ↔ hasEdge x := by
    constructor
    · rintro ⟨p, l, hmem, hp, hl⟩
      exact ⟨p, l, (hadj_iff p l).mp hmem, hp, hl⟩
    · rintro ⟨p, l, hadj, hp, hl⟩
      exact ⟨p, l, (hadj_iff p l).mpr hadj, hp, hl⟩
  have hbd : ∀ x : Fin 14 → Bool,
      ((hasEdge x ∧ ∀ i : Fin 14, x i = true → ¬ hasEdge (Function.update x i false)) ∨
        (¬ hasEdge x ∧ ∀ i : Fin 14, x i = false → hasEdge (Function.update x i true))) →
      (C0.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 1]]) = true ↔ hasEdge x) := by
    intro x hx
    have hx0 : ((∃ p l : Fin 14, (p.val, l.val) ∈ edges ∧ x p = true ∧ x l = true) ∧
          ∀ i : Fin 14, x i = true → ¬ ∃ p l : Fin 14, (p.val, l.val) ∈ edges ∧ Function.update x i false p = true ∧ Function.update x i false l = true) ∨
        (¬ (∃ p l : Fin 14, (p.val, l.val) ∈ edges ∧ x p = true ∧ x l = true) ∧
          ∀ i : Fin 14, x i = false → ∃ p l : Fin 14, (p.val, l.val) ∈ edges ∧ Function.update x i true p = true ∧ Function.update x i true l = true) := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨(hhasEdge_iff x).mpr h1, fun i hi hup => h2 i hi ((hhasEdge_iff _).mp hup)⟩
      · exact Or.inr ⟨fun h => h1 ((hhasEdge_iff x).mp h), fun i hi => (hhasEdge_iff _).mpr (h2 i hi)⟩
    exact (hbd0 x hx0).trans (hhasEdge_iff x)
  have hor_eval (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    change (a || (b || false)) = (a || b)
    exact congrArg (a || ·) (Bool.or_false b)
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l d (n := j) (by omega)]
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
  let wLe : List Bool → List Bool → Prop := fun w1 w2 =>
    w1.length = w2.length ∧ ∀ i, w1.getD i false = true → w2.getD i false = true
  have run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      ∀ w1 w2, wLe w1 w2 → wLe (run gs w1) (run gs w2) := by
    induction gs with
    | nil => intro w1 w2 h; exact h
    | cons g rest ih =>
      intro w1 w2 hle
      simp only [run, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      have hg := (hgs g List.mem_cons_self).1
      have hbit : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
        rcases hg with hop | hop
        · rw [hop]
          change (g.inputs.map fun i => w1.getD i false).all id = true →
            (g.inputs.map fun i => w2.getD i false).all id = true
          intro hall
          rw [List.all_eq_true] at hall ⊢
          intro b hb
          rw [List.mem_map] at hb
          obtain ⟨i, hi, rfl⟩ := hb
          exact hle.2 i (hall (w1.getD i false) (List.mem_map_of_mem hi))
        · rw [hop]
          change (g.inputs.map fun i => w1.getD i false).any id = true →
            (g.inputs.map fun i => w2.getD i false).any id = true
          intro hany
          rw [List.any_eq_true] at hany ⊢
          obtain ⟨b, hb, hbt⟩ := hany
          rw [List.mem_map] at hb
          obtain ⟨i, hi, rfl⟩ := hb
          exact ⟨w2.getD i false, List.mem_map_of_mem hi, hle.2 i hbt⟩
      refine ⟨by simp only [step, List.length_append, hle.1, List.length_cons, List.length_nil], ?_⟩
      intro i hi
      dsimp only [step] at hi ⊢
      by_cases heq : i = w1.length
      · subst heq
        rw [getD_snoc_eq w1 _ false] at hi
        rw [hle.1, getD_snoc_eq w2 _ false]
        exact hbit hi
      · have heq2 : i ≠ w2.length := by rw [← hle.1]; exact heq
        rw [getD_snoc_ne w1 _ false i heq] at hi
        rw [getD_snoc_ne w2 _ false i heq2]
        exact hle.2 i hi
  have hC0_mono (x y : Fin 14 → Bool) (hxy : ∀ i : Fin 14, x i = true → y i = true)
      (hx : C0.eval (List.ofFn x ++ [x 0 || x 1]) = true) :
      C0.eval (List.ofFn y ++ [y 0 || y 1]) = true := by
    have hwle : wLe (List.ofFn x ++ [x 0 || x 1]) (List.ofFn y ++ [y 0 || y 1]) := by
      refine ⟨by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil], ?_⟩
      intro i hi
      by_cases hi14 : i < 14
      · have h1 : (List.ofFn x ++ [x 0 || x 1]).getD i false = x ⟨i, hi14⟩ := by
          have hlt : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hi14
          rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        have h2 : (List.ofFn y ++ [y 0 || y 1]).getD i false = y ⟨i, hi14⟩ := by
          have hlt : i < (List.ofFn y).length := by simp only [List.length_ofFn]; exact hi14
          rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rw [h1] at hi
        rw [h2]
        exact hxy ⟨i, hi14⟩ hi
      · by_cases hi_eq : i = 14
        · subst hi_eq
          have h1 : (List.ofFn x ++ [x 0 || x 1]).getD 14 false = (x 0 || x 1) := by
            simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x) (x 0 || x 1) false
          have h2 : (List.ofFn y ++ [y 0 || y 1]).getD 14 false = (y 0 || y 1) := by
            simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn y) (y 0 || y 1) false
          rw [h1] at hi
          rw [h2, Bool.or_eq_true]
          rcases (Bool.or_eq_true _ _).mp hi with h0 | h1x
          · exact Or.inl (hxy 0 h0)
          · exact Or.inr (hxy 1 h1x)
        · rw [List.getD_eq_default _ false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)] at hi
          cases hi
    exact (run_mono C0.gates hmono0 _ _ hwle).2 C0.output hx
  have hmax_indep : ∀ (k : ℕ) (x : Fin 14 → Bool), ¬ hasEdge x →
      (Finset.univ.filter (fun i : Fin 14 => x i = false)).card ≤ k →
      ∃ y : Fin 14 → Bool, (∀ i, x i = true → y i = true) ∧
        ¬ hasEdge y ∧ ∀ i, y i = false → hasEdge (Function.update y i true) := by
    intro k
    induction k with
    | zero =>
      intro x hnx hcard
      refine ⟨x, fun _ h => h, hnx, ?_⟩
      intro i hi
      have hmem : i ∈ Finset.univ.filter (fun j : Fin 14 => x j = false) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
    | succ k ih =>
      intro x hnx hcard
      by_cases hmax : ∀ i : Fin 14, x i = false → hasEdge (Function.update x i true)
      · exact ⟨x, fun _ h => h, hnx, hmax⟩
      · have hex : ∃ i : Fin 14, x i = false ∧ ¬ hasEdge (Function.update x i true) := by
          by_contra h
          exact hmax (fun i hi => by
            by_contra hne
            exact h ⟨i, hi, hne⟩)
        obtain ⟨i0, hi0, hnx'⟩ := hex
        let x' : Fin 14 → Bool := Function.update x i0 true
        have hsub : Finset.univ.filter (fun j : Fin 14 => x' j = false) =
            (Finset.univ.filter (fun j : Fin 14 => x j = false)).erase i0 := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, x']
          by_cases hj : j = i0
          · subst hj
            rw [Function.update_self]
            exact ⟨(fun h => by cases h), (fun h => absurd rfl h.1)⟩
          · rw [Function.update_of_ne hj]
            exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩
        have hmem0 : i0 ∈ Finset.univ.filter (fun j : Fin 14 => x j = false) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi0]
        have hcard' : (Finset.univ.filter (fun j : Fin 14 => x' j = false)).card ≤ k := by
          rw [hsub, Finset.card_erase_of_mem hmem0]
          have hpos := Finset.card_pos.mpr ⟨i0, hmem0⟩
          omega
        obtain ⟨y, hxy', hny, hmaxy⟩ := ih x' hnx' hcard'
        refine ⟨y, fun i hi => hxy' i ?_, hny, hmaxy⟩
        dsimp only [x']
        by_cases hji : i = i0
        · subst hji; rw [Function.update_self]
        · rw [Function.update_of_ne hji]; exact hi
  have hFull0 : ∀ x : Fin 14 → Bool,
      C0.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ hasEdge x := by
    intro x
    constructor
    · intro hev
      by_contra hnx
      have hcard : (Finset.univ.filter (fun i : Fin 14 => x i = false)).card ≤ 14 := by
        have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin 14)) (fun i => x i = false)
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        exact h1
      obtain ⟨y, hxy, hny, hmaxy⟩ := hmax_indep 14 x hnx hcard
      have hby := hbd y (Or.inr ⟨hny, hmaxy⟩)
      rw [hor_eval (y 0) (y 1)] at hby
      exact hny (hby.mp (hC0_mono x y hxy hev))
    · intro hx
      obtain ⟨p, l, hadj, hp, hl⟩ := hx
      have hbip := hadj_bip p l hadj
      let xe : Fin 14 → Bool := fun i => decide (i = p ∨ i = l)
      have hxe_edge : hasEdge xe := ⟨p, l, hadj, by simp only [xe, true_or, decide_true], by simp only [xe, or_true, decide_true]⟩
      have hxe_min : ∀ i : Fin 14, xe i = true → ¬ hasEdge (Function.update xe i false) := by
        intro i hi hup
        have hip : i = p ∨ i = l := by simpa only [xe, decide_eq_true_eq] using hi
        obtain ⟨a, b, hab, ha, hb⟩ := hup
        have hbip_ab := hadj_bip a b hab
        rcases hip with hip | hip
        · subst i
          have hne : a ≠ p := by
            intro h; subst h; rw [Function.update_self] at ha; cases ha
          rw [Function.update_of_ne hne] at ha
          have ha_pl : a = p ∨ a = l := by simpa only [xe, decide_eq_true_eq] using ha
          rcases ha_pl with h1 | h2
          · exact hne h1
          · subst h2; omega
        · subst i
          have hne : b ≠ l := by
            intro h; subst h; rw [Function.update_self] at hb; cases hb
          rw [Function.update_of_ne hne] at hb
          have hb_pl : b = p ∨ b = l := by simpa only [xe, decide_eq_true_eq] using hb
          rcases hb_pl with h1 | h2
          · subst h1; omega
          · exact hne h2
      have hbxe := hbd xe (Or.inl ⟨hxe_edge, hxe_min⟩)
      rw [hor_eval (xe 0) (xe 1)] at hbxe
      have hev_xe : C0.eval (List.ofFn xe ++ [xe 0 || xe 1]) = true := hbxe.mpr hxe_edge
      apply hC0_mono xe x _ hev_xe
      intro i hi
      have hip : i = p ∨ i = l := by simpa only [xe, decide_eq_true_eq] using hi
      rcases hip with rfl | rfl
      · exact hp
      · exact hl
  have hLexMin (P : Circuit → Prop) (Cinit : Circuit) (hP0 : P Cinit) :
      ∃ C : Circuit, P C ∧ cnt C ≤ cnt Cinit ∧
        ∀ D : Circuit, P D → cnt C < cnt D ∨ (cnt C = cnt D ∧ C.size ≤ D.size) := by
    have hMinCnt : ∀ k : ℕ, ∀ C : Circuit, P C → cnt C ≤ k →
        ∃ C1 : Circuit, P C1 ∧ cnt C1 ≤ cnt C ∧ ∀ D : Circuit, P D → cnt C1 ≤ cnt D := by
      intro k
      induction k with
      | zero =>
        intro C hPC hle
        exact ⟨C, hPC, Nat.le_refl _, fun D _ => by omega⟩
      | succ k ih =>
        intro C hPC hle
        by_cases hmin : ∀ D : Circuit, P D → cnt C ≤ cnt D
        · exact ⟨C, hPC, Nat.le_refl _, hmin⟩
        · have hex : ∃ D : Circuit, P D ∧ cnt D < cnt C := by
            by_contra h
            exact hmin (fun D hPD => by
              by_contra hlt
              exact h ⟨D, hPD, by omega⟩)
          obtain ⟨D, hPD, hlt⟩ := hex
          obtain ⟨C1, hPC1, hle1, hmin1⟩ := ih D hPD (by omega)
          exact ⟨C1, hPC1, Nat.le_trans hle1 (Nat.le_of_lt hlt), hmin1⟩
    obtain ⟨C1, hPC1, hcnt1, hminCnt⟩ := hMinCnt (cnt Cinit) Cinit hP0 (Nat.le_refl _)
    have hMinSz : ∀ n : ℕ, ∀ C : Circuit, P C → cnt C = cnt C1 → C.size ≤ n →
        ∃ C2 : Circuit, P C2 ∧ cnt C2 = cnt C1 ∧ ∀ D : Circuit, P D → cnt D = cnt C1 → C2.size ≤ D.size := by
      intro n
      induction n with
      | zero =>
        intro C hPC hce hsz
        exact ⟨C, hPC, hce, fun D _ _ => by omega⟩
      | succ n ih =>
        intro C hPC hce hsz
        by_cases hmin : ∀ D : Circuit, P D → cnt D = cnt C1 → C.size ≤ D.size
        · exact ⟨C, hPC, hce, hmin⟩
        · have hex : ∃ D : Circuit, P D ∧ cnt D = cnt C1 ∧ D.size < C.size := by
            by_contra h
            exact hmin (fun D hPD hDe => by
              by_contra hlt
              exact h ⟨D, hPD, hDe, by omega⟩)
          obtain ⟨D, hPD, hDe, hlt⟩ := hex
          exact ih D hPD hDe (by omega)
    obtain ⟨C2, hPC2, hce2, hminSz⟩ := hMinSz C1.size C1 hPC1 rfl (Nat.le_refl _)
    refine ⟨C2, hPC2, by omega, fun D hPD => ?_⟩
    have hge := hminCnt D hPD
    by_cases heq : cnt C2 = cnt D
    · exact Or.inr ⟨heq, hminSz D hPD (by omega)⟩
    · exact Or.inl (by omega)
  obtain ⟨C, hokC, hcntLe, hMinC⟩ := hLexMin ok15 C0 ⟨hmono0, hFull0⟩
  obtain ⟨hmono, hFull⟩ := hokC
  have h19C : 19 ≤ cnt C := by
    by_cases hreads14 : ∃ g ∈ C.gates, 14 ∈ g.inputs
    · by_cases hAllClean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ x : Fin 14 → Bool, ¬ hasEdge x → w C x (15 + j) = false
      · exact hClean C ⟨hmono, hFull⟩ hMinC hreads14 hAllClean
      · have hDirty : ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
            ∃ x : Fin 14 → Bool, ¬ hasEdge x ∧ w C x (15 + j) = true := by
          by_contra h
          exact hAllClean (fun j hj hand x hnx => by
            cases hval : w C x (15 + j)
            · rfl
            · exact absurd ⟨j, hj, hand, x, hnx, hval⟩ h)
        by_cases hOneHot : ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
            ∃ v : Fin 14, w C (fun i => decide (i = v)) (15 + j) = true
        · exact hDirtyOneHot C ⟨hmono, hFull⟩ hMinC hreads14 hOneHot
        · have hNoOneHot : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
              ∀ v : Fin 14, w C (fun i => decide (i = v)) (15 + j) = false := by
            intro j hj hand v
            cases hval : w C (fun i => decide (i = v)) (15 + j)
            · rfl
            · exact absurd ⟨j, hj, hand, v, hval⟩ hOneHot
          exact hDirtyNoOneHot C ⟨hmono, hFull⟩ hMinC hreads14 hNoOneHot hDirty
    · have hno14 : ∀ g ∈ C.gates, 14 ∉ g.inputs := fun g hg h14 => hreads14 ⟨g, hg, h14⟩
      have hout_ne14 : C.output ≠ 14 := by
        intro hout14
        let x0 : Fin 14 → Bool := fun i => decide (i = 0)
        have hnx0 : ¬ hasEdge x0 := by
          intro h
          obtain ⟨p, l, hadj, _, hl⟩ := h
          have hbip := hadj_bip p l hadj
          have hl0 : l = 0 := by simpa only [x0, decide_eq_true_eq] using hl
          subst hl0
          have : (0 : Fin 14).val = 0 := rfl
          omega
        have hev0 : C.eval (List.ofFn x0 ++ [x0 0 || x0 1]) = true := by
          change (run C.gates (List.ofFn x0 ++ [x0 0 || x0 1])).getD C.output false = true
          rw [hout14, run_keep C.gates _ 14 (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
          have h14 : (List.ofFn x0 ++ [x0 0 || x0 1]).getD 14 false = (x0 0 || x0 1) := by
            simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x0) (x0 0 || x0 1) false
          rw [h14]
          have hx00 : x0 0 = true := rfl
          rw [hx00]
          rfl
        exact hnx0 ((hFull x0).mp hev0)
      let drop14 : ℕ → ℕ := fun i => if i < 14 then i else i - 1
      have drop14_sim (gs : List Gate) (hgs : ∀ g ∈ gs, 14 ∉ g.inputs)
          (wA wB : List Bool) (hwA : 14 ≤ wA.length) (hwB : wB.length = wA.length + 1)
          (hrel : ∀ i, i ≠ 14 → wA.getD (drop14 i) false = wB.getD i false) :
          ∀ i, i ≠ 14 → (run (gs.map fun g => ⟨g.op, g.inputs.map drop14⟩) wA).getD (drop14 i) false =
            (run gs wB).getD i false := by
        induction gs generalizing wA wB with
        | nil => exact hrel
        | cons g rest ih =>
          simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
          have hg14 : 14 ∉ g.inputs := hgs g List.mem_cons_self
          have hinp : (g.inputs.map drop14).map (fun j => wA.getD j false) =
              g.inputs.map (fun i => wB.getD i false) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro i hi
            exact hrel i (fun h => hg14 (h ▸ hi))
          let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
          have hstepA : step wA ⟨g.op, g.inputs.map drop14⟩ = wA ++ [b] := by
            dsimp only [step, b]; rw [hinp]
          rw [hstepA]
          apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (wA ++ [b]) (step wB g)
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          · intro i hi14
            dsimp only [step]
            by_cases heq : i = wB.length
            · subst heq
              have hdr : drop14 wB.length = wA.length := by
                dsimp only [drop14]
                split
                · omega
                · omega
              rw [hdr, getD_snoc_eq wA b false, getD_snoc_eq wB b false]
            · have hdr_ne : drop14 i ≠ wA.length := by
                dsimp only [drop14]
                split
                · omega
                · omega
              rw [getD_snoc_ne wA b false (drop14 i) hdr_ne, getD_snoc_ne wB b false i heq]
              exact hrel i hi14
      let D : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map drop14⟩), drop14 C.output⟩
      have hDmono : Monotone2 D := by
        intro g hg
        simp only [D, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        have h := hmono g0 hg0
        exact ⟨h.1, by simp only [List.length_map]; exact h.2⟩
      have hDfull : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ hasEdge x := by
        intro x
        have hbase : ∀ i, i ≠ 14 →
            (List.ofFn x).getD (drop14 i) false = (List.ofFn x ++ [x 0 || x 1]).getD i false := by
          intro i hi14
          by_cases hi : i < 14
          · have hdr : drop14 i = i := by simp only [drop14, hi, ↓reduceIte]
            rw [hdr]
            exact (List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hi)).symm
          · have hdr : drop14 i = i - 1 := by simp only [drop14, hi, ↓reduceIte]
            rw [hdr,
                List.getD_eq_default (List.ofFn x) false (n := i - 1) (by simp only [List.length_ofFn]; omega),
                List.getD_eq_default (List.ofFn x ++ [x 0 || x 1]) false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
        have hev := drop14_sim C.gates hno14 (List.ofFn x) (List.ofFn x ++ [x 0 || x 1])
          (by simp only [List.length_ofFn]; omega)
          (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
          hbase C.output hout_ne14
        change (run D.gates (List.ofFn x)).getD (drop14 C.output) false = true ↔ hasEdge x
        rw [hev]
        exact hFull x
      have hcntD : cnt D = cnt C := by
        change List.countP _ (C.gates.map _) = List.countP _ C.gates
        rw [List.countP_map]
        rfl
      obtain ⟨D1, hokD1, hcntD1, hMinD1⟩ := hLexMin ok14 D ⟨hDmono, hDfull⟩
      have h19D : 19 ≤ cnt D1 := hNoExtra D1 hokD1 hMinD1
      omega
  exact Nat.le_trans h19C hcntLe
