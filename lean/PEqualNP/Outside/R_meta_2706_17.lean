import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_2706_17
    (hAndAnd :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w2 w3 : ℕ),
        PEqualNP.TopForm.IsAO2 14 D →
        D.size ≤ 25 →
        14 ≤ w2 →
        14 ≤ w3 →
        w2 ≠ w3 →
        PEqualNP.ReadTwo.isAnd D (w2 - 14) →
        PEqualNP.ReadTwo.isAnd D (w3 - 14) →
        have edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
        have H : (Fin 14 → Bool) → Prop := fun x => ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
        (∀ x : Fin 14 → Bool, H x ↔ (PEqualNP.ReadTwo.wval D x w2 = true ∨ PEqualNP.ReadTwo.wval D x w3 = true)) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w2 = true ∧ PEqualNP.ReadTwo.wval D x w3 = false) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w3 = true ∧ PEqualNP.ReadTwo.wval D x w2 = false) →
        PEqualNP.ReadTwo.wval D (fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7)) w2 = true →
        (¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
          (PEqualNP.ReadTwo.orp D 14 (14 + j) w2 ∨ PEqualNP.ReadTwo.orp D 14 (14 + j) w3) ∧
          PEqualNP.ReadTwo.orp D 14 0 a ∧ PEqualNP.ReadTwo.orp D 14 7 b) →
        False)
    (hAndOr :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w2 w3 : ℕ),
        PEqualNP.TopForm.IsAO2 14 D →
        D.size ≤ 25 →
        14 ≤ w2 →
        14 ≤ w3 →
        w2 ≠ w3 →
        PEqualNP.ReadTwo.isAnd D (w2 - 14) →
        PEqualNP.ReadTwo.isOr D (w3 - 14) →
        have edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
        have H : (Fin 14 → Bool) → Prop := fun x => ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
        (∀ x : Fin 14 → Bool, H x ↔ (PEqualNP.ReadTwo.wval D x w2 = true ∨ PEqualNP.ReadTwo.wval D x w3 = true)) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w2 = true ∧ PEqualNP.ReadTwo.wval D x w3 = false) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w3 = true ∧ PEqualNP.ReadTwo.wval D x w2 = false) →
        PEqualNP.ReadTwo.wval D (fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7)) w2 = true →
        (¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
          (PEqualNP.ReadTwo.orp D 14 (14 + j) w2 ∨ PEqualNP.ReadTwo.orp D 14 (14 + j) w3) ∧
          PEqualNP.ReadTwo.orp D 14 0 a ∧ PEqualNP.ReadTwo.orp D 14 7 b) →
        False)
    (hOrAnd :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w2 w3 : ℕ),
        PEqualNP.TopForm.IsAO2 14 D →
        D.size ≤ 25 →
        14 ≤ w2 →
        14 ≤ w3 →
        w2 ≠ w3 →
        PEqualNP.ReadTwo.isOr D (w2 - 14) →
        PEqualNP.ReadTwo.isAnd D (w3 - 14) →
        have edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
        have H : (Fin 14 → Bool) → Prop := fun x => ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
        (∀ x : Fin 14 → Bool, H x ↔ (PEqualNP.ReadTwo.wval D x w2 = true ∨ PEqualNP.ReadTwo.wval D x w3 = true)) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w2 = true ∧ PEqualNP.ReadTwo.wval D x w3 = false) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w3 = true ∧ PEqualNP.ReadTwo.wval D x w2 = false) →
        PEqualNP.ReadTwo.wval D (fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7)) w2 = true →
        (¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
          (PEqualNP.ReadTwo.orp D 14 (14 + j) w2 ∨ PEqualNP.ReadTwo.orp D 14 (14 + j) w3) ∧
          PEqualNP.ReadTwo.orp D 14 0 a ∧ PEqualNP.ReadTwo.orp D 14 7 b) →
        False)
    (hOrOr :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w2 w3 : ℕ),
        PEqualNP.TopForm.IsAO2 14 D →
        D.size ≤ 25 →
        14 ≤ w2 →
        14 ≤ w3 →
        w2 ≠ w3 →
        PEqualNP.ReadTwo.isOr D (w2 - 14) →
        PEqualNP.ReadTwo.isOr D (w3 - 14) →
        have edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
        have H : (Fin 14 → Bool) → Prop := fun x => ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
        (∀ x : Fin 14 → Bool, H x ↔ (PEqualNP.ReadTwo.wval D x w2 = true ∨ PEqualNP.ReadTwo.wval D x w3 = true)) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w2 = true ∧ PEqualNP.ReadTwo.wval D x w3 = false) →
        (∃ x : Fin 14 → Bool, PEqualNP.ReadTwo.wval D x w3 = true ∧ PEqualNP.ReadTwo.wval D x w2 = false) →
        PEqualNP.ReadTwo.wval D (fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7)) w2 = true →
        (¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
          (PEqualNP.ReadTwo.orp D 14 (14 + j) w2 ∨ PEqualNP.ReadTwo.orp D 14 (14 + j) w3) ∧
          PEqualNP.ReadTwo.orp D 14 0 a ∧ PEqualNP.ReadTwo.orp D 14 7 b) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) → (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) → (26 : ℕ) ≤ x1.size := by
  let edges : List (ℕ × ℕ) :=
    [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
     (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
     (6, 8), (6, 9), (6, 11)]
  let I : Fin 7 → Fin 7 → Prop := fun p l => (p.val, 7 + l.val) ∈ edges
  have hedges_bounds : ∀ e ∈ edges, e.1 < 7 ∧ 7 ≤ e.2 ∧ e.2 < 14 := by decide
  have hNoC4_b : ∀ (p1 p2 l1 l2 : Fin 7), p1 ≠ p2 → l1 ≠ l2 →
      !(edges.contains (p1.val, 7 + l1.val) && edges.contains (p1.val, 7 + l2.val) &&
        edges.contains (p2.val, 7 + l1.val) && edges.contains (p2.val, 7 + l2.val)) = true := by decide
  have hNoC4 : ∀ (p1 p2 l1 l2 : Fin 7), p1 ≠ p2 → l1 ≠ l2 →
      ¬ (I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
    rintro p1 p2 l1 l2 hp hl ⟨h1, h2, h3, h4⟩
    have hb := hNoC4_b p1 p2 l1 l2 hp hl
    have c1 : edges.contains (p1.val, 7 + l1.val) = true := List.contains_iff_mem.mpr h1
    have c2 : edges.contains (p1.val, 7 + l2.val) = true := List.contains_iff_mem.mpr h2
    have c3 : edges.contains (p2.val, 7 + l1.val) = true := List.contains_iff_mem.mpr h3
    have c4 : edges.contains (p2.val, 7 + l2.val) = true := List.contains_iff_mem.mpr h4
    rw [c1, c2, c3, c4] at hb
    cases hb
  have hI_card : (Finset.univ.filter fun e : Fin 7 × Fin 7 => I e.1 e.2).card = 21 := by decide
  let matchL : Fin 7 → Fin 7 := fun p => ([0, 2, 1, 5, 6, 3, 4] : List (Fin 7)).getD p.val p
  have hmatch_I : ∀ p : Fin 7, I p (matchL p) := by decide
  have hmatch_inj : ∀ p1 p2 : Fin 7, matchL p1 = matchL p2 → p1 = p2 := by decide
  let autTable : List ((ℕ × ℕ) × List ℕ × List ℕ) := [
    ((0, 7), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
    ((0, 8), [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13], [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]),
    ((0, 10), [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13], [0, 4, 1, 5, 2, 6, 3, 10, 7, 11, 8, 12, 9, 13]),
    ((1, 7), [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8], [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8]),
    ((1, 9), [2, 0, 4, 6, 5, 3, 1, 8, 13, 7, 12, 9, 11, 10], [1, 6, 0, 5, 2, 4, 3, 9, 7, 11, 13, 12, 10, 8]),
    ((1, 13), [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7], [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8]),
    ((2, 8), [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8], [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7]),
    ((2, 12), [2, 4, 0, 1, 5, 3, 6, 13, 8, 11, 12, 9, 7, 10], [2, 3, 0, 5, 1, 4, 6, 12, 8, 11, 13, 9, 10, 7]),
    ((2, 13), [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7], [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7]),
    ((3, 7), [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12], [3, 0, 2, 1, 6, 4, 5, 7, 12, 10, 11, 9, 13, 8]),
    ((3, 11), [2, 6, 4, 0, 3, 5, 1, 8, 13, 9, 12, 7, 10, 11], [3, 6, 0, 4, 2, 5, 1, 11, 7, 9, 12, 13, 10, 8]),
    ((3, 12), [2, 6, 1, 0, 5, 3, 4, 8, 13, 11, 12, 10, 7, 9], [3, 2, 0, 5, 6, 4, 1, 12, 7, 13, 11, 9, 10, 8]),
    ((4, 10), [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8], [4, 0, 1, 5, 3, 6, 2, 10, 13, 8, 11, 12, 9, 7]),
    ((4, 11), [2, 4, 5, 1, 0, 6, 3, 13, 12, 11, 8, 7, 9, 10], [4, 3, 0, 6, 1, 2, 5, 11, 10, 12, 13, 9, 8, 7]),
    ((4, 13), [2, 1, 3, 4, 0, 6, 5, 13, 12, 9, 8, 10, 11, 7], [4, 1, 0, 2, 3, 6, 5, 13, 10, 9, 11, 12, 8, 7]),
    ((5, 9), [2, 1, 5, 4, 6, 0, 3, 13, 12, 7, 8, 11, 10, 9], [5, 1, 0, 6, 3, 2, 4, 9, 10, 13, 12, 11, 8, 7]),
    ((5, 10), [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12], [5, 0, 1, 4, 3, 2, 6, 10, 9, 8, 12, 11, 13, 7]),
    ((5, 12), [2, 4, 3, 1, 6, 0, 5, 13, 12, 10, 8, 9, 7, 11], [5, 3, 0, 2, 1, 6, 4, 12, 10, 11, 9, 13, 8, 7]),
    ((6, 8), [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12], [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7]),
    ((6, 9), [2, 1, 6, 4, 5, 3, 0, 13, 8, 7, 12, 10, 11, 9], [6, 1, 0, 5, 3, 4, 2, 9, 8, 13, 11, 12, 10, 7]),
    ((6, 11), [2, 4, 6, 1, 3, 5, 0, 13, 8, 10, 12, 7, 9, 11], [6, 3, 0, 4, 1, 5, 2, 11, 8, 12, 9, 13, 10, 7])
  ]
  have haut_cov : ∀ e ∈ edges, ∃ t ∈ autTable, t.1 = e := by decide
  have haut_ok : ∀ t ∈ autTable,
      t.2.1.length = 14 ∧ t.2.2.length = 14 ∧
      (∀ i : Fin 14, t.2.1.getD i.val 14 < 14 ∧ t.2.2.getD i.val 14 < 14) ∧
      (∀ i : Fin 14, t.2.2.getD (t.2.1.getD i.val 14) 14 = i.val ∧
                     t.2.1.getD (t.2.2.getD i.val 14) 14 = i.val) ∧
      t.2.1.getD t.1.1 14 = 0 ∧ t.2.1.getD t.1.2 14 = 7 ∧
      (∀ ab ∈ edges, (t.2.1.getD ab.1 14, t.2.1.getD ab.2 14) ∈ edges) ∧
      (∀ ab ∈ edges, (t.2.2.getD ab.1 14, t.2.2.getD ab.2 14) ∈ edges) := by decide
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      rw [ih (step w g)]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_keep (gs : List Gate) (w : List Bool) :
      ∀ i < w.length, (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => intro i _; rfl
    | cons g rest ih =>
      intro i hi
      simp only [run, List.foldl_cons] at ih ⊢
      have hi' : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step w g) i hi']
      exact List.getD_append _ _ _ _ hi
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l d (n := j) (by omega)]
  let sval : List Bool → Bool ⊕ ℕ → Bool := fun w => Sum.elim id (fun i => w.getD i false)
  let svalid : ℕ → Bool ⊕ ℕ → Prop := fun m => Sum.elim (fun _ => True) (fun i => i < m)
  let simpAnd : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.casesOn ins (none, Sum.inl true) (fun a rest =>
      List.casesOn rest (none, a) (fun b _ =>
        Sum.elim
          (fun ba => if ba then (none, b) else (none, Sum.inl false))
          (fun ia => Sum.elim
            (fun bb => if bb then (none, Sum.inr ia) else (none, Sum.inl false))
            (fun ib => (some (Gate.mk GateOp.and [ia, ib]), Sum.inr m))
            b)
          a))
  let simpOr : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.casesOn ins (none, Sum.inl false) (fun a rest =>
      List.casesOn rest (none, a) (fun b _ =>
        Sum.elim
          (fun ba => if ba then (none, Sum.inl true) else (none, b))
          (fun ia => Sum.elim
            (fun bb => if bb then (none, Sum.inl true) else (none, Sum.inr ia))
            (fun ib => (some (Gate.mk GateOp.or [ia, ib]), Sum.inr m))
            b)
          a))
  let simplify : GateOp → ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun op m ins =>
    GateOp.rec (simpAnd m ins) (simpOr m ins) (none, Sum.inl false) (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op
  have simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
      (hv : ∀ s ∈ ins, svalid m s) :
      ∀ g ∈ (simplify op m ins).1.toList,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m := by
    cases op with
    | and =>
      cases ins with
      | nil => intro g hg; cases hg
      | cons a t =>
        cases t with
        | nil => intro g hg; cases hg
        | cons b t2 =>
          cases a with
          | inl ba => cases ba <;> (intro g hg; cases hg)
          | inr ia =>
            cases b with
            | inl bb => cases bb <;> (intro g hg; cases hg)
            | inr ib =>
              intro g hg
              change g ∈ [Gate.mk GateOp.and [ia, ib]] at hg
              rw [List.mem_singleton] at hg
              subst hg
              have hia : ia < m := hv (Sum.inr ia) List.mem_cons_self
              have hib : ib < m := hv (Sum.inr ib) (List.mem_cons_of_mem _ List.mem_cons_self)
              refine ⟨Or.inl rfl, rfl, ?_⟩
              intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> assumption
    | or =>
      cases ins with
      | nil => intro g hg; cases hg
      | cons a t =>
        cases t with
        | nil => intro g hg; cases hg
        | cons b t2 =>
          cases a with
          | inl ba => cases ba <;> (intro g hg; cases hg)
          | inr ia =>
            cases b with
            | inl bb => cases bb <;> (intro g hg; cases hg)
            | inr ib =>
              intro g hg
              change g ∈ [Gate.mk GateOp.or [ia, ib]] at hg
              rw [List.mem_singleton] at hg
              subst hg
              have hia : ia < m := hv (Sum.inr ia) List.mem_cons_self
              have hib : ib < m := hv (Sum.inr ib) (List.mem_cons_of_mem _ List.mem_cons_self)
              refine ⟨Or.inr rfl, rfl, ?_⟩
              intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> assumption
    | not => intro g hg; cases hg
    | mod _ => intro g hg; cases hg
    | maj => intro g hg; cases hg
  have simplify_sound (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, svalid w.length s) :
      svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      sval (run (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
        op.eval (ins.map (sval w)) := by
    rcases hop with rfl | rfl
    · cases ins with
      | nil => exact ⟨trivial, rfl⟩
      | cons a t =>
        cases t with
        | nil =>
          have ha := hv a (by simp only [List.mem_cons, true_or])
          refine ⟨by simpa only [simplify, simpAnd, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
          change sval w a = (sval w a && true)
          exact (Bool.and_true _).symm
        | cons b t2 =>
          cases t2 with
          | cons _ _ => simp only [List.length_cons] at hlen; omega
          | nil =>
            have ha := hv a (by simp only [List.mem_cons, true_or])
            have hb := hv b (by simp only [List.mem_cons, true_or, or_true])
            cases a with
            | inl ba =>
              cases ba with
              | true =>
                refine ⟨by simpa only [simplify, simpAnd, Sum.elim_inl, ite_true, Option.toList_none, List.length_nil, Nat.add_zero] using hb, ?_⟩
                change sval w b = (true && (sval w b && true))
                cases sval w b <;> rfl
              | false =>
                refine ⟨trivial, ?_⟩
                change false = (false && (sval w b && true))
                rfl
            | inr ia =>
              cases b with
              | inl bb =>
                cases bb with
                | true =>
                  refine ⟨by simpa only [simplify, simpAnd, Sum.elim_inr, Sum.elim_inl, ite_true, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
                  change w.getD ia false = (w.getD ia false && (true && true))
                  cases w.getD ia false <;> rfl
                | false =>
                  refine ⟨trivial, ?_⟩
                  change false = (w.getD ia false && (false && true))
                  cases w.getD ia false <;> rfl
              | inr ib =>
                refine ⟨show w.length < w.length + 1 by omega, ?_⟩
                change (w ++ [(w.getD ia false && (w.getD ib false && true))]).getD w.length false =
                  (w.getD ia false && (w.getD ib false && true))
                exact getD_snoc_eq w _ false
    · cases ins with
      | nil => exact ⟨trivial, rfl⟩
      | cons a t =>
        cases t with
        | nil =>
          have ha := hv a (by simp only [List.mem_cons, true_or])
          refine ⟨by simpa only [simplify, simpOr, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
          change sval w a = (sval w a || false)
          exact (Bool.or_false _).symm
        | cons b t2 =>
          cases t2 with
          | cons _ _ => simp only [List.length_cons] at hlen; omega
          | nil =>
            have ha := hv a (by simp only [List.mem_cons, true_or])
            have hb := hv b (by simp only [List.mem_cons, true_or, or_true])
            cases a with
            | inl ba =>
              cases ba with
              | true =>
                refine ⟨trivial, ?_⟩
                change true = (true || (sval w b || false))
                rfl
              | false =>
                refine ⟨by simpa only [simplify, simpOr, Sum.elim_inl, Bool.false_eq_true, ite_false, Option.toList_none, List.length_nil, Nat.add_zero] using hb, ?_⟩
                change sval w b = (false || (sval w b || false))
                cases sval w b <;> rfl
            | inr ia =>
              cases b with
              | inl bb =>
                cases bb with
                | true =>
                  refine ⟨trivial, ?_⟩
                  change true = (w.getD ia false || (true || false))
                  cases w.getD ia false <;> rfl
                | false =>
                  refine ⟨by simpa only [simplify, simpOr, Sum.elim_inr, Sum.elim_inl, Bool.false_eq_true, ite_false, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
                  change w.getD ia false = (w.getD ia false || (false || false))
                  cases w.getD ia false <;> rfl
              | inr ib =>
                refine ⟨show w.length < w.length + 1 by omega, ?_⟩
                change (w ++ [(w.getD ia false || (w.getD ib false || false))]).getD w.length false =
                  (w.getD ia false || (w.getD ib false || false))
                exact getD_snoc_eq w _ false
  let elimStep : List (Bool ⊕ ℕ) × List Gate → Gate → List (Bool ⊕ ℕ) × List Gate := fun acc g =>
    let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
    let r := simplify g.op (14 + acc.2.length) ins
    (acc.1 ++ [r.2], acc.2 ++ r.1.toList)
  let elim : List Gate → List (Bool ⊕ ℕ) × List Gate → List (Bool ⊕ ℕ) × List Gate := fun gs acc =>
    gs.foldl elimStep acc
  have elim_len (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
      (elim gs acc).2.length ≤ acc.2.length + gs.length := by
    induction gs generalizing acc with
    | nil => simp only [elim, List.foldl_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    | cons g rest ih =>
      simp only [elim, List.foldl_cons] at ih ⊢
      have h1 := ih (elimStep acc g)
      have h2 : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
        dsimp only [elimStep]
        rw [List.length_append]
        cases (simplify g.op (14 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
          simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
      simp only [List.length_cons]
      omega
  let Inv : List Bool → List Bool → List (Bool ⊕ ℕ) × List Gate → Prop := fun w z acc =>
    w.length = 14 ∧ acc.1.length = z.length ∧
    (∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    (∀ j < acc.2.length, ∀ i ∈ (acc.2.getD j ⟨GateOp.or, []⟩).inputs, i < 14 + j) ∧
    ∀ i, svalid (14 + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
         sval (run acc.2 w) (acc.1.getD i (Sum.inl false)) = z.getD i false
  have elim_inv (gs : List Gate) (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (hinv : Inv w z acc) : Inv w (run gs z) (elim gs acc) := by
    induction gs generalizing z acc with
    | nil => exact hinv
    | cons g rest ih =>
      simp only [run, elim, List.foldl_cons] at ih ⊢
      apply ih (step z g) (elimStep acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      obtain ⟨hwl, hml, hok2, hrb2, hmap⟩ := hinv
      have hg := hgs g List.mem_cons_self
      let w' := run acc.2 w
      have hw'len : w'.length = 14 + acc.2.length := by
        dsimp only [w']; rw [run_len, hwl]
      let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
      let r := simplify g.op w'.length ins
      have hins_len : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact hg.2
      have hins_v : ∀ s ∈ ins, svalid w'.length s := by
        intro s hs
        simp only [ins, List.mem_map] at hs
        obtain ⟨i, _, rfl⟩ := hs
        rw [hw'len]; exact (hmap i).1
      have hrs := simplify_sound g.op hg.1 w' ins hins_len hins_v
      have hrok := simplify_ok g.op w'.length ins hins_v
      have hvals : ins.map (sval w') = g.inputs.map (fun i => z.getD i false) := by
        dsimp only [ins]
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact (hmap i).2
      have hstep_run : run (acc.2 ++ r.1.toList) w = run r.1.toList w' := by
        dsimp only [run, w']; exact List.foldl_append
      have heq_r : simplify g.op (14 + acc.2.length) ins = r := by rw [← hw'len]
      refine ⟨hwl, ?_, ?_, ?_, ?_⟩
      · simp only [elimStep, step, List.length_append, hml, List.length_cons, List.length_nil]
      · intro g' hg'
        dsimp only [elimStep] at hg'
        change g' ∈ acc.2 ++ (simplify g.op (14 + acc.2.length) ins).1.toList at hg'
        rw [heq_r, List.mem_append] at hg'
        rcases hg' with h1 | h2
        · exact hok2 g' h1
        · exact ⟨(hrok g' h2).1, (hrok g' h2).2.1⟩
      · intro j hj u hu
        dsimp only [elimStep] at hj hu
        change j < (acc.2 ++ (simplify g.op (14 + acc.2.length) ins).1.toList).length at hj
        change u ∈ ((acc.2 ++ (simplify g.op (14 + acc.2.length) ins).1.toList).getD j ⟨GateOp.or, []⟩).inputs at hu
        rw [heq_r] at hj hu
        by_cases hjlt : j < acc.2.length
        · rw [List.getD_append _ _ _ _ hjlt] at hu
          exact hrb2 j hjlt u hu
        · cases hr1 : r.1 with
          | none =>
            rw [hr1, Option.toList_none, List.append_nil] at hj
            omega
          | some gn =>
            rw [hr1, Option.toList_some] at hj hu
            have hjeq : j = acc.2.length := by
              simp only [List.length_append, List.length_cons, List.length_nil] at hj
              omega
            subst hjeq
            rw [getD_snoc_eq acc.2 gn ⟨GateOp.or, []⟩] at hu
            have hgn : gn ∈ r.1.toList := by rw [hr1]; exact List.mem_singleton_self gn
            have hlt := (hrok gn hgn).2.2 u hu
            omega
      · intro i
        dsimp only [elimStep]
        change svalid (14 + (acc.2 ++ (simplify g.op (14 + acc.2.length) ins).1.toList).length)
            ((acc.1 ++ [(simplify g.op (14 + acc.2.length) ins).2]).getD i (Sum.inl false)) ∧
          sval (run (acc.2 ++ (simplify g.op (14 + acc.2.length) ins).1.toList) w)
            ((acc.1 ++ [(simplify g.op (14 + acc.2.length) ins).2]).getD i (Sum.inl false)) =
          (z ++ [g.op.eval (g.inputs.map fun j => z.getD j false)]).getD i false
        rw [heq_r, hstep_run, List.length_append, ← Nat.add_assoc, ← hw'len]
        by_cases hi : i = acc.1.length
        · subst hi
          rw [getD_snoc_eq acc.1 r.2 (Sum.inl false), hml, getD_snoc_eq z _ false]
          exact ⟨hrs.1, hrs.2.trans (congrArg g.op.eval hvals)⟩
        · have hi' : i ≠ z.length := by rw [← hml]; exact hi
          rw [getD_snoc_ne acc.1 r.2 (Sum.inl false) i hi, getD_snoc_ne z _ false i hi']
          have hmi := hmap i
          rw [← hw'len] at hmi
          cases hsi : acc.1.getD i (Sum.inl false) with
          | inl b =>
            rw [hsi] at hmi
            exact ⟨trivial, hmi.2⟩
          | inr idx =>
            rw [hsi] at hmi
            have hidx_lt : idx < w'.length := hmi.1
            refine ⟨show idx < w'.length + r.1.toList.length by omega, ?_⟩
            change (run r.1.toList w').getD idx false = z.getD i false
            rw [run_keep r.1.toList w' idx hidx_lt]
            exact hmi.2
  have hstar_bound : ∀ (C : Circuit), IsAO2 14 C →
      (∀ x : Fin 14 → Bool, circuitFun 14 C x =
        decide (∃ (p l : Fin 7), I p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      (∀ (p l : Fin 7), I p l →
        ∃ (j a b : ℕ), andOn C j a b ∧
          orp C 14 (14 + j) C.output ∧
          orp C 14 p.val a ∧
          orp C 14 (7 + l.val) b) →
      28 ≤ C.size + 1 := by
    classical
    intro C hAO2 hComp hall
    let N : ℕ := 14
    let E : Finset (Fin 7 × Fin 7) := Finset.univ.filter (fun e => I e.1 e.2)
    have hmem_E (p l : Fin 7) : (p, l) ∈ E ↔ I p l := by
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    have hE_card : E.card = 21 := by
      convert hI_card
    have hRB : ReadsBack 14 C := hAO2.2.1
    let OrPath : ℕ → ℕ → Prop := fun w target =>
      ∀ Q : ℕ → Prop,
        Q target →
        (∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
          ∀ a ∈ (gateAt C k).inputs, Q a → Q (N + k)) →
        Q w
    have orPath_refl (t : ℕ) : OrPath t t := fun _ h _ => h
    have orPath_step {k a t : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
        (ha : a ∈ (gateAt C k).inputs) (hp : OrPath a t) : OrPath (N + k) t :=
      fun Q ht hs => hs k hk hor a ha (hp Q ht hs)
    have orPath_trans {u v w : ℕ} (huv : OrPath u v) (hvw : OrPath v w) : OrPath u w :=
      fun Q hw hs => huv Q (hvw Q hw hs) hs
    have orPath_cases {w t : ℕ} (h : OrPath w t) :
        w = t ∨ ∃ k < C.gates.length, w = N + k ∧ (gateAt C k).op = GateOp.or ∧
          ∃ a ∈ (gateAt C k).inputs, OrPath a t := by
      apply h (fun x => x = t ∨ ∃ k < C.gates.length, x = N + k ∧ (gateAt C k).op = GateOp.or ∧
          ∃ a ∈ (gateAt C k).inputs, OrPath a t)
      · exact Or.inl rfl
      · intro k hk hor a ha hPa
        refine Or.inr ⟨k, hk, rfl, hor, a, ha, ?_⟩
        rcases hPa with rfl | ⟨k', hk', rfl, hor', a', ha', hp'⟩
        · exact orPath_refl _
        · exact orPath_step hk' hor' ha' hp'
    have orPath_parent {w t : ℕ} (h : OrPath w t) (hne : w ≠ t) :
        ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
          OrPath w (N + y) ∧ t ∈ (gateAt C y).inputs := by
      have hdisj : w = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
          OrPath w (N + y) ∧ t ∈ (gateAt C y).inputs := by
        apply h (fun x => x = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
            OrPath x (N + y) ∧ t ∈ (gateAt C y).inputs)
        · exact Or.inl rfl
        · intro k hk hor a ha hPa
          rcases hPa with rfl | ⟨y, hy, hory, hpy, hty⟩
          · exact Or.inr ⟨k, hk, hor, orPath_refl (N + k), ha⟩
          · exact Or.inr ⟨y, hy, hory, orPath_step hk hor ha hpy, hty⟩
      rcases hdisj with heq | hex
      · exact (hne heq).elim
      · exact hex
    have orp_to_orPath {t w : ℕ} (h : orp C N t w) : OrPath w t := by
      change Relation.ReflTransGen (fun a b => a < b ∧ ∃ j, b = N + j ∧ isOr C j ∧ a ∈ (gateAt C j).inputs) t w at h
      induction h with
      | refl => exact orPath_refl t
      | tail _ hstep ih =>
        obtain ⟨_, j, rfl, ⟨hj, hor⟩, ha⟩ := hstep
        exact orPath_step hj hor ha ih
    have wireVal_input (i : Fin N) (x : Fin N → Bool) :
        wireVal N C i.val x = x i := by
      change (run C.gates (List.ofFn x)).getD i.val false = x i
      rw [run_keep C.gates (List.ofFn x) i.val (by simp only [List.length_ofFn]; exact i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
    have wireVal_gate (k : ℕ) (hk : k < C.gates.length) (x : Fin N → Bool) :
        wireVal N C (N + k) x =
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wireVal N C i x) := by
      change (run C.gates (List.ofFn x)).getD (N + k) false =
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
          (run C.gates (List.ofFn x)).getD i false)
      have hsplit : C.gates = C.gates.take k ++ [gateAt C k] ++ C.gates.drop (k + 1) := by
        have h1 : C.gates = C.gates.take (k + 1) ++ C.gates.drop (k + 1) :=
          (List.take_append_drop (k + 1) C.gates).symm
        conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hk]
        rfl
      let w0 := run (C.gates.take k) (List.ofFn x)
      have hw0_len : w0.length = N + k := by
        dsimp only [w0]
        rw [run_len, List.length_ofFn, List.length_take]
        omega
      have hw_lt : ∀ i < N + k, (run C.gates (List.ofFn x)).getD i false = w0.getD i false := by
        intro i hi
        change (C.gates.foldl step (List.ofFn x)).getD i false = w0.getD i false
        conv_lhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
        exact run_keep (C.gates.drop k) w0 i (by omega)
      change (C.gates.foldl step (List.ofFn x)).getD (N + k) false = _
      conv_lhs => rw [hsplit, List.foldl_append, List.foldl_append]
      have hstep_len : (run [gateAt C k] w0).length = N + k + 1 := by
        rw [run_len]; simp only [List.length_cons, List.length_nil]; omega
      rw [run_keep (C.gates.drop (k + 1)) (run [gateAt C k] w0) (N + k) (by omega)]
      simp only [run, List.foldl_cons, List.foldl_nil, step]
      rw [← hw0_len, getD_snoc_eq w0 _ false]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (hw_lt i (hRB k hk i hi)).symm
    have wireVal_or_mem {k a : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
        (ha : a ∈ (gateAt C k).inputs) (x : Fin N → Bool)
        (hva : wireVal N C a x = true) :
        wireVal N C (N + k) x = true := by
      rw [wireVal_gate k hk x, hor]
      change ((gateAt C k).inputs.map fun i => wireVal N C i x).any id = true
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩
    have wireVal_and_pair {k a b : ℕ} (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and)
        (hin : (gateAt C k).inputs = [a, b]) (x : Fin N → Bool) :
        wireVal N C (N + k) x = (wireVal N C a x && wireVal N C b x) := by
      rw [wireVal_gate k hk x, hand, hin]
      change [wireVal N C a x, wireVal N C b x].all id = (wireVal N C a x && wireVal N C b x)
      simp
    have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin N → Bool)
        (ht : wireVal N C t x = true) : wireVal N C w x = true := by
      apply hp (fun u => wireVal N C u x = true) ht
      intro k hk hor a ha hva
      exact wireVal_or_mem hk hor ha x hva
    have isAO2_gate_inputs {k : ℕ} (hk : k < C.gates.length) :
        ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a < N + k ∧ b < N + k := by
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
        (wireOf : X → ℕ) (hwire_lt : ∀ x : X, wireOf x < N)
        (hwire_inj : Function.Injective wireOf)
        (S_gates : Finset (Fin C.gates.length))
        (opWire : Fin C.gates.length → ℕ)
        (hnonempty : ∀ j ∈ S_gates, ∃ x : X, OrPath (opWire j) (wireOf x)) :
        let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
        let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
        let O_S : Finset (Fin C.gates.length) :=
          Finset.univ.filter (fun o =>
            (gateAt C o.val).op = GateOp.or ∧
            2 ≤ (reach (N + o.val)).card ∧
            ∃ j ∈ S_gates, OrPath (opWire j) (N + o.val))
        E_S.card ≤ O_S.card + S_gates.card := by
      let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
      let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
      let O_S : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun o =>
          (gateAt C o.val).op = GateOp.or ∧
          2 ≤ (reach (N + o.val)).card ∧
          ∃ j ∈ S_gates, OrPath (opWire j) (N + o.val))
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
            have hstep_ex : ∃ k < C.gates.length, w = N + k ∧ (gateAt C k).op = GateOp.or := by
              rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
              · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
                · exact (hne_w h2).elim
                · exact ⟨k, hk, hwk, hor⟩
              · exact ⟨k, hk, hwk, hor⟩
            obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
            let o : Fin C.gates.length := ⟨k, hk⟩
            have h2card : 2 ≤ (reach (N + o.val)).card := by
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
              have hlt_x : wireOf x < N := hwire_lt x
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
    let pts (w : ℕ) : Finset (Fin 7) := Finset.univ.filter (fun p => OrPath w p.val)
    let lns (w : ℕ) : Finset (Fin 7) := Finset.univ.filter (fun l => OrPath w (7 + l.val))
    have hComp_wire (x : Fin N → Bool) :
        wireVal N C C.output x =
          decide (∃ (p l : Fin 7), (p, l) ∈ E ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) := by
      have h := hComp x
      change wireVal N C C.output x = _ at h
      rw [h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, hmem_E]
    have hno_pts_only (x : Fin N → Bool) (h0 : ∀ l : Fin 7, x (Fin.natAdd 7 l) = false) :
        wireVal N C C.output x = false := by
      rw [hComp_wire, decide_eq_false_iff_not]
      rintro ⟨p, l, _, _, hl⟩
      rw [h0 l] at hl; cases hl
    have hno_lns_only (x : Fin N → Bool) (h0 : ∀ p : Fin 7, x (Fin.castAdd 7 p) = false) :
        wireVal N C C.output x = false := by
      rw [hComp_wire, decide_eq_false_iff_not]
      rintro ⟨p, l, _, hp, _⟩
      rw [h0 p] at hp; cases hp
    have hedge_covered : ∀ p l : Fin 7, (p, l) ∈ E →
        ∃ j : Fin C.gates.length, (gateAt C j.val).op = GateOp.and ∧
          OrPath C.output (N + j.val) ∧
          ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
            ((OrPath a p.val ∧ OrPath b (7 + l.val)) ∨
             (OrPath a (7 + l.val) ∧ OrPath b p.val)) := by
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
        OrPath C.output (N + j.val) ∧
        ∃ p l : Fin 7, ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
          ((OrPath a p.val ∧ OrPath b (7 + l.val)) ∨
           (OrPath a (7 + l.val) ∧ OrPath b p.val)))
    let pWire (j : Fin C.gates.length) : ℕ :=
      let a := (gateAt C j.val).inputs.getD 0 0
      let b := (gateAt C j.val).inputs.getD 1 0
      if (pts a).Nonempty then a else b
    let lWire (j : Fin C.gates.length) : ℕ :=
      let a := (gateAt C j.val).inputs.getD 0 0
      let b := (gateAt C j.val).inputs.getD 1 0
      if (pts a).Nonempty then b else a
    let pSide (j : Fin C.gates.length) : Finset (Fin 7) := pts (pWire j)
    let lSide (j : Fin C.gates.length) : Finset (Fin 7) := lns (lWire j)
    have hTstar_props : ∀ j ∈ Tstar,
        (gateAt C j.val).op = GateOp.and ∧
        OrPath C.output (N + j.val) ∧
        (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
        lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
        (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) ∧
        ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
      intro j hj
      obtain ⟨hand, htop, p0, l0, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
      have ha_get : (gateAt C j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt C j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
      have hand_sound : ∀ x : Fin N → Bool,
          wireVal N C a x = true → wireVal N C b x = true → wireVal N C C.output x = true := by
        intro x hxa hxb
        apply orPath_sound htop x
        rw [wireVal_and_pair j.isLt hand hab x, hxa, hxb]
        rfl
      have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
        rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
        let x : Fin N → Bool := fun i => decide (i = Fin.castAdd 7 p1 ∨ i = Fin.castAdd 7 p2)
        have h1 : wireVal N C p1.val x = true := by
          have := wireVal_input (Fin.castAdd 7 p1) x; simpa [x] using this
        have h2 : wireVal N C p2.val x = true := by
          have := wireVal_input (Fin.castAdd 7 p2) x; simpa [x] using this
        have ht := hand_sound x
          (orPath_sound (Finset.mem_filter.mp hp1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hp2).2 x h2)
        have hf := hno_pts_only x (fun l => by
          simp only [x, decide_eq_false_iff_not]
          rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
        rw [ht] at hf; cases hf
      have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
        rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
        let x : Fin N → Bool := fun i => decide (i = Fin.natAdd 7 l1 ∨ i = Fin.natAdd 7 l2)
        have h1 : wireVal N C (7 + l1.val) x = true := by
          have := wireVal_input (Fin.natAdd 7 l1) x; simpa [x, Nat.add_comm] using this
        have h2 : wireVal N C (7 + l2.val) x = true := by
          have := wireVal_input (Fin.natAdd 7 l2) x; simpa [x, Nat.add_comm] using this
        have ht := hand_sound x
          (orPath_sound (Finset.mem_filter.mp hl1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hl2).2 x h2)
        have hf := hno_lns_only x (fun p => by
          simp only [x, decide_eq_false_iff_not]
          rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
        rw [ht] at hf; cases hf
      have hbiclique : ∀ (p l : Fin 7),
          ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → (p, l) ∈ E := by
        intro p l hpl
        let x : Fin N → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
        have hxp : wireVal N C p.val x = true := by
          have := wireVal_input (Fin.castAdd 7 p) x; simpa [x] using this
        have hxl : wireVal N C (7 + l.val) x = true := by
          have := wireVal_input (Fin.natAdd 7 l) x; simpa [x, Nat.add_comm] using this
        have hout_t : wireVal N C C.output x = true := by
          rcases hpl with ⟨hpa, hlb⟩ | ⟨hpb, hla⟩
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hpa).2 x hxp)
              (orPath_sound (Finset.mem_filter.mp hlb).2 x hxl)
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hla).2 x hxl)
              (orPath_sound (Finset.mem_filter.mp hpb).2 x hxp)
        rw [hComp_wire, decide_eq_true_eq] at hout_t
        obtain ⟨p', l', hp'l', hxp', hxl'⟩ := hout_t
        simp only [x, decide_eq_true_eq] at hxp' hxl'
        have hp_eq : p' = p := by
          rcases hxp' with h1 | h2
          · exact Fin.ext (by simpa using congrArg Fin.val h1)
          · have := congrArg Fin.val h2; simp at this; omega
        have hl_eq : l' = l := by
          rcases hxl' with h1 | h2
          · have := congrArg Fin.val h1; simp at this; omega
          · exact Fin.ext (by have := congrArg Fin.val h2; simp at this; omega)
        rw [← hp_eq, ← hl_eq]; exact hp'l'
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
    have hE_in_Tstar : ∀ p l : Fin 7, (p, l) ∈ E →
        ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
      intro p l hpl
      obtain ⟨j, hand, htop, a, b, hab, hlr⟩ := hedge_covered p l hpl
      have hjT : j ∈ Tstar :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hand, htop, p, l, a, b, hab, hlr⟩
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
          rw [hpW] at hlem
          rw [hlem] at hla_m; cases hla_m
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
    let centerP (j : Fin C.gates.length) : Fin 7 :=
      if h : (pSide j).Nonempty then h.choose else 0
    let centerL (j : Fin C.gates.length) : Fin 7 :=
      if h : (lSide j).Nonempty then h.choose else 0
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
    let A : Finset (Fin 7) := Tpt.image centerP
    let B : Finset (Fin 7) := Tln.image centerL
    have hAB_card : A.card + B.card ≤ Tstar.card := by
      have hA : A.card ≤ Tpt.card := Finset.card_image_le
      have hB : B.card ≤ Tln.card := Finset.card_image_le
      omega
    have hcover : ∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B := by
      intro e he
      obtain ⟨j, hjT, hpj, hlj⟩ := hE_in_Tstar e.1 e.2 he
      by_cases h1 : (pSide j).card = 1
      · have hjpt : j ∈ Tpt := Finset.mem_filter.mpr ⟨hjT, h1⟩
        exact Or.inl (Finset.mem_image.mpr ⟨j, hjpt, (hcenterP_eq j hjpt e.1 hpj).symm⟩)
      · have hjln : j ∈ Tln := Finset.mem_filter.mpr ⟨hjT, h1⟩
        exact Or.inr (Finset.mem_image.mpr ⟨j, hjln, (hcenterL_eq j hjln e.2 hlj).symm⟩)
    have hAB_ge7 : 7 ≤ A.card + B.card := by
      let B' : Finset (Fin 7) := Finset.univ.filter (fun p => matchL p ∈ B)
      have hsub : (Finset.univ : Finset (Fin 7)) ⊆ A ∪ B' := by
        intro p _
        rcases hcover (p, matchL p) ((hmem_E p (matchL p)).mpr (hmatch_I p)) with hpA | hlB
        · exact Finset.mem_union_left _ hpA
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlB⟩)
      have hB'_le : B'.card ≤ B.card := by
        have h1 : B'.card = (B'.image matchL).card :=
          (Finset.card_image_of_injective B' hmatch_inj).symm
        have h2 : B'.image matchL ⊆ B := by
          intro l hl
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
          exact (Finset.mem_filter.mp hp).2
        have h3 := Finset.card_le_card h2
        omega
      have h7 : 7 ≤ (A ∪ B').card := by
        have h1 := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        exact h1
      have h2 := Finset.card_union_le A B'
      omega
    let Otop : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        OrPath C.output (N + o.val) ∧
        ∃ a ∈ Tstar, OrPath (N + o.val) (N + a.val))
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
        have hroot_ex : ∃ root ∈ Otop, C.output = N + root.val := by
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
        have hpar_ex : ∀ x ∈ H.erase root,
            ∃ y ∈ Otop, N + x.val ∈ (gateAt C y.val).inputs := by
          intro x hx
          have hxne : x ≠ root := (Finset.mem_erase.mp hx).1
          have hxH : x ∈ H := (Finset.mem_erase.mp hx).2
          have hx_out : OrPath C.output (N + x.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.1
            · exact (hTstar_props x hT).2.1
          have hx_a : ∃ a ∈ Tstar, OrPath (N + x.val) (N + a.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.2
            · exact ⟨x, hT, orPath_refl _⟩
          have hne_out : C.output ≠ N + x.val := by
            rw [hroot_eq]; intro h; exact hxne (Fin.ext (by omega))
          obtain ⟨y, hy, hory, hpy, hxin⟩ := orPath_parent hx_out hne_out
          obtain ⟨a, haT, hxa⟩ := hx_a
          refine ⟨⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hory, hpy,
            a, haT, orPath_step hy hory hxin hxa⟩, hxin⟩
        let par (x : Fin C.gates.length) : Fin C.gates.length :=
          if hx : x ∈ H.erase root then (hpar_ex x hx).choose else root
        have hpar_mem : ∀ x ∈ H.erase root, par x ∈ Otop := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.1
        have hpar_in : ∀ x ∈ H.erase root, N + x.val ∈ (gateAt C (par x).val).inputs := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.2
        have hfiber_le2 : ∀ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ 2 := by
          intro y _
          let F := (H.erase root).filter (fun x => par x = y)
          have hsub : F.image (fun x : Fin C.gates.length => N + x.val) ⊆ (gateAt C y.val).inputs.toFinset := by
            intro w hw
            obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hw
            obtain ⟨hxH, hxy⟩ := Finset.mem_filter.mp hxF
            rw [List.mem_toFinset, ← hxy]
            exact hpar_in x hxH
          have hinj : Function.Injective (fun x : Fin C.gates.length => N + x.val) := by
            intro a b h; dsimp only at h; exact Fin.ext (by omega)
          have h1 : F.card = (F.image (fun x : Fin C.gates.length => N + x.val)).card :=
            (Finset.card_image_of_injective F hinj).symm
          have h2 : (F.image (fun x : Fin C.gates.length => N + x.val)).card ≤ ((gateAt C y.val).inputs.toFinset).card :=
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
    let Tpt_p (p : Fin 7) : Finset (Fin C.gates.length) := Tpt.filter (fun j => centerP j = p)
    let E_p (p : Fin 7) : Finset (Fin 7) := (Tpt_p p).biUnion lSide
    let Obot_p (p : Fin 7) : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        2 ≤ (lns (N + o.val)).card ∧
        ∃ j ∈ Tpt_p p, OrPath (lWire j) (N + o.val))
    let Tln_l (l : Fin 7) : Finset (Fin C.gates.length) := Tln.filter (fun j => centerL j = l)
    let E_l (l : Fin 7) : Finset (Fin 7) := (Tln_l l).biUnion pSide
    let Obot_l (l : Fin 7) : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        2 ≤ (pts (N + o.val)).card ∧
        ∃ j ∈ Tln_l l, OrPath (pWire j) (N + o.val))
    have hEp_bound : ∀ p ∈ A, (E_p p).card ≤ (Obot_p p).card + (Tpt_p p).card := by
      intro p _
      exact side_component_bound
        (fun l : Fin 7 => 7 + l.val) (fun l => by omega)
        (fun l1 l2 h => Fin.ext (by dsimp only at h; omega))
        (Tpt_p p) lWire
        (fun j hj => by
          obtain ⟨l, hl⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.2.1
          exact ⟨l, (Finset.mem_filter.mp hl).2⟩)
    have hEl_bound : ∀ l ∈ B, (E_l l).card ≤ (Obot_l l).card + (Tln_l l).card := by
      intro l _
      exact side_component_bound
        (fun p : Fin 7 => p.val) (fun p => by omega)
        (fun p1 p2 h => Fin.ext h)
        (Tln_l l) pWire
        (fun j hj => by
          obtain ⟨p, hp⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.1
          exact ⟨p, (Finset.mem_filter.mp hp).2⟩)
    have hObot_p_disj : Set.PairwiseDisjoint (A : Set (Fin 7)) Obot_p := by
      intro p1 _ p2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro o h1 h2
      obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
      obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (lns (N + o.val)).card)
      have hj1pt := (Finset.mem_filter.mp hj1).1
      have hj1p := (Finset.mem_filter.mp hj1).2
      have hj2pt := (Finset.mem_filter.mp hj2).1
      have hj2p := (Finset.mem_filter.mp hj2).2
      have hp1_in : p1 ∈ pSide j1 := hj1p ▸ hcenterP_mem j1 hj1pt
      have hp2_in : p2 ∈ pSide j2 := hj2p ▸ hcenterP_mem j2 hj2pt
      have hl1_j1 : l1 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo1 (Finset.mem_filter.mp hl1).2⟩
      have hl2_j1 : l2 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo1 (Finset.mem_filter.mp hl2).2⟩
      have hl1_j2 : l1 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo2 (Finset.mem_filter.mp hl1).2⟩
      have hl2_j2 : l2 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo2 (Finset.mem_filter.mp hl2).2⟩
      have hpr1 := (hTstar_props j1 (Finset.mem_filter.mp hj1pt).1).2.2.2.2.2.2.1
      have hpr2 := (hTstar_props j2 (Finset.mem_filter.mp hj2pt).1).2.2.2.2.2.2.1
      exact hNoC4 p1 p2 l1 l2 hne hlne
        ⟨(hmem_E p1 l1).mp (hpr1 p1 hp1_in l1 hl1_j1),
         (hmem_E p1 l2).mp (hpr1 p1 hp1_in l2 hl2_j1),
         (hmem_E p2 l1).mp (hpr2 p2 hp2_in l1 hl1_j2),
         (hmem_E p2 l2).mp (hpr2 p2 hp2_in l2 hl2_j2)⟩
    have hObot_l_disj : Set.PairwiseDisjoint (B : Set (Fin 7)) Obot_l := by
      intro l1 _ l2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro o h1 h2
      obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (pts (N + o.val)).card)
      have hj1ln := (Finset.mem_filter.mp hj1).1
      have hj1l := (Finset.mem_filter.mp hj1).2
      have hj2ln := (Finset.mem_filter.mp hj2).1
      have hj2l := (Finset.mem_filter.mp hj2).2
      have hl1_in : l1 ∈ lSide j1 := hj1l ▸ hcenterL_mem j1 hj1ln
      have hl2_in : l2 ∈ lSide j2 := hj2l ▸ hcenterL_mem j2 hj2ln
      have hp1_j1 : p1 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo1 (Finset.mem_filter.mp hp1).2⟩
      have hp2_j1 : p2 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo1 (Finset.mem_filter.mp hp2).2⟩
      have hp1_j2 : p1 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo2 (Finset.mem_filter.mp hp1).2⟩
      have hp2_j2 : p2 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo2 (Finset.mem_filter.mp hp2).2⟩
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
      obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (N + o.val)).card)
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
        have hcard := (Finset.mem_filter.mp ho).2.2.1
        obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (N + o.val)).card)
        have hop := orPath_trans hop_out (Finset.mem_filter.mp hl0).2
        let x : Fin N → Bool := fun i => decide (i = Fin.natAdd 7 l0)
        have hx_l : wireVal N C (7 + l0.val) x = true := by
          have := wireVal_input (Fin.natAdd 7 l0) x; simpa [x, Nat.add_comm] using this
        have ht := orPath_sound hop x hx_l
        have hf := hno_lns_only x (fun p' => by
          simp only [x, decide_eq_false_iff_not]
          intro h; have := congrArg Fin.val h; simp at this; omega)
        rw [ht] at hf; cases hf
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
        have hcard := (Finset.mem_filter.mp ho).2.2.1
        obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < (pts (N + o.val)).card)
        have hop := orPath_trans hop_out (Finset.mem_filter.mp hp0).2
        let x : Fin N → Bool := fun i => decide (i = Fin.castAdd 7 p0)
        have hx_p : wireVal N C p0.val x = true := by
          have := wireVal_input (Fin.castAdd 7 p0) x; simpa [x] using this
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
    omega
  intro x1 x2 x3 hMono hx2_lt hx3_lt
  dsimp only
  intro hpos hneg hw2_only hw3_only
  by_contra hlt26
  have hsz25 : x1.size ≤ 25 := by omega
  let H : (Fin 14 → Bool) → Prop := fun x =>
    ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
  let M0 : List (Bool ⊕ ℕ) := (List.range 14).map (Sum.inr : ℕ → Bool ⊕ ℕ)
  have hM0_len : M0.length = 14 := by simp only [M0, List.length_map, List.length_range]
  have hM0_lt (j : ℕ) (hj : j < 14) : M0.getD j (Sum.inl false) = Sum.inr j := by
    have hlt : j < M0.length := by rw [hM0_len]; exact hj
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [M0, List.getElem_map, List.getElem_range]
  let res := elim x1.gates (M0, [])
  have hbase (x : Fin 14 → Bool) : Inv (List.ofFn x) (List.ofFn x) (M0, []) := by
    refine ⟨List.length_ofFn, (by rw [hM0_len, List.length_ofFn]), (fun _ h => by cases h),
      (fun _ h _ _ => by simp only [List.length_nil] at h; omega), ?_⟩
    intro i
    by_cases hi : i < 14
    · rw [hM0_lt i hi]
      exact ⟨show i < 14 + 0 by omega, rfl⟩
    · rw [List.getD_eq_default M0 (Sum.inl false) (n := i) (by rw [hM0_len]; omega),
          List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega)]
      exact ⟨trivial, rfl⟩
  have hfin (x : Fin 14 → Bool) : Inv (List.ofFn x) (run x1.gates (List.ofFn x)) res :=
    elim_inv x1.gates (List.ofFn x) (List.ofFn x) (M0, []) hMono (hbase x)
  let D0 : Circuit := ⟨res.2, 0⟩
  have hD0_sz : D0.size ≤ 25 := by
    have h1 := elim_len x1.gates (M0, [])
    change (elim x1.gates (M0, [])).2.length ≤ 25
    simp only [List.length_nil, Nat.zero_add] at h1
    have h2 : x1.gates.length ≤ 25 := hsz25
    omega
  have hD0_AO : IsAO2 14 D0 := by
    have hf0 := hfin (fun _ => false)
    refine ⟨fun g hg => (hf0.2.2.1 g hg).1, ?_, fun g hg => (hf0.2.2.1 g hg).2⟩
    intro j hj i hi
    exact hf0.2.2.2.1 j hj i hi
  have hH_false : ¬ H (fun _ => false) := by
    rintro ⟨a, b, _, ha, _⟩; cases ha
  have hH_single (k : ℕ) : ¬ H (fun i : Fin 14 => decide (i.val = k)) := by
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [decide_eq_true_eq] at ha hb
    have hbd := hedges_bounds (a.val, b.val) hab
    omega
  have hmap_wire (xold : ℕ) (hx_t : ∃ x : Fin 14 → Bool, (x1.wires (List.ofFn x)).getD xold false = true)
      (hx_f : (x1.wires (List.ofFn (fun _ : Fin 14 => false))).getD xold false = false) :
      ∃ w : ℕ, w < 14 + D0.gates.length ∧
        ∀ x : Fin 14 → Bool, wval D0 x w = (x1.wires (List.ofFn x)).getD xold false := by
    cases hs : res.1.getD xold (Sum.inl false) with
    | inl b =>
      cases b with
      | false =>
        obtain ⟨x, hx⟩ := hx_t
        have h := ((hfin x).2.2.2.2 xold).2
        rw [hs] at h
        change false = (x1.wires (List.ofFn x)).getD xold false at h
        rw [hx] at h; cases h
      | true =>
        have h := ((hfin (fun _ => false)).2.2.2.2 xold).2
        rw [hs] at h
        change true = (x1.wires (List.ofFn fun _ => false)).getD xold false at h
        rw [hx_f] at h; cases h
    | inr w =>
      have hv := ((hfin (fun _ => false)).2.2.2.2 xold).1
      rw [hs] at hv
      refine ⟨w, hv, fun x => ?_⟩
      have h := ((hfin x).2.2.2.2 xold).2
      rw [hs] at h
      exact h
  obtain ⟨x12, hx12H, hx12_2, hx12_3⟩ := hw2_only
  obtain ⟨x13, hx13H, hx13_3, hx13_2⟩ := hw3_only
  obtain ⟨w2, hw2_lt, hw2_eq⟩ := hmap_wire x2 ⟨x12, hx12_2⟩ (hneg (fun _ => false) hH_false).1
  obtain ⟨w3, hw3_lt, hw3_eq⟩ := hmap_wire x3 ⟨x13, hx13_3⟩ (hneg (fun _ => false) hH_false).2
  have hD0_iff (x : Fin 14 → Bool) : H x ↔ (wval D0 x w2 = true ∨ wval D0 x w3 = true) := by
    rw [hw2_eq x, hw3_eq x]
    constructor
    · exact hpos x
    · intro hor
      by_contra hnh
      have hf := hneg x hnh
      rcases hor with h2 | h3
      · rw [hf.1] at h2; cases h2
      · rw [hf.2] at h3; cases h3
  have hw2_ge14 : 14 ≤ w2 := by
    by_contra hlt
    let xs : Fin 14 → Bool := fun i => decide (i.val = w2)
    have hf : wval D0 xs w2 = false := by
      rw [hw2_eq xs]
      exact (hneg xs (hH_single w2)).1
    have ht : wval D0 xs w2 = true := by
      change (run D0.gates (List.ofFn xs)).getD w2 false = true
      have h1 : w2 < (List.ofFn xs).length := by simp only [List.length_ofFn]; omega
      rw [run_keep D0.gates (List.ofFn xs) w2 h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
      simp only [xs, decide_eq_true_eq]
    rw [ht] at hf; cases hf
  have hw3_ge14 : 14 ≤ w3 := by
    by_contra hlt
    let xs : Fin 14 → Bool := fun i => decide (i.val = w3)
    have hf : wval D0 xs w3 = false := by
      rw [hw3_eq xs]
      exact (hneg xs (hH_single w3)).2
    have ht : wval D0 xs w3 = true := by
      change (run D0.gates (List.ofFn xs)).getD w3 false = true
      have h1 : w3 < (List.ofFn xs).length := by simp only [List.length_ofFn]; omega
      rw [run_keep D0.gates (List.ofFn xs) w3 h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
      simp only [xs, decide_eq_true_eq]
    rw [ht] at hf; cases hf
  have hw2_ne_w3 : w2 ≠ w3 := by
    intro heq
    have h2 : wval D0 x12 w2 = true := by rw [hw2_eq x12]; exact hx12_2
    have h3 : wval D0 x12 w3 = false := by rw [hw3_eq x12]; exact hx12_3
    rw [heq, h3] at h2; cases h2
  have huncov : ∃ p l : Fin 7, I p l ∧
      ¬ ∃ j a b : ℕ, andOn D0 j a b ∧
        (orp D0 14 (14 + j) w2 ∨ orp D0 14 (14 + j) w3) ∧
        orp D0 14 p.val a ∧ orp D0 14 (7 + l.val) b := by
    by_contra hall_not
    have hallD : ∀ p l : Fin 7, I p l →
        ∃ j a b : ℕ, andOn D0 j a b ∧
          (orp D0 14 (14 + j) w2 ∨ orp D0 14 (14 + j) w3) ∧
          orp D0 14 p.val a ∧ orp D0 14 (7 + l.val) b := by
      intro p l hpl
      by_contra hno
      exact hall_not ⟨p, l, hpl, hno⟩
    let gTop : Gate := ⟨GateOp.or, [w2, w3]⟩
    let E : Circuit := ⟨D0.gates ++ [gTop], 14 + D0.gates.length⟩
    have hE_sz : E.size ≤ 26 := by
      change (D0.gates ++ [gTop]).length ≤ 26
      rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      have h1 : D0.gates.length ≤ 25 := hD0_sz
      omega
    have hE_gate_lt (j : ℕ) (hj : j < D0.gates.length) : gateAt E j = gateAt D0 j := by
      change (D0.gates ++ [gTop]).getD j ⟨GateOp.or, []⟩ = D0.gates.getD j ⟨GateOp.or, []⟩
      exact List.getD_append _ _ _ _ hj
    have hE_gate_top : gateAt E D0.gates.length = gTop := by
      change (D0.gates ++ [gTop]).getD D0.gates.length ⟨GateOp.or, []⟩ = gTop
      exact getD_snoc_eq D0.gates gTop ⟨GateOp.or, []⟩
    have hE_AO : IsAO2 14 E := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        change g ∈ D0.gates ++ [gTop] at hg
        rw [List.mem_append, List.mem_singleton] at hg
        rcases hg with h1 | rfl
        · exact hD0_AO.1 g h1
        · exact Or.inr rfl
      · intro j hj u hu
        change j < (D0.gates ++ [gTop]).length at hj
        rw [List.length_append] at hj
        simp only [List.length_cons, List.length_nil] at hj
        by_cases hlt : j < D0.gates.length
        · rw [hE_gate_lt j hlt] at hu
          exact hD0_AO.2.1 j hlt u hu
        · have hjeq : j = D0.gates.length := by omega
          subst hjeq
          rw [hE_gate_top] at hu
          change u ∈ [w2, w3] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
      · intro g hg
        change g ∈ D0.gates ++ [gTop] at hg
        rw [List.mem_append, List.mem_singleton] at hg
        rcases hg with h1 | rfl
        · exact hD0_AO.2.2 g h1
        · rfl
    have hE_comp : ∀ x : Fin 14 → Bool, circuitFun 14 E x =
        decide (∃ (p l : Fin 7), I p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) := by
      intro x
      have hEv : circuitFun 14 E x = (wval D0 x w2 || wval D0 x w3) := by
        change (run (D0.gates ++ [gTop]) (List.ofFn x)).getD (14 + D0.gates.length) false = _
        have hrf : run (D0.gates ++ [gTop]) (List.ofFn x) =
            step (run D0.gates (List.ofFn x)) gTop := by
          dsimp only [run]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [hrf]
        have hlen : (run D0.gates (List.ofFn x)).length = 14 + D0.gates.length := by
          rw [run_len, List.length_ofFn]
        dsimp only [step]
        rw [← hlen, getD_snoc_eq _ _ false]
        change (wval D0 x w2 || (wval D0 x w3 || false)) = (wval D0 x w2 || wval D0 x w3)
        rw [Bool.or_false]
      rw [hEv]
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true, decide_eq_true_eq, ← hD0_iff x]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        have hbd := hedges_bounds (a.val, b.val) hab
        refine ⟨⟨a.val, hbd.1⟩, ⟨b.val - 7, by omega⟩, ?_, ?_, ?_⟩
        · change (a.val, 7 + (b.val - 7)) ∈ edges
          have hbe : 7 + (b.val - 7) = b.val := by omega
          rw [hbe]; exact hab
        · convert ha using 2; apply Fin.ext; rfl
        · convert hb using 2; apply Fin.ext; change 7 + (b.val - 7) = b.val; omega
      · rintro ⟨p, l, hpl, hp, hl⟩
        exact ⟨Fin.castAdd 7 p, Fin.natAdd 7 l, hpl, hp, hl⟩
    have horp_lift : ∀ x y : ℕ, orp D0 14 x y → orp E 14 x y := by
      intro x y h
      change Relation.ReflTransGen _ x y at h ⊢
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        obtain ⟨hlt, j, rfl, ⟨hjlt, hjor⟩, ha⟩ := hstep
        refine Relation.ReflTransGen.tail ih ⟨hlt, j, rfl, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · change j < (D0.gates ++ [gTop]).length
            rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega
          · rw [hE_gate_lt j hjlt]; exact hjor
        · rw [hE_gate_lt j hjlt]; exact ha
    have hallE : ∀ p l : Fin 7, I p l →
        ∃ j a b : ℕ, andOn E j a b ∧
          orp E 14 (14 + j) E.output ∧
          orp E 14 p.val a ∧
          orp E 14 (7 + l.val) b := by
      intro p l hpl
      obtain ⟨j, a, b, handD, htopD, hpa, hlb⟩ := hallD p l hpl
      obtain ⟨⟨hjlt, hjand⟩, hord⟩ := handD
      have hjltE : j < E.gates.length := by
        change j < (D0.gates ++ [gTop]).length
        rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega
      have handE : andOn E j a b := by
        refine ⟨⟨hjltE, by rw [hE_gate_lt j hjlt]; exact hjand⟩, ?_⟩
        have h0 : in0 E j = in0 D0 j := by
          change (gateAt E j).inputs.getD 0 0 = (gateAt D0 j).inputs.getD 0 0
          rw [hE_gate_lt j hjlt]
        have h1 : in1 E j = in1 D0 j := by
          change (gateAt E j).inputs.getD 1 0 = (gateAt D0 j).inputs.getD 1 0
          rw [hE_gate_lt j hjlt]
        rw [h0, h1]; exact hord
      have htop_step (w : ℕ) (hw : w < 14 + D0.gates.length) (hmem : w ∈ [w2, w3]) :
          orp E 14 w E.output := by
        refine Relation.ReflTransGen.single ⟨hw, D0.gates.length, rfl, ⟨?_, ?_⟩, ?_⟩
        · change D0.gates.length < (D0.gates ++ [gTop]).length
          rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega
        · rw [hE_gate_top]
        · rw [hE_gate_top]; exact hmem
      have htopE : orp E 14 (14 + j) E.output := by
        rcases htopD with h2 | h3
        · exact Relation.ReflTransGen.trans (horp_lift _ _ h2)
            (htop_step w2 hw2_lt List.mem_cons_self)
        · exact Relation.ReflTransGen.trans (horp_lift _ _ h3)
            (htop_step w3 hw3_lt (List.mem_cons_of_mem _ List.mem_cons_self))
      exact ⟨j, a, b, handE, htopE, horp_lift _ _ hpa, horp_lift _ _ hlb⟩
    have h28 := hstar_bound E hE_AO hE_comp hallE
    omega
  obtain ⟨p0, l0, hI0, huncov0⟩ := huncov
  obtain ⟨entry, hentry_mem, hentry_eq⟩ := haut_cov (p0.val, 7 + l0.val) hI0
  obtain ⟨hplen, hpinvlen, hbounds, hinvs, hp0, hp7, hfwd, hbwd⟩ := haut_ok entry hentry_mem
  let pList : List ℕ := entry.2.1
  let pinvList : List ℕ := entry.2.2
  have hpList_len : pList.length = 14 := hplen
  have hpinvList_len : pinvList.length = 14 := hpinvlen
  let π : ℕ → ℕ := fun w => pList.getD w w
  let πinv : ℕ → ℕ := fun w => pinvList.getD w w
  have hπ_lt (w : ℕ) (hw : w < 14) : π w < 14 := by
    have h1 := (hbounds ⟨w, hw⟩).1
    have h2 : pList.getD w w = pList.getD w 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    change pList.getD w w < 14
    rw [h2]; exact h1
  have hπinv_lt (w : ℕ) (hw : w < 14) : πinv w < 14 := by
    have h1 := (hbounds ⟨w, hw⟩).2
    have h2 : pinvList.getD w w = pinvList.getD w 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    change pinvList.getD w w < 14
    rw [h2]; exact h1
  have hπ_ge (w : ℕ) (hw : 14 ≤ w) : π w = w :=
    List.getD_eq_default pList w (n := w) (by omega)
  have hπinv_ge (w : ℕ) (hw : 14 ≤ w) : πinv w = w :=
    List.getD_eq_default pinvList w (n := w) (by omega)
  have hπinv_π (w : ℕ) : πinv (π w) = w := by
    by_cases hw : w < 14
    · have h1 := (hinvs ⟨w, hw⟩).1
      have hpw : π w < 14 := hπ_lt w hw
      have heq1 : pList.getD w w = pList.getD w 14 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      have heq2 : pinvList.getD (π w) (π w) = pinvList.getD (π w) 14 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      change pinvList.getD (π w) (π w) = w
      rw [heq2]; dsimp only [π]; rw [heq1]; exact h1
    · rw [hπ_ge w (by omega), hπinv_ge w (by omega)]
  have hπ_πinv (w : ℕ) : π (πinv w) = w := by
    by_cases hw : w < 14
    · have h1 := (hinvs ⟨w, hw⟩).2
      have hpw : πinv w < 14 := hπinv_lt w hw
      have heq1 : pinvList.getD w w = pinvList.getD w 14 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      have heq2 : pList.getD (πinv w) (πinv w) = pList.getD (πinv w) 14 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      change pList.getD (πinv w) (πinv w) = w
      rw [heq2]; dsimp only [πinv]; rw [heq1]; exact h1
    · rw [hπinv_ge w (by omega), hπ_ge w (by omega)]
  have hπ_p0 : π p0.val = 0 := by
    have hlt : p0.val < 14 := by omega
    have heq : pList.getD p0.val p0.val = pList.getD p0.val 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    change pList.getD p0.val p0.val = 0
    rw [heq]
    have he1 : entry.1.1 = p0.val := by rw [hentry_eq]
    rw [← he1]; exact hp0
  have hπ_l0 : π (7 + l0.val) = 7 := by
    have hlt : 7 + l0.val < 14 := by omega
    have heq : pList.getD (7 + l0.val) (7 + l0.val) = pList.getD (7 + l0.val) 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    change pList.getD (7 + l0.val) (7 + l0.val) = 7
    rw [heq]
    have he2 : entry.1.2 = 7 + l0.val := by rw [hentry_eq]
    rw [← he2]; exact hp7
  have hπinv_0 : πinv 0 = p0.val := (congrArg πinv hπ_p0).symm.trans (hπinv_π p0.val)
  have hπinv_7 : πinv 7 = 7 + l0.val := (congrArg πinv hπ_l0).symm.trans (hπinv_π (7 + l0.val))
  have hπ_edges : ∀ a b : ℕ, (a, b) ∈ edges → (π a, π b) ∈ edges := by
    intro a b hab
    have hbd := hedges_bounds (a, b) hab
    have ha : pList.getD a a = pList.getD a 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    have hb : pList.getD b b = pList.getD b 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    change (pList.getD a a, pList.getD b b) ∈ edges
    rw [ha, hb]; exact hfwd (a, b) hab
  have hπinv_edges : ∀ a b : ℕ, (a, b) ∈ edges → (πinv a, πinv b) ∈ edges := by
    intro a b hab
    have hbd := hedges_bounds (a, b) hab
    have ha : pinvList.getD a a = pinvList.getD a 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    have hb : pinvList.getD b b = pinvList.getD b 14 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    change (pinvList.getD a a, pinvList.getD b b) ∈ edges
    rw [ha, hb]; exact hbwd (a, b) hab
  let πf : Fin 14 → Fin 14 := fun i => ⟨π i.val, hπ_lt i.val i.isLt⟩
  let πinvf : Fin 14 → Fin 14 := fun i => ⟨πinv i.val, hπinv_lt i.val i.isLt⟩
  let mapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map π⟩
  let D1 : Circuit := ⟨D0.gates.map mapGate, π D0.output⟩
  have hD1_sz : D1.size ≤ 25 := by
    change (D0.gates.map mapGate).length ≤ 25
    rw [List.length_map]
    exact hD0_sz
  have hD1_gate (j : ℕ) (hj : j < D0.gates.length) : gateAt D1 j = mapGate (gateAt D0 j) := by
    have hj' : j < (D0.gates.map mapGate).length := by rw [List.length_map]; exact hj
    change (D0.gates.map mapGate).getD j ⟨GateOp.or, []⟩ = mapGate (D0.gates.getD j ⟨GateOp.or, []⟩)
    rw [List.getD_eq_getElem _ _ hj', List.getElem_map, List.getD_eq_getElem _ _ hj]
  have hD1_AO : IsAO2 14 D1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro g' hg'
      change g' ∈ D0.gates.map mapGate at hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact hD0_AO.1 g hg
    · intro j hj u hu
      have hj0 : j < D0.gates.length := by
        change j < (D0.gates.map mapGate).length at hj
        rw [List.length_map] at hj; exact hj
      rw [hD1_gate j hj0] at hu
      change u ∈ (gateAt D0 j).inputs.map π at hu
      rw [List.mem_map] at hu
      obtain ⟨i, hi, rfl⟩ := hu
      have hi_lt := hD0_AO.2.1 j hj0 i hi
      by_cases hi14 : i < 14
      · have h := hπ_lt i hi14; omega
      · rw [hπ_ge i (by omega)]; exact hi_lt
    · intro g' hg'
      change g' ∈ D0.gates.map mapGate at hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      change (g.inputs.map π).length = 2
      rw [List.length_map]
      exact hD0_AO.2.2 g hg
  have run_perm (gs : List Gate) (w1 w2 : List Bool) (hlen : w1.length = w2.length) (h14 : 14 ≤ w1.length)
      (hrel : ∀ j, w2.getD (π j) false = w1.getD j false) :
      ∀ j, (run (gs.map mapGate) w2).getD (π j) false = (run gs w1).getD j false := by
    induction gs generalizing w1 w2 with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hvals : ((mapGate g).inputs.map fun i => w2.getD i false) =
          (g.inputs.map fun i => w1.getD i false) := by
        dsimp only [mapGate]
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hrel i
      have heval : (mapGate g).op.eval ((mapGate g).inputs.map fun i => w2.getD i false) =
          g.op.eval (g.inputs.map fun i => w1.getD i false) := congrArg g.op.eval hvals
      apply ih (step w1 g) (step w2 (mapGate g))
      · simp only [step, List.length_append, hlen, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro j
        dsimp only [step]
        rw [heval]
        by_cases hj : j = w1.length
        · subst hj
          have hπl : π w1.length = w1.length := hπ_ge w1.length h14
          rw [hπl, getD_snoc_eq w1 _ false, hlen, getD_snoc_eq w2 _ false]
        · have hπj : π j ≠ w2.length := by
            intro heq
            have h1 : j = πinv w2.length := by rw [← heq, hπinv_π j]
            rw [← hlen, hπinv_ge w1.length h14] at h1
            exact hj h1
          rw [getD_snoc_ne w2 _ false (π j) hπj, getD_snoc_ne w1 _ false j hj]
          exact hrel j
  have hD1_wval (f : Fin 14 → Bool) (w : ℕ) (hw14 : 14 ≤ w) :
      wval D1 f w = wval D0 (fun t => f (πf t)) w := by
    have hrel : ∀ j, (List.ofFn f).getD (π j) false = (List.ofFn fun t => f (πf t)).getD j false := by
      intro j
      by_cases hj : j < 14
      · have hπj : π j < 14 := hπ_lt j hj
        have h1 : π j < (List.ofFn f).length := by simp only [List.length_ofFn]; exact hπj
        have h2 : j < (List.ofFn fun t => f (πf t)).length := by simp only [List.length_ofFn]; exact hj
        rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn,
            List.getD_eq_getElem _ _ h2, List.getElem_ofFn]
      · rw [hπ_ge j (by omega),
            List.getD_eq_default _ false (n := j) (by simp only [List.length_ofFn]; omega),
            List.getD_eq_default _ false (n := j) (by simp only [List.length_ofFn]; omega)]
    have hr := run_perm D0.gates (List.ofFn fun t => f (πf t)) (List.ofFn f)
      (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega) hrel w
    rw [hπ_ge w hw14] at hr
    exact hr
  have hD1_iff (f : Fin 14 → Bool) : H f ↔ (wval D1 f w2 = true ∨ wval D1 f w3 = true) := by
    rw [hD1_wval f w2 hw2_ge14, hD1_wval f w3 hw3_ge14, ← hD0_iff (fun t => f (πf t))]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      refine ⟨πinvf a, πinvf b, hπinv_edges a.val b.val hab, ?_, ?_⟩
      · convert ha using 2; apply Fin.ext; exact hπ_πinv a.val
      · convert hb using 2; apply Fin.ext; exact hπ_πinv b.val
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨πf a, πf b, hπ_edges a.val b.val hab, ha, hb⟩
  have hD1_w2_only : ∃ f : Fin 14 → Bool, wval D1 f w2 = true ∧ wval D1 f w3 = false := by
    refine ⟨fun i => x12 (πinvf i), ?_, ?_⟩
    · rw [hD1_wval _ w2 hw2_ge14]
      have hfn : (fun t : Fin 14 => x12 (πinvf (πf t))) = x12 :=
        funext fun t => congrArg x12 (Fin.ext (hπinv_π t.val))
      rw [hfn, hw2_eq x12]; exact hx12_2
    · rw [hD1_wval _ w3 hw3_ge14]
      have hfn : (fun t : Fin 14 => x12 (πinvf (πf t))) = x12 :=
        funext fun t => congrArg x12 (Fin.ext (hπinv_π t.val))
      rw [hfn, hw3_eq x12]; exact hx12_3
  have hD1_w3_only : ∃ f : Fin 14 → Bool, wval D1 f w3 = true ∧ wval D1 f w2 = false := by
    refine ⟨fun i => x13 (πinvf i), ?_, ?_⟩
    · rw [hD1_wval _ w3 hw3_ge14]
      have hfn : (fun t : Fin 14 => x13 (πinvf (πf t))) = x13 :=
        funext fun t => congrArg x13 (Fin.ext (hπinv_π t.val))
      rw [hfn, hw3_eq x13]; exact hx13_3
    · rw [hD1_wval _ w2 hw2_ge14]
      have hfn : (fun t : Fin 14 => x13 (πinvf (πf t))) = x13 :=
        funext fun t => congrArg x13 (Fin.ext (hπinv_π t.val))
      rw [hfn, hw2_eq x13]; exact hx13_2
  have horp_pull : ∀ x y : ℕ, orp D1 14 x y → orp D0 14 (πinv x) (πinv y) := by
    intro x y h
    change Relation.ReflTransGen _ x y at h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      obtain ⟨_, k, rfl, ⟨hklt, hkor⟩, ha⟩ := hstep
      have hk0 : k < D0.gates.length := by
        change k < (D0.gates.map mapGate).length at hklt
        rw [List.length_map] at hklt; exact hklt
      rw [hD1_gate k hk0] at hkor ha
      change _ ∈ (gateAt D0 k).inputs.map π at ha
      rw [List.mem_map] at ha
      obtain ⟨a0, ha0, ha0eq⟩ := ha
      have hpi : πinv (14 + k) = 14 + k := hπinv_ge (14 + k) (by omega)
      have ha_inv : πinv (π a0) = a0 := hπinv_π a0
      rw [← ha0eq] at ih
      rw [ha_inv] at ih
      rw [hpi]
      exact Relation.ReflTransGen.tail ih ⟨hD0_AO.2.1 k hk0 a0 ha0, k, rfl, ⟨hk0, hkor⟩, ha0⟩
  have hD1_uncov : ¬ ∃ j a b : ℕ, andOn D1 j a b ∧
      (orp D1 14 (14 + j) w2 ∨ orp D1 14 (14 + j) w3) ∧
      orp D1 14 0 a ∧ orp D1 14 7 b := by
    rintro ⟨j, a, b, ⟨⟨hjlt, hjand⟩, hord⟩, htop, h0a, h7b⟩
    have hj0 : j < D0.gates.length := by
      change j < (D0.gates.map mapGate).length at hjlt
      rw [List.length_map] at hjlt; exact hjlt
    apply huncov0
    refine ⟨j, πinv a, πinv b, ⟨⟨hj0, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
    · rw [hD1_gate j hj0] at hjand; exact hjand
    · have hlen2 : (gateAt D0 j).inputs.length = 2 := by
        have hmem : gateAt D0 j ∈ D0.gates := by
          change D0.gates.getD j ⟨GateOp.or, []⟩ ∈ D0.gates
          rw [List.getD_eq_getElem _ _ hj0]
          exact List.getElem_mem hj0
        exact hD0_AO.2.2 _ hmem
      cases hins : (gateAt D0 j).inputs with
      | nil => rw [hins] at hlen2; cases hlen2
      | cons u t1 =>
        cases t1 with
        | nil => rw [hins] at hlen2; cases hlen2
        | cons v t2 =>
          cases t2 with
          | cons _ _ => rw [hins] at hlen2; cases hlen2
          | nil =>
            have h0D1 : in0 D1 j = π u := by
              change (gateAt D1 j).inputs.getD 0 0 = π u
              rw [hD1_gate j hj0]; change ((gateAt D0 j).inputs.map π).getD 0 0 = π u
              rw [hins]; rfl
            have h1D1 : in1 D1 j = π v := by
              change (gateAt D1 j).inputs.getD 1 0 = π v
              rw [hD1_gate j hj0]; change ((gateAt D0 j).inputs.map π).getD 1 0 = π v
              rw [hins]; rfl
            have h0D0 : in0 D0 j = u := by
              change (gateAt D0 j).inputs.getD 0 0 = u; rw [hins]; rfl
            have h1D0 : in1 D0 j = v := by
              change (gateAt D0 j).inputs.getD 1 0 = v; rw [hins]; rfl
            rw [h0D1, h1D1] at hord
            rw [h0D0, h1D0]
            rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨by rw [← h1, hπinv_π], by rw [← h2, hπinv_π]⟩
            · exact Or.inr ⟨by rw [← h1, hπinv_π], by rw [← h2, hπinv_π]⟩
    · rcases htop with h2 | h3
      · left
        have h := horp_pull _ _ h2
        rw [hπinv_ge (14 + j) (by omega), hπinv_ge w2 hw2_ge14] at h
        exact h
      · right
        have h := horp_pull _ _ h3
        rw [hπinv_ge (14 + j) (by omega), hπinv_ge w3 hw3_ge14] at h
        exact h
    · have h := horp_pull _ _ h0a
      rw [hπinv_0] at h; exact h
    · have h := horp_pull _ _ h7b
      rw [hπinv_7] at h; exact h
  have hdispatch (u v : ℕ) (hu14 : 14 ≤ u) (hv14 : 14 ≤ v) (hult : u < 14 + D1.gates.length)
      (hvlt : v < 14 + D1.gates.length) (huv : u ≠ v)
      (hiff : ∀ x : Fin 14 → Bool, H x ↔ (wval D1 x u = true ∨ wval D1 x v = true))
      (hu_only : ∃ x : Fin 14 → Bool, wval D1 x u = true ∧ wval D1 x v = false)
      (hv_only : ∃ x : Fin 14 → Bool, wval D1 x v = true ∧ wval D1 x u = false)
      (hu07 : wval D1 (fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7)) u = true)
      (hunc : ¬ ∃ j a b : ℕ, andOn D1 j a b ∧
        (orp D1 14 (14 + j) u ∨ orp D1 14 (14 + j) v) ∧
        orp D1 14 0 a ∧ orp D1 14 7 b) : False := by
    have hu_lt : u - 14 < D1.gates.length := by omega
    have hv_lt : v - 14 < D1.gates.length := by omega
    have hu_mem : gateAt D1 (u - 14) ∈ D1.gates := by
      change D1.gates.getD (u - 14) ⟨GateOp.or, []⟩ ∈ D1.gates
      rw [List.getD_eq_getElem _ _ hu_lt]
      exact List.getElem_mem hu_lt
    have hv_mem : gateAt D1 (v - 14) ∈ D1.gates := by
      change D1.gates.getD (v - 14) ⟨GateOp.or, []⟩ ∈ D1.gates
      rw [List.getD_eq_getElem _ _ hv_lt]
      exact List.getElem_mem hv_lt
    rcases hD1_AO.1 _ hu_mem with hu_and | hu_or <;> rcases hD1_AO.1 _ hv_mem with hv_and | hv_or
    · exact hAndAnd D1 u v hD1_AO hD1_sz hu14 hv14 huv ⟨hu_lt, hu_and⟩ ⟨hv_lt, hv_and⟩ hiff hu_only hv_only hu07 hunc
    · exact hAndOr D1 u v hD1_AO hD1_sz hu14 hv14 huv ⟨hu_lt, hu_and⟩ ⟨hv_lt, hv_or⟩ hiff hu_only hv_only hu07 hunc
    · exact hOrAnd D1 u v hD1_AO hD1_sz hu14 hv14 huv ⟨hu_lt, hu_or⟩ ⟨hv_lt, hv_and⟩ hiff hu_only hv_only hu07 hunc
    · exact hOrOr D1 u v hD1_AO hD1_sz hu14 hv14 huv ⟨hu_lt, hu_or⟩ ⟨hv_lt, hv_or⟩ hiff hu_only hv_only hu07 hunc
  have hD1_len : D1.gates.length = D0.gates.length := List.length_map _
  have hw2_lt1 : w2 < 14 + D1.gates.length := by omega
  have hw3_lt1 : w3 < 14 + D1.gates.length := by omega
  have h07_H : H (fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7)) :=
    ⟨(0 : Fin 14), (7 : Fin 14), List.mem_cons_self, by decide, by decide⟩
  rcases (hD1_iff _).mp h07_H with hw2_07 | hw3_07
  · exact hdispatch w2 w3 hw2_ge14 hw3_ge14 hw2_lt1 hw3_lt1 hw2_ne_w3
      hD1_iff hD1_w2_only hD1_w3_only hw2_07 hD1_uncov
  · exact hdispatch w3 w2 hw3_ge14 hw2_ge14 hw3_lt1 hw2_lt1 hw2_ne_w3.symm
      (fun x => (hD1_iff x).trans or_comm) hD1_w3_only hD1_w2_only hw3_07
      (by
        rintro ⟨j, a, b, hand, htop, h0a, h7b⟩
        exact hD1_uncov ⟨j, a, b, hand, htop.symm, h0a, h7b⟩)
