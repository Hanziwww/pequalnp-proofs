import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4813_17
    (hBase : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      ∃ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [x 0 && x 2]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
           x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hEdge : ∀ p ∈ ([(0, 1), (0, 4), (1, 6), (3, 4), (3, 8), (6, 8)] : List (Fin 10 × Fin 10)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      ∃ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [x 0 && x 2, x p.1 && x p.2]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
           x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hNonEdge : ∀ p ∈ ([(0, 3), (0, 6), (0, 8), (1, 3), (1, 8), (3, 5), (3, 6), (3, 7), (3, 9), (8, 9)] : List (Fin 10 × Fin 10)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      ∃ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [x 0 && x 2, x p.1 && x p.2]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
           x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hTriple : ∀ i ∈ ([1, 3, 6, 8] : List (Fin 10)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      ∃ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [x 0 && x 2, x i && (x 0 && x 2)]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
           x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  intro D xs hfan hsize hxlen
  let P10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let edges10 : List (Fin 10 × Fin 10) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
     (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  have hP10_any (x : Fin 10 → Bool) : P10 x = edges10.any (fun e => x e.1 && x e.2) := by
    change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) =
      (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 ||
      (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 4 && x 9 ||
      (x 5 && x 7 || (x 7 && x 9 || (x 9 && x 6 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))))))
    rw [Bool.or_false]
    ac_rfl
  let w0 : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 && x 2]
  have hw0_len (x : Fin 10 → Bool) : (w0 x).length = 11 := by
    simp only [w0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have hw0_read (x : Fin 10 → Bool) (i : Fin 10) : (w0 x).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simp only [List.length_ofFn]; exact i.isLt
    dsimp only [w0]
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hw0_read10 (x : Fin 10 → Bool) : (w0 x).getD 10 false = (x 0 && x 2) := by
    have h10 : (List.ofFn x).length = 10 := List.length_ofFn
    dsimp only [w0]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [h10, Nat.sub_self, List.getD_cons_zero]
  have hw0_read11 (x : Fin 10 → Bool) : (w0 x).getD 11 false = false :=
    List.getD_eq_default (w0 x) false (n := 11) (by rw [hw0_len x])
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
  let simpNot : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.casesOn ins (none, Sum.inl true) (fun a _ =>
      Sum.elim (fun b => (none, Sum.inl (!b))) (fun i => (some (Gate.mk GateOp.not [i]), Sum.inr m)) a)
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
    GateOp.rec (simpAnd m ins) (simpOr m ins) (simpNot m ins) (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op
  have simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
      ∀ g ∈ (simplify op m ins).1.toList,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
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
              exact ⟨Or.inl rfl, Nat.le_refl 2⟩
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
              exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
    | not =>
      cases ins with
      | nil => intro g hg; cases hg
      | cons a t =>
        cases a with
        | inl ba => intro g hg; cases hg
        | inr ia =>
          intro g hg
          change g ∈ [Gate.mk GateOp.not [ia]] at hg
          rw [List.mem_singleton] at hg
          subst hg
          exact ⟨Or.inr (Or.inr rfl), Nat.le_succ 1⟩
    | mod _ => intro g hg; cases hg
    | maj => intro g hg; cases hg
  have simplify_sound (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, svalid w.length s) :
      svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      sval (run (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
        op.eval (ins.map (sval w)) := by
    rcases hop with rfl | rfl | rfl
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
    · cases ins with
      | nil => exact ⟨trivial, rfl⟩
      | cons a t =>
        cases a with
        | inl ba => exact ⟨trivial, rfl⟩
        | inr ia =>
          refine ⟨show w.length < w.length + 1 by omega, ?_⟩
          change (w ++ [!w.getD ia false]).getD w.length false = !w.getD ia false
          exact getD_snoc_eq w _ false
  let elimStep : List (Bool ⊕ ℕ) × List Gate → Gate → List (Bool ⊕ ℕ) × List Gate := fun acc g =>
    let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
    let r := simplify g.op (11 + acc.2.length) ins
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
        cases (simplify g.op (11 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
          simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
      simp only [List.length_cons]
      omega
  have elim_ok (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hacc : ∀ g ∈ acc.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      ∀ g ∈ (elim gs acc).2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    induction gs generalizing acc with
    | nil => exact hacc
    | cons g rest ih =>
      simp only [elim, List.foldl_cons] at ih ⊢
      apply ih (elimStep acc g)
      intro g' hg'
      dsimp only [elimStep] at hg'
      rw [List.mem_append] at hg'
      rcases hg' with h1 | h2
      · exact hacc g' h1
      · exact simplify_ok g.op (11 + acc.2.length) _ g' h2
  let Inv : List Bool → List Bool → List (Bool ⊕ ℕ) × List Gate → Prop := fun w z acc =>
    w.length = 11 ∧ acc.1.length = z.length ∧
    ∀ i, svalid (11 + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
         sval (run acc.2 w) (acc.1.getD i (Sum.inl false)) = z.getD i false
  have elim_inv (gs : List Gate) (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (hinv : Inv w z acc) : Inv w (run gs z) (elim gs acc) := by
    induction gs generalizing z acc with
    | nil => exact hinv
    | cons g rest ih =>
      simp only [run, elim, List.foldl_cons] at ih ⊢
      apply ih (step z g) (elimStep acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      obtain ⟨hwl, hml, hmap⟩ := hinv
      have hg := hgs g List.mem_cons_self
      let w' := run acc.2 w
      have hw'len : w'.length = 11 + acc.2.length := by
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
      have hvals : ins.map (sval w') = g.inputs.map (fun i => z.getD i false) := by
        dsimp only [ins]
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact (hmap i).2
      have hstep_run : run (acc.2 ++ r.1.toList) w = run r.1.toList w' := by
        dsimp only [run, w']; exact List.foldl_append
      have heq_r : simplify g.op (11 + acc.2.length) ins = r := by rw [← hw'len]
      refine ⟨hwl, ?_, ?_⟩
      · simp only [elimStep, step, List.length_append, hml, List.length_cons, List.length_nil]
      · intro i
        dsimp only [elimStep]
        change svalid (11 + (acc.2 ++ (simplify g.op (11 + acc.2.length) ins).1.toList).length)
            ((acc.1 ++ [(simplify g.op (11 + acc.2.length) ins).2]).getD i (Sum.inl false)) ∧
          sval (run (acc.2 ++ (simplify g.op (11 + acc.2.length) ins).1.toList) w)
            ((acc.1 ++ [(simplify g.op (11 + acc.2.length) ins).2]).getD i (Sum.inl false)) =
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
  have kill_redundant (s1 : Bool ⊕ ℕ) (hs1v : svalid 11 s1)
      (hs1e : ∀ x : Fin 10 → Bool, sval (w0 x) s1 = GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false)) :
      ∃ x : Fin 10 → Bool,
        have x7 : List Bool := List.ofFn x ++ [x 0 && x 2];
        D.eval (x7 ++ [GateOp.and.eval (xs.map fun i => x7.getD i.val false)]) ≠ P10 x := by
    by_contra hno
    have hagree (x : Fin 10 → Bool) :
        D.eval (w0 x ++ [GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false)]) = P10 x := by
      by_contra hne
      exact hno ⟨x, hne⟩
    let M0 : List (Bool ⊕ ℕ) := (List.range 11).map (Sum.inr : ℕ → Bool ⊕ ℕ) ++ [s1]
    have hM0_len : M0.length = 12 := by
      simp only [M0, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    have hM0_lt (k : ℕ) (hk : k < 11) : M0.getD k (Sum.inl false) = Sum.inr k := by
      have hrl : ((List.range 11).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = 11 := by
        simp only [List.length_map, List.length_range]
      dsimp only [M0]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
          List.getElem_map, List.getElem_range]
    have hM0_11 : M0.getD 11 (Sum.inl false) = s1 := by
      have hrl : ((List.range 11).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = 11 := by
        simp only [List.length_map, List.length_range]
      dsimp only [M0]
      simpa only [hrl] using getD_snoc_eq ((List.range 11).map (Sum.inr : ℕ → Bool ⊕ ℕ)) s1 (Sum.inl false)
    let res := elim D.gates (M0, [])
    have hbase (x : Fin 10 → Bool) :
        Inv (w0 x) (w0 x ++ [GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false)]) (M0, []) := by
      refine ⟨hw0_len x, by simp only [hM0_len, List.length_append, hw0_len x, List.length_cons, List.length_nil], ?_⟩
      intro k
      by_cases hk : k < 11
      · rw [hM0_lt k hk]
        refine ⟨show k < 11 + 0 by omega, ?_⟩
        change (w0 x).getD k false = (w0 x ++ [_]).getD k false
        exact (List.getD_append _ _ _ _ (by rw [hw0_len x]; exact hk)).symm
      · by_cases hk11 : k = 11
        · subst hk11
          rw [hM0_11]
          have h11z : (w0 x ++ [GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false)]).getD 11 false =
              GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false) := by
            simpa only [hw0_len x] using getD_snoc_eq (w0 x) (GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false)) false
          rw [h11z]
          exact ⟨by simpa only [List.length_nil, Nat.add_zero] using hs1v, hs1e x⟩
        · have hm : M0.getD k (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default M0 (Sum.inl false) (n := k) (by omega)
          have hz : (w0 x ++ [GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false)]).getD k false = false :=
            List.getD_eq_default _ false (n := k) (by simp only [List.length_append, hw0_len x, List.length_cons, List.length_nil]; omega)
          rw [hm, hz]
          exact ⟨trivial, rfl⟩
    have hfin (x : Fin 10 → Bool) := elim_inv D.gates (w0 x)
      (w0 x ++ [GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false)]) (M0, []) hfan (hbase x)
    cases hout : res.1.getD D.output (Sum.inl false) with
    | inl b =>
      have hf0 : b = P10 (fun _ => false) := by
        have h := ((hfin (fun _ => false)).2.2 D.output).2
        rw [hout] at h
        exact h.trans (hagree (fun _ => false))
      have hf1 : b = P10 (fun _ => true) := by
        have h := ((hfin (fun _ => true)).2.2 D.output).2
        rw [hout] at h
        exact h.trans (hagree (fun _ => true))
      have hne : P10 (fun _ => false) ≠ P10 (fun _ => true) := by decide
      exact hne (hf0.symm.trans hf1)
    | inr out =>
      let D' : Circuit := ⟨res.2, out⟩
      have hD'fan : FanInTwo D' := elim_ok D.gates (M0, []) (fun _ h => by cases h)
      have hD'sz : D'.size ≤ 17 := by
        have h := elim_len D.gates (M0, [])
        change (elim D.gates (M0, [])).2.length ≤ 17
        change D.gates.length ≤ 17 at hsize
        simp only [List.length_nil, Nat.zero_add] at h
        omega
      obtain ⟨x, hx⟩ := hBase D' hD'fan hD'sz
      have hev : D'.eval (w0 x) = P10 x := by
        have h := ((hfin x).2.2 D.output).2
        rw [hout] at h
        exact h.trans (hagree x)
      exact hx hev
  let permTable : List (List ℕ) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
     [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
     [2, 1, 0, 5, 7, 3, 6, 4, 8, 9]]
  let permNat : ℕ → ℕ → ℕ := fun m i => (permTable.getD m []).getD i i
  have hperm_row_len : ∀ m : Fin 4, (permTable.getD m.val []).length = 10 := by
    dsimp only [permTable]; decide
  have hperm_lt : ∀ m : Fin 4, ∀ i : Fin 10, permNat m.val i.val < 10 := by
    dsimp only [permNat, permTable]; decide
  have hperm_ge (m : Fin 4) (i : ℕ) (hi : 10 ≤ i) : permNat m.val i = i := by
    dsimp only [permNat]
    exact List.getD_eq_default (permTable.getD m.val []) i (n := i) (by rw [hperm_row_len m]; exact hi)
  have hperm_inv_fin : ∀ m : Fin 4, ∀ i : Fin 10, permNat m.val (permNat m.val i.val) = i.val := by
    dsimp only [permNat, permTable]; decide
  let permFin : Fin 4 → Fin 10 → Fin 10 := fun m i => ⟨permNat m.val i.val, hperm_lt m i⟩
  have hpermFin_inv (m : Fin 4) (i : Fin 10) : permFin m (permFin m i) = i :=
    Fin.ext (hperm_inv_fin m i)
  have hedges10_perm : ∀ m : Fin 4, ∀ e ∈ edges10,
      (∃ e' ∈ edges10, e'.1.val = permNat m.val e.1.val ∧ e'.2.val = permNat m.val e.2.val) ∨
      (∃ e' ∈ edges10, e'.1.val = permNat m.val e.2.val ∧ e'.2.val = permNat m.val e.1.val) := by
    dsimp only [edges10, permNat, permTable]; decide
  have hP10_perm (m : Fin 4) (x : Fin 10 → Bool) : P10 (fun i => x (permFin m i)) = P10 x := by
    have hdir : ∀ (y : Fin 10 → Bool), P10 (fun i => y (permFin m i)) = true → P10 y = true := by
      intro y hy
      rw [hP10_any (fun i => y (permFin m i))] at hy
      rw [hP10_any y]
      rw [List.any_eq_true] at hy ⊢
      obtain ⟨e, he, hbe⟩ := hy
      rcases hedges10_perm m e he with ⟨e', he', h1, h2⟩ | ⟨e', he', h1, h2⟩
      · have he1 : e'.1 = permFin m e.1 := Fin.ext h1
        have he2 : e'.2 = permFin m e.2 := Fin.ext h2
        exact ⟨e', he', by rw [he1, he2]; exact hbe⟩
      · have he1 : e'.1 = permFin m e.2 := Fin.ext h1
        have he2 : e'.2 = permFin m e.1 := Fin.ext h2
        exact ⟨e', he', by rw [he1, he2, Bool.and_comm]; exact hbe⟩
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hdir x
    · intro hx
      have hcomp : (fun i : Fin 10 => x (permFin m (permFin m i))) = x := by
        funext i; rw [hpermFin_inv m i]
      have h2 := hdir (fun i => x (permFin m i))
      rw [hcomp] at h2
      exact h2 hx
  have h02_perm (m : Fin 4) (x : Fin 10 → Bool) :
      (x (permFin m 0) && x (permFin m 2)) = (x 0 && x 2) := by
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by
      have := m.isLt; omega
    rcases hcases with rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · exact Bool.and_comm _ _
    · exact Bool.and_comm _ _
  have remap_bijection (m : Fin 4) (gs : List Gate) (wA wB : List Bool)
      (hlen_w : wA.length = wB.length) (h10 : 10 ≤ wA.length)
      (hrel : ∀ i, wB.getD (permNat m.val i) false = wA.getD i false) :
      ∀ i, (run (gs.map fun g => Gate.mk g.op (g.inputs.map (permNat m.val))) wB).getD (permNat m.val i) false =
        (run gs wA).getD i false := by
    induction gs generalizing wA wB with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hinp : (g.inputs.map (permNat m.val)).map (fun i => wB.getD i false) =
          g.inputs.map (fun i => wA.getD i false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hrel i
      let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
      have hstepB : step wB (Gate.mk g.op (g.inputs.map (permNat m.val))) = wB ++ [b] := by
        dsimp only [step, b]; rw [hinp]
      rw [hstepB]
      apply ih (step wA g) (wB ++ [b])
      · simp only [step, List.length_append, hlen_w, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        dsimp only [step]
        by_cases hi : i = wA.length
        · subst hi
          have hfi : permNat m.val wA.length = wB.length := by rw [hperm_ge m wA.length h10, hlen_w]
          rw [hfi, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
        · have hfi : permNat m.val i ≠ wB.length := by
            intro hfeq
            by_cases hlt : i < 10
            · have hpi : permNat m.val i < 10 := hperm_lt m ⟨i, hlt⟩; omega
            · have := hperm_ge m i (by omega); omega
          rw [getD_snoc_ne wB b false (permNat m.val i) hfi, getD_snoc_ne wA b false i hi]
          exact hrel i
  have transport (m : Fin 4) (e' : (Fin 10 → Bool) → Bool)
      (he : ∀ x : Fin 10 → Bool, e' x = GateOp.and.eval (xs.map fun i => (w0 (fun j => x (permFin m j))).getD i.val false))
      (hD' : ∀ D' : Circuit, FanInTwo D' → D'.size ≤ 17 → ∃ x : Fin 10 → Bool, D'.eval (w0 x ++ [e' x]) ≠ P10 x) :
      ∃ x : Fin 10 → Bool,
        have x7 : List Bool := List.ofFn x ++ [x 0 && x 2];
        D.eval (x7 ++ [GateOp.and.eval (xs.map fun i => x7.getD i.val false)]) ≠ P10 x := by
    let D' : Circuit := ⟨D.gates.map (fun g => Gate.mk g.op (g.inputs.map (permNat m.val))), permNat m.val D.output⟩
    have hD'fan : FanInTwo D' := by
      intro g hg
      simp only [D', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have h := hfan g0 hg0
      exact ⟨h.1, by simp only [List.length_map]; exact h.2⟩
    have hD'sz : D'.size ≤ 17 := by
      change (D.gates.map _).length ≤ 17
      rw [List.length_map]
      exact hsize
    obtain ⟨x, hx⟩ := hD' D' hD'fan hD'sz
    let y : Fin 10 → Bool := fun j => x (permFin m j)
    let wA := w0 y ++ [GateOp.and.eval (xs.map fun i => (w0 y).getD i.val false)]
    let wB := w0 x ++ [e' x]
    have hrel : ∀ i, wB.getD (permNat m.val i) false = wA.getD i false := by
      intro i
      by_cases hi10 : i < 10
      · have hpi : permNat m.val i < 10 := hperm_lt m ⟨i, hi10⟩
        dsimp only [wA, wB]
        rw [List.getD_append (w0 x) _ _ _ (by rw [hw0_len x]; omega),
            List.getD_append (w0 y) _ _ _ (by rw [hw0_len y]; omega)]
        have h1 : (w0 x).getD (permNat m.val i) false = x (permFin m ⟨i, hi10⟩) := hw0_read x ⟨permNat m.val i, hpi⟩
        have h2 : (w0 y).getD i false = y ⟨i, hi10⟩ := hw0_read y ⟨i, hi10⟩
        rw [h1, h2]
      · by_cases hi_eq10 : i = 10
        · subst hi_eq10
          rw [hperm_ge m 10 (by omega)]
          dsimp only [wA, wB]
          rw [List.getD_append (w0 x) _ _ _ (by rw [hw0_len x]; omega),
              List.getD_append (w0 y) _ _ _ (by rw [hw0_len y]; omega),
              hw0_read10 x, hw0_read10 y]
          exact (h02_perm m x).symm
        · by_cases hi_eq11 : i = 11
          · subst hi_eq11
            rw [hperm_ge m 11 (by omega)]
            dsimp only [wA, wB]
            rw [show 11 = (w0 x).length from (hw0_len x).symm, getD_snoc_eq (w0 x) _ false,
                show (w0 x).length = (w0 y).length from (hw0_len x).trans (hw0_len y).symm,
                getD_snoc_eq (w0 y) _ false]
            exact he x
          · rw [hperm_ge m i (by omega),
                List.getD_eq_default wB false (n := i) (by simp only [wB, List.length_append, hw0_len x, List.length_cons, List.length_nil]; omega),
                List.getD_eq_default wA false (n := i) (by simp only [wA, List.length_append, hw0_len y, List.length_cons, List.length_nil]; omega)]
    have hev : D'.eval wB = D.eval wA :=
      remap_bijection m D.gates wA wB
        (by simp only [wA, wB, List.length_append, hw0_len y, hw0_len x, List.length_cons, List.length_nil])
        (by simp only [wA, List.length_append, hw0_len y, List.length_cons, List.length_nil]; omega)
        hrel D.output
    refine ⟨y, ?_⟩
    dsimp only
    change D.eval wA ≠ P10 y
    rw [← hev, hP10_perm m x]
    exact hx
  let edgeReps : List (Fin 10 × Fin 10) := [(0, 1), (0, 4), (1, 6), (3, 4), (3, 8), (6, 8)]
  let nonEdgeReps : List (Fin 10 × Fin 10) :=
    [(0, 3), (0, 6), (0, 8), (1, 3), (1, 8), (3, 5), (3, 6), (3, 7), (3, 9), (8, 9)]
  let tripleReps : List (Fin 10) := [1, 3, 6, 8]
  have htriple_cov : ∀ b : Fin 10, b ≠ 0 → b ≠ 2 →
      ∃ m : Fin 4, ∃ r ∈ tripleReps, permNat m.val b.val = r.val := by
    dsimp only [tripleReps, permNat, permTable]; decide
  have hpair_cov : ∀ a b : Fin 10, a ≠ b → ¬ (a = 0 ∧ b = 2) → ¬ (a = 2 ∧ b = 0) →
      (∃ m : Fin 4, ∃ p ∈ edgeReps,
        (permNat m.val a.val = p.1.val ∧ permNat m.val b.val = p.2.val) ∨
        (permNat m.val a.val = p.2.val ∧ permNat m.val b.val = p.1.val)) ∨
      (∃ m : Fin 4, ∃ p ∈ nonEdgeReps,
        (permNat m.val a.val = p.1.val ∧ permNat m.val b.val = p.2.val) ∨
        (permNat m.val a.val = p.2.val ∧ permNat m.val b.val = p.1.val)) := by
    dsimp only [edgeReps, nonEdgeReps, permNat, permTable]; decide
  cases hxs : xs with
  | nil =>
    rw [← hxs]
    exact kill_redundant (Sum.inl true) trivial (fun _ => by rw [hxs]; rfl)
  | cons a t =>
    cases t with
    | nil =>
      rw [← hxs]
      by_cases ha11 : a.val < 11
      · exact kill_redundant (Sum.inr a.val) ha11 (fun x => by
          rw [hxs]
          change (w0 x).getD a.val false = ((w0 x).getD a.val false && true)
          exact (Bool.and_true _).symm)
      · have ha_eq11 : a.val = 11 := by have := a.isLt; omega
        exact kill_redundant (Sum.inl false) trivial (fun x => by
          rw [hxs]
          change false = ((w0 x).getD a.val false && true)
          rw [ha_eq11, hw0_read11 x]; rfl)
    | cons b t2 =>
      cases t2 with
      | cons _ _ => rw [hxs] at hxlen; simp only [List.length_cons] at hxlen; omega
      | nil =>
        rw [← hxs]
        have h11_eval (x : Fin 10 → Bool) :
            GateOp.and.eval (xs.map fun i => (w0 x).getD i.val false) =
              ((w0 x).getD a.val false && (w0 x).getD b.val false) := by
          rw [hxs]
          change ((w0 x).getD a.val false && ((w0 x).getD b.val false && true)) = _
          rw [Bool.and_true]
        by_cases h11 : a.val = 11 ∨ b.val = 11
        · exact kill_redundant (Sum.inl false) trivial (fun x => by
            rw [h11_eval x]
            rcases h11 with ha | hb
            · rw [ha, hw0_read11 x]; rfl
            · rw [hb, hw0_read11 x, Bool.and_false]; rfl)
        · have ha_lt11 : a.val < 11 := by have := a.isLt; omega
          have hb_lt11 : b.val < 11 := by have := b.isLt; omega
          by_cases hab : a.val = b.val
          · exact kill_redundant (Sum.inr a.val) ha_lt11 (fun x => by
              rw [h11_eval x, ← hab]
              exact (Bool.and_self _).symm)
          · by_cases h02 : (a.val = 0 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0)
            · exact kill_redundant (Sum.inr 10) (show (10 : ℕ) < 11 by omega) (fun x => by
                rw [h11_eval x]
                change (w0 x).getD 10 false = _
                rw [hw0_read10 x]
                rcases h02 with ⟨ha0, hb2⟩ | ⟨ha2, hb0⟩
                · rw [ha0, hb2, show (w0 x).getD 0 false = x 0 from hw0_read x 0,
                      show (w0 x).getD 2 false = x 2 from hw0_read x 2]
                · rw [ha2, hb0, show (w0 x).getD 2 false = x 2 from hw0_read x 2,
                      show (w0 x).getD 0 false = x 0 from hw0_read x 0, Bool.and_comm])
            · by_cases habsorb : (a.val = 10 ∧ (b.val = 0 ∨ b.val = 2)) ∨ (b.val = 10 ∧ (a.val = 0 ∨ a.val = 2))
              · exact kill_redundant (Sum.inr 10) (show (10 : ℕ) < 11 by omega) (fun x => by
                  rw [h11_eval x]
                  change (w0 x).getD 10 false = _
                  rw [hw0_read10 x]
                  rcases habsorb with ⟨ha10, hb0 | hb2⟩ | ⟨hb10, ha0 | ha2⟩
                  · rw [ha10, hb0, hw0_read10 x, show (w0 x).getD 0 false = x 0 from hw0_read x 0]
                    cases x 0 <;> cases x 2 <;> rfl
                  · rw [ha10, hb2, hw0_read10 x, show (w0 x).getD 2 false = x 2 from hw0_read x 2]
                    cases x 0 <;> cases x 2 <;> rfl
                  · rw [hb10, ha0, hw0_read10 x, show (w0 x).getD 0 false = x 0 from hw0_read x 0]
                    cases x 0 <;> cases x 2 <;> rfl
                  · rw [hb10, ha2, hw0_read10 x, show (w0 x).getD 2 false = x 2 from hw0_read x 2]
                    cases x 0 <;> cases x 2 <;> rfl)
              · by_cases ha10 : a.val = 10
                · have hb10 : b.val < 10 := by omega
                  let bf : Fin 10 := ⟨b.val, hb10⟩
                  have hb_ne0 : bf ≠ 0 := fun h => by have hv := congrArg Fin.val h; exact habsorb (Or.inl ⟨ha10, Or.inl hv⟩)
                  have hb_ne2 : bf ≠ 2 := fun h => by have hv := congrArg Fin.val h; exact habsorb (Or.inl ⟨ha10, Or.inr hv⟩)
                  obtain ⟨m, r, hr_mem, hmr⟩ := htriple_cov bf hb_ne0 hb_ne2
                  have hperm_b : permFin m bf = r := Fin.ext hmr
                  apply transport m (fun x => x r && (x 0 && x 2))
                  · intro x
                    rw [h11_eval (fun j => x (permFin m j)), ha10, hw0_read10,
                        show (w0 (fun j => x (permFin m j))).getD b.val false = x (permFin m bf) from hw0_read _ bf,
                        hperm_b, h02_perm m x, Bool.and_comm]
                  · intro D' hD'fan hD'sz
                    obtain ⟨x, hx⟩ := hTriple r hr_mem D' hD'fan hD'sz
                    exact ⟨x, by simpa only [w0, List.append_assoc, List.cons_append, List.nil_append] using hx⟩
                · by_cases hb10 : b.val = 10
                  · have ha10' : a.val < 10 := by omega
                    let af : Fin 10 := ⟨a.val, ha10'⟩
                    have ha_ne0 : af ≠ 0 := fun h => by have hv := congrArg Fin.val h; exact habsorb (Or.inr ⟨hb10, Or.inl hv⟩)
                    have ha_ne2 : af ≠ 2 := fun h => by have hv := congrArg Fin.val h; exact habsorb (Or.inr ⟨hb10, Or.inr hv⟩)
                    obtain ⟨m, r, hr_mem, hmr⟩ := htriple_cov af ha_ne0 ha_ne2
                    have hperm_a : permFin m af = r := Fin.ext hmr
                    apply transport m (fun x => x r && (x 0 && x 2))
                    · intro x
                      rw [h11_eval (fun j => x (permFin m j)), hb10, hw0_read10,
                          show (w0 (fun j => x (permFin m j))).getD a.val false = x (permFin m af) from hw0_read _ af,
                          hperm_a, h02_perm m x]
                    · intro D' hD'fan hD'sz
                      obtain ⟨x, hx⟩ := hTriple r hr_mem D' hD'fan hD'sz
                      exact ⟨x, by simpa only [w0, List.append_assoc, List.cons_append, List.nil_append] using hx⟩
                  · have ha10' : a.val < 10 := by omega
                    have hb10' : b.val < 10 := by omega
                    let af : Fin 10 := ⟨a.val, ha10'⟩
                    let bf : Fin 10 := ⟨b.val, hb10'⟩
                    have hab_ne : af ≠ bf := fun h => by have hv := congrArg Fin.val h; exact hab hv
                    have hne02 : ¬ (af = 0 ∧ bf = 2) := fun h => by
                      have h1 := congrArg Fin.val h.1; have h2 := congrArg Fin.val h.2; exact h02 (Or.inl ⟨h1, h2⟩)
                    have hne20 : ¬ (af = 2 ∧ bf = 0) := fun h => by
                      have h1 := congrArg Fin.val h.1; have h2 := congrArg Fin.val h.2; exact h02 (Or.inr ⟨h1, h2⟩)
                    rcases hpair_cov af bf hab_ne hne02 hne20 with ⟨m, p, hp_mem, hmp⟩ | ⟨m, p, hp_mem, hmp⟩
                    · apply transport m (fun x => x p.1 && x p.2)
                      · intro x
                        rw [h11_eval (fun j => x (permFin m j)),
                            show (w0 (fun j => x (permFin m j))).getD a.val false = x (permFin m af) from hw0_read _ af,
                            show (w0 (fun j => x (permFin m j))).getD b.val false = x (permFin m bf) from hw0_read _ bf]
                        rcases hmp with ⟨h1, h2⟩ | ⟨h1, h2⟩
                        · rw [show permFin m af = p.1 from Fin.ext h1, show permFin m bf = p.2 from Fin.ext h2]
                        · rw [show permFin m af = p.2 from Fin.ext h1, show permFin m bf = p.1 from Fin.ext h2, Bool.and_comm]
                      · intro D' hD'fan hD'sz
                        obtain ⟨x, hx⟩ := hEdge p hp_mem D' hD'fan hD'sz
                        exact ⟨x, by simpa only [w0, List.append_assoc, List.cons_append, List.nil_append] using hx⟩
                    · apply transport m (fun x => x p.1 && x p.2)
                      · intro x
                        rw [h11_eval (fun j => x (permFin m j)),
                            show (w0 (fun j => x (permFin m j))).getD a.val false = x (permFin m af) from hw0_read _ af,
                            show (w0 (fun j => x (permFin m j))).getD b.val false = x (permFin m bf) from hw0_read _ bf]
                        rcases hmp with ⟨h1, h2⟩ | ⟨h1, h2⟩
                        · rw [show permFin m af = p.1 from Fin.ext h1, show permFin m bf = p.2 from Fin.ext h2]
                        · rw [show permFin m af = p.2 from Fin.ext h1, show permFin m bf = p.1 from Fin.ext h2, Bool.and_comm]
                      · intro D' hD'fan hD'sz
                        obtain ⟨x, hx⟩ := hNonEdge p hp_mem D' hD'fan hD'sz
                        exact ⟨x, by simpa only [w0, List.append_assoc, List.cons_append, List.nil_append] using hx⟩
