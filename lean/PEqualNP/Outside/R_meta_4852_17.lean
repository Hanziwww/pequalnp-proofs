import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4852_17
    (hFirstNot :
      ∀ a ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 10] : List ℕ),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0, x 1 || x 3]
          D.eval (w ++ [!w.getD a false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFirstAndEdge :
      ∀ p ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8)] : List (ℕ × ℕ)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0, x 1 || x 3]
          D.eval (w ++ [w.getD p.1 false && w.getD p.2 false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFirstAndOther :
      ∀ a b : ℕ, a < b → b < 11 →
      (a, b) ∉ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8), (0, 9), (1, 10), (3, 10)] : List (ℕ × ℕ)) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0, x 1 || x 3]
          D.eval (w ++ [w.getD a false && w.getD b false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFirstOr :
      ∀ a b : ℕ, a < b → b < 11 →
      (a, b) ∉ ([(0, 9), (1, 3), (1, 10), (3, 10)] : List (ℕ × ℕ)) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0, x 1 || x 3]
          D.eval (w ++ [w.getD a false || w.getD b false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ)), x4 (1 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ))]) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  let p9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let w0 : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0, x 1 || x 3]
  have hw0_len (x : Fin 9 → Bool) : (w0 x).length = 11 := by
    simp only [w0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have hw0_read (x : Fin 9 → Bool) (i : Fin 9) : (w0 x).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simp only [List.length_ofFn]; exact i.isLt
    dsimp only [w0]
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hw0_read0 (x : Fin 9 → Bool) : (w0 x).getD 0 false = x 0 := hw0_read x 0
  have hw0_read1 (x : Fin 9 → Bool) : (w0 x).getD 1 false = x 1 := hw0_read x 1
  have hw0_read3 (x : Fin 9 → Bool) : (w0 x).getD 3 false = x 3 := hw0_read x 3
  have hw0_read9 (x : Fin 9 → Bool) : (w0 x).getD 9 false = !x 0 := by
    have h9 : (List.ofFn x).length = 9 := List.length_ofFn
    dsimp only [w0]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [h9, Nat.sub_self, List.getD_cons_zero]
  have hw0_read10 (x : Fin 9 → Bool) : (w0 x).getD 10 false = (x 1 || x 3) := by
    have h9 : (List.ofFn x).length = 9 := List.length_ofFn
    dsimp only [w0]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [h9, show 10 - 9 = 1 from rfl, List.getD_cons_succ, List.getD_cons_zero]
  have hw0_read_ge (x : Fin 9 → Bool) (i : ℕ) (hi : 11 ≤ i) : (w0 x).getD i false = false :=
    List.getD_eq_default (w0 x) false (n := i) (by rw [hw0_len x]; exact hi)
  have hp9_false : p9 (fun _ => false) = false := by dsimp only [p9]; decide
  have hp9_true : p9 (fun _ => true) = true := by dsimp only [p9]; decide
  have hp9_onehot : ∀ k : Fin 9, p9 (fun i => decide (i = k)) = false := by dsimp only [p9]; decide
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
  have hnot_cov : ∀ i : Fin 11, i.val ≠ 0 → i.val ≠ 9 → i.val ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 10] : List ℕ) := by decide
  suffices hmain : ∀ k : ℕ, k ≤ 13 → ∀ C : Circuit, FanInTwo C → C.size = k →
      ∃ x : Fin 9 → Bool, C.eval (w0 x) ≠ p9 x by
    intro C hfan hsize
    exact hmain C.size hsize C hfan rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk C hfan hsize
    cases hgs : C.gates with
    | nil =>
      have hC_nil (x : Fin 9 → Bool) : C.eval (w0 x) = (w0 x).getD C.output false := by
        change (run C.gates (w0 x)).getD C.output false = (w0 x).getD C.output false
        rw [hgs]; rfl
      by_cases hlt9 : C.output < 9
      · let jf : Fin 9 := ⟨C.output, hlt9⟩
        refine ⟨fun i => decide (i = jf), ?_⟩
        rw [hC_nil, hw0_read _ jf, hp9_onehot jf, decide_eq_true rfl]
        decide
      · by_cases heq9 : C.output = 9
        · refine ⟨fun _ => false, ?_⟩
          rw [hC_nil, heq9, hw0_read9, hp9_false]
          decide
        · by_cases heq10 : C.output = 10
          · refine ⟨fun i => decide (i = 1), ?_⟩
            rw [hC_nil, heq10, hw0_read10, hp9_onehot 1]
            decide
          · refine ⟨fun _ => true, ?_⟩
            rw [hC_nil, hw0_read_ge _ C.output (by omega), hp9_true]
            decide
    | cons g0 gs =>
      let D : Circuit := ⟨gs, C.output⟩
      have hDfan : FanInTwo D := fun g hg => hfan g (by rw [hgs]; exact List.mem_cons_of_mem g0 hg)
      have hDlen : gs.length + 1 = k := by
        have h : C.gates.length = k := hsize
        rw [hgs, List.length_cons] at h
        exact h
      have hDsz : D.size ≤ 12 := by
        change gs.length ≤ 12
        omega
      have hg0 : g0.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g0.inputs.length ≤ 2 :=
        hfan g0 (by rw [hgs]; exact List.mem_cons_self)
      let val0 : (Fin 9 → Bool) → Bool := fun x => g0.op.eval (g0.inputs.map fun i => (w0 x).getD i false)
      have hC_eval (x : Fin 9 → Bool) : C.eval (w0 x) = D.eval (w0 x ++ [val0 x]) := by
        change (run C.gates (w0 x)).getD C.output false = (run gs (w0 x ++ [val0 x])).getD C.output false
        rw [hgs]; rfl
      have kill_redundant (s1 : Bool ⊕ ℕ) (hs1v : svalid 11 s1)
          (hs1e : ∀ x : Fin 9 → Bool, sval (w0 x) s1 = val0 x) :
          ∃ x : Fin 9 → Bool, C.eval (w0 x) ≠ p9 x := by
        let M0 : List (Bool ⊕ ℕ) := (List.range 11).map (Sum.inr : ℕ → Bool ⊕ ℕ) ++ [s1]
        have hM0_len : M0.length = 12 := by
          simp only [M0, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
        have hM0_lt (j : ℕ) (hj : j < 11) : M0.getD j (Sum.inl false) = Sum.inr j := by
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
        let res := elim gs (M0, [])
        have hbase (x : Fin 9 → Bool) : Inv (w0 x) (w0 x ++ [val0 x]) (M0, []) := by
          refine ⟨hw0_len x, by simp only [hM0_len, List.length_append, hw0_len x, List.length_cons, List.length_nil], ?_⟩
          intro j
          by_cases hj : j < 11
          · rw [hM0_lt j hj]
            refine ⟨show j < 11 + 0 by omega, ?_⟩
            change (w0 x).getD j false = (w0 x ++ [val0 x]).getD j false
            exact (List.getD_append _ _ _ _ (by rw [hw0_len x]; exact hj)).symm
          · by_cases hj11 : j = 11
            · subst hj11
              rw [hM0_11]
              have h11z : (w0 x ++ [val0 x]).getD 11 false = val0 x := by
                simpa only [hw0_len x] using getD_snoc_eq (w0 x) (val0 x) false
              rw [h11z]
              exact ⟨by simpa only [List.length_nil, Nat.add_zero] using hs1v, hs1e x⟩
            · have hm : M0.getD j (Sum.inl false) = Sum.inl false :=
                List.getD_eq_default M0 (Sum.inl false) (n := j) (by omega)
              have hz : (w0 x ++ [val0 x]).getD j false = false :=
                List.getD_eq_default _ false (n := j) (by simp only [List.length_append, hw0_len x, List.length_cons, List.length_nil]; omega)
              rw [hm, hz]
              exact ⟨trivial, rfl⟩
        have hfin (x : Fin 9 → Bool) := elim_inv gs (w0 x) (w0 x ++ [val0 x]) (M0, []) hDfan (hbase x)
        cases hout : res.1.getD C.output (Sum.inl false) with
        | inl b =>
          cases b with
          | false =>
            refine ⟨fun _ => true, ?_⟩
            have h := ((hfin (fun _ => true)).2.2 C.output).2
            rw [hout] at h
            rw [hC_eval (fun _ => true), hp9_true]
            change (run gs (w0 (fun _ => true) ++ [val0 (fun _ => true)])).getD C.output false ≠ true
            rw [← h]
            change false ≠ true
            decide
          | true =>
            refine ⟨fun _ => false, ?_⟩
            have h := ((hfin (fun _ => false)).2.2 C.output).2
            rw [hout] at h
            rw [hC_eval (fun _ => false), hp9_false]
            change (run gs (w0 (fun _ => false) ++ [val0 (fun _ => false)])).getD C.output false ≠ false
            rw [← h]
            change true ≠ false
            decide
        | inr out =>
          let D' : Circuit := ⟨res.2, out⟩
          have hD'fan : FanInTwo D' := elim_ok gs (M0, []) (fun _ h => by cases h)
          have hD'lt : D'.size < k := by
            have h := elim_len gs (M0, [])
            change (elim gs (M0, [])).2.length < k
            simp only [List.length_nil, Nat.zero_add] at h
            omega
          obtain ⟨x, hx⟩ := ih D'.size hD'lt (by omega) D' hD'fan rfl
          refine ⟨x, ?_⟩
          have h := ((hfin x).2.2 C.output).2
          rw [hout] at h
          rw [hC_eval x]
          exact fun heq => hx (h.trans heq)
      rcases hg0.1 with hop_and | hop_or | hop_not
      · cases hins : g0.inputs with
        | nil =>
          exact kill_redundant (Sum.inl true) trivial (fun _ => by dsimp only [val0]; rw [hop_and, hins]; rfl)
        | cons a t =>
          cases t with
          | nil =>
            by_cases ha11 : a < 11
            · exact kill_redundant (Sum.inr a) ha11 (fun x => by
                dsimp only [val0]; rw [hop_and, hins]
                change (w0 x).getD a false = ((w0 x).getD a false && true)
                exact (Bool.and_true _).symm)
            · exact kill_redundant (Sum.inl false) trivial (fun x => by
                dsimp only [val0]; rw [hop_and, hins]
                change false = ((w0 x).getD a false && true)
                rw [hw0_read_ge x a (by omega)]; rfl)
          | cons b t2 =>
            cases t2 with
            | cons _ _ =>
              have hlen := hg0.2
              rw [hins] at hlen
              simp only [List.length_cons] at hlen
              omega
            | nil =>
              have hval_and (x : Fin 9 → Bool) : val0 x = ((w0 x).getD a false && (w0 x).getD b false) := by
                dsimp only [val0]; rw [hop_and, hins]
                change ((w0 x).getD a false && ((w0 x).getD b false && true)) = _
                rw [Bool.and_true]
              by_cases hoob : 11 ≤ a ∨ 11 ≤ b
              · exact kill_redundant (Sum.inl false) trivial (fun x => by
                  rw [hval_and x]
                  rcases hoob with ha | hb
                  · rw [hw0_read_ge x a ha]; rfl
                  · rw [hw0_read_ge x b hb, Bool.and_false]; rfl)
              · by_cases hab : a = b
                · exact kill_redundant (Sum.inr a) (show a < 11 by omega) (fun x => by
                    rw [hval_and x, ← hab]
                    exact (Bool.and_self _).symm)
                · let p : ℕ := if a < b then a else b
                  let q : ℕ := if a < b then b else a
                  have hpq : p < q := by dsimp only [p, q]; split_ifs <;> omega
                  have hq11 : q < 11 := by dsimp only [q]; split_ifs <;> omega
                  have hval_pq (x : Fin 9 → Bool) : val0 x = ((w0 x).getD p false && (w0 x).getD q false) := by
                    rw [hval_and x]
                    dsimp only [p, q]
                    split_ifs
                    · rfl
                    · exact Bool.and_comm _ _
                  by_cases h09 : p = 0 ∧ q = 9
                  · exact kill_redundant (Sum.inl false) trivial (fun x => by
                      rw [hval_pq x, h09.1, h09.2, hw0_read0 x, hw0_read9 x]
                      cases x 0 <;> rfl)
                  · by_cases h110 : p = 1 ∧ q = 10
                    · exact kill_redundant (Sum.inr 1) (show (1 : ℕ) < 11 by omega) (fun x => by
                        rw [hval_pq x, h110.1, h110.2]
                        change (w0 x).getD 1 false = ((w0 x).getD 1 false && (w0 x).getD 10 false)
                        rw [hw0_read1 x, hw0_read10 x]
                        cases x 1 <;> cases x 3 <;> rfl)
                    · by_cases h310 : p = 3 ∧ q = 10
                      · exact kill_redundant (Sum.inr 3) (show (3 : ℕ) < 11 by omega) (fun x => by
                          rw [hval_pq x, h310.1, h310.2]
                          change (w0 x).getD 3 false = ((w0 x).getD 3 false && (w0 x).getD 10 false)
                          rw [hw0_read3 x, hw0_read10 x]
                          cases x 1 <;> cases x 3 <;> rfl)
                      · by_cases hedge : (p, q) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8)] : List (ℕ × ℕ))
                        · obtain ⟨x, hx⟩ := hFirstAndEdge (p, q) hedge D hDfan hDsz
                          refine ⟨x, ?_⟩
                          rw [hC_eval x, hval_pq x]
                          exact hx
                        · have hnotmem : (p, q) ∉ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8), (0, 9), (1, 10), (3, 10)] : List (ℕ × ℕ)) := by
                            intro hmem
                            have hmem' : (p, q) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8)] : List (ℕ × ℕ)) ++ [(0, 9), (1, 10), (3, 10)] := hmem
                            rw [List.mem_append] at hmem'
                            rcases hmem' with h1 | h2
                            · exact hedge h1
                            · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h2
                              rcases h2 with h | h | h
                              · exact h09 h
                              · exact h110 h
                              · exact h310 h
                          obtain ⟨x, hx⟩ := hFirstAndOther p q hpq hq11 hnotmem D hDfan hDsz
                          refine ⟨x, ?_⟩
                          rw [hC_eval x, hval_pq x]
                          exact hx
      · cases hins : g0.inputs with
        | nil =>
          exact kill_redundant (Sum.inl false) trivial (fun _ => by dsimp only [val0]; rw [hop_or, hins]; rfl)
        | cons a t =>
          cases t with
          | nil =>
            by_cases ha11 : a < 11
            · exact kill_redundant (Sum.inr a) ha11 (fun x => by
                dsimp only [val0]; rw [hop_or, hins]
                change (w0 x).getD a false = ((w0 x).getD a false || false)
                exact (Bool.or_false _).symm)
            · exact kill_redundant (Sum.inl false) trivial (fun x => by
                dsimp only [val0]; rw [hop_or, hins]
                change false = ((w0 x).getD a false || false)
                rw [hw0_read_ge x a (by omega)]; rfl)
          | cons b t2 =>
            cases t2 with
            | cons _ _ =>
              have hlen := hg0.2
              rw [hins] at hlen
              simp only [List.length_cons] at hlen
              omega
            | nil =>
              have hval_or (x : Fin 9 → Bool) : val0 x = ((w0 x).getD a false || (w0 x).getD b false) := by
                dsimp only [val0]; rw [hop_or, hins]
                change ((w0 x).getD a false || ((w0 x).getD b false || false)) = _
                rw [Bool.or_false]
              by_cases ha11 : a < 11
              · by_cases hb11 : b < 11
                · by_cases hab : a = b
                  · exact kill_redundant (Sum.inr a) ha11 (fun x => by
                      rw [hval_or x, ← hab]
                      exact (Bool.or_self _).symm)
                  · let p : ℕ := if a < b then a else b
                    let q : ℕ := if a < b then b else a
                    have hpq : p < q := by dsimp only [p, q]; split_ifs <;> omega
                    have hq11 : q < 11 := by dsimp only [q]; split_ifs <;> omega
                    have hval_pq (x : Fin 9 → Bool) : val0 x = ((w0 x).getD p false || (w0 x).getD q false) := by
                      rw [hval_or x]
                      dsimp only [p, q]
                      split_ifs
                      · rfl
                      · exact Bool.or_comm _ _
                    by_cases h09 : p = 0 ∧ q = 9
                    · exact kill_redundant (Sum.inl true) trivial (fun x => by
                        rw [hval_pq x, h09.1, h09.2, hw0_read0 x, hw0_read9 x]
                        cases x 0 <;> rfl)
                    · by_cases h13 : p = 1 ∧ q = 3
                      · exact kill_redundant (Sum.inr 10) (show (10 : ℕ) < 11 by omega) (fun x => by
                          rw [hval_pq x, h13.1, h13.2]
                          change (w0 x).getD 10 false = ((w0 x).getD 1 false || (w0 x).getD 3 false)
                          rw [hw0_read10 x, hw0_read1 x, hw0_read3 x])
                      · by_cases h110 : p = 1 ∧ q = 10
                        · exact kill_redundant (Sum.inr 10) (show (10 : ℕ) < 11 by omega) (fun x => by
                            rw [hval_pq x, h110.1, h110.2]
                            change (w0 x).getD 10 false = ((w0 x).getD 1 false || (w0 x).getD 10 false)
                            rw [hw0_read10 x, hw0_read1 x]
                            cases x 1 <;> cases x 3 <;> rfl)
                        · by_cases h310 : p = 3 ∧ q = 10
                          · exact kill_redundant (Sum.inr 10) (show (10 : ℕ) < 11 by omega) (fun x => by
                              rw [hval_pq x, h310.1, h310.2]
                              change (w0 x).getD 10 false = ((w0 x).getD 3 false || (w0 x).getD 10 false)
                              rw [hw0_read10 x, hw0_read3 x]
                              cases x 1 <;> cases x 3 <;> rfl)
                          · have hnotmem : (p, q) ∉ ([(0, 9), (1, 3), (1, 10), (3, 10)] : List (ℕ × ℕ)) := by
                              intro hmem
                              simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
                              rcases hmem with h | h | h | h
                              · exact h09 h
                              · exact h13 h
                              · exact h110 h
                              · exact h310 h
                            obtain ⟨x, hx⟩ := hFirstOr p q hpq hq11 hnotmem D hDfan hDsz
                            refine ⟨x, ?_⟩
                            rw [hC_eval x, hval_pq x]
                            exact hx
                · exact kill_redundant (Sum.inr a) ha11 (fun x => by
                    rw [hval_or x, hw0_read_ge x b (by omega), Bool.or_false]; rfl)
              · by_cases hb11 : b < 11
                · exact kill_redundant (Sum.inr b) hb11 (fun x => by
                    rw [hval_or x, hw0_read_ge x a (by omega), Bool.false_or]; rfl)
                · exact kill_redundant (Sum.inl false) trivial (fun x => by
                    rw [hval_or x, hw0_read_ge x a (by omega), hw0_read_ge x b (by omega)]; rfl)
      · cases hins : g0.inputs with
        | nil =>
          exact kill_redundant (Sum.inl true) trivial (fun _ => by dsimp only [val0]; rw [hop_not, hins]; rfl)
        | cons a t =>
          have hval_not (x : Fin 9 → Bool) : val0 x = !(w0 x).getD a false := by
            dsimp only [val0]; rw [hop_not, hins]; rfl
          by_cases ha11 : a < 11
          · by_cases ha0 : a = 0
            · exact kill_redundant (Sum.inr 9) (show (9 : ℕ) < 11 by omega) (fun x => by
                rw [hval_not x, ha0]
                change (w0 x).getD 9 false = !(w0 x).getD 0 false
                rw [hw0_read9 x, hw0_read0 x])
            · by_cases ha9 : a = 9
              · exact kill_redundant (Sum.inr 0) (show (0 : ℕ) < 11 by omega) (fun x => by
                  rw [hval_not x, ha9]
                  change (w0 x).getD 0 false = !(w0 x).getD 9 false
                  rw [hw0_read0 x, hw0_read9 x]
                  cases x 0 <;> rfl)
              · have ha_mem : a ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 10] : List ℕ) :=
                  hnot_cov ⟨a, ha11⟩ ha0 ha9
                obtain ⟨x, hx⟩ := hFirstNot a ha_mem D hDfan hDsz
                refine ⟨x, ?_⟩
                rw [hC_eval x, hval_not x]
                exact hx
          · exact kill_redundant (Sum.inl true) trivial (fun x => by
              rw [hval_not x, hw0_read_ge x a (by omega)]; rfl)
