import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3273_17
    (hFirstNot :
      ∀ a ∈ ([1, 2, 3, 4, 6] : List ℕ),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0]
          D.eval (w ++ [!w.getD a false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFirstAndEdge :
      ∀ p ∈ ([(0, 1), (0, 4), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4)] : List (ℕ × ℕ)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0]
          D.eval (w ++ [w.getD p.1 false && w.getD p.2 false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFirstAndOther :
      ∀ a b : ℕ, a < b → b < 10 →
      (a, b) ∉ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8), (0, 9)] : List (ℕ × ℕ)) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0]
          D.eval (w ++ [w.getD a false && w.getD b false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFirstOr :
      ∀ a b : ℕ, a < b → b < 10 → (a, b) ≠ (0, 9) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := List.ofFn x ++ [!x 0]
          D.eval (w ++ [w.getD a false || w.getD b false]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
             x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (0 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((9 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((10 : Fin (12 : ℕ)), (10 : Fin (12 : ℕ))), ((11 : Fin (12 : ℕ)), (11 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let p9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let w0 : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0]
  have hw0_len (x : Fin 9 → Bool) : (w0 x).length = 10 := by
    simp only [w0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have hw0_read (x : Fin 9 → Bool) (i : Fin 9) : (w0 x).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simp only [List.length_ofFn]; exact i.isLt
    dsimp only [w0]
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hw0_read0 (x : Fin 9 → Bool) : (w0 x).getD 0 false = x 0 := hw0_read x 0
  have hw0_read9 (x : Fin 9 → Bool) : (w0 x).getD 9 false = !x 0 := by
    have h9 : (List.ofFn x).length = 9 := List.length_ofFn
    dsimp only [w0]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [h9, Nat.sub_self, List.getD_cons_zero]
  have hw0_read_ge (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) : (w0 x).getD i false = false :=
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
    let r := simplify g.op (10 + acc.2.length) ins
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
        cases (simplify g.op (10 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
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
      · exact simplify_ok g.op (10 + acc.2.length) _ g' h2
  let Inv : List Bool → List Bool → List (Bool ⊕ ℕ) × List Gate → Prop := fun w z acc =>
    w.length = 10 ∧ acc.1.length = z.length ∧
    ∀ i, svalid (10 + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
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
      have hw'len : w'.length = 10 + acc.2.length := by
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
      have heq_r : simplify g.op (10 + acc.2.length) ins = r := by rw [← hw'len]
      refine ⟨hwl, ?_, ?_⟩
      · simp only [elimStep, step, List.length_append, hml, List.length_cons, List.length_nil]
      · intro i
        dsimp only [elimStep]
        change svalid (10 + (acc.2 ++ (simplify g.op (10 + acc.2.length) ins).1.toList).length)
            ((acc.1 ++ [(simplify g.op (10 + acc.2.length) ins).2]).getD i (Sum.inl false)) ∧
          sval (run (acc.2 ++ (simplify g.op (10 + acc.2.length) ins).1.toList) w)
            ((acc.1 ++ [(simplify g.op (10 + acc.2.length) ins).2]).getD i (Sum.inl false)) =
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
  have reduce10 (E : Circuit) (hE : FanInTwo E) (val : (Fin 9 → Bool) → Bool)
      (s1 : Bool ⊕ ℕ) (hs1v : svalid 10 s1) (hs1e : ∀ x : Fin 9 → Bool, sval (w0 x) s1 = val x) :
      (∃ x : Fin 9 → Bool, E.eval (w0 x ++ [val x]) ≠ p9 x) ∨
      (∃ D' : Circuit, FanInTwo D' ∧ D'.size ≤ E.size ∧
        ∀ x : Fin 9 → Bool, D'.eval (w0 x) = E.eval (w0 x ++ [val x])) := by
    let M0 : List (Bool ⊕ ℕ) := (List.range 10).map (Sum.inr : ℕ → Bool ⊕ ℕ) ++ [s1]
    have hM0_len : M0.length = 11 := by
      simp only [M0, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    have hM0_lt (j : ℕ) (hj : j < 10) : M0.getD j (Sum.inl false) = Sum.inr j := by
      have hrl : ((List.range 10).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = 10 := by
        simp only [List.length_map, List.length_range]
      dsimp only [M0]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
          List.getElem_map, List.getElem_range]
    have hM0_10 : M0.getD 10 (Sum.inl false) = s1 := by
      have hrl : ((List.range 10).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = 10 := by
        simp only [List.length_map, List.length_range]
      dsimp only [M0]
      simpa only [hrl] using getD_snoc_eq ((List.range 10).map (Sum.inr : ℕ → Bool ⊕ ℕ)) s1 (Sum.inl false)
    let res := elim E.gates (M0, [])
    have hbase (x : Fin 9 → Bool) : Inv (w0 x) (w0 x ++ [val x]) (M0, []) := by
      refine ⟨hw0_len x, by simp only [hM0_len, List.length_append, hw0_len x, List.length_cons, List.length_nil], ?_⟩
      intro j
      by_cases hj : j < 10
      · rw [hM0_lt j hj]
        refine ⟨show j < 10 + 0 by omega, ?_⟩
        change (w0 x).getD j false = (w0 x ++ [val x]).getD j false
        exact (List.getD_append _ _ _ _ (by rw [hw0_len x]; exact hj)).symm
      · by_cases hj10 : j = 10
        · subst hj10
          rw [hM0_10]
          have h10z : (w0 x ++ [val x]).getD 10 false = val x := by
            simpa only [hw0_len x] using getD_snoc_eq (w0 x) (val x) false
          rw [h10z]
          exact ⟨by simpa only [List.length_nil, Nat.add_zero] using hs1v, hs1e x⟩
        · have hm : M0.getD j (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default M0 (Sum.inl false) (n := j) (by omega)
          have hz : (w0 x ++ [val x]).getD j false = false :=
            List.getD_eq_default _ false (n := j) (by simp only [List.length_append, hw0_len x, List.length_cons, List.length_nil]; omega)
          rw [hm, hz]
          exact ⟨trivial, rfl⟩
    have hfin (x : Fin 9 → Bool) := elim_inv E.gates (w0 x) (w0 x ++ [val x]) (M0, []) hE (hbase x)
    cases hout : res.1.getD E.output (Sum.inl false) with
    | inl b =>
      left
      cases b with
      | false =>
        refine ⟨fun _ => true, ?_⟩
        have h := ((hfin (fun _ => true)).2.2 E.output).2
        rw [hout] at h
        rw [hp9_true]
        change (run E.gates (w0 (fun _ => true) ++ [val (fun _ => true)])).getD E.output false ≠ true
        rw [← h]
        change false ≠ true
        decide
      | true =>
        refine ⟨fun _ => false, ?_⟩
        have h := ((hfin (fun _ => false)).2.2 E.output).2
        rw [hout] at h
        rw [hp9_false]
        change (run E.gates (w0 (fun _ => false) ++ [val (fun _ => false)])).getD E.output false ≠ false
        rw [← h]
        change true ≠ false
        decide
    | inr out =>
      right
      refine ⟨⟨res.2, out⟩, elim_ok E.gates (M0, []) (fun _ h => by cases h), ?_, ?_⟩
      · have h := elim_len E.gates (M0, [])
        change (elim E.gates (M0, [])).2.length ≤ E.gates.length
        simp only [List.length_nil, Nat.zero_add] at h
        exact h
      · intro x
        have h := ((hfin x).2.2 E.output).2
        rw [hout] at h
        exact h
  let σ : ℕ → ℕ := fun w => ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ).getD w w
  let σf : Fin 9 → Fin 9 := fun i => ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List (Fin 9)).getD i.val i
  have hσ_val : ∀ i : Fin 9, (σf i).val = σ i.val := by decide
  have hσf_inv : ∀ i : Fin 9, σf (σf i) = i := by decide
  have hσ_inv9 : ∀ i : Fin 9, σ (σ i.val) = i.val := by decide
  have hσ_ge (w : ℕ) (hw : 9 ≤ w) : σ w = w :=
    List.getD_eq_default ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) w (n := w) hw
  have hσ_inv (w : ℕ) : σ (σ w) = w := by
    by_cases hw : w < 9
    · exact hσ_inv9 ⟨w, hw⟩
    · rw [hσ_ge w (by omega), hσ_ge w (by omega)]
  have hσ_lt10_fin : ∀ i : Fin 10, σ i.val < 10 := by decide
  have hσ_lt10 (w : ℕ) (hw : w < 10) : σ w < 10 := hσ_lt10_fin ⟨w, hw⟩
  have hσ_ge10 (w : ℕ) (hw : 10 ≤ w) : σ w = w := hσ_ge w (by omega)
  have hσ_9 : σ 9 = 9 := rfl
  have hσf_0 : σf 0 = 0 := rfl
  have hw0_σ (x : Fin 9 → Bool) (w : ℕ) : (w0 (fun i => x (σf i))).getD w false = (w0 x).getD (σ w) false := by
    by_cases hw9 : w < 9
    · let wf : Fin 9 := ⟨w, hw9⟩
      change (w0 (fun i => x (σf i))).getD wf.val false = (w0 x).getD (σ wf.val) false
      rw [hw0_read _ wf, ← hσ_val wf, hw0_read _ (σf wf)]
    · by_cases heq9 : w = 9
      · subst heq9
        rw [hw0_read9, hσ_9, hw0_read9, hσf_0]
      · rw [hw0_read_ge _ w (by omega), hσ_ge10 w (by omega), hw0_read_ge _ w (by omega)]
  let edges : List (Fin 9 × Fin 9) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
  have hp9_iff (y : Fin 9 → Bool) : p9 y = true ↔ ∃ e ∈ edges, y e.1 = true ∧ y e.2 = true := by
    dsimp only [p9, edges]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left, or_assoc]
  have hedges_σ : ∀ e ∈ edges, (σf e.1, σf e.2) ∈ edges ∨ (σf e.2, σf e.1) ∈ edges := by decide
  have hp9_σ_imp (y : Fin 9 → Bool) (h : p9 (fun i => y (σf i)) = true) : p9 y = true := by
    obtain ⟨e, he, h1, h2⟩ := (hp9_iff (fun i => y (σf i))).mp h
    apply (hp9_iff y).mpr
    rcases hedges_σ e he with hm | hm
    · exact ⟨(σf e.1, σf e.2), hm, h1, h2⟩
    · exact ⟨(σf e.2, σf e.1), hm, h2, h1⟩
  have hp9_σ (x : Fin 9 → Bool) : p9 (fun i => x (σf i)) = p9 x := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hp9_σ_imp x
    · intro h
      apply hp9_σ_imp (fun i => x (σf i))
      have heq : (fun i => x (σf (σf i))) = x := funext (fun i => congrArg x (hσf_inv i))
      rwa [heq]
  let mapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map σ⟩
  let mapCirc : Circuit → Circuit := fun E => ⟨E.gates.map mapGate, σ E.output⟩
  have mapCirc_fan (E : Circuit) (hE : FanInTwo E) : FanInTwo (mapCirc E) := by
    intro g' hg'
    change g' ∈ E.gates.map mapGate at hg'
    rw [List.mem_map] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    have h := hE g hg
    exact ⟨h.1, by simp only [mapGate, List.length_map]; exact h.2⟩
  have mapCirc_size (E : Circuit) : (mapCirc E).size = E.size := by
    change (E.gates.map mapGate).length = E.gates.length
    exact List.length_map _
  have run_σ (gs : List Gate) (w1 w2 : List Bool) (hlen : w1.length = w2.length) (h10 : 10 ≤ w1.length)
      (hrel : ∀ i, w2.getD i false = w1.getD (σ i) false) :
      ∀ i, (run (gs.map mapGate) w2).getD i false = (run gs w1).getD (σ i) false := by
    induction gs generalizing w1 w2 with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hvals : ((mapGate g).inputs.map fun j => w2.getD j false) =
          (g.inputs.map fun j => w1.getD j false) := by
        dsimp only [mapGate]
        rw [List.map_map]
        apply List.map_congr_left
        intro j _
        dsimp only [Function.comp_apply]
        rw [hrel (σ j), hσ_inv j]
      have heval : (mapGate g).op.eval ((mapGate g).inputs.map fun j => w2.getD j false) =
          g.op.eval (g.inputs.map fun j => w1.getD j false) := congrArg g.op.eval hvals
      apply ih (step w1 g) (step w2 (mapGate g))
      · simp only [step, List.length_append, hlen, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        dsimp only [step]
        rw [heval]
        by_cases hi : i = w1.length
        · subst hi
          have hσl : σ w1.length = w1.length := hσ_ge10 w1.length h10
          rw [hσl, getD_snoc_eq w1 _ false, hlen, getD_snoc_eq w2 _ false]
        · have hi2 : i ≠ w2.length := by omega
          have hσi : σ i ≠ w1.length := by
            intro heq
            have h1 : i = σ w1.length := by rw [← heq, hσ_inv i]
            rw [hσ_ge10 w1.length h10] at h1
            exact hi h1
          rw [getD_snoc_ne w2 _ false i hi2, getD_snoc_ne w1 _ false (σ i) hσi]
          exact hrel i
  have apply_σ (E : Circuit) (v1 v2 : (Fin 9 → Bool) → Bool)
      (hv : ∀ y : Fin 9 → Bool, v1 (fun i => y (σf i)) = v2 y)
      (h : ∃ y : Fin 9 → Bool, (mapCirc E).eval (w0 y ++ [v2 y]) ≠ p9 y) :
      ∃ x : Fin 9 → Bool, E.eval (w0 x ++ [v1 x]) ≠ p9 x := by
    obtain ⟨y, hy⟩ := h
    let x : Fin 9 → Bool := fun i => y (σf i)
    refine ⟨x, ?_⟩
    have hrel : ∀ i, (w0 y ++ [v2 y]).getD i false = (w0 x ++ [v1 x]).getD (σ i) false := by
      intro i
      by_cases hi : i < 10
      · have hσi : σ i < 10 := hσ_lt10 i hi
        rw [List.getD_append (w0 y) [v2 y] _ _ (by rw [hw0_len y]; exact hi),
            List.getD_append (w0 x) [v1 x] _ _ (by rw [hw0_len x]; exact hσi)]
        dsimp only [x]
        rw [hw0_σ y (σ i), hσ_inv i]
      · by_cases hi10 : i = 10
        · subst hi10
          have hσ10 : σ 10 = 10 := hσ_ge10 10 (Nat.le_refl 10)
          rw [hσ10]
          have hl1 : (w0 y ++ [v2 y]).getD 10 false = v2 y := by
            simpa only [hw0_len y] using getD_snoc_eq (w0 y) (v2 y) false
          have hl2 : (w0 x ++ [v1 x]).getD 10 false = v1 x := by
            simpa only [hw0_len x] using getD_snoc_eq (w0 x) (v1 x) false
          rw [hl1, hl2, hv y]
        · have hσi : σ i = i := hσ_ge10 i (by omega)
          rw [hσi,
              List.getD_eq_default _ false (n := i) (by simp only [List.length_append, hw0_len y, List.length_cons, List.length_nil]; omega),
              List.getD_eq_default _ false (n := i) (by simp only [List.length_append, hw0_len x, List.length_cons, List.length_nil]; omega)]
    have hev : (mapCirc E).eval (w0 y ++ [v2 y]) = E.eval (w0 x ++ [v1 x]) := by
      have hlen : (w0 x ++ [v1 x]).length = (w0 y ++ [v2 y]).length := by
        simp only [List.length_append, hw0_len, List.length_cons, List.length_nil]
      have h10 : 10 ≤ (w0 x ++ [v1 x]).length := by
        simp only [List.length_append, hw0_len, List.length_cons, List.length_nil]; omega
      have hr := run_σ E.gates (w0 x ++ [v1 x]) (w0 y ++ [v2 y]) hlen h10 hrel (σ E.output)
      rw [hσ_inv E.output] at hr
      exact hr
    rw [← hev, hp9_σ y]
    exact hy
  let edgeReps : List (ℕ × ℕ) := [(0, 1), (0, 4), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4)]
  let allEdges : List (ℕ × ℕ) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8)]
  have hedge_cov : ∀ e ∈ allEdges, e ∈ edgeReps ∨ (σ e.1, σ e.2) ∈ edgeReps ∨ (σ e.2, σ e.1) ∈ edgeReps := by
    decide
  have hnot_cov : ∀ i : Fin 10, i.val ≠ 0 → i.val ≠ 9 →
      i.val ∈ ([1, 2, 3, 4, 6] : List ℕ) ∨ σ i.val ∈ ([1, 2, 3, 4, 6] : List ℕ) := by decide
  have hmain : ∀ k : ℕ, k ≤ 13 → ∀ C : Circuit, FanInTwo C → C.size = k →
      ∃ x : Fin 9 → Bool, C.eval (w0 x) ≠ p9 x := by
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
        have kill_redundant (s1 : Bool ⊕ ℕ) (hs1v : svalid 10 s1)
            (hs1e : ∀ x : Fin 9 → Bool, sval (w0 x) s1 = val0 x) :
            ∃ x : Fin 9 → Bool, C.eval (w0 x) ≠ p9 x := by
          rcases reduce10 D hDfan val0 s1 hs1v hs1e with ⟨x, hx⟩ | ⟨D', hD'fan, hD'sz, hD'eq⟩
          · refine ⟨x, ?_⟩
            rw [hC_eval x]
            exact hx
          · have hD'lt : D'.size < k := by
              have h1 : D'.size ≤ gs.length := hD'sz
              omega
            obtain ⟨x, hx⟩ := ih D'.size hD'lt (by omega) D' hD'fan rfl
            refine ⟨x, ?_⟩
            rw [hC_eval x, ← hD'eq x]
            exact hx
        rcases hg0.1 with hop_and | hop_or | hop_not
        · cases hins : g0.inputs with
          | nil =>
            exact kill_redundant (Sum.inl true) trivial (fun _ => by dsimp only [val0]; rw [hop_and, hins]; rfl)
          | cons a t =>
            cases t with
            | nil =>
              by_cases ha10 : a < 10
              · exact kill_redundant (Sum.inr a) ha10 (fun x => by
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
                by_cases hoob : 10 ≤ a ∨ 10 ≤ b
                · exact kill_redundant (Sum.inl false) trivial (fun x => by
                    rw [hval_and x]
                    rcases hoob with ha | hb
                    · rw [hw0_read_ge x a ha]; rfl
                    · rw [hw0_read_ge x b hb, Bool.and_false]; rfl)
                · by_cases hab : a = b
                  · exact kill_redundant (Sum.inr a) (show a < 10 by omega) (fun x => by
                      rw [hval_and x, ← hab]
                      exact (Bool.and_self _).symm)
                  · let p : ℕ := if a < b then a else b
                    let q : ℕ := if a < b then b else a
                    have hpq : p < q := by dsimp only [p, q]; split_ifs <;> omega
                    have hq10 : q < 10 := by dsimp only [q]; split_ifs <;> omega
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
                    · by_cases hedge : (p, q) ∈ allEdges
                      · rcases hedge_cov (p, q) hedge with hrep | hσ1 | hσ2
                        · obtain ⟨x, hx⟩ := hFirstAndEdge (p, q) hrep D hDfan hDsz
                          refine ⟨x, ?_⟩
                          rw [hC_eval x, hval_pq x]
                          exact hx
                        · have hres := apply_σ D
                            (fun x => (w0 x).getD p false && (w0 x).getD q false)
                            (fun y => (w0 y).getD (σ p) false && (w0 y).getD (σ q) false)
                            (fun y => by rw [hw0_σ y p, hw0_σ y q])
                            (hFirstAndEdge (σ p, σ q) hσ1 (mapCirc D) (mapCirc_fan D hDfan) (by rw [mapCirc_size]; exact hDsz))
                          obtain ⟨x, hx⟩ := hres
                          refine ⟨x, ?_⟩
                          rw [hC_eval x, hval_pq x]
                          exact hx
                        · have hres := apply_σ D
                            (fun x => (w0 x).getD p false && (w0 x).getD q false)
                            (fun y => (w0 y).getD (σ q) false && (w0 y).getD (σ p) false)
                            (fun y => by rw [hw0_σ y p, hw0_σ y q, Bool.and_comm])
                            (hFirstAndEdge (σ q, σ p) hσ2 (mapCirc D) (mapCirc_fan D hDfan) (by rw [mapCirc_size]; exact hDsz))
                          obtain ⟨x, hx⟩ := hres
                          refine ⟨x, ?_⟩
                          rw [hC_eval x, hval_pq x]
                          exact hx
                      · have hnotmem : (p, q) ∉ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8), (0, 9)] : List (ℕ × ℕ)) := by
                          intro hmem
                          have hmem' : (p, q) ∈ allEdges ++ [(0, 9)] := hmem
                          rw [List.mem_append] at hmem'
                          rcases hmem' with h1 | h2
                          · exact hedge h1
                          · simp only [List.mem_singleton, Prod.mk.injEq] at h2
                            exact h09 h2
                        obtain ⟨x, hx⟩ := hFirstAndOther p q hpq hq10 hnotmem D hDfan hDsz
                        refine ⟨x, ?_⟩
                        rw [hC_eval x, hval_pq x]
                        exact hx
        · cases hins : g0.inputs with
          | nil =>
            exact kill_redundant (Sum.inl false) trivial (fun _ => by dsimp only [val0]; rw [hop_or, hins]; rfl)
          | cons a t =>
            cases t with
            | nil =>
              by_cases ha10 : a < 10
              · exact kill_redundant (Sum.inr a) ha10 (fun x => by
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
                by_cases ha10 : a < 10
                · by_cases hb10 : b < 10
                  · by_cases hab : a = b
                    · exact kill_redundant (Sum.inr a) ha10 (fun x => by
                        rw [hval_or x, ← hab]
                        exact (Bool.or_self _).symm)
                    · let p : ℕ := if a < b then a else b
                      let q : ℕ := if a < b then b else a
                      have hpq : p < q := by dsimp only [p, q]; split_ifs <;> omega
                      have hq10 : q < 10 := by dsimp only [q]; split_ifs <;> omega
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
                      · have hne09 : (p, q) ≠ (0, 9) := by
                          intro h
                          exact h09 (Prod.mk.inj h)
                        obtain ⟨x, hx⟩ := hFirstOr p q hpq hq10 hne09 D hDfan hDsz
                        refine ⟨x, ?_⟩
                        rw [hC_eval x, hval_pq x]
                        exact hx
                  · exact kill_redundant (Sum.inr a) ha10 (fun x => by
                      rw [hval_or x, hw0_read_ge x b (by omega), Bool.or_false]; rfl)
                · by_cases hb10 : b < 10
                  · exact kill_redundant (Sum.inr b) hb10 (fun x => by
                      rw [hval_or x, hw0_read_ge x a (by omega), Bool.false_or]; rfl)
                  · exact kill_redundant (Sum.inl false) trivial (fun x => by
                      rw [hval_or x, hw0_read_ge x a (by omega), hw0_read_ge x b (by omega)]; rfl)
        · cases hins : g0.inputs with
          | nil =>
            exact kill_redundant (Sum.inl true) trivial (fun _ => by dsimp only [val0]; rw [hop_not, hins]; rfl)
          | cons a t =>
            have hval_not (x : Fin 9 → Bool) : val0 x = !(w0 x).getD a false := by
              dsimp only [val0]; rw [hop_not, hins]; rfl
            by_cases ha10 : a < 10
            · by_cases ha0 : a = 0
              · exact kill_redundant (Sum.inr 9) (show (9 : ℕ) < 10 by omega) (fun x => by
                  rw [hval_not x, ha0]
                  change (w0 x).getD 9 false = !(w0 x).getD 0 false
                  rw [hw0_read9 x, hw0_read0 x])
              · by_cases ha9 : a = 9
                · exact kill_redundant (Sum.inr 0) (show (0 : ℕ) < 10 by omega) (fun x => by
                    rw [hval_not x, ha9]
                    change (w0 x).getD 0 false = !(w0 x).getD 9 false
                    rw [hw0_read0 x, hw0_read9 x]
                    cases x 0 <;> rfl)
                · rcases hnot_cov ⟨a, ha10⟩ ha0 ha9 with ha_mem | hσa_mem
                  · obtain ⟨x, hx⟩ := hFirstNot a ha_mem D hDfan hDsz
                    refine ⟨x, ?_⟩
                    rw [hC_eval x, hval_not x]
                    exact hx
                  · have hres := apply_σ D
                      (fun x => !(w0 x).getD a false)
                      (fun y => !(w0 y).getD (σ a) false)
                      (fun y => by rw [hw0_σ y a])
                      (hFirstNot (σ a) hσa_mem (mapCirc D) (mapCirc_fan D hDfan) (by rw [mapCirc_size]; exact hDsz))
                    obtain ⟨x, hx⟩ := hres
                    refine ⟨x, ?_⟩
                    rw [hC_eval x, hval_not x]
                    exact hx
            · exact kill_redundant (Sum.inl true) trivial (fun x => by
                rw [hval_not x, hw0_read_ge x a (by omega)]; rfl)
  intro x1 hx1 C hCfan hCsz
  have hdiag : x1.1 = x1.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
    rcases hx1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  let val1 : (Fin 9 → Bool) → Bool := fun x6 =>
    let x8 : Fin 12 → Bool := fun i => if i = (11 : Fin 12) then true else (w0 x6).getD i.val false
    x8 x1.1 && x8 x1.2
  have hval1_eq (x : Fin 9 → Bool) :
      val1 x = (if x1.1 = (11 : Fin 12) then true else (w0 x).getD x1.1.val false) := by
    dsimp only [val1]
    rw [← hdiag]
    exact Bool.and_self _
  have hred : ∃ s1 : Bool ⊕ ℕ, svalid 10 s1 ∧ ∀ x : Fin 9 → Bool, sval (w0 x) s1 = val1 x := by
    by_cases h11 : x1.1 = (11 : Fin 12)
    · refine ⟨Sum.inl true, trivial, fun x => ?_⟩
      rw [hval1_eq x, h11]; rfl
    · by_cases hlt10 : x1.1.val < 10
      · refine ⟨Sum.inr x1.1.val, hlt10, fun x => ?_⟩
        rw [hval1_eq x, ite_eq_right_iff.mpr (fun h => absurd h h11)]; rfl
      · refine ⟨Sum.inl false, trivial, fun x => ?_⟩
        rw [hval1_eq x, ite_eq_right_iff.mpr (fun h => absurd h h11), hw0_read_ge x x1.1.val (by omega)]; rfl
  obtain ⟨s1, hs1v, hs1e⟩ := hred
  rcases reduce10 C hCfan val1 s1 hs1v hs1e with ⟨x, hx⟩ | ⟨D', hD'fan, hD'sz, hD'eq⟩
  · exact ⟨x, hx⟩
  · obtain ⟨x, hx⟩ := hmain D'.size (Nat.le_trans hD'sz hCsz) D' hD'fan rfl
    refine ⟨x, ?_⟩
    change C.eval (w0 x ++ [val1 x]) ≠ p9 x
    rw [← hD'eq x]
    exact hx
