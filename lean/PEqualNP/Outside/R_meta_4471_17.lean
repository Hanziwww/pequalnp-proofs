import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4471_17
    (hBase : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 4 || x 6]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hEdge : ∀ p ∈ ([(0, 1), (0, 4), (0, 5), (2, 7)] : List (Fin 9 × Fin 9)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 4 || x 6, x p.1 && x p.2]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hNonEdge : ∀ p ∈ ([(0, 2), (0, 3), (0, 6), (0, 7), (0, 8), (2, 4), (2, 5), (4, 6), (4, 7)] : List (Fin 9 × Fin 9)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 4 || x 6, x p.1 && x p.2]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hOrAnd : ∀ i ∈ ([0, 2, 7] : List (Fin 9)),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 4 || x 6, x i && (x 4 || x 6)]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 x2 : Fin (11 : ℕ)),   (11 : ℕ) * ↑x1 + ↑x2 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (10 : ℕ), (24 : ℕ), (26 : ℕ), (27 : ℕ), (29 : ℕ), (31 : ℕ), (32 : ℕ), (48 : ℕ), (50 : ℕ), (51 : ℕ), (53 : ℕ), (54 : ℕ), (84 : ℕ), (86 : ℕ), (87 : ℕ), (108 : ℕ), (109 : ℕ), (120 : ℕ)] →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))];             x4.eval (x8 ++ [x8.getD (↑x1) Bool.false && x8.getD (↑x2) Bool.false]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 hmem D hfan hsize
  let F : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let w0 (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 4 || x 6]
  have hw0_len (x : Fin 9 → Bool) : (w0 x).length = 10 := by
    simp only [w0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have hw0_read (x : Fin 9 → Bool) (i : Fin 9) : (w0 x).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hw0_read9 (x : Fin 9 → Bool) : (w0 x).getD 9 false = (x 4 || x 6) := by
    change (List.ofFn x ++ [x 4 || x 6]).getD 9 false = (x 4 || x 6)
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn]
    rfl
  have hw0_read10 (x : Fin 9 → Bool) : (w0 x).getD 10 false = false :=
    List.getD_eq_default (w0 x) false (n := 10) (by rw [hw0_len x])
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have run_len (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
    induction gs with
    | nil => intro w; simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro w
      change (run gs (step w g)).length = w.length + (g :: gs).length
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
      (run gs w).getD i false = w.getD i false := by
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (run gs (step w g)).getD i false = w.getD i false
      rw [ih (step w g) i (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default _ _ (by omega)]
  let sval (w : List Bool) : Bool ⊕ ℕ → Bool := Sum.elim id (fun j => w.getD j false)
  let svalid (m : ℕ) : Bool ⊕ ℕ → Prop := Sum.elim (fun _ => True) (fun j => j < m)
  let simpNot (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
    ins.casesOn (none, Sum.inl true) fun a _ =>
      a.elim (fun c => (none, Sum.inl (!c))) (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m))
  let simpAnd (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
    ins.casesOn (none, Sum.inl true) fun a t =>
      t.casesOn (none, a) fun b u =>
        u.casesOn
          (a.elim
            (fun c => b.elim (fun d => (none, Sum.inl (c && d)))
              (fun j => (none, bif c then Sum.inr j else Sum.inl false)))
            (fun j => b.elim (fun c => (none, bif c then Sum.inr j else Sum.inl false))
              (fun k => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m))))
          (fun _ _ => (none, Sum.inl false))
  let simpOr (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
    ins.casesOn (none, Sum.inl false) fun a t =>
      t.casesOn (none, a) fun b u =>
        u.casesOn
          (a.elim
            (fun c => b.elim (fun d => (none, Sum.inl (c || d)))
              (fun j => (none, bif c then Sum.inl true else Sum.inr j)))
            (fun j => b.elim (fun c => (none, bif c then Sum.inl true else Sum.inr j))
              (fun k => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m))))
          (fun _ _ => (none, Sum.inl false))
  let simplify (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
    GateOp.rec (simpAnd m ins) (simpOr m ins) (simpNot m ins)
      (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op
  have simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
      ∀ g ∈ (simplify op m ins).1.toList,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · cases hg
      · cases hg
      · cases a with
        | inl b1 =>
          cases b with
          | inl b2 => cases hg
          | inr j => cases b1 <;> cases hg
        | inr j =>
          cases b with
          | inl b2 => cases b2 <;> cases hg
          | inr k =>
            change g ∈ [⟨GateOp.and, [j, k]⟩] at hg
            simp only [List.mem_singleton] at hg
            subst hg
            exact ⟨Set.mem_insert _ _, by simp only [List.length_cons, List.length_nil]; omega⟩
      · cases hg
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · cases hg
      · cases hg
      · cases a with
        | inl b1 =>
          cases b with
          | inl b2 => cases hg
          | inr j => cases b1 <;> cases hg
        | inr j =>
          cases b with
          | inl b2 => cases b2 <;> cases hg
          | inr k =>
            change g ∈ [⟨GateOp.or, [j, k]⟩] at hg
            simp only [List.mem_singleton] at hg
            subst hg
            exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp only [List.length_cons, List.length_nil]; omega⟩
      · cases hg
    | not =>
      rcases ins with _ | ⟨a, l⟩
      · cases hg
      · cases a with
        | inl b1 => cases hg
        | inr j =>
          change g ∈ [⟨GateOp.not, [j]⟩] at hg
          simp only [List.mem_singleton] at hg
          subst hg
          exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp only [List.length_cons, List.length_nil]; omega⟩
    | mod _ => cases hg
    | maj => cases hg
  have simplify_sound (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, svalid w.length s) :
      svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      sval (run (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
        op.eval (ins.map (sval w)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl b1 => exact ⟨trivial, by change b1 = (b1 && true); exact (Bool.and_true b1).symm⟩
        | inr j => exact ⟨by change j < w.length + 0; have h1 : j < w.length := hv (Sum.inr j) List.mem_cons_self; omega, by change w.getD j false = (w.getD j false && true); exact (Bool.and_true _).symm⟩
      · cases a with
        | inl b1 =>
          cases b with
          | inl b2 => exact ⟨trivial, by change (b1 && b2) = (b1 && (b2 && true)); rw [Bool.and_true]⟩
          | inr j =>
            cases b1 with
            | false => exact ⟨trivial, rfl⟩
            | true => exact ⟨by change j < w.length + 0; have h1 : j < w.length := hv (Sum.inr j) (List.mem_cons_of_mem _ List.mem_cons_self); omega, by change w.getD j false = (true && (w.getD j false && true)); simp only [Bool.true_and, Bool.and_true]⟩
        | inr j =>
          cases b with
          | inl b2 =>
            cases b2 with
            | false => exact ⟨trivial, by change false = (w.getD j false && (false && true)); simp only [Bool.false_and, Bool.and_false]⟩
            | true => exact ⟨by change j < w.length + 0; have h1 : j < w.length := hv (Sum.inr j) List.mem_cons_self; omega, by change w.getD j false = (w.getD j false && (true && true)); simp only [Bool.and_true]⟩
          | inr k =>
            refine ⟨by change w.length < w.length + 1; omega, ?_⟩
            change (w ++ [w.getD j false && (w.getD k false && true)]).getD w.length false = (w.getD j false && (w.getD k false && true))
            exact getD_snoc_eq w _ false
      · simp only [List.length_cons] at hlen; omega
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl b1 => exact ⟨trivial, by change b1 = (b1 || false); exact (Bool.or_false b1).symm⟩
        | inr j => exact ⟨by change j < w.length + 0; have h1 : j < w.length := hv (Sum.inr j) List.mem_cons_self; omega, by change w.getD j false = (w.getD j false || false); exact (Bool.or_false _).symm⟩
      · cases a with
        | inl b1 =>
          cases b with
          | inl b2 => exact ⟨trivial, by change (b1 || b2) = (b1 || (b2 || false)); rw [Bool.or_false]⟩
          | inr j =>
            cases b1 with
            | false => exact ⟨by change j < w.length + 0; have h1 : j < w.length := hv (Sum.inr j) (List.mem_cons_of_mem _ List.mem_cons_self); omega, by change w.getD j false = (false || (w.getD j false || false)); simp only [Bool.false_or, Bool.or_false]⟩
            | true => exact ⟨trivial, rfl⟩
        | inr j =>
          cases b with
          | inl b2 =>
            cases b2 with
            | false => exact ⟨by change j < w.length + 0; have h1 : j < w.length := hv (Sum.inr j) List.mem_cons_self; omega, by change w.getD j false = (w.getD j false || (false || false)); simp only [Bool.or_false]⟩
            | true => exact ⟨trivial, by change true = (w.getD j false || (true || false)); simp only [Bool.true_or, Bool.or_true]⟩
          | inr k =>
            refine ⟨by change w.length < w.length + 1; omega, ?_⟩
            change (w ++ [w.getD j false || (w.getD k false || false)]).getD w.length false = (w.getD j false || (w.getD k false || false))
            exact getD_snoc_eq w _ false
      · simp only [List.length_cons] at hlen; omega
    · rcases ins with _ | ⟨a, l⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl b1 => exact ⟨trivial, rfl⟩
        | inr j =>
          refine ⟨by change w.length < w.length + 1; omega, ?_⟩
          change (w ++ [!(w.getD j false)]).getD w.length false = !(w.getD j false)
          exact getD_snoc_eq w _ false
  let elimStep (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
    let r := simplify g.op (10 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    (acc.1 ++ [r.2], acc.2 ++ r.1.toList)
  let elim (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : List (Bool ⊕ ℕ) × List Gate :=
    gs.foldl elimStep acc
  have elim_len (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
      (elim gs acc).2.length ≤ acc.2.length + gs.length := by
    induction gs with
    | nil => intro acc; simp only [elim, List.foldl_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    | cons g gs ih =>
      intro acc
      change (elim gs (elimStep acc g)).2.length ≤ acc.2.length + (g :: gs).length
      have h1 := ih (elimStep acc g)
      have h2 : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        cases (simplify g.op (10 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
        | none => simp only [Option.toList, List.length_nil]; omega
        | some _ => simp only [Option.toList, List.length_singleton]; omega
      simp only [List.length_cons]
      omega
  have elim_ok (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
      (∀ g ∈ acc.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ (elim gs acc).2,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h
      apply ih (elimStep acc g)
      intro g' hg'
      rcases List.mem_append.mp hg' with h1 | h2
      · exact h g' h1
      · exact simplify_ok _ _ _ g' h2
  let Inv (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
    w.length = 10 ∧ acc.1.length = z.length ∧
      ∀ k, svalid (10 + acc.2.length) (acc.1.getD k (Sum.inl false)) ∧
        sval (run acc.2 w) (acc.1.getD k (Sum.inl false)) = z.getD k false
  have elim_inv (gs : List Gate) : ∀ (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      Inv w z acc → Inv w (run gs z) (elim gs acc) := by
    induction gs with
    | nil => intro w z acc _ h; exact h
    | cons g gs ih =>
      intro w z acc hok hinv
      obtain ⟨hw, hlen, hagree⟩ := hinv
      have hg := hok g List.mem_cons_self
      let W := run acc.2 w
      have hWlen : W.length = 10 + acc.2.length := by
        dsimp only [W]
        rw [run_len, hw]
      let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
      let r := simplify g.op (10 + acc.2.length) ins
      have hsr := simplify_sound g.op hg.1 W ins (by simpa only [ins, List.length_map] using hg.2) (by
        intro s hs
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
        simpa only [hWlen] using (hagree i).1)
      have hreq : simplify g.op W.length ins = r := by rw [hWlen]
      rw [hreq] at hsr
      apply ih w (step z g) (elimStep acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      refine ⟨hw, by simp only [elimStep, step, List.length_append, List.length_cons, List.length_nil, hlen], ?_⟩
      intro k
      have hrun_app : run (acc.2 ++ r.1.toList) w = run r.1.toList W := by
        simp only [run, W, List.foldl_append]
      change svalid (10 + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD k (Sum.inl false)) ∧
        sval (run (acc.2 ++ r.1.toList) w) ((acc.1 ++ [r.2]).getD k (Sum.inl false)) = (step z g).getD k false
      by_cases hk : k = acc.1.length
      · subst hk
        rw [getD_snoc_eq, hrun_app]
        have hstepk : (step z g).getD acc.1.length false = g.op.eval (g.inputs.map fun i => z.getD i false) := by
          simp only [step, hlen, getD_snoc_eq]
        rw [hstepk]
        refine ⟨by simpa only [List.length_append, Nat.add_assoc, hWlen] using hsr.1, ?_⟩
        rw [hsr.2]
        congr 1
        simp only [ins, List.map_map, Function.comp_def]
        exact List.map_congr_left (fun i _ => (hagree i).2)
      · rw [getD_snoc_ne _ _ _ _ hk]
        have hstepk : (step z g).getD k false = z.getD k false :=
          getD_snoc_ne _ _ _ _ (by omega)
        rw [hstepk, hrun_app]
        have hvalid_old := (hagree k).1
        have hval_old := (hagree k).2
        cases hst : acc.1.getD k (Sum.inl false) with
        | inl b =>
          rw [hst] at hval_old
          exact ⟨trivial, hval_old⟩
        | inr j =>
          rw [hst] at hvalid_old hval_old
          change j < 10 + acc.2.length at hvalid_old
          refine ⟨by change j < 10 + (acc.2 ++ r.1.toList).length; simp only [List.length_append]; omega, ?_⟩
          change (run r.1.toList W).getD j false = z.getD k false
          rw [run_keep r.1.toList W j (by omega)]
          exact hval_old
  have kill_redundant (s1 : Bool ⊕ ℕ) (hs1v : svalid 10 s1)
      (hs1e : ∀ x : Fin 9 → Bool, sval (w0 x) s1 = ((w0 x).getD x1.val false && (w0 x).getD x2.val false)) :
      ∃ x : Fin 9 → Bool, D.eval (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]) ≠ F x := by
    by_contra hno
    have hagree (x : Fin 9 → Bool) :
        D.eval (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]) = F x := by
      by_contra hne
      exact hno ⟨x, hne⟩
    let M0 : List (Bool ⊕ ℕ) := (List.range 10).map Sum.inr ++ [s1]
    have hM0_len : M0.length = 11 := by
      simp only [M0, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    have hM0_lt (k : ℕ) (hk : k < 10) : M0.getD k (Sum.inl false) = Sum.inr k := by
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
    let res := elim D.gates (M0, [])
    have hbase (x : Fin 9 → Bool) :
        Inv (w0 x) (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]) (M0, []) := by
      refine ⟨hw0_len x, by simp only [hM0_len, List.length_append, hw0_len x, List.length_cons, List.length_nil], ?_⟩
      intro k
      by_cases hk : k < 10
      · rw [hM0_lt k hk]
        refine ⟨show k < 10 + 0 by omega, ?_⟩
        change (w0 x).getD k false = (w0 x ++ [_]).getD k false
        exact (List.getD_append _ _ _ _ (by rw [hw0_len x]; exact hk)).symm
      · by_cases hk10 : k = 10
        · subst hk10
          rw [hM0_10]
          have h10z : (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]).getD 10 false =
              ((w0 x).getD x1.val false && (w0 x).getD x2.val false) := by
            simpa only [hw0_len x] using getD_snoc_eq (w0 x) ((w0 x).getD x1.val false && (w0 x).getD x2.val false) false
          rw [h10z]
          exact ⟨by simpa only [List.length_nil, Nat.add_zero] using hs1v, hs1e x⟩
        · have hm : M0.getD k (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default M0 (Sum.inl false) (n := k) (by omega)
          have hz : (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]).getD k false = false :=
            List.getD_eq_default _ false (n := k) (by simp only [List.length_append, hw0_len x, List.length_cons, List.length_nil]; omega)
          rw [hm, hz]
          exact ⟨trivial, rfl⟩
    have hfin (x : Fin 9 → Bool) := elim_inv D.gates (w0 x)
      (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]) (M0, []) hfan (hbase x)
    cases hout : res.1.getD D.output (Sum.inl false) with
    | inl b =>
      have hf0 : b = F (fun _ => false) := by
        have h := ((hfin (fun _ => false)).2.2 D.output).2
        rw [hout] at h
        exact h.trans (hagree (fun _ => false))
      have hf1 : b = F (fun _ => true) := by
        have h := ((hfin (fun _ => true)).2.2 D.output).2
        rw [hout] at h
        exact h.trans (hagree (fun _ => true))
      have hne : F (fun _ => false) ≠ F (fun _ => true) := by decide
      exact hne (hf0.symm.trans hf1)
    | inr out =>
      let D' : Circuit := ⟨res.2, out⟩
      have hD'fan : FanInTwo D' := elim_ok D.gates (M0, []) (fun _ h => by cases h)
      have hD'sz : D'.size ≤ 13 := by
        have h := elim_len D.gates (M0, [])
        change (elim D.gates (M0, [])).2.length ≤ 13
        change D.gates.length ≤ 13 at hsize
        simp only [List.length_nil, Nat.zero_add] at h
        omega
      obtain ⟨x, hx⟩ := hBase D' hD'fan hD'sz
      have hev : D'.eval (w0 x) = F x := by
        have h := ((hfin x).2.2 D.output).2
        rw [hout] at h
        exact h.trans (hagree x)
      exact hx hev
  have kill_false (h10 : x1.val = 10 ∨ x2.val = 10) :=
    kill_redundant (Sum.inl false) trivial (fun x => by
      rcases h10 with h1 | h2
      · rw [h1, hw0_read10 x]; rfl
      · rw [h2, hw0_read10 x, Bool.and_false]; rfl)
  have kill_diag (heq : x1.val = x2.val) (hlt : x1.val < 10) :=
    kill_redundant (Sum.inr x1.val) (show x1.val < 10 by exact hlt) (fun x => by
      rw [← heq]
      exact (Bool.and_self _).symm)
  have kill_49 (h1 : x1.val = 4) (h2 : x2.val = 9) :=
    kill_redundant (Sum.inr 4) (show 4 < 10 by omega) (fun x => by
      rw [h1, h2, hw0_read9 x]
      change (w0 x).getD 4 false = ((w0 x).getD 4 false && (x 4 || x 6))
      rw [show (w0 x).getD 4 false = x 4 from hw0_read x 4]
      cases x 4 <;> cases x 6 <;> rfl)
  have kill_edge (a b : Fin 9) (hp : (a, b) ∈ ([(0, 1), (0, 4), (0, 5), (2, 7)] : List (Fin 9 × Fin 9)))
      (h1 : x1.val = a.val) (h2 : x2.val = b.val) :
      ∃ x : Fin 9 → Bool,
        have x8 : List Bool := List.ofFn x ++ [x 4 || x 6];
        D.eval (x8 ++ [x8.getD x1.val false && x8.getD x2.val false]) ≠ F x := by
    obtain ⟨x, hx⟩ := hEdge (a, b) hp D hfan hsize
    refine ⟨x, ?_⟩
    dsimp only
    change D.eval (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]) ≠ F x
    rw [h1, h2, hw0_read x a, hw0_read x b]
    simpa only [w0, List.append_assoc, List.cons_append, List.nil_append] using hx
  have kill_nonedge (a b : Fin 9)
      (hp : (a, b) ∈ ([(0, 2), (0, 3), (0, 6), (0, 7), (0, 8), (2, 4), (2, 5), (4, 6), (4, 7)] : List (Fin 9 × Fin 9)))
      (h1 : x1.val = a.val) (h2 : x2.val = b.val) :
      ∃ x : Fin 9 → Bool,
        have x8 : List Bool := List.ofFn x ++ [x 4 || x 6];
        D.eval (x8 ++ [x8.getD x1.val false && x8.getD x2.val false]) ≠ F x := by
    obtain ⟨x, hx⟩ := hNonEdge (a, b) hp D hfan hsize
    refine ⟨x, ?_⟩
    dsimp only
    change D.eval (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]) ≠ F x
    rw [h1, h2, hw0_read x a, hw0_read x b]
    simpa only [w0, List.append_assoc, List.cons_append, List.nil_append] using hx
  have kill_orand (i : Fin 9) (hi : i ∈ ([0, 2, 7] : List (Fin 9)))
      (h1 : x1.val = i.val) (h2 : x2.val = 9) :
      ∃ x : Fin 9 → Bool,
        have x8 : List Bool := List.ofFn x ++ [x 4 || x 6];
        D.eval (x8 ++ [x8.getD x1.val false && x8.getD x2.val false]) ≠ F x := by
    obtain ⟨x, hx⟩ := hOrAnd i hi D hfan hsize
    refine ⟨x, ?_⟩
    dsimp only
    change D.eval (w0 x ++ [(w0 x).getD x1.val false && (w0 x).getD x2.val false]) ≠ F x
    rw [h1, h2, hw0_read x i, hw0_read9 x]
    simpa only [w0, List.append_assoc, List.cons_append, List.nil_append] using hx
  have hx1 : x1.val < 11 := x1.isLt
  have hx2 : x2.val < 11 := x2.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact kill_diag (by omega) (by omega)
  · exact kill_edge 0 1 (by decide) (by omega) (by omega)
  · exact kill_nonedge 0 2 (by decide) (by omega) (by omega)
  · exact kill_nonedge 0 3 (by decide) (by omega) (by omega)
  · exact kill_edge 0 4 (by decide) (by omega) (by omega)
  · exact kill_edge 0 5 (by decide) (by omega) (by omega)
  · exact kill_nonedge 0 6 (by decide) (by omega) (by omega)
  · exact kill_nonedge 0 7 (by decide) (by omega) (by omega)
  · exact kill_nonedge 0 8 (by decide) (by omega) (by omega)
  · exact kill_orand 0 (by decide) (by omega) (by omega)
  · exact kill_false (Or.inr (by omega))
  · exact kill_diag (by omega) (by omega)
  · exact kill_nonedge 2 4 (by decide) (by omega) (by omega)
  · exact kill_nonedge 2 5 (by decide) (by omega) (by omega)
  · exact kill_edge 2 7 (by decide) (by omega) (by omega)
  · exact kill_orand 2 (by decide) (by omega) (by omega)
  · exact kill_false (Or.inr (by omega))
  · exact kill_diag (by omega) (by omega)
  · exact kill_nonedge 4 6 (by decide) (by omega) (by omega)
  · exact kill_nonedge 4 7 (by decide) (by omega) (by omega)
  · exact kill_49 (by omega) (by omega)
  · exact kill_false (Or.inr (by omega))
  · exact kill_diag (by omega) (by omega)
  · exact kill_orand 7 (by decide) (by omega) (by omega)
  · exact kill_false (Or.inr (by omega))
  · exact kill_diag (by omega) (by omega)
  · exact kill_false (Or.inr (by omega))
  · exact kill_false (Or.inl (by omega))
