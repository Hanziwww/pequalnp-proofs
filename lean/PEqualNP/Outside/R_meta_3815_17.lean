import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3815_17
    (baseline : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (gate1Not : ∀ w ∈ ([0, 1, 3, 4, 6, 8, 9] : List ℕ), ∀ D : Circuit,
      Monotone2 D → D.size = 13 → D.output < 24 →
      (∀ x : Fin 9 → Bool,
        let v : List Bool := List.ofFn x ++ [x 0 || x 2]
        D.eval (v ++ [!(v.getD w false)]) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
           x 6 && x 8 || x 8 && x 5)) → False)
    (gate1OrTriple : ∀ c ∈ ([1, 3, 4, 6, 8] : List (Fin 9)), ∀ D : Circuit,
      FanInTwo D → D.size = 13 → D.output < 24 → notCount D = 1 →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 2, x 0 || x 2 || x c]) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
           x 6 && x 8 || x 8 && x 5)) → False)
    (gate1OrPair : ∀ p ∈ ([(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8),
        (1, 3), (1, 4), (1, 6), (1, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8),
        (4, 6), (4, 7), (4, 8), (6, 8)] : List (ℕ × ℕ)), ∀ D : Circuit,
      FanInTwo D → D.size = 13 → D.output < 24 → notCount D = 1 →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 2, x (Fin.ofNat 9 p.1) || x (Fin.ofNat 9 p.2)]) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
           x 6 && x 8 || x 8 && x 5)) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length), ↑x3 ≠ (0 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → x4 = x3) → (¬∃ (x4 : Fin x1.gates.length), ↑x4 = (1 : ℕ) ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hfan hnot hnoand hw9 hfun
  let f : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  have hfeval (x : Fin 9 → Bool) : C.eval (List.ofFn x) = f x := congrFun hfun x
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
  have ofFn_read_nat (x : Fin 9 → Bool) (ys : List Bool) (i : ℕ) (hi : i < 9) :
      (List.ofFn x ++ ys).getD i false = x ⟨i, hi⟩ := by
    have hlt : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  have ofFn_read (x : Fin 9 → Bool) (ys : List Bool) (i : Fin 9) :
      (List.ofFn x ++ ys).getD i.val false = x i :=
    ofFn_read_nat x ys i.val i.isLt
  by_contra hlt
  have hle15 : C.size ≤ 15 := by omega
  by_cases hle14 : C.size ≤ 14
  · let sh (i : ℕ) : ℕ := if i < 9 then i else i + 1
    let shGate (g : Gate) : Gate := ⟨g.op, g.inputs.map sh⟩
    let C' : Circuit := ⟨C.gates.map shGate, sh C.output⟩
    have sh_run (gs : List Gate) : ∀ (w v : List Bool),
        9 ≤ w.length → v.length = w.length + 1 →
        (∀ i, v.getD (sh i) false = w.getD i false) →
        ∀ i, (run (gs.map shGate) v).getD (sh i) false = (run gs w).getD i false := by
      induction gs with
      | nil => intro w v _ _ h i; exact h i
      | cons g gs ih =>
        intro w v hw hlen h i
        change (run (gs.map shGate) (step v (shGate g))).getD (sh i) false =
          (run gs (step w g)).getD i false
        have hval : (shGate g).op.eval ((shGate g).inputs.map fun j => v.getD j false) =
            g.op.eval (g.inputs.map fun j => w.getD j false) := by
          simp only [shGate, List.map_map, Function.comp_def, h]
        apply ih (step w g) (step v (shGate g))
          (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
          (by simp only [step, List.length_append, List.length_cons, List.length_nil, hlen])
        intro j
        by_cases hj : j = w.length
        · subst hj
          have hsh : sh w.length = v.length := by
            simp only [sh, show ¬ w.length < 9 by omega, ↓reduceIte, hlen]
          simp only [step, hval, hsh, getD_snoc_eq]
        · have hjv : sh j ≠ v.length := by
            dsimp only [sh]
            split <;> omega
          simp only [step]
          rw [getD_snoc_ne _ _ _ _ hjv, getD_snoc_ne _ _ _ _ hj]
          exact h j
    have hfan' : FanInTwo C' := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g0 hg0).1, by simpa only [shGate, List.length_map] using (hfan g0 hg0).2⟩
    have heval' (x : Fin 9 → Bool) : C'.eval (List.ofFn x ++ [false]) = f x := by
      rw [← hfeval x]
      apply sh_run C.gates (List.ofFn x) (List.ofFn x ++ [false])
        (by simp only [List.length_ofFn]; omega)
        (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
      intro i
      by_cases hi : i < 9
      · simp only [sh, hi, ↓reduceIte]
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hi)]
      · simp only [sh, hi, ↓reduceIte]
        rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
    have h15 := baseline C' hfan' heval'
    have hsz' : C'.size = C.size := by
      change (C.gates.map shGate).length = C.gates.length
      exact List.length_map shGate
    omega
  have hsz15 : C.gates.length = 15 := by
    change C.gates.length ≤ 15 at hle15
    change ¬ C.gates.length ≤ 14 at hle14
    omega
  rcases hgs : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp only [hgs, List.length_nil] at hsz15; omega
  · simp only [hgs, List.length_cons, List.length_nil] at hsz15; omega
  have hrest_len : rest.length = 13 := by
    simp only [hgs, List.length_cons] at hsz15
    omega
  let v10 (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]
  have v10_read (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : (v10 x).getD i false = x ⟨i, hi⟩ :=
    ofFn_read_nat x [x 0 || x 2] i hi
  have hstep0 (x : Fin 9 → Bool) : step (List.ofFn x) g0 = v10 x := by
    have hkeep := run_keep (g1 :: rest) (step (List.ofFn x) g0) 9
      (by simp only [step, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)
    have hw : (C.wires (List.ofFn x)).getD 9 false = (step (List.ofFn x) g0).getD 9 false := by
      change (run C.gates (List.ofFn x)).getD 9 false = _
      rw [hgs]
      exact hkeep
    have hval0 : g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
      have h9 := hw9 x
      rw [hw] at h9
      have hsnoc := getD_snoc_eq (List.ofFn x) (g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)) false
      rw [List.length_ofFn] at hsnoc
      exact hsnoc.symm.trans h9
    change List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)] = List.ofFn x ++ [x 0 || x 2]
    rw [hval0]
  let val1 (x : Fin 9 → Bool) : Bool := g1.op.eval (g1.inputs.map fun i => (v10 x).getD i false)
  let D0 : Circuit := ⟨rest, C.output⟩
  have hD0_eval (x : Fin 9 → Bool) : D0.eval (v10 x ++ [val1 x]) = f x := by
    have h := hfeval x
    change (run C.gates (List.ofFn x)).getD C.output false = f x at h
    rw [hgs] at h
    change (run rest (step (step (List.ofFn x) g0) g1)).getD C.output false = f x at h
    rw [hstep0 x] at h
    exact h
  have hD0_fan : FanInTwo D0 := by
    intro g hg
    exact hfan g (by rw [hgs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
  have hD0_out : D0.output < 24 := by
    by_contra hge
    have htrue := hD0_eval (fun _ => true)
    have hlen : (D0.wires (v10 (fun _ => true) ++ [val1 (fun _ => true)])).length = 24 := by
      change (run rest _).length = 24
      rw [run_len]
      simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil, hrest_len]
    have hfalse : D0.eval (v10 (fun _ => true) ++ [val1 (fun _ => true)]) = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hfalse] at htrue
    exact Bool.false_ne_true (htrue.trans (by decide))
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
    let r := simplify g.op (11 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
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
        cases (simplify g.op (11 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
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
  let Inv (w0 z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
    w0.length = 11 ∧ acc.1.length = z.length ∧
      ∀ k, svalid (11 + acc.2.length) (acc.1.getD k (Sum.inl false)) ∧
        sval (run acc.2 w0) (acc.1.getD k (Sum.inl false)) = z.getD k false
  have elim_inv (gs : List Gate) : ∀ (w0 z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      Inv w0 z acc → Inv w0 (run gs z) (elim gs acc) := by
    induction gs with
    | nil => intro w0 z acc _ h; exact h
    | cons g gs ih =>
      intro w0 z acc hok hinv
      obtain ⟨hw0, hlen, hagree⟩ := hinv
      have hg := hok g List.mem_cons_self
      let W := run acc.2 w0
      have hWlen : W.length = 11 + acc.2.length := by
        dsimp only [W]
        rw [run_len, hw0]
      let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
      let r := simplify g.op (11 + acc.2.length) ins
      have hsr := simplify_sound g.op hg.1 W ins (by simpa only [ins, List.length_map] using hg.2) (by
        intro s hs
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
        simpa only [hWlen] using (hagree i).1)
      have hreq : simplify g.op W.length ins = r := by rw [hWlen]
      rw [hreq] at hsr
      apply ih w0 (step z g) (elimStep acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      refine ⟨hw0, by simp only [elimStep, step, List.length_append, List.length_cons, List.length_nil, hlen], ?_⟩
      intro k
      have hrun_app : run (acc.2 ++ r.1.toList) w0 = run r.1.toList W := by
        simp only [run, W, List.foldl_append]
      change svalid (11 + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD k (Sum.inl false)) ∧
        sval (run (acc.2 ++ r.1.toList) w0) ((acc.1 ++ [r.2]).getD k (Sum.inl false)) = (step z g).getD k false
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
          change j < 11 + acc.2.length at hvalid_old
          refine ⟨by change j < 11 + (acc.2 ++ r.1.toList).length; simp only [List.length_append]; omega, ?_⟩
          change (run r.1.toList W).getD j false = z.getD k false
          rw [run_keep r.1.toList W j (by omega)]
          exact hval_old
  have kill_redundant (s1 : Bool ⊕ ℕ) (hs1v : svalid 11 s1)
      (hs1e : ∀ x : Fin 9 → Bool, sval (List.ofFn x ++ [false, x 0 || x 2]) s1 = val1 x) : False := by
    let M0 : List (Bool ⊕ ℕ) :=
      [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5,
       Sum.inr 6, Sum.inr 7, Sum.inr 8, Sum.inr 10, s1]
    let res := elim rest (M0, [])
    have hbase (x : Fin 9 → Bool) :
        Inv (List.ofFn x ++ [false, x 0 || x 2]) (v10 x ++ [val1 x]) (M0, []) := by
      have hv10_eq : v10 x ++ [val1 x] = List.ofFn x ++ [x 0 || x 2, val1 x] := by
        simp only [v10, List.append_assoc, List.cons_append, List.nil_append]
      refine ⟨by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil],
        by simp only [M0, v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil], ?_⟩
      intro k
      by_cases hk : k < 11
      · interval_cases k
        · exact ⟨show 0 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 0 (by omega)).trans (ofFn_read_nat x _ 0 (by omega)).symm⟩
        · exact ⟨show 1 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 1 (by omega)).trans (ofFn_read_nat x _ 1 (by omega)).symm⟩
        · exact ⟨show 2 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 2 (by omega)).trans (ofFn_read_nat x _ 2 (by omega)).symm⟩
        · exact ⟨show 3 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 3 (by omega)).trans (ofFn_read_nat x _ 3 (by omega)).symm⟩
        · exact ⟨show 4 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 4 (by omega)).trans (ofFn_read_nat x _ 4 (by omega)).symm⟩
        · exact ⟨show 5 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 5 (by omega)).trans (ofFn_read_nat x _ 5 (by omega)).symm⟩
        · exact ⟨show 6 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 6 (by omega)).trans (ofFn_read_nat x _ 6 (by omega)).symm⟩
        · exact ⟨show 7 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 7 (by omega)).trans (ofFn_read_nat x _ 7 (by omega)).symm⟩
        · exact ⟨show 8 < 11 by omega, by rw [hv10_eq]; exact (ofFn_read_nat x _ 8 (by omega)).trans (ofFn_read_nat x _ 8 (by omega)).symm⟩
        · refine ⟨show 10 < 11 by omega, ?_⟩
          rw [hv10_eq]
          change (List.ofFn x ++ [false, x 0 || x 2]).getD 10 false = (List.ofFn x ++ [x 0 || x 2, val1 x]).getD 9 false
          rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega),
              List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
          simp only [List.length_ofFn]
          rfl
        · refine ⟨hs1v, ?_⟩
          have h10m : M0.getD 10 (Sum.inl false) = s1 := rfl
          have h10z : (v10 x ++ [val1 x]).getD 10 false = val1 x := by
            have hl : (v10 x).length = 10 := by
              simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
            simpa only [hl] using getD_snoc_eq (v10 x) (val1 x) false
          rw [h10m, h10z]
          exact hs1e x
      · have hm : M0.getD k (Sum.inl false) = Sum.inl false :=
          List.getD_eq_default _ _ (by simp only [M0, List.length_cons, List.length_nil]; omega)
        have hz : (v10 x ++ [val1 x]).getD k false = false :=
          List.getD_eq_default _ _ (by simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)
        rw [hm, hz]
        exact ⟨trivial, rfl⟩
    have hfin (x : Fin 9 → Bool) := elim_inv rest (List.ofFn x ++ [false, x 0 || x 2])
      (v10 x ++ [val1 x]) (M0, []) hD0_fan (hbase x)
    cases hout : res.1.getD C.output (Sum.inl false) with
    | inl b =>
      have hf0 : b = f (fun _ => false) := by
        have h := ((hfin (fun _ => false)).2.2 C.output).2
        rw [hout] at h
        exact h.trans (hD0_eval (fun _ => false))
      have hf1 : b = f (fun _ => true) := by
        have h := ((hfin (fun _ => true)).2.2 C.output).2
        rw [hout] at h
        exact h.trans (hD0_eval (fun _ => true))
      have hne : f (fun _ => false) ≠ f (fun _ => true) := by decide
      exact hne (hf0.symm.trans hf1)
    | inr out =>
      let g0' : Gate := ⟨GateOp.or, [0, 2]⟩
      let E : Circuit := ⟨g0' :: res.2, out⟩
      have hEfan : FanInTwo E := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp only [g0', List.length_cons, List.length_nil]; omega⟩
        · exact elim_ok rest (M0, []) (fun _ h => by cases h) g hg
      have hEeval (x : Fin 9 → Bool) : E.eval (List.ofFn x ++ [false]) = f x := by
        have hst0 : step (List.ofFn x ++ [false]) g0' = List.ofFn x ++ [false, x 0 || x 2] := by
          change (List.ofFn x ++ [false]) ++
            [((List.ofFn x ++ [false]).getD 0 false || ((List.ofFn x ++ [false]).getD 2 false || false))] = _
          rw [ofFn_read_nat x [false] 0 (by omega), ofFn_read_nat x [false] 2 (by omega), Bool.or_false]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          rfl
        change (run res.2 (step (List.ofFn x ++ [false]) g0')).getD out false = f x
        rw [hst0]
        have h := ((hfin x).2.2 C.output).2
        rw [hout] at h
        exact h.trans (hD0_eval x)
      have h15 := baseline E hEfan hEeval
      have hlen : res.2.length ≤ 13 := by
        have h := elim_len rest (M0, [])
        simp only [List.length_nil, Nat.zero_add, hrest_len] at h
        exact h
      change 15 ≤ (g0' :: res.2).length at h15
      simp only [List.length_cons] at h15
      omega
  let τ : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]
  have hτ2 : τ 2 = 0 := rfl
  have hτ5 : τ 5 = 3 := rfl
  have hτ7 : τ 7 = 4 := rfl
  have hτ_sym (x : Fin 9 → Bool) : f (x ∘ τ) = f x := by
    change (x 2 && x 1 || x 1 && x 0 || x 0 && x 5 || x 5 && x 7 || x 7 && x 2 ||
      x 2 && x 3 || x 1 && x 6 || x 0 && x 4 || x 5 && x 8 || x 3 && x 4 ||
      x 6 && x 8 || x 8 && x 3) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5)
    simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  have hτ_or02 (x : Fin 9 → Bool) : ((x ∘ τ) 0 || (x ∘ τ) 2) = (x 0 || x 2) := by
    change (x 2 || x 0) = (x 0 || x 2)
    exact Bool.or_comm _ _
  let ρ (i : ℕ) : ℕ := if h : i < 9 then (τ ⟨i, h⟩).val else i
  have hρ_small (i : ℕ) (hi : i < 9) : ρ i < 9 := by
    simp only [ρ, hi, ↓reduceDIte]
    exact (τ ⟨i, hi⟩).isLt
  have hρ_fix (i : ℕ) (hi : 9 ≤ i) : ρ i = i := by
    simp only [ρ, show ¬ i < 9 by omega, ↓reduceDIte]
  let relGate (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
  let relCirc (D : Circuit) : Circuit := ⟨D.gates.map relGate, ρ D.output⟩
  have rel_run (gs : List Gate) : ∀ (w z : List Bool),
      w.length = z.length → 9 ≤ w.length →
      (∀ i, z.getD (ρ i) false = w.getD i false) →
      ∀ i, (run (gs.map relGate) z).getD (ρ i) false = (run gs w).getD i false := by
    induction gs with
    | nil => intro w z _ _ h i; exact h i
    | cons g gs ih =>
      intro w z hlen h9 h i
      change (run (gs.map relGate) (step z (relGate g))).getD (ρ i) false =
        (run gs (step w g)).getD i false
      have hval : (relGate g).op.eval ((relGate g).inputs.map fun j => z.getD j false) =
          g.op.eval (g.inputs.map fun j => w.getD j false) := by
        simp only [relGate, List.map_map, Function.comp_def, h]
      apply ih (step w g) (step z (relGate g))
        (by simp only [step, List.length_append, List.length_cons, List.length_nil, hlen])
        (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
      intro j
      by_cases hj : j = w.length
      · subst hj
        rw [hρ_fix w.length h9]
        simp only [step, hval]
        rw [getD_snoc_eq, hlen, getD_snoc_eq]
      · have hjz : ρ j ≠ z.length := by
          intro he
          by_cases hjs : j < 9
          · have := hρ_small j hjs
            omega
          · rw [hρ_fix j (by omega)] at he
            omega
        simp only [step]
        rw [getD_snoc_ne _ _ _ _ hjz, getD_snoc_ne _ _ _ _ hj]
        exact h j
  have rel_eval (D : Circuit) (x : Fin 9 → Bool) (b : Bool) :
      (relCirc D).eval (v10 x ++ [b]) = D.eval (v10 (x ∘ τ) ++ [b]) := by
    apply rel_run D.gates (v10 (x ∘ τ) ++ [b]) (v10 x ++ [b])
      (by simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
      (by simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)
    intro i
    by_cases hi : i < 9
    · have hri := hρ_small i hi
      simp only [v10, List.append_assoc, List.cons_append, List.nil_append]
      rw [ofFn_read_nat (x ∘ τ) _ i hi, ofFn_read_nat x [x 0 || x 2, b] (ρ i) hri]
      change x ⟨ρ i, hri⟩ = x (τ ⟨i, hi⟩)
      congr 1
      apply Fin.ext
      simp only [ρ, hi, ↓reduceDIte]
    · rw [hρ_fix i (by omega)]
      simp only [v10, List.append_assoc, List.cons_append, List.nil_append]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega),
          List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
      simp only [List.length_ofFn, hτ_or02 x]
  have hrel_fan (D : Circuit) (hD : FanInTwo D) : FanInTwo (relCirc D) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hD g' hg').1, by simpa only [relGate, List.length_map] using (hD g' hg').2⟩
  have hrel_mono (D : Circuit) (hD : Monotone2 D) : Monotone2 (relCirc D) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hD g' hg').1, by simpa only [relGate, List.length_map] using (hD g' hg').2⟩
  have hrel_size (D : Circuit) : (relCirc D).size = D.size := by
    change (D.gates.map relGate).length = D.gates.length
    exact List.length_map relGate
  have hrel_out (D : Circuit) (ho : D.output < 24) : (relCirc D).output < 24 := by
    dsimp only [relCirc, ρ]
    split
    · rename_i hlt9
      have := (τ ⟨D.output, hlt9⟩).isLt
      omega
    · exact ho
  have hrel_notCount (D : Circuit) : notCount (relCirc D) = notCount D := by
    have aux (p : Gate → Bool) (hp : ∀ g, p (relGate g) = p g) (gs : List Gate) :
        ((gs.map relGate).filter p).length = (gs.filter p).length := by
      induction gs with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.map_cons, List.filter_cons, hp g]
        cases p g
        · simp only [Bool.false_eq_true, ↓reduceIte, ih]
        · simp only [↓reduceIte, List.length_cons, ih]
    exact aux _ (fun _ => rfl) D.gates
  have hget1 : C.gates.get ⟨1, by omega⟩ = g1 := by
    apply Option.some.inj
    rw [List.get_eq_getElem, ← List.getElem?_eq_getElem]
    change C.gates[1]? = some g1
    rw [hgs]; rfl
  have hget_rest (j : Fin rest.length) :
      C.gates.get ⟨j.val + 2, by rw [hgs]; exact Nat.add_lt_add_right j.isLt 2⟩ = rest.get j := by
    apply Option.some.inj
    rw [List.get_eq_getElem, List.get_eq_getElem, ← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
    change C.gates[j.val + 2]? = rest[j.val]?
    rw [hgs]; rfl
  have hg1_fan := hfan g1 (by rw [hgs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨hg1_op, hg1_len⟩ := hg1_fan
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg1_op
  rcases hg1_op with hop_and | hop_or | hop_not
  · exfalso
    apply hnoand
    refine ⟨⟨1, by omega⟩, rfl, ?_⟩
    rw [hget1]
    exact hop_and
  · obtain ⟨idx, hidx0, hidx_not, hidx_uniq⟩ := hnot
    have hidx1 : idx.val ≠ 1 := by
      intro h1
      have heq : idx = ⟨1, by omega⟩ := Fin.ext h1
      rw [heq, hget1, hop_or] at hidx_not
      exact GateOp.noConfusion hidx_not
    have hidx2 : 2 ≤ idx.val := by omega
    have hD0_notCount : notCount D0 = 1 := by
      have aux (p : Gate → Bool) (hp : ∀ g, p g = true ↔ g.op = GateOp.not) :
          ∀ (gs : List Gate) (k : Fin gs.length), (gs.get k).op = GateOp.not →
            (∀ j : Fin gs.length, (gs.get j).op = GateOp.not → j = k) →
            (gs.filter p).length = 1 := by
        intro gs
        induction gs with
        | nil => intro k; exact Fin.elim0 k
        | cons a l ih =>
          intro k hk hu
          cases k using Fin.cases with
          | zero =>
            have hpa : p a = true := (hp a).2 hk
            have hfl : l.filter p = [] := by
              rw [List.filter_eq_nil_iff]
              intro x hx hpx
              obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
              have hju := hu j.succ ((hp _).1 (by simpa using hpx))
              exact Fin.succ_ne_zero j hju
            simp only [List.filter_cons, hpa, ↓reduceIte, hfl, List.length_singleton]
          | succ k' =>
            have hpa : p a = false := by
              cases h : p a
              · rfl
              · have h0 := hu 0 ((hp a).1 h)
                exact (Fin.succ_ne_zero k' h0.symm).elim
            simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte]
            apply ih k' hk
            intro j hj
            have hju := hu j.succ hj
            exact Fin.succ_inj.mp hju
      let k : Fin rest.length := ⟨idx.val - 2, by have := idx.isLt; omega⟩
      have hk : (rest.get k).op = GateOp.not := by
        rw [← hget_rest k]
        have heq : (⟨k.val + 2, by rw [hgs]; exact Nat.add_lt_add_right k.isLt 2⟩ : Fin C.gates.length) = idx := by
          apply Fin.ext
          dsimp only [k]
          omega
        rw [heq]
        exact hidx_not
      have hu (j : Fin rest.length) (hj : (rest.get j).op = GateOp.not) : j = k := by
        rw [← hget_rest j] at hj
        have hju := hidx_uniq ⟨j.val + 2, by rw [hgs]; exact Nat.add_lt_add_right j.isLt 2⟩ hj
        apply Fin.ext
        have hval := congrArg Fin.val hju
        dsimp only [k] at hval ⊢
        omega
      exact aux
        (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not))
        (fun g => @decide_eq_true_iff _ (lineDegreeGateOpDecEq g.op GateOp.not))
        rest k hk hu
    have kill_wire (a : ℕ) (hval : ∀ x, val1 x = (v10 x).getD a false) : False := by
      by_cases ha9 : a < 9
      · exact kill_redundant (Sum.inr a) (show a < 11 by omega) (fun x => by
          rw [hval x]
          exact (ofFn_read_nat x [false, x 0 || x 2] a ha9).trans (v10_read x a ha9).symm)
      · by_cases ha10 : a = 9
        · subst ha10
          exact kill_redundant (Sum.inr 10) (show 10 < 11 by omega) (fun x => by
            rw [hval x]
            change (List.ofFn x ++ [false, x 0 || x 2]).getD 10 false = (List.ofFn x ++ [x 0 || x 2]).getD 9 false
            rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega),
                List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
            simp only [List.length_ofFn]
            rfl)
        · exact kill_redundant (Sum.inl false) trivial (fun x => by
            rw [hval x]
            exact (List.getD_eq_default (v10 x) false (n := a) (by simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)).symm)
    rcases hg1_ins : g1.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact kill_redundant (Sum.inl false) trivial (fun x => by dsimp only [val1, sval]; rw [hop_or, hg1_ins]; rfl)
    · exact kill_wire a (fun x => by dsimp only [val1]; rw [hop_or, hg1_ins]; exact Bool.or_false _)
    · have hval1_ab (x : Fin 9 → Bool) : val1 x = ((v10 x).getD a false || (v10 x).getD b false) := by
        dsimp only [val1]
        rw [hop_or, hg1_ins]
        change ((v10 x).getD a false || ((v10 x).getD b false || false)) = _
        rw [Bool.or_false]
      by_cases ha10 : 10 ≤ a
      · exact kill_wire b (fun x => by
          rw [hval1_ab x, List.getD_eq_default (v10 x) false (n := a) (by simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega), Bool.false_or])
      by_cases hb10 : 10 ≤ b
      · exact kill_wire a (fun x => by
          rw [hval1_ab x, List.getD_eq_default (v10 x) false (n := b) (by simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega), Bool.or_false])
      by_cases hab : a = b
      · subst hab
        exact kill_wire a (fun x => by rw [hval1_ab x, Bool.or_self])
      have h02 (x : Fin 9 → Bool) : (v10 x).getD 9 false = (x 0 || x 2) := by
        change (List.ofFn x ++ [x 0 || x 2]).getD 9 false = (x 0 || x 2)
        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
        simp only [List.length_ofFn]
        rfl
      have kill_or02 (he : ∀ x, val1 x = (x 0 || x 2)) : False :=
        kill_redundant (Sum.inr 10) (show 10 < 11 by omega) (fun x => by
          rw [he x]
          change (List.ofFn x ++ [false, x 0 || x 2]).getD 10 false = (x 0 || x 2)
          rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
          simp only [List.length_ofFn]
          rfl)
      by_cases hred : (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 0 ∧ b = 9) ∨
          (a = 9 ∧ b = 0) ∨ (a = 2 ∧ b = 9) ∨ (a = 9 ∧ b = 2)
      · apply kill_or02
        intro x
        rw [hval1_ab x]
        rcases hred with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [v10_read x 0 (by omega), v10_read x 2 (by omega)]; rfl
        · rw [v10_read x 2 (by omega), v10_read x 0 (by omega), Bool.or_comm]; rfl
        · rw [v10_read x 0 (by omega), h02 x]; change (x 0 || (x 0 || x 2)) = (x 0 || x 2); cases x 0 <;> cases x 2 <;> rfl
        · rw [h02 x, v10_read x 0 (by omega)]; change ((x 0 || x 2) || x 0) = (x 0 || x 2); cases x 0 <;> cases x 2 <;> rfl
        · rw [v10_read x 2 (by omega), h02 x]; change (x 2 || (x 0 || x 2)) = (x 0 || x 2); cases x 0 <;> cases x 2 <;> rfl
        · rw [h02 x, v10_read x 2 (by omega)]; change ((x 0 || x 2) || x 2) = (x 0 || x 2); cases x 0 <;> cases x 2 <;> rfl
      by_cases ha9 : a = 9
      · subst ha9
        have hb9 : b < 9 := by omega
        have hval_c (x : Fin 9 → Bool) : val1 x = (x 0 || x 2 || x ⟨b, hb9⟩) := by
          rw [hval1_ab x, h02 x, v10_read x b hb9]
        have hD0_c (x : Fin 9 → Bool) : D0.eval (List.ofFn x ++ [x 0 || x 2, x 0 || x 2 || x ⟨b, hb9⟩]) = f x := by
          simpa only [v10, List.append_assoc, List.cons_append, List.nil_append, hval_c x] using hD0_eval x
        interval_cases b
        · exact (hred (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))).elim
        · exact gate1OrTriple 1 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact (hred (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))).elim
        · exact gate1OrTriple 3 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact gate1OrTriple 4 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact gate1OrTriple 3 (by decide) (relCirc D0) (hrel_fan D0 hD0_fan)
            (by rw [hrel_size]; exact hrest_len) (hrel_out D0 hD0_out)
            (by rw [hrel_notCount]; exact hD0_notCount) (fun x => by
              have hre := rel_eval D0 x (x 0 || x 2 || x 3)
              simp only [v10, List.append_assoc, List.cons_append, List.nil_append] at hre
              rw [hre, hτ_or02 x]
              have h1 := hD0_c (x ∘ τ)
              rw [hτ_or02 x, hτ_sym x] at h1
              exact h1)
        · exact gate1OrTriple 6 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact gate1OrTriple 4 (by decide) (relCirc D0) (hrel_fan D0 hD0_fan)
            (by rw [hrel_size]; exact hrest_len) (hrel_out D0 hD0_out)
            (by rw [hrel_notCount]; exact hD0_notCount) (fun x => by
              have hre := rel_eval D0 x (x 0 || x 2 || x 4)
              simp only [v10, List.append_assoc, List.cons_append, List.nil_append] at hre
              rw [hre, hτ_or02 x]
              have h1 := hD0_c (x ∘ τ)
              rw [hτ_or02 x, hτ_sym x] at h1
              exact h1)
        · exact gate1OrTriple 8 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
      by_cases hb9 : b = 9
      · subst hb9
        have ha9' : a < 9 := by omega
        have hval_c (x : Fin 9 → Bool) : val1 x = (x 0 || x 2 || x ⟨a, ha9'⟩) := by
          rw [hval1_ab x, h02 x, v10_read x a ha9', Bool.or_comm]
        have hD0_c (x : Fin 9 → Bool) : D0.eval (List.ofFn x ++ [x 0 || x 2, x 0 || x 2 || x ⟨a, ha9'⟩]) = f x := by
          simpa only [v10, List.append_assoc, List.cons_append, List.nil_append, hval_c x] using hD0_eval x
        interval_cases a
        · exact (hred (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))).elim
        · exact gate1OrTriple 1 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact (hred (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))).elim
        · exact gate1OrTriple 3 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact gate1OrTriple 4 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact gate1OrTriple 3 (by decide) (relCirc D0) (hrel_fan D0 hD0_fan)
            (by rw [hrel_size]; exact hrest_len) (hrel_out D0 hD0_out)
            (by rw [hrel_notCount]; exact hD0_notCount) (fun x => by
              have hre := rel_eval D0 x (x 0 || x 2 || x 3)
              simp only [v10, List.append_assoc, List.cons_append, List.nil_append] at hre
              rw [hre, hτ_or02 x]
              have h1 := hD0_c (x ∘ τ)
              rw [hτ_or02 x, hτ_sym x] at h1
              exact h1)
        · exact gate1OrTriple 6 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
        · exact gate1OrTriple 4 (by decide) (relCirc D0) (hrel_fan D0 hD0_fan)
            (by rw [hrel_size]; exact hrest_len) (hrel_out D0 hD0_out)
            (by rw [hrel_notCount]; exact hD0_notCount) (fun x => by
              have hre := rel_eval D0 x (x 0 || x 2 || x 4)
              simp only [v10, List.append_assoc, List.cons_append, List.nil_append] at hre
              rw [hre, hτ_or02 x]
              have h1 := hD0_c (x ∘ τ)
              rw [hτ_or02 x, hτ_sym x] at h1
              exact h1)
        · exact gate1OrTriple 8 (by decide) D0 hD0_fan hrest_len hD0_out hD0_notCount hD0_c
      have ha_lt : a < 9 := by omega
      have hb_lt : b < 9 := by omega
      let A : Fin 9 := ⟨a, ha_lt⟩
      let B : Fin 9 := ⟨b, hb_lt⟩
      let pairs20 : List (ℕ × ℕ) :=
        [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8),
         (1, 3), (1, 4), (1, 6), (1, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8),
         (4, 6), (4, 7), (4, 8), (6, 8)]
      let perm (s : Bool) (i : Fin 9) : Fin 9 := if s then τ i else i
      have horbits : ∀ u v : Fin 9, u ≠ v → ¬(u = 0 ∧ v = 2) → ¬(u = 2 ∧ v = 0) →
          ∃ p ∈ pairs20, ∃ s : Bool,
            ((Fin.ofNat 9 p.1, Fin.ofNat 9 p.2) = (perm s u, perm s v) ∨
             (Fin.ofNat 9 p.1, Fin.ofNat 9 p.2) = (perm s v, perm s u)) := by
        decide +kernel
      have hAB : A ≠ B := fun e => hab (congrArg Fin.val e)
      have hAB02 : ¬(A = 0 ∧ B = 2) := fun h =>
        hred (Or.inl ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩)
      have hAB20 : ¬(A = 2 ∧ B = 0) := fun h =>
        hred (Or.inr (Or.inl ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩))
      obtain ⟨p, hp, s, hmatch⟩ := horbits A B hAB hAB02 hAB20
      have hD0_ab (x : Fin 9 → Bool) : D0.eval (List.ofFn x ++ [x 0 || x 2, x A || x B]) = f x := by
        have h1 : val1 x = (x A || x B) := by
          rw [hval1_ab x, v10_read x a ha_lt, v10_read x b hb_lt]
        simpa only [v10, List.append_assoc, List.cons_append, List.nil_append, h1] using hD0_eval x
      cases s with
      | false =>
        apply gate1OrPair p hp D0 hD0_fan hrest_len hD0_out hD0_notCount
        intro x
        have hor : (x (Fin.ofNat 9 p.1) || x (Fin.ofNat 9 p.2)) = (x A || x B) := by
          rcases hmatch with h | h
          · cases Prod.mk.inj h with | intro h1 h2 => simp only [perm, Bool.false_eq_true, ↓reduceIte] at h1 h2; rw [h1, h2]
          · cases Prod.mk.inj h with | intro h1 h2 => simp only [perm, Bool.false_eq_true, ↓reduceIte] at h1 h2; rw [h1, h2, Bool.or_comm]
        rw [hor]
        exact hD0_ab x
      | true =>
        apply gate1OrPair p hp (relCirc D0) (hrel_fan D0 hD0_fan)
          (by rw [hrel_size]; exact hrest_len) (hrel_out D0 hD0_out)
          (by rw [hrel_notCount]; exact hD0_notCount)
        intro x
        have hor : (x (Fin.ofNat 9 p.1) || x (Fin.ofNat 9 p.2)) = ((x ∘ τ) A || (x ∘ τ) B) := by
          rcases hmatch with h | h
          · cases Prod.mk.inj h with | intro h1 h2 => simp only [perm, ↓reduceIte] at h1 h2; simp only [Function.comp_apply, h1, h2]
          · cases Prod.mk.inj h with | intro h1 h2 => simp only [perm, ↓reduceIte] at h1 h2; simp only [Function.comp_apply, h1, h2, Bool.or_comm]
        have hre := rel_eval D0 x (x (Fin.ofNat 9 p.1) || x (Fin.ofNat 9 p.2))
        simp only [v10, List.append_assoc, List.cons_append, List.nil_append] at hre
        rw [hre, hor, hτ_or02 x]
        have h1 := hD0_ab (x ∘ τ)
        rw [hτ_or02 x, hτ_sym x] at h1
        exact h1
    · simp only [hg1_ins, List.length_cons] at hg1_len; omega
  · obtain ⟨idx, _, _, hidx_uniq⟩ := hnot
    have hidx_eq : idx = ⟨1, by omega⟩ := by
      symm
      apply hidx_uniq ⟨1, by omega⟩
      rw [hget1]
      exact hop_not
    have hD0_mono : Monotone2 D0 := by
      intro g hg
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
      have hne_not : (rest.get j).op ≠ GateOp.not := by
        intro hjn
        rw [← hget_rest j] at hjn
        have hju := hidx_uniq ⟨j.val + 2, by rw [hgs]; exact Nat.add_lt_add_right j.isLt 2⟩ hjn
        rw [hidx_eq] at hju
        have := congrArg Fin.val hju
        dsimp at this
        omega
      have hf := hD0_fan (rest.get j) (List.get_mem _ _)
      refine ⟨?_, hf.2⟩
      have hop := hf.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      tauto
    rcases hg1_ins : g1.inputs with _ | ⟨w, ws⟩
    · exact kill_redundant (Sum.inl true) trivial (fun x => by dsimp only [val1, sval]; rw [hop_not, hg1_ins]; rfl)
    · have hval1_w (x : Fin 9 → Bool) : val1 x = !((v10 x).getD w false) := by
        dsimp only [val1]
        rw [hop_not, hg1_ins]
        rfl
      by_cases hw10 : 10 ≤ w
      · exact kill_redundant (Sum.inl true) trivial (fun x => by
          rw [hval1_w x, List.getD_eq_default (v10 x) false (n := w) (by simp only [v10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
          rfl)
      have hD0_w (x : Fin 9 → Bool) : D0.eval (v10 x ++ [!((v10 x).getD w false)]) = f x := by
        simpa only [hval1_w x] using hD0_eval x
      have hrel_not (k : ℕ) (hk : k ∈ ([0, 1, 3, 4, 6, 8, 9] : List ℕ))
          (hmatch : ∀ x : Fin 9 → Bool, (v10 (x ∘ τ)).getD w false = (v10 x).getD k false) : False := by
        apply gate1Not k hk (relCirc D0) (hrel_mono D0 hD0_mono)
          (by rw [hrel_size]; exact hrest_len) (hrel_out D0 hD0_out)
        intro x
        dsimp only
        rw [rel_eval D0 x (!((v10 x).getD k false)), ← hmatch x]
        exact (hD0_w (x ∘ τ)).trans (hτ_sym x)
      interval_cases w
      · exact gate1Not 0 (by decide) D0 hD0_mono hrest_len hD0_out hD0_w
      · exact gate1Not 1 (by decide) D0 hD0_mono hrest_len hD0_out hD0_w
      · exact hrel_not 0 (by decide) (fun x => by
          rw [v10_read (x ∘ τ) 2 (by omega), v10_read x 0 (by omega)]; rfl)
      · exact gate1Not 3 (by decide) D0 hD0_mono hrest_len hD0_out hD0_w
      · exact gate1Not 4 (by decide) D0 hD0_mono hrest_len hD0_out hD0_w
      · exact hrel_not 3 (by decide) (fun x => by
          rw [v10_read (x ∘ τ) 5 (by omega), v10_read x 3 (by omega)]; rfl)
      · exact gate1Not 6 (by decide) D0 hD0_mono hrest_len hD0_out hD0_w
      · exact hrel_not 4 (by decide) (fun x => by
          rw [v10_read (x ∘ τ) 7 (by omega), v10_read x 4 (by omega)]; rfl)
      · exact gate1Not 8 (by decide) D0 hD0_mono hrest_len hD0_out hD0_w
      · exact gate1Not 9 (by decide) D0 hD0_mono hrest_len hD0_out hD0_w
