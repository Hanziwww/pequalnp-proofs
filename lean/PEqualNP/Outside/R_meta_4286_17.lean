import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4286_17
    (hMono : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 3]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hNotInput : ∀ idx ∈ ([0, 1, 4, 5, 6, 9] : List ℕ),
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 3]
        D.eval (w ++ [!w.getD idx false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hNotAnd : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (k a u v : ℕ),
      gs.length = 13 →
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
      1 ≤ k → k < 13 → 10 ≤ a → a < 10 + k →
      (∀ j (hj : j < gs.length), gs[j].op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = k) →
      gs[k]?.map (fun g => g.inputs.head?) = some (some a) →
      gs[a - 10]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.and →
      10 ≤ u → u ≤ v → v < 23 → u ≠ 10 + k → v ≠ 10 + k →
      ∃ x : Fin 9 → Bool,
        let w := ({ gates := gs, output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD u false && w.getD v false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hNotOr : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (k a u v : ℕ),
      gs.length = 13 →
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
      1 ≤ k → k < 13 → 10 ≤ a → a < 10 + k →
      (∀ j (hj : j < gs.length), gs[j].op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = k) →
      gs[k]?.map (fun g => g.inputs.head?) = some (some a) →
      gs[a - 10]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.or →
      10 ≤ u → u ≤ v → v < 23 → u ≠ 10 + k → v ≠ 10 + k →
      ∃ x : Fin 9 → Bool,
        let w := ({ gates := gs, output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD u false && w.getD v false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),
      x1.length = (13 : ℕ) →
        PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
          List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (1 : ℕ) →
            (10 : ℕ) ≤ x2 →
              x2 ≤ x3 →
                x3 < (23 : ℕ) →
                  ∃ (x10 : Fin (9 : ℕ) → Bool),
                    have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);
                    (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro gs u v hlen hfan hcnt hu huv hv
  let P9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let w0 : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 3]
  have hw0_len (x : Fin 9 → Bool) : (w0 x).length = 10 := by
    simp only [w0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have hw0_read (x : Fin 9 → Bool) (i : Fin 9) : (w0 x).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simp only [List.length_ofFn]; exact i.isLt
    dsimp only [w0]
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hw0_read9 (x : Fin 9 → Bool) : (w0 x).getD 9 false = (x 0 || x 3) := by
    have h9 : (List.ofFn x).length = 9 := List.length_ofFn
    dsimp only [w0]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [h9, Nat.sub_self, List.getD_cons_zero]
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs' w => gs'.foldl step w
  have run_len (gs' : List Gate) (w : List Bool) : (run gs' w).length = w.length + gs'.length := by
    induction gs' generalizing w with
    | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      rw [ih (step w g)]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · have hgt : l.length + 1 ≤ j := by omega
      rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l d (n := j) (by omega)]
  have run_keep (gs' : List Gate) (w : List Bool) :
      ∀ i < w.length, (run gs' w).getD i false = w.getD i false := by
    induction gs' generalizing w with
    | nil => intro i _; rfl
    | cons g rest ih =>
      intro i hi
      simp only [run, List.foldl_cons] at ih ⊢
      have hi' : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step w g) i hi']
      exact List.getD_append _ _ _ _ hi
  have run_append (gs1 gs2 : List Gate) (w : List Bool) :
      run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
    dsimp only [run]
    exact List.foldl_append
  by_contra hno
  have hagree (x : Fin 9 → Bool) :
      ((run gs (w0 x)).getD u false && (run gs (w0 x)).getD v false) = P9 x := by
    by_contra hne
    exact hno ⟨x, hne⟩
  have eval_false_iff (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
      op.eval [false] = true ↔ op = GateOp.not := by
    rcases hop with rfl | rfl | rfl
    · change false = true ↔ GateOp.and = GateOp.not
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    · change false = true ↔ GateOp.or = GateOp.not
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    · change true = true ↔ GateOp.not = GateOp.not
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  have countP_eq_one {α : Type} (p : α → Bool) :
      ∀ (l : List α), l.countP p = 1 →
        ∃ k : ℕ, k < l.length ∧ ∀ j (hj : j < l.length), p l[j] = true ↔ j = k := by
    intro l
    induction l with
    | nil =>
      intro h
      simp only [List.countP_nil] at h
      omega
    | cons hd tl ih =>
      intro h
      rw [List.countP_cons] at h
      cases hp : p hd with
      | true =>
        rw [hp] at h
        have hzero : tl.countP p = 0 := by
          simp only [↓reduceIte] at h
          omega
        have hall : ∀ x ∈ tl, p x = false := by
          intro x hx
          have h0 := List.countP_eq_zero.mp hzero x hx
          cases hpx : p x with
          | false => rfl
          | true => exact absurd hpx h0
        refine ⟨0, by simp only [List.length_cons]; omega, fun j hj => ?_⟩
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero, hp]
        | succ j' =>
          have hj' : j' < tl.length := by simp only [List.length_cons] at hj; omega
          have hmem : tl[j'] ∈ tl := List.getElem_mem hj'
          simp only [List.getElem_cons_succ, hall tl[j'] hmem]
          exact ⟨(fun h1 => by cases h1), (fun h1 => by cases h1)⟩
      | false =>
        rw [hp] at h
        have hone : tl.countP p = 1 := by
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          omega
        obtain ⟨k, hk, huniq⟩ := ih hone
        refine ⟨k + 1, by simp only [List.length_cons]; omega, fun j hj => ?_⟩
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero, hp]
          exact ⟨(fun h1 => by cases h1), (fun h1 => by cases h1)⟩
        | succ j' =>
          have hj' : j' < tl.length := by simp only [List.length_cons] at hj; omega
          simp only [List.getElem_cons_succ]
          rw [huniq j' hj']
          omega
  obtain ⟨k, hk_len, huniq_p⟩ := countP_eq_one (fun g : Gate => g.op.eval [false]) gs hcnt
  have hk13 : k < 13 := by omega
  have huniq (j : ℕ) (hj : j < gs.length) : gs[j].op = GateOp.not ↔ j = k := by
    have hgj : gs[j] ∈ gs := List.getElem_mem hj
    have hop := (hfan gs[j] hgj).1
    exact (eval_false_iff gs[j].op hop).symm.trans (huniq_p j hj)
  let pre : List Gate := gs.take k
  let gk : Gate := gs[k]'hk_len
  let post : List Gate := gs.drop (k + 1)
  have hpre_len : pre.length = k := by
    simp only [pre, List.length_take]
    omega
  have hpost_len : post.length = 12 - k := by
    simp only [post, List.length_drop]
    omega
  have hgs_split : gs = pre ++ (gk :: post) := by
    have h1 : gs.take k ++ gs.drop k = gs := List.take_append_drop k gs
    have h2 : gs.drop k = gk :: gs.drop (k + 1) := List.drop_eq_getElem_cons hk_len
    rw [← h2]
    exact h1.symm
  have hgk_op : gk.op = GateOp.not := (huniq k hk_len).mpr rfl
  have hpre_ok : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj_len : j < gs.length := by omega
    have heq : pre[j]'hj = gs[j]'hj_len := List.getElem_take
    rw [heq]
    have hmem : gs[j]'hj_len ∈ gs := List.getElem_mem hj_len
    have hf := hfan (gs[j]'hj_len) hmem
    have hne : (gs[j]'hj_len).op ≠ GateOp.not := by
      intro hnot
      have hjk := (huniq j hj_len).mp hnot
      omega
    rcases hf.1 with hop | hop | hop
    · exact ⟨Or.inl hop, hf.2⟩
    · exact ⟨Or.inr hop, hf.2⟩
    · exact absurd hop hne
  have hpost_ok : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj_len : k + 1 + j < gs.length := by omega
    have heq : post[j]'hj = gs[k + 1 + j]'hj_len := List.getElem_drop
    rw [heq]
    have hmem : gs[k + 1 + j]'hj_len ∈ gs := List.getElem_mem hj_len
    have hf := hfan (gs[k + 1 + j]'hj_len) hmem
    have hne : (gs[k + 1 + j]'hj_len).op ≠ GateOp.not := by
      intro hnot
      have hjk := (huniq (k + 1 + j) hj_len).mp hnot
      omega
    rcases hf.1 with hop | hop | hop
    · exact ⟨Or.inl hop, hf.2⟩
    · exact ⟨Or.inr hop, hf.2⟩
    · exact absurd hop hne
  have hrun_split (x : Fin 9 → Bool) :
      run gs (w0 x) = run post (step (run pre (w0 x)) gk) := by
    conv_lhs => rw [hgs_split]
    rw [run_append]
    rfl
  have hwire_k (x : Fin 9 → Bool) :
      (run gs (w0 x)).getD (10 + k) false =
        gk.op.eval (gk.inputs.map fun i => (run pre (w0 x)).getD i false) := by
    rw [hrun_split x]
    have hpre_wlen : (run pre (w0 x)).length = 10 + k := by
      rw [run_len, hw0_len x, hpre_len]
    have hstep_len : (step (run pre (w0 x)) gk).length = 10 + k + 1 := by
      simp only [step, List.length_append, hpre_wlen, List.length_cons, List.length_nil]
    rw [run_keep post (step (run pre (w0 x)) gk) (10 + k) (by omega)]
    dsimp only [step]
    simpa only [hpre_wlen] using getD_snoc_eq (run pre (w0 x))
      (gk.op.eval (gk.inputs.map fun i => (run pre (w0 x)).getD i false)) false
  let sval : List Bool → Bool ⊕ ℕ → Bool := fun w => Sum.elim id (fun i => w.getD i false)
  let svalid : ℕ → Bool ⊕ ℕ → Prop := fun m => Sum.elim (fun _ => True) (fun i => i < m)
  let simpAnd : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.casesOn ins (none, Sum.inl true) (fun a rest =>
      List.casesOn rest (none, a) (fun b _ =>
        Sum.elim
          (fun ba => if ba then (none, b) else (none, Sum.inl false))
          (fun ia => Sum.elim
            (fun bb => if bb then (none, Sum.inr ia) else (none, Sum.inl false))
            (fun ib => (some ⟨GateOp.and, [ia, ib]⟩, Sum.inr m))
            b)
          a))
  let simpOr : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
    List.casesOn ins (none, Sum.inl false) (fun a rest =>
      List.casesOn rest (none, a) (fun b _ =>
        Sum.elim
          (fun ba => if ba then (none, Sum.inl true) else (none, b))
          (fun ia => Sum.elim
            (fun bb => if bb then (none, Sum.inl true) else (none, Sum.inr ia))
            (fun ib => (some ⟨GateOp.or, [ia, ib]⟩, Sum.inr m))
            b)
          a))
  let simplifyMono : GateOp → ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun op m ins =>
    GateOp.rec (simpAnd m ins) (simpOr m ins) (none, Sum.inl false) (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op
  have simplifyMono_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
      ∀ g ∈ (simplifyMono op m ins).1.toList, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
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
              change g ∈ [⟨GateOp.and, [ia, ib]⟩] at hg
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
              change g ∈ [⟨GateOp.or, [ia, ib]⟩] at hg
              rw [List.mem_singleton] at hg
              subst hg
              exact ⟨Or.inr rfl, Nat.le_refl 2⟩
    | not => intro g hg; cases hg
    | mod _ => intro g hg; cases hg
    | maj => intro g hg; cases hg
  have simplifyMono_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen_i : ins.length ≤ 2)
      (hv_i : ∀ s ∈ ins, svalid w.length s) :
      svalid (w.length + (simplifyMono op w.length ins).1.toList.length) (simplifyMono op w.length ins).2 ∧
      sval (run (simplifyMono op w.length ins).1.toList w) (simplifyMono op w.length ins).2 =
        op.eval (ins.map (sval w)) := by
    rcases hop with rfl | rfl
    · cases ins with
      | nil => exact ⟨trivial, rfl⟩
      | cons a t =>
        cases t with
        | nil =>
          have ha := hv_i a (by simp only [List.mem_cons, true_or])
          refine ⟨by simpa only [simplifyMono, simpAnd, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
          change sval w a = (sval w a && true)
          exact (Bool.and_true _).symm
        | cons b t2 =>
          cases t2 with
          | cons _ _ => simp only [List.length_cons] at hlen_i; omega
          | nil =>
            have ha := hv_i a (by simp only [List.mem_cons, true_or])
            have hb := hv_i b (by simp only [List.mem_cons, true_or, or_true])
            cases a with
            | inl ba =>
              cases ba with
              | true =>
                refine ⟨by simpa only [simplifyMono, simpAnd, Sum.elim_inl, ite_true, Option.toList_none, List.length_nil, Nat.add_zero] using hb, ?_⟩
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
                  refine ⟨by simpa only [simplifyMono, simpAnd, Sum.elim_inr, Sum.elim_inl, ite_true, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
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
          have ha := hv_i a (by simp only [List.mem_cons, true_or])
          refine ⟨by simpa only [simplifyMono, simpOr, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
          change sval w a = (sval w a || false)
          exact (Bool.or_false _).symm
        | cons b t2 =>
          cases t2 with
          | cons _ _ => simp only [List.length_cons] at hlen_i; omega
          | nil =>
            have ha := hv_i a (by simp only [List.mem_cons, true_or])
            have hb := hv_i b (by simp only [List.mem_cons, true_or, or_true])
            cases a with
            | inl ba =>
              cases ba with
              | true =>
                refine ⟨trivial, ?_⟩
                change true = (true || (sval w b || false))
                rfl
              | false =>
                refine ⟨by simpa only [simplifyMono, simpOr, Sum.elim_inl, Bool.false_eq_true, ite_false, Option.toList_none, List.length_nil, Nat.add_zero] using hb, ?_⟩
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
                  refine ⟨by simpa only [simplifyMono, simpOr, Sum.elim_inr, Sum.elim_inl, Bool.false_eq_true, ite_false, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
                  change w.getD ia false = (w.getD ia false || (false || false))
                  cases w.getD ia false <;> rfl
              | inr ib =>
                refine ⟨show w.length < w.length + 1 by omega, ?_⟩
                change (w ++ [(w.getD ia false || (w.getD ib false || false))]).getD w.length false =
                  (w.getD ia false || (w.getD ib false || false))
                exact getD_snoc_eq w _ false
  let elimStep : List (Bool ⊕ ℕ) × List Gate → Gate → List (Bool ⊕ ℕ) × List Gate := fun acc g =>
    let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
    let r := simplifyMono g.op (10 + acc.2.length) ins
    (acc.1 ++ [r.2], acc.2 ++ r.1.toList)
  let elim : List Gate → List (Bool ⊕ ℕ) × List Gate → List (Bool ⊕ ℕ) × List Gate := fun gs' acc =>
    gs'.foldl elimStep acc
  have elim_len (gs' : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
      (elim gs' acc).2.length ≤ acc.2.length + gs'.length := by
    induction gs' generalizing acc with
    | nil => simp only [elim, List.foldl_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    | cons g rest ih =>
      simp only [elim, List.foldl_cons] at ih ⊢
      have h1 := ih (elimStep acc g)
      have h2 : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
        dsimp only [elimStep]
        rw [List.length_append]
        cases (simplifyMono g.op (10 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
          simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
      simp only [List.length_cons]
      omega
  have elim_ok (gs' : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hacc : ∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
      ∀ g ∈ (elim gs' acc).2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    induction gs' generalizing acc with
    | nil => exact hacc
    | cons g rest ih =>
      simp only [elim, List.foldl_cons] at ih ⊢
      apply ih (elimStep acc g)
      intro g' hg'
      dsimp only [elimStep] at hg'
      rw [List.mem_append] at hg'
      rcases hg' with h1 | h2
      · exact hacc g' h1
      · exact simplifyMono_ok g.op (10 + acc.2.length) _ g' h2
  let Inv : List Bool → List Bool → List (Bool ⊕ ℕ) × List Gate → Prop := fun w z acc =>
    w.length = 10 ∧ acc.1.length = z.length ∧
    ∀ i, svalid (10 + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
         sval (run acc.2 w) (acc.1.getD i (Sum.inl false)) = z.getD i false
  have elim_inv (gs' : List Gate) (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hgs' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (hinv : Inv w z acc) : Inv w (run gs' z) (elim gs' acc) := by
    induction gs' generalizing z acc with
    | nil => exact hinv
    | cons g rest ih =>
      simp only [run, elim, List.foldl_cons] at ih ⊢
      apply ih (step z g) (elimStep acc g) (fun g' hg' => hgs' g' (List.mem_cons_of_mem g hg'))
      obtain ⟨hwl, hml, hmap⟩ := hinv
      have hg := hgs' g (List.mem_cons_self)
      let w' := run acc.2 w
      have hw'len : w'.length = 10 + acc.2.length := by
        dsimp only [w']; rw [run_len, hwl]
      let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
      let r := simplifyMono g.op w'.length ins
      have hins_len : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact hg.2
      have hins_v : ∀ s ∈ ins, svalid w'.length s := by
        intro s hs
        simp only [ins, List.mem_map] at hs
        obtain ⟨i, _, rfl⟩ := hs
        rw [hw'len]; exact (hmap i).1
      have hrs := simplifyMono_sound g.op hg.1 w' ins hins_len hins_v
      have hvals : ins.map (sval w') = g.inputs.map (fun i => z.getD i false) := by
        dsimp only [ins]
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact (hmap i).2
      have hstep_run : run (acc.2 ++ r.1.toList) w = run r.1.toList w' := run_append acc.2 r.1.toList w
      have heq_r : simplifyMono g.op (10 + acc.2.length) ins = r := by rw [← hw'len]
      refine ⟨hwl, ?_, ?_⟩
      · simp only [elimStep, step, List.length_append, hml, List.length_cons, List.length_nil]
      · intro i
        dsimp only [elimStep]
        change svalid (10 + (acc.2 ++ (simplifyMono g.op (10 + acc.2.length) ins).1.toList).length)
            ((acc.1 ++ [(simplifyMono g.op (10 + acc.2.length) ins).2]).getD i (Sum.inl false)) ∧
          sval (run (acc.2 ++ (simplifyMono g.op (10 + acc.2.length) ins).1.toList) w)
            ((acc.1 ++ [(simplifyMono g.op (10 + acc.2.length) ins).2]).getD i (Sum.inl false)) =
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
  have kill_const_k (c : Bool)
      (hc : ∀ x : Fin 9 → Bool,
        gk.op.eval (gk.inputs.map fun i => (run pre (w0 x)).getD i false) = c) : False := by
    let M0 : List (Bool ⊕ ℕ) := (List.range 10).map (Sum.inr : ℕ → Bool ⊕ ℕ)
    have hM0_len : M0.length = 10 := by
      simp only [M0, List.length_map, List.length_range]
    have hM0_lt (j : ℕ) (hj : j < 10) : M0.getD j (Sum.inl false) = Sum.inr j := by
      dsimp only [M0]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hj),
          List.getElem_map, List.getElem_range]
    have hbase (x : Fin 9 → Bool) : Inv (w0 x) (w0 x) (M0, []) := by
      refine ⟨hw0_len x, by rw [hM0_len, hw0_len x], ?_⟩
      intro i
      by_cases hi : i < 10
      · rw [hM0_lt i hi]
        exact ⟨show i < 10 + 0 by omega, rfl⟩
      · rw [List.getD_eq_default M0 (Sum.inl false) (n := i) (by omega),
            List.getD_eq_default (w0 x) false (n := i) (by rw [hw0_len x]; omega)]
        exact ⟨trivial, rfl⟩
    let r1 := elim pre (M0, [])
    have hr1_len : r1.2.length ≤ k := by
      have h := elim_len pre (M0, [])
      change (elim pre (M0, [])).2.length ≤ k
      simp only [List.length_nil, Nat.zero_add, hpre_len] at h
      exact h
    have hr1_ok : ∀ g ∈ r1.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      elim_ok pre (M0, []) (fun _ h => by cases h)
    have hr1_inv (x : Fin 9 → Bool) : Inv (w0 x) (run pre (w0 x)) r1 :=
      elim_inv pre (w0 x) (w0 x) (M0, []) hpre_ok (hbase x)
    let acc1 : List (Bool ⊕ ℕ) × List Gate := (r1.1 ++ [Sum.inl c], r1.2)
    have hacc1_inv (x : Fin 9 → Bool) : Inv (w0 x) (step (run pre (w0 x)) gk) acc1 := by
      obtain ⟨hwl, hml, hmap⟩ := hr1_inv x
      refine ⟨hwl, ?_, ?_⟩
      · simp only [acc1, step, List.length_append, hml, List.length_cons, List.length_nil]
      · intro i
        dsimp only [acc1, step]
        by_cases hi : i = r1.1.length
        · subst hi
          rw [getD_snoc_eq r1.1 (Sum.inl c) (Sum.inl false), hml, getD_snoc_eq (run pre (w0 x)) _ false]
          exact ⟨trivial, (hc x).symm⟩
        · have hi' : i ≠ (run pre (w0 x)).length := by rw [← hml]; exact hi
          rw [getD_snoc_ne r1.1 (Sum.inl c) (Sum.inl false) i hi,
              getD_snoc_ne (run pre (w0 x)) _ false i hi']
          exact hmap i
    let r2 := elim post acc1
    have hr2_len : r2.2.length ≤ 12 := by
      have h := elim_len post acc1
      change (elim post acc1).2.length ≤ 12
      change (elim post acc1).2.length ≤ r1.2.length + post.length at h
      omega
    have hr2_ok : ∀ g ∈ r2.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      elim_ok post acc1 hr1_ok
    have hr2_inv (x : Fin 9 → Bool) : Inv (w0 x) (run gs (w0 x)) r2 := by
      rw [hrun_split x]
      exact elim_inv post (w0 x) (step (run pre (w0 x)) gk) acc1 hpost_ok (hacc1_inv x)
    let su := r2.1.getD u (Sum.inl false)
    let sv := r2.1.getD v (Sum.inl false)
    let rf := simplifyMono GateOp.and (10 + r2.2.length) [su, sv]
    let gs3 := r2.2 ++ rf.1.toList
    have hgs3_len : gs3.length ≤ 13 := by
      dsimp only [gs3]
      rw [List.length_append]
      cases rf.1 <;> simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
    have hgs3_ok : ∀ g ∈ gs3, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      dsimp only [gs3] at hg
      rw [List.mem_append] at hg
      rcases hg with h1 | h2
      · exact hr2_ok g h1
      · exact simplifyMono_ok GateOp.and (10 + r2.2.length) [su, sv] g h2
    have hrf_eval (x : Fin 9 → Bool) : sval (run gs3 (w0 x)) rf.2 = P9 x := by
      have hinv := hr2_inv x
      have hw'len : (run r2.2 (w0 x)).length = 10 + r2.2.length := by rw [run_len, hw0_len x]
      have hvs : ∀ s ∈ ([su, sv] : List (Bool ⊕ ℕ)), svalid (run r2.2 (w0 x)).length s := by
        intro s hs
        rw [hw'len]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact (hinv.2.2 u).1
        · exact (hinv.2.2 v).1
      have hs := simplifyMono_sound GateOp.and (Or.inl rfl) (run r2.2 (w0 x)) [su, sv] (Nat.le_refl 2) hvs
      have heq_rf : simplifyMono GateOp.and (run r2.2 (w0 x)).length [su, sv] = rf := by
        dsimp only [rf]; rw [hw'len]
      rw [heq_rf] at hs
      dsimp only [gs3]
      rw [run_append, hs.2]
      change (sval (run r2.2 (w0 x)) su && (sval (run r2.2 (w0 x)) sv && true)) = P9 x
      rw [Bool.and_true, (hinv.2.2 u).2, (hinv.2.2 v).2]
      exact hagree x
    cases hrf2 : rf.2 with
    | inl b =>
      have hf0 : b = P9 (fun _ => false) := by
        have h := hrf_eval (fun _ => false); rw [hrf2] at h; exact h
      have hf1 : b = P9 (fun _ => true) := by
        have h := hrf_eval (fun _ => true); rw [hrf2] at h; exact h
      have hne : P9 (fun _ => false) ≠ P9 (fun _ => true) := by decide
      exact hne (hf0.symm.trans hf1)
    | inr out =>
      let D : Circuit := ⟨gs3, out⟩
      have hDfan : FanInTwo D := by
        intro g hg
        have h := hgs3_ok g hg
        rcases h.1 with hop | hop
        · exact ⟨Or.inl hop, h.2⟩
        · exact ⟨Or.inr (Or.inl hop), h.2⟩
      have hDmono : ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
        intro g hg hnot
        have h := hgs3_ok g hg
        rcases h.1 with hop | hop <;> (rw [hop] at hnot; cases hnot)
      obtain ⟨x, hx⟩ := hMono D hDfan hgs3_len hDmono
      have hev : D.eval (w0 x) = P9 x := by
        have h := hrf_eval x; rw [hrf2] at h; exact h
      exact hx hev
  have remap_bijection (f : ℕ → ℕ) (L0 : ℕ)
      (hf_lt : ∀ i, i < L0 → f i < L0) (hf_ge : ∀ i, L0 ≤ i → f i = i)
      (gs' : List Gate) (wA wB : List Bool)
      (hlen_w : wA.length = wB.length) (hL0 : L0 ≤ wA.length)
      (hrel : ∀ i, wB.getD (f i) false = wA.getD i false) :
      ∀ i, (run (gs'.map fun g => ⟨g.op, g.inputs.map f⟩) wB).getD (f i) false =
        (run gs' wA).getD i false := by
    induction gs' generalizing wA wB with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hinp : (g.inputs.map f).map (fun i => wB.getD i false) =
          g.inputs.map (fun i => wA.getD i false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hrel i
      let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
      have hstepB : step wB ⟨g.op, g.inputs.map f⟩ = wB ++ [b] := by
        dsimp only [step, b]; rw [hinp]
      rw [hstepB]
      apply ih (step wA g) (wB ++ [b])
      · simp only [step, List.length_append, hlen_w, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        dsimp only [step]
        by_cases hi : i = wA.length
        · subst hi
          have hfi : f wA.length = wB.length := by rw [hf_ge wA.length hL0, hlen_w]
          rw [hfi, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
        · have hfi : f i ≠ wB.length := by
            intro hfeq
            by_cases hlt : i < L0
            · have := hf_lt i hlt; omega
            · have := hf_ge i (by omega); omega
          rw [getD_snoc_ne wB b false (f i) hfi, getD_snoc_ne wA b false i hi]
          exact hrel i
  let sigNat : ℕ → ℕ := fun i =>
    if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 0
    else if i = 5 then 8 else if i = 6 then 7 else if i = 7 then 6 else if i = 8 then 5
    else i
  have hsig_lt (i : ℕ) (hi : i < 9) : sigNat i < 9 := by
    dsimp only [sigNat]
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    omega
  have hsig_ge (i : ℕ) (hi : 9 ≤ i) : sigNat i = i := by
    dsimp only [sigNat]
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    split; · omega
    rfl
  let sigFin : Fin 9 → Fin 9 := fun i => ⟨sigNat i.val, hsig_lt i.val i.isLt⟩
  have hP9_sig (x : Fin 9 → Bool) : P9 (fun i => x (sigFin i)) = P9 x := by
    change (x 3 && x 2 || x 2 && x 1 || x 1 && x 0 || x 0 && x 4 || x 4 && x 3 ||
            x 3 && x 8 || x 2 && x 7 || x 1 && x 6 || x 0 && x 5 || x 8 && x 6 ||
            x 7 && x 5 || x 5 && x 8) =
           (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
            x 6 && x 8 || x 8 && x 5)
    rw [Bool.and_comm (x 3) (x 2), Bool.and_comm (x 2) (x 1), Bool.and_comm (x 1) (x 0),
        Bool.and_comm (x 0) (x 4), Bool.and_comm (x 4) (x 3), Bool.and_comm (x 8) (x 6),
        Bool.and_comm (x 7) (x 5), Bool.and_comm (x 5) (x 8)]
    ac_rfl
  have kill_not_input (idx : ℕ) (hidx : idx < 10) (hhead : gk.inputs.head? = some idx) : False := by
    let shiftPre : ℕ → ℕ := fun i => if i < 10 then i else i + 1
    let remapPreStep : ℕ × List Gate → Gate → ℕ × List Gate := fun acc g =>
      (acc.1 + 1, acc.2 ++ [⟨g.op, g.inputs.map (fun i => if i < acc.1 then shiftPre i else acc.1 + 1)⟩])
    let remapPre : List Gate → ℕ × List Gate → ℕ × List Gate := fun gs' acc =>
      gs'.foldl remapPreStep acc
    have remapPre_len (gs' : List Gate) (acc : ℕ × List Gate) :
        (remapPre gs' acc).1 = acc.1 + gs'.length ∧
        (remapPre gs' acc).2.length = acc.2.length + gs'.length := by
      induction gs' generalizing acc with
      | nil => simp only [remapPre, List.foldl_nil, List.length_nil, Nat.add_zero, and_self]
      | cons g rest ih =>
        simp only [remapPre, List.foldl_cons] at ih ⊢
        have h1 : (remapPreStep acc g).1 = acc.1 + 1 := rfl
        have h2 : (remapPreStep acc g).2.length = acc.2.length + 1 := by
          simp only [remapPreStep, List.length_append, List.length_cons, List.length_nil]
        have h := ih (remapPreStep acc g)
        simp only [List.length_cons]
        omega
    have remapPre_ok (gs' : List Gate) (acc : ℕ × List Gate)
        (hgs' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
        (hacc : ∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
        ∀ g ∈ (remapPre gs' acc).2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      induction gs' generalizing acc with
      | nil => exact hacc
      | cons g rest ih =>
        simp only [remapPre, List.foldl_cons] at ih ⊢
        apply ih (remapPreStep acc g) (fun g' hg' => hgs' g' (List.mem_cons_of_mem g hg'))
        intro g' hg'
        dsimp only [remapPreStep] at hg'
        rw [List.mem_append] at hg'
        rcases hg' with h1 | h2
        · exact hacc g' h1
        · simp only [List.mem_singleton] at h2
          subst h2
          have hg := hgs' g List.mem_cons_self
          exact ⟨hg.1, by simp only [List.length_map]; exact hg.2⟩
    have remapPre_sim (gs' : List Gate) (acc : ℕ × List Gate) (wOld wBase : List Bool)
        (hBase_len : wBase.length = 11)
        (hOld_len : wOld.length = acc.1) (hAcc_len : acc.1 = 10 + acc.2.length)
        (hrel : ∀ i < wOld.length, (run acc.2 wBase).getD (shiftPre i) false = wOld.getD i false) :
        ∀ i < (run gs' wOld).length,
          (run (remapPre gs' acc).2 wBase).getD (shiftPre i) false = (run gs' wOld).getD i false := by
      induction gs' generalizing acc wOld with
      | nil => exact hrel
      | cons g rest ih =>
        simp only [remapPre, run, List.foldl_cons] at ih ⊢
        let g' : Gate := ⟨g.op, g.inputs.map (fun i => if i < acc.1 then shiftPre i else acc.1 + 1)⟩
        let wNew := run acc.2 wBase
        have hwNew_len : wNew.length = acc.1 + 1 := by
          dsimp only [wNew]; rw [run_len, hBase_len]; omega
        have hinp : g'.inputs.map (fun i => wNew.getD i false) =
            g.inputs.map (fun i => wOld.getD i false) := by
          dsimp only [g']
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          change wNew.getD (if i < acc.1 then shiftPre i else acc.1 + 1) false = wOld.getD i false
          split
          · exact hrel i (by omega)
          · rw [List.getD_eq_default wNew false (n := acc.1 + 1) (by omega),
                List.getD_eq_default wOld false (n := i) (by omega)]
        let b := g.op.eval (g.inputs.map fun i => wOld.getD i false)
        have hrun_next : run (acc.2 ++ [g']) wBase = wNew ++ [b] := by
          rw [run_append]
          change step wNew g' = wNew ++ [b]
          dsimp only [step, b]
          rw [hinp]
        apply ih (remapPreStep acc g) (step wOld g)
        · simp only [remapPreStep, step, List.length_append, hOld_len, List.length_cons, List.length_nil]
        · simp only [remapPreStep, List.length_append, List.length_cons, List.length_nil]; omega
        · intro i hi
          change (run (acc.2 ++ [g']) wBase).getD (shiftPre i) false = (wOld ++ [b]).getD i false
          rw [hrun_next]
          simp only [step, List.length_append, List.length_cons, List.length_nil] at hi
          by_cases hieq : i = wOld.length
          · subst hieq
            have hsh : shiftPre wOld.length = wNew.length := by
              dsimp only [shiftPre]
              split
              · omega
              · omega
            rw [hsh, getD_snoc_eq wNew b false, getD_snoc_eq wOld b false]
          · have hlt : i < wOld.length := by omega
            have hsh_ne : shiftPre i ≠ wNew.length := by
              dsimp only [shiftPre]
              split
              · omega
              · omega
            rw [getD_snoc_ne wNew b false (shiftPre i) hsh_ne, getD_snoc_ne wOld b false i hieq]
            exact hrel i hlt
    let pre' : List Gate := (remapPre pre (10, [])).2
    let slide : ℕ → ℕ := fun i =>
      if i < 10 then i else if i < 10 + k then i + 1 else if i = 10 + k then 10 else i
    let post' : List Gate := post.map (fun g => ⟨g.op, g.inputs.map slide⟩)
    let gs_new : List Gate := pre' ++ post' ++ [⟨GateOp.and, [slide u, slide v]⟩]
    have hpre'_len : pre'.length = k := by
      have h := (remapPre_len pre (10, [])).2
      dsimp only [pre']
      simp only [List.length_nil, Nat.zero_add, hpre_len] at h
      exact h
    have hgs_new_len : gs_new.length = 13 := by
      dsimp only [gs_new, post']
      simp only [List.length_append, List.length_map, hpre'_len, hpost_len, List.length_cons, List.length_nil]
      omega
    have hgs_new_ok : ∀ g ∈ gs_new, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      dsimp only [gs_new] at hg
      rw [List.mem_append, List.mem_append] at hg
      rcases hg with (h1 | h2) | h3
      · exact remapPre_ok pre (10, []) hpre_ok (fun _ h => by cases h) g h1
      · simp only [post', List.mem_map] at h2
        obtain ⟨g0, hg0, rfl⟩ := h2
        have h := hpost_ok g0 hg0
        exact ⟨h.1, by simp only [List.length_map]; exact h.2⟩
      · simp only [List.mem_singleton] at h3
        subst h3
        exact ⟨Or.inl rfl, Nat.le_refl 2⟩
    let D : Circuit := ⟨gs_new, 23⟩
    have hDfan : FanInTwo D := by
      intro g hg
      have h := hgs_new_ok g hg
      rcases h.1 with hop | hop
      · exact ⟨Or.inl hop, h.2⟩
      · exact ⟨Or.inr (Or.inl hop), h.2⟩
    have hDsz : D.size ≤ 13 := by change gs_new.length ≤ 13; omega
    have hDmono : ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
      intro g hg hnot
      have h := hgs_new_ok g hg
      rcases h.1 with hop | hop <;> (rw [hop] at hnot; cases hnot)
    have hgk_val (x : Fin 9 → Bool) :
        gk.op.eval (gk.inputs.map fun i => (run pre (w0 x)).getD i false) = !(w0 x).getD idx false := by
      rw [hgk_op]
      cases hgi : gk.inputs with
      | nil => rw [hgi] at hhead; cases hhead
      | cons a tl =>
        rw [hgi] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst a
        change (!((run pre (w0 x)).getD idx false)) = !(w0 x).getD idx false
        rw [run_keep pre (w0 x) idx (by rw [hw0_len x]; exact hidx)]
    have hDeval (x : Fin 9 → Bool) : D.eval (w0 x ++ [!(w0 x).getD idx false]) = P9 x := by
      let wBase := w0 x ++ [!(w0 x).getD idx false]
      have hwBase_len : wBase.length = 11 := by
        simp only [wBase, List.length_append, hw0_len x, List.length_cons, List.length_nil]
      have hpre_sim := remapPre_sim pre (10, []) (w0 x) wBase hwBase_len (hw0_len x) rfl
        (fun i hi => by
          have hi10 : i < 10 := by rw [hw0_len x] at hi; exact hi
          change wBase.getD (shiftPre i) false = (w0 x).getD i false
          have hsh : shiftPre i = i := by simp only [shiftPre, hi10, ↓reduceIte]
          rw [hsh]
          exact List.getD_append _ _ _ _ hi)
      let wOld_k := step (run pre (w0 x)) gk
      let wNew_pre := run pre' wBase
      have hwOld_pre_len : (run pre (w0 x)).length = 10 + k := by
        rw [run_len, hw0_len x, hpre_len]
      have hwOld_k_len : wOld_k.length = 10 + k + 1 := by
        simp only [wOld_k, step, List.length_append, hwOld_pre_len, List.length_cons, List.length_nil]
      have hwNew_pre_len : wNew_pre.length = 10 + k + 1 := by
        dsimp only [wNew_pre]; rw [run_len, hwBase_len, hpre'_len]; omega
      have hrel_k : ∀ i, wNew_pre.getD (slide i) false = wOld_k.getD i false := by
        intro i
        by_cases hi10 : i < 10
        · have hsl : slide i = i := by simp only [slide, hi10, ↓reduceIte]
          have hsh : shiftPre i = i := by simp only [shiftPre, hi10, ↓reduceIte]
          rw [hsl]
          have h1 := hpre_sim i (by omega)
          rw [hsh] at h1
          have h2 : wOld_k.getD i false = (run pre (w0 x)).getD i false :=
            getD_snoc_ne (run pre (w0 x)) _ false i (by omega)
          rw [h2]; exact h1
        · by_cases hik : i < 10 + k
          · have hsl : slide i = i + 1 := by simp only [slide, hi10, hik, ↓reduceIte]
            have hsh : shiftPre i = i + 1 := by simp only [shiftPre, hi10, ↓reduceIte]
            rw [hsl]
            have h1 := hpre_sim i (by omega)
            rw [hsh] at h1
            have h2 : wOld_k.getD i false = (run pre (w0 x)).getD i false :=
              getD_snoc_ne (run pre (w0 x)) _ false i (by omega)
            rw [h2]; exact h1
          · by_cases hieq : i = 10 + k
            · subst hieq
              have hsl : slide (10 + k) = 10 := by simp only [slide, hi10, hik, ↓reduceIte]
              rw [hsl]
              have h1 : wNew_pre.getD 10 false = !(w0 x).getD idx false := by
                dsimp only [wNew_pre]
                rw [run_keep pre' wBase 10 (by omega)]
                dsimp only [wBase]
                simpa only [hw0_len x] using getD_snoc_eq (w0 x) (!(w0 x).getD idx false) false
              have h2 : wOld_k.getD (10 + k) false = !(w0 x).getD idx false := by
                dsimp only [wOld_k, step]
                rw [← hwOld_pre_len, getD_snoc_eq (run pre (w0 x)) _ false]
                exact hgk_val x
              rw [h1, h2]
            · have hgt : 10 + k + 1 ≤ i := by omega
              have hsl : slide i = i := by simp only [slide, hi10, hik, hieq, ↓reduceIte]
              rw [hsl,
                  List.getD_eq_default wNew_pre false (n := i) (by omega),
                  List.getD_eq_default wOld_k false (n := i) (by omega)]
      have hpost_rel := remap_bijection slide (10 + k + 1)
        (fun i hi => by dsimp only [slide]; split <;> (try split) <;> (try split) <;> omega)
        (fun i hi => by
          dsimp only [slide]
          split; · omega
          split; · omega
          split; · omega
          rfl)
        post wOld_k wNew_pre (by omega) (by omega) hrel_k
      let wNew_mid := run post' wNew_pre
      have hwNew_mid_len : wNew_mid.length = 23 := by
        dsimp only [wNew_mid, post']; rw [run_len, hwNew_pre_len, List.length_map, hpost_len]; omega
      have hrun_D : run gs_new wBase = wNew_mid ++ [(wNew_mid.getD (slide u) false && (wNew_mid.getD (slide v) false && true))] := by
        dsimp only [gs_new]
        rw [run_append, run_append]
        rfl
      change (run gs_new wBase).getD 23 false = P9 x
      rw [hrun_D, ← hwNew_mid_len, getD_snoc_eq wNew_mid _ false, Bool.and_true]
      have hu_eq : wNew_mid.getD (slide u) false = (run gs (w0 x)).getD u false := by
        rw [hrun_split x]; exact hpost_rel u
      have hv_eq : wNew_mid.getD (slide v) false = (run gs (w0 x)).getD v false := by
        rw [hrun_split x]; exact hpost_rel v
      rw [hu_eq, hv_eq]
      exact hagree x
    by_cases hmem_idx : idx ∈ ([0, 1, 4, 5, 6, 9] : List ℕ)
    · obtain ⟨x, hx⟩ := hNotInput idx hmem_idx D hDfan hDsz hDmono
      exact hx (hDeval x)
    · have hsig_mem : sigNat idx ∈ ([0, 1, 4, 5, 6, 9] : List ℕ) := by
        have hcases : idx = 2 ∨ idx = 3 ∨ idx = 7 ∨ idx = 8 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_idx
          omega
        rcases hcases with rfl | rfl | rfl | rfl <;> decide
      let Dsig : Circuit := ⟨D.gates.map fun g => ⟨g.op, g.inputs.map sigNat⟩, sigNat D.output⟩
      have hDsig_fan : FanInTwo Dsig := by
        intro g hg
        simp only [Dsig, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        have h := hDfan g0 hg0
        exact ⟨h.1, by simp only [List.length_map]; exact h.2⟩
      have hDsig_sz : Dsig.size ≤ 13 := by
        change (D.gates.map _).length ≤ 13
        rw [List.length_map]
        exact hDsz
      have hDsig_mono : ∀ g ∈ Dsig.gates, g.op ≠ GateOp.not := by
        intro g hg
        simp only [Dsig, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        exact hDmono g0 hg0
      have hDsig_eval (x : Fin 9 → Bool) :
          Dsig.eval (w0 x ++ [!(w0 x).getD (sigNat idx) false]) = P9 x := by
        let y : Fin 9 → Bool := fun i => x (sigFin i)
        let wA := w0 y ++ [!(w0 y).getD idx false]
        let wB := w0 x ++ [!(w0 x).getD (sigNat idx) false]
        have hw0_sig (i : ℕ) : (w0 x).getD (sigNat i) false = (w0 y).getD i false := by
          by_cases hi9 : i < 9
          · have hsi9 : sigNat i < 9 := hsig_lt i hi9
            have h1 := hw0_read x ⟨sigNat i, hsi9⟩
            have h2 := hw0_read y ⟨i, hi9⟩
            exact h1.trans h2.symm
          · by_cases hi_eq9 : i = 9
            · subst hi_eq9
              have hs9 : sigNat 9 = 9 := rfl
              rw [hs9, hw0_read9 x, hw0_read9 y]
              change (x 0 || x 3) = (x 3 || x 0)
              exact Bool.or_comm _ _
            · have hsge : sigNat i = i := hsig_ge i (by omega)
              rw [hsge,
                  List.getD_eq_default (w0 x) false (n := i) (by rw [hw0_len x]; omega),
                  List.getD_eq_default (w0 y) false (n := i) (by rw [hw0_len y]; omega)]
        have hrel_ab : ∀ i, wB.getD (sigNat i) false = wA.getD i false := by
          intro i
          by_cases hi10 : i = 10
          · subst hi10
            have hs10 : sigNat 10 = 10 := rfl
            rw [hs10]
            dsimp only [wA, wB]
            rw [show 10 = (w0 x).length from (hw0_len x).symm, getD_snoc_eq (w0 x) _ false,
                show (w0 x).length = (w0 y).length from (hw0_len x).trans (hw0_len y).symm,
                getD_snoc_eq (w0 y) _ false, hw0_sig idx]
          · have hsi10 : sigNat i ≠ 10 := by
              by_cases hi9 : i < 9
              · have := hsig_lt i hi9; omega
              · rw [hsig_ge i (by omega)]; exact hi10
            dsimp only [wA, wB]
            rw [getD_snoc_ne (w0 x) _ false (sigNat i) (by rw [hw0_len x]; exact hsi10),
                getD_snoc_ne (w0 y) _ false i (by rw [hw0_len y]; exact hi10)]
            exact hw0_sig i
        have hbij := remap_bijection sigNat 9 hsig_lt hsig_ge
          D.gates wA wB
          (by simp only [wA, wB, List.length_append, hw0_len y, hw0_len x, List.length_cons, List.length_nil])
          (by simp only [wA, List.length_append, hw0_len y, List.length_cons, List.length_nil]; omega)
          hrel_ab
        have h1 : Dsig.eval wB = D.eval wA := hbij D.output
        exact h1.trans ((hDeval y).trans (hP9_sig x))
      obtain ⟨x, hx⟩ := hNotInput (sigNat idx) hsig_mem Dsig hDsig_fan hDsig_sz hDsig_mono
      exact hx (hDsig_eval x)
  let wLe : List Bool → List Bool → Prop := fun w1 w2 =>
    w1.length = w2.length ∧ ∀ i, w1.getD i false = true → w2.getD i false = true
  have run_mono (gs' : List Gate) (hgs' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
      ∀ w1 w2, wLe w1 w2 → wLe (run gs' w1) (run gs' w2) := by
    induction gs' with
    | nil => intro w1 w2 h; exact h
    | cons g rest ih =>
      intro w1 w2 hle
      simp only [run, List.foldl_cons]
      apply ih (fun g' hg' => hgs' g' (List.mem_cons_of_mem g hg'))
      have hg := (hgs' g List.mem_cons_self).1
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
  cases hhead : gk.inputs.head? with
  | none =>
    apply kill_const_k true
    intro x
    rw [hgk_op]
    cases hgi : gk.inputs with
    | nil => rfl
    | cons a tl => rw [hgi] at hhead; cases hhead
  | some a =>
    by_cases ha_hi : 10 + k ≤ a
    · apply kill_const_k true
      intro x
      rw [hgk_op]
      cases hgi : gk.inputs with
      | nil => rw [hgi] at hhead; cases hhead
      | cons b tl =>
        rw [hgi] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst b
        change !((run pre (w0 x)).getD a false) = true
        have hlen_p : (run pre (w0 x)).length = 10 + k := by rw [run_len, hw0_len x, hpre_len]
        rw [List.getD_eq_default (run pre (w0 x)) false (n := a) (by omega)]
        rfl
    · by_cases ha10 : a < 10
      · exact kill_not_input a ha10 hhead
      · have hgk_eval_a (x : Fin 9 → Bool) :
            gk.op.eval (gk.inputs.map fun i => (run pre (w0 x)).getD i false) =
              !((run pre (w0 x)).getD a false) := by
          rw [hgk_op]
          cases hgi : gk.inputs with
          | nil => rw [hgi] at hhead; cases hhead
          | cons b tl =>
            rw [hgi] at hhead
            simp only [List.head?_cons, Option.some.injEq] at hhead
            subst b
            rfl
        have hnot_uv (huvk : u = 10 + k ∨ v = 10 + k) : False := by
          let x1 : Fin 9 → Bool := fun _ => true
          have hP9_1 : P9 x1 = true := by decide
          have h1 := hagree x1
          rw [hP9_1] at h1
          have hwk1 : (run gs (w0 x1)).getD (10 + k) false = true := by
            rcases huvk with rfl | rfl
            · exact (Bool.and_eq_true _ _).mp h1 |>.1
            · exact (Bool.and_eq_true _ _).mp h1 |>.2
          rw [hwire_k x1, hgk_eval_a x1] at hwk1
          have ha_false_1 : (run pre (w0 x1)).getD a false = false := by
            cases h : (run pre (w0 x1)).getD a false with
            | false => rfl
            | true => rw [h] at hwk1; cases hwk1
          apply kill_const_k true
          intro x
          rw [hgk_eval_a x]
          have hw0_le : wLe (w0 x) (w0 x1) := by
            refine ⟨(hw0_len x).trans (hw0_len x1).symm, ?_⟩
            intro i hi
            by_cases hi9 : i < 9
            · exact hw0_read x1 ⟨i, hi9⟩
            · by_cases hi_eq9 : i = 9
              · subst hi_eq9; exact hw0_read9 x1
              · rw [List.getD_eq_default (w0 x) false (n := i) (by rw [hw0_len x]; omega)] at hi
                cases hi
          have hpre_le := run_mono pre hpre_ok (w0 x) (w0 x1) hw0_le
          cases hxa : (run pre (w0 x)).getD a false with
          | false => rfl
          | true =>
            have hcontra := hpre_le.2 a hxa
            rw [ha_false_1] at hcontra
            cases hcontra
        have huk : u ≠ 10 + k := fun h => hnot_uv (Or.inl h)
        have hvk : v ≠ 10 + k := fun h => hnot_uv (Or.inr h)
        have h1k : 1 ≤ k := by omega
        have h10a : 10 ≤ a := by omega
        have hak : a < 10 + k := by omega
        have ha_idx : a - 10 < gs.length := by omega
        have hhead_map : gs[k]?.map (fun g => g.inputs.head?) = some (some a) := by
          rw [List.getElem?_eq_getElem hk_len]
          exact congrArg some hhead
        have ha_op_ne : (gs[a - 10]'ha_idx).op ≠ GateOp.not := by
          intro hnot
          have hjk := (huniq (a - 10) ha_idx).mp hnot
          omega
        have ha_fan := (hfan (gs[a - 10]'ha_idx) (List.getElem_mem ha_idx)).1
        rcases ha_fan with hop | hop | hop
        · have hop_map : gs[a - 10]?.map (fun g => g.op) = some GateOp.and := by
            rw [List.getElem?_eq_getElem ha_idx]
            exact congrArg some hop
          obtain ⟨x, hx⟩ := hNotAnd gs k a u v hlen hfan h1k hk13 h10a hak huniq hhead_map hop_map hu huv hv huk hvk
          exact hx (hagree x)
        · have hop_map : gs[a - 10]?.map (fun g => g.op) = some GateOp.or := by
            rw [List.getElem?_eq_getElem ha_idx]
            exact congrArg some hop
          obtain ⟨x, hx⟩ := hNotOr gs k a u v hlen hfan h1k hk13 h10a hak huniq hhead_map hop_map hu huv hv huk hvk
          exact hx (hagree x)
        · exact absurd hop ha_op_ne
