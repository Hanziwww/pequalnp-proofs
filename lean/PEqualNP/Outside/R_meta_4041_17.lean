import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_4041_17
    (hSizeLe123 :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 42 D →
        D.size ≤ 123 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
            x u = true ∧ x v = true) →
        (∃ d ∈ ([0, 5] : List ℕ),
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 42 (42 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 42 0 a ∧
            PEqualNP.ReadTwo.orp D 42 (21 + d) b) →
        False)
    (hSize124Unit :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 42 D →
        D.size = 124 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
            x u = true ∧ x v = true) →
        (∃ p l : Fin 21, (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 42 (42 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 42 p.val a ∧
            PEqualNP.ReadTwo.orp D 42 (21 + l.val) b) →
        (∃ k a c : ℕ, PEqualNP.ReadTwo.andOn D k a c ∧
          PEqualNP.ReadTwo.orp D 42 0 a ∧
          PEqualNP.ReadTwo.orp D 42 0 c) →
        False)
    (hSize124Same :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 42 D →
        D.size = 124 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
            x u = true ∧ x v = true) →
        (∃ p l : Fin 21, (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 42 (42 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 42 p.val a ∧
            PEqualNP.ReadTwo.orp D 42 (21 + l.val) b) →
        (∀ k : ℕ, PEqualNP.ReadTwo.isAnd D k →
          ∀ v : Fin 42, PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (42 + k) = false) →
        (∃ b ∈ ([1, 3, 7] : List ℕ), ∃ k a c : ℕ, PEqualNP.ReadTwo.andOn D k a c ∧
          PEqualNP.ReadTwo.orp D 42 0 a ∧
          PEqualNP.ReadTwo.orp D 42 b c) →
        False)
    (hSize124Cross :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 42 D →
        D.size = 124 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
            x u = true ∧ x v = true) →
        (∃ p l : Fin 21, (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧
          ¬ ∃ j a b : ℕ, PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 42 (42 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 42 p.val a ∧
            PEqualNP.ReadTwo.orp D 42 (21 + l.val) b) →
        (∀ k : ℕ, PEqualNP.ReadTwo.isAnd D k →
          ∀ v : Fin 42, PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (42 + k) = false) →
        (∃ b ∈ ([22, 23, 24, 35] : List ℕ), ∃ k a c : ℕ, PEqualNP.ReadTwo.andOn D k a c ∧
          PEqualNP.ReadTwo.orp D 42 0 a ∧
          PEqualNP.ReadTwo.orp D 42 b c) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) := by
  let D5 : List ℕ := [0, 5, 7, 17, 20]
  let S_indep : List ℕ := [0, 1, 2, 6, 8, 18, 24, 31, 33, 37]
  let I : Fin 21 → Fin 21 → Prop := fun p l => (l.val + 21 - p.val) % 21 ∈ D5
  let Hpg : (Fin 42 → Bool) → Prop := fun x =>
    ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ D5) ∧
      x u = true ∧ x v = true
  have hD5_diff : ∀ a ∈ D5, ∀ b ∈ D5, ∀ c ∈ D5, ∀ d ∈ D5,
      a ≠ b → a ≠ c → (b + 21 - a) % 21 ≠ (d + 21 - c) % 21 := by decide
  have hNoC4 : ∀ (p1 p2 l1 l2 : Fin 21), p1 ≠ p2 → l1 ≠ l2 →
      ¬ (I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
    rintro p1 p2 l1 l2 hp hl ⟨h11, h12, h21, h22⟩
    have hne1 : (l1.val + 21 - p1.val) % 21 ≠ (l2.val + 21 - p1.val) % 21 := by
      intro heq; apply hl; apply Fin.ext; omega
    have hne2 : (l1.val + 21 - p1.val) % 21 ≠ (l1.val + 21 - p2.val) % 21 := by
      intro heq; apply hp; apply Fin.ext; omega
    have hsame : ((l2.val + 21 - p1.val) % 21 + 21 - (l1.val + 21 - p1.val) % 21) % 21 =
        ((l2.val + 21 - p2.val) % 21 + 21 - (l1.val + 21 - p2.val) % 21) % 21 := by omega
    exact hD5_diff _ h11 _ h12 _ h21 _ h22 hne1 hne2 hsame
  have hI_diag (p : Fin 21) : I p p := by
    change (p.val + 21 - p.val) % 21 ∈ D5
    have h0 : (p.val + 21 - p.val) % 21 = 0 := by omega
    rw [h0]; exact List.mem_cons_self
  let lineOf (p : Fin 21) (k : Fin 5) : Fin 21 :=
    ⟨(p.val + D5.getD k.val 0) % 21, Nat.mod_lt _ (by omega)⟩
  have hD5_get_lt : ∀ k : Fin 5, D5.getD k.val 0 < 21 := by decide
  have hD5_get_mem : ∀ k : Fin 5, D5.getD k.val 0 ∈ D5 := by decide
  have hD5_get_inj : ∀ k1 k2 : Fin 5, D5.getD k1.val 0 = D5.getD k2.val 0 → k1 = k2 := by decide
  have hlineOf_I (p : Fin 21) (k : Fin 5) : I p (lineOf p k) := by
    change ((p.val + D5.getD k.val 0) % 21 + 21 - p.val) % 21 ∈ D5
    have hd := hD5_get_lt k
    have heq : ((p.val + D5.getD k.val 0) % 21 + 21 - p.val) % 21 = D5.getD k.val 0 := by omega
    rw [heq]; exact hD5_get_mem k
  have hlineOf_inj (p : Fin 21) (k1 k2 : Fin 5) (h : lineOf p k1 = lineOf p k2) : k1 = k2 := by
    have hv := congrArg Fin.val h
    dsimp only [lineOf] at hv
    have hd1 := hD5_get_lt k1
    have hd2 := hD5_get_lt k2
    exact hD5_get_inj k1 k2 (by omega)
  have hS_indep : ∀ u ∈ S_indep, ∀ v ∈ S_indep, u < 21 → 21 ≤ v → (v + 21 - u) % 21 ∉ D5 := by decide
  let affTable : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1, 0, 1, 0), (2, 7, 11, 7), (4, 0, 16, 0), (8, 7, 8, 7), (11, 7, 2, 7), (16, 0, 4, 0)]
  have haff_ok : ∀ t ∈ affTable,
      (∀ p : Fin 21, (t.2.2.1 * ((t.1 * p.val) % 21)) % 21 = p.val ∧
                     (t.1 * ((t.2.2.1 * p.val) % 21)) % 21 = p.val) ∧
      (∀ l : Fin 21, (t.2.2.1 * ((t.1 * l.val + t.2.1) % 21) + t.2.2.2) % 21 = l.val ∧
                     (t.1 * ((t.2.2.1 * l.val + t.2.2.2) % 21) + t.2.1) % 21 = l.val) ∧
      (∀ d ∈ D5, (t.1 * d + t.2.1) % 21 ∈ D5 ∧ (t.2.2.1 * d + t.2.2.2) % 21 ∈ D5) := by decide
  have haff_edge : ∀ d ∈ D5, ∃ t ∈ affTable, (t.1 * d + t.2.1) % 21 ∈ ([0, 5] : List ℕ) := by decide
  have haff_same : ∀ a : Fin 21, a.val ≠ 0 →
      ∃ t ∈ affTable, (t.1 * a.val) % 21 ∈ ([1, 3, 7] : List ℕ) ∨
                      (t.1 * (21 - a.val)) % 21 ∈ ([1, 3, 7] : List ℕ) := by decide
  have haff_cross : ∀ d : Fin 21, d.val ∉ D5 →
      ∃ t ∈ affTable, (t.1 * d.val + t.2.1) % 21 ∈ ([1, 2, 3, 14] : List ℕ) := by decide
  have hmod_aff (m s p l : ℕ) (hp : p < 21) (hl : l < 21) :
      ((m * l + s) % 21 + 21 - (m * p) % 21) % 21 = (m * ((l + 21 - p) % 21) + s) % 21 := by
    have h1 : (m * ((l + 21 - p) % 21) + s) % 21 = (m * (l + 21 - p) + s) % 21 := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    have h2 : m * (l + 21 - p) + s + m * p = m * l + s + 21 * m := by
      have : m * (l + 21 - p) + m * p = m * (l + 21) := by
        rw [← Nat.mul_add]; congr 1; omega
      rw [Nat.mul_add] at this
      omega
    have h3 : ((m * (l + 21 - p) + s) % 21 + (m * p) % 21) % 21 = (m * l + s) % 21 := by
      rw [← Nat.add_mod, h2, Nat.add_mul_mod_self_left]
    rw [h1]
    have ha : (m * l + s) % 21 < 21 := Nat.mod_lt _ (by omega)
    have hb : (m * p) % 21 < 21 := Nat.mod_lt _ (by omega)
    have hc : (m * (l + 21 - p) + s) % 21 < 21 := Nat.mod_lt _ (by omega)
    omega
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
  have run_getD_gate (gs : List Gate) (ws : List Bool) (j : ℕ) (g : Gate)
      (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
      (run gs ws).getD (ws.length + j) false =
        g.op.eval (g.inputs.map fun i => (run gs ws).getD i false) := by
    induction gs generalizing ws j with
    | nil => cases hj
    | cons g0 rest ih =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [Nat.add_zero] at hback ⊢
        change (run rest (step ws g0)).getD ws.length false =
          g0.op.eval (g0.inputs.map fun i => (run rest (step ws g0)).getD i false)
        have hlt : ws.length < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [run_keep rest (step ws g0) ws.length hlt]
        have hstep : (step ws g0).getD ws.length false =
            g0.op.eval (g0.inputs.map fun k => ws.getD k false) := getD_snoc_eq ws _ false
        rw [hstep]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlti : i < ws.length := hback i hi
        have hlti' : i < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [run_keep rest (step ws g0) i hlti']
        exact (List.getD_append _ _ _ _ hlti).symm
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        change (run rest (step ws g0)).getD (ws.length + (j' + 1)) false =
          g.op.eval (g.inputs.map fun i => (run rest (step ws g0)).getD i false)
        have hlen : (step ws g0).length = ws.length + 1 := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
        have hidx : ws.length + (j' + 1) = (step ws g0).length + j' := by omega
        rw [hidx]
        exact ih (step ws g0) j' hj (fun i hi => by have := hback i hi; omega)
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
  have simplify_some_inv (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (m : ℕ) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2) (gn : Gate)
      (hsome : (simplify op m ins).1 = some gn) :
      ∃ ia ib : ℕ, ins = [Sum.inr ia, Sum.inr ib] ∧ (simplify op m ins).2 = Sum.inr m := by
    rcases hop with rfl | rfl
    · cases ins with
      | nil => cases hsome
      | cons a t =>
        cases t with
        | nil => cases hsome
        | cons b t2 =>
          cases t2 with
          | cons _ _ => simp only [List.length_cons] at hlen; omega
          | nil =>
            cases a with
            | inl ba => cases ba <;> cases hsome
            | inr ia =>
              cases b with
              | inl bb => cases bb <;> cases hsome
              | inr ib => exact ⟨ia, ib, rfl, rfl⟩
    · cases ins with
      | nil => cases hsome
      | cons a t =>
        cases t with
        | nil => cases hsome
        | cons b t2 =>
          cases t2 with
          | cons _ _ => simp only [List.length_cons] at hlen; omega
          | nil =>
            cases a with
            | inl ba => cases ba <;> cases hsome
            | inr ia =>
              cases b with
              | inl bb => cases bb <;> cases hsome
              | inr ib => exact ⟨ia, ib, rfl, rfl⟩
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
    let r := simplify g.op (42 + acc.2.length) ins
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
        cases (simplify g.op (42 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
          simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
      simp only [List.length_cons]
      omega
  have elim_full_ao2 (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (hacc : acc.1 = (List.range (42 + acc.2.length)).map (Sum.inr : ℕ → Bool ⊕ ℕ))
      (heq : (elim gs acc).2.length = acc.2.length + gs.length) :
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < 42 + acc.2.length + j) := by
    induction gs generalizing acc with
    | nil =>
      exact ⟨(fun _ h => by cases h), (fun _ h _ _ => by simp only [List.length_nil] at h; omega)⟩
    | cons g rest ih =>
      have heq' : (elim rest (elimStep acc g)).2.length = acc.2.length + (rest.length + 1) := by
        simpa only [elim, List.foldl_cons, List.length_cons] using heq
      have hrem := elim_len rest (elimStep acc g)
      have hg := hgs g List.mem_cons_self
      let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
      let r := simplify g.op (42 + acc.2.length) ins
      have hstep_len : (elimStep acc g).2.length = acc.2.length + 1 := by
        have hle : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
          dsimp only [elimStep]
          rw [List.length_append]
          cases r.1 <;> simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
        omega
      cases hr1 : r.1 with
      | none =>
        have hbad : (elimStep acc g).2.length = acc.2.length := by
          dsimp only [elimStep]
          change (acc.2 ++ r.1.toList).length = acc.2.length
          rw [hr1, Option.toList_none, List.append_nil]
        omega
      | some gn =>
        have hins_len : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact hg.2
        obtain ⟨ia, ib, hins_eq, hr2⟩ := simplify_some_inv g.op hg.1 (42 + acc.2.length) ins hins_len gn hr1
        have hget_inr (u v : ℕ) (h : acc.1.getD u (Sum.inl false) = Sum.inr v) :
            u < 42 + acc.2.length := by
          by_contra hge
          have hlen_acc : acc.1.length = 42 + acc.2.length := by
            rw [hacc, List.length_map, List.length_range]
          rw [List.getD_eq_default acc.1 (Sum.inl false) (n := u) (by omega)] at h
          cases h
        have hg_len2 : g.inputs.length = 2 := by
          have hl := congrArg List.length hins_eq
          dsimp only [ins] at hl
          rw [List.length_map] at hl
          exact hl
        have hg_form : g.inputs.length = 2 ∧ ∀ u ∈ g.inputs, u < 42 + acc.2.length := by
          cases hgins : g.inputs with
          | nil => rw [hgins] at hg_len2; cases hg_len2
          | cons u t1 =>
            cases t1 with
            | nil => rw [hgins] at hg_len2; cases hg_len2
            | cons v t2 =>
              cases t2 with
              | cons _ _ => rw [hgins] at hg_len2; cases hg_len2
              | nil =>
                dsimp only [ins] at hins_eq
                rw [hgins] at hins_eq
                simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hins_eq
                refine ⟨rfl, ?_⟩
                intro x hx
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl
                · exact hget_inr x ia hins_eq.1
                · exact hget_inr x ib hins_eq.2
        have hacc' : (elimStep acc g).1 = (List.range (42 + (elimStep acc g).2.length)).map (Sum.inr : ℕ → Bool ⊕ ℕ) := by
          rw [hstep_len]
          dsimp only [elimStep]
          change acc.1 ++ [r.2] = (List.range (42 + (acc.2.length + 1))).map (Sum.inr : ℕ → Bool ⊕ ℕ)
          rw [hacc, hr2, show 42 + (acc.2.length + 1) = (42 + acc.2.length) + 1 by omega,
              List.range_succ, List.map_append]
          rfl
        have hrec := ih (elimStep acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) hacc' (by omega)
        refine ⟨?_, ?_⟩
        · intro g' hg'
          rcases List.mem_cons.mp hg' with rfl | hrest
          · exact ⟨by rcases hg.1 with h | h <;> [exact Or.inl h; exact Or.inr h], hg_form.1⟩
          · exact hrec.1 g' hrest
        · intro j hj u hu
          cases j with
          | zero =>
            simp only [List.getD_cons_zero] at hu
            have := hg_form.2 u hu; omega
          | succ j' =>
            simp only [List.length_cons] at hj
            simp only [List.getD_cons_succ] at hu
            have := hrec.2 j' (by omega) u hu
            omega
  let Inv : List Bool → List Bool → List (Bool ⊕ ℕ) × List Gate → Prop := fun w z acc =>
    w.length = 42 ∧ acc.1.length = z.length ∧
    (∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    (∀ j < acc.2.length, ∀ i ∈ (acc.2.getD j ⟨GateOp.or, []⟩).inputs, i < 42 + j) ∧
    ∀ i, svalid (42 + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
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
      have hw'len : w'.length = 42 + acc.2.length := by
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
      have heq_r : simplify g.op (42 + acc.2.length) ins = r := by rw [← hw'len]
      refine ⟨hwl, ?_, ?_, ?_, ?_⟩
      · simp only [elimStep, step, List.length_append, hml, List.length_cons, List.length_nil]
      · intro g' hg'
        dsimp only [elimStep] at hg'
        change g' ∈ acc.2 ++ (simplify g.op (42 + acc.2.length) ins).1.toList at hg'
        rw [heq_r, List.mem_append] at hg'
        rcases hg' with h1 | h2
        · exact hok2 g' h1
        · exact ⟨(hrok g' h2).1, (hrok g' h2).2.1⟩
      · intro j hj u hu
        dsimp only [elimStep] at hj hu
        change j < (acc.2 ++ (simplify g.op (42 + acc.2.length) ins).1.toList).length at hj
        change u ∈ ((acc.2 ++ (simplify g.op (42 + acc.2.length) ins).1.toList).getD j ⟨GateOp.or, []⟩).inputs at hu
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
        change svalid (42 + (acc.2 ++ (simplify g.op (42 + acc.2.length) ins).1.toList).length)
            ((acc.1 ++ [(simplify g.op (42 + acc.2.length) ins).2]).getD i (Sum.inl false)) ∧
          sval (run (acc.2 ++ (simplify g.op (42 + acc.2.length) ins).1.toList) w)
            ((acc.1 ++ [(simplify g.op (42 + acc.2.length) ins).2]).getD i (Sum.inl false)) =
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
  have hstar_bound : ∀ (C : Circuit), IsAO2 42 C →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ Hpg x) →
      (∀ (p l : Fin 21), I p l →
        ∃ (j a b : ℕ), andOn C j a b ∧
          orp C 42 (42 + j) C.output ∧
          orp C 42 p.val a ∧
          orp C 42 (21 + l.val) b) →
      126 ≤ C.size + 1 := by
    classical
    intro C hAO2 hComp_iff hall
    let N : ℕ := 42
    let E : Finset (Fin 21 × Fin 21) := Finset.univ.filter (fun e => I e.1 e.2)
    have hmem_E (p l : Fin 21) : (p, l) ∈ E ↔ I p l := by
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    have hE_ge105 : 105 ≤ E.card := by
      let f : Fin 21 × Fin 5 → Fin 21 × Fin 21 := fun pk => (pk.1, lineOf pk.1 pk.2)
      have hsub : (Finset.univ : Finset (Fin 21 × Fin 5)).image f ⊆ E := by
        intro e he
        obtain ⟨pk, _, rfl⟩ := Finset.mem_image.mp he
        exact (hmem_E pk.1 (lineOf pk.1 pk.2)).mpr (hlineOf_I pk.1 pk.2)
      have hinj : Function.Injective f := by
        intro a b h
        dsimp only [f] at h
        have h1 : a.1 = b.1 := (Prod.mk.inj h).1
        have h2 : lineOf a.1 a.2 = lineOf b.1 b.2 := (Prod.mk.inj h).2
        rw [h1] at h2
        exact Prod.ext h1 (hlineOf_inj b.1 a.2 b.2 h2)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin] at h1
      exact h1
    have hComp (x : Fin 42 → Bool) :
        wireVal 42 C C.output x =
          decide (∃ (p l : Fin 21), (p, l) ∈ E ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true) := by
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      have hc : wireVal 42 C C.output x = true ↔ Hpg x := hComp_iff x
      rw [hc]
      constructor
      · rintro ⟨u, v, ⟨hu21, hv21, hmod⟩, hxu, hxv⟩
        refine ⟨⟨u.val, hu21⟩, ⟨v.val - 21, by omega⟩, ?_, ?_, ?_⟩
        · rw [hmem_E]
          change (v.val - 21 + 21 - u.val) % 21 ∈ D5
          have h1 : (v.val - 21 + 21 - u.val) % 21 = (v.val + 21 - u.val) % 21 := by omega
          rw [h1]; exact hmod
        · convert hxu using 2; apply Fin.ext; rfl
        · convert hxv using 2; apply Fin.ext; change 21 + (v.val - 21) = v.val; omega
      · rintro ⟨p, l, hpl, hp, hl⟩
        refine ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, ⟨p.isLt, by change 21 ≤ 21 + l.val; omega, ?_⟩, hp, hl⟩
        have hI := (hmem_E p l).mp hpl
        change (21 + l.val + 21 - p.val) % 21 ∈ D5
        have h1 : (21 + l.val + 21 - p.val) % 21 = (l.val + 21 - p.val) % 21 := by omega
        rw [h1]; exact hI
    have hRB : ReadsBack 42 C := hAO2.2.1
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
    let pts (w : ℕ) : Finset (Fin 21) := Finset.univ.filter (fun p => OrPath w p.val)
    let lns (w : ℕ) : Finset (Fin 21) := Finset.univ.filter (fun l => OrPath w (21 + l.val))
    have hno_pts_only (x : Fin N → Bool) (h0 : ∀ l : Fin 21, x (Fin.natAdd 21 l) = false) :
        wireVal N C C.output x = false := by
      rw [hComp, decide_eq_false_iff_not]
      rintro ⟨p, l, _, _, hl⟩
      rw [h0 l] at hl; cases hl
    have hno_lns_only (x : Fin N → Bool) (h0 : ∀ p : Fin 21, x (Fin.castAdd 21 p) = false) :
        wireVal N C C.output x = false := by
      rw [hComp, decide_eq_false_iff_not]
      rintro ⟨p, l, _, hp, _⟩
      rw [h0 p] at hp; cases hp
    have hedge_covered : ∀ p l : Fin 21, (p, l) ∈ E →
        ∃ j : Fin C.gates.length, (gateAt C j.val).op = GateOp.and ∧
          OrPath C.output (N + j.val) ∧
          ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
            ((OrPath a p.val ∧ OrPath b (21 + l.val)) ∨
             (OrPath a (21 + l.val) ∧ OrPath b p.val)) := by
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
        ∃ p l : Fin 21, ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
          ((OrPath a p.val ∧ OrPath b (21 + l.val)) ∨
           (OrPath a (21 + l.val) ∧ OrPath b p.val)))
    let pWire (j : Fin C.gates.length) : ℕ :=
      let a := (gateAt C j.val).inputs.getD 0 0
      let b := (gateAt C j.val).inputs.getD 1 0
      if (pts a).Nonempty then a else b
    let lWire (j : Fin C.gates.length) : ℕ :=
      let a := (gateAt C j.val).inputs.getD 0 0
      let b := (gateAt C j.val).inputs.getD 1 0
      if (pts a).Nonempty then b else a
    let pSide (j : Fin C.gates.length) : Finset (Fin 21) := pts (pWire j)
    let lSide (j : Fin C.gates.length) : Finset (Fin 21) := lns (lWire j)
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
        let x : Fin N → Bool := fun i => decide (i = Fin.castAdd 21 p1 ∨ i = Fin.castAdd 21 p2)
        have h1 : wireVal N C p1.val x = true := by
          have := wireVal_input (Fin.castAdd 21 p1) x; simpa [x] using this
        have h2 : wireVal N C p2.val x = true := by
          have := wireVal_input (Fin.castAdd 21 p2) x; simpa [x] using this
        have ht := hand_sound x
          (orPath_sound (Finset.mem_filter.mp hp1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hp2).2 x h2)
        have hf := hno_pts_only x (fun l => by
          simp only [x, decide_eq_false_iff_not]
          rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
        rw [ht] at hf; cases hf
      have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
        rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
        let x : Fin N → Bool := fun i => decide (i = Fin.natAdd 21 l1 ∨ i = Fin.natAdd 21 l2)
        have h1 : wireVal N C (21 + l1.val) x = true := by
          have := wireVal_input (Fin.natAdd 21 l1) x; simpa [x, Nat.add_comm] using this
        have h2 : wireVal N C (21 + l2.val) x = true := by
          have := wireVal_input (Fin.natAdd 21 l2) x; simpa [x, Nat.add_comm] using this
        have ht := hand_sound x
          (orPath_sound (Finset.mem_filter.mp hl1).2 x h1)
          (orPath_sound (Finset.mem_filter.mp hl2).2 x h2)
        have hf := hno_lns_only x (fun p => by
          simp only [x, decide_eq_false_iff_not]
          rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
        rw [ht] at hf; cases hf
      have hbiclique : ∀ (p l : Fin 21),
          ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → (p, l) ∈ E := by
        intro p l hpl
        let x : Fin N → Bool := fun i => decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l)
        have hxp : wireVal N C p.val x = true := by
          have := wireVal_input (Fin.castAdd 21 p) x; simpa [x] using this
        have hxl : wireVal N C (21 + l.val) x = true := by
          have := wireVal_input (Fin.natAdd 21 l) x; simpa [x, Nat.add_comm] using this
        have hout_t : wireVal N C C.output x = true := by
          rcases hpl with ⟨hpa, hlb⟩ | ⟨hpb, hla⟩
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hpa).2 x hxp)
              (orPath_sound (Finset.mem_filter.mp hlb).2 x hxl)
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hla).2 x hxl)
              (orPath_sound (Finset.mem_filter.mp hpb).2 x hxp)
        rw [hComp, decide_eq_true_eq] at hout_t
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
    have hE_in_Tstar : ∀ p l : Fin 21, (p, l) ∈ E →
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
      ext j
      simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h1 : (pSide j).card = 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr ⟨h, h1⟩
    have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
      rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
    let centerP (j : Fin C.gates.length) : Fin 21 :=
      if h : (pSide j).Nonempty then h.choose else 0
    let centerL (j : Fin C.gates.length) : Fin 21 :=
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
    let A : Finset (Fin 21) := Tpt.image centerP
    let B : Finset (Fin 21) := Tln.image centerL
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
    have hAB_ge21 : 21 ≤ A.card + B.card := by
      have hsub : (Finset.univ : Finset (Fin 21)) ⊆ A ∪ B := by
        intro p _
        rcases hcover (p, p) ((hmem_E p p).mpr (hI_diag p)) with hpA | hpB
        · exact Finset.mem_union_left _ hpA
        · exact Finset.mem_union_right _ hpB
      have h1 := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      have h2 := Finset.card_union_le A B
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
    let Tpt_p (p : Fin 21) : Finset (Fin C.gates.length) := Tpt.filter (fun j => centerP j = p)
    let E_p (p : Fin 21) : Finset (Fin 21) := (Tpt_p p).biUnion lSide
    let Obot_p (p : Fin 21) : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        2 ≤ (lns (N + o.val)).card ∧
        ∃ j ∈ Tpt_p p, OrPath (lWire j) (N + o.val))
    let Tln_l (l : Fin 21) : Finset (Fin C.gates.length) := Tln.filter (fun j => centerL j = l)
    let E_l (l : Fin 21) : Finset (Fin 21) := (Tln_l l).biUnion pSide
    let Obot_l (l : Fin 21) : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        2 ≤ (pts (N + o.val)).card ∧
        ∃ j ∈ Tln_l l, OrPath (pWire j) (N + o.val))
    have hEp_bound : ∀ p ∈ A, (E_p p).card ≤ (Obot_p p).card + (Tpt_p p).card := by
      intro p _
      exact side_component_bound
        (fun l : Fin 21 => 21 + l.val) (fun l => by omega)
        (fun l1 l2 h => Fin.ext (by dsimp only at h; omega))
        (Tpt_p p) lWire
        (fun j hj => by
          obtain ⟨l, hl⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.2.1
          exact ⟨l, (Finset.mem_filter.mp hl).2⟩)
    have hEl_bound : ∀ l ∈ B, (E_l l).card ≤ (Obot_l l).card + (Tln_l l).card := by
      intro l _
      exact side_component_bound
        (fun p : Fin 21 => p.val) (fun p => by omega)
        (fun p1 p2 h => Fin.ext h)
        (Tln_l l) pWire
        (fun j hj => by
          obtain ⟨p, hp⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.1
          exact ⟨p, (Finset.mem_filter.mp hp).2⟩)
    have hObot_p_disj : Set.PairwiseDisjoint (A : Set (Fin 21)) Obot_p := by
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
    have hObot_l_disj : Set.PairwiseDisjoint (B : Set (Fin 21)) Obot_l := by
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
        let x : Fin N → Bool := fun i => decide (i = Fin.natAdd 21 l0)
        have hx_l : wireVal N C (21 + l0.val) x = true := by
          have := wireVal_input (Fin.natAdd 21 l0) x; simpa [x, Nat.add_comm] using this
        have ht := orPath_sound hop x hx_l
        have hf := hno_lns_only x (fun p' => by
          simp only [x, decide_eq_false_iff_not]
          intro h; have := congrArg Fin.val h; simp at this; omega)
        rw [ht] at hf; cases hf
      · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
        have hcard := (Finset.mem_filter.mp ho).2.2.1
        obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < (pts (N + o.val)).card)
        have hop := orPath_trans hop_out (Finset.mem_filter.mp hp0).2
        let x : Fin N → Bool := fun i => decide (i = Fin.castAdd 21 p0)
        have hx_p : wireVal N C p0.val x = true := by
          have := wireVal_input (Fin.castAdd 21 p0) x; simpa [x] using this
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
  have huncov_any (C : Circuit) (hAO : IsAO2 42 C) (hsz : C.size ≤ 124)
      (hpg : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ Hpg x) :
      ∃ p l : Fin 21, I p l ∧
        ¬ ∃ j a b : ℕ, andOn C j a b ∧
          orp C 42 (42 + j) C.output ∧
          orp C 42 p.val a ∧
          orp C 42 (21 + l.val) b := by
    by_contra hall_not
    have hall : ∀ p l : Fin 21, I p l →
        ∃ j a b : ℕ, andOn C j a b ∧
          orp C 42 (42 + j) C.output ∧
          orp C 42 p.val a ∧
          orp C 42 (21 + l.val) b := by
      intro p l hpl
      by_contra hno
      exact hall_not ⟨p, l, hpl, hno⟩
    have h126 := hstar_bound C hAO hpg hall
    omega
  have apply_aut (D : Circuit) (hAO : IsAO2 42 D)
      (hpg : ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔ Hpg x)
      (π πinv : ℕ → ℕ)
      (hπ_lt : ∀ w < 42, π w < 42) (hπinv_lt : ∀ w < 42, πinv w < 42)
      (hπ_ge : ∀ w, 42 ≤ w → π w = w) (hπinv_ge : ∀ w, 42 ≤ w → πinv w = w)
      (hπinv_π : ∀ w, πinv (π w) = w) (hπ_πinv : ∀ w, π (πinv w) = w)
      (hπ_Hpg : ∀ f : Fin 42 → Bool, Hpg f ↔ Hpg (fun t => f ⟨π t.val, hπ_lt t.val t.isLt⟩)) :
      let mapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map π⟩
      let D' : Circuit := ⟨D.gates.map mapGate, π D.output⟩
      D'.size = D.size ∧
      IsAO2 42 D' ∧
      (∀ x : Fin 42 → Bool, D'.eval (List.ofFn x) = true ↔ Hpg x) ∧
      (∀ f : Fin 42 → Bool, ∀ w : ℕ, wval D' f (π w) = wval D (fun t => f ⟨π t.val, hπ_lt t.val t.isLt⟩) w) ∧
      (∀ j a b : ℕ, andOn D j a b → andOn D' j (π a) (π b)) ∧
      (∀ j a b : ℕ, andOn D' j a b → andOn D j (πinv a) (πinv b)) ∧
      (∀ x y : ℕ, orp D 42 x y → orp D' 42 (π x) (π y)) ∧
      (∀ x y : ℕ, orp D' 42 x y → orp D 42 (πinv x) (πinv y)) := by
    let mapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map π⟩
    let D' : Circuit := ⟨D.gates.map mapGate, π D.output⟩
    have hD'_sz : D'.size = D.size := by
      change (D.gates.map mapGate).length = D.gates.length
      exact List.length_map _
    have hD'_gate (j : ℕ) (hj : j < D.gates.length) : gateAt D' j = mapGate (gateAt D j) := by
      have hj' : j < (D.gates.map mapGate).length := by rw [List.length_map]; exact hj
      change (D.gates.map mapGate).getD j ⟨GateOp.or, []⟩ = mapGate (D.gates.getD j ⟨GateOp.or, []⟩)
      rw [List.getD_eq_getElem _ _ hj', List.getElem_map, List.getD_eq_getElem _ _ hj]
    have hD'_AO : IsAO2 42 D' := by
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        change g' ∈ D.gates.map mapGate at hg'
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact hAO.1 g hg
      · intro j hj u hu
        have hj0 : j < D.gates.length := by
          change j < (D.gates.map mapGate).length at hj
          rw [List.length_map] at hj; exact hj
        rw [hD'_gate j hj0] at hu
        change u ∈ (gateAt D j).inputs.map π at hu
        rw [List.mem_map] at hu
        obtain ⟨i, hi, rfl⟩ := hu
        have hi_lt := hAO.2.1 j hj0 i hi
        by_cases hi42 : i < 42
        · have h := hπ_lt i hi42; omega
        · rw [hπ_ge i (by omega)]; exact hi_lt
      · intro g' hg'
        change g' ∈ D.gates.map mapGate at hg'
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        change (g.inputs.map π).length = 2
        rw [List.length_map]
        exact hAO.2.2 g hg
    have run_perm (gs : List Gate) (w1 w2 : List Bool) (hlen : w1.length = w2.length) (h42 : 42 ≤ w1.length)
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
            have hπl : π w1.length = w1.length := hπ_ge w1.length h42
            rw [hπl, getD_snoc_eq w1 _ false, hlen, getD_snoc_eq w2 _ false]
          · have hπj : π j ≠ w2.length := by
              intro heq
              have h1 : j = πinv w2.length := by rw [← heq, hπinv_π j]
              rw [← hlen, hπinv_ge w1.length h42] at h1
              exact hj h1
            rw [getD_snoc_ne w2 _ false (π j) hπj, getD_snoc_ne w1 _ false j hj]
            exact hrel j
    have hwval_eq (f : Fin 42 → Bool) (w : ℕ) :
        wval D' f (π w) = wval D (fun t => f ⟨π t.val, hπ_lt t.val t.isLt⟩) w := by
      have hrel : ∀ j, (List.ofFn f).getD (π j) false =
          (List.ofFn fun t : Fin 42 => f ⟨π t.val, hπ_lt t.val t.isLt⟩).getD j false := by
        intro j
        by_cases hj : j < 42
        · have hπj : π j < 42 := hπ_lt j hj
          have h1 : π j < (List.ofFn f).length := by simp only [List.length_ofFn]; exact hπj
          have h2 : j < (List.ofFn fun t : Fin 42 => f ⟨π t.val, hπ_lt t.val t.isLt⟩).length := by
            simp only [List.length_ofFn]; exact hj
          rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn,
              List.getD_eq_getElem _ _ h2, List.getElem_ofFn]
        · rw [hπ_ge j (by omega),
              List.getD_eq_default _ false (n := j) (by simp only [List.length_ofFn]; omega),
              List.getD_eq_default _ false (n := j) (by simp only [List.length_ofFn]; omega)]
      exact run_perm D.gates (List.ofFn fun t : Fin 42 => f ⟨π t.val, hπ_lt t.val t.isLt⟩) (List.ofFn f)
        (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega) hrel w
    have hD'_pg (f : Fin 42 → Bool) : D'.eval (List.ofFn f) = true ↔ Hpg f := by
      have hev : D'.eval (List.ofFn f) = D.eval (List.ofFn fun t : Fin 42 => f ⟨π t.val, hπ_lt t.val t.isLt⟩) :=
        hwval_eq f D.output
      rw [hev, hpg, ← hπ_Hpg f]
    have hgate_in2 (j : ℕ) (hj : j < D.gates.length) :
        ∃ u v : ℕ, (gateAt D j).inputs = [u, v] ∧ in0 D j = u ∧ in1 D j = v ∧
          in0 D' j = π u ∧ in1 D' j = π v := by
      have hmem : gateAt D j ∈ D.gates := by
        change D.gates.getD j ⟨GateOp.or, []⟩ ∈ D.gates
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      have hlen2 := hAO.2.2 _ hmem
      cases hins : (gateAt D j).inputs with
      | nil => rw [hins] at hlen2; cases hlen2
      | cons u t1 =>
        cases t1 with
        | nil => rw [hins] at hlen2; cases hlen2
        | cons v t2 =>
          cases t2 with
          | cons _ _ => rw [hins] at hlen2; cases hlen2
          | nil =>
            refine ⟨u, v, rfl, ?_, ?_, ?_, ?_⟩
            · change (gateAt D j).inputs.getD 0 0 = u; rw [hins]; rfl
            · change (gateAt D j).inputs.getD 1 0 = v; rw [hins]; rfl
            · change (gateAt D' j).inputs.getD 0 0 = π u
              rw [hD'_gate j hj]; change ((gateAt D j).inputs.map π).getD 0 0 = π u; rw [hins]; rfl
            · change (gateAt D' j).inputs.getD 1 0 = π v
              rw [hD'_gate j hj]; change ((gateAt D j).inputs.map π).getD 1 0 = π v; rw [hins]; rfl
    have hand_push (j a b : ℕ) (h : andOn D j a b) : andOn D' j (π a) (π b) := by
      obtain ⟨⟨hj, hand⟩, hord⟩ := h
      obtain ⟨u, v, _, h0D, h1D, h0D', h1D'⟩ := hgate_in2 j hj
      have hj' : j < D'.gates.length := by change j < (D.gates.map mapGate).length; rw [List.length_map]; exact hj
      refine ⟨⟨hj', by rw [hD'_gate j hj]; exact hand⟩, ?_⟩
      rw [h0D, h1D] at hord
      rw [h0D', h1D']
      rcases hord with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    have hand_pull (j a b : ℕ) (h : andOn D' j a b) : andOn D j (πinv a) (πinv b) := by
      obtain ⟨⟨hj', hand'⟩, hord⟩ := h
      have hj : j < D.gates.length := by
        change j < (D.gates.map mapGate).length at hj'; rw [List.length_map] at hj'; exact hj'
      obtain ⟨u, v, _, h0D, h1D, h0D', h1D'⟩ := hgate_in2 j hj
      refine ⟨⟨hj, by rw [hD'_gate j hj] at hand'; exact hand'⟩, ?_⟩
      rw [h0D', h1D'] at hord
      rw [h0D, h1D]
      rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [← h1, hπinv_π], by rw [← h2, hπinv_π]⟩
      · exact Or.inr ⟨by rw [← h1, hπinv_π], by rw [← h2, hπinv_π]⟩
    have horp_push (x y : ℕ) (h : orp D 42 x y) : orp D' 42 (π x) (π y) := by
      change Relation.ReflTransGen _ x y at h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail m _ _ hstep ih =>
        obtain ⟨hlt, k, rfl, ⟨hk, hor⟩, ha⟩ := hstep
        have hk' : k < D'.gates.length := by change k < (D.gates.map mapGate).length; rw [List.length_map]; exact hk
        have hlt' : π m < 42 + k := by
          by_cases h42 : m < 42
          · have := hπ_lt m h42; omega
          · rw [hπ_ge m (by omega)]; exact hlt
        rw [hπ_ge (42 + k) (by omega)]
        exact Relation.ReflTransGen.tail ih
          ⟨hlt', k, rfl, ⟨hk', by rw [hD'_gate k hk]; exact hor⟩,
            by rw [hD'_gate k hk]; exact List.mem_map_of_mem ha⟩
    have horp_pull (x y : ℕ) (h : orp D' 42 x y) : orp D 42 (πinv x) (πinv y) := by
      change Relation.ReflTransGen _ x y at h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        obtain ⟨_, k, rfl, ⟨hk', hor'⟩, ha⟩ := hstep
        have hk : k < D.gates.length := by
          change k < (D.gates.map mapGate).length at hk'; rw [List.length_map] at hk'; exact hk'
        rw [hD'_gate k hk] at hor' ha
        change _ ∈ (gateAt D k).inputs.map π at ha
        rw [List.mem_map] at ha
        obtain ⟨a0, ha0, ha0eq⟩ := ha
        rw [← ha0eq, hπinv_π a0] at ih
        rw [hπinv_ge (42 + k) (by omega)]
        exact Relation.ReflTransGen.tail ih ⟨hAO.2.1 k hk a0 ha0, k, rfl, ⟨hk, hor'⟩, ha0⟩
    exact ⟨hD'_sz, hD'_AO, hD'_pg, hwval_eq, hand_push, hand_pull, horp_push, horp_pull⟩
  let sh (s : ℕ) (w : ℕ) : ℕ :=
    if w < 21 then (w + s) % 21 else if w < 42 then 21 + (w - 21 + s) % 21 else w
  have hsh_lt (s w : ℕ) (hw : w < 42) : sh s w < 42 := by
    dsimp only [sh]
    by_cases h21 : w < 21
    · rw [ite_eq_left_iff.mpr (fun h => absurd h21 h)]
      have := Nat.mod_lt (w + s) (show 0 < 21 by omega); omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd hw h)]
      have := Nat.mod_lt (w - 21 + s) (show 0 < 21 by omega); omega
  have hsh_ge (s w : ℕ) (hw : 42 ≤ w) : sh s w = w := by
    dsimp only [sh]
    rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
  have hsh_inv (s w : ℕ) : sh ((21 - s % 21) % 21) (sh s w) = w := by
    by_cases h21 : w < 21
    · dsimp only [sh]
      have h1 : (w + s) % 21 < 21 := Nat.mod_lt _ (by omega)
      rw [ite_eq_left_iff.mpr (fun h => absurd h21 h), ite_eq_left_iff.mpr (fun h => absurd h1 h)]
      omega
    · by_cases h42 : w < 42
      · dsimp only [sh]
        have h1 : (w - 21 + s) % 21 < 21 := Nat.mod_lt _ (by omega)
        rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd h42 h),
            ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (by omega)]
        omega
      · rw [hsh_ge s w (by omega), hsh_ge _ w (by omega)]
  have hsh_inv2 (s w : ℕ) : sh s (sh ((21 - s % 21) % 21) w) = w := by
    by_cases h21 : w < 21
    · dsimp only [sh]
      have h1 : (w + (21 - s % 21) % 21) % 21 < 21 := Nat.mod_lt _ (by omega)
      rw [ite_eq_left_iff.mpr (fun h => absurd h21 h), ite_eq_left_iff.mpr (fun h => absurd h1 h)]
      omega
    · by_cases h42 : w < 42
      · dsimp only [sh]
        have h1 : (w - 21 + (21 - s % 21) % 21) % 21 < 21 := Nat.mod_lt _ (by omega)
        rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd h42 h),
            ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (by omega)]
        omega
      · rw [hsh_ge _ w (by omega), hsh_ge s w (by omega)]
  have hsh_Hpg (s : ℕ) (f : Fin 42 → Bool) :
      Hpg f ↔ Hpg (fun t => f ⟨sh s t.val, hsh_lt s t.val t.isLt⟩) := by
    let s' := (21 - s % 21) % 21
    constructor
    · rintro ⟨u, v, ⟨hu, hv, hmod⟩, hfu, hfv⟩
      refine ⟨⟨sh s' u.val, hsh_lt s' u.val u.isLt⟩, ⟨sh s' v.val, hsh_lt s' v.val v.isLt⟩,
        ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · dsimp only [sh]; rw [ite_eq_left_iff.mpr (fun h => absurd hu h)]; exact Nat.mod_lt _ (by omega)
      · dsimp only [sh]; rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]; omega
      · dsimp only [sh]
        rw [ite_eq_left_iff.mpr (fun h => absurd hu h), ite_eq_right_iff.mpr (by omega),
            ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]
        have heq : (21 + (v.val - 21 + s') % 21 + 21 - (u.val + s') % 21) % 21 =
            (v.val + 21 - u.val) % 21 := by omega
        rw [heq]; exact hmod
      · convert hfu using 2; apply Fin.ext; exact hsh_inv2 s u.val
      · convert hfv using 2; apply Fin.ext; exact hsh_inv2 s v.val
    · rintro ⟨u, v, ⟨hu, hv, hmod⟩, hfu, hfv⟩
      refine ⟨⟨sh s u.val, hsh_lt s u.val u.isLt⟩, ⟨sh s v.val, hsh_lt s v.val v.isLt⟩,
        ⟨?_, ?_, ?_⟩, hfu, hfv⟩
      · dsimp only [sh]; rw [ite_eq_left_iff.mpr (fun h => absurd hu h)]; exact Nat.mod_lt _ (by omega)
      · dsimp only [sh]; rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]; omega
      · dsimp only [sh]
        rw [ite_eq_left_iff.mpr (fun h => absurd hu h), ite_eq_right_iff.mpr (by omega),
            ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]
        have heq : (21 + (v.val - 21 + s) % 21 + 21 - (u.val + s) % 21) % 21 =
            (v.val + 21 - u.val) % 21 := by omega
        rw [heq]; exact hmod
  let du (w : ℕ) : ℕ :=
    if w < 21 then 21 + (21 - w) % 21 else if w < 42 then (21 - (w - 21)) % 21 else w
  have hdu_lt (w : ℕ) (hw : w < 42) : du w < 42 := by
    dsimp only [du]
    by_cases h21 : w < 21
    · rw [ite_eq_left_iff.mpr (fun h => absurd h21 h)]
      have := Nat.mod_lt (21 - w) (show 0 < 21 by omega); omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd hw h)]
      have := Nat.mod_lt (21 - (w - 21)) (show 0 < 21 by omega); omega
  have hdu_ge (w : ℕ) (hw : 42 ≤ w) : du w = w := by
    dsimp only [du]
    rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
  have hdu_inv (w : ℕ) : du (du w) = w := by
    by_cases h21 : w < 21
    · dsimp only [du]
      have h1 : (21 - w) % 21 < 21 := Nat.mod_lt _ (by omega)
      rw [ite_eq_left_iff.mpr (fun h => absurd h21 h), ite_eq_right_iff.mpr (by omega),
          ite_eq_left_iff.mpr (by omega)]
      omega
    · by_cases h42 : w < 42
      · dsimp only [du]
        have h1 : (21 - (w - 21)) % 21 < 21 := Nat.mod_lt _ (by omega)
        rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd h42 h),
            ite_eq_left_iff.mpr (fun h => absurd h1 h)]
        omega
      · rw [hdu_ge w (by omega), hdu_ge w (by omega)]
  have hdu_Hpg (f : Fin 42 → Bool) :
      Hpg f ↔ Hpg (fun t => f ⟨du t.val, hdu_lt t.val t.isLt⟩) := by
    constructor
    · rintro ⟨u, v, ⟨hu, hv, hmod⟩, hfu, hfv⟩
      have hdu_u : du u.val = 21 + (21 - u.val) % 21 := by
        dsimp only [du]; rw [ite_eq_left_iff.mpr (fun h => absurd hu h)]
      have hdu_v : du v.val = (21 - (v.val - 21)) % 21 := by
        dsimp only [du]; rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]
      refine ⟨⟨du v.val, hdu_lt v.val v.isLt⟩, ⟨du u.val, hdu_lt u.val u.isLt⟩,
        ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · change du v.val < 21; rw [hdu_v]; exact Nat.mod_lt _ (by omega)
      · change 21 ≤ du u.val; rw [hdu_u]; omega
      · change (du u.val + 21 - du v.val) % 21 ∈ D5
        rw [hdu_u, hdu_v]
        have heq : (21 + (21 - u.val) % 21 + 21 - (21 - (v.val - 21)) % 21) % 21 =
            (v.val + 21 - u.val) % 21 := by omega
        rw [heq]; exact hmod
      · convert hfv using 2; apply Fin.ext; exact hdu_inv v.val
      · convert hfu using 2; apply Fin.ext; exact hdu_inv u.val
    · rintro ⟨u, v, ⟨hu, hv, hmod⟩, hfu, hfv⟩
      have hdu_u : du u.val = 21 + (21 - u.val) % 21 := by
        dsimp only [du]; rw [ite_eq_left_iff.mpr (fun h => absurd hu h)]
      have hdu_v : du v.val = (21 - (v.val - 21)) % 21 := by
        dsimp only [du]; rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]
      refine ⟨⟨du v.val, hdu_lt v.val v.isLt⟩, ⟨du u.val, hdu_lt u.val u.isLt⟩,
        ⟨?_, ?_, ?_⟩, hfv, hfu⟩
      · change du v.val < 21; rw [hdu_v]; exact Nat.mod_lt _ (by omega)
      · change 21 ≤ du u.val; rw [hdu_u]; omega
      · change (du u.val + 21 - du v.val) % 21 ∈ D5
        rw [hdu_u, hdu_v]
        have heq : (21 + (21 - u.val) % 21 + 21 - (21 - (v.val - 21)) % 21) % 21 =
            (v.val + 21 - u.val) % 21 := by omega
        rw [heq]; exact hmod
  let af (m s : ℕ) (w : ℕ) : ℕ :=
    if w < 21 then (m * w) % 21 else if w < 42 then 21 + (m * (w - 21) + s) % 21 else w
  have haf_lt (m s w : ℕ) (hw : w < 42) : af m s w < 42 := by
    dsimp only [af]
    by_cases h21 : w < 21
    · rw [ite_eq_left_iff.mpr (fun h => absurd h21 h)]
      have := Nat.mod_lt (m * w) (show 0 < 21 by omega); omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd hw h)]
      have := Nat.mod_lt (m * (w - 21) + s) (show 0 < 21 by omega); omega
  have haf_ge (m s w : ℕ) (hw : 42 ≤ w) : af m s w = w := by
    dsimp only [af]
    rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
  have haf_props (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ affTable) :
      (∀ w, af t.2.2.1 t.2.2.2 (af t.1 t.2.1 w) = w) ∧
      (∀ w, af t.1 t.2.1 (af t.2.2.1 t.2.2.2 w) = w) ∧
      (∀ f : Fin 42 → Bool, Hpg f ↔ Hpg (fun i => f ⟨af t.1 t.2.1 i.val, haf_lt t.1 t.2.1 i.val i.isLt⟩)) := by
    obtain ⟨hp_inv, hl_inv, hD_pres⟩ := haff_ok t ht
    have hinv1 (w : ℕ) : af t.2.2.1 t.2.2.2 (af t.1 t.2.1 w) = w := by
      by_cases h21 : w < 21
      · dsimp only [af]
        have h1 : (t.1 * w) % 21 < 21 := Nat.mod_lt _ (by omega)
        rw [ite_eq_left_iff.mpr (fun h => absurd h21 h), ite_eq_left_iff.mpr (fun h => absurd h1 h)]
        exact (hp_inv ⟨w, h21⟩).1
      · by_cases h42 : w < 42
        · dsimp only [af]
          have h1 : (t.1 * (w - 21) + t.2.1) % 21 < 21 := Nat.mod_lt _ (by omega)
          rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd h42 h),
              ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (by omega)]
          have h2 : 21 + (t.1 * (w - 21) + t.2.1) % 21 - 21 = (t.1 * (w - 21) + t.2.1) % 21 := by omega
          have h3 := (hl_inv ⟨w - 21, by omega⟩).1
          dsimp only at h3
          rw [h2, h3]; omega
        · rw [haf_ge t.1 t.2.1 w (by omega), haf_ge t.2.2.1 t.2.2.2 w (by omega)]
    have hinv2 (w : ℕ) : af t.1 t.2.1 (af t.2.2.1 t.2.2.2 w) = w := by
      by_cases h21 : w < 21
      · dsimp only [af]
        have h1 : (t.2.2.1 * w) % 21 < 21 := Nat.mod_lt _ (by omega)
        rw [ite_eq_left_iff.mpr (fun h => absurd h21 h), ite_eq_left_iff.mpr (fun h => absurd h1 h)]
        exact (hp_inv ⟨w, h21⟩).2
      · by_cases h42 : w < 42
        · dsimp only [af]
          have h1 : (t.2.2.1 * (w - 21) + t.2.2.2) % 21 < 21 := Nat.mod_lt _ (by omega)
          rw [ite_eq_right_iff.mpr (fun h => absurd h h21), ite_eq_left_iff.mpr (fun h => absurd h42 h),
              ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (by omega)]
          have h2 : 21 + (t.2.2.1 * (w - 21) + t.2.2.2) % 21 - 21 = (t.2.2.1 * (w - 21) + t.2.2.2) % 21 := by omega
          have h3 := (hl_inv ⟨w - 21, by omega⟩).2
          dsimp only at h3
          rw [h2, h3]; omega
        · rw [haf_ge t.2.2.1 t.2.2.2 w (by omega), haf_ge t.1 t.2.1 w (by omega)]
    refine ⟨hinv1, hinv2, fun f => ?_⟩
    constructor
    · rintro ⟨u, v, ⟨hu, hv, hmod⟩, hfu, hfv⟩
      refine ⟨⟨af t.2.2.1 t.2.2.2 u.val, haf_lt t.2.2.1 t.2.2.2 u.val u.isLt⟩,
        ⟨af t.2.2.1 t.2.2.2 v.val, haf_lt t.2.2.1 t.2.2.2 v.val v.isLt⟩,
        ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · dsimp only [af]; rw [ite_eq_left_iff.mpr (fun h => absurd hu h)]; exact Nat.mod_lt _ (by omega)
      · dsimp only [af]; rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]; omega
      · dsimp only [af]
        rw [ite_eq_left_iff.mpr (fun h => absurd hu h), ite_eq_right_iff.mpr (by omega),
            ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]
        have hstep1 : (21 + (t.2.2.1 * (v.val - 21) + t.2.2.2) % 21 + 21 - (t.2.2.1 * u.val) % 21) % 21 =
            ((t.2.2.1 * (v.val - 21) + t.2.2.2) % 21 + 21 - (t.2.2.1 * u.val) % 21) % 21 := by omega
        rw [hstep1, hmod_aff t.2.2.1 t.2.2.2 u.val (v.val - 21) hu (by omega)]
        have hstep2 : (v.val - 21 + 21 - u.val) % 21 = (v.val + 21 - u.val) % 21 := by omega
        rw [hstep2]
        exact (hD_pres _ hmod).2
      · convert hfu using 2; apply Fin.ext; exact hinv2 u.val
      · convert hfv using 2; apply Fin.ext; exact hinv2 v.val
    · rintro ⟨u, v, ⟨hu, hv, hmod⟩, hfu, hfv⟩
      refine ⟨⟨af t.1 t.2.1 u.val, haf_lt t.1 t.2.1 u.val u.isLt⟩,
        ⟨af t.1 t.2.1 v.val, haf_lt t.1 t.2.1 v.val v.isLt⟩,
        ⟨?_, ?_, ?_⟩, hfu, hfv⟩
      · dsimp only [af]; rw [ite_eq_left_iff.mpr (fun h => absurd hu h)]; exact Nat.mod_lt _ (by omega)
      · dsimp only [af]; rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]; omega
      · dsimp only [af]
        rw [ite_eq_left_iff.mpr (fun h => absurd hu h), ite_eq_right_iff.mpr (by omega),
            ite_eq_left_iff.mpr (fun h => absurd v.isLt h)]
        have hstep1 : (21 + (t.1 * (v.val - 21) + t.2.1) % 21 + 21 - (t.1 * u.val) % 21) % 21 =
            ((t.1 * (v.val - 21) + t.2.1) % 21 + 21 - (t.1 * u.val) % 21) % 21 := by omega
        rw [hstep1, hmod_aff t.1 t.2.1 u.val (v.val - 21) hu (by omega)]
        have hstep2 : (v.val - 21 + 21 - u.val) % 21 = (v.val + 21 - u.val) % 21 := by omega
        rw [hstep2]
        exact (hD_pres _ hmod).1
  have hzero_false (C : Circuit) (hAO : IsAO2 42 C) :
      ∀ w : ℕ, wval C (fun _ : Fin 42 => false) w = false := by
    have hrun_f : ∀ (gs : List Gate) (ws : List Bool),
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
        (∀ i, ws.getD i false = false) →
        ∀ i, (run gs ws).getD i false = false := by
      intro gs
      induction gs with
      | nil => intro ws _ hws; exact hws
      | cons g rest ih =>
        intro ws hgs hws
        simp only [run, List.foldl_cons]
        apply ih (step ws g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
        intro i
        dsimp only [step]
        by_cases hi : i = ws.length
        · subst hi
          rw [getD_snoc_eq ws _ false]
          have hg := hgs g List.mem_cons_self
          cases hins : g.inputs with
          | nil => rw [hins] at hg; cases hg.2
          | cons a t1 =>
            cases t1 with
            | nil => rw [hins] at hg; cases hg.2
            | cons b t2 =>
              cases t2 with
              | cons _ _ => rw [hins] at hg; cases hg.2
              | nil =>
                simp only [List.map_cons, List.map_nil, hws a, hws b]
                rcases hg.1 with hop | hop <;> (rw [hop]; rfl)
        · rw [getD_snoc_ne ws _ false i hi]; exact hws i
    apply hrun_f C.gates (List.ofFn fun _ : Fin 42 => false)
      (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩)
    intro i
    by_cases hi : i < 42
    · have h1 : i < (List.ofFn fun _ : Fin 42 => false).length := by simp only [List.length_ofFn]; exact hi
      rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
    · exact List.getD_eq_default _ false (n := i) (by simp only [List.length_ofFn]; omega)
  intro x1 x2 hMono hsz124 hcard2 hx2_sub hx2_and
  by_contra hno_err
  have hpg1 : ∀ x : Fin 42 → Bool, x1.eval (List.ofFn x) = true ↔ Hpg x := by
    intro x
    by_contra hne
    exact hno_err ⟨x, hne⟩
  let M0 : List (Bool ⊕ ℕ) := (List.range 42).map (Sum.inr : ℕ → Bool ⊕ ℕ)
  have hM0_len : M0.length = 42 := by simp only [M0, List.length_map, List.length_range]
  have hM0_lt (j : ℕ) (hj : j < 42) : M0.getD j (Sum.inl false) = Sum.inr j := by
    have hlt : j < M0.length := by rw [hM0_len]; exact hj
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [M0, List.getElem_map, List.getElem_range]
  let res := elim x1.gates (M0, [])
  have hbase (x : Fin 42 → Bool) : Inv (List.ofFn x) (List.ofFn x) (M0, []) := by
    refine ⟨List.length_ofFn, (by rw [hM0_len, List.length_ofFn]), (fun _ h => by cases h),
      (fun _ h _ _ => by simp only [List.length_nil] at h; omega), ?_⟩
    intro i
    by_cases hi : i < 42
    · rw [hM0_lt i hi]
      exact ⟨show i < 42 + 0 by omega, rfl⟩
    · rw [List.getD_eq_default M0 (Sum.inl false) (n := i) (by rw [hM0_len]; omega),
          List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega)]
      exact ⟨trivial, rfl⟩
  have hfin (x : Fin 42 → Bool) : Inv (List.ofFn x) (run x1.gates (List.ofFn x)) res :=
    elim_inv x1.gates (List.ofFn x) (List.ofFn x) (M0, []) hMono (hbase x)
  have hres_le : res.2.length ≤ x1.gates.length := by
    have h := elim_len x1.gates (M0, [])
    simp only [List.length_nil, Nat.zero_add] at h
    exact h
  have hHpg_false : ¬ Hpg (fun _ => false) := by
    rintro ⟨u, v, _, hu, _⟩; cases hu
  have hHpg_021 : Hpg (fun i : Fin 42 => decide (i.val = 0 ∨ i.val = 21)) :=
    ⟨(0 : Fin 42), (21 : Fin 42), ⟨by omega, by omega, by decide⟩, by decide, by decide⟩
  cases hout : res.1.getD x1.output (Sum.inl false) with
  | inl b =>
    cases b with
    | false =>
      have h1 := ((hfin (fun i => decide (i.val = 0 ∨ i.val = 21))).2.2.2.2 x1.output).2
      rw [hout] at h1
      have h2 := (hpg1 (fun i => decide (i.val = 0 ∨ i.val = 21))).mpr hHpg_021
      change false = x1.eval (List.ofFn fun i => decide (i.val = 0 ∨ i.val = 21)) at h1
      rw [h2] at h1; cases h1
    | true =>
      have h1 := ((hfin (fun _ => false)).2.2.2.2 x1.output).2
      rw [hout] at h1
      change true = x1.eval (List.ofFn fun _ => false) at h1
      exact hHpg_false ((hpg1 (fun _ => false)).mp h1.symm)
  | inr out =>
    let D : Circuit := ⟨res.2, out⟩
    have hD_AO : IsAO2 42 D := by
      have hf0 := hfin (fun _ => false)
      refine ⟨fun g hg => (hf0.2.2.1 g hg).1, ?_, fun g hg => (hf0.2.2.1 g hg).2⟩
      intro j hj i hi
      exact hf0.2.2.2.1 j hj i hi
    have hD_pg (x : Fin 42 → Bool) : D.eval (List.ofFn x) = true ↔ Hpg x := by
      have h := ((hfin x).2.2.2.2 x1.output).2
      rw [hout] at h
      change D.eval (List.ofFn x) = x1.eval (List.ofFn x) at h
      rw [h]; exact hpg1 x
    by_cases hD_le123 : D.size ≤ 123
    · obtain ⟨p0, l0, hI0, hunc0⟩ := huncov_any D hD_AO (by omega) hD_pg
      let s0 : ℕ := (21 - p0.val) % 21
      have hsh0 := apply_aut D hD_AO hD_pg (sh s0) (sh ((21 - s0 % 21) % 21))
        (hsh_lt s0) (hsh_lt _) (hsh_ge s0) (hsh_ge _) (hsh_inv s0) (hsh_inv2 s0) (hsh_Hpg s0)
      let D1 : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map (sh s0)⟩), sh s0 D.output⟩
      have hD1_sz : D1.size ≤ 123 := by rw [hsh0.1]; exact hD_le123
      let d0 : ℕ := (l0.val + 21 - p0.val) % 21
      have hd0_mem : d0 ∈ D5 := hI0
      obtain ⟨t, ht_mem, ht_hit⟩ := haff_edge d0 hd0_mem
      obtain ⟨ht_inv1, ht_inv2, ht_Hpg⟩ := haf_props t ht_mem
      have haf0 := apply_aut D1 hsh0.2.1 hsh0.2.2.1 (af t.1 t.2.1) (af t.2.2.1 t.2.2.2)
        (haf_lt t.1 t.2.1) (haf_lt t.2.2.1 t.2.2.2) (haf_ge t.1 t.2.1) (haf_ge t.2.2.1 t.2.2.2)
        ht_inv1 ht_inv2 ht_Hpg
      let D2 : Circuit := ⟨D1.gates.map (fun g => ⟨g.op, g.inputs.map (af t.1 t.2.1)⟩), af t.1 t.2.1 D1.output⟩
      have hD2_sz : D2.size ≤ 123 := by rw [haf0.1]; exact hD1_sz
      apply hSizeLe123 D2 haf0.2.1 hD2_sz haf0.2.2.1
      refine ⟨(t.1 * d0 + t.2.1) % 21, ht_hit, ?_⟩
      rintro ⟨j, a, b, hand2, htop2, h0a2, hdb2⟩
      have hand1 := haf0.2.2.2.2.2.1 j a b hand2
      have htop1 := haf0.2.2.2.2.2.2.2 _ _ htop2
      have h0a1 := haf0.2.2.2.2.2.2.2 _ _ h0a2
      have hdb1 := haf0.2.2.2.2.2.2.2 _ _ hdb2
      rw [haf_ge t.2.2.1 t.2.2.2 (42 + j) (by omega), ht_inv1 D1.output] at htop1
      have haf_0 : af t.2.2.1 t.2.2.2 0 = 0 := by
        dsimp only [af]; rw [ite_eq_left_iff.mpr (by omega)]; simp
      have haf_d : af t.2.2.1 t.2.2.2 (21 + (t.1 * d0 + t.2.1) % 21) = 21 + d0 := by
        have hd0_lt : d0 < 21 := Nat.mod_lt _ (by omega)
        have hstep : af t.1 t.2.1 (21 + d0) = 21 + (t.1 * d0 + t.2.1) % 21 := by
          dsimp only [af]
          rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (by omega)]
          have : 21 + d0 - 21 = d0 := by omega
          rw [this]
        rw [← hstep, ht_inv1 (21 + d0)]
      rw [haf_0] at h0a1
      rw [haf_d] at hdb1
      have hand0 := hsh0.2.2.2.2.2.1 j _ _ hand1
      have htop0 := hsh0.2.2.2.2.2.2.2 _ _ htop1
      have h0a0 := hsh0.2.2.2.2.2.2.2 _ _ h0a1
      have hdb0 := hsh0.2.2.2.2.2.2.2 _ _ hdb1
      rw [hsh_ge _ (42 + j) (by omega), hsh_inv s0 D.output] at htop0
      have hsh_0 : sh ((21 - s0 % 21) % 21) 0 = p0.val := by
        have hstep : sh s0 p0.val = 0 := by
          dsimp only [sh, s0]; rw [ite_eq_left_iff.mpr (fun h => absurd p0.isLt h)]; omega
        rw [← hstep, hsh_inv s0 p0.val]
      have hsh_d : sh ((21 - s0 % 21) % 21) (21 + d0) = 21 + l0.val := by
        have hstep : sh s0 (21 + l0.val) = 21 + d0 := by
          dsimp only [sh, s0, d0]
          rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (by omega)]
          omega
        rw [← hstep, hsh_inv s0 (21 + l0.val)]
      rw [hsh_0] at h0a0
      rw [hsh_d] at hdb0
      exact hunc0 ⟨j, _, _, hand0, htop0, h0a0, hdb0⟩
    · have hD_eq124 : D.size = 124 := by
        have h1 : D.size ≤ x1.size := hres_le
        omega
      have hx1_eq124 : x1.size = 124 := by
        have h1 : D.size ≤ x1.size := hres_le
        omega
      have hx1_AO : IsAO2 42 x1 := by
        have hfull := elim_full_ao2 x1.gates (M0, []) hMono rfl
          (by change res.2.length = 0 + x1.gates.length; have h1 : res.2.length = 124 := hD_eq124; have h2 : x1.gates.length = 124 := hx1_eq124; omega)
        refine ⟨fun g hg => (hfull.1 g hg).1, ?_, fun g hg => (hfull.1 g hg).2⟩
        intro j hj i hi
        have := hfull.2 j hj i hi
        simpa only [List.length_nil, Nat.add_zero] using this
      by_cases hunit : ∃ (v : Fin 42) (k : ℕ), isAnd x1 k ∧ wval x1 (fun i => decide (i = v)) (42 + k) = true
      · obtain ⟨v0, k_init, hk_init_and, hk_init_t⟩ := hunit
        have hex_min : ∃ k : ℕ, isAnd x1 k ∧ wval x1 (fun i => decide (i = v0)) (42 + k) = true ∧
            ∀ j < k, isAnd x1 j → wval x1 (fun i => decide (i = v0)) (42 + j) = false := by
          suffices hmin : ∀ m : ℕ, isAnd x1 m → wval x1 (fun i => decide (i = v0)) (42 + m) = true →
              ∃ k : ℕ, isAnd x1 k ∧ wval x1 (fun i => decide (i = v0)) (42 + k) = true ∧
                ∀ j < k, isAnd x1 j → wval x1 (fun i => decide (i = v0)) (42 + j) = false by
            exact hmin k_init hk_init_and hk_init_t
          intro m
          induction m using Nat.strong_induction_on with
          | ind m ih =>
            intro hm_and hm_t
            by_cases hsm : ∃ j < m, isAnd x1 j ∧ wval x1 (fun i => decide (i = v0)) (42 + j) = true
            · obtain ⟨j, hjlt, hjand, hjt⟩ := hsm
              exact ih j hjlt hjand hjt
            · refine ⟨m, hm_and, hm_t, fun j hjlt hjand => ?_⟩
              cases hval : wval x1 (fun i => decide (i = v0)) (42 + j) with
              | false => rfl
              | true => exact (hsm ⟨j, hjlt, hjand, hval⟩).elim
        obtain ⟨k, ⟨hk_lt, hk_and⟩, hk_t, hk_min⟩ := hex_min
        have hbelow_orp : ∀ w < 42 + k, wval x1 (fun i => decide (i = v0)) w = true → orp x1 42 v0.val w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw_lt hw_t
            by_cases hw42 : w < 42
            · have h1 : w < (List.ofFn fun i : Fin 42 => decide (i = v0)).length := by
                simp only [List.length_ofFn]; exact hw42
              have hr : wval x1 (fun i => decide (i = v0)) w = decide (⟨w, hw42⟩ = v0) := by
                change (run x1.gates (List.ofFn fun i : Fin 42 => decide (i = v0))).getD w false = _
                rw [run_keep x1.gates _ w h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
              rw [hr, decide_eq_true_eq] at hw_t
              have hveq : v0.val = w := (congrArg Fin.val hw_t).symm
              rw [hveq]; exact Relation.ReflTransGen.refl
            · let j : ℕ := w - 42
              have hjlt : j < k := by omega
              have hjlen : j < x1.gates.length := by omega
              let gj : Gate := x1.gates[j]
              have hgj_eq : x1.gates[j]? = some gj := List.getElem?_eq_getElem hjlen
              have hgat_j : gateAt x1 j = gj := by
                change x1.gates.getD j ⟨GateOp.or, []⟩ = gj
                rw [List.getD_eq_getElem _ _ hjlen]
              have hgj_mem : gj ∈ x1.gates := List.getElem_mem hjlen
              have hback_j : ∀ i ∈ gj.inputs, i < 42 + j := by
                intro i hi; have := hx1_AO.2.1 j hjlen i; rw [hgat_j] at this; exact this hi
              have heval_j : wval x1 (fun i => decide (i = v0)) (42 + j) =
                  gj.op.eval (gj.inputs.map fun i => wval x1 (fun i => decide (i = v0)) i) := by
                change (run x1.gates (List.ofFn fun i : Fin 42 => decide (i = v0))).getD (42 + j) false =
                  gj.op.eval (gj.inputs.map fun i => (run x1.gates (List.ofFn fun i : Fin 42 => decide (i = v0))).getD i false)
                have h := run_getD_gate x1.gates (List.ofFn fun i : Fin 42 => decide (i = v0)) j gj hgj_eq
                  (by simpa only [List.length_ofFn] using hback_j)
                simpa only [List.length_ofFn] using h
              have hwj : 42 + j = w := by omega
              rcases hx1_AO.1 gj hgj_mem with hja | hjo
              · have hf := hk_min j hjlt ⟨hjlen, by rw [hgat_j]; exact hja⟩
                rw [hwj] at hf; rw [hw_t] at hf; cases hf
              · rw [← hwj, heval_j, hjo] at hw_t
                change (gj.inputs.map fun i => wval x1 (fun i => decide (i = v0)) i).any id = true at hw_t
                rw [List.any_eq_true] at hw_t
                obtain ⟨b, hb, hbt⟩ := hw_t
                rw [List.mem_map] at hb
                obtain ⟨u, hu, rfl⟩ := hb
                have hult : u < 42 + j := hback_j u hu
                have hop_u := ih u (by omega) (by omega) hbt
                rw [← hwj]
                exact Relation.ReflTransGen.tail hop_u ⟨hult, j, rfl, ⟨hjlen, by rw [hgat_j]; exact hjo⟩, by rw [hgat_j]; exact hu⟩
        have hgat_k_mem : gateAt x1 k ∈ x1.gates := by
          change x1.gates.getD k ⟨GateOp.or, []⟩ ∈ x1.gates
          rw [List.getD_eq_getElem _ _ hk_lt]; exact List.getElem_mem hk_lt
        have hlen2_k := hx1_AO.2.2 _ hgat_k_mem
        have hk_pair : ∃ a c : ℕ, andOn x1 k a c ∧ orp x1 42 v0.val a ∧ orp x1 42 v0.val c := by
          cases hins : (gateAt x1 k).inputs with
          | nil => rw [hins] at hlen2_k; cases hlen2_k
          | cons a t1 =>
            cases t1 with
            | nil => rw [hins] at hlen2_k; cases hlen2_k
            | cons c t2 =>
              cases t2 with
              | cons _ _ => rw [hins] at hlen2_k; cases hlen2_k
              | nil =>
                have ha_lt : a < 42 + k := hx1_AO.2.1 k hk_lt a (by rw [hins]; exact List.mem_cons_self)
                have hc_lt : c < 42 + k := hx1_AO.2.1 k hk_lt c (by rw [hins]; exact List.mem_cons_of_mem _ List.mem_cons_self)
                have hgk_eq : x1.gates[k]? = some (gateAt x1 k) := by
                  change x1.gates[k]? = some (x1.gates.getD k ⟨GateOp.or, []⟩)
                  rw [List.getD_eq_getElem _ _ hk_lt, List.getElem?_eq_getElem hk_lt]
                have heval_k : wval x1 (fun i => decide (i = v0)) (42 + k) =
                    (wval x1 (fun i => decide (i = v0)) a && wval x1 (fun i => decide (i = v0)) c) := by
                  have hback_k : ∀ i ∈ (gateAt x1 k).inputs, i < 42 + k := hx1_AO.2.1 k hk_lt
                  have h := run_getD_gate x1.gates (List.ofFn fun i : Fin 42 => decide (i = v0)) k (gateAt x1 k) hgk_eq
                    (by simpa only [List.length_ofFn] using hback_k)
                  have h' : wval x1 (fun i => decide (i = v0)) (42 + k) =
                      (gateAt x1 k).op.eval ((gateAt x1 k).inputs.map fun i => wval x1 (fun i => decide (i = v0)) i) := by
                    change (run x1.gates (List.ofFn fun i : Fin 42 => decide (i = v0))).getD (42 + k) false =
                      (gateAt x1 k).op.eval ((gateAt x1 k).inputs.map fun i => (run x1.gates (List.ofFn fun j : Fin 42 => decide (j = v0))).getD i false)
                    simpa only [List.length_ofFn] using h
                  rw [h', hk_and, hins]
                  change (wval x1 (fun i => decide (i = v0)) a && (wval x1 (fun i => decide (i = v0)) c && true)) = _
                  rw [Bool.and_true]
                rw [heval_k, Bool.and_eq_true] at hk_t
                refine ⟨a, c, ⟨⟨hk_lt, hk_and⟩, Or.inl ⟨?_, ?_⟩⟩, hbelow_orp a ha_lt hk_t.1, hbelow_orp c hc_lt hk_t.2⟩
                · change (gateAt x1 k).inputs.getD 0 0 = a; rw [hins]; rfl
                · change (gateAt x1 k).inputs.getD 1 0 = c; rw [hins]; rfl
        obtain ⟨a0, c0, hand_k, horp_a, horp_c⟩ := hk_pair
        have hunit_from_pt (C0 : Circuit) (hC0_AO : IsAO2 42 C0) (hC0_sz : C0.size = 124)
            (hC0_pg : ∀ x : Fin 42 → Bool, C0.eval (List.ofFn x) = true ↔ Hpg x)
            (p : ℕ) (hp21 : p < 21) (k' a' c' : ℕ)
            (hand' : andOn C0 k' a' c') (ha' : orp C0 42 p a') (hc' : orp C0 42 p c') : False := by
          let s0 : ℕ := (21 - p) % 21
          have hsh0 := apply_aut C0 hC0_AO hC0_pg (sh s0) (sh ((21 - s0 % 21) % 21))
            (hsh_lt s0) (hsh_lt _) (hsh_ge s0) (hsh_ge _) (hsh_inv s0) (hsh_inv2 s0) (hsh_Hpg s0)
          let C1 : Circuit := ⟨C0.gates.map (fun g => ⟨g.op, g.inputs.map (sh s0)⟩), sh s0 C0.output⟩
          have hC1_sz : C1.size = 124 := hsh0.1.trans hC0_sz
          have hsh_p : sh s0 p = 0 := by
            dsimp only [sh, s0]; rw [ite_eq_left_iff.mpr (fun h => absurd hp21 h)]; omega
          have ha1 := hsh0.2.2.2.2.2.2.1 _ _ ha'
          have hc1 := hsh0.2.2.2.2.2.2.1 _ _ hc'
          rw [hsh_p] at ha1 hc1
          exact hSize124Unit C1 hsh0.2.1 hC1_sz hsh0.2.2.1
            (huncov_any C1 hsh0.2.1 (by omega) hsh0.2.2.1)
            ⟨k', sh s0 a', sh s0 c', hsh0.2.2.2.2.1 k' a' c' hand', ha1, hc1⟩
        by_cases hv21 : v0.val < 21
        · exact hunit_from_pt x1 hx1_AO hx1_eq124 hpg1 v0.val hv21 k a0 c0 hand_k horp_a horp_c
        · have hdu0 := apply_aut x1 hx1_AO hpg1 du du hdu_lt hdu_lt hdu_ge hdu_ge hdu_inv hdu_inv hdu_Hpg
          let Cdu : Circuit := ⟨x1.gates.map (fun g => ⟨g.op, g.inputs.map du⟩), du x1.output⟩
          have hdu_v : du v0.val < 21 := by
            dsimp only [du]
            rw [ite_eq_right_iff.mpr (fun h => absurd h hv21), ite_eq_left_iff.mpr (fun h => absurd v0.isLt h)]
            exact Nat.mod_lt _ (by omega)
          exact hunit_from_pt Cdu hdu0.2.1 (hdu0.1.trans hx1_eq124) hdu0.2.2.1
            (du v0.val) hdu_v k (du a0) (du c0)
            (hdu0.2.2.2.2.1 k a0 c0 hand_k)
            (hdu0.2.2.2.2.2.2.1 _ _ horp_a) (hdu0.2.2.2.2.2.2.1 _ _ horp_c)
      · have hclean1 : ∀ k : ℕ, isAnd x1 k →
            ∀ v : Fin 42, wval x1 (fun i => decide (i = v)) (42 + k) = false := by
          intro k hk v
          cases hval : wval x1 (fun i => decide (i = v)) (42 + k) with
          | false => rfl
          | true => exact (hunit ⟨v, k, hk, hval⟩).elim
        obtain ⟨k_w, g_w, hkw_eq, hkw_and, hkw_t⟩ := hx2_and
        have hkw_lt : k_w < x1.gates.length := (List.getElem?_eq_some_iff.mp hkw_eq).1
        have hgat_kw : gateAt x1 k_w = g_w := by
          have h1 := List.getElem?_eq_some_iff.mp hkw_eq
          change x1.gates.getD k_w ⟨GateOp.or, []⟩ = g_w
          rw [List.getD_eq_getElem _ _ hkw_lt]; exact h1.2
        have hx2_ne0 : x2.card ≠ 0 := by
          intro hc0
          have hem : x2 = ∅ := Finset.card_eq_zero.mp hc0
          have hfn : (fun i : Fin 42 => decide (i ∈ x2)) = (fun _ => false) := by
            funext i; rw [hem]; simp
          have hf := hzero_false x1 hx1_AO (42 + k_w)
          change wval x1 (fun i => decide (i ∈ x2)) (42 + k_w) = true at hkw_t
          rw [hfn, hf] at hkw_t; cases hkw_t
        have hx2_ne1 : x2.card ≠ 1 := by
          intro hc1
          obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc1
          have hfn : (fun i : Fin 42 => decide (i ∈ ({v} : Finset (Fin 42)))) = (fun i => decide (i = v)) := by
            funext i; simp only [Finset.mem_singleton]
          have hf := hclean1 k_w ⟨hkw_lt, by rw [hgat_kw]; exact hkw_and⟩ v
          change wval x1 (fun i => decide (i ∈ ({v} : Finset (Fin 42)))) (42 + k_w) = true at hkw_t
          rw [hfn, hf] at hkw_t; cases hkw_t
        have hx2_eq2 : x2.card = 2 := by omega
        obtain ⟨u0, v0, huv_ne, rfl⟩ := Finset.card_eq_two.mp hx2_eq2
        let xuv : Fin 42 → Bool := fun i => decide (i = u0 ∨ i = v0)
        have hxuv_eq : (fun i : Fin 42 => decide (i ∈ ({u0, v0} : Finset (Fin 42)))) = xuv := by
          funext i; simp only [xuv, Finset.mem_insert, Finset.mem_singleton]
        change wval x1 (fun i => decide (i ∈ ({u0, v0} : Finset (Fin 42)))) (42 + k_w) = true at hkw_t
        rw [hxuv_eq] at hkw_t
        have hex_min2 : ∃ k : ℕ, isAnd x1 k ∧ wval x1 xuv (42 + k) = true ∧
            ∀ j < k, isAnd x1 j → wval x1 xuv (42 + j) = false := by
          suffices hmin : ∀ m : ℕ, isAnd x1 m → wval x1 xuv (42 + m) = true →
              ∃ k : ℕ, isAnd x1 k ∧ wval x1 xuv (42 + k) = true ∧
                ∀ j < k, isAnd x1 j → wval x1 xuv (42 + j) = false by
            exact hmin k_w ⟨hkw_lt, by rw [hgat_kw]; exact hkw_and⟩ hkw_t
          intro m
          induction m using Nat.strong_induction_on with
          | ind m ih =>
            intro hm_and hm_t
            by_cases hsm : ∃ j < m, isAnd x1 j ∧ wval x1 xuv (42 + j) = true
            · obtain ⟨j, hjlt, hjand, hjt⟩ := hsm
              exact ih j hjlt hjand hjt
            · refine ⟨m, hm_and, hm_t, fun j hjlt hjand => ?_⟩
              cases hval : wval x1 xuv (42 + j) with
              | false => rfl
              | true => exact (hsm ⟨j, hjlt, hjand, hval⟩).elim
        obtain ⟨k, ⟨hk_lt, hk_and⟩, hk_t, hk_min⟩ := hex_min2
        have hbelow_orp2 : ∀ w < 42 + k, wval x1 xuv w = true →
            orp x1 42 u0.val w ∨ orp x1 42 v0.val w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw_lt hw_t
            by_cases hw42 : w < 42
            · have h1 : w < (List.ofFn xuv).length := by simp only [List.length_ofFn]; exact hw42
              have hr : wval x1 xuv w = xuv ⟨w, hw42⟩ := by
                change (run x1.gates (List.ofFn xuv)).getD w false = _
                rw [run_keep x1.gates _ w h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
              rw [hr] at hw_t
              simp only [xuv, decide_eq_true_eq] at hw_t
              rcases hw_t with hu | hv
              · left; rw [← congrArg Fin.val hu]; exact Relation.ReflTransGen.refl
              · right; rw [← congrArg Fin.val hv]; exact Relation.ReflTransGen.refl
            · let j : ℕ := w - 42
              have hjlt : j < k := by omega
              have hjlen : j < x1.gates.length := by omega
              let gj : Gate := x1.gates[j]
              have hgj_eq : x1.gates[j]? = some gj := List.getElem?_eq_getElem hjlen
              have hgat_j : gateAt x1 j = gj := by
                change x1.gates.getD j ⟨GateOp.or, []⟩ = gj
                rw [List.getD_eq_getElem _ _ hjlen]
              have hgj_mem : gj ∈ x1.gates := List.getElem_mem hjlen
              have hback_j : ∀ i ∈ gj.inputs, i < 42 + j := by
                intro i hi; have := hx1_AO.2.1 j hjlen i; rw [hgat_j] at this; exact this hi
              have heval_j : wval x1 xuv (42 + j) = gj.op.eval (gj.inputs.map fun i => wval x1 xuv i) := by
                change (run x1.gates (List.ofFn xuv)).getD (42 + j) false =
                  gj.op.eval (gj.inputs.map fun i => (run x1.gates (List.ofFn xuv)).getD i false)
                have h := run_getD_gate x1.gates (List.ofFn xuv) j gj hgj_eq
                  (by simpa only [List.length_ofFn] using hback_j)
                simpa only [List.length_ofFn] using h
              have hwj : 42 + j = w := by omega
              rcases hx1_AO.1 gj hgj_mem with hja | hjo
              · have hf := hk_min j hjlt ⟨hjlen, by rw [hgat_j]; exact hja⟩
                rw [hwj] at hf; rw [hw_t] at hf; cases hf
              · rw [← hwj, heval_j, hjo] at hw_t
                change (gj.inputs.map fun i => wval x1 xuv i).any id = true at hw_t
                rw [List.any_eq_true] at hw_t
                obtain ⟨b, hb, hbt⟩ := hw_t
                rw [List.mem_map] at hb
                obtain ⟨y, hy, rfl⟩ := hb
                have hylt : y < 42 + j := hback_j y hy
                have hstep_or : ∀ src, orp x1 42 src y → orp x1 42 src w := fun src hsrc => by
                  rw [← hwj]
                  exact Relation.ReflTransGen.tail hsrc ⟨hylt, j, rfl, ⟨hjlen, by rw [hgat_j]; exact hjo⟩, by rw [hgat_j]; exact hy⟩
                rcases ih y (by omega) (by omega) hbt with hop_u | hop_v
                · exact Or.inl (hstep_or u0.val hop_u)
                · exact Or.inr (hstep_or v0.val hop_v)
        have horp_sound_x1 (src : Fin 42) (w : ℕ) (h : orp x1 42 src.val w) :
            wval x1 (fun i => decide (i = src)) w = true := by
          change Relation.ReflTransGen _ src.val w at h
          induction h with
          | refl =>
            have h1 : src.val < (List.ofFn fun i : Fin 42 => decide (i = src)).length := by
              simp only [List.length_ofFn]; exact src.isLt
            change (run x1.gates (List.ofFn fun i : Fin 42 => decide (i = src))).getD src.val false = true
            rw [run_keep x1.gates _ src.val h1, List.getD_eq_getElem _ _ h1, List.getElem_ofFn]
            simp only [decide_eq_true_eq]
          | tail _ hstep ih =>
            obtain ⟨_, j, rfl, ⟨hjlen, hjor⟩, ha⟩ := hstep
            have hgj_eq : x1.gates[j]? = some (gateAt x1 j) := by
              change x1.gates[j]? = some (x1.gates.getD j ⟨GateOp.or, []⟩)
              rw [List.getD_eq_getElem _ _ hjlen, List.getElem?_eq_getElem hjlen]
            have hback_j : ∀ i ∈ (gateAt x1 j).inputs, i < 42 + j := hx1_AO.2.1 j hjlen
            have h := run_getD_gate x1.gates (List.ofFn fun i : Fin 42 => decide (i = src)) j (gateAt x1 j) hgj_eq
              (by simpa only [List.length_ofFn] using hback_j)
            have h' : wval x1 (fun i => decide (i = src)) (42 + j) =
                (gateAt x1 j).op.eval ((gateAt x1 j).inputs.map fun i => wval x1 (fun i => decide (i = src)) i) := by
              change (run x1.gates (List.ofFn fun i : Fin 42 => decide (i = src))).getD (42 + j) false =
                (gateAt x1 j).op.eval ((gateAt x1 j).inputs.map fun i => (run x1.gates (List.ofFn fun l : Fin 42 => decide (l = src))).getD i false)
              simpa only [List.length_ofFn] using h
            rw [h', hjor]
            change ((gateAt x1 j).inputs.map fun i => wval x1 (fun i => decide (i = src)) i).any id = true
            rw [List.any_eq_true]
            exact ⟨true, List.mem_map.mpr ⟨_, ha, ih⟩, rfl⟩
        have hgat_k_mem : gateAt x1 k ∈ x1.gates := by
          change x1.gates.getD k ⟨GateOp.or, []⟩ ∈ x1.gates
          rw [List.getD_eq_getElem _ _ hk_lt]; exact List.getElem_mem hk_lt
        have hlen2_k := hx1_AO.2.2 _ hgat_k_mem
        have hk_sep : ∃ a c : ℕ, andOn x1 k a c ∧ orp x1 42 u0.val a ∧ orp x1 42 v0.val c := by
          cases hins : (gateAt x1 k).inputs with
          | nil => rw [hins] at hlen2_k; cases hlen2_k
          | cons a t1 =>
            cases t1 with
            | nil => rw [hins] at hlen2_k; cases hlen2_k
            | cons c t2 =>
              cases t2 with
              | cons _ _ => rw [hins] at hlen2_k; cases hlen2_k
              | nil =>
                have ha_lt : a < 42 + k := hx1_AO.2.1 k hk_lt a (by rw [hins]; exact List.mem_cons_self)
                have hc_lt : c < 42 + k := hx1_AO.2.1 k hk_lt c (by rw [hins]; exact List.mem_cons_of_mem _ List.mem_cons_self)
                have hgk_eq : x1.gates[k]? = some (gateAt x1 k) := by
                  change x1.gates[k]? = some (x1.gates.getD k ⟨GateOp.or, []⟩)
                  rw [List.getD_eq_getElem _ _ hk_lt, List.getElem?_eq_getElem hk_lt]
                have heval_k_gen (f : Fin 42 → Bool) :
                    wval x1 f (42 + k) = (wval x1 f a && wval x1 f c) := by
                  have hback_k : ∀ i ∈ (gateAt x1 k).inputs, i < 42 + k := hx1_AO.2.1 k hk_lt
                  have h := run_getD_gate x1.gates (List.ofFn f) k (gateAt x1 k) hgk_eq
                    (by simpa only [List.length_ofFn] using hback_k)
                  have h' : wval x1 f (42 + k) =
                      (gateAt x1 k).op.eval ((gateAt x1 k).inputs.map fun i => wval x1 f i) := by
                    change (run x1.gates (List.ofFn f)).getD (42 + k) false =
                      (gateAt x1 k).op.eval ((gateAt x1 k).inputs.map fun i => (run x1.gates (List.ofFn f)).getD i false)
                    simpa only [List.length_ofFn] using h
                  rw [h', hk_and, hins]
                  change (wval x1 f a && (wval x1 f c && true)) = _
                  rw [Bool.and_true]
                rw [heval_k_gen xuv, Bool.and_eq_true] at hk_t
                have h0_in : in0 x1 k = a := by change (gateAt x1 k).inputs.getD 0 0 = a; rw [hins]; rfl
                have h1_in : in1 x1 k = c := by change (gateAt x1 k).inputs.getD 1 0 = c; rw [hins]; rfl
                rcases hbelow_orp2 a ha_lt hk_t.1 with hau | hav <;> rcases hbelow_orp2 c hc_lt hk_t.2 with hcu | hcv
                · exfalso
                  have h1 := hclean1 k ⟨hk_lt, hk_and⟩ u0
                  rw [heval_k_gen _, horp_sound_x1 u0 a hau, horp_sound_x1 u0 c hcu] at h1
                  cases h1
                · exact ⟨a, c, ⟨⟨hk_lt, hk_and⟩, Or.inl ⟨h0_in, h1_in⟩⟩, hau, hcv⟩
                · exact ⟨c, a, ⟨⟨hk_lt, hk_and⟩, Or.inr ⟨h0_in, h1_in⟩⟩, hcu, hav⟩
                · exfalso
                  have h1 := hclean1 k ⟨hk_lt, hk_and⟩ v0
                  rw [heval_k_gen _, horp_sound_x1 v0 a hav, horp_sound_x1 v0 c hcv] at h1
                  cases h1
        obtain ⟨a0, c0, hand_k, horp_u, horp_v⟩ := hk_sep
        have hclean_aut (C0 : Circuit) (hC0_AO : IsAO2 42 C0)
            (hC0_pg : ∀ x : Fin 42 → Bool, C0.eval (List.ofFn x) = true ↔ Hpg x)
            (hC0_clean : ∀ j : ℕ, isAnd C0 j → ∀ v : Fin 42, wval C0 (fun i => decide (i = v)) (42 + j) = false)
            (π πinv : ℕ → ℕ)
            (hπ_lt : ∀ w < 42, π w < 42) (hπinv_lt : ∀ w < 42, πinv w < 42)
            (hπ_ge : ∀ w, 42 ≤ w → π w = w) (hπinv_ge : ∀ w, 42 ≤ w → πinv w = w)
            (hπinv_π : ∀ w, πinv (π w) = w) (hπ_πinv : ∀ w, π (πinv w) = w)
            (hπ_Hpg : ∀ f : Fin 42 → Bool, Hpg f ↔ Hpg (fun t => f ⟨π t.val, hπ_lt t.val t.isLt⟩)) :
            let C1 : Circuit := ⟨C0.gates.map (fun g => ⟨g.op, g.inputs.map π⟩), π C0.output⟩
            ∀ j : ℕ, isAnd C1 j → ∀ v : Fin 42, wval C1 (fun i => decide (i = v)) (42 + j) = false := by
          have ha := apply_aut C0 hC0_AO hC0_pg π πinv hπ_lt hπinv_lt hπ_ge hπinv_ge hπinv_π hπ_πinv hπ_Hpg
          dsimp only
          intro j hj_and v
          obtain ⟨hj1, hj1_and⟩ := hj_and
          have hj0 : j < C0.gates.length := by
            change j < (C0.gates.map fun g => Gate.mk g.op (g.inputs.map π)).length at hj1
            rw [List.length_map] at hj1; exact hj1
          have hgat : gateAt (⟨C0.gates.map (fun g => Gate.mk g.op (g.inputs.map π)), π C0.output⟩ : Circuit) j =
              Gate.mk (gateAt C0 j).op ((gateAt C0 j).inputs.map π) := by
            change (C0.gates.map fun g => Gate.mk g.op (g.inputs.map π)).getD j ⟨GateOp.or, []⟩ =
              Gate.mk (C0.gates.getD j ⟨GateOp.or, []⟩).op ((C0.gates.getD j ⟨GateOp.or, []⟩).inputs.map π)
            rw [List.getD_eq_getElem _ _ hj1, List.getElem_map, List.getD_eq_getElem _ _ hj0]
          rw [hgat] at hj1_and
          have hw := ha.2.2.2.1 (fun i : Fin 42 => decide (i = v)) (42 + j)
          rw [hπ_ge (42 + j) (by omega)] at hw
          rw [hw]
          have hfn : (fun t : Fin 42 => decide (⟨π t.val, hπ_lt t.val t.isLt⟩ = v)) =
              (fun t : Fin 42 => decide (t = ⟨πinv v.val, hπinv_lt v.val v.isLt⟩)) := by
            funext t
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq]
            constructor
            · intro h; apply Fin.ext; change t.val = πinv v.val; have hv := congrArg Fin.val h; dsimp only at hv; rw [← hv, hπinv_π t.val]
            · intro h; apply Fin.ext; change π t.val = v.val; have hv := congrArg Fin.val h; dsimp only at hv; rw [hv, hπ_πinv v.val]
          rw [hfn]
          exact hC0_clean j ⟨hj0, hj1_and⟩ ⟨πinv v.val, hπinv_lt v.val v.isLt⟩
        have hsame_pts (C0 : Circuit) (hC0_AO : IsAO2 42 C0) (hC0_sz : C0.size = 124)
            (hC0_pg : ∀ x : Fin 42 → Bool, C0.eval (List.ofFn x) = true ↔ Hpg x)
            (hC0_clean : ∀ j : ℕ, isAnd C0 j → ∀ v : Fin 42, wval C0 (fun i => decide (i = v)) (42 + j) = false)
            (p1 p2 : ℕ) (hp1 : p1 < 21) (hp2 : p2 < 21) (hne : p1 ≠ p2)
            (k' a' c' : ℕ) (hand' : andOn C0 k' a' c') (ha' : orp C0 42 p1 a') (hc' : orp C0 42 p2 c') : False := by
          have hstep_to_rep (q1 q2 : ℕ) (hq1 : q1 < 21) (hq2 : q2 < 21)
              (a1 c1 : ℕ) (hand1 : andOn C0 k' a1 c1) (ha1 : orp C0 42 q1 a1) (hc1 : orp C0 42 q2 c1)
              (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ affTable)
              (hhit : (t.1 * ((q2 + 21 - q1) % 21)) % 21 ∈ ([1, 3, 7] : List ℕ)) : False := by
            let s0 : ℕ := (21 - q1) % 21
            have hsh0 := apply_aut C0 hC0_AO hC0_pg (sh s0) (sh ((21 - s0 % 21) % 21))
              (hsh_lt s0) (hsh_lt _) (hsh_ge s0) (hsh_ge _) (hsh_inv s0) (hsh_inv2 s0) (hsh_Hpg s0)
            let C1 : Circuit := ⟨C0.gates.map (fun g => ⟨g.op, g.inputs.map (sh s0)⟩), sh s0 C0.output⟩
            have hC1_clean := hclean_aut C0 hC0_AO hC0_pg hC0_clean (sh s0) (sh ((21 - s0 % 21) % 21))
              (hsh_lt s0) (hsh_lt _) (hsh_ge s0) (hsh_ge _) (hsh_inv s0) (hsh_inv2 s0) (hsh_Hpg s0)
            obtain ⟨ht_inv1, ht_inv2, ht_Hpg⟩ := haf_props t ht
            have haf0 := apply_aut C1 hsh0.2.1 hsh0.2.2.1 (af t.1 t.2.1) (af t.2.2.1 t.2.2.2)
              (haf_lt t.1 t.2.1) (haf_lt t.2.2.1 t.2.2.2) (haf_ge t.1 t.2.1) (haf_ge t.2.2.1 t.2.2.2)
              ht_inv1 ht_inv2 ht_Hpg
            let C2 : Circuit := ⟨C1.gates.map (fun g => ⟨g.op, g.inputs.map (af t.1 t.2.1)⟩), af t.1 t.2.1 C1.output⟩
            have hC2_clean := hclean_aut C1 hsh0.2.1 hsh0.2.2.1 hC1_clean (af t.1 t.2.1) (af t.2.2.1 t.2.2.2)
              (haf_lt t.1 t.2.1) (haf_lt t.2.2.1 t.2.2.2) (haf_ge t.1 t.2.1) (haf_ge t.2.2.1 t.2.2.2)
              ht_inv1 ht_inv2 ht_Hpg
            have hC2_sz : C2.size = 124 := haf0.1.trans (hsh0.1.trans hC0_sz)
            have hmap1 : af t.1 t.2.1 (sh s0 q1) = 0 := by
              have h1 : sh s0 q1 = 0 := by dsimp only [sh, s0]; rw [ite_eq_left_iff.mpr (fun h => absurd hq1 h)]; omega
              rw [h1]; dsimp only [af]; rw [ite_eq_left_iff.mpr (by omega)]; simp
            have hmap2 : af t.1 t.2.1 (sh s0 q2) = (t.1 * ((q2 + 21 - q1) % 21)) % 21 := by
              have h1 : sh s0 q2 = (q2 + 21 - q1) % 21 := by
                dsimp only [sh, s0]; rw [ite_eq_left_iff.mpr (fun h => absurd hq2 h)]; omega
              rw [h1]; dsimp only [af]; rw [ite_eq_left_iff.mpr (by have := Nat.mod_lt (q2 + 21 - q1) (show 0 < 21 by omega); omega)]
            have ha2 := haf0.2.2.2.2.2.2.1 _ _ (hsh0.2.2.2.2.2.2.1 _ _ ha1)
            have hc2 := haf0.2.2.2.2.2.2.1 _ _ (hsh0.2.2.2.2.2.2.1 _ _ hc1)
            rw [hmap1] at ha2; rw [hmap2] at hc2
            exact hSize124Same C2 haf0.2.1 hC2_sz haf0.2.2.1
              (huncov_any C2 haf0.2.1 (by omega) haf0.2.2.1) hC2_clean
              ⟨(t.1 * ((q2 + 21 - q1) % 21)) % 21, hhit, k',
                af t.1 t.2.1 (sh s0 a1), af t.1 t.2.1 (sh s0 c1),
                haf0.2.2.2.2.1 k' _ _ (hsh0.2.2.2.2.1 k' _ _ hand1), ha2, hc2⟩
          let diff : Fin 21 := ⟨(p2 + 21 - p1) % 21, Nat.mod_lt _ (by omega)⟩
          have hdiff_ne : diff.val ≠ 0 := by dsimp only [diff]; omega
          obtain ⟨t, ht_mem, hhit1 | hhit2⟩ := haff_same diff hdiff_ne
          · exact hstep_to_rep p1 p2 hp1 hp2 a' c' hand' ha' hc' t ht_mem hhit1
          · have hrev : 21 - diff.val = (p1 + 21 - p2) % 21 := by dsimp only [diff]; omega
            rw [hrev] at hhit2
            have hand_sym : andOn C0 k' c' a' := ⟨hand'.1, hand'.2.symm⟩
            exact hstep_to_rep p2 p1 hp2 hp1 c' a' hand_sym hc' ha' t ht_mem hhit2
        have hcross_pt_ln (p l : ℕ) (hp21 : p < 21) (hl21 : 21 ≤ l) (hl42 : l < 42)
            (hnonedge : (l + 21 - p) % 21 ∉ D5)
            (a1 c1 : ℕ) (hand1 : andOn x1 k a1 c1) (ha1 : orp x1 42 p a1) (hc1 : orp x1 42 l c1) : False := by
          let d : Fin 21 := ⟨(l + 21 - p) % 21, Nat.mod_lt _ (by omega)⟩
          obtain ⟨t, ht_mem, ht_hit⟩ := haff_cross d hnonedge
          let s0 : ℕ := (21 - p) % 21
          have hsh0 := apply_aut x1 hx1_AO hpg1 (sh s0) (sh ((21 - s0 % 21) % 21))
            (hsh_lt s0) (hsh_lt _) (hsh_ge s0) (hsh_ge _) (hsh_inv s0) (hsh_inv2 s0) (hsh_Hpg s0)
          let C1 : Circuit := ⟨x1.gates.map (fun g => ⟨g.op, g.inputs.map (sh s0)⟩), sh s0 x1.output⟩
          have hC1_clean := hclean_aut x1 hx1_AO hpg1 hclean1 (sh s0) (sh ((21 - s0 % 21) % 21))
            (hsh_lt s0) (hsh_lt _) (hsh_ge s0) (hsh_ge _) (hsh_inv s0) (hsh_inv2 s0) (hsh_Hpg s0)
          obtain ⟨ht_inv1, ht_inv2, ht_Hpg⟩ := haf_props t ht_mem
          have haf0 := apply_aut C1 hsh0.2.1 hsh0.2.2.1 (af t.1 t.2.1) (af t.2.2.1 t.2.2.2)
            (haf_lt t.1 t.2.1) (haf_lt t.2.2.1 t.2.2.2) (haf_ge t.1 t.2.1) (haf_ge t.2.2.1 t.2.2.2)
            ht_inv1 ht_inv2 ht_Hpg
          let C2 : Circuit := ⟨C1.gates.map (fun g => ⟨g.op, g.inputs.map (af t.1 t.2.1)⟩), af t.1 t.2.1 C1.output⟩
          have hC2_clean := hclean_aut C1 hsh0.2.1 hsh0.2.2.1 hC1_clean (af t.1 t.2.1) (af t.2.2.1 t.2.2.2)
            (haf_lt t.1 t.2.1) (haf_lt t.2.2.1 t.2.2.2) (haf_ge t.1 t.2.1) (haf_ge t.2.2.1 t.2.2.2)
            ht_inv1 ht_inv2 ht_Hpg
          have hC2_sz : C2.size = 124 := haf0.1.trans (hsh0.1.trans hx1_eq124)
          have hmap1 : af t.1 t.2.1 (sh s0 p) = 0 := by
            have h1 : sh s0 p = 0 := by dsimp only [sh, s0]; rw [ite_eq_left_iff.mpr (fun h => absurd hp21 h)]; omega
            rw [h1]; dsimp only [af]; rw [ite_eq_left_iff.mpr (by omega)]; simp
          have hmap2 : af t.1 t.2.1 (sh s0 l) = 21 + (t.1 * d.val + t.2.1) % 21 := by
            have h1 : sh s0 l = 21 + d.val := by
              dsimp only [sh, s0, d]
              rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (fun h => absurd hl42 h)]
              omega
            rw [h1]; dsimp only [af]
            rw [ite_eq_right_iff.mpr (by omega), ite_eq_left_iff.mpr (by have := d.isLt; omega)]
            have : 21 + d.val - 21 = d.val := by omega
            rw [this]
          have hhit2 : 21 + (t.1 * d.val + t.2.1) % 21 ∈ ([22, 23, 24, 35] : List ℕ) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht_hit ⊢
            rcases ht_hit with h | h | h | h <;> omega
          have ha2 := haf0.2.2.2.2.2.2.1 _ _ (hsh0.2.2.2.2.2.2.1 _ _ ha1)
          have hc2 := haf0.2.2.2.2.2.2.1 _ _ (hsh0.2.2.2.2.2.2.1 _ _ hc1)
          rw [hmap1] at ha2; rw [hmap2] at hc2
          exact hSize124Cross C2 haf0.2.1 hC2_sz haf0.2.2.1
            (huncov_any C2 haf0.2.1 (by omega) haf0.2.2.1) hC2_clean
            ⟨21 + (t.1 * d.val + t.2.1) % 21, hhit2, k,
              af t.1 t.2.1 (sh s0 a1), af t.1 t.2.1 (sh s0 c1),
              haf0.2.2.2.2.1 k _ _ (hsh0.2.2.2.2.1 k _ _ hand1), ha2, hc2⟩
        have hu0_S : u0.val ∈ S_indep := hx2_sub u0 (Finset.mem_insert_self u0 {v0})
        have hv0_S : v0.val ∈ S_indep := hx2_sub v0 (Finset.mem_insert_of_mem (Finset.mem_singleton_self v0))
        by_cases hu21 : u0.val < 21
        · by_cases hv21 : v0.val < 21
          · exact hsame_pts x1 hx1_AO hx1_eq124 hpg1 hclean1 u0.val v0.val hu21 hv21
              (fun h => huv_ne (Fin.ext h)) k a0 c0 hand_k horp_u horp_v
          · exact hcross_pt_ln u0.val v0.val hu21 (by omega) v0.isLt
              (hS_indep u0.val hu0_S v0.val hv0_S hu21 (by omega))
              a0 c0 hand_k horp_u horp_v
        · by_cases hv21 : v0.val < 21
          · exact hcross_pt_ln v0.val u0.val hv21 (by omega) u0.isLt
              (hS_indep v0.val hv0_S u0.val hu0_S hv21 (by omega))
              c0 a0 ⟨hand_k.1, hand_k.2.symm⟩ horp_v horp_u
          · have hdu0 := apply_aut x1 hx1_AO hpg1 du du hdu_lt hdu_lt hdu_ge hdu_ge hdu_inv hdu_inv hdu_Hpg
            let Cdu : Circuit := ⟨x1.gates.map (fun g => ⟨g.op, g.inputs.map du⟩), du x1.output⟩
            have hCdu_clean := hclean_aut x1 hx1_AO hpg1 hclean1 du du hdu_lt hdu_lt hdu_ge hdu_ge hdu_inv hdu_inv hdu_Hpg
            have hdu_u : du u0.val < 21 := by
              dsimp only [du]
              rw [ite_eq_right_iff.mpr (fun h => absurd h hu21), ite_eq_left_iff.mpr (fun h => absurd u0.isLt h)]
              exact Nat.mod_lt _ (by omega)
            have hdu_v : du v0.val < 21 := by
              dsimp only [du]
              rw [ite_eq_right_iff.mpr (fun h => absurd h hv21), ite_eq_left_iff.mpr (fun h => absurd v0.isLt h)]
              exact Nat.mod_lt _ (by omega)
            have hdu_ne : du u0.val ≠ du v0.val := by
              intro h
              have := congrArg du h
              rw [hdu_inv, hdu_inv] at this
              exact huv_ne (Fin.ext this)
            exact hsame_pts Cdu hdu0.2.1 (hdu0.1.trans hx1_eq124) hdu0.2.2.1 hCdu_clean
              (du u0.val) (du v0.val) hdu_u hdu_v hdu_ne k (du a0) (du c0)
              (hdu0.2.2.2.2.1 k a0 c0 hand_k)
              (hdu0.2.2.2.2.2.2.1 _ _ horp_u) (hdu0.2.2.2.2.2.2.1 _ _ horp_v)
