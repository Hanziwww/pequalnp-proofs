import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_2397_17
    (hNonGenericLine0 :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 D →
        D.size ≤ 63 →
        (∀ p l : Fin 13, I p l →
          PEqualNP.MetaComplexity.circuitFun 26 D (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        (∀ A B : Finset (Fin 13), A.card ≤ 2 → B.card ≤ 2 → (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) →
          PEqualNP.MetaComplexity.circuitFun 26 D
            (fun i => decide ((∃ p ∈ A, i = Fin.castAdd 13 p) ∨ (∃ l ∈ B, i = Fin.natAdd 13 l))) = false) →
        (∃ A B : Finset (Fin 13), (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) ∧ 3 ≤ {p ∈ A | I p 0}.card ∧
          PEqualNP.MetaComplexity.circuitFun 26 D
            (fun i => decide ((∃ p ∈ A, i = Fin.castAdd 13 p) ∨ (∃ l ∈ B, i = Fin.natAdd 13 l))) = true) →
        ∃ A B : Finset (Fin 13),
          (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) ∧
          (∀ l : Fin 13, {p ∈ A | I p l}.card ≤ 2) ∧
          (∀ p : Fin 13, {l ∈ B | I p l}.card ≤ 2) ∧
          PEqualNP.MetaComplexity.circuitFun 26 D
            (fun i => decide ((∃ p ∈ A, i = Fin.castAdd 13 p) ∨ (∃ l ∈ B, i = Fin.natAdd 13 l))) = true)
    (hExactCleanUncovered :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 D →
        D.size ≤ 63 →
        (∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 D x =
          decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) →
        (∃ (p l : Fin 13), I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 26 p.val a ∧
            PEqualNP.ReadTwo.orp D 26 (13 + l.val) b) →
        (∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
          ∀ x : Fin 26 → Bool,
            PEqualNP.MetaComplexity.circuitFun 26 D x = false →
            PEqualNP.ReadTwo.wval D x (26 + j) = false) →
        False)
    (hExactDirtyOneHot :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 D →
        D.size ≤ 63 →
        (∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 D x =
          decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) →
        (∃ (p l : Fin 13), I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 26 p.val a ∧
            PEqualNP.ReadTwo.orp D 26 (13 + l.val) b) →
        (∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
          ∃ v : Fin 26, PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (26 + j) = true) →
        False)
    (hExactDirtyNoOneHot :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 D →
        D.size ≤ 63 →
        (∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 D x =
          decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) →
        (∃ (p l : Fin 13), I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
            PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
            PEqualNP.ReadTwo.orp D 26 p.val a ∧
            PEqualNP.ReadTwo.orp D 26 (13 + l.val) b) →
        (∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
          ∀ v : Fin 26, PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (26 + j) = false) →
        (∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
          ∃ x : Fin 26 → Bool,
            PEqualNP.MetaComplexity.circuitFun 26 D x = false ∧
            PEqualNP.ReadTwo.wval D x (26 + j) = true) →
        False) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), (∀ x9 ∈ x6, x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true) → (∀ x10 ∈ x7, x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x8 = Bool.true := by
  intro I C hCmono hCsize hCedges
  let charVec : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool :=
    fun A B i => decide ((∃ p ∈ A, i = Fin.castAdd 13 p) ∨ (∃ l ∈ B, i = Fin.natAdd 13 l))
  have hcast_ne_nat (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hcast_inj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd] at hv
    exact Fin.ext hv
  have hnat_inj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    exact Fin.ext (by omega)
  have hchar_p (A B : Finset (Fin 13)) (p : Fin 13) :
      charVec A B (Fin.castAdd 13 p) = decide (p ∈ A) := by
    dsimp only [charVec]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro (⟨p', hp', h⟩ | ⟨l', _, h⟩)
      · rw [hcast_inj h]; exact hp'
      · exact False.elim (hcast_ne_nat p l' h)
    · intro hp
      exact Or.inl ⟨p, hp, rfl⟩
  have hchar_l (A B : Finset (Fin 13)) (l : Fin 13) :
      charVec A B (Fin.natAdd 13 l) = decide (l ∈ B) := by
    dsimp only [charVec]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro (⟨p', _, h⟩ | ⟨l', hl', h⟩)
      · exact False.elim (hcast_ne_nat p' l h.symm)
      · rw [hnat_inj h]; exact hl'
    · intro hl
      exact Or.inr ⟨l, hl, rfl⟩
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
  have hrun_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
        (∀ i, w1.getD i false = true → w2.getD i false = true) →
        ∀ i, (run gs w1).getD i false = true → (run gs w2).getD i false = true := by
    induction gs with
    | nil => intro w1 w2 _ hle i hi; exact hle i hi
    | cons g rest ih =>
      intro w1 w2 hlen hle
      simp only [run, List.foldl_cons] at ih ⊢
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (step w1 g) (step w2 g)
      · simp only [step, List.length_append, hlen, List.length_cons, List.length_nil]
      · intro i hi
        dsimp only [step] at hi ⊢
        by_cases hieq : i = w1.length
        · subst hieq
          rw [getD_snoc_eq w1 _ false] at hi
          rw [hlen, getD_snoc_eq w2 _ false]
          rcases hgs g List.mem_cons_self with hop | hop
          · rw [hop] at hi ⊢
            change (g.inputs.map fun j => w1.getD j false).all id = true at hi
            change (g.inputs.map fun j => w2.getD j false).all id = true
            rw [List.all_eq_true] at hi ⊢
            intro b hb
            rw [List.mem_map] at hb
            obtain ⟨j, hj, rfl⟩ := hb
            exact hle j (hi (w1.getD j false) (List.mem_map.mpr ⟨j, hj, rfl⟩))
          · rw [hop] at hi ⊢
            change (g.inputs.map fun j => w1.getD j false).any id = true at hi
            change (g.inputs.map fun j => w2.getD j false).any id = true
            rw [List.any_eq_true] at hi ⊢
            obtain ⟨b, hb, hbt⟩ := hi
            rw [List.mem_map] at hb
            obtain ⟨j, hj, rfl⟩ := hb
            exact ⟨w2.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hle j hbt⟩
        · rw [getD_snoc_ne w1 _ false i hieq] at hi
          rw [getD_snoc_ne w2 _ false i (by omega)]
          exact hle i hi
  have hC_mono (x y : Fin 26 → Bool) (hxy : ∀ i : Fin 26, x i = true → y i = true) :
      circuitFun 26 C x = true → circuitFun 26 C y = true := by
    intro hx
    change (run C.gates (List.ofFn x)).getD C.output false = true at hx
    change (run C.gates (List.ofFn y)).getD C.output false = true
    apply hrun_mono C.gates (fun g hg => (hCmono g hg).1) (List.ofFn x) (List.ofFn y)
      (by simp only [List.length_ofFn]) _ C.output hx
    intro i hi
    by_cases hlt : i < 26
    · have hi' : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hlt
      have hi'' : i < (List.ofFn y).length := by simp only [List.length_ofFn]; exact hlt
      rw [List.getD_eq_getElem _ _ hi', List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem _ _ hi'', List.getElem_ofFn]
      exact hxy ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega)] at hi
      cases hi
  have finish_with (A B : Finset (Fin 13))
      (hind : ∀ p ∈ A, ∀ l ∈ B, ¬ I p l)
      (hgl : ∀ l : Fin 13, {p ∈ A | I p l}.card ≤ 2)
      (hgp : ∀ p : Fin 13, {l ∈ B | I p l}.card ≤ 2)
      (htrue : circuitFun 26 C (charVec A B) = true) :
      ∃ (A' B' : Finset (Fin 13)),
        (∀ p ∈ A', ∀ l ∈ B', ¬ I p l) ∧
        (∀ l : Fin 13, {p ∈ A' | I p l}.card ≤ 2) ∧
        (∀ p : Fin 13, {l ∈ B' | I p l}.card ≤ 2) ∧
        ∀ x : Fin 26 → Bool,
          (∀ p ∈ A', x (Fin.castAdd 13 p) = true) →
          (∀ l ∈ B', x (Fin.natAdd 13 l) = true) →
          circuitFun 26 C x = true := by
    refine ⟨A, B, hind, hgl, hgp, ?_⟩
    intro x hxA hxB
    apply hC_mono (charVec A B) x _ htrue
    intro i hi
    dsimp only [charVec] at hi
    rw [decide_eq_true_eq] at hi
    rcases hi with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
    · exact hxA p hp
    · exact hxB l hl
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
  have simplify_ao2 (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
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
              have hia : ia < m := hv (Sum.inr ia) (by simp only [List.mem_cons, true_or])
              have hib : ib < m := hv (Sum.inr ib) (by simp only [List.mem_cons, true_or, or_true])
              refine ⟨Or.inl rfl, rfl, ?_⟩
              intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact hia
              · exact hib
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
              have hia : ia < m := hv (Sum.inr ia) (by simp only [List.mem_cons, true_or])
              have hib : ib < m := hv (Sum.inr ib) (by simp only [List.mem_cons, true_or, or_true])
              refine ⟨Or.inr rfl, rfl, ?_⟩
              intro i hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact hia
              · exact hib
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
    let r := simplify g.op (26 + acc.2.length) ins
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
        cases (simplify g.op (26 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
          simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
      simp only [List.length_cons]
      omega
  let InvAO2 : List (Bool ⊕ ℕ) × List Gate → Prop := fun acc =>
    (∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    (∀ j < acc.2.length, ∀ i ∈ (acc.2.getD j ⟨GateOp.or, []⟩).inputs, i < 26 + j) ∧
    (∀ i, svalid (26 + acc.2.length) (acc.1.getD i (Sum.inl false)))
  have elim_ao2 (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (hinv : InvAO2 acc) : InvAO2 (elim gs acc) := by
    induction gs generalizing acc with
    | nil => exact hinv
    | cons g rest ih =>
      simp only [elim, List.foldl_cons] at ih ⊢
      apply ih (elimStep acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      obtain ⟨hao, hrb, hv⟩ := hinv
      have hg := hgs g List.mem_cons_self
      let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
      let r := simplify g.op (26 + acc.2.length) ins
      have hins_v : ∀ s ∈ ins, svalid (26 + acc.2.length) s := by
        intro s hs
        simp only [ins, List.mem_map] at hs
        obtain ⟨i, _, rfl⟩ := hs
        exact hv i
      have hr_ao2 := simplify_ao2 g.op (26 + acc.2.length) ins hins_v
      have hr_val : svalid (26 + acc.2.length + r.1.toList.length) r.2 := by
        let wdummy : List Bool := List.replicate (26 + acc.2.length) false
        have hwd : wdummy.length = 26 + acc.2.length := List.length_replicate
        have hs := simplify_sound g.op hg.1 wdummy ins (by simp only [ins, List.length_map]; exact hg.2)
          (by rw [hwd]; exact hins_v)
        rw [hwd] at hs
        exact hs.1
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        dsimp only [elimStep] at hg'
        rw [List.mem_append] at hg'
        rcases hg' with h1 | h2
        · exact hao g' h1
        · have h := hr_ao2 g' h2
          exact ⟨h.1, h.2.1⟩
      · intro j hj i hi
        dsimp only [elimStep] at hj hi
        by_cases hjlt : j < acc.2.length
        · rw [List.getD_append _ _ _ _ hjlt] at hi
          exact hrb j hjlt i hi
        · cases hr1 : r.1 with
          | none =>
            have hr1' : (simplify g.op (26 + acc.2.length) ins).1 = none := hr1
            rw [hr1'] at hj
            simp only [Option.toList_none, List.append_nil] at hj
            omega
          | some gnew =>
            have hr1' : (simplify g.op (26 + acc.2.length) ins).1 = some gnew := hr1
            rw [hr1'] at hj hi
            simp only [Option.toList_some, List.length_append, List.length_cons, List.length_nil] at hj
            simp only [Option.toList_some] at hi
            have hjeq : j = acc.2.length := by omega
            subst hjeq
            rw [getD_snoc_eq acc.2 gnew _] at hi
            have hgnew_mem : gnew ∈ r.1.toList := by rw [hr1]; exact List.mem_cons_self
            exact (hr_ao2 gnew hgnew_mem).2.2 i hi
      · intro i
        dsimp only [elimStep]
        change svalid (26 + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false))
        rw [List.length_append, ← Nat.add_assoc]
        by_cases hi : i = acc.1.length
        · subst hi
          rw [getD_snoc_eq acc.1 r.2 (Sum.inl false)]
          exact hr_val
        · rw [getD_snoc_ne acc.1 r.2 (Sum.inl false) i hi]
          have hvi := hv i
          cases hsi : acc.1.getD i (Sum.inl false) with
          | inl _ => trivial
          | inr idx =>
            rw [hsi] at hvi
            have : idx < 26 + acc.2.length := hvi
            change idx < 26 + acc.2.length + r.1.toList.length
            omega
  let InvEval : List Bool → List Bool → List (Bool ⊕ ℕ) × List Gate → Prop := fun w z acc =>
    w.length = 26 ∧ acc.1.length = z.length ∧
    ∀ i, svalid (26 + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
         sval (run acc.2 w) (acc.1.getD i (Sum.inl false)) = z.getD i false
  have elim_eval (gs : List Gate) (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (hinv : InvEval w z acc) : InvEval w (run gs z) (elim gs acc) := by
    induction gs generalizing z acc with
    | nil => exact hinv
    | cons g rest ih =>
      simp only [run, elim, List.foldl_cons] at ih ⊢
      apply ih (step z g) (elimStep acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      obtain ⟨hwl, hml, hmap⟩ := hinv
      have hg := hgs g List.mem_cons_self
      let w' := run acc.2 w
      have hw'len : w'.length = 26 + acc.2.length := by
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
      have heq_r : simplify g.op (26 + acc.2.length) ins = r := by rw [← hw'len]
      refine ⟨hwl, ?_, ?_⟩
      · simp only [elimStep, step, List.length_append, hml, List.length_cons, List.length_nil]
      · intro i
        dsimp only [elimStep]
        change svalid (26 + (acc.2 ++ (simplify g.op (26 + acc.2.length) ins).1.toList).length)
            ((acc.1 ++ [(simplify g.op (26 + acc.2.length) ins).2]).getD i (Sum.inl false)) ∧
          sval (run (acc.2 ++ (simplify g.op (26 + acc.2.length) ins).1.toList) w)
            ((acc.1 ++ [(simplify g.op (26 + acc.2.length) ins).2]).getD i (Sum.inl false)) =
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
  let M0 : List (Bool ⊕ ℕ) := (List.range 26).map (Sum.inr : ℕ → Bool ⊕ ℕ)
  have hM0_len : M0.length = 26 := by simp only [M0, List.length_map, List.length_range]
  have hM0_lt (j : ℕ) (hj : j < 26) : M0.getD j (Sum.inl false) = Sum.inr j := by
    dsimp only [M0]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hj),
        List.getElem_map, List.getElem_range]
  have hbase_ao2 : InvAO2 (M0, []) := by
    refine ⟨fun _ h => (by cases h), fun _ h => (by simp at h), ?_⟩
    intro i
    by_cases hi : i < 26
    · rw [hM0_lt i hi]; exact show i < 26 + 0 by omega
    · rw [List.getD_eq_default M0 (Sum.inl false) (n := i) (by omega)]; trivial
  have hbase_eval (x : Fin 26 → Bool) : InvEval (List.ofFn x) (List.ofFn x) (M0, []) := by
    refine ⟨List.length_ofFn, by rw [hM0_len, List.length_ofFn], ?_⟩
    intro i
    by_cases hi : i < 26
    · rw [hM0_lt i hi]
      exact ⟨show i < 26 + 0 by omega, rfl⟩
    · rw [List.getD_eq_default M0 (Sum.inl false) (n := i) (by omega),
          List.getD_eq_default (List.ofFn x) false (n := i) (by rw [List.length_ofFn]; omega)]
      exact ⟨trivial, rfl⟩
  let res := elim C.gates (M0, [])
  have hres_ao2 : InvAO2 res := elim_ao2 C.gates (M0, []) hCmono hbase_ao2
  have hres_eval (x : Fin 26 → Bool) : InvEval (List.ofFn x) (run C.gates (List.ofFn x)) res :=
    elim_eval C.gates (List.ofFn x) (List.ofFn x) (M0, []) hCmono (hbase_eval x)
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b with
    | false =>
      have h00 : I 0 0 := Or.inl rfl
      have htrue := hCedges 0 0 h00
      have hev := ((hres_eval (fun i => decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13)))).2.2 C.output).2
      rw [hout] at hev
      change false = circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))) at hev
      rw [htrue] at hev
      cases hev
    | true =>
      apply finish_with ∅ ∅ (fun _ h => by cases h) (fun _ => by simp) (fun _ => by simp)
      have hev := ((hres_eval (charVec ∅ ∅)).2.2 C.output).2
      rw [hout] at hev
      change true = circuitFun 26 C (charVec ∅ ∅) at hev
      exact hev.symm
  | inr out =>
    let D : Circuit := ⟨res.2, out⟩
    have hDAO2 : IsAO2 26 D := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        exact (hres_ao2.1 g hg).1
      · intro j hj i hi
        exact hres_ao2.2.1 j hj i hi
      · intro g hg
        exact (hres_ao2.1 g hg).2
    have hDsize : D.size ≤ 63 := by
      have h := elim_len C.gates (M0, [])
      change (elim C.gates (M0, [])).2.length ≤ 63
      change C.gates.length ≤ 63 at hCsize
      simp only [List.length_nil, Nat.zero_add] at h
      omega
    have hDfun (x : Fin 26 → Bool) : circuitFun 26 D x = circuitFun 26 C x := by
      have hev := ((hres_eval x).2.2 C.output).2
      rw [hout] at hev
      exact hev
    have hDedges (p l : Fin 13) (hpl : I p l) :
        circuitFun 26 D (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true := by
      rw [hDfun]; exact hCedges p l hpl
    by_cases hsmall : ∃ A B : Finset (Fin 13), A.card ≤ 2 ∧ B.card ≤ 2 ∧ (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) ∧
        circuitFun 26 D (charVec A B) = true
    · obtain ⟨A, B, hA2, hB2, hind, hDt⟩ := hsmall
      apply finish_with A B hind
      · intro l; exact le_trans (Finset.card_filter_le A _) hA2
      · intro p; exact le_trans (Finset.card_filter_le B _) hB2
      · rw [← hDfun]; exact hDt
    · have hsmall_false (A B : Finset (Fin 13)) (hA2 : A.card ≤ 2) (hB2 : B.card ≤ 2)
          (hind : ∀ p ∈ A, ∀ l ∈ B, ¬ I p l) :
          circuitFun 26 D (charVec A B) = false := by
        by_contra hne
        exact hsmall ⟨A, B, hA2, hB2, hind, Bool.eq_true_of_not_eq_false hne⟩
      by_cases hnonedge : ∃ x : Fin 26 → Bool,
          (∀ p l : Fin 13, I p l → ¬(x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) ∧
          circuitFun 26 D x = true
      · obtain ⟨x0, hx0_ind, hx0_true⟩ := hnonedge
        let Ax : Finset (Fin 13) := Finset.univ.filter (fun p : Fin 13 => x0 (Fin.castAdd 13 p) = true)
        let Bx : Finset (Fin 13) := Finset.univ.filter (fun l : Fin 13 => x0 (Fin.natAdd 13 l) = true)
        have hchar_x0 : charVec Ax Bx = x0 := by
          funext i
          by_cases hi : i.val < 13
          · have hi_eq : i = Fin.castAdd 13 ⟨i.val, hi⟩ := Fin.ext rfl
            rw [hi_eq, hchar_p]
            simp only [Ax, Finset.mem_filter, Finset.mem_univ, true_and]
            cases x0 (Fin.castAdd 13 ⟨i.val, hi⟩) <;> rfl
          · have hi26 := i.isLt
            have hi_eq : i = Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ : Fin 13) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
            rw [hi_eq, hchar_l]
            simp only [Bx, Finset.mem_filter, Finset.mem_univ, true_and]
            cases x0 (Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ : Fin 13)) <;> rfl
        have hAxBx_ind : ∀ p ∈ Ax, ∀ l ∈ Bx, ¬ I p l := by
          intro p hp l hl hpl
          exact hx0_ind p l hpl ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hl).2⟩
        have hAxBx_true : circuitFun 26 D (charVec Ax Bx) = true := by rw [hchar_x0]; exact hx0_true
        by_cases hgen : (∀ l : Fin 13, {p ∈ Ax | I p l}.card ≤ 2) ∧ (∀ p : Fin 13, {l ∈ Bx | I p l}.card ≤ 2)
        · exact finish_with Ax Bx hAxBx_ind hgen.1 hgen.2 (by rw [← hDfun]; exact hAxBx_true)
        · have remap_circuit (π : Fin 26 → Fin 26) (hπ_bij : Function.Bijective π) :
              ∃ D' : Circuit, IsAO2 26 D' ∧ D'.size ≤ 63 ∧
                ∀ x : Fin 26 → Bool, circuitFun 26 D' x = circuitFun 26 D (fun i => x (π i)) := by
            let πNat : ℕ → ℕ := fun w => if h : w < 26 then (π ⟨w, h⟩).val else w
            have hπ_lt (w : ℕ) (hw : w < 26) : πNat w < 26 := by
              dsimp only [πNat]; simp only [hw, ↓reduceDIte]; exact (π ⟨w, hw⟩).isLt
            have hπ_ge (w : ℕ) (hw : 26 ≤ w) : πNat w = w := by
              dsimp only [πNat]; simp only [show ¬ w < 26 by omega, ↓reduceDIte]
            let D' : Circuit := ⟨D.gates.map (fun g => Gate.mk g.op (g.inputs.map πNat)), πNat D.output⟩
            have hD'AO2 : IsAO2 26 D' := by
              refine ⟨?_, ?_, ?_⟩
              · intro g hg
                simp only [D', List.mem_map] at hg
                obtain ⟨g0, hg0, rfl⟩ := hg
                exact hDAO2.1 g0 hg0
              · intro j hj i hi
                have hj' : j < D.gates.length := by
                  change j < (D.gates.map _).length at hj
                  rw [List.length_map] at hj; exact hj
                have hg_eq : gateAt D' j = Gate.mk (gateAt D j).op ((gateAt D j).inputs.map πNat) := by
                  change (D.gates.map _).getD j (Gate.mk GateOp.or []) = _
                  rw [List.getD_eq_getElem _ _ hj, List.getElem_map]
                  change Gate.mk (D.gates[j]'hj').op ((D.gates[j]'hj').inputs.map πNat) =
                    Gate.mk (D.gates.getD j (Gate.mk GateOp.or [])).op ((D.gates.getD j (Gate.mk GateOp.or [])).inputs.map πNat)
                  rw [List.getD_eq_getElem D.gates (Gate.mk GateOp.or []) hj']
                rw [hg_eq] at hi
                simp only [List.mem_map] at hi
                obtain ⟨i0, hi0, rfl⟩ := hi
                have hi0_lt : i0 < 26 + j := hDAO2.2.1 j hj' i0 hi0
                by_cases h26 : i0 < 26
                · have := hπ_lt i0 h26; omega
                · rw [hπ_ge i0 (by omega)]; exact hi0_lt
              · intro g hg
                simp only [D', List.mem_map] at hg
                obtain ⟨g0, hg0, rfl⟩ := hg
                simp only [List.length_map]
                exact hDAO2.2.2 g0 hg0
            have hD'sz : D'.size ≤ 63 := by
              change (D.gates.map _).length ≤ 63
              rw [List.length_map]
              exact hDsize
            have hremap_run (gs : List Gate) (wA wB : List Bool)
                (hlen_w : wA.length = wB.length) (h26 : 26 ≤ wA.length)
                (hrel : ∀ i, wB.getD (πNat i) false = wA.getD i false) :
                ∀ i, (run (gs.map fun g => Gate.mk g.op (g.inputs.map πNat)) wB).getD (πNat i) false =
                  (run gs wA).getD i false := by
              induction gs generalizing wA wB with
              | nil => exact hrel
              | cons g rest ih =>
                simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
                have hinp : (g.inputs.map πNat).map (fun i => wB.getD i false) =
                    g.inputs.map (fun i => wA.getD i false) := by
                  rw [List.map_map]
                  apply List.map_congr_left
                  intro i _
                  exact hrel i
                let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
                have hstepB : step wB (Gate.mk g.op (g.inputs.map πNat)) = wB ++ [b] := by
                  dsimp only [step, b]; rw [hinp]
                rw [hstepB]
                apply ih (step wA g) (wB ++ [b])
                · simp only [step, List.length_append, hlen_w, List.length_cons, List.length_nil]
                · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
                · intro i
                  dsimp only [step]
                  by_cases hi : i = wA.length
                  · subst hi
                    have hfi : πNat wA.length = wB.length := by rw [hπ_ge wA.length h26, hlen_w]
                    rw [hfi, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
                  · have hfi : πNat i ≠ wB.length := by
                      intro hfeq
                      by_cases hlt : i < 26
                      · have := hπ_lt i hlt; omega
                      · have := hπ_ge i (by omega); omega
                    rw [getD_snoc_ne wB b false (πNat i) hfi, getD_snoc_ne wA b false i hi]
                    exact hrel i
            refine ⟨D', hD'AO2, hD'sz, ?_⟩
            intro x
            change (run (D.gates.map fun g => Gate.mk g.op (g.inputs.map πNat)) (List.ofFn x)).getD (πNat D.output) false =
              (run D.gates (List.ofFn fun i => x (π i))).getD D.output false
            apply hremap_run D.gates (List.ofFn fun i => x (π i)) (List.ofFn x)
              (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega)
            intro i
            by_cases hi : i < 26
            · have hpi : πNat i < 26 := hπ_lt i hi
              rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hpi), List.getElem_ofFn,
                  List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hi), List.getElem_ofFn]
              congr 1
              apply Fin.ext
              dsimp only [πNat]
              simp only [hi, ↓reduceDIte]
            · rw [hπ_ge i (by omega),
                  List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega),
                  List.getD_eq_default (List.ofFn fun j => x (π j)) false (n := i) (by simp only [List.length_ofFn]; omega)]
          have hI_shift (c p l : Fin 13) : I (p - c) (l - c) ↔ I p l := by
            dsimp only [I]
            have hsub (k : Fin 13) : (p - c = l - c + k) ↔ (p = l + k) := by
              constructor <;> intro h
              · calc p = (p - c) + c := (sub_add_cancel p c).symm
                  _ = (l - c + k) + c := by rw [h]
                  _ = l + k := by abel
              · rw [h]; abel
            constructor
            · rintro (h | h | h | h)
              · exact Or.inl (by simpa only [add_zero] using (hsub 0).mp (by simpa only [add_zero] using h))
              · exact Or.inr (Or.inl ((hsub 1).mp h))
              · exact Or.inr (Or.inr (Or.inl ((hsub 3).mp h)))
              · exact Or.inr (Or.inr (Or.inr ((hsub 9).mp h)))
            · rintro (h | h | h | h)
              · exact Or.inl (by simpa only [add_zero] using (hsub 0).mpr (by simpa only [add_zero] using h))
              · exact Or.inr (Or.inl ((hsub 1).mpr h))
              · exact Or.inr (Or.inr (Or.inl ((hsub 3).mpr h)))
              · exact Or.inr (Or.inr (Or.inr ((hsub 9).mpr h)))
          have hI_dual (c p l : Fin 13) : I (c - l) (c - p) ↔ I p l := by
            dsimp only [I]
            have hsub (k : Fin 13) : (c - l = c - p + k) ↔ (p = l + k) := by
              constructor <;> intro h
              · have h1 : (c - l) + l = (c - p + k) + l := congrArg (· + l) h
                rw [sub_add_cancel] at h1
                have h2 : c + p = ((c - p + k) + l) + p := congrArg (· + p) h1
                have h3 : ((c - p + k) + l) + p = c + (l + k) := by abel
                rw [h3] at h2
                exact add_left_cancel h2
              · rw [h]; abel
            constructor
            · rintro (h | h | h | h)
              · exact Or.inl (by simpa only [add_zero] using (hsub 0).mp (by simpa only [add_zero] using h))
              · exact Or.inr (Or.inl ((hsub 1).mp h))
              · exact Or.inr (Or.inr (Or.inl ((hsub 3).mp h)))
              · exact Or.inr (Or.inr (Or.inr ((hsub 9).mp h)))
            · rintro (h | h | h | h)
              · exact Or.inl (by simpa only [add_zero] using (hsub 0).mpr (by simpa only [add_zero] using h))
              · exact Or.inr (Or.inl ((hsub 1).mpr h))
              · exact Or.inr (Or.inr (Or.inl ((hsub 3).mpr h)))
              · exact Or.inr (Or.inr (Or.inr ((hsub 9).mpr h)))
          by_cases hline3 : ∃ l0 : Fin 13, 3 ≤ {p ∈ Ax | I p l0}.card
          · obtain ⟨l0, hl0⟩ := hline3
            let π : Fin 26 → Fin 26 := fun i =>
              if h : i.val < 13 then Fin.castAdd 13 (⟨i.val, h⟩ - l0)
              else Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ - l0)
            let πinv : Fin 26 → Fin 26 := fun i =>
              if h : i.val < 13 then Fin.castAdd 13 (⟨i.val, h⟩ + l0)
              else Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ + l0)
            have hπ_p (p : Fin 13) : π (Fin.castAdd 13 p) = Fin.castAdd 13 (p - l0) := by
              dsimp only [π]; simp only [Fin.val_castAdd, p.isLt, ↓reduceDIte]
            have hπ_l (l : Fin 13) : π (Fin.natAdd 13 l) = Fin.natAdd 13 (l - l0) := by
              dsimp only [π]
              have hge : ¬ (13 + l.val < 13) := by omega
              simp only [Fin.val_natAdd, hge, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta]
            have hπ_bij : Function.Bijective π := by
              refine Function.bijective_iff_has_inverse.mpr ⟨πinv, ?_, ?_⟩
              · intro i
                by_cases hi : i.val < 13
                · have hi_eq : i = Fin.castAdd 13 ⟨i.val, hi⟩ := Fin.ext rfl
                  rw [hi_eq, hπ_p]; dsimp only [πinv]
                  simp only [Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, sub_add_cancel]
                · have hi_eq : i = Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ : Fin 13) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
                  rw [hi_eq, hπ_l]; dsimp only [πinv]
                  have hge : ¬ (13 + (⟨i.val - 13, by have := i.isLt; omega⟩ - l0 : Fin 13).val < 13) := by omega
                  simp only [Fin.val_natAdd, hge, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta, sub_add_cancel]
              · intro i
                by_cases hi : i.val < 13
                · have hi_eq : i = Fin.castAdd 13 ⟨i.val, hi⟩ := Fin.ext rfl
                  rw [hi_eq]; dsimp only [πinv]
                  simp only [Fin.val_castAdd, hi, ↓reduceDIte]
                  rw [hπ_p, add_sub_cancel_right]
                · have hi_eq : i = Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ : Fin 13) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
                  rw [hi_eq]; dsimp only [πinv]
                  have hge : ¬ (13 + (i.val - 13) < 13) := by omega
                  simp only [Fin.val_natAdd, hge, ↓reduceDIte, Nat.add_sub_cancel_left]
                  rw [hπ_l, add_sub_cancel_right]
            obtain ⟨D', hD'AO2, hD'sz, hD'fun⟩ := remap_circuit π hπ_bij
            have hchar_pull (A B : Finset (Fin 13)) :
                (fun i => charVec A B (π i)) = charVec (A.image (· + l0)) (B.image (· + l0)) := by
              funext i
              by_cases hi : i.val < 13
              · have hi_eq : i = Fin.castAdd 13 ⟨i.val, hi⟩ := Fin.ext rfl
                rw [hi_eq, hπ_p, hchar_p, hchar_p]
                apply Bool.eq_iff_iff.mpr
                simp only [decide_eq_true_eq, Finset.mem_image]
                constructor
                · intro h; exact ⟨⟨i.val, hi⟩ - l0, h, sub_add_cancel _ _⟩
                · rintro ⟨a, ha, heq⟩; rw [← heq, add_sub_cancel_right]; exact ha
              · have hi_eq : i = Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ : Fin 13) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
                rw [hi_eq, hπ_l, hchar_l, hchar_l]
                apply Bool.eq_iff_iff.mpr
                simp only [decide_eq_true_eq, Finset.mem_image]
                constructor
                · intro h; exact ⟨⟨i.val - 13, by have := i.isLt; omega⟩ - l0, h, sub_add_cancel _ _⟩
                · rintro ⟨b, hb, heq⟩; rw [← heq, add_sub_cancel_right]; exact hb
            have hD'edges : ∀ p l : Fin 13, I p l →
                circuitFun 26 D' (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true := by
              intro p l hpl
              rw [hD'fun]
              have heq_vec : (fun i : Fin 26 => decide (π i = Fin.castAdd 13 p ∨ π i = Fin.natAdd 13 l)) =
                  (fun i : Fin 26 => decide (i = Fin.castAdd 13 (p + l0) ∨ i = Fin.natAdd 13 (l + l0))) := by
                funext i
                apply Bool.eq_iff_iff.mpr
                simp only [decide_eq_true_eq]
                constructor
                · rintro (h | h)
                  · left; apply hπ_bij.1; rw [h, hπ_p, add_sub_cancel_right]
                  · right; apply hπ_bij.1; rw [h, hπ_l, add_sub_cancel_right]
                · rintro (rfl | rfl)
                  · left; rw [hπ_p, add_sub_cancel_right]
                  · right; rw [hπ_l, add_sub_cancel_right]
              rw [heq_vec]
              apply hDedges (p + l0) (l + l0)
              have h := (hI_shift l0 (p + l0) (l + l0)).mp
              rw [add_sub_cancel_right, add_sub_cancel_right] at h
              exact h hpl
            have hD'small : ∀ A B : Finset (Fin 13), A.card ≤ 2 → B.card ≤ 2 → (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) →
                circuitFun 26 D' (charVec A B) = false := by
              intro A B hA2 hB2 hind
              rw [hD'fun, hchar_pull]
              apply hsmall_false (A.image (· + l0)) (B.image (· + l0))
                (le_trans Finset.card_image_le hA2) (le_trans Finset.card_image_le hB2)
              intro p hp l hl hpl
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
              obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
              have h := (hI_shift l0 (a + l0) (b + l0)).mpr hpl
              rw [add_sub_cancel_right, add_sub_cancel_right] at h
              exact hind a ha b hb h
            have hD'wit : ∃ A B : Finset (Fin 13), (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) ∧ 3 ≤ {p ∈ A | I p 0}.card ∧
                circuitFun 26 D' (charVec A B) = true := by
              let A' := Ax.image (· - l0)
              let B' := Bx.image (· - l0)
              refine ⟨A', B', ?_, ?_, ?_⟩
              · intro a ha b hb hab
                obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
                obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hb
                exact hAxBx_ind p hp l hl ((hI_shift l0 p l).mp hab)
              · have hsub : ({p ∈ Ax | I p l0}).image (· - l0) ⊆ {a ∈ A' | I a 0} := by
                  intro a ha
                  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
                  obtain ⟨hpAx, hpl0⟩ := Finset.mem_filter.mp hp
                  refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hpAx, ?_⟩
                  have h := (hI_shift l0 p l0).mpr hpl0
                  rwa [sub_self] at h
                have hinj : Function.Injective (fun p : Fin 13 => p - l0) := fun x y h => by
                  simpa only [sub_add_cancel] using congrArg (· + l0) h
                have hcard := Finset.card_le_card hsub
                rw [Finset.card_image_of_injective _ hinj] at hcard
                omega
              · rw [hD'fun, hchar_pull]
                have hAeq : A'.image (· + l0) = Ax := by
                  ext p; simp only [A', Finset.mem_image]
                  constructor
                  · rintro ⟨a, ⟨p0, hp0, rfl⟩, rfl⟩; rwa [sub_add_cancel]
                  · intro hp; exact ⟨p - l0, ⟨p, hp, rfl⟩, sub_add_cancel p l0⟩
                have hBeq : B'.image (· + l0) = Bx := by
                  ext l; simp only [B', Finset.mem_image]
                  constructor
                  · rintro ⟨b, ⟨l0', hl0', rfl⟩, rfl⟩; rwa [sub_add_cancel]
                  · intro hl; exact ⟨l - l0, ⟨l, hl, rfl⟩, sub_add_cancel l l0⟩
                rw [hAeq, hBeq]
                exact hAxBx_true
            obtain ⟨A1, B1, h1ind, h1gl, h1gp, h1true⟩ := hNonGenericLine0 D' hD'AO2 hD'sz hD'edges hD'small hD'wit
            apply finish_with (A1.image (· + l0)) (B1.image (· + l0))
            · intro p hp l hl hpl
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
              obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
              have h := (hI_shift l0 (a + l0) (b + l0)).mpr hpl
              rw [add_sub_cancel_right, add_sub_cancel_right] at h
              exact h1ind a ha b hb h
            · intro l
              have hsub : {p ∈ A1.image (· + l0) | I p l} ⊆ ({a ∈ A1 | I a (l - l0)}).image (· + l0) := by
                intro p hp
                obtain ⟨hpI, hpl⟩ := Finset.mem_filter.mp hp
                obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpI
                refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, rfl⟩
                have h := (hI_shift l0 (a + l0) l).mpr hpl
                rwa [add_sub_cancel_right] at h
              exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (h1gl (l - l0)))
            · intro p
              have hsub : {l ∈ B1.image (· + l0) | I p l} ⊆ ({b ∈ B1 | I (p - l0) b}).image (· + l0) := by
                intro l hl
                obtain ⟨hlI, hpl⟩ := Finset.mem_filter.mp hl
                obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hlI
                refine Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, ?_⟩, rfl⟩
                have h := (hI_shift l0 p (b + l0)).mpr hpl
                rwa [add_sub_cancel_right] at h
              exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (h1gp (p - l0)))
            · rw [← hDfun, ← hchar_pull, ← hD'fun]
              exact h1true
          · have hpoint3 : ∃ p0 : Fin 13, 3 ≤ {l ∈ Bx | I p0 l}.card := by
              by_contra hno
              apply hgen
              refine ⟨?_, ?_⟩
              · intro l; by_contra hgt; exact hline3 ⟨l, by omega⟩
              · intro p; by_contra hgt; exact hno ⟨p, by omega⟩
            obtain ⟨p0, hp0⟩ := hpoint3
            let π : Fin 26 → Fin 26 := fun i =>
              if h : i.val < 13 then Fin.natAdd 13 (p0 - ⟨i.val, h⟩)
              else Fin.castAdd 13 (p0 - ⟨i.val - 13, by have := i.isLt; omega⟩)
            have hπ_p (p : Fin 13) : π (Fin.castAdd 13 p) = Fin.natAdd 13 (p0 - p) := by
              dsimp only [π]; simp only [Fin.val_castAdd, p.isLt, ↓reduceDIte]
            have hπ_l (l : Fin 13) : π (Fin.natAdd 13 l) = Fin.castAdd 13 (p0 - l) := by
              dsimp only [π]
              have hge : ¬ (13 + l.val < 13) := by omega
              simp only [Fin.val_natAdd, hge, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta]
            have hπ_inv (i : Fin 26) : π (π i) = i := by
              by_cases hi : i.val < 13
              · have hi_eq : i = Fin.castAdd 13 ⟨i.val, hi⟩ := Fin.ext rfl
                rw [hi_eq, hπ_p, hπ_l, sub_sub_cancel]
              · have hi_eq : i = Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ : Fin 13) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
                rw [hi_eq, hπ_l, hπ_p, sub_sub_cancel]
            have hπ_bij : Function.Bijective π :=
              Function.bijective_iff_has_inverse.mpr ⟨π, hπ_inv, hπ_inv⟩
            obtain ⟨D', hD'AO2, hD'sz, hD'fun⟩ := remap_circuit π hπ_bij
            have hchar_pull (A B : Finset (Fin 13)) :
                (fun i => charVec A B (π i)) = charVec (B.image (fun b => p0 - b)) (A.image (fun a => p0 - a)) := by
              funext i
              by_cases hi : i.val < 13
              · have hi_eq : i = Fin.castAdd 13 ⟨i.val, hi⟩ := Fin.ext rfl
                rw [hi_eq, hπ_p, hchar_l, hchar_p]
                apply Bool.eq_iff_iff.mpr
                simp only [decide_eq_true_eq, Finset.mem_image]
                constructor
                · intro h; exact ⟨p0 - ⟨i.val, hi⟩, h, sub_sub_cancel p0 _⟩
                · rintro ⟨b, hb, heq⟩; rw [← heq, sub_sub_cancel]; exact hb
              · have hi_eq : i = Fin.natAdd 13 (⟨i.val - 13, by have := i.isLt; omega⟩ : Fin 13) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
                rw [hi_eq, hπ_l, hchar_p, hchar_l]
                apply Bool.eq_iff_iff.mpr
                simp only [decide_eq_true_eq, Finset.mem_image]
                constructor
                · intro h; exact ⟨p0 - ⟨i.val - 13, by have := i.isLt; omega⟩, h, sub_sub_cancel p0 _⟩
                · rintro ⟨a, ha, heq⟩; rw [← heq, sub_sub_cancel]; exact ha
            have hD'edges : ∀ p l : Fin 13, I p l →
                circuitFun 26 D' (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true := by
              intro p l hpl
              rw [hD'fun]
              have heq_vec : (fun i : Fin 26 => decide (π i = Fin.castAdd 13 p ∨ π i = Fin.natAdd 13 l)) =
                  (fun i : Fin 26 => decide (i = Fin.castAdd 13 (p0 - l) ∨ i = Fin.natAdd 13 (p0 - p))) := by
                funext i
                apply Bool.eq_iff_iff.mpr
                simp only [decide_eq_true_eq]
                constructor
                · rintro (h | h)
                  · right; apply hπ_bij.1; rw [h, hπ_l, sub_sub_cancel]
                  · left; apply hπ_bij.1; rw [h, hπ_p, sub_sub_cancel]
                · rintro (rfl | rfl)
                  · right; rw [hπ_p, sub_sub_cancel]
                  · left; rw [hπ_l, sub_sub_cancel]
              rw [heq_vec]
              apply hDedges (p0 - l) (p0 - p)
              have h := (hI_dual p0 (p0 - l) (p0 - p)).mp
              rw [sub_sub_cancel, sub_sub_cancel] at h
              exact h hpl
            have hD'small : ∀ A B : Finset (Fin 13), A.card ≤ 2 → B.card ≤ 2 → (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) →
                circuitFun 26 D' (charVec A B) = false := by
              intro A B hA2 hB2 hind
              rw [hD'fun, hchar_pull]
              apply hsmall_false (B.image (fun b => p0 - b)) (A.image (fun a => p0 - a))
                (le_trans Finset.card_image_le hB2) (le_trans Finset.card_image_le hA2)
              intro p hp l hl hpl
              obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
              have h := (hI_dual p0 (p0 - b) (p0 - a)).mpr hpl
              rw [sub_sub_cancel, sub_sub_cancel] at h
              exact hind a ha b hb h
            have hD'wit : ∃ A B : Finset (Fin 13), (∀ p ∈ A, ∀ l ∈ B, ¬ I p l) ∧ 3 ≤ {p ∈ A | I p 0}.card ∧
                circuitFun 26 D' (charVec A B) = true := by
              let A' := Bx.image (fun l => p0 - l)
              let B' := Ax.image (fun p => p0 - p)
              refine ⟨A', B', ?_, ?_, ?_⟩
              · intro a ha b hb hab
                obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
                obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
                exact hAxBx_ind p hp l hl ((hI_dual p0 p l).mp hab)
              · have hsub : ({l ∈ Bx | I p0 l}).image (fun l => p0 - l) ⊆ {a ∈ A' | I a 0} := by
                  intro a ha
                  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
                  obtain ⟨hlBx, hp0l⟩ := Finset.mem_filter.mp hl
                  refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hlBx, ?_⟩
                  have h := (hI_dual p0 p0 l).mpr hp0l
                  rwa [sub_self] at h
                have hinj : Function.Injective (fun l : Fin 13 => p0 - l) := fun x y h => by
                  simpa only [sub_sub_cancel] using congrArg (fun z => p0 - z) h
                have hcard := Finset.card_le_card hsub
                rw [Finset.card_image_of_injective _ hinj] at hcard
                omega
              · rw [hD'fun, hchar_pull]
                have hAeq : B'.image (fun b => p0 - b) = Ax := by
                  ext p; simp only [B', Finset.mem_image]
                  constructor
                  · rintro ⟨b, ⟨p1, hp1, rfl⟩, rfl⟩; rwa [sub_sub_cancel]
                  · intro hp; exact ⟨p0 - p, ⟨p, hp, rfl⟩, sub_sub_cancel p0 p⟩
                have hBeq : A'.image (fun a => p0 - a) = Bx := by
                  ext l; simp only [A', Finset.mem_image]
                  constructor
                  · rintro ⟨a, ⟨l1, hl1, rfl⟩, rfl⟩; rwa [sub_sub_cancel]
                  · intro hl; exact ⟨p0 - l, ⟨l, hl, rfl⟩, sub_sub_cancel p0 l⟩
                rw [hAeq, hBeq]
                exact hAxBx_true
            obtain ⟨A1, B1, h1ind, h1gl, h1gp, h1true⟩ := hNonGenericLine0 D' hD'AO2 hD'sz hD'edges hD'small hD'wit
            apply finish_with (B1.image (fun b => p0 - b)) (A1.image (fun a => p0 - a))
            · intro p hp l hl hpl
              obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
              have h := (hI_dual p0 (p0 - b) (p0 - a)).mpr hpl
              rw [sub_sub_cancel, sub_sub_cancel] at h
              exact h1ind a ha b hb h
            · intro l
              have hsub : {p ∈ B1.image (fun b => p0 - b) | I p l} ⊆ ({b ∈ B1 | I (p0 - l) b}).image (fun b => p0 - b) := by
                intro p hp
                obtain ⟨hpI, hpl⟩ := Finset.mem_filter.mp hp
                obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hpI
                refine Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, ?_⟩, rfl⟩
                have h := (hI_dual p0 (p0 - b) l).mpr hpl
                rwa [sub_sub_cancel] at h
              exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (h1gp (p0 - l)))
            · intro p
              have hsub : {l ∈ A1.image (fun a => p0 - a) | I p l} ⊆ ({a ∈ A1 | I a (p0 - p)}).image (fun a => p0 - a) := by
                intro l hl
                obtain ⟨hlI, hpl⟩ := Finset.mem_filter.mp hl
                obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hlI
                refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, rfl⟩
                have h := (hI_dual p0 p (p0 - a)).mpr hpl
                rwa [sub_sub_cancel] at h
              exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (h1gl (p0 - p)))
            · rw [← hDfun, ← hchar_pull, ← hD'fun]
              exact h1true
      · exfalso
        have hD_exact : ∀ x : Fin 26 → Bool, circuitFun 26 D x =
            decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
          intro x
          apply Bool.eq_iff_iff.mpr
          rw [decide_eq_true_eq]
          constructor
          · intro hxt
            by_contra hno
            apply hnonedge
            refine ⟨x, ?_, hxt⟩
            intro p l hpl h
            exact hno ⟨p, l, hpl, h.1, h.2⟩
          · rintro ⟨p, l, hpl, hxp, hxl⟩
            rw [hDfun]
            apply hC_mono (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) x _ (hCedges p l hpl)
            intro i hi
            rw [decide_eq_true_eq] at hi
            rcases hi with rfl | rfl
            · exact hxp
            · exact hxl
        by_cases hall : ∀ (p l : Fin 13), I p l →
            ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
              PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
              PEqualNP.ReadTwo.orp D 26 p.val a ∧
              PEqualNP.ReadTwo.orp D 26 (13 + l.val) b
        · have hNoC4 : ∀ (p1 p2 l1 l2 : Fin 13), p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
            have hdiff : ∀ a ∈ ([0, 1, 3, 9] : List (Fin 13)), ∀ b ∈ ([0, 1, 3, 9] : List (Fin 13)),
                ∀ c ∈ ([0, 1, 3, 9] : List (Fin 13)), ∀ d ∈ ([0, 1, 3, 9] : List (Fin 13)),
                a ≠ b → a ≠ c → a + d ≠ b + c := by decide
            have hI_mem (p l : Fin 13) (h : I p l) : p - l ∈ ([0, 1, 3, 9] : List (Fin 13)) := by
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              rcases h with rfl | rfl | rfl | rfl
              · exact Or.inl (sub_self _)
              · exact Or.inr (Or.inl (add_sub_cancel_left _ _))
              · exact Or.inr (Or.inr (Or.inl (add_sub_cancel_left _ _)))
              · exact Or.inr (Or.inr (Or.inr (add_sub_cancel_left _ _)))
            intro p1 p2 l1 l2 hp hl h
            obtain ⟨h11, h12, h21, h22⟩ := h
            apply hdiff (p1 - l1) (hI_mem p1 l1 h11) (p1 - l2) (hI_mem p1 l2 h12)
              (p2 - l1) (hI_mem p2 l1 h21) (p2 - l2) (hI_mem p2 l2 h22)
            · intro heq
              have h := congrArg (fun z => p1 - z) heq
              simp only [sub_sub_cancel] at h
              exact hl h
            · intro heq; exact hp (by simpa only [sub_add_cancel] using congrArg (· + l1) heq)
            · abel
          have hidx : ∀ i j : Fin 4, ([0, 1, 3, 9] : List (Fin 13)).getD i.val 0 =
              ([0, 1, 3, 9] : List (Fin 13)).getD j.val 0 → i = j := by decide
          classical
          let E : Finset (Fin 13 × Fin 13) := PEqualNP.ReadTwo.incid I
          have hmem_E (p l : Fin 13) : (p, l) ∈ E ↔ I p l := by
            change (p, l) ∈ @Finset.filter (Fin 13 × Fin 13) (fun e => I e.1 e.2) (Classical.decPred _) Finset.univ ↔ I p l
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hEempty : E ≠ ∅ := by
            intro h
            have h00 : ((0 : Fin 13), (0 : Fin 13)) ∈ E := (hmem_E 0 0).mpr (Or.inl rfl)
            rw [h] at h00; cases h00
          have hE_card : E.card = 52 := by
            let f : Fin 13 × Fin 4 → Fin 13 × Fin 13 := fun q =>
              (q.1 + ([0, 1, 3, 9] : List (Fin 13)).getD q.2.val 0, q.1)
            have hf_inj : Function.Injective f := by
              intro a b h
              have h2 : a.1 = b.1 := congrArg Prod.snd h
              have h1 : a.1 + ([0, 1, 3, 9] : List (Fin 13)).getD a.2.val 0 =
                  b.1 + ([0, 1, 3, 9] : List (Fin 13)).getD b.2.val 0 := congrArg Prod.fst h
              rw [h2] at h1
              have hd := add_left_cancel h1
              exact Prod.ext h2 (hidx a.2 b.2 hd)
            have hE_eq : E = Finset.univ.image f := by
              ext e
              obtain ⟨p, l⟩ := e
              rw [hmem_E p l, Finset.mem_image]
              constructor
              · intro hpl
                rcases hpl with rfl | rfl | rfl | rfl
                · exact ⟨(p, 0), Finset.mem_univ _, by simp [f]⟩
                · exact ⟨(l, 1), Finset.mem_univ _, by simp [f]⟩
                · exact ⟨(l, 2), Finset.mem_univ _, by simp [f]⟩
                · exact ⟨(l, 3), Finset.mem_univ _, by simp [f]⟩
              · rintro ⟨⟨l0, k⟩, _, heq⟩
                have hl : l0 = l := congrArg Prod.snd heq
                have hp : l0 + ([0, 1, 3, 9] : List (Fin 13)).getD k.val 0 = p := congrArg Prod.fst heq
                subst hl; subst hp
                have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by have := k.isLt; omega
                rcases hk with rfl | rfl | rfl | rfl
                · exact Or.inl (by change l0 + 0 = l0; exact add_zero l0)
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr (Or.inl rfl))
                · exact Or.inr (Or.inr (Or.inr rfl))
            rw [hE_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
          have hRB : ReadsBack 26 D := hDAO2.2.1
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
          have wireVal_input (i : Fin 26) (x : Fin 26 → Bool) :
              wireVal 26 D i.val x = x i := by
            change (run D.gates (List.ofFn x)).getD i.val false = x i
            rw [run_keep D.gates (List.ofFn x) i.val (by simp [i.isLt])]
            rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
          have wireVal_gate (k : ℕ) (hk : k < D.gates.length) (x : Fin 26 → Bool) :
              wireVal 26 D (26 + k) x =
                (gateAt D k).op.eval ((gateAt D k).inputs.map fun i => wireVal 26 D i x) := by
            change (run D.gates (List.ofFn x)).getD (26 + k) false =
              (gateAt D k).op.eval ((gateAt D k).inputs.map fun i => (run D.gates (List.ofFn x)).getD i false)
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
              conv_lhs => rw [← List.take_append_drop k D.gates]
              have hfold : run (D.gates.take k ++ D.gates.drop k) (List.ofFn x) = run (D.gates.drop k) w0 := by
                dsimp only [run, w0]; exact List.foldl_append
              rw [hfold]
              exact run_keep (D.gates.drop k) w0 i (by omega)
            have hrun_split : run D.gates (List.ofFn x) = run (D.gates.drop (k + 1)) (step w0 (gateAt D k)) := by
              have h1 : run D.gates (List.ofFn x) = run (D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1)) (List.ofFn x) :=
                congrArg (fun gs => run gs (List.ofFn x)) hsplit
              rw [h1]
              dsimp only [run, w0]
              rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
            conv_lhs => rw [hrun_split]
            rw [run_keep _ _ (26 + k) (by simp only [step, List.length_append, hw0_len, List.length_cons, List.length_nil]; omega)]
            dsimp only [step]
            rw [show 26 + k = w0.length from hw0_len.symm, getD_snoc_eq w0 _ false]
            congr 1
            apply List.map_congr_left
            intro i hi
            exact (hw_lt i (hRB k hk i hi)).symm
          have wireVal_or_mem {k a : ℕ} (hk : k < D.gates.length) (hor : (gateAt D k).op = GateOp.or)
              (ha : a ∈ (gateAt D k).inputs) (x : Fin 26 → Bool)
              (hva : wireVal 26 D a x = true) :
              wireVal 26 D (26 + k) x = true := by
            rw [wireVal_gate k hk x, hor]
            change ((gateAt D k).inputs.map fun i => wireVal 26 D i x).any id = true
            rw [List.any_eq_true]
            exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩
          have wireVal_and_pair {k a b : ℕ} (hk : k < D.gates.length) (hand : (gateAt D k).op = GateOp.and)
              (hin : (gateAt D k).inputs = [a, b]) (x : Fin 26 → Bool) :
              wireVal 26 D (26 + k) x = (wireVal 26 D a x && wireVal 26 D b x) := by
            rw [wireVal_gate k hk x, hand, hin]
            change [wireVal 26 D a x, wireVal 26 D b x].all id = (wireVal 26 D a x && wireVal 26 D b x)
            simp
          have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin 26 → Bool)
              (ht : wireVal 26 D t x = true) : wireVal 26 D w x = true := by
            apply hp (fun u => wireVal 26 D u x = true) ht
            intro k hk hor a ha hva
            exact wireVal_or_mem hk hor ha x hva
          have isAO2_gate_inputs {k : ℕ} (hk : k < D.gates.length) :
              ∃ a b : ℕ, (gateAt D k).inputs = [a, b] ∧ a < 26 + k ∧ b < 26 + k := by
            have hmem : gateAt D k ∈ D.gates := by
              change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
              rw [List.getD_eq_getElem _ _ hk]
              exact List.getElem_mem hk
            have hlen := hDAO2.2.2 (gateAt D k) hmem
            cases hin : (gateAt D k).inputs with
            | nil => rw [hin] at hlen; simp at hlen
            | cons a t1 =>
              cases t1 with
              | nil => rw [hin] at hlen; simp at hlen
              | cons b t2 =>
                cases t2 with
                | nil =>
                  have ha := hDAO2.2.1 k hk a (by rw [hin]; exact List.mem_cons_self)
                  have hb := hDAO2.2.1 k hk b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
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
              rw [Finset.length_toList] at h1
              exact h1
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
              have hu : hne.1.choose ∈ reach a := hne.1.choose_spec
              have hv : hne.2.choose ∈ reach b := hne.2.choose_spec
              have hua : OrPath a (wireOf hne.1.choose) := (Finset.mem_filter.mp hu).2
              have hvb : OrPath b (wireOf hne.2.choose) := (Finset.mem_filter.mp hv).2
              have ha_mem : a ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_self
              have hb_mem : b ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
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
                  have hstep_ex : ∃ k < D.gates.length, w = 26 + k ∧ (gateAt D k).op = GateOp.or := by
                    rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
                    · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
                      · exact (hne_w h2).elim
                      · exact ⟨k, hk, hwk, hor⟩
                    · exact ⟨k, hk, hwk, hor⟩
                  obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
                  let o : Fin D.gates.length := ⟨k, hk⟩
                  have h2card : 2 ≤ (reach (26 + o.val)).card := by
                    rw [← hwk]
                    exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
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
          let pts (w : ℕ) : Finset (Fin 13) :=
            Finset.univ.filter (fun p => OrPath w p.val)
          let lns (w : ℕ) : Finset (Fin 13) :=
            Finset.univ.filter (fun l => OrPath w (13 + l.val))
          have hComp_wire (x : Fin 26 → Bool) :
              wireVal 26 D D.output x =
                decide (∃ (p l : Fin 13), (p, l) ∈ E ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
            have h := hD_exact x
            change wireVal 26 D D.output x = _ at h
            rw [h]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, hmem_E]
          have hno_pts_only (x : Fin 26 → Bool) (h0 : ∀ l : Fin 13, x (Fin.natAdd 13 l) = false) :
              wireVal 26 D D.output x = false := by
            rw [hComp_wire, decide_eq_false_iff_not]
            rintro ⟨p, l, _, _, hl⟩
            rw [h0 l] at hl; cases hl
          have hno_lns_only (x : Fin 26 → Bool) (h0 : ∀ p : Fin 13, x (Fin.castAdd 13 p) = false) :
              wireVal 26 D D.output x = false := by
            rw [hComp_wire, decide_eq_false_iff_not]
            rintro ⟨p, l, _, hp, _⟩
            rw [h0 p] at hp; cases hp
          have hedge_covered : ∀ p l : Fin 13, (p, l) ∈ E →
              ∃ j : Fin D.gates.length, (gateAt D j.val).op = GateOp.and ∧
                OrPath D.output (26 + j.val) ∧
                ∃ a b : ℕ, (gateAt D j.val).inputs = [a, b] ∧
                  ((OrPath a p.val ∧ OrPath b (13 + l.val)) ∨
                   (OrPath a (13 + l.val) ∧ OrPath b p.val)) := by
            intro p l hpl
            obtain ⟨j, a, b, handOn, htop, hpa, hlb⟩ := hall p l ((hmem_E p l).mp hpl)
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
              (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) ∧
              ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
            intro j hj
            obtain ⟨hand, htop, p0, l0, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
            have ha_get : (gateAt D j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
            have hb_get : (gateAt D j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
            have hand_sound : ∀ x : Fin 26 → Bool,
                wireVal 26 D a x = true → wireVal 26 D b x = true → wireVal 26 D D.output x = true := by
              intro x hxa hxb
              apply orPath_sound htop x
              rw [wireVal_and_pair j.isLt hand hab x, hxa, hxb]
              rfl
            have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
              rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
              let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p1 ∨ i = Fin.castAdd 13 p2)
              have h1 : wireVal 26 D p1.val x = true := by
                have := wireVal_input (Fin.castAdd 13 p1) x
                simpa [x] using this
              have h2 : wireVal 26 D p2.val x = true := by
                have := wireVal_input (Fin.castAdd 13 p2) x
                simpa [x] using this
              have hxa := orPath_sound (Finset.mem_filter.mp hp1).2 x h1
              have hxb := orPath_sound (Finset.mem_filter.mp hp2).2 x h2
              have ht := hand_sound x hxa hxb
              have hf := hno_pts_only x (fun l => by
                simp only [x, decide_eq_false_iff_not]
                rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
              rw [ht] at hf; cases hf
            have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
              rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
              let x : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l1 ∨ i = Fin.natAdd 13 l2)
              have h1 : wireVal 26 D (13 + l1.val) x = true := by
                have := wireVal_input (Fin.natAdd 13 l1) x
                simpa [x, Nat.add_comm] using this
              have h2 : wireVal 26 D (13 + l2.val) x = true := by
                have := wireVal_input (Fin.natAdd 13 l2) x
                simpa [x, Nat.add_comm] using this
              have hxa := orPath_sound (Finset.mem_filter.mp hl1).2 x h1
              have hxb := orPath_sound (Finset.mem_filter.mp hl2).2 x h2
              have ht := hand_sound x hxa hxb
              have hf := hno_lns_only x (fun p => by
                simp only [x, decide_eq_false_iff_not]
                rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
              rw [ht] at hf; cases hf
            have hbiclique : ∀ p l : Fin 13,
                ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → (p, l) ∈ E := by
              intro p l hpl
              let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
              have hxp : wireVal 26 D p.val x = true := by
                have := wireVal_input (Fin.castAdd 13 p) x
                simpa [x] using this
              have hxl : wireVal 26 D (13 + l.val) x = true := by
                have := wireVal_input (Fin.natAdd 13 l) x
                simpa [x, Nat.add_comm] using this
              have hout_t : wireVal 26 D D.output x = true := by
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
          have hE_in_Tstar : ∀ p l : Fin 13, (p, l) ∈ E →
              ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
            intro p l hpl
            obtain ⟨j, hand, htop, a, b, hab, hlr⟩ := hedge_covered p l hpl
            have hjT : j ∈ Tstar :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hand, htop, p, l, a, b, hab, hlr⟩
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
                rw [hpW] at hlem
                rw [hlem] at hla_m; cases hla_m
              have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
              have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
              exact ⟨by simpa [pSide, hpW] using hpb_m, by simpa [lSide, hlW] using hla_m⟩
          let Tpt : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
          let Tln : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
          have hTpt_Tln_disj : Disjoint Tpt Tln := by
            rw [Finset.disjoint_left]
            intro j h1 h2
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
          let A : Finset (Fin 13) := Tpt.image centerP
          let B : Finset (Fin 13) := Tln.image centerL
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
          have hAB_ge13 : 13 ≤ A.card + B.card := by
            have hE_cov_sub : E ⊆
                A.biUnion (fun p => ({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))) ∪
                B.biUnion (fun l => ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l))) := by
              intro e hpl
              obtain ⟨p, l⟩ := e
              have hIpl : I p l := (hmem_E p l).mp hpl
              rcases hcover (p, l) hpl with hpA | hlB
              · apply Finset.mem_union_left
                refine Finset.mem_biUnion.mpr ⟨p, hpA, Finset.mem_image.mpr ⟨l, ?_, rfl⟩⟩
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases hIpl with rfl | rfl | rfl | rfl
                · exact Or.inl rfl
                · exact Or.inr (Or.inl (add_sub_cancel_right l 1).symm)
                · exact Or.inr (Or.inr (Or.inl (add_sub_cancel_right l 3).symm))
                · exact Or.inr (Or.inr (Or.inr (add_sub_cancel_right l 9).symm))
              · apply Finset.mem_union_right
                refine Finset.mem_biUnion.mpr ⟨l, hlB, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact hIpl
            have hcard4p (p : Fin 13) : (({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))).card ≤ 4 := by
              refine le_trans Finset.card_image_le ?_
              exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
                (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
                  (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))))))
            have hcard4l (l : Fin 13) : (({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l))).card ≤ 4 := by
              refine le_trans Finset.card_image_le ?_
              exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
                (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
                  (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))))))
            have hbound : E.card ≤ 4 * A.card + 4 * B.card := by
              calc E.card
                  ≤ (A.biUnion (fun p => ({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))) ∪
                     B.biUnion (fun l => ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l)))).card :=
                      Finset.card_le_card hE_cov_sub
                _ ≤ (A.biUnion _).card + (B.biUnion _).card := Finset.card_union_le _ _
                _ ≤ (∑ p ∈ A, (({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))).card) +
                    (∑ l ∈ B, (({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l))).card) :=
                      Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
                _ ≤ (∑ _p ∈ A, 4) + (∑ _l ∈ B, 4) :=
                      Nat.add_le_add (Finset.sum_le_sum fun p _ => hcard4p p) (Finset.sum_le_sum fun l _ => hcard4l l)
                _ = 4 * A.card + 4 * B.card := by simp only [Finset.sum_const, smul_eq_mul]; omega
            omega
          let Otop : Finset (Fin D.gates.length) :=
            Finset.univ.filter (fun o =>
              (gateAt D o.val).op = GateOp.or ∧
              OrPath D.output (26 + o.val) ∧
              ∃ a ∈ Tstar, OrPath (26 + o.val) (26 + a.val))
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
              have hroot_ex : ∃ root ∈ Otop, D.output = 26 + root.val := by
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
                  ∃ y ∈ Otop, 26 + x.val ∈ (gateAt D y.val).inputs := by
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
                have hne_out : D.output ≠ 26 + x.val := by
                  rw [hroot_eq]; intro h; exact hxne (Fin.ext (by omega))
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
                  rw [List.mem_toFinset, ← hxy]
                  exact hpar_in x hxH
                have hinj : Function.Injective (fun x : Fin D.gates.length => 26 + x.val) := by
                  intro a b h; dsimp only at h; exact Fin.ext (by omega)
                have h1 : F.card = (F.image (fun x : Fin D.gates.length => 26 + x.val)).card :=
                  (Finset.card_image_of_injective F hinj).symm
                have h2 : (F.image (fun x : Fin D.gates.length => 26 + x.val)).card ≤ ((gateAt D y.val).inputs.toFinset).card :=
                  Finset.card_le_card hsub
                have h3 : ((gateAt D y.val).inputs.toFinset).card ≤ (gateAt D y.val).inputs.length :=
                  List.toFinset_card_le _
                have h4 : (gateAt D y.val).inputs.length = 2 := by
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
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
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
          have hObot_l_disj : Set.PairwiseDisjoint (B : Set (Fin 13)) Obot_l := by
            intro l1 _ l2 _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
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
              obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (26 + o.val)).card)
              have hop := orPath_trans hop_out (Finset.mem_filter.mp hl0).2
              let x : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l0)
              have hx_l : wireVal 26 D (13 + l0.val) x = true := by
                have := wireVal_input (Fin.natAdd 13 l0) x
                simpa [x, Nat.add_comm] using this
              have ht := orPath_sound hop x hx_l
              have hf := hno_lns_only x (fun p' => by
                simp only [x, decide_eq_false_iff_not]
                intro h; have := congrArg Fin.val h; simp at this; omega)
              rw [ht] at hf; cases hf
            · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
              have hcard := (Finset.mem_filter.mp ho).2.2.1
              obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < (pts (26 + o.val)).card)
              have hop := orPath_trans hop_out (Finset.mem_filter.mp hp0).2
              let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p0)
              have hx_p : wireVal 26 D p0.val x = true := by
                have := wireVal_input (Fin.castAdd 13 p0) x
                simpa [x] using this
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
          have h3disj : Tstar.card + Obot.card + Otop.card ≤ D.size := by
            have hdisj1 : Disjoint (Tstar ∪ Obot) Otop := by
              rw [Finset.disjoint_union_left]
              exact ⟨hOtop_disj_Tstar.symm, hObot_disj_Otop⟩
            have hcard_u : ((Tstar ∪ Obot) ∪ Otop).card = Tstar.card + Obot.card + Otop.card := by
              rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hObot_disj_Tstar.symm]
            have hle : ((Tstar ∪ Obot) ∪ Otop).card ≤ (Finset.univ : Finset (Fin D.gates.length)).card :=
              Finset.card_le_card (Finset.subset_univ _)
            simp only [Finset.card_univ, Fintype.card_fin] at hle
            change Tstar.card + Obot.card + Otop.card ≤ D.gates.length
            omega
          omega
        · have huncov : ∃ (p l : Fin 13), I p l ∧
              ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn D j a b ∧
                PEqualNP.ReadTwo.orp D 26 (26 + j) D.output ∧
                PEqualNP.ReadTwo.orp D 26 p.val a ∧
                PEqualNP.ReadTwo.orp D 26 (13 + l.val) b := by
            by_contra hno
            apply hall
            intro p l hpl
            by_contra hnot
            exact hno ⟨p, l, hpl, hnot⟩
          by_cases hclean : ∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
              ∀ x : Fin 26 → Bool,
                PEqualNP.MetaComplexity.circuitFun 26 D x = false →
                PEqualNP.ReadTwo.wval D x (26 + j) = false
          · exact hExactCleanUncovered D hDAO2 hDsize hD_exact huncov hclean
          · have hdirty : ∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
                ∃ x : Fin 26 → Bool,
                  PEqualNP.MetaComplexity.circuitFun 26 D x = false ∧
                  PEqualNP.ReadTwo.wval D x (26 + j) = true := by
              by_contra hno
              apply hclean
              intro j hj x hx0
              by_contra hne
              exact hno ⟨j, hj, x, hx0, Bool.eq_true_of_not_eq_false hne⟩
            by_cases honehot : ∃ j : ℕ, PEqualNP.ReadTwo.isAnd D j ∧
                ∃ v : Fin 26, PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (26 + j) = true
            · exact hExactDirtyOneHot D hDAO2 hDsize hD_exact huncov honehot
            · have hno1 : ∀ j : ℕ, PEqualNP.ReadTwo.isAnd D j →
                  ∀ v : Fin 26, PEqualNP.ReadTwo.wval D (fun i => decide (i = v)) (26 + j) = false := by
                intro j hj v
                by_contra hne
                exact honehot ⟨j, hj, v, Bool.eq_true_of_not_eq_false hne⟩
              exact hExactDirtyNoOneHot D hDAO2 hDsize hD_exact huncov hno1 hdirty
