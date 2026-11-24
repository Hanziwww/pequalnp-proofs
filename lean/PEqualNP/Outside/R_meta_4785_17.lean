import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4785_17
    (hNoExtra : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      (∀ x : Fin 14 → Bool,
        D.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true) →
      26 ≤ D.size)
    (hEdge7 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 7]) = true ↔
          ∃ p l : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true) →
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
        (∀ a b, g.inputs = [a, b] → a < 14 → b < 14 → a ≠ b →
          (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a 0).testBit b = true ∨
          (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD b 0).testBit a = true)) →
      (∃ g ∈ C.gates, 14 ∈ g.inputs) →
      26 ≤ C.size)
    (hNonEdge9Or : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 9]) = true ↔
          ∃ p l : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true) →
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
        (∀ a b, g.inputs = [a, b] → a < 14 → b < 14 → a ≠ b →
          (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a 0).testBit b = true ∨
          (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD b 0).testBit a = true)) →
      (∃ g ∈ C.gates, 14 ∈ g.inputs) →
      (∀ g ∈ C.gates, 14 ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      26 ≤ C.size)
    (hNonEdge9And : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 9]) = true ↔
          ∃ p l : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD p.val 0).testBit l.val = true ∧ x p = true ∧ x l = true) →
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
        (∀ a b, g.inputs = [a, b] → a < 14 → b < 14 → a ≠ b →
          (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a 0).testBit b = true ∨
          (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD b 0).testBit a = true)) →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 14 ∈ g.inputs) →
      26 ≤ C.size) :
    have x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD x1 (0 : ℕ)).testBit x2 = Bool.true; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), x1 ↑x3 ↑x4 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)) => PEqualNP.MetaComplexity.Monotone2 x4 ∧ ∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 x5]]) = Bool.true ↔ x2 x6); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x6 ∈ x5.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.and → ((14 : ℕ) ∈ x6.inputs → ∀ x10 ∈ x6.inputs, (14 : ℕ) ≤ x10) ∧ ∀ (x9 x10 : ℕ), x6.inputs = [x9, x10] → x9 < (14 : ℕ) → x10 < (14 : ℕ) → x9 ≠ x10 → x1 x9 x10 ∨ x1 x10 x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)), x7 = (7 : Fin (14 : ℕ)) ∨ x7 = (9 : Fin (14 : ℕ)) → x4 x6 x7 → x5 x6 → (26 : ℕ) ≤ x6.size := by
  dsimp only
  intro C v hv h4 h5
  obtain ⟨hmono, hbd⟩ := h4
  let adj : ℕ → ℕ → Prop := fun a b =>
    (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a 0).testBit b = true
  let hasEdge : (Fin 14 → Bool) → Prop := fun x =>
    ∃ p l : Fin 14, adj p.val l.val ∧ x p = true ∧ x l = true
  have hadj_bip : ∀ a b : Fin 14, adj a.val b.val → a.val < 7 ∧ 7 ≤ b.val := by decide
  have hor_eval (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    change (a || (b || false)) = (a || b)
    exact congrArg (a || ·) (Bool.or_false b)
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l d (n := j) (by omega)]
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
  have hC_mono (x y : Fin 14 → Bool) (hxy : ∀ i : Fin 14, x i = true → y i = true)
      (hx : C.eval (List.ofFn x ++ [x 0 || x v]) = true) :
      C.eval (List.ofFn y ++ [y 0 || y v]) = true := by
    have hwle : wLe (List.ofFn x ++ [x 0 || x v]) (List.ofFn y ++ [y 0 || y v]) := by
      refine ⟨by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil], ?_⟩
      intro i hi
      by_cases hi14 : i < 14
      · have h1 : (List.ofFn x ++ [x 0 || x v]).getD i false = x ⟨i, hi14⟩ := by
          have hlt : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hi14
          rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        have h2 : (List.ofFn y ++ [y 0 || y v]).getD i false = y ⟨i, hi14⟩ := by
          have hlt : i < (List.ofFn y).length := by simp only [List.length_ofFn]; exact hi14
          rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rw [h1] at hi
        rw [h2]
        exact hxy ⟨i, hi14⟩ hi
      · by_cases hi_eq : i = 14
        · subst hi_eq
          have h1 : (List.ofFn x ++ [x 0 || x v]).getD 14 false = (x 0 || x v) := by
            simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x) (x 0 || x v) false
          have h2 : (List.ofFn y ++ [y 0 || y v]).getD 14 false = (y 0 || y v) := by
            simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn y) (y 0 || y v) false
          rw [h1] at hi
          rw [h2, Bool.or_eq_true]
          rcases (Bool.or_eq_true _ _).mp hi with h0 | hvx
          · exact Or.inl (hxy 0 h0)
          · exact Or.inr (hxy v hvx)
        · rw [List.getD_eq_default _ false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)] at hi
          cases hi
    exact (run_mono C.gates hmono _ _ hwle).2 C.output hx
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
  have hFull : ∀ x : Fin 14 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x v]) = true ↔ hasEdge x := by
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
      rw [hor_eval (y 0) (y v)] at hby
      exact hny (hby.mp (hC_mono x y hxy hev))
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
      rw [hor_eval (xe 0) (xe v)] at hbxe
      have hev_xe : C.eval (List.ofFn xe ++ [xe 0 || xe v]) = true := hbxe.mpr hxe_edge
      apply hC_mono xe x _ hev_xe
      intro i hi
      have hip : i = p ∨ i = l := by simpa only [xe, decide_eq_true_eq] using hi
      rcases hip with rfl | rfl
      · exact hp
      · exact hl
  by_cases hreads14 : ∃ g ∈ C.gates, 14 ∈ g.inputs
  · rcases hv with rfl | rfl
    · exact hEdge7 C hmono hFull h5 hreads14
    · by_cases hAnd : ∃ g ∈ C.gates, g.op = GateOp.and ∧ 14 ∈ g.inputs
      · exact hNonEdge9And C hmono hFull h5 hAnd
      · apply hNonEdge9Or C hmono hFull h5 hreads14
        intro g hg h14
        rcases (hmono g hg).1 with hop | hop
        · exact absurd ⟨g, hg, hop, h14⟩ hAnd
        · exact hop
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
      have hev0 : C.eval (List.ofFn x0 ++ [x0 0 || x0 v]) = true := by
        change (run C.gates (List.ofFn x0 ++ [x0 0 || x0 v])).getD C.output false = true
        rw [hout14, run_keep C.gates _ 14 (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
        have h14 : (List.ofFn x0 ++ [x0 0 || x0 v]).getD 14 false = (x0 0 || x0 v) := by
          simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x0) (x0 0 || x0 v) false
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
          (List.ofFn x).getD (drop14 i) false = (List.ofFn x ++ [x 0 || x v]).getD i false := by
        intro i hi14
        by_cases hi : i < 14
        · have hdr : drop14 i = i := by simp only [drop14, hi, ↓reduceIte]
          rw [hdr]
          exact (List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hi)).symm
        · have hdr : drop14 i = i - 1 := by simp only [drop14, hi, ↓reduceIte]
          rw [hdr,
              List.getD_eq_default (List.ofFn x) false (n := i - 1) (by simp only [List.length_ofFn]; omega),
              List.getD_eq_default (List.ofFn x ++ [x 0 || x v]) false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
      have hev := drop14_sim C.gates hno14 (List.ofFn x) (List.ofFn x ++ [x 0 || x v])
        (by simp only [List.length_ofFn]; omega)
        (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
        hbase C.output hout_ne14
      change (run D.gates (List.ofFn x)).getD (drop14 C.output) false = true ↔ hasEdge x
      rw [hev]
      exact hFull x
    have hDsz := hNoExtra D hDmono hDfull
    have hsz_eq : D.size = C.size := by
      change (C.gates.map _).length = C.gates.length
      exact List.length_map _
    omega
