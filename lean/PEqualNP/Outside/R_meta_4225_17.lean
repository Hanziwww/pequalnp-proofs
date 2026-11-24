import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4225_17
    (hFirstNot0 :
      let P9 : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = P9 →
        (∀ j : Fin C.size, let g := C.gates.get j; (∀ i ∈ g.inputs, i < 9 + j.val) ∧ g.inputs.Nodup ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∃ j : Fin C.size, (∀ k : Fin C.size, v.val ∈ (C.gates.get k).inputs ↔ k = j) ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ j : Fin C.size, ∀ a ∈ (C.gates.get j).inputs, ∀ b ∈ (C.gates.get j).inputs, a ∈ ([4, 6, 7] : List ℕ) → b ∈ ([4, 6, 7] : List ℕ) → a = b) →
        C.gates[0]? = some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [0]) →
        False)
    (hOneNotAnd :
      let P9 : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (j4 j6 j7 n0 : Fin C.size) (a : ℕ),
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = P9 →
        (∀ j : Fin C.size, let g := C.gates.get j; (∀ i ∈ g.inputs, i < 9 + j.val) ∧ g.inputs.Nodup ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        j4 < j6 → j6 < j7 →
        (∀ k : Fin C.size, 4 ∈ (C.gates.get k).inputs ↔ k = j4) → (C.gates.get j4).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, 6 ∈ (C.gates.get k).inputs ↔ k = j6) → (C.gates.get j6).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, 7 ∈ (C.gates.get k).inputs ↔ k = j7) → (C.gates.get j7).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ k = n0) →
        9 ≤ a → a < 9 + n0.val → (C.gates.get n0).inputs = [a] →
        C.gates[a - 9]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.and →
        False)
    (hOneNotOr :
      let P9 : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (j4 j6 j7 n0 : Fin C.size) (a : ℕ),
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = P9 →
        (∀ j : Fin C.size, let g := C.gates.get j; (∀ i ∈ g.inputs, i < 9 + j.val) ∧ g.inputs.Nodup ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        j4 < j6 → j6 < j7 →
        (∀ k : Fin C.size, 4 ∈ (C.gates.get k).inputs ↔ k = j4) → (C.gates.get j4).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, 6 ∈ (C.gates.get k).inputs ↔ k = j6) → (C.gates.get j6).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, 7 ∈ (C.gates.get k).inputs ↔ k = j7) → (C.gates.get j7).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ k = n0) →
        9 ≤ a → a < 9 + n0.val → (C.gates.get n0).inputs = [a] →
        C.gates[a - 9]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.or →
        False)
    (hMultiNot :
      let P9 : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (j4 j6 j7 n0 : Fin C.size) (a : ℕ),
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = P9 →
        (∀ j : Fin C.size, let g := C.gates.get j; (∀ i ∈ g.inputs, i < 9 + j.val) ∧ g.inputs.Nodup ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        j4 < j6 → j6 < j7 →
        (∀ k : Fin C.size, 4 ∈ (C.gates.get k).inputs ↔ k = j4) → (C.gates.get j4).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, 6 ∈ (C.gates.get k).inputs ↔ k = j6) → (C.gates.get j6).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ k : Fin C.size, 7 ∈ (C.gates.get k).inputs ↔ k = j7) → (C.gates.get j7).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        2 ≤ C.gates.countP (fun g => g.op.eval [false]) →
        (C.gates.get n0).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        (∀ k : Fin C.size, k < n0 → (C.gates.get k).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
        9 ≤ a → a < 9 + n0.val → (C.gates.get n0).inputs = [a] →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∃ (x8 : Fin x1.size), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  intro C hmin hsz hfun hclean huniqOr hnoPair hhasNot
  let edges : List (Fin 9 × Fin 9) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
  let P9 : (Fin 9 → Bool) → Bool := fun x => edges.any fun e => x e.1 && x e.2
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
  have run_append (gs1 gs2 : List Gate) (w : List Bool) :
      run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
    dsimp only [run]
    exact List.foldl_append
  have remap_bijection (f : ℕ → ℕ) (L0 : ℕ)
      (hf_lt : ∀ i, i < L0 → f i < L0) (hf_ge : ∀ i, L0 ≤ i → f i = i)
      (gs : List Gate) (wA wB : List Bool)
      (hlen_w : wA.length = wB.length) (hL0 : L0 ≤ wA.length)
      (hrel : ∀ i, wB.getD (f i) false = wA.getD i false) :
      ∀ i, (run (gs.map fun g => Gate.mk g.op (g.inputs.map f)) wB).getD (f i) false =
        (run gs wA).getD i false := by
    induction gs generalizing wA wB with
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
      have hstepB : step wB (Gate.mk g.op (g.inputs.map f)) = wB ++ [b] := by
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
  let permTable : List (List ℕ) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8],
     [1, 0, 5, 8, 6, 2, 4, 7, 3],
     [5, 8, 3, 2, 7, 0, 6, 4, 1],
     [2, 3, 8, 5, 7, 1, 4, 6, 0],
     [8, 5, 0, 1, 6, 3, 7, 4, 2],
     [3, 2, 1, 0, 4, 8, 7, 6, 5]]
  let permNat : ℕ → ℕ → ℕ := fun m i => (permTable.getD m []).getD i i
  let invIdx : Fin 6 → Fin 6 := fun m => if m = 3 then 4 else if m = 4 then 3 else m
  have hperm_row_len : ∀ m : Fin 6, (permTable.getD m.val []).length = 9 := by
    dsimp only [permTable]; decide
  have hperm_lt : ∀ m : Fin 6, ∀ i : Fin 9, permNat m.val i.val < 9 := by
    dsimp only [permNat, permTable]; decide
  have hperm_ge (m : Fin 6) (i : ℕ) (hi : 9 ≤ i) : permNat m.val i = i := by
    dsimp only [permNat]
    exact List.getD_eq_default (permTable.getD m.val []) i (n := i) (by rw [hperm_row_len m]; exact hi)
  have hperm_inv_fin : ∀ m : Fin 6, ∀ i : Fin 9, permNat (invIdx m).val (permNat m.val i.val) = i.val := by
    dsimp only [permNat, permTable, invIdx]; decide
  have hinv_inv : ∀ m : Fin 6, invIdx (invIdx m) = m := by
    dsimp only [invIdx]; decide
  have hperm_inv (m : Fin 6) (i : ℕ) : permNat (invIdx m).val (permNat m.val i) = i := by
    by_cases hi : i < 9
    · exact hperm_inv_fin m ⟨i, hi⟩
    · have hge : 9 ≤ i := by omega
      rw [hperm_ge m i hge, hperm_ge (invIdx m) i hge]
  have hperm_inj (m : Fin 6) : Function.Injective (permNat m.val) := fun a b hab => by
    have := congrArg (permNat (invIdx m).val) hab
    rw [hperm_inv m a, hperm_inv m b] at this
    exact this
  let permFin : Fin 6 → Fin 9 → Fin 9 := fun m i => ⟨permNat m.val i.val, hperm_lt m i⟩
  have hpermFin_inv (m : Fin 6) (i : Fin 9) : permFin (invIdx m) (permFin m i) = i :=
    Fin.ext (hperm_inv_fin m i)
  have hedges_perm_nat : ∀ m : Fin 6, ∀ e ∈ edges,
      (∃ e' ∈ edges, e'.1.val = permNat m.val e.1.val ∧ e'.2.val = permNat m.val e.2.val) ∨
      (∃ e' ∈ edges, e'.1.val = permNat m.val e.2.val ∧ e'.2.val = permNat m.val e.1.val) := by
    dsimp only [edges, permNat, permTable]; decide
  have hP9_perm (m : Fin 6) (x : Fin 9 → Bool) : P9 (fun i => x (permFin m i)) = P9 x := by
    have hdir : ∀ (m' : Fin 6) (y : Fin 9 → Bool), P9 (fun i => y (permFin m' i)) = true → P9 y = true := by
      intro m' y hy
      dsimp only [P9] at hy ⊢
      rw [List.any_eq_true] at hy ⊢
      obtain ⟨e, he, hbe⟩ := hy
      rcases hedges_perm_nat m' e he with ⟨e', he', h1, h2⟩ | ⟨e', he', h1, h2⟩
      · have he1 : e'.1 = permFin m' e.1 := Fin.ext h1
        have he2 : e'.2 = permFin m' e.2 := Fin.ext h2
        exact ⟨e', he', by rw [he1, he2]; exact hbe⟩
      · have he1 : e'.1 = permFin m' e.2 := Fin.ext h1
        have he2 : e'.2 = permFin m' e.1 := Fin.ext h2
        exact ⟨e', he', by rw [he1, he2, Bool.and_comm]; exact hbe⟩
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hdir m x
    · intro hx
      have hcomp : (fun i : Fin 9 => x (permFin m (permFin (invIdx m) i))) = x := by
        funext i
        have h := hpermFin_inv (invIdx m) i
        rw [hinv_inv m] at h
        rw [h]
      have h2 := hdir (invIdx m) (fun i => x (permFin m i))
      rw [hcomp] at h2
      exact h2 hx
  let permC (m : Fin 6) (D : Circuit) : Circuit :=
    ⟨D.gates.map (fun g => Gate.mk g.op (g.inputs.map (permNat m.val))), permNat m.val D.output⟩
  have hpermC_eval (m : Fin 6) (D : Circuit) (x : Fin 9 → Bool) :
      (permC m D).eval (List.ofFn x) = D.eval (List.ofFn fun i : Fin 9 => x (permFin m i)) := by
    let y : Fin 9 → Bool := fun i => x (permFin m i)
    have hrel0 : ∀ i, (List.ofFn x).getD (permNat m.val i) false = (List.ofFn y).getD i false := by
      intro i
      by_cases hi : i < 9
      · have hpi := hperm_lt m ⟨i, hi⟩
        have hlenx : permNat m.val i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hpi
        have hleny : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact hi
        rw [List.getD_eq_getElem _ _ hlenx, List.getElem_ofFn, List.getD_eq_getElem _ _ hleny, List.getElem_ofFn]
      · have hge : 9 ≤ i := by omega
        rw [hperm_ge m i hge,
            List.getD_eq_default (List.ofFn x) false (n := i) (by rw [List.length_ofFn]; exact hge),
            List.getD_eq_default (List.ofFn y) false (n := i) (by rw [List.length_ofFn]; exact hge)]
    exact remap_bijection (permNat m.val) 9 (fun i hi => hperm_lt m ⟨i, hi⟩) (hperm_ge m)
      D.gates (List.ofFn y) (List.ofFn x) (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega) hrel0 D.output
  have hpermC_fan (m : Fin 6) (D : Circuit) (hf : FanInTwo D) : FanInTwo (permC m D) := by
    intro g hg
    simp only [permC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have h := hf g0 hg0
    exact ⟨h.1, by simp only [List.length_map]; exact h.2⟩
  have hpermC_len (m : Fin 6) (D : Circuit) : (permC m D).gates.length = D.gates.length :=
    List.length_map _
  have hpermC_sz_eq (m : Fin 6) (D : Circuit) : (permC m D).size = D.size := hpermC_len m D
  have hpermC_fun (m : Fin 6) : circuitFun 9 (permC m C) = P9 := by
    funext x
    change (permC m C).eval (List.ofFn x) = P9 x
    rw [hpermC_eval m C x]
    have h := congrFun hfun (fun i => x (permFin m i))
    exact h.trans (hP9_perm m x)
  have hpermC_min (m : Fin 6) : IsMinimalCircuit 9 (permC m C) := by
    refine ⟨hpermC_fan m C hmin.1, ?_⟩
    intro D hDfan hDfun
    have hD'_fun : circuitFun 9 (permC (invIdx m) D) = circuitFun 9 C := by
      funext x
      change (permC (invIdx m) D).eval (List.ofFn x) = C.eval (List.ofFn x)
      rw [hpermC_eval (invIdx m) D x]
      have h1 : D.eval (List.ofFn fun i => x (permFin (invIdx m) i)) =
          P9 (fun i => x (permFin (invIdx m) i)) := by
        have := congrFun (hDfun.trans (hpermC_fun m)) (fun i => x (permFin (invIdx m) i))
        exact this
      rw [h1, hP9_perm (invIdx m) x]
      exact (congrFun hfun x).symm
    have hle := hmin.2 (permC (invIdx m) D) (hpermC_fan (invIdx m) D hDfan) hD'_fun
    rw [hpermC_sz_eq (invIdx m) D] at hle
    rw [hpermC_sz_eq m C]
    exact hle
  have hpermC_get (m : Fin 6) (j : Fin (permC m C).size) :
      (permC m C).gates.get j =
        Gate.mk (C.gates.get (⟨j.val, by rw [← hpermC_sz_eq m C]; exact j.isLt⟩ : Fin C.size)).op
          ((C.gates.get (⟨j.val, by rw [← hpermC_sz_eq m C]; exact j.isLt⟩ : Fin C.size)).inputs.map (permNat m.val)) := by
    change ((C.gates.map (fun g => Gate.mk g.op (g.inputs.map (permNat m.val))))[j.val]'(by rw [List.length_map]; exact (by rw [← hpermC_len m C]; exact j.isLt))) = _
    exact List.getElem_map (f := fun g : Gate => Gate.mk g.op (g.inputs.map (permNat m.val)))
  have hpermC_clean (m : Fin 6) :
      ∀ j : Fin (permC m C).size,
        let g := (permC m C).gates.get j
        (∀ i ∈ g.inputs, i < 9 + j.val) ∧ g.inputs.Nodup ∧
        (g.op = GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ GateOp.not ∧ g.inputs.length = 2) := by
    intro j
    dsimp only
    rw [hpermC_get m j]
    let j0 : Fin C.size := ⟨j.val, by rw [← hpermC_sz_eq m C]; exact j.isLt⟩
    have hc := hclean j0
    refine ⟨?_, hc.2.1.map (hperm_inj m), ?_⟩
    · intro i hi
      simp only [List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hlt : i0 < 9 + j.val := hc.1 i0 hi0
      by_cases h9 : i0 < 9
      · have hpi : permNat m.val i0 < 9 := hperm_lt m ⟨i0, h9⟩
        omega
      · rw [hperm_ge m i0 (by omega)]; exact hlt
    · simp only [List.length_map]
      exact hc.2.2
  have hperm_467 : ∀ m : Fin 6, ∀ i : Fin 9, i.val ∈ ([4, 6, 7] : List ℕ) ↔ permNat m.val i.val ∈ ([4, 6, 7] : List ℕ) := by
    dsimp only [permNat, permTable]; decide
  have hperm_467_nat (m : Fin 6) (i : ℕ) : i ∈ ([4, 6, 7] : List ℕ) ↔ permNat m.val i ∈ ([4, 6, 7] : List ℕ) := by
    by_cases hi : i < 9
    · exact hperm_467 m ⟨i, hi⟩
    · rw [hperm_ge m i (by omega)]
  have hpermC_uniqOr (m : Fin 6) :
      ∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∃ j : Fin (permC m C).size,
        (∀ k : Fin (permC m C).size, v.val ∈ ((permC m C).gates.get k).inputs ↔ k = j) ∧
        ((permC m C).gates.get j).op = GateOp.or := by
    intro v hv
    let u : Fin 9 := permFin (invIdx m) v
    have hu_mem : u ∈ ([4, 6, 7] : List (Fin 9)) := by
      have hv_nat : v.val ∈ ([4, 6, 7] : List ℕ) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
        rcases hv with rfl | rfl | rfl <;> omega
      have hu_nat : u.val ∈ ([4, 6, 7] : List ℕ) := (hperm_467 (invIdx m) v).mp hv_nat
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_nat ⊢
      rcases hu_nat with h1 | h2 | h3
      · exact Or.inl (Fin.ext h1)
      · exact Or.inr (Or.inl (Fin.ext h2))
      · exact Or.inr (Or.inr (Fin.ext h3))
    obtain ⟨j0, hj0_uniq, hj0_op⟩ := huniqOr u hu_mem
    let j : Fin (permC m C).size := ⟨j0.val, by rw [hpermC_sz_eq m C]; exact j0.isLt⟩
    refine ⟨j, ?_, ?_⟩
    · intro k
      rw [hpermC_get m k]
      let k0 : Fin C.size := ⟨k.val, by rw [← hpermC_sz_eq m C]; exact k.isLt⟩
      have hmem_iff : v.val ∈ (C.gates.get k0).inputs.map (permNat m.val) ↔ u.val ∈ (C.gates.get k0).inputs := by
        rw [List.mem_map]
        constructor
        · intro h
          obtain ⟨i0, hi0, heq⟩ := h
          have hi0_eq : i0 = u.val := by
            have := congrArg (permNat (invIdx m).val) heq
            rw [hperm_inv m i0] at this
            exact this
          rw [← hi0_eq]; exact hi0
        · intro hu_in
          refine ⟨u.val, hu_in, ?_⟩
          have h := hperm_inv (invIdx m) v.val
          rw [hinv_inv m] at h
          exact h
      rw [hmem_iff, hj0_uniq k0]
      constructor
      · intro h; have hv := congrArg Fin.val h; exact Fin.ext hv
      · intro h; have hv := congrArg Fin.val h; exact Fin.ext hv
    · rw [hpermC_get m j]; exact hj0_op
  have hpermC_noPair (m : Fin 6) :
      ∀ j : Fin (permC m C).size, ∀ a ∈ ((permC m C).gates.get j).inputs, ∀ b ∈ ((permC m C).gates.get j).inputs,
        a ∈ ([4, 6, 7] : List ℕ) → b ∈ ([4, 6, 7] : List ℕ) → a = b := by
    intro j a ha b hb ha467 hb467
    rw [hpermC_get m j] at ha hb
    simp only [List.mem_map] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := ha
    obtain ⟨b0, hb0, rfl⟩ := hb
    have heq := hnoPair ⟨j.val, by rw [← hpermC_sz_eq m C]; exact j.isLt⟩ a0 ha0 b0 hb0
      ((hperm_467_nat m a0).mpr ha467) ((hperm_467_nat m b0).mpr hb467)
    rw [heq]
  have hfirstNot : ∃ n0 : Fin C.size, (C.gates.get n0).op = GateOp.not ∧
      ∀ k : Fin C.size, k.val < n0.val → (C.gates.get k).op ≠ GateOp.not := by
    have haux : ∀ (bound : ℕ), (∃ j : Fin C.size, j.val < bound ∧ (C.gates.get j).op = GateOp.not) →
        ∃ n0 : Fin C.size, (C.gates.get n0).op = GateOp.not ∧
          ∀ k : Fin C.size, k.val < n0.val → (C.gates.get k).op ≠ GateOp.not := by
      intro bound
      induction bound with
      | zero =>
        intro h; obtain ⟨j, hj, _⟩ := h; omega
      | succ b ih =>
        intro h
        by_cases hlt : ∃ j : Fin C.size, j.val < b ∧ (C.gates.get j).op = GateOp.not
        · exact ih hlt
        · obtain ⟨j, hjb, hjop⟩ := h
          have hjeq : j.val = b := by
            by_contra hne
            exact hlt ⟨j, by omega, hjop⟩
          refine ⟨j, hjop, ?_⟩
          intro k hkj hkop
          exact hlt ⟨k, by omega, hkop⟩
    obtain ⟨j, hj⟩ := hhasNot
    exact haux C.size ⟨j, j.isLt, hj⟩
  obtain ⟨n0, hn0_op, hn0_first⟩ := hfirstNot
  have hn0_len : (C.gates.get n0).inputs.length = 1 := by
    rcases (hclean n0).2.2 with h1 | h2
    · exact h1.2
    · exact absurd hn0_op h2.1
  cases hn0_ins : (C.gates.get n0).inputs with
  | nil => rw [hn0_ins] at hn0_len; cases hn0_len
  | cons a t =>
    cases t with
    | cons _ _ => rw [hn0_ins] at hn0_len; cases hn0_len
    | nil =>
      have ha_lt : a < 9 + n0.val := by
        have hrb := (hclean n0).1 a
        rw [hn0_ins] at hrb
        exact hrb (by simp only [List.mem_cons, true_or])
      by_cases ha9 : a < 9
      · have ha_not467 : a ∉ ([4, 6, 7] : List ℕ) := by
          intro hmem
          have hv : (⟨a, ha9⟩ : Fin 9) ∈ ([4, 6, 7] : List (Fin 9)) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
            rcases hmem with h1 | h2 | h3
            · exact Or.inl (Fin.ext h1)
            · exact Or.inr (Or.inl (Fin.ext h2))
            · exact Or.inr (Or.inr (Fin.ext h3))
          obtain ⟨j, hj_uniq, hj_op⟩ := huniqOr ⟨a, ha9⟩ hv
          have ha_in : a ∈ (C.gates.get n0).inputs := by rw [hn0_ins]; exact List.mem_cons_self
          have heq : n0 = j := (hj_uniq n0).mp ha_in
          rw [heq, hj_op] at hn0_op
          cases hn0_op
        have hex_m : ∃ m : Fin 6, permNat m.val a = 0 := by
          have ha_cases : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 5 ∨ a = 8 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_not467
            omega
          rcases ha_cases with rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨4, rfl⟩
          · exact ⟨5, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
        obtain ⟨m, hm0⟩ := hex_m
        let C1 := permC m C
        have hC1_min : IsMinimalCircuit 9 C1 := hpermC_min m
        have hC1_sz : C1.size ≤ 15 := by rw [hpermC_sz_eq m C]; exact hsz
        have hC1_fun : circuitFun 9 C1 = P9 := hpermC_fun m
        have hC1_clean := hpermC_clean m
        have hC1_uniqOr := hpermC_uniqOr m
        have hC1_noPair := hpermC_noPair m
        let k := n0.val
        have hk_len : k < C1.gates.length := by
          change n0.val < C1.size; rw [hpermC_sz_eq m C]; exact n0.isLt
        let n1 : Fin C1.size := ⟨k, hk_len⟩
        have hn1_eq : C1.gates.get n1 = Gate.mk GateOp.not [0] := by
          rw [hpermC_get m n1]
          have h1 : (C.gates.get n0).op = GateOp.not := hn0_op
          have h2 : (C.gates.get n0).inputs = [a] := hn0_ins
          change Gate.mk (C.gates.get n0).op ((C.gates.get n0).inputs.map (permNat m.val)) = Gate.mk GateOp.not [0]
          rw [h1, h2]
          simp only [List.map_cons, List.map_nil, hm0]
        let pre := C1.gates.take k
        let post := C1.gates.drop (k + 1)
        have hpre_len : pre.length = k := by simp only [pre, List.length_take]; omega
        have hpost_len : post.length = C1.gates.length - (k + 1) := by simp only [post, List.length_drop]
        have hC1_split : C1.gates = pre ++ (Gate.mk GateOp.not [0] :: post) := by
          have h1 : C1.gates.take k ++ C1.gates.drop k = C1.gates := List.take_append_drop k C1.gates
          have h2 : C1.gates.drop k = C1.gates[k]'hk_len :: C1.gates.drop (k + 1) := List.drop_eq_getElem_cons hk_len
          have h3 : C1.gates[k]'hk_len = Gate.mk GateOp.not [0] := hn1_eq
          rw [← h3, ← h2]
          exact h1.symm
        let slide : ℕ → ℕ := fun i =>
          if i < 9 then i else if i < 9 + k then i + 1 else if i = 9 + k then 9 else i
        let unslide : ℕ → ℕ := fun i =>
          if i < 9 then i else if i = 9 then 9 + k else if i ≤ 9 + k then i - 1 else i
        have hunslide_slide (i : ℕ) : unslide (slide i) = i := by
          dsimp only [slide, unslide]
          by_cases h1 : i < 9
          · simp only [h1, ↓reduceIte]
          · by_cases h2 : i < 9 + k
            · have ha : ¬ i + 1 < 9 := by omega
              have hb : ¬ i + 1 = 9 := by omega
              have hc : i + 1 ≤ 9 + k := by omega
              simp only [h1, h2, ha, hb, hc, ↓reduceIte]
              omega
            · by_cases h3 : i = 9 + k
              · subst h3
                have ha : ¬ (9 : ℕ) < 9 := by omega
                simp only [h1, h2, ha, ↓reduceIte]
              · have ha : ¬ i = 9 := by omega
                have hb : ¬ i ≤ 9 + k := by omega
                simp only [h1, h2, h3, ha, hb, ↓reduceIte]
        have hslide_inj : Function.Injective slide := fun u v huv => by
          have := congrArg unslide huv
          rw [hunslide_slide u, hunslide_slide v] at this
          exact this
        let C2 : Circuit :=
          ⟨Gate.mk GateOp.not [0] :: ((pre ++ post).map fun g => Gate.mk g.op (g.inputs.map slide)), slide C1.output⟩
        have hC2_sz_eq : C2.size = C1.size := by
          change ((pre ++ post).map _).length + 1 = C1.gates.length
          rw [List.length_map, List.length_append, hpre_len, hpost_len]
          omega
        have hC2_get0 : C2.gates[0]? = some (Gate.mk GateOp.not [0]) := rfl
        have hC2_get_succ (j' : ℕ) (hj' : j' + 1 < C2.gates.length) :
            C2.gates[j' + 1]'hj' =
              let idx1 := if j' < k then j' else j' + 1
              let g1 := C1.gates[idx1]'(by
                change j' + 1 < C2.size at hj'; rw [hC2_sz_eq] at hj'; change j' + 1 < C1.gates.length at hj'
                dsimp only [idx1]; split <;> omega)
              Gate.mk g1.op (g1.inputs.map slide) := by
          dsimp only [C2]
          simp only [List.getElem_cons_succ, List.getElem_map]
          by_cases hjk : j' < k
          · simp only [hjk, ↓reduceIte]
            have h1 : (pre ++ post)[j']'(by rw [List.length_append, hpre_len, hpost_len]; change j' + 1 < C2.size at hj'; rw [hC2_sz_eq] at hj'; change j' + 1 < C1.gates.length at hj'; omega) =
                pre[j']'(by rw [hpre_len]; exact hjk) := List.getElem_append_left (by rw [hpre_len]; exact hjk)
            rw [h1]
            have h2 : pre[j']'(by rw [hpre_len]; exact hjk) = C1.gates[j']'(by omega) := List.getElem_take
            rw [h2]
          · simp only [hjk, ↓reduceIte]
            have h1 : (pre ++ post)[j']'(by rw [List.length_append, hpre_len, hpost_len]; change j' + 1 < C2.size at hj'; rw [hC2_sz_eq] at hj'; change j' + 1 < C1.gates.length at hj'; omega) =
                post[j' - k]'(by rw [hpost_len]; change j' + 1 < C2.size at hj'; rw [hC2_sz_eq] at hj'; change j' + 1 < C1.gates.length at hj'; omega) := by
              rw [List.getElem_append_right (by rw [hpre_len]; omega)]
              simp only [hpre_len]
            rw [h1]
            have h2 : post[j' - k]'(by rw [hpost_len]; change j' + 1 < C2.size at hj'; rw [hC2_sz_eq] at hj'; change j' + 1 < C1.gates.length at hj'; omega) =
                C1.gates[k + 1 + (j' - k)]'(by change j' + 1 < C2.size at hj'; rw [hC2_sz_eq] at hj'; change j' + 1 < C1.gates.length at hj'; omega) := List.getElem_drop
            rw [h2]
            have hidx : k + 1 + (j' - k) = j' + 1 := by omega
            simp only [hidx]
        have hC2_eval (x : Fin 9 → Bool) : C2.eval (List.ofFn x) = C1.eval (List.ofFn x) := by
          let wBase := List.ofFn x ++ [!x 0]
          have hwBase_len : wBase.length = 10 := by
            simp only [wBase, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
          have hstep0 : step (List.ofFn x) (Gate.mk GateOp.not [0]) = wBase := rfl
          have hpre_sim : ∀ (m' : ℕ), m' ≤ k → ∀ i < 9 + m',
              (run ((C1.gates.take m').map fun g => Gate.mk g.op (g.inputs.map slide)) wBase).getD (slide i) false =
                (run (C1.gates.take m') (List.ofFn x)).getD i false := by
            intro m'
            induction m' with
            | zero =>
              intro _ i hi
              dsimp only [List.take_zero, List.map_nil, run, List.foldl_nil]
              have hsl : slide i = i := by simp only [slide, hi, ↓reduceIte]
              rw [hsl]
              exact List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hi)
            | succ m' ih =>
              intro hm' i hi
              have hm'_lt : m' < C1.gates.length := by omega
              have htake : C1.gates.take (m' + 1) = C1.gates.take m' ++ [C1.gates[m']'hm'_lt] :=
                List.take_succ_eq_append_getElem hm'_lt
              let g := C1.gates[m']'hm'_lt
              let wOld := run (C1.gates.take m') (List.ofFn x)
              let wNew := run ((C1.gates.take m').map fun g => Gate.mk g.op (g.inputs.map slide)) wBase
              have hwOld_len : wOld.length = 9 + m' := by
                dsimp only [wOld]; rw [run_len, List.length_ofFn, List.length_take]; omega
              have hwNew_len : wNew.length = 10 + m' := by
                dsimp only [wNew]; rw [run_len, hwBase_len, List.length_map, List.length_take]; omega
              have hih := ih (by omega)
              have hinp : (g.inputs.map slide).map (fun j => wNew.getD j false) =
                  g.inputs.map (fun j => wOld.getD j false) := by
                rw [List.map_map]
                apply List.map_congr_left
                intro j hj
                have hj_lt : j < 9 + m' := (hC1_clean ⟨m', hm'_lt⟩).1 j hj
                exact hih j hj_lt
              let b := g.op.eval (g.inputs.map fun j => wOld.getD j false)
              have hrunOld : run (C1.gates.take (m' + 1)) (List.ofFn x) = wOld ++ [b] := by
                rw [htake, run_append]; rfl
              have hrunNew : run ((C1.gates.take (m' + 1)).map fun g => Gate.mk g.op (g.inputs.map slide)) wBase = wNew ++ [b] := by
                rw [htake, List.map_append, run_append]
                change step wNew (Gate.mk g.op (g.inputs.map slide)) = wNew ++ [b]
                dsimp only [step, b]; rw [hinp]
              rw [hrunNew, hrunOld]
              by_cases hieq : i = 9 + m'
              · subst hieq
                have hsl : slide (9 + m') = 10 + m' := by
                  have h1 : ¬ 9 + m' < 9 := by omega
                  have h2 : 9 + m' < 9 + k := by omega
                  simp only [slide, h1, h2, ↓reduceIte]; omega
                rw [hsl, ← hwNew_len, getD_snoc_eq wNew b false, ← hwOld_len, getD_snoc_eq wOld b false]
              · have hilt : i < 9 + m' := by omega
                have hsl_ne : slide i ≠ wNew.length := by
                  dsimp only [slide]
                  split; · omega
                  split; · omega
                  omega
                rw [getD_snoc_ne wNew b false (slide i) hsl_ne, getD_snoc_ne wOld b false i (by omega)]
                exact hih i hilt
          let pre' := pre.map (fun g => Gate.mk g.op (g.inputs.map slide))
          let post' := post.map (fun g => Gate.mk g.op (g.inputs.map slide))
          let wOld_k := step (run pre (List.ofFn x)) (Gate.mk GateOp.not [0])
          let wNew_pre := run pre' wBase
          have hwOld_pre_len : (run pre (List.ofFn x)).length = 9 + k := by
            rw [run_len, List.length_ofFn, hpre_len]
          have hwOld_k_len : wOld_k.length = 10 + k := by
            simp only [wOld_k, step, List.length_append, hwOld_pre_len, List.length_cons, List.length_nil]; omega
          have hwNew_pre_len : wNew_pre.length = 10 + k := by
            dsimp only [wNew_pre, pre']; rw [run_len, hwBase_len, List.length_map, hpre_len]
          have hrel_k : ∀ i, wNew_pre.getD (slide i) false = wOld_k.getD i false := by
            intro i
            by_cases hik : i < 9 + k
            · have h1 := hpre_sim k (Nat.le_refl k) i hik
              have h2 : wOld_k.getD i false = (run pre (List.ofFn x)).getD i false :=
                getD_snoc_ne (run pre (List.ofFn x)) _ false i (by omega)
              rw [h2]; exact h1
            · by_cases hieq : i = 9 + k
              · subst hieq
                have hsl : slide (9 + k) = 9 := by
                  have h1 : ¬ 9 + k < 9 := by omega
                  simp only [slide, h1, hik, ↓reduceIte]
                rw [hsl]
                have h1 : wNew_pre.getD 9 false = !x 0 := by
                  dsimp only [wNew_pre]
                  rw [run_keep pre' wBase 9 (by omega)]
                  dsimp only [wBase]
                  simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x) (!x 0) false
                have h2 : wOld_k.getD (9 + k) false = !x 0 := by
                  dsimp only [wOld_k, step]
                  rw [← hwOld_pre_len, getD_snoc_eq (run pre (List.ofFn x)) _ false]
                  change (!((run pre (List.ofFn x)).getD 0 false)) = !x 0
                  rw [run_keep pre (List.ofFn x) 0 (by rw [List.length_ofFn]; omega),
                      List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]
                  rfl
                rw [h1, h2]
              · have hsl : slide i = i := by
                  have h1 : ¬ i < 9 := by omega
                  simp only [slide, h1, hik, hieq, ↓reduceIte]
                rw [hsl,
                    List.getD_eq_default wNew_pre false (n := i) (by omega),
                    List.getD_eq_default wOld_k false (n := i) (by omega)]
          have hpost_rel := remap_bijection slide (10 + k)
            (fun i hi => by dsimp only [slide]; split <;> (try split) <;> (try split) <;> omega)
            (fun i hi => by
              have h1 : ¬ i < 9 := by omega
              have h2 : ¬ i < 9 + k := by omega
              have h3 : ¬ i = 9 + k := by omega
              simp only [slide, h1, h2, h3, ↓reduceIte])
            post wOld_k wNew_pre (by omega) (by omega) hrel_k
          have hrun_C2 : C2.wires (List.ofFn x) = run post' wNew_pre := by
            change run C2.gates (List.ofFn x) = _
            dsimp only [C2, run]
            rw [List.foldl_cons, hstep0, List.map_append, List.foldl_append]
          have hrun_C1 : C1.wires (List.ofFn x) = run post wOld_k := by
            change run C1.gates (List.ofFn x) = _
            conv_lhs => rw [hC1_split]
            rw [run_append]; rfl
          change (C2.wires (List.ofFn x)).getD (slide C1.output) false = (C1.wires (List.ofFn x)).getD C1.output false
          rw [hrun_C2, hrun_C1]
          exact hpost_rel C1.output
        have hC2_fun : circuitFun 9 C2 = P9 := by
          funext x
          exact (hC2_eval x).trans (congrFun hC1_fun x)
        have hC2_fan : FanInTwo C2 := by
          intro g hg
          dsimp only [C2] at hg
          rw [List.mem_cons] at hg
          rcases hg with rfl | hrest
          · exact ⟨Or.inr (Or.inr rfl), by decide⟩
          · rw [List.mem_map] at hrest
            obtain ⟨g0, hg0, rfl⟩ := hrest
            have hg0_mem : g0 ∈ C1.gates := by
              rw [hC1_split]
              rw [List.mem_append] at hg0
              rcases hg0 with h1 | h2
              · exact List.mem_append_left _ h1
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
            have hf := hC1_min.1 g0 hg0_mem
            exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
        have hC2_min : IsMinimalCircuit 9 C2 := by
          refine ⟨hC2_fan, ?_⟩
          intro D hDfan hDfun
          have hle := hC1_min.2 D hDfan (hDfun.trans (hC2_fun.trans hC1_fun.symm))
          rw [hC2_sz_eq]; exact hle
        have hC2_clean : ∀ j : Fin C2.size,
            let g := C2.gates.get j
            (∀ i ∈ g.inputs, i < 9 + j.val) ∧ g.inputs.Nodup ∧
            (g.op = GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ GateOp.not ∧ g.inputs.length = 2) := by
          intro j
          dsimp only
          cases hj : j.val with
          | zero =>
            have h0 : C2.gates.get j = Gate.mk GateOp.not [0] := by
              change C2.gates[j.val]'j.isLt = _
              simp only [hj, C2, List.getElem_cons_zero]
            rw [h0]
            refine ⟨fun i hi => by simp only [List.mem_singleton] at hi; omega, by decide, Or.inl ⟨rfl, rfl⟩⟩
          | succ j' =>
            have hj_lt : j' + 1 < C2.gates.length := by rw [← hj]; exact j.isLt
            have hg_eq := hC2_get_succ j' hj_lt
            have hget : C2.gates.get j = C2.gates[j' + 1]'hj_lt := by
              change C2.gates[j.val]'j.isLt = _
              simp only [hj]
            rw [hget, hg_eq]
            dsimp only
            let idx1 := if j' < k then j' else j' + 1
            have hidx1_lt : idx1 < C1.size := by
              have : j' + 1 < C1.size := by rw [← hC2_sz_eq]; exact hj_lt
              dsimp only [idx1]; split <;> omega
            have hc1 := hC1_clean ⟨idx1, hidx1_lt⟩
            refine ⟨?_, hc1.2.1.map hslide_inj, ?_⟩
            · intro i hi
              simp only [List.mem_map] at hi
              obtain ⟨i0, hi0, rfl⟩ := hi
              have hi0_lt : i0 < 9 + idx1 := hc1.1 i0 hi0
              by_cases hjk : j' < k
              · have hidx_eq : idx1 = j' := by simp only [idx1, hjk, ↓reduceIte]
                rw [hidx_eq] at hi0_lt
                dsimp only [slide]
                split; · omega
                split; · omega
                omega
              · have hidx_eq : idx1 = j' + 1 := by simp only [idx1, hjk, ↓reduceIte]
                rw [hidx_eq] at hi0_lt
                dsimp only [slide]
                split; · omega
                split; · omega
                split; · omega
                omega
            · simp only [List.length_map]
              exact hc1.2.2
        have hslide_lt9 (i : ℕ) (hi : i < 9) : slide i = i := by simp only [slide, hi, ↓reduceIte]
        have hslide_mem_lt9 (l : List ℕ) (w : ℕ) (hw : w < 9) : w ∈ l.map slide ↔ w ∈ l := by
          rw [List.mem_map]
          constructor
          · intro h
            obtain ⟨i0, hi0, heq⟩ := h
            have hi0_eq : i0 = w := hslide_inj (heq.trans (hslide_lt9 w hw).symm)
            rw [← hi0_eq]; exact hi0
          · intro hw_in
            exact ⟨w, hw_in, hslide_lt9 w hw⟩
        have hC2_uniqOr : ∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∃ j : Fin C2.size,
            (∀ r : Fin C2.size, v.val ∈ (C2.gates.get r).inputs ↔ r = j) ∧
            (C2.gates.get j).op = GateOp.or := by
          intro v hv
          obtain ⟨j1, hj1_uniq, hj1_op⟩ := hC1_uniqOr v hv
          have hj1_ne : j1.val ≠ k := by
            intro heq
            have hj1_eq : j1 = n1 := Fin.ext heq
            rw [hj1_eq, hn1_eq] at hj1_op
            cases hj1_op
          have hv_ne0 : v.val ≠ 0 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl <;> decide
          let j2_val := if j1.val < k then j1.val + 1 else j1.val
          have hj2_lt : j2_val < C2.size := by
            rw [hC2_sz_eq]
            have hk_sz : k < C1.size := hk_len
            dsimp only [j2_val]
            split; · omega
            exact j1.isLt
          let j2 : Fin C2.size := ⟨j2_val, hj2_lt⟩
          have hC2_mem (r : Fin C2.size) : v.val ∈ (C2.gates.get r).inputs ↔ r = j2 := by
            cases hr : r.val with
            | zero =>
              have h0 : C2.gates.get r = Gate.mk GateOp.not [0] := by
                change C2.gates[r.val]'r.isLt = _
                simp only [hr, C2, List.getElem_cons_zero]
              rw [h0]
              constructor
              · intro h
                simp only [List.mem_singleton] at h
                exact absurd h hv_ne0
              · intro h
                have : 0 = j2_val := by rw [← hr]; exact congrArg Fin.val h
                dsimp only [j2_val] at this
                split at this <;> omega
            | succ r' =>
              have hr_lt : r' + 1 < C2.gates.length := by rw [← hr]; exact r.isLt
              have hget : C2.gates.get r = C2.gates[r' + 1]'hr_lt := by
                change C2.gates[r.val]'r.isLt = _
                simp only [hr]
              rw [hget, hC2_get_succ r' hr_lt]
              dsimp only
              let idx1 := if r' < k then r' else r' + 1
              have hidx1_lt : idx1 < C1.size := by
                have : r' + 1 < C1.size := by rw [← hC2_sz_eq]; exact hr_lt
                dsimp only [idx1]; split <;> omega
              rw [hslide_mem_lt9 _ v.val v.isLt]
              have hu := hj1_uniq ⟨idx1, hidx1_lt⟩
              change v.val ∈ (C1.gates[idx1]'hidx1_lt).inputs ↔ ⟨idx1, hidx1_lt⟩ = j1 at hu
              change v.val ∈ (C1.gates[idx1]'hidx1_lt).inputs ↔ r = j2
              rw [hu]
              constructor
              · intro h
                have hval : idx1 = j1.val := congrArg Fin.val h
                apply Fin.ext
                rw [hr]
                dsimp only [j2, j2_val, idx1] at hval ⊢
                split at hval
                · split <;> omega
                · split <;> omega
              · intro h
                have hval : r' + 1 = j2_val := by rw [← hr]; exact congrArg Fin.val h
                apply Fin.ext
                dsimp only [j2_val, idx1] at hval ⊢
                split at hval
                · split <;> omega
                · split <;> omega
          refine ⟨j2, hC2_mem, ?_⟩
          have hj2_pos : 0 < j2_val := by dsimp only [j2_val]; split <;> omega
          let j2' := j2_val - 1
          have hj2_eq : j2_val = j2' + 1 := by omega
          have hj2_len : j2' + 1 < C2.gates.length := by rw [← hj2_eq]; exact hj2_lt
          have hget : C2.gates.get j2 = C2.gates[j2' + 1]'hj2_len := by
            change C2.gates[j2.val]'j2.isLt = _
            dsimp only [j2]
            simp only [hj2_eq]
          rw [hget, hC2_get_succ j2' hj2_len]
          dsimp only
          have hidx_eq : (if j2' < k then j2' else j2' + 1) = j1.val := by
            dsimp only [j2', j2_val]
            split
            · split <;> omega
            · split <;> omega
          have hj1_op' : (C1.gates[j1.val]'j1.isLt).op = GateOp.or := hj1_op
          change (C1.gates[if j2' < k then j2' else j2' + 1]'(by rw [hidx_eq]; exact j1.isLt)).op = GateOp.or
          simp only [hidx_eq]
          exact hj1_op'
        have hC2_noPair : ∀ j : Fin C2.size, ∀ u ∈ (C2.gates.get j).inputs, ∀ w ∈ (C2.gates.get j).inputs,
            u ∈ ([4, 6, 7] : List ℕ) → w ∈ ([4, 6, 7] : List ℕ) → u = w := by
          intro j u hu w hw hu467 hw467
          have hu9 : u < 9 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hu467; omega
          have hw9 : w < 9 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw467; omega
          cases hj : j.val with
          | zero =>
            have h0 : C2.gates.get j = Gate.mk GateOp.not [0] := by
              change C2.gates[j.val]'j.isLt = _
              simp only [hj, C2, List.getElem_cons_zero]
            rw [h0] at hu
            simp only [List.mem_singleton] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu467
            omega
          | succ j' =>
            have hj_lt : j' + 1 < C2.gates.length := by rw [← hj]; exact j.isLt
            have hget : C2.gates.get j = C2.gates[j' + 1]'hj_lt := by
              change C2.gates[j.val]'j.isLt = _
              simp only [hj]
            rw [hget, hC2_get_succ j' hj_lt] at hu hw
            dsimp only at hu hw
            rw [hslide_mem_lt9 _ u hu9] at hu
            rw [hslide_mem_lt9 _ w hw9] at hw
            let idx1 := if j' < k then j' else j' + 1
            have hidx1_lt : idx1 < C1.size := by
              have : j' + 1 < C1.size := by rw [← hC2_sz_eq]; exact hj_lt
              dsimp only [idx1]; split <;> omega
            exact hC1_noPair ⟨idx1, hidx1_lt⟩ u hu w hw hu467 hw467
        exact hFirstNot0 C2 hC2_min (by rw [hC2_sz_eq]; exact hC1_sz) hC2_fun hC2_clean hC2_uniqOr hC2_noPair hC2_get0
      · have h9a : 9 ≤ a := by omega
        obtain ⟨j4, hj4_uniq, hj4_op⟩ := huniqOr 4 (by decide)
        obtain ⟨j6, hj6_uniq, hj6_op⟩ := huniqOr 6 (by decide)
        obtain ⟨j7, hj7_uniq, hj7_op⟩ := huniqOr 7 (by decide)
        have h46_ne : j4.val ≠ j6.val := by
          intro heq
          have hj_eq : j4 = j6 := Fin.ext heq
          have h4_in : 4 ∈ (C.gates.get j4).inputs := (hj4_uniq j4).mpr rfl
          have h6_in : 6 ∈ (C.gates.get j4).inputs := by rw [hj_eq]; exact (hj6_uniq j6).mpr rfl
          have hcontra := hnoPair j4 4 h4_in 6 h6_in (by decide) (by decide)
          omega
        have h47_ne : j4.val ≠ j7.val := by
          intro heq
          have hj_eq : j4 = j7 := Fin.ext heq
          have h4_in : 4 ∈ (C.gates.get j4).inputs := (hj4_uniq j4).mpr rfl
          have h7_in : 7 ∈ (C.gates.get j4).inputs := by rw [hj_eq]; exact (hj7_uniq j7).mpr rfl
          have hcontra := hnoPair j4 4 h4_in 7 h7_in (by decide) (by decide)
          omega
        have h67_ne : j6.val ≠ j7.val := by
          intro heq
          have hj_eq : j6 = j7 := Fin.ext heq
          have h6_in : 6 ∈ (C.gates.get j6).inputs := (hj6_uniq j6).mpr rfl
          have h7_in : 7 ∈ (C.gates.get j6).inputs := by rw [hj_eq]; exact (hj7_uniq j7).mpr rfl
          have hcontra := hnoPair j6 6 h6_in 7 h7_in (by decide) (by decide)
          omega
        have hsort_m : ∃ m : Fin 6, ∃ (r4 r6 r7 : Fin (permC m C).size),
            r4.val < r6.val ∧ r6.val < r7.val ∧
            (∀ k : Fin (permC m C).size, 4 ∈ ((permC m C).gates.get k).inputs ↔ k = r4) ∧
            ((permC m C).gates.get r4).op = GateOp.or ∧
            (∀ k : Fin (permC m C).size, 6 ∈ ((permC m C).gates.get k).inputs ↔ k = r6) ∧
            ((permC m C).gates.get r6).op = GateOp.or ∧
            (∀ k : Fin (permC m C).size, 7 ∈ ((permC m C).gates.get k).inputs ↔ k = r7) ∧
            ((permC m C).gates.get r7).op = GateOp.or := by
          have mk_reader (m : Fin 6) (u v : Fin 9) (huv : permNat m.val u.val = v.val)
              (ju : Fin C.size) (hju_uniq : ∀ k : Fin C.size, u.val ∈ (C.gates.get k).inputs ↔ k = ju)
              (hju_op : (C.gates.get ju).op = GateOp.or) :
              let ju' : Fin (permC m C).size := ⟨ju.val, by rw [hpermC_sz_eq m C]; exact ju.isLt⟩
              (∀ k : Fin (permC m C).size, v.val ∈ ((permC m C).gates.get k).inputs ↔ k = ju') ∧
              ((permC m C).gates.get ju').op = GateOp.or := by
            intro ju'
            constructor
            · intro k
              rw [hpermC_get m k]
              let k0 : Fin C.size := ⟨k.val, by rw [← hpermC_sz_eq m C]; exact k.isLt⟩
              have hm_iff : v.val ∈ (C.gates.get k0).inputs.map (permNat m.val) ↔ u.val ∈ (C.gates.get k0).inputs := by
                rw [List.mem_map]
                constructor
                · intro h; obtain ⟨i0, hi0, heq⟩ := h
                  have : i0 = u.val := hperm_inj m (heq.trans huv.symm)
                  rw [← this]; exact hi0
                · intro h; exact ⟨u.val, h, huv⟩
              rw [hm_iff, hju_uniq k0]
              constructor
              · intro h; have hv := congrArg Fin.val h; exact Fin.ext hv
              · intro h; have hv := congrArg Fin.val h; exact Fin.ext hv
            · rw [hpermC_get m ju']; exact hju_op
          by_cases h46 : j4.val < j6.val
          · by_cases h67 : j6.val < j7.val
            · have r4 := mk_reader 0 4 4 rfl j4 hj4_uniq hj4_op
              have r6 := mk_reader 0 6 6 rfl j6 hj6_uniq hj6_op
              have r7 := mk_reader 0 7 7 rfl j7 hj7_uniq hj7_op
              exact ⟨0, _, _, _, h46, h67, r4.1, r4.2, r6.1, r6.2, r7.1, r7.2⟩
            · by_cases h47 : j4.val < j7.val
              · have r4 := mk_reader 5 4 4 rfl j4 hj4_uniq hj4_op
                have r6 := mk_reader 5 7 6 rfl j7 hj7_uniq hj7_op
                have r7 := mk_reader 5 6 7 rfl j6 hj6_uniq hj6_op
                exact ⟨5, _, _, _, h47, show j7.val < j6.val by omega, r4.1, r4.2, r6.1, r6.2, r7.1, r7.2⟩
              · have r4 := mk_reader 4 7 4 rfl j7 hj7_uniq hj7_op
                have r6 := mk_reader 4 4 6 rfl j4 hj4_uniq hj4_op
                have r7 := mk_reader 4 6 7 rfl j6 hj6_uniq hj6_op
                exact ⟨4, _, _, _, show j7.val < j4.val by omega, h46, r4.1, r4.2, r6.1, r6.2, r7.1, r7.2⟩
          · by_cases h47 : j4.val < j7.val
            · have r4 := mk_reader 1 6 4 rfl j6 hj6_uniq hj6_op
              have r6 := mk_reader 1 4 6 rfl j4 hj4_uniq hj4_op
              have r7 := mk_reader 1 7 7 rfl j7 hj7_uniq hj7_op
              exact ⟨1, _, _, _, show j6.val < j4.val by omega, h47, r4.1, r4.2, r6.1, r6.2, r7.1, r7.2⟩
            · by_cases h67 : j6.val < j7.val
              · have r4 := mk_reader 3 6 4 rfl j6 hj6_uniq hj6_op
                have r6 := mk_reader 3 7 6 rfl j7 hj7_uniq hj7_op
                have r7 := mk_reader 3 4 7 rfl j4 hj4_uniq hj4_op
                exact ⟨3, _, _, _, h67, show j7.val < j4.val by omega, r4.1, r4.2, r6.1, r6.2, r7.1, r7.2⟩
              · have r4 := mk_reader 2 7 4 rfl j7 hj7_uniq hj7_op
                have r6 := mk_reader 2 6 6 rfl j6 hj6_uniq hj6_op
                have r7 := mk_reader 2 4 7 rfl j4 hj4_uniq hj4_op
                exact ⟨2, _, _, _, show j7.val < j6.val by omega, show j6.val < j4.val by omega, r4.1, r4.2, r6.1, r6.2, r7.1, r7.2⟩
        obtain ⟨m, r4, r6, r7, hr46, hr67, hr4_u, hr4_op, hr6_u, hr6_op, hr7_u, hr7_op⟩ := hsort_m
        let C1 := permC m C
        have hC1_min : IsMinimalCircuit 9 C1 := hpermC_min m
        have hC1_sz : C1.size ≤ 15 := by rw [hpermC_sz_eq m C]; exact hsz
        have hC1_fun : circuitFun 9 C1 = P9 := hpermC_fun m
        have hC1_clean := hpermC_clean m
        let n1 : Fin C1.size := ⟨n0.val, by rw [hpermC_sz_eq m C]; exact n0.isLt⟩
        have hn1_op : (C1.gates.get n1).op = GateOp.not := by
          rw [hpermC_get m n1]; exact hn0_op
        have hn1_first : ∀ k : Fin C1.size, k.val < n1.val → (C1.gates.get k).op ≠ GateOp.not := by
          intro k hkn
          rw [hpermC_get m k]
          exact hn0_first ⟨k.val, by rw [← hpermC_sz_eq m C]; exact k.isLt⟩ hkn
        have hn1_ins : (C1.gates.get n1).inputs = [a] := by
          rw [hpermC_get m n1]
          change (C.gates.get n0).inputs.map (permNat m.val) = [a]
          rw [hn0_ins]
          simp only [List.map_cons, List.map_nil, hperm_ge m a h9a]
        by_cases hmulti : 2 ≤ C1.gates.countP (fun g => g.op.eval [false])
        · exact hMultiNot C1 r4 r6 r7 n1 a hC1_min hC1_sz hC1_fun hC1_clean hr46 hr67
            hr4_u hr4_op hr6_u hr6_op hr7_u hr7_op hmulti hn1_op hn1_first h9a ha_lt hn1_ins
        · have hle1 : C1.gates.countP (fun g => g.op.eval [false]) ≤ 1 := by omega
          have eval_false_iff (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
              op.eval [false] = true ↔ op = GateOp.not := by
            rcases hop with rfl | rfl | rfl
            · change false = true ↔ GateOp.and = GateOp.not
              exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
            · change false = true ↔ GateOp.or = GateOp.not
              exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
            · change true = true ↔ GateOp.not = GateOp.not
              exact ⟨fun _ => rfl, fun _ => rfl⟩
          have countP_le_one_uniq {α : Type} (p : α → Bool) :
              ∀ (l : List α) (i0 : Fin l.length), l.countP p ≤ 1 → p (l.get i0) = true →
                ∀ k : Fin l.length, p (l.get k) = true ↔ k = i0 := by
            intro l
            induction l with
            | nil => intro i0; exact Fin.elim0 i0
            | cons hd tl ih =>
              intro i0 hle hp0 k
              rw [List.countP_cons] at hle
              cases hi0 : i0.val with
              | zero =>
                have hhd : p hd = true := by simpa only [List.get_eq_getElem, hi0, List.getElem_cons_zero] using hp0
                rw [hhd] at hle
                have hzero : tl.countP p = 0 := by simp only [↓reduceIte] at hle; omega
                cases hk : k.val with
                | zero =>
                  have heq : k = i0 := Fin.ext (hk.trans hi0.symm)
                  rw [heq]
                  exact ⟨fun _ => rfl, fun _ => hp0⟩
                | succ k' =>
                  have hk' : k' < tl.length := by have := k.isLt; simp only [List.length_cons] at this; omega
                  have hne : k ≠ i0 := fun h => by have := congrArg Fin.val h; omega
                  have hpk : p (tl[k']'hk') = false := by
                    have h0 := List.countP_eq_zero.mp hzero (tl[k']'hk') (List.getElem_mem hk')
                    cases h : p (tl[k']'hk') with
                    | false => rfl
                    | true => exact absurd h h0
                  simp only [List.get_eq_getElem, hk, List.getElem_cons_succ, hpk]
                  exact ⟨(fun h => by cases h), fun h => absurd h hne⟩
              | succ m0 =>
                have hm0 : m0 < tl.length := by have := i0.isLt; simp only [List.length_cons] at this; omega
                have hpm0 : p (tl.get ⟨m0, hm0⟩) = true := by
                  simpa only [List.get_eq_getElem, hi0, List.getElem_cons_succ] using hp0
                have hpos : 0 < tl.countP p :=
                  List.countP_pos_iff.mpr ⟨tl.get ⟨m0, hm0⟩, List.get_mem _ _, hpm0⟩
                have hhd : p hd = false := by
                  cases h : p hd with
                  | false => rfl
                  | true => rw [h] at hle; simp only [↓reduceIte] at hle; omega
                rw [hhd] at hle
                have htl_le : tl.countP p ≤ 1 := by simp only [Bool.false_eq_true, ↓reduceIte] at hle; omega
                cases hk : k.val with
                | zero =>
                  have hne : k ≠ i0 := fun h => by have := congrArg Fin.val h; omega
                  simp only [List.get_eq_getElem, hk, List.getElem_cons_zero, hhd]
                  exact ⟨(fun h => by cases h), fun h => absurd h hne⟩
                | succ k' =>
                  have hk' : k' < tl.length := by have := k.isLt; simp only [List.length_cons] at this; omega
                  have hu := ih ⟨m0, hm0⟩ htl_le hpm0 ⟨k', hk'⟩
                  simp only [List.get_eq_getElem, hk, List.getElem_cons_succ] at hu ⊢
                  rw [hu]
                  exact ⟨fun h => Fin.ext (by have hv : k' = m0 := congrArg Fin.val h; omega),
                         fun h => Fin.ext (show k' = m0 by have hv : k.val = i0.val := congrArg Fin.val h; omega)⟩
          have hn1_p : (C1.gates.get n1).op.eval [false] = true :=
            (eval_false_iff _ (hC1_min.1 (C1.gates.get n1) (List.get_mem _ _)).1).mpr hn1_op
          have huniq_n1 : ∀ k : Fin C1.size, (C1.gates.get k).op = GateOp.not ↔ k = n1 := by
            intro k
            have h1 := countP_le_one_uniq (fun g : Gate => g.op.eval [false]) C1.gates n1 hle1 hn1_p k
            have h2 := eval_false_iff (C1.gates.get k).op (hC1_min.1 (C1.gates.get k) (List.get_mem _ _)).1
            exact h2.symm.trans h1
          have ha_idx : a - 9 < C1.gates.length := by
            have hn0_len_c1 : n0.val < C1.gates.length := n1.isLt
            omega
          have ha_op_ne : (C1.gates[a - 9]'ha_idx).op ≠ GateOp.not :=
            hn1_first ⟨a - 9, ha_idx⟩ (by dsimp only [n1]; omega)
          have ha_fan := (hC1_min.1 (C1.gates[a - 9]'ha_idx) (List.getElem_mem ha_idx)).1
          rcases ha_fan with hop | hop | hop
          · have hop_map : C1.gates[a - 9]?.map (fun g => g.op) = some GateOp.and := by
              rw [List.getElem?_eq_getElem ha_idx]; exact congrArg some hop
            exact hOneNotAnd C1 r4 r6 r7 n1 a hC1_min hC1_sz hC1_fun hC1_clean hr46 hr67
              hr4_u hr4_op hr6_u hr6_op hr7_u hr7_op huniq_n1 h9a ha_lt hn1_ins hop_map
          · have hop_map : C1.gates[a - 9]?.map (fun g => g.op) = some GateOp.or := by
              rw [List.getElem?_eq_getElem ha_idx]; exact congrArg some hop
            exact hOneNotOr C1 r4 r6 r7 n1 a hC1_min hC1_sz hC1_fun hC1_clean hr46 hr67
              hr4_u hr4_op hr6_u hr6_op hr7_u hr7_op huniq_n1 h9a ha_lt hn1_ins hop_map
          · exact absurd hop ha_op_ne
