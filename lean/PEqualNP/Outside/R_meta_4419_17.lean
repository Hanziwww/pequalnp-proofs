import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4419_17
    (hMonoP9 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 14 →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x) ≠
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
            (fun e => x e.1 && x e.2))
    (hMonoH : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 11 →
      ∃ x : Fin 8 → Bool,
        D.eval (List.ofFn x) ≠
          ([(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any
            (fun e => x e.1 && x e.2))
    (hPosFirst : ∀ (isAnd : Fin 14 → Bool) (in1 in2 : Fin 14 → ℕ × Bool) (out : ℕ)
      (W : (Fin 9 → Bool) → ℕ → Bool) (jp jn : Fin 14),
      jp < jn →
      (∀ j : Fin 14, (in1 j).1 < 10 + j.val ∧ (in2 j).1 < 10 + j.val ∧ (in1 j).1 ≠ 9 ∧ (in2 j).1 ≠ 9) →
      out < 24 → out ≠ 9 →
      (∀ j : Fin 14, ((in1 j).2 = true → (in1 j).1 = 0) ∧ ((in2 j).2 = true → (in2 j).1 = 0)) →
      (∀ j : Fin 14, ((in1 j) = (0, false) ∨ (in2 j) = (0, false)) ↔ j = jp) →
      (∀ j : Fin 14, ((in1 j) = (0, true) ∨ (in2 j) = (0, true)) ↔ j = jn) →
      isAnd jp = false → isAnd jn = true →
      (∀ x (i : Fin 9), W x i.val = x i) →
      (∀ x (j : Fin 14),
        have rd : ℕ × Bool → Bool := fun p => W x p.1 ^^ p.2
        W x (10 + j.val) = if isAnd j = true then rd (in1 j) && rd (in2 j) else rd (in1 j) || rd (in2 j)) →
      ∃ x : Fin 9 → Bool, W x out ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
          (fun e => x e.1 && x e.2))
    (hNegFirst : ∀ (isAnd : Fin 14 → Bool) (in1 in2 : Fin 14 → ℕ × Bool) (out : ℕ)
      (W : (Fin 9 → Bool) → ℕ → Bool) (jp jn : Fin 14),
      jn < jp →
      (∀ j : Fin 14, (in1 j).1 < 10 + j.val ∧ (in2 j).1 < 10 + j.val ∧ (in1 j).1 ≠ 9 ∧ (in2 j).1 ≠ 9) →
      out < 24 → out ≠ 9 →
      (∀ j : Fin 14, ((in1 j).2 = true → (in1 j).1 = 0) ∧ ((in2 j).2 = true → (in2 j).1 = 0)) →
      (∀ j : Fin 14, ((in1 j) = (0, false) ∨ (in2 j) = (0, false)) ↔ j = jp) →
      (∀ j : Fin 14, ((in1 j) = (0, true) ∨ (in2 j) = (0, true)) ↔ j = jn) →
      isAnd jp = false → isAnd jn = true →
      (∀ x (i : Fin 9), W x i.val = x i) →
      (∀ x (j : Fin 14),
        have rd : ℕ × Bool → Bool := fun p => W x p.1 ^^ p.2
        W x (10 + j.val) = if isAnd j = true then rd (in1 j) && rd (in2 j) else rd (in1 j) || rd (in2 j)) →
      ∃ x : Fin 9 → Bool, W x out ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
          (fun e => x e.1 && x e.2)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : ℕ) (x3 : Fin x2 → Bool) (x4 x5 : Fin x2 → ℕ × Bool) (x6 : ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (13 : ℕ) ≤ x2 →     x2 ≤ (14 : ℕ) →       (∀ (x10 : Fin x2), (x4 x10).1 < (10 : ℕ) + ↑x10 ∧ (x5 x10).1 < (10 : ℕ) + ↑x10) →         x6 < (10 : ℕ) + x2 →           (∀ (x12 : Fin x2), ((x4 x12).2 = Bool.true → (x4 x12).1 = (0 : ℕ) ∨ (x4 x12).1 = (9 : ℕ)) ∧ ((x5 x12).2 = Bool.true → (x5 x12).1 = (0 : ℕ) ∨ (x5 x12).1 = (9 : ℕ))) →             (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x7 x13 ↑x14 = x13 x14) →               (∀ (x14 : Fin (9 : ℕ) → Bool), x7 x14 (9 : ℕ) = Bool.false) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin x2),                     have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x7 x15 x17.1 ^^ x17.2;                     x7 x15 ((10 : ℕ) + ↑x16) = if x3 x16 = Bool.true then x17 (x4 x16) && x17 (x5 x16) else x17 (x4 x16) || x17 (x5 x16)) →                   ∃ (x16 : Fin (9 : ℕ) → Bool), x7 x16 x6 ≠ x1 x16 := by
  intro P9 s isAnd in1 in2 out W _ hs_le hbd hout hpol hW_in hW_9 hW_gate
  by_contra hno
  have hcomp : ∀ x : Fin 9 → Bool, W x out = P9 x := by
    intro x
    by_contra hne
    exact hno ⟨x, hne⟩
  let H : (Fin 8 → Bool) → Bool := fun y =>
    ([(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any
      (fun e => y e.1 && y e.2)
  let dB : Bool × (ℕ × Bool) × (ℕ × Bool) := (false, (0, false), (0, false))
  let in10 (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [false]
  let stepB (ws : List Bool) (g : Bool × (ℕ × Bool) × (ℕ × Bool)) : List Bool :=
    let b1 := ws.getD g.2.1.1 false ^^ g.2.1.2
    let b2 := ws.getD g.2.2.1 false ^^ g.2.2.2
    ws ++ [if g.1 = true then b1 && b2 else b1 || b2]
  let runB (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (ws : List Bool) : List Bool :=
    gs.foldl stepB ws
  let stepC (ws : List Bool) (g : Gate) : List Bool :=
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let runC (gs : List Gate) (ws : List Bool) : List Bool := gs.foldl stepC ws
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have getD_snoc_end (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have getD_snoc_ne (l : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ l.length) :
      (l ++ [b]).getD i false = l.getD i false := by
    by_cases hlt : i < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default _ _ (by omega)]
  have runB_len (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) :
      ∀ ws : List Bool, (runB gs ws).length = ws.length + gs.length := by
    induction gs with
    | nil => intro ws; simp only [runB, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro ws
      change (runB gs (stepB ws g)).length = ws.length + (g :: gs).length
      rw [ih]
      simp only [stepB, List.length_append, List.length_cons, List.length_nil]
      omega
  have runB_keep (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) :
      ∀ (ws : List Bool) (i : ℕ), i < ws.length → (runB gs ws).getD i false = ws.getD i false := by
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      change (runB gs (stepB ws g)).getD i false = ws.getD i false
      rw [ih (stepB ws g) i (by simp only [stepB, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  have runB_append (gs1 gs2 : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (ws : List Bool) :
      runB (gs1 ++ gs2) ws = runB gs2 (runB gs1 ws) := List.foldl_append
  have runC_len (gs : List Gate) : ∀ ws : List Bool, (runC gs ws).length = ws.length + gs.length := by
    induction gs with
    | nil => intro ws; simp only [runC, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro ws
      change (runC gs (stepC ws g)).length = ws.length + (g :: gs).length
      rw [ih]
      simp only [stepC, List.length_append, List.length_cons, List.length_nil]
      omega
  have runC_keep (gs : List Gate) : ∀ (ws : List Bool) (i : ℕ), i < ws.length →
      (runC gs ws).getD i false = ws.getD i false := by
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      change (runC gs (stepC ws g)).getD i false = ws.getD i false
      rw [ih (stepC ws g) i (by simp only [stepC, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  have runC_append (gs1 gs2 : List Gate) (ws : List Bool) :
      runC (gs1 ++ gs2) ws = runC gs2 (runC gs1 ws) := List.foldl_append
  have in10_len (x : Fin 9 → Bool) : (in10 x).length = 10 := by
    simp only [in10, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have in10_lt (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
      (in10 x).getD i false = x ⟨i, hi⟩ := by
    have hlt : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  have in10_9 (x : Fin 9 → Bool) : (in10 x).getD 9 false = false := by
    simp only [in10, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show (List.ofFn x).length ≤ 9 by simp),
      List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  let gsOrig : List (Bool × (ℕ × Bool) × (ℕ × Bool)) :=
    List.ofFn (fun j : Fin s => (isAnd j, in1 j, in2 j))
  have hgsOrig_len : gsOrig.length = s := List.length_ofFn
  have hgsOrig_take : ∀ j ≤ s, ∀ (x : Fin 9 → Bool) (k : ℕ), k < 10 + j →
      (runB (gsOrig.take j) (in10 x)).getD k false = W x k := by
    intro j
    induction j with
    | zero =>
      intro _ x k hk
      simp only [List.take_zero, runB, List.foldl_nil]
      by_cases hlt : k < 9
      · rw [in10_lt x k hlt, ← hW_in x ⟨k, hlt⟩]
      · have hk9 : k = 9 := by omega
        rw [hk9, in10_9, hW_9]
    | succ j ih =>
      intro hj x k hk
      have hjs : j < s := by omega
      have htake : gsOrig.take (j + 1) = gsOrig.take j ++ [(isAnd ⟨j, hjs⟩, in1 ⟨j, hjs⟩, in2 ⟨j, hjs⟩)] := by
        rw [List.take_succ_eq_append_getElem (by rw [hgsOrig_len]; exact hjs)]
        simp only [gsOrig, List.getElem_ofFn]
      rw [htake, runB_append]
      let w0 := runB (gsOrig.take j) (in10 x)
      have hw0_len : w0.length = 10 + j := by
        simp only [w0, runB_len, in10_len, List.length_take, hgsOrig_len]
        omega
      change (stepB w0 (isAnd ⟨j, hjs⟩, in1 ⟨j, hjs⟩, in2 ⟨j, hjs⟩)).getD k false = W x k
      by_cases hkj : k < 10 + j
      · have hne : k ≠ w0.length := by omega
        dsimp only [stepB]
        rw [getD_snoc_ne w0 _ k hne]
        exact ih (by omega) x k hkj
      · have hkeq : k = 10 + j := by omega
        rw [hkeq]
        dsimp only [stepB]
        conv_lhs => rw [← hw0_len, getD_snoc_end]
        have hb := hbd ⟨j, hjs⟩
        have h1 := ih (by omega) x (in1 ⟨j, hjs⟩).1 hb.1
        have h2 := ih (by omega) x (in2 ⟨j, hjs⟩).1 hb.2
        have hgw := hW_gate x ⟨j, hjs⟩
        dsimp only at hgw
        rw [h1, h2, ← hgw]
  have hgsOrig_val (x : Fin 9 → Bool) (k : ℕ) (hk : k < 10 + s) :
      (runB gsOrig (in10 x)).getD k false = W x k := by
    have ht : gsOrig.take s = gsOrig := List.take_of_length_le (by rw [hgsOrig_len])
    rw [← ht]
    exact hgsOrig_take s (Nat.le_refl s) x k hk
  have hgsOrig_pol : ∀ g ∈ gsOrig,
      (g.2.1.2 = true → g.2.1.1 = 0 ∨ g.2.1.1 = 9) ∧
      (g.2.2.2 = true → g.2.2.1 = 0 ∨ g.2.2.1 = 9) := by
    intro g hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact hpol j
  let evalSymB (sb : Bool ⊕ (ℕ × Bool)) (ws : List Bool) : Bool :=
    Sum.elim id (fun p => ws.getD p.1 false ^^ p.2) sb
  let flipSym (pol : Bool) (sb : Bool ⊕ (ℕ × Bool)) : Bool ⊕ (ℕ × Bool) :=
    Sum.elim (fun c => Sum.inl (c ^^ pol)) (fun p => Sum.inr (p.1, p.2 ^^ pol)) sb
  have heval_flip (pol : Bool) (sb : Bool ⊕ (ℕ × Bool)) (ws : List Bool) :
      evalSymB (flipSym pol sb) ws = (evalSymB sb ws ^^ pol) := by
    cases sb with
    | inl c => rfl
    | inr p =>
      simp only [flipSym, evalSymB, Sum.elim_inr]
      exact (Bool.xor_assoc _ _ _).symm
  let SymInv (n : ℕ) (sb : Bool ⊕ (ℕ × Bool)) : Prop :=
    Sum.elim (fun _ => True) (fun p => p.1 < 10 + n ∧ p.1 ≠ 9 ∧ (p.2 = true → p.1 = 0)) sb
  let CleanPropB (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) : Prop :=
    ∀ j < gs.length,
      let g := gs.getD j dB
      g.2.1.1 < 10 + j ∧ g.2.2.1 < 10 + j ∧
      g.2.1.1 ≠ 9 ∧ g.2.2.1 ≠ 9 ∧
      (g.2.1.2 = true → g.2.1.1 = 0) ∧ (g.2.2.2 = true → g.2.2.1 = 0) ∧
      g.2.1 ≠ g.2.2 ∧ ¬ (g.2.1.1 = 0 ∧ g.2.2.1 = 0)
  have cleanPropB_snoc (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool)))
      (g : Bool × (ℕ × Bool) × (ℕ × Bool)) (hcl : CleanPropB gs)
      (hg : g.2.1.1 < 10 + gs.length ∧ g.2.2.1 < 10 + gs.length ∧
        g.2.1.1 ≠ 9 ∧ g.2.2.1 ≠ 9 ∧
        (g.2.1.2 = true → g.2.1.1 = 0) ∧ (g.2.2.2 = true → g.2.2.1 = 0) ∧
        g.2.1 ≠ g.2.2 ∧ ¬ (g.2.1.1 = 0 ∧ g.2.2.1 = 0)) :
      CleanPropB (gs ++ [g]) := by
    intro j hj
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j dB = gs.getD j dB := List.getD_append _ _ _ _ hlt
      dsimp only; rw [hget]; exact hcl j hlt
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hget : (gs ++ [g]).getD gs.length dB = g := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      dsimp only; rw [hget]; exact hg
  let cleanGateB (st : List (Bool ⊕ (ℕ × Bool))) (outIdx : ℕ)
      (g : Bool × (ℕ × Bool) × (ℕ × Bool)) :
      (Bool ⊕ (ℕ × Bool)) × Option (Bool × (ℕ × Bool) × (ℕ × Bool)) :=
    let a := flipSym g.2.1.2 (st.getD g.2.1.1 (Sum.inl false))
    let b := flipSym g.2.2.2 (st.getD g.2.2.1 (Sum.inl false))
    Sum.elim
      (fun ca => Bool.casesOn g.1
        (Bool.casesOn ca (b, none) (Sum.inl true, none))
        (Bool.casesOn ca (Sum.inl false, none) (b, none)))
      (fun pa => Sum.elim
        (fun cb => Bool.casesOn g.1
          (Bool.casesOn cb (Sum.inr pa, none) (Sum.inl true, none))
          (Bool.casesOn cb (Sum.inl false, none) (Sum.inr pa, none)))
        (fun pb =>
          if pa == pb then (Sum.inr pa, none)
          else if pa.1 == 0 && pb.1 == 0 then (Sum.inl (!g.1), none)
          else (Sum.inr (outIdx, false), some (g.1, pa, pb))) b) a
  let cleanStepB (acc : List (Bool ⊕ (ℕ × Bool)) × List (Bool × (ℕ × Bool) × (ℕ × Bool)))
      (g : Bool × (ℕ × Bool) × (ℕ × Bool)) :
      List (Bool ⊕ (ℕ × Bool)) × List (Bool × (ℕ × Bool) × (ℕ × Bool)) :=
    let r := cleanGateB acc.1 (10 + acc.2.length) g
    (acc.1 ++ [r.1], Option.elim r.2 acc.2 (fun g' => acc.2 ++ [g']))
  have clean_fold : ∀ (gs_in : List (Bool × (ℕ × Bool) × (ℕ × Bool)))
      (st : List (Bool ⊕ (ℕ × Bool)))
      (gs_out gs_done : List (Bool × (ℕ × Bool) × (ℕ × Bool))),
      (∀ g ∈ gs_in, (g.2.1.2 = true → g.2.1.1 = 0 ∨ g.2.1.1 = 9) ∧
        (g.2.2.2 = true → g.2.2.1 = 0 ∨ g.2.2.1 = 9)) →
      st.length = 10 + gs_done.length →
      st.getD 0 (Sum.inl false) = Sum.inr (0, false) →
      st.getD 9 (Sum.inl false) = Sum.inl false →
      gs_out.length ≤ gs_done.length →
      CleanPropB gs_out →
      (∀ sb ∈ st, SymInv gs_out.length sb) →
      (∀ (x : Fin 9 → Bool) (i : ℕ), i < st.length →
        evalSymB (st.getD i (Sum.inl false)) (runB gs_out (in10 x)) =
          (runB gs_done (in10 x)).getD i false) →
      let res := gs_in.foldl cleanStepB (st, gs_out)
      res.1.length = 10 + (gs_done ++ gs_in).length ∧
      res.2.length ≤ (gs_done ++ gs_in).length ∧
      CleanPropB res.2 ∧
      (∀ sb ∈ res.1, SymInv res.2.length sb) ∧
      (∀ (x : Fin 9 → Bool) (i : ℕ), i < res.1.length →
        evalSymB (res.1.getD i (Sum.inl false)) (runB res.2 (in10 x)) =
          (runB (gs_done ++ gs_in) (in10 x)).getD i false) := by
    intro gs_in
    induction gs_in with
    | nil =>
      intro st gs_out gs_done _ hst _ _ hlen hcl hbd hag
      simp only [List.foldl_nil, List.append_nil]
      exact ⟨hst, hlen, hcl, hbd, hag⟩
    | cons g rest ih =>
      intro st gs_out gs_done hpol_in hst hst0 hst9 hlen hcl hbd hag
      have hgpol := hpol_in g List.mem_cons_self
      have hrest_pol : ∀ g' ∈ rest,
          (g'.2.1.2 = true → g'.2.1.1 = 0 ∨ g'.2.1.1 = 9) ∧
          (g'.2.2.2 = true → g'.2.2.1 = 0 ∨ g'.2.2.1 = 9) :=
        fun g' hm => hpol_in g' (List.mem_cons_of_mem _ hm)
      have hget_inv (i : ℕ) : SymInv gs_out.length (st.getD i (Sum.inl false)) := by
        by_cases hi : i < st.length
        · rw [List.getD_eq_getElem _ _ hi]
          exact hbd _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
          trivial
      have hflip_inv (p : ℕ × Bool) (hp : p.2 = true → p.1 = 0 ∨ p.1 = 9) :
          SymInv gs_out.length (flipSym p.2 (st.getD p.1 (Sum.inl false))) := by
        cases hpolp : p.2 with
        | false =>
          cases hs : st.getD p.1 (Sum.inl false) with
          | inl c => trivial
          | inr q =>
            have hq := hget_inv p.1
            rw [hs] at hq
            simp only [flipSym, SymInv, Sum.elim_inr, Bool.xor_false] at hq ⊢
            exact hq
        | true =>
          rcases hp hpolp with hp0 | hp9
          · rw [hp0, hst0]
            simp only [flipSym, SymInv, Sum.elim_inr]
            exact ⟨by omega, by omega, fun _ => trivial⟩
          · rw [hp9, hst9]
            trivial
      have hval (x : Fin 9 → Bool) (i : ℕ) :
          evalSymB (st.getD i (Sum.inl false)) (runB gs_out (in10 x)) =
            (runB gs_done (in10 x)).getD i false := by
        by_cases hi : i < st.length
        · exact hag x i hi
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
              List.getD_eq_default _ _ (by rw [runB_len, in10_len]; omega)]
          rfl
      let r := cleanGateB st (10 + gs_out.length) g
      let st1 := st ++ [r.1]
      let gs1 := Option.elim r.2 gs_out (fun g' => gs_out ++ [g'])
      have ha_inv : SymInv gs_out.length (flipSym g.2.1.2 (st.getD g.2.1.1 (Sum.inl false))) := hflip_inv g.2.1 hgpol.1
      have hb_inv : SymInv gs_out.length (flipSym g.2.2.2 (st.getD g.2.2.1 (Sum.inl false))) := hflip_inv g.2.2 hgpol.2
      have ha_val (x : Fin 9 → Bool) :
          evalSymB (flipSym g.2.1.2 (st.getD g.2.1.1 (Sum.inl false))) (runB gs_out (in10 x)) =
            ((runB gs_done (in10 x)).getD g.2.1.1 false ^^ g.2.1.2) := by
        rw [heval_flip, hval]
      have hb_val (x : Fin 9 → Bool) :
          evalSymB (flipSym g.2.2.2 (st.getD g.2.2.1 (Sum.inl false))) (runB gs_out (in10 x)) =
            ((runB gs_done (in10 x)).getD g.2.2.1 false ^^ g.2.2.2) := by
        rw [heval_flip, hval]
      have hstep : gs1.length ≤ gs_done.length + 1 ∧ SymInv gs1.length r.1 ∧ CleanPropB gs1 ∧
          (∀ x : Fin 9 → Bool,
            evalSymB r.1 (runB gs1 (in10 x)) =
              let b1 := (runB gs_done (in10 x)).getD g.2.1.1 false ^^ g.2.1.2
              let b2 := (runB gs_done (in10 x)).getD g.2.2.1 false ^^ g.2.2.2
              if g.1 = true then b1 && b2 else b1 || b2) := by
        cases ha : flipSym g.2.1.2 (st.getD g.2.1.1 (Sum.inl false)) with
        | inl ca =>
          cases hg1 : g.1 with
          | false =>
            cases ca with
            | false =>
              have hr : r = (flipSym g.2.2.2 (st.getD g.2.2.1 (Sum.inl false)), none) := by
                simp only [r, cleanGateB, ha, hg1, Sum.elim_inl]
              refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                by simp only [gs1, hr, Option.elim_none]; exact hb_inv,
                by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
              have hax := ha_val x; rw [ha] at hax; simp only [evalSymB, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte, ← hax, Bool.false_or]
              exact hb_val x
            | true =>
              have hr : r = (Sum.inl true, none) := by simp only [r, cleanGateB, ha, hg1, Sum.elim_inl]
              refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                by simp only [hr]; trivial,
                by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
              have hax := ha_val x; rw [ha] at hax; simp only [evalSymB, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte,
                evalSymB, Sum.elim_inl, id, ← hax, Bool.true_or]
          | true =>
            cases ca with
            | false =>
              have hr : r = (Sum.inl false, none) := by simp only [r, cleanGateB, ha, hg1, Sum.elim_inl]
              refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                by simp only [hr]; trivial,
                by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
              have hax := ha_val x; rw [ha] at hax; simp only [evalSymB, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, ↓reduceIte,
                evalSymB, Sum.elim_inl, id, ← hax, Bool.false_and]
            | true =>
              have hr : r = (flipSym g.2.2.2 (st.getD g.2.2.1 (Sum.inl false)), none) := by
                simp only [r, cleanGateB, ha, hg1, Sum.elim_inl]
              refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                by simp only [gs1, hr, Option.elim_none]; exact hb_inv,
                by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
              have hax := ha_val x; rw [ha] at hax; simp only [evalSymB, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, ↓reduceIte, ← hax, Bool.true_and]
              exact hb_val x
        | inr pa =>
          rw [ha] at ha_inv
          cases hb : flipSym g.2.2.2 (st.getD g.2.2.1 (Sum.inl false)) with
          | inl cb =>
            cases hg1 : g.1 with
            | false =>
              cases cb with
              | false =>
                have hr : r = (Sum.inr pa, none) := by
                  simp only [r, cleanGateB, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                  by simp only [gs1, hr, Option.elim_none]; exact ha_inv,
                  by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
                have hax := ha_val x; rw [ha] at hax
                have hbx := hb_val x; rw [hb] at hbx; simp only [evalSymB, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte, ← hbx, Bool.or_false]
                exact hax
              | true =>
                have hr : r = (Sum.inl true, none) := by
                  simp only [r, cleanGateB, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                  by simp only [hr]; trivial,
                  by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
                have hbx := hb_val x; rw [hb] at hbx; simp only [evalSymB, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte,
                  evalSymB, Sum.elim_inl, id, ← hbx, Bool.or_true]
            | true =>
              cases cb with
              | false =>
                have hr : r = (Sum.inl false, none) := by
                  simp only [r, cleanGateB, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                  by simp only [hr]; trivial,
                  by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
                have hbx := hb_val x; rw [hb] at hbx; simp only [evalSymB, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, ↓reduceIte,
                  evalSymB, Sum.elim_inl, id, ← hbx, Bool.and_false]
              | true =>
                have hr : r = (Sum.inr pa, none) := by
                  simp only [r, cleanGateB, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                  by simp only [gs1, hr, Option.elim_none]; exact ha_inv,
                  by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
                have hax := ha_val x; rw [ha] at hax
                have hbx := hb_val x; rw [hb] at hbx; simp only [evalSymB, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, ↓reduceIte, ← hbx, Bool.and_true]
                exact hax
          | inr pb =>
            rw [hb] at hb_inv
            by_cases heq : pa = pb
            · have hbeq : (pa == pb) = true := beq_iff_eq.mpr heq
              have hr : r = (Sum.inr pa, none) := by
                simp only [r, cleanGateB, ha, hb, Sum.elim_inr, hbeq, ↓reduceIte]
              refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                by simp only [gs1, hr, Option.elim_none]; exact ha_inv,
                by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
              have hax := ha_val x; rw [ha] at hax
              have hbx := hb_val x; rw [hb, ← heq] at hbx
              simp only [gs1, hr, Option.elim_none, ← hax, ← hbx]
              cases g.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_self, Bool.or_self]
            · have hbeq : (pa == pb) = false := beq_eq_false_iff_ne.mpr heq
              by_cases h00 : pa.1 = 0 ∧ pb.1 = 0
              · have hb00 : (pa.1 == 0 && pb.1 == 0) = true := by
                  simp only [Bool.and_eq_true, beq_iff_eq]; exact h00
                have hr : r = (Sum.inl (!g.1), none) := by
                  simp only [r, cleanGateB, ha, hb, Sum.elim_inr, hbeq, Bool.false_eq_true, ↓reduceIte, hb00]
                refine ⟨by simp only [gs1, hr, Option.elim_none]; omega,
                  by simp only [hr]; trivial,
                  by simp only [gs1, hr, Option.elim_none]; exact hcl, fun x => ?_⟩
                have hax := ha_val x; rw [ha] at hax
                have hbx := hb_val x; rw [hb] at hbx
                have hpne : pa.2 ≠ pb.2 := by
                  intro h2
                  apply heq
                  cases pa; cases pb; simp only at h00 h2; rw [h00.1, h00.2, h2]
                simp only [gs1, hr, Option.elim_none, evalSymB, Sum.elim_inl, id, ← hax, ← hbx]
                simp only [Sum.elim_inr, h00.1, h00.2]
                cases hp1 : pa.2 <;> cases hp2 : pb.2 <;> cases g.1 <;>
                  simp only [hp1, hp2] at hpne <;>
                  first | exact (hpne rfl).elim | simp
              · have hb00 : (pa.1 == 0 && pb.1 == 0) = false := by
                  rw [Bool.eq_false_iff]
                  intro h
                  simp only [Bool.and_eq_true, beq_iff_eq] at h
                  exact h00 h
                have hr : r = (Sum.inr (10 + gs_out.length, false), some (g.1, pa, pb)) := by
                  simp only [r, cleanGateB, ha, hb, Sum.elim_inr, hbeq, hb00, Bool.false_eq_true, ↓reduceIte]
                refine ⟨by simp only [gs1, hr, Option.elim_some, List.length_append, List.length_cons, List.length_nil]; omega,
                  by simp only [gs1, hr, Option.elim_some, SymInv, Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; exact ⟨by omega, by omega, fun h => by cases h⟩,
                  by
                    simp only [gs1, hr, Option.elim_some]
                    exact cleanPropB_snoc gs_out (g.1, pa, pb) hcl
                      ⟨ha_inv.1, hb_inv.1, ha_inv.2.1, hb_inv.2.1, ha_inv.2.2, hb_inv.2.2, heq, h00⟩,
                  fun x => ?_⟩
                simp only [gs1, hr, Option.elim_some, evalSymB, Sum.elim_inr, Bool.xor_false, runB_append]
                have hl : 10 + gs_out.length = (runB gs_out (in10 x)).length := by
                  rw [runB_len, in10_len]
                simp only [runB, List.foldl_cons, List.foldl_nil, stepB, hl, getD_snoc_end]
                have hax := ha_val x; rw [ha] at hax; simp only [evalSymB, Sum.elim_inr] at hax
                have hbx := hb_val x; rw [hb] at hbx; simp only [evalSymB, Sum.elim_inr] at hbx
                rw [hax, hbx]
      have hgs1_ge : gs_out.length ≤ gs1.length := by
        dsimp only [gs1]
        cases r.2 with
        | none => exact Nat.le_refl _
        | some g' => simp only [Option.elim_some, List.length_append, List.length_cons, List.length_nil]; omega
      have hkeep_old (x : Fin 9 → Bool) (sb : Bool ⊕ (ℕ × Bool)) (hsb : SymInv gs_out.length sb) :
          evalSymB sb (runB gs1 (in10 x)) = evalSymB sb (runB gs_out (in10 x)) := by
        cases sb with
        | inl c => rfl
        | inr p =>
          simp only [evalSymB, Sum.elim_inr]
          dsimp only [gs1]
          cases r.2 with
          | none => rfl
          | some g' =>
            simp only [Option.elim_some, runB_append]
            rw [runB_keep [g'] (runB gs_out (in10 x)) p.1 (by rw [runB_len, in10_len]; exact hsb.1)]
      have hst1_len : st1.length = 10 + (gs_done ++ [g]).length := by
        simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega
      have hst1_0 : st1.getD 0 (Sum.inl false) = Sum.inr (0, false) := by
        rw [List.getD_append _ _ _ _ (by omega)]; exact hst0
      have hst1_9 : st1.getD 9 (Sum.inl false) = Sum.inl false := by
        rw [List.getD_append _ _ _ _ (by omega)]; exact hst9
      have hst1_inv : ∀ sb ∈ st1, SymInv gs1.length sb := by
        intro sb hsb
        simp only [st1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hsb
        rcases hsb with hsb | rfl
        · have ho := hbd sb hsb
          cases sb with
          | inl c => trivial
          | inr p =>
            have ho1 : p.1 < 10 + gs_out.length := ho.1
            exact ⟨by omega, ho.2.1, ho.2.2⟩
        · exact hstep.2.1
      have hst1_ag : ∀ (x : Fin 9 → Bool) (i : ℕ), i < st1.length →
          evalSymB (st1.getD i (Sum.inl false)) (runB gs1 (in10 x)) =
            (runB (gs_done ++ [g]) (in10 x)).getD i false := by
        intro x i hi
        rw [runB_append]
        change evalSymB (st1.getD i (Sum.inl false)) (runB gs1 (in10 x)) =
          (stepB (runB gs_done (in10 x)) g).getD i false
        by_cases hilt : i < st.length
        · rw [List.getD_append _ _ _ _ hilt, hkeep_old x _ (hget_inv i), hag x i hilt]
          have hne : i ≠ (runB gs_done (in10 x)).length := by rw [runB_len, in10_len]; omega
          exact (getD_snoc_ne (runB gs_done (in10 x)) _ i hne).symm
        · have hieq : i = st.length := by
            simp only [st1, List.length_append, List.length_cons, List.length_nil] at hi; omega
          subst hieq
          have hget : st1.getD st.length (Sum.inl false) = r.1 := by
            simp only [st1, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [hget]
          have hl : st.length = (runB gs_done (in10 x)).length := by rw [runB_len, in10_len, hst]
          dsimp only [stepB]
          rw [hl, getD_snoc_end]
          exact hstep.2.2.2 x
      have hres := ih st1 gs1 (gs_done ++ [g]) hrest_pol hst1_len hst1_0 hst1_9
        (by simp only [List.length_append, List.length_cons, List.length_nil]; exact hstep.1)
        hstep.2.2.1 hst1_inv hst1_ag
      rw [List.append_assoc, List.singleton_append] at hres
      exact hres
  let stInit : List (Bool ⊕ (ℕ × Bool)) :=
    [Sum.inr (0, false), Sum.inr (1, false), Sum.inr (2, false), Sum.inr (3, false),
     Sum.inr (4, false), Sum.inr (5, false), Sum.inr (6, false), Sum.inr (7, false),
     Sum.inr (8, false), Sum.inl false]
  have hclean := clean_fold gsOrig stInit [] [] hgsOrig_pol rfl rfl rfl (Nat.le_refl 0)
    (fun _ h => by cases h)
    (by
      intro sb hsb
      simp only [stInit, List.mem_cons, List.not_mem_nil, or_false] at hsb
      rcases hsb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial)
    (by
      intro x i hi
      simp only [stInit, List.length_cons, List.length_nil] at hi
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [stInit, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, evalSymB, Sum.elim_inr, Sum.elim_inl, id, Bool.xor_false, runB, List.foldl_nil]
      rfl)
  let res1 := gsOrig.foldl cleanStepB (stInit, [])
  let st1 := res1.1
  let gs1 := res1.2
  have hst1_len : st1.length = 10 + s := by
    have h := hclean.1; simp only [List.nil_append, hgsOrig_len] at h; exact h
  have hgs1_len : gs1.length ≤ 14 := by
    have h := hclean.2.1; simp only [List.nil_append, hgsOrig_len] at h
    change gs1.length ≤ s at h; omega
  have hgs1_clean : CleanPropB gs1 := hclean.2.2.1
  let out1 := st1.getD out (Sum.inl false)
  have hout1_inv : SymInv gs1.length out1 := by
    have hi : out < st1.length := by omega
    dsimp only [out1]
    rw [List.getD_eq_getElem _ _ hi]
    exact hclean.2.2.2.1 _ (List.getElem_mem hi)
  have hout1_val (x : Fin 9 → Bool) : evalSymB out1 (runB gs1 (in10 x)) = P9 x := by
    have h := hclean.2.2.2.2 x out (by change out < st1.length; omega)
    simp only [List.nil_append] at h
    rw [h, hgsOrig_val x out hout, hcomp x]
  have hP9_false : P9 (fun _ => false) = false := rfl
  have hP9_true : P9 (fun _ => true) = true := rfl
  have hP9_e0 : P9 (fun i => decide (i = 0)) = false := rfl
  have hout1_inr : ∃ u1 : ℕ, out1 = Sum.inr (u1, false) ∧ u1 < 10 + gs1.length ∧ u1 ≠ 0 ∧ u1 ≠ 9 := by
    cases ho : out1 with
    | inl c =>
      cases c
      · have h := hout1_val (fun _ => true); rw [ho, hP9_true] at h; cases h
      · have h := hout1_val (fun _ => false); rw [ho, hP9_false] at h; cases h
    | inr p =>
      rw [ho] at hout1_inv
      cases hp2 : p.2 with
      | true =>
        have hp1 : p.1 = 0 := hout1_inv.2.2 hp2
        have h := hout1_val (fun _ => false)
        rw [ho] at h
        simp only [evalSymB, Sum.elim_inr, hp1, hp2,
          runB_keep gs1 (in10 (fun _ => false)) 0 (by rw [in10_len]; omega),
          in10_lt (fun _ => false) 0 (by omega), Bool.false_xor, hP9_false] at h
        cases h
      | false =>
        have hp1ne0 : p.1 ≠ 0 := by
          intro h0
          have h := hout1_val (fun i => decide (i = 0))
          rw [ho] at h
          simp only [evalSymB, Sum.elim_inr, h0, hp2, Bool.xor_false,
            runB_keep gs1 (in10 (fun i => decide (i = 0))) 0 (by rw [in10_len]; omega),
            in10_lt (fun i => decide (i = 0)) 0 (by omega), hP9_e0] at h
          cases h
        exact ⟨p.1, by cases p; simp only at hp2; subst hp2; rfl, hout1_inv.1, hp1ne0, hout1_inv.2.1⟩
  obtain ⟨u1, hu1_eq, hu1_lt, hu1_ne0, hu1_ne9⟩ := hout1_inr
  have hu1_val (x : Fin 9 → Bool) : (runB gs1 (in10 x)).getD u1 false = P9 x := by
    have h := hout1_val x
    rw [hu1_eq] at h
    simpa only [evalSymB, Sum.elim_inr, Bool.xor_false] using h
  let drop (t i : ℕ) : ℕ := if i < t then i else i - 1
  let dropPin (t : ℕ) (p : ℕ × Bool) : ℕ × Bool := (drop t p.1, p.2)
  let dropGateB (t : ℕ) (g : Bool × (ℕ × Bool) × (ℕ × Bool)) : Bool × (ℕ × Bool) × (ℕ × Bool) :=
    (g.1, dropPin t g.2.1, dropPin t g.2.2)
  have dropB_sim (t : ℕ) (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) :
      ∀ (wA wB : List Bool),
        wA.length = wB.length + 1 → t ≤ wB.length →
        (∀ g ∈ gs, g.2.1.1 ≠ t ∧ g.2.2.1 ≠ t) →
        (∀ i : ℕ, i ≠ t → wB.getD (drop t i) false = wA.getD i false) →
        ∀ i : ℕ, i ≠ t → (runB (gs.map (dropGateB t)) wB).getD (drop t i) false = (runB gs wA).getD i false := by
    induction gs with
    | nil => intro wA wB _ _ _ hag i hi; exact hag i hi
    | cons g rest ih =>
      intro wA wB hlen htle hno hag i hi
      have hgno := hno g List.mem_cons_self
      have hrest_no : ∀ g' ∈ rest, g'.2.1.1 ≠ t ∧ g'.2.2.1 ≠ t :=
        fun g' hm => hno g' (List.mem_cons_of_mem _ hm)
      change (runB (rest.map (dropGateB t)) (stepB wB (dropGateB t g))).getD (drop t i) false =
        (runB rest (stepB wA g)).getD i false
      have hval_eq :
          (if g.1 = true
            then (wB.getD (drop t g.2.1.1) false ^^ g.2.1.2) && (wB.getD (drop t g.2.2.1) false ^^ g.2.2.2)
            else (wB.getD (drop t g.2.1.1) false ^^ g.2.1.2) || (wB.getD (drop t g.2.2.1) false ^^ g.2.2.2)) =
          (if g.1 = true
            then (wA.getD g.2.1.1 false ^^ g.2.1.2) && (wA.getD g.2.2.1 false ^^ g.2.2.2)
            else (wA.getD g.2.1.1 false ^^ g.2.1.2) || (wA.getD g.2.2.1 false ^^ g.2.2.2)) := by
        rw [hag g.2.1.1 hgno.1, hag g.2.2.1 hgno.2]
      apply ih (stepB wA g) (stepB wB (dropGateB t g))
        (by simp only [stepB, List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [stepB, List.length_append, List.length_cons, List.length_nil]; omega)
        hrest_no _ i hi
      intro z hz
      dsimp only [stepB, dropGateB, dropPin]
      rw [hval_eq]
      by_cases hzeq : z = wA.length
      · subst hzeq
        have hdz : drop t wA.length = wB.length := by dsimp only [drop]; split_ifs <;> omega
        rw [hdz, getD_snoc_end, getD_snoc_end]
      · have hdzne : drop t z ≠ wB.length := by dsimp only [drop]; split_ifs <;> omega
        rw [getD_snoc_ne wB _ (drop t z) hdzne, getD_snoc_ne wA _ z hzeq]
        exact hag z hz
  have prune_exists : ∀ n : ℕ, ∀ (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (ua : ℕ),
      gs.length = n → CleanPropB gs → ua < 10 + gs.length → ua ≠ 0 → ua ≠ 9 →
      (∀ x : Fin 9 → Bool, (runB gs (in10 x)).getD ua false = P9 x) →
      ∃ (gs' : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (u' : ℕ),
        gs'.length ≤ gs.length ∧ CleanPropB gs' ∧ u' < 10 + gs'.length ∧ u' ≠ 0 ∧ u' ≠ 9 ∧
        (∀ x : Fin 9 → Bool, (runB gs' (in10 x)).getD u' false = P9 x) ∧
        (∀ j < gs'.length, 10 + j = u' ∨
          ∃ j' < gs'.length, (gs'.getD j' dB).2.1.1 = 10 + j ∨ (gs'.getD j' dB).2.2.1 = 10 + j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro gs ua hlen hcl hua hu0 hu9 huval
      by_cases hreach : ∀ j < gs.length, 10 + j = ua ∨
          ∃ j' < gs.length, (gs.getD j' dB).2.1.1 = 10 + j ∨ (gs.getD j' dB).2.2.1 = 10 + j
      · exact ⟨gs, ua, Nat.le_refl _, hcl, hua, hu0, hu9, huval, hreach⟩
      · have hex : ∃ j < gs.length, 10 + j ≠ ua ∧
            ∀ j' < gs.length, (gs.getD j' dB).2.1.1 ≠ 10 + j ∧ (gs.getD j' dB).2.2.1 ≠ 10 + j := by
          by_contra hall
          apply hreach
          intro j hj
          by_contra hnot
          apply hall
          refine ⟨j, hj, fun heq => hnot (Or.inl heq), fun j' hj' => ?_⟩
          exact ⟨fun h1 => hnot (Or.inr ⟨j', hj', Or.inl h1⟩), fun h2 => hnot (Or.inr ⟨j', hj', Or.inr h2⟩)⟩
        obtain ⟨j, hj, hju, hjno⟩ := hex
        let t := 10 + j
        let pref := gs.take j
        let suf := gs.drop (j + 1)
        let gs' := pref ++ suf.map (dropGateB t)
        have hpref_len : pref.length = j := List.length_take_of_le (by omega)
        have hsuf_len : suf.length = gs.length - (j + 1) := List.length_drop
        have hgs'_len : gs'.length = gs.length - 1 := by
          simp only [gs', List.length_append, List.length_map, hpref_len, hsuf_len]; omega
        have hsplit : gs = pref ++ [gs[j]] ++ suf := by
          have h1 : gs = gs.take (j + 1) ++ gs.drop (j + 1) := (List.take_append_drop (j + 1) gs).symm
          conv_lhs => rw [h1, List.take_succ_eq_append_getElem hj]
        have hsuf_no : ∀ g ∈ suf, g.2.1.1 ≠ t ∧ g.2.2.1 ≠ t := by
          intro g hg
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
          have hk' : j + 1 + k < gs.length := by rw [hsuf_len] at hk; omega
          have hget : suf[k] = gs.getD (j + 1 + k) dB := by
            rw [List.getD_eq_getElem _ _ hk', List.getElem_drop]
          rw [hget]
          exact hjno (j + 1 + k) hk'
        have hgs'_clean : CleanPropB gs' := by
          intro k hk
          by_cases hkj : k < j
          · have hget : gs'.getD k dB = gs.getD k dB := by
              rw [List.getD_append _ _ _ _ (by rw [hpref_len]; exact hkj)]
              rw [List.getD_eq_getElem _ _ (by rw [hpref_len]; exact hkj),
                  List.getD_eq_getElem _ _ (by omega), List.getElem_take]
            dsimp only; rw [hget]; exact hcl k (by omega)
          · have hk' : k + 1 < gs.length := by omega
            have hks : k - j < suf.length := by rw [hsuf_len]; omega
            have hget : gs'.getD k dB = dropGateB t (gs.getD (k + 1) dB) := by
              have h1 : gs'.getD k dB = (suf.map (dropGateB t)).getD (k - j) dB := by
                have hge : pref.length ≤ k := by rw [hpref_len]; omega
                simp only [gs', List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hpref_len]
              rw [h1, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hks),
                  List.getElem_map, List.getD_eq_getElem _ _ hk']
              congr 1
              have hidx : j + 1 + (k - j) = k + 1 := by omega
              rw [List.getElem_drop]; congr 1
            dsimp only; rw [hget]
            have ho := hcl (k + 1) hk'
            have hno_t := hjno (k + 1) hk'
            change (gs.getD (k + 1) dB).2.1.1 ≠ t ∧ (gs.getD (k + 1) dB).2.2.1 ≠ t at hno_t
            dsimp only [dropGateB, dropPin]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · dsimp only [drop, t] at *; split_ifs <;> omega
            · dsimp only [drop, t] at *; split_ifs <;> omega
            · dsimp only [drop, t] at *; split_ifs <;> omega
            · dsimp only [drop, t] at *; split_ifs <;> omega
            · intro hp; have h0 := ho.2.2.2.2.1 hp; dsimp only [drop, t]; rw [h0]; split_ifs <;> omega
            · intro hp; have h0 := ho.2.2.2.2.2.1 hp; dsimp only [drop, t]; rw [h0]; split_ifs <;> omega
            · intro hpeq
              apply ho.2.2.2.2.2.2.1
              have h1 := congrArg Prod.fst hpeq
              have h2 := congrArg Prod.snd hpeq
              dsimp only at h1 h2
              have h1eq : (gs.getD (k + 1) dB).2.1.1 = (gs.getD (k + 1) dB).2.2.1 := by
                dsimp only [drop, t] at h1; split_ifs at h1 <;> omega
              exact Prod.ext h1eq h2
            · rintro ⟨h1, h2⟩
              apply ho.2.2.2.2.2.2.2
              refine ⟨by dsimp only [drop, t] at h1; split_ifs at h1 <;> omega,
                      by dsimp only [drop, t] at h2; split_ifs at h2 <;> omega⟩
        have hsim_all (x : Fin 9 → Bool) (i : ℕ) (hi : i ≠ t) :
            (runB gs' (in10 x)).getD (drop t i) false = (runB gs (in10 x)).getD i false := by
          symm
          conv_lhs => rw [hsplit]
          rw [runB_append, runB_append, runB_append]
          let w0 := runB pref (in10 x)
          let w1 := runB [gs[j]] w0
          have hw0_len : w0.length = t := by simp only [w0, t, runB_len, in10_len, hpref_len]
          have hw1_len : w1.length = w0.length + 1 := by
            simp only [w1, runB_len, List.length_cons, List.length_nil]
          symm
          apply dropB_sim t suf w1 w0 hw1_len (by omega) hsuf_no _ i hi
          intro z hz
          have hz_ne : z ≠ w0.length := by omega
          by_cases hlt : z < t
          · have hdz : drop t z = z := by dsimp only [drop]; split_ifs; rfl
            rw [hdz]
            exact (getD_snoc_ne w0 _ z hz_ne).symm
          · have hdz : drop t z = z - 1 := by dsimp only [drop]; split_ifs; omega
            rw [hdz, List.getD_eq_default w0 _ (by omega), List.getD_eq_default w1 _ (by omega)]
        obtain ⟨gs'', u'', hle'', hcl'', hu'', hu0'', hu9'', hval'', hreach''⟩ :=
          ih gs'.length (by omega) gs' (drop t ua) rfl hgs'_clean
            (by dsimp only [drop, t]; split_ifs <;> omega)
            (by dsimp only [drop, t]; split_ifs <;> omega)
            (by dsimp only [drop, t]; split_ifs <;> omega)
            (fun x => (hsim_all x ua (fun h => hju h.symm)).trans (huval x))
        exact ⟨gs'', u'', by omega, hcl'', hu'', hu0'', hu9'', hval'', hreach''⟩
  obtain ⟨gs2, u2, hgs2_le, hgs2_clean, hu2_lt, hu2_ne0, hu2_ne9, hu2_val, hgs2_reach⟩ :=
    prune_exists gs1.length gs1 u1 rfl hgs1_clean hu1_lt hu1_ne0 hu1_ne9 hu1_val
  have hgs2_le14 : gs2.length ≤ 14 := by omega
  let isPos0 (g : Bool × (ℕ × Bool) × (ℕ × Bool)) : Bool :=
    (g.2.1 == (0, false)) || (g.2.2 == (0, false))
  let isNeg0 (g : Bool × (ℕ × Bool) × (ℕ × Bool)) : Bool :=
    (g.2.1 == (0, true)) || (g.2.2 == (0, true))
  let isAny0 (g : Bool × (ℕ × Bool) × (ℕ × Bool)) : Bool :=
    (g.2.1.1 == 0) || (g.2.2.1 == 0)
  have hisPos0_iff (g : Bool × (ℕ × Bool) × (ℕ × Bool)) :
      isPos0 g = true ↔ g.2.1 = (0, false) ∨ g.2.2 = (0, false) := by
    simp only [isPos0, Bool.or_eq_true, beq_iff_eq]
  have hisNeg0_iff (g : Bool × (ℕ × Bool) × (ℕ × Bool)) :
      isNeg0 g = true ↔ g.2.1 = (0, true) ∨ g.2.2 = (0, true) := by
    simp only [isNeg0, Bool.or_eq_true, beq_iff_eq]
  have hisAny0_iff (g : Bool × (ℕ × Bool) × (ℕ × Bool)) :
      isAny0 g = true ↔ g.2.1.1 = 0 ∨ g.2.2.1 = 0 := by
    simp only [isAny0, Bool.or_eq_true, beq_iff_eq]
  let nPos := (gs2.filter isPos0).length
  let nNeg := (gs2.filter isNeg0).length
  let nAny := (gs2.filter isAny0).length
  have hnNeg_pos : 1 ≤ nNeg := by
    by_contra hneg0
    have hnoNeg : ∀ g ∈ gs2, g.2.1.1 ≠ 9 ∧ g.2.2.1 ≠ 9 ∧ g.2.1.2 = false ∧ g.2.2.2 = false := by
      intro g hg
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hg
      have hcl := hgs2_clean j hj
      have hgd : gs2.getD j dB = g := by rw [List.getD_eq_getElem _ _ hj, hget]
      rw [hgd] at hcl
      have hnotneg : isNeg0 g = false := by
        cases hn : isNeg0 g with
        | false => rfl
        | true =>
          have hmem : g ∈ gs2.filter isNeg0 := List.mem_filter.mpr ⟨hg, hn⟩
          have hpos : 0 < nNeg := List.length_pos_of_mem hmem
          omega
      have hp1f : g.2.1.2 = false := by
        cases h1 : g.2.1.2 with
        | false => rfl
        | true =>
          have h0 := hcl.2.2.2.2.1 h1
          have heq : g.2.1 = (0, true) := Prod.ext h0 h1
          have ht : isNeg0 g = true := (hisNeg0_iff g).mpr (Or.inl heq)
          rw [ht] at hnotneg; cases hnotneg
      have hp2f : g.2.2.2 = false := by
        cases h2 : g.2.2.2 with
        | false => rfl
        | true =>
          have h0 := hcl.2.2.2.2.2.1 h2
          have heq : g.2.2 = (0, true) := Prod.ext h0 h2
          have ht : isNeg0 g = true := (hisNeg0_iff g).mpr (Or.inr heq)
          rw [ht] at hnotneg; cases hnotneg
      exact ⟨hcl.2.2.1, hcl.2.2.2.1, hp1f, hp2f⟩
    let toMonoGate (g : Bool × (ℕ × Bool) × (ℕ × Bool)) : Gate :=
      ⟨if g.1 = true then GateOp.and else GateOp.or, [drop 9 g.2.1.1, drop 9 g.2.2.1]⟩
    have toMono_sim : ∀ (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (wA wB : List Bool),
        wA.length = wB.length + 1 → 9 ≤ wB.length →
        (∀ g ∈ gs, g.2.1.1 ≠ 9 ∧ g.2.2.1 ≠ 9 ∧ g.2.1.2 = false ∧ g.2.2.2 = false) →
        (∀ i : ℕ, i ≠ 9 → wB.getD (drop 9 i) false = wA.getD i false) →
        ∀ i : ℕ, i ≠ 9 → (runC (gs.map toMonoGate) wB).getD (drop 9 i) false = (runB gs wA).getD i false := by
      intro gs
      induction gs with
      | nil => intro wA wB _ _ _ hag i hi; exact hag i hi
      | cons g rest ih =>
        intro wA wB hlen h9 hno hag i hi
        have hgno := hno g List.mem_cons_self
        have hrest_no : ∀ g' ∈ rest, g'.2.1.1 ≠ 9 ∧ g'.2.2.1 ≠ 9 ∧ g'.2.1.2 = false ∧ g'.2.2.2 = false :=
          fun g' hm => hno g' (List.mem_cons_of_mem _ hm)
        change (runC (rest.map toMonoGate) (stepC wB (toMonoGate g))).getD (drop 9 i) false =
          (runB rest (stepB wA g)).getD i false
        have hval_eq :
            (toMonoGate g).op.eval ((toMonoGate g).inputs.map fun k => wB.getD k false) =
            (if g.1 = true
              then (wA.getD g.2.1.1 false ^^ g.2.1.2) && (wA.getD g.2.2.1 false ^^ g.2.2.2)
              else (wA.getD g.2.1.1 false ^^ g.2.1.2) || (wA.getD g.2.2.1 false ^^ g.2.2.2)) := by
          dsimp only [toMonoGate]
          rw [hgno.2.2.1, hgno.2.2.2]
          cases g.1 <;>
            simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
              eval_and, eval_or, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
              id, Bool.and_true, Bool.or_false, Bool.xor_false,
              hag g.2.1.1 hgno.1, hag g.2.2.1 hgno.2.1]
        apply ih (stepB wA g) (stepC wB (toMonoGate g))
          (by simp only [stepB, stepC, List.length_append, List.length_cons, List.length_nil]; omega)
          (by simp only [stepC, List.length_append, List.length_cons, List.length_nil]; omega)
          hrest_no _ i hi
        intro z hz
        dsimp only [stepB, stepC]
        rw [hval_eq]
        by_cases hzeq : z = wA.length
        · subst hzeq
          have hdz : drop 9 wA.length = wB.length := by dsimp only [drop]; split_ifs <;> omega
          rw [hdz, getD_snoc_end, getD_snoc_end]
        · have hdzne : drop 9 z ≠ wB.length := by dsimp only [drop]; split_ifs <;> omega
          rw [getD_snoc_ne wB _ (drop 9 z) hdzne, getD_snoc_ne wA _ z hzeq]
          exact hag z hz
    let D : Circuit := ⟨gs2.map toMonoGate, drop 9 u2⟩
    have hD_mono : Monotone2 D := by
      intro g hg
      obtain ⟨gb, _, rfl⟩ := List.mem_map.mp hg
      dsimp only [toMonoGate]
      refine ⟨?_, by simp⟩
      cases gb.1
      · exact Or.inr rfl
      · exact Or.inl rfl
    have hD_size : D.size ≤ 14 := by
      change (gs2.map toMonoGate).length ≤ 14
      rw [List.length_map]; exact hgs2_le14
    obtain ⟨x, hx⟩ := hMonoP9 D hD_mono hD_size
    apply hx
    change (runC (gs2.map toMonoGate) (List.ofFn x)).getD (drop 9 u2) false = P9 x
    rw [toMono_sim gs2 (in10 x) (List.ofFn x)
      (by rw [in10_len, List.length_ofFn]) (by rw [List.length_ofFn]) hnoNeg _ u2 hu2_ne9]
    · exact hu2_val x
    · intro i hi
      by_cases hlt : i < 9
      · have hdi : drop 9 i = i := by dsimp only [drop]; split_ifs; rfl
        rw [hdi, in10_lt x i hlt, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt),
            List.getElem_ofFn]
      · have hdi : drop 9 i = i - 1 := by dsimp only [drop]; split_ifs; omega
        rw [hdi, List.getD_eq_default (List.ofFn x) _ (by rw [List.length_ofFn]; omega),
            List.getD_eq_default (in10 x) _ (by rw [in10_len]; omega)]
  have hnPos_pos : 1 ≤ nPos := by
    by_contra hpos0
    have hnoPos : ∀ g ∈ gs2,
        g.2.1 ≠ (0, false) ∧ g.2.2 ≠ (0, false) ∧
        (g.2.1.2 = true → g.2.1.1 = 0) ∧ (g.2.2.2 = true → g.2.2.1 = 0) := by
      intro g hg
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hg
      have hcl := hgs2_clean j hj
      have hgd : gs2.getD j dB = g := by rw [List.getD_eq_getElem _ _ hj, hget]
      rw [hgd] at hcl
      have hnotpos : isPos0 g = false := by
        cases hp : isPos0 g with
        | false => rfl
        | true =>
          have hmem : g ∈ gs2.filter isPos0 := List.mem_filter.mpr ⟨hg, hp⟩
          have hpos : 0 < nPos := List.length_pos_of_mem hmem
          omega
      refine ⟨fun h1 => (by
          have ht : isPos0 g = true := (hisPos0_iff g).mpr (Or.inl h1)
          rw [ht] at hnotpos; cases hnotpos),
        fun h2 => (by
          have ht : isPos0 g = true := (hisPos0_iff g).mpr (Or.inr h2)
          rw [ht] at hnotpos; cases hnotpos),
        hcl.2.2.2.2.1, hcl.2.2.2.2.2.1⟩
    have hanti_mono : ∀ (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (wA wB : List Bool),
        wA.length = wB.length → 1 ≤ wA.length →
        wB.getD 0 false = true → wA.getD 0 false = false →
        (∀ g ∈ gs, g.2.1 ≠ (0, false) ∧ g.2.2 ≠ (0, false) ∧
          (g.2.1.2 = true → g.2.1.1 = 0) ∧ (g.2.2.2 = true → g.2.2.1 = 0)) →
        (∀ i : ℕ, i ≠ 0 → wB.getD i false = true → wA.getD i false = true) →
        ∀ i : ℕ, i ≠ 0 → (runB gs wB).getD i false = true → (runB gs wA).getD i false = true := by
      intro gs
      induction gs with
      | nil => intro wA wB _ _ _ _ _ hle i hi; exact hle i hi
      | cons g rest ih =>
        intro wA wB hlen h1 hwB0 hwA0 hno hle i hi
        have hgno := hno g List.mem_cons_self
        have hrest_no : ∀ g' ∈ rest, g'.2.1 ≠ (0, false) ∧ g'.2.2 ≠ (0, false) ∧
            (g'.2.1.2 = true → g'.2.1.1 = 0) ∧ (g'.2.2.2 = true → g'.2.2.1 = 0) :=
          fun g' hm => hno g' (List.mem_cons_of_mem _ hm)
        have hpin (p : ℕ × Bool) (hpne : p ≠ (0, false)) (hppol : p.2 = true → p.1 = 0) :
            (wB.getD p.1 false ^^ p.2) = true → (wA.getD p.1 false ^^ p.2) = true := by
          cases hp2 : p.2 with
          | true =>
            have hp1 : p.1 = 0 := hppol hp2
            rw [hp1, hwB0]; intro h; cases h
          | false =>
            have hp1ne : p.1 ≠ 0 := fun h0 => hpne (Prod.ext h0 hp2)
            simp only [Bool.xor_false]
            exact hle p.1 hp1ne
        have h1_le := hpin g.2.1 hgno.1 hgno.2.2.1
        have h2_le := hpin g.2.2 hgno.2.1 hgno.2.2.2
        have hval_le :
            (if g.1 = true
              then (wB.getD g.2.1.1 false ^^ g.2.1.2) && (wB.getD g.2.2.1 false ^^ g.2.2.2)
              else (wB.getD g.2.1.1 false ^^ g.2.1.2) || (wB.getD g.2.2.1 false ^^ g.2.2.2)) = true →
            (if g.1 = true
              then (wA.getD g.2.1.1 false ^^ g.2.1.2) && (wA.getD g.2.2.1 false ^^ g.2.2.2)
              else (wA.getD g.2.1.1 false ^^ g.2.1.2) || (wA.getD g.2.2.1 false ^^ g.2.2.2)) = true := by
          cases g.1
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
            rintro (h | h)
            · exact Or.inl (h1_le h)
            · exact Or.inr (h2_le h)
          · simp only [↓reduceIte, Bool.and_eq_true]
            rintro ⟨h1, h2⟩
            exact ⟨h1_le h1, h2_le h2⟩
        change (runB rest (stepB wB g)).getD i false = true → (runB rest (stepB wA g)).getD i false = true
        apply ih (stepB wA g) (stepB wB g)
          (by simp only [stepB, List.length_append, List.length_cons, List.length_nil]; omega)
          (by simp only [stepB, List.length_append, List.length_cons, List.length_nil]; omega)
          (by dsimp only [stepB]; rw [List.getD_append _ _ _ _ (by omega)]; exact hwB0)
          (by dsimp only [stepB]; rw [List.getD_append _ _ _ _ (by omega)]; exact hwA0)
          hrest_no _ i hi
        intro z hz
        dsimp only [stepB]
        by_cases hzeq : z = wB.length
        · subst hzeq
          rw [getD_snoc_end, ← hlen, getD_snoc_end]
          exact hval_le
        · rw [getD_snoc_ne wB _ z hzeq, getD_snoc_ne wA _ z (by omega)]
          exact hle z hz
    let xA : Fin 9 → Bool := fun i => decide (i = 1)
    let xB : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have hP9_xA : P9 xA = false := rfl
    have hP9_xB : P9 xB = true := rfl
    have hfalse : (runB gs2 (in10 xA)).getD u2 false = true := by
      apply hanti_mono gs2 (in10 xA) (in10 xB)
        (by rw [in10_len, in10_len]) (by rw [in10_len]; omega)
        (by rw [in10_lt xB 0 (by omega)]; rfl)
        (by rw [in10_lt xA 0 (by omega)]; rfl)
        hnoPos _ u2 hu2_ne0
      · rw [hu2_val xB, hP9_xB]
      · intro i hi hBi
        by_cases hlt : i < 9
        · rw [in10_lt xB i hlt] at hBi
          rw [in10_lt xA i hlt]
          have hine0 : (⟨i, hlt⟩ : Fin 9) ≠ 0 := fun h => hi (congrArg Fin.val h)
          dsimp only [xB, xA] at hBi ⊢
          simp only [decide_eq_true_eq] at hBi ⊢
          rcases hBi with h0 | h1
          · exact (hine0 h0).elim
          · exact h1
        · by_cases h9 : i = 9
          · rw [h9, in10_9] at hBi; cases hBi
          · rw [List.getD_eq_default (in10 xB) _ (by rw [in10_len]; omega)] at hBi
            cases hBi
    rw [hu2_val xA, hP9_xA] at hfalse
    cases hfalse
  have hn_sum : nPos + nNeg = nAny := by
    have haux : ∀ gs : List (Bool × (ℕ × Bool) × (ℕ × Bool)),
        (∀ g ∈ gs, ¬ (g.2.1.1 = 0 ∧ g.2.2.1 = 0)) →
        (gs.filter isPos0).length + (gs.filter isNeg0).length = (gs.filter isAny0).length := by
      intro gs
      induction gs with
      | nil => intro _; rfl
      | cons g rest ih =>
        intro hdisj
        have hg := hdisj g List.mem_cons_self
        have hih := ih (fun g' hm => hdisj g' (List.mem_cons_of_mem _ hm))
        simp only [List.filter_cons]
        cases h1 : g.2.1.1 with
        | zero =>
          have h2ne : g.2.2.1 ≠ 0 := fun h2 => hg ⟨h1, h2⟩
          have hC : isAny0 g = true := (hisAny0_iff g).mpr (Or.inl h1)
          cases hp1 : g.2.1.2
          · have hA : isPos0 g = true := (hisPos0_iff g).mpr (Or.inl (Prod.ext h1 hp1))
            have hB : isNeg0 g = false := by
              rw [Bool.eq_false_iff]; intro ht
              rcases (hisNeg0_iff g).mp ht with ha | hb
              · have := congrArg Prod.snd ha; rw [hp1] at this; cases this
              · exact h2ne (congrArg Prod.fst hb)
            rw [hA, hB, hC]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
          · have hB : isNeg0 g = true := (hisNeg0_iff g).mpr (Or.inl (Prod.ext h1 hp1))
            have hA : isPos0 g = false := by
              rw [Bool.eq_false_iff]; intro ht
              rcases (hisPos0_iff g).mp ht with ha | hb
              · have := congrArg Prod.snd ha; rw [hp1] at this; cases this
              · exact h2ne (congrArg Prod.fst hb)
            rw [hA, hB, hC]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
        | succ m1 =>
          have h1ne : g.2.1.1 ≠ 0 := by omega
          cases h2 : g.2.2.1 with
          | zero =>
            have hC : isAny0 g = true := (hisAny0_iff g).mpr (Or.inr h2)
            cases hp2 : g.2.2.2
            · have hA : isPos0 g = true := (hisPos0_iff g).mpr (Or.inr (Prod.ext h2 hp2))
              have hB : isNeg0 g = false := by
                rw [Bool.eq_false_iff]; intro ht
                rcases (hisNeg0_iff g).mp ht with ha | hb
                · exact h1ne (congrArg Prod.fst ha)
                · have := congrArg Prod.snd hb; rw [hp2] at this; cases this
              rw [hA, hB, hC]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
            · have hB : isNeg0 g = true := (hisNeg0_iff g).mpr (Or.inr (Prod.ext h2 hp2))
              have hA : isPos0 g = false := by
                rw [Bool.eq_false_iff]; intro ht
                rcases (hisPos0_iff g).mp ht with ha | hb
                · exact h1ne (congrArg Prod.fst ha)
                · have := congrArg Prod.snd hb; rw [hp2] at this; cases this
              rw [hA, hB, hC]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
          | succ m2 =>
            have h2ne : g.2.2.1 ≠ 0 := by omega
            have hA : isPos0 g = false := by
              rw [Bool.eq_false_iff]; intro ht
              rcases (hisPos0_iff g).mp ht with ha | hb
              · exact h1ne (congrArg Prod.fst ha)
              · exact h2ne (congrArg Prod.fst hb)
            have hB : isNeg0 g = false := by
              rw [Bool.eq_false_iff]; intro ht
              rcases (hisNeg0_iff g).mp ht with ha | hb
              · exact h1ne (congrArg Prod.fst ha)
              · exact h2ne (congrArg Prod.fst hb)
            have hC : isAny0 g = false := by
              rw [Bool.eq_false_iff]; intro ht
              rcases (hisAny0_iff g).mp ht with ha | hb
              · exact h1ne ha
              · exact h2ne hb
            rw [hA, hB, hC]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hih
    apply haux gs2
    intro g hg
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hg
    have hcl := hgs2_clean j hj
    have hgd : gs2.getD j dB = g := by rw [List.getD_eq_getElem _ _ hj, hget]
    rw [hgd] at hcl
    exact hcl.2.2.2.2.2.2.2
  let lift (y : Fin 8 → Bool) : Fin 9 → Bool :=
    fun i => if h : i.val = 0 then false else y ⟨i.val - 1, by omega⟩
  have hP9_lift (y : Fin 8 → Bool) : P9 (lift y) = H y := by
    change ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
      (fun e => lift y e.1 && lift y e.2) = H y
    simp only [H, List.any_cons, List.any_nil, lift]
    change (false && y 0 || (y 0 && y 1 || (y 1 && y 2 || (y 2 && y 3 || (y 3 && false ||
      (false && y 4 || (y 0 && y 5 || (y 1 && y 6 || (y 2 && y 7 ||
      (y 4 && y 6 || (y 5 && y 7 || (y 7 && y 4 || false)))))))))))) =
      (y 0 && y 1 || (y 1 && y 2 || (y 2 && y 3 || (y 0 && y 5 || (y 1 && y 6 ||
      (y 2 && y 7 || (y 4 && y 6 || (y 5 && y 7 || (y 7 && y 4 || false)))))))))
    simp only [Bool.false_and, Bool.and_false, Bool.false_or]
  let evalSymM (sm : Bool ⊕ ℕ) (ws : List Bool) : Bool :=
    Sum.elim id (fun k => ws.getD k false) sm
  let readPin (st : List (Bool ⊕ ℕ)) (p : ℕ × Bool) : Bool ⊕ ℕ :=
    Sum.elim (fun c => Sum.inl (c ^^ p.2)) Sum.inr (st.getD p.1 (Sum.inl false))
  let elimGateM (st : List (Bool ⊕ ℕ)) (outIdx : ℕ)
      (g : Bool × (ℕ × Bool) × (ℕ × Bool)) : (Bool ⊕ ℕ) × Option Gate :=
    let a := readPin st g.2.1
    let b := readPin st g.2.2
    Sum.elim
      (fun ca => Bool.casesOn g.1
        (Bool.casesOn ca (b, none) (Sum.inl true, none))
        (Bool.casesOn ca (Sum.inl false, none) (b, none)))
      (fun ka => Sum.elim
        (fun cb => Bool.casesOn g.1
          (Bool.casesOn cb (Sum.inr ka, none) (Sum.inl true, none))
          (Bool.casesOn cb (Sum.inl false, none) (Sum.inr ka, none)))
        (fun kb => (Sum.inr outIdx, some ⟨if g.1 = true then GateOp.and else GateOp.or, [ka, kb]⟩)) b) a
  let elimStepM (acc : List (Bool ⊕ ℕ) × List Gate × List Bool)
      (g : Bool × (ℕ × Bool) × (ℕ × Bool)) :
      List (Bool ⊕ ℕ) × List Gate × List Bool :=
    let r := elimGateM acc.1 (8 + acc.2.1.length) g
    (acc.1 ++ [r.1], Option.elim r.2 acc.2.1 (fun g' => acc.2.1 ++ [g']), acc.2.2 ++ [r.2.isSome])
  have heG_indep (sL : List (Bool ⊕ ℕ)) (o1 o2 : ℕ) (gx : Bool × (ℕ × Bool) × (ℕ × Bool)) :
      (elimGateM sL o1 gx).2.isSome = (elimGateM sL o2 gx).2.isSome ∧
      (∀ c : Bool, (elimGateM sL o1 gx).1 = Sum.inl c ↔ (elimGateM sL o2 gx).1 = Sum.inl c) := by
    dsimp only [elimGateM]
    cases readPin sL gx.2.1 with
    | inl ca => cases gx.1 <;> cases ca <;> exact ⟨rfl, fun _ => Iff.rfl⟩
    | inr ka =>
      cases readPin sL gx.2.2 with
      | inl cb => cases gx.1 <;> cases cb <;> exact ⟨rfl, fun _ => Iff.rfl⟩
      | inr kb => exact ⟨rfl, fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩
  have elim_fold : ∀ (gs_in : List (Bool × (ℕ × Bool) × (ℕ × Bool)))
      (st : List (Bool ⊕ ℕ)) (gs_out : List Gate) (fl : List Bool)
      (gs_done : List (Bool × (ℕ × Bool) × (ℕ × Bool))),
      (∀ g ∈ gs_in, (g.2.1.2 = true → g.2.1.1 = 0) ∧ (g.2.2.2 = true → g.2.2.1 = 0)) →
      st.length = 10 + gs_done.length →
      st.getD 0 (Sum.inl false) = Sum.inl false →
      fl.length = gs_done.length →
      gs_out.length = fl.count true →
      (∀ g ∈ gs_out, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ sm ∈ st, Sum.elim (fun _ => True) (fun k => k < 8 + gs_out.length) sm) →
      (∀ (y : Fin 8 → Bool) (i : ℕ), i < st.length →
        evalSymM (st.getD i (Sum.inl false)) (runC gs_out (List.ofFn y)) =
          (runB gs_done (in10 (lift y))).getD i false) →
      let res := gs_in.foldl elimStepM (st, gs_out, fl)
      res.1.length = 10 + (gs_done ++ gs_in).length ∧
      res.2.2.length = (gs_done ++ gs_in).length ∧
      res.2.1.length = res.2.2.count true ∧
      (∀ g ∈ res.2.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ i < st.length, res.1.getD i (Sum.inl false) = st.getD i (Sum.inl false)) ∧
      (∀ j < fl.length, res.2.2.getD j false = fl.getD j false) ∧
      (∀ j < gs_in.length,
        let gx := gs_in.getD j dB
        gx.2.1.1 < 10 + gs_done.length + j → gx.2.2.1 < 10 + gs_done.length + j →
        let r := elimGateM res.1 (8 + gs_out.length) gx
        (res.2.2.getD (gs_done.length + j) false = r.2.isSome) ∧
        (∀ c : Bool, r.1 = Sum.inl c → res.1.getD (10 + gs_done.length + j) (Sum.inl false) = Sum.inl c)) ∧
      (∀ (y : Fin 8 → Bool) (i : ℕ), i < res.1.length →
        evalSymM (res.1.getD i (Sum.inl false)) (runC res.2.1 (List.ofFn y)) =
          (runB (gs_done ++ gs_in) (in10 (lift y))).getD i false) := by
    intro gs_in
    induction gs_in with
    | nil =>
      intro st gs_out fl gs_done _ hst _ hfl hcnt hmono _ hag
      simp only [List.foldl_nil, List.append_nil, List.length_nil]
      exact ⟨hst, hfl, hcnt, hmono, fun _ _ => trivial, fun _ _ => trivial, fun j hj => by omega, hag⟩
    | cons g rest ih =>
      intro st gs_out fl gs_done hpol_in hst hst0 hfl hcnt hmono hbd hag
      have hgpol := hpol_in g List.mem_cons_self
      have hrest_pol : ∀ g' ∈ rest, (g'.2.1.2 = true → g'.2.1.1 = 0) ∧ (g'.2.2.2 = true → g'.2.2.1 = 0) :=
        fun g' hm => hpol_in g' (List.mem_cons_of_mem _ hm)
      have hget_bd (i : ℕ) : Sum.elim (fun _ => True) (fun k => k < 8 + gs_out.length) (st.getD i (Sum.inl false)) := by
        by_cases hi : i < st.length
        · rw [List.getD_eq_getElem _ _ hi]; exact hbd _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; trivial
      have hread_bd (p : ℕ × Bool) :
          Sum.elim (fun _ => True) (fun k => k < 8 + gs_out.length) (readPin st p) := by
        dsimp only [readPin]
        have h := hget_bd p.1
        cases hs : st.getD p.1 (Sum.inl false) with
        | inl c => trivial
        | inr k => rw [hs] at h; exact h
      have hval (y : Fin 8 → Bool) (i : ℕ) :
          evalSymM (st.getD i (Sum.inl false)) (runC gs_out (List.ofFn y)) =
            (runB gs_done (in10 (lift y))).getD i false := by
        by_cases hi : i < st.length
        · exact hag y i hi
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
              List.getD_eq_default _ _ (by rw [runB_len, in10_len]; omega)]
          rfl
      have hread_val (y : Fin 8 → Bool) (p : ℕ × Bool) (hp : p.2 = true → p.1 = 0) :
          evalSymM (readPin st p) (runC gs_out (List.ofFn y)) =
            ((runB gs_done (in10 (lift y))).getD p.1 false ^^ p.2) := by
        rw [← hval y p.1]
        cases hp2 : p.2 with
        | false =>
          dsimp only [readPin]
          cases st.getD p.1 (Sum.inl false) <;>
            simp only [hp2, Sum.elim_inl, Sum.elim_inr, evalSymM, id, Bool.xor_false]
        | true =>
          have hp1 := hp hp2
          simp only [readPin, hp1, hp2, hst0, Sum.elim_inl, evalSymM, id]
      let r := elimGateM st (8 + gs_out.length) g
      let st1 := st ++ [r.1]
      let gs1 := Option.elim r.2 gs_out (fun g' => gs_out ++ [g'])
      let fl1 := fl ++ [r.2.isSome]
      have hcnt_none (hr : r.2 = none) : gs1.length = fl1.count true := by
        simp only [gs1, fl1, hr, Option.elim_none, Option.isSome_none,
          List.count_append, List.count_cons, List.count_nil, hcnt]; rfl
      have hcnt_some (g' : Gate) (hr : r.2 = some g') : gs1.length = fl1.count true := by
        simp only [gs1, fl1, hr, Option.elim_some, Option.isSome_some,
          List.length_append, List.length_cons, List.length_nil,
          List.count_append, List.count_cons, List.count_nil, hcnt, beq_self_eq_true, ↓reduceIte]
      have hstep : gs1.length = fl1.count true ∧
          (∀ g' ∈ gs1, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
          Sum.elim (fun _ => True) (fun k => k < 8 + gs1.length) r.1 ∧
          (∀ y : Fin 8 → Bool,
            evalSymM r.1 (runC gs1 (List.ofFn y)) =
              let b1 := (runB gs_done (in10 (lift y))).getD g.2.1.1 false ^^ g.2.1.2
              let b2 := (runB gs_done (in10 (lift y))).getD g.2.2.1 false ^^ g.2.2.2
              if g.1 = true then b1 && b2 else b1 || b2) := by
        cases ha : readPin st g.2.1 with
        | inl ca =>
          cases hg1 : g.1 with
          | false =>
            cases ca with
            | false =>
              have hr : r = (readPin st g.2.2, none) := by simp only [r, elimGateM, ha, hg1, Sum.elim_inl]
              refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                by simp only [gs1, hr, Option.elim_none]; exact hread_bd g.2.2, fun y => ?_⟩
              have hax := hread_val y g.2.1 hgpol.1; rw [ha] at hax; simp only [evalSymM, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte, ← hax, Bool.false_or]
              exact hread_val y g.2.2 hgpol.2
            | true =>
              have hr : r = (Sum.inl true, none) := by simp only [r, elimGateM, ha, hg1, Sum.elim_inl]
              refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                by simp only [hr]; trivial, fun y => ?_⟩
              have hax := hread_val y g.2.1 hgpol.1; rw [ha] at hax; simp only [evalSymM, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte,
                evalSymM, Sum.elim_inl, id, ← hax, Bool.true_or]
          | true =>
            cases ca with
            | false =>
              have hr : r = (Sum.inl false, none) := by simp only [r, elimGateM, ha, hg1, Sum.elim_inl]
              refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                by simp only [hr]; trivial, fun y => ?_⟩
              have hax := hread_val y g.2.1 hgpol.1; rw [ha] at hax; simp only [evalSymM, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, ↓reduceIte,
                evalSymM, Sum.elim_inl, id, ← hax, Bool.false_and]
            | true =>
              have hr : r = (readPin st g.2.2, none) := by simp only [r, elimGateM, ha, hg1, Sum.elim_inl]
              refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                by simp only [gs1, hr, Option.elim_none]; exact hread_bd g.2.2, fun y => ?_⟩
              have hax := hread_val y g.2.1 hgpol.1; rw [ha] at hax; simp only [evalSymM, Sum.elim_inl, id] at hax
              simp only [gs1, hr, Option.elim_none, ↓reduceIte, ← hax, Bool.true_and]
              exact hread_val y g.2.2 hgpol.2
        | inr ka =>
          have hka := hread_bd g.2.1; rw [ha] at hka
          cases hb : readPin st g.2.2 with
          | inl cb =>
            cases hg1 : g.1 with
            | false =>
              cases cb with
              | false =>
                have hr : r = (Sum.inr ka, none) := by
                  simp only [r, elimGateM, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                  by simp only [gs1, hr, Option.elim_none]; exact hka, fun y => ?_⟩
                have hax := hread_val y g.2.1 hgpol.1; rw [ha] at hax
                have hbx := hread_val y g.2.2 hgpol.2; rw [hb] at hbx; simp only [evalSymM, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte, ← hbx, Bool.or_false]
                exact hax
              | true =>
                have hr : r = (Sum.inl true, none) := by
                  simp only [r, elimGateM, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                  by simp only [hr]; trivial, fun y => ?_⟩
                have hbx := hread_val y g.2.2 hgpol.2; rw [hb] at hbx; simp only [evalSymM, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, Bool.false_eq_true, ↓reduceIte,
                  evalSymM, Sum.elim_inl, id, ← hbx, Bool.or_true]
            | true =>
              cases cb with
              | false =>
                have hr : r = (Sum.inl false, none) := by
                  simp only [r, elimGateM, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                  by simp only [hr]; trivial, fun y => ?_⟩
                have hbx := hread_val y g.2.2 hgpol.2; rw [hb] at hbx; simp only [evalSymM, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, ↓reduceIte,
                  evalSymM, Sum.elim_inl, id, ← hbx, Bool.and_false]
              | true =>
                have hr : r = (Sum.inr ka, none) := by
                  simp only [r, elimGateM, ha, hb, hg1, Sum.elim_inr, Sum.elim_inl]
                refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hmono,
                  by simp only [gs1, hr, Option.elim_none]; exact hka, fun y => ?_⟩
                have hax := hread_val y g.2.1 hgpol.1; rw [ha] at hax
                have hbx := hread_val y g.2.2 hgpol.2; rw [hb] at hbx; simp only [evalSymM, Sum.elim_inl, id] at hbx
                simp only [gs1, hr, Option.elim_none, ↓reduceIte, ← hbx, Bool.and_true]
                exact hax
          | inr kb =>
            let gNew : Gate := ⟨if g.1 = true then GateOp.and else GateOp.or, [ka, kb]⟩
            have hr : r = (Sum.inr (8 + gs_out.length), some gNew) := by
              simp only [r, elimGateM, ha, hb, Sum.elim_inr, gNew]
            refine ⟨hcnt_some gNew (by rw [hr]), ?_,
              by simp only [gs1, hr, Option.elim_some, Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; omega,
              fun y => ?_⟩
            · intro g' hm
              simp only [gs1, hr, Option.elim_some, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
              rcases hm with hm | rfl
              · exact hmono g' hm
              · dsimp only [gNew]
                refine ⟨?_, by simp⟩
                cases g.1
                · exact Or.inr rfl
                · exact Or.inl rfl
            · simp only [gs1, hr, Option.elim_some, evalSymM, Sum.elim_inr, runC_append]
              have hl : 8 + gs_out.length = (runC gs_out (List.ofFn y)).length := by
                rw [runC_len, List.length_ofFn]
              have hax := hread_val y g.2.1 hgpol.1; rw [ha] at hax; simp only [evalSymM, Sum.elim_inr] at hax
              have hbx := hread_val y g.2.2 hgpol.2; rw [hb] at hbx; simp only [evalSymM, Sum.elim_inr] at hbx
              change (stepC (runC gs_out (List.ofFn y)) gNew).getD (8 + gs_out.length) false = _
              dsimp only [stepC, gNew]
              rw [hl, getD_snoc_end]
              cases g.1 <;>
                simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
                  eval_and, eval_or, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
                  id, Bool.and_true, Bool.or_false, hax, hbx]
      have hgs1_ge : gs_out.length ≤ gs1.length := by
        dsimp only [gs1]
        cases r.2 with
        | none => exact Nat.le_refl _
        | some _ => simp only [Option.elim_some, List.length_append, List.length_cons, List.length_nil]; omega
      have hkeep_old (y : Fin 8 → Bool) (sm : Bool ⊕ ℕ)
          (hsm : Sum.elim (fun _ => True) (fun k => k < 8 + gs_out.length) sm) :
          evalSymM sm (runC gs1 (List.ofFn y)) = evalSymM sm (runC gs_out (List.ofFn y)) := by
        cases sm with
        | inl c => rfl
        | inr k =>
          simp only [evalSymM, Sum.elim_inr]
          dsimp only [gs1]
          cases r.2 with
          | none => rfl
          | some g' =>
            simp only [Option.elim_some, runC_append]
            rw [runC_keep [g'] (runC gs_out (List.ofFn y)) k (by rw [runC_len, List.length_ofFn]; exact hsm)]
      have hst1_len : st1.length = 10 + (gs_done ++ [g]).length := by
        simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega
      have hst1_0 : st1.getD 0 (Sum.inl false) = Sum.inl false := by
        rw [List.getD_append _ _ _ _ (by omega)]; exact hst0
      have hfl1_len : fl1.length = (gs_done ++ [g]).length := by
        simp only [fl1, List.length_append, List.length_cons, List.length_nil]; omega
      have hst1_bd : ∀ sm ∈ st1, Sum.elim (fun _ => True) (fun k => k < 8 + gs1.length) sm := by
        intro sm hsm
        simp only [st1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hsm
        rcases hsm with hsm | rfl
        · have ho := hbd sm hsm
          cases sm with
          | inl _ => trivial
          | inr k => exact Nat.lt_of_lt_of_le ho (by omega)
        · exact hstep.2.2.1
      have hst1_ag : ∀ (y : Fin 8 → Bool) (i : ℕ), i < st1.length →
          evalSymM (st1.getD i (Sum.inl false)) (runC gs1 (List.ofFn y)) =
            (runB (gs_done ++ [g]) (in10 (lift y))).getD i false := by
        intro y i hi
        rw [runB_append]
        change evalSymM (st1.getD i (Sum.inl false)) (runC gs1 (List.ofFn y)) =
          (stepB (runB gs_done (in10 (lift y))) g).getD i false
        by_cases hilt : i < st.length
        · rw [List.getD_append _ _ _ _ hilt, hkeep_old y _ (hget_bd i), hag y i hilt]
          have hne : i ≠ (runB gs_done (in10 (lift y))).length := by rw [runB_len, in10_len]; omega
          exact (getD_snoc_ne (runB gs_done (in10 (lift y))) _ i hne).symm
        · have hieq : i = st.length := by
            simp only [st1, List.length_append, List.length_cons, List.length_nil] at hi; omega
          subst hieq
          have hget : st1.getD st.length (Sum.inl false) = r.1 := by
            simp only [st1, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [hget]
          have hl : st.length = (runB gs_done (in10 (lift y))).length := by rw [runB_len, in10_len, hst]
          dsimp only [stepB]
          rw [hl, getD_snoc_end]
          exact hstep.2.2.2 y
      have hres := ih st1 gs1 fl1 (gs_done ++ [g]) hrest_pol hst1_len hst1_0 hfl1_len
        hstep.1 hstep.2.1 hst1_bd hst1_ag
      rw [List.append_assoc, List.singleton_append] at hres
      dsimp only
      have hfold : (g :: rest).foldl elimStepM (st, gs_out, fl) = rest.foldl elimStepM (st1, gs1, fl1) := rfl
      rw [hfold]
      refine ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1, ?_, ?_, ?_, hres.2.2.2.2.2.2.2⟩
      · intro i hi
        rw [hres.2.2.2.2.1 i (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)]
        exact List.getD_append _ _ _ _ hi
      · intro j hj
        rw [hres.2.2.2.2.2.1 j (by simp only [fl1, List.length_append, List.length_cons, List.length_nil]; omega)]
        exact List.getD_append _ _ _ _ hj
      · intro j hj hb1 hb2
        cases j with
        | zero =>
          change g.2.1.1 < 10 + gs_done.length + 0 at hb1
          change g.2.2.1 < 10 + gs_done.length + 0 at hb2
          have hst_agree1 : (rest.foldl elimStepM (st1, gs1, fl1)).1.getD g.2.1.1 (Sum.inl false) =
              st.getD g.2.1.1 (Sum.inl false) := by
            rw [hres.2.2.2.2.1 g.2.1.1 (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          have hst_agree2 : (rest.foldl elimStepM (st1, gs1, fl1)).1.getD g.2.2.1 (Sum.inl false) =
              st.getD g.2.2.1 (Sum.inl false) := by
            rw [hres.2.2.2.2.1 g.2.2.1 (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          have heg_eq : elimGateM (rest.foldl elimStepM (st1, gs1, fl1)).1 (8 + gs_out.length) g = r := by
            dsimp only [r, elimGateM, readPin]
            rw [hst_agree1, hst_agree2]
          change ((rest.foldl elimStepM (st1, gs1, fl1)).2.2.getD (gs_done.length + 0) false =
              (elimGateM (rest.foldl elimStepM (st1, gs1, fl1)).1 (8 + gs_out.length) g).2.isSome) ∧
            (∀ c : Bool, (elimGateM (rest.foldl elimStepM (st1, gs1, fl1)).1 (8 + gs_out.length) g).1 = Sum.inl c →
              (rest.foldl elimStepM (st1, gs1, fl1)).1.getD (10 + gs_done.length + 0) (Sum.inl false) = Sum.inl c)
          rw [heg_eq]
          refine ⟨?_, ?_⟩
          · rw [Nat.add_zero, hres.2.2.2.2.2.1 gs_done.length (by simp only [fl1, List.length_append, List.length_cons, List.length_nil]; omega)]
            simp only [fl1, ← hfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          · intro c hc
            rw [Nat.add_zero, hres.2.2.2.2.1 (10 + gs_done.length) (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)]
            rw [← hst]
            simp only [st1, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hc]
        | succ j' =>
          change (rest.getD j' dB).2.1.1 < 10 + gs_done.length + (j' + 1) at hb1
          change (rest.getD j' dB).2.2.1 < 10 + gs_done.length + (j' + 1) at hb2
          have hj' : j' < rest.length := by simp only [List.length_cons] at hj; omega
          have hsub := hres.2.2.2.2.2.2.1 j' hj'
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          have hidx1 : (gs_done ++ [g]).length + j' = gs_done.length + (j' + 1) := by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          have hidx2 : 10 + (gs_done ++ [g]).length + j' = 10 + gs_done.length + (j' + 1) := by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          rw [hidx1, hidx2] at hsub
          have hindep := heG_indep (rest.foldl elimStepM (st1, gs1, fl1)).1 (8 + gs1.length) (8 + gs_out.length) (rest.getD j' dB)
          change ((rest.foldl elimStepM (st1, gs1, fl1)).2.2.getD (gs_done.length + (j' + 1)) false =
              (elimGateM (rest.foldl elimStepM (st1, gs1, fl1)).1 (8 + gs_out.length) (rest.getD j' dB)).2.isSome) ∧
            (∀ c : Bool, (elimGateM (rest.foldl elimStepM (st1, gs1, fl1)).1 (8 + gs_out.length) (rest.getD j' dB)).1 = Sum.inl c →
              (rest.foldl elimStepM (st1, gs1, fl1)).1.getD (10 + gs_done.length + (j' + 1)) (Sum.inl false) = Sum.inl c)
          refine ⟨hsub.1.trans hindep.1, fun c hc => hsub.2 c ((hindep.2 c).mpr hc)⟩
  let st0 : List (Bool ⊕ ℕ) :=
    [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3,
     Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl false]
  have hgs2_pol : ∀ g ∈ gs2, (g.2.1.2 = true → g.2.1.1 = 0) ∧ (g.2.2.2 = true → g.2.2.1 = 0) := by
    intro g hg
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hg
    have hcl := hgs2_clean j hj
    have hgd : gs2.getD j dB = g := by rw [List.getD_eq_getElem _ _ hj, hget]
    rw [hgd] at hcl
    exact ⟨hcl.2.2.2.2.1, hcl.2.2.2.2.2.1⟩
  have helim := elim_fold gs2 st0 [] [] [] hgs2_pol rfl rfl rfl rfl (fun _ h => by cases h)
    (by
      intro sm hm
      simp only [st0, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | trivial | (simp only [Sum.elim_inr, List.length_nil, Nat.add_zero]; omega))
    (by
      intro y i hi
      simp only [st0, List.length_cons, List.length_nil] at hi
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change false = (in10 (lift y)).getD 0 false
        rw [in10_lt _ 0 (by omega)]; rfl
      · change (List.ofFn y).getD 0 false = (in10 (lift y)).getD 1 false
        rw [in10_lt _ 1 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change (List.ofFn y).getD 1 false = (in10 (lift y)).getD 2 false
        rw [in10_lt _ 2 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change (List.ofFn y).getD 2 false = (in10 (lift y)).getD 3 false
        rw [in10_lt _ 3 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change (List.ofFn y).getD 3 false = (in10 (lift y)).getD 4 false
        rw [in10_lt _ 4 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change (List.ofFn y).getD 4 false = (in10 (lift y)).getD 5 false
        rw [in10_lt _ 5 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change (List.ofFn y).getD 5 false = (in10 (lift y)).getD 6 false
        rw [in10_lt _ 6 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change (List.ofFn y).getD 6 false = (in10 (lift y)).getD 7 false
        rw [in10_lt _ 7 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change (List.ofFn y).getD 7 false = (in10 (lift y)).getD 8 false
        rw [in10_lt _ 8 (by omega), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      · change false = (in10 (lift y)).getD 9 false
        exact (in10_9 _).symm)
  let res0 := gs2.foldl elimStepM (st0, [], [])
  let stF := res0.1
  let gs0 := res0.2.1
  let flF := res0.2.2
  have hflF_len : flF.length = gs2.length := by
    have h := helim.2.1; simp only [List.nil_append] at h; exact h
  have hgs0_cnt : gs0.length = flF.count true := helim.2.2.1
  have hgs0_mono : ∀ g ∈ gs0, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    helim.2.2.2.1
  have hstF_0 : stF.getD 0 (Sum.inl false) = Sum.inl false :=
    helim.2.2.2.2.1 0 (by simp [st0])
  have hstF_val : ∀ (y : Fin 8 → Bool) (i : ℕ), i < 10 + gs2.length →
      evalSymM (stF.getD i (Sum.inl false)) (runC gs0 (List.ofFn y)) =
        (runB gs2 (in10 (lift y))).getD i false := by
    intro y i hi
    have hstlen : stF.length = 10 + gs2.length := by
      have h := helim.1; simp only [List.nil_append] at h; exact h
    have h := helim.2.2.2.2.2.2.2 y i (by change i < stF.length; omega)
    simp only [List.nil_append] at h
    exact h
  let out0 := stF.getD u2 (Sum.inl false)
  have hout0_val (y : Fin 8 → Bool) : evalSymM out0 (runC gs0 (List.ofFn y)) = H y := by
    rw [hstF_val y u2 hu2_lt, hu2_val (lift y), hP9_lift y]
  have hH_false : H (fun _ => false) = false := rfl
  have hH_true : H (fun _ => true) = true := rfl
  have hout0_ne_inl (c : Bool) : out0 ≠ Sum.inl c := by
    intro h
    cases c
    · have hy := hout0_val (fun _ => true); rw [h, hH_true] at hy; cases hy
    · have hy := hout0_val (fun _ => false); rw [h, hH_false] at hy; cases hy
  have hgs0_ge12 : 12 ≤ gs0.length := by
    by_contra hle11
    cases ho : out0 with
    | inl c => exact hout0_ne_inl c ho
    | inr o0 =>
      let D0 : Circuit := ⟨gs0, o0⟩
      have hD0_mono : Monotone2 D0 := hgs0_mono
      have hD0_size : D0.size ≤ 11 := by change gs0.length ≤ 11; omega
      obtain ⟨y, hy⟩ := hMonoH D0 hD0_mono hD0_size
      apply hy
      change (runC gs0 (List.ofFn y)).getD o0 false = H y
      have h := hout0_val y
      rw [ho] at h
      exact h
  have hread_inl (p : ℕ × Bool) (b : Bool) (h : stF.getD p.1 (Sum.inl false) = Sum.inl b) :
      readPin stF p = Sum.inl (b ^^ p.2) := by
    simp only [readPin, h, Sum.elim_inl]
  have hruleA (j : ℕ) (hj : j < gs2.length)
      (hex : (∃ b : Bool, stF.getD (gs2.getD j dB).2.1.1 (Sum.inl false) = Sum.inl b) ∨
        (∃ b : Bool, stF.getD (gs2.getD j dB).2.2.1 (Sum.inl false) = Sum.inl b)) :
      flF.getD j false = false := by
    have hcl := hgs2_clean j hj
    have h7 := helim.2.2.2.2.2.2.1 j hj (by simpa only [List.length_nil, Nat.add_zero] using hcl.1)
      (by simpa only [List.length_nil, Nat.add_zero] using hcl.2.1)
    simp only [List.length_nil, Nat.zero_add] at h7
    rw [h7.1]
    dsimp only [elimGateM]
    rcases hex with ⟨b, hb⟩ | ⟨b, hb⟩
    · rw [hread_inl _ b hb]
      cases (gs2.getD j dB).1 <;> cases (b ^^ (gs2.getD j dB).2.1.2) <;> rfl
    · rw [hread_inl _ b hb]
      cases readPin stF (gs2.getD j dB).2.1 with
      | inl ca => cases (gs2.getD j dB).1 <;> cases ca <;> rfl
      | inr _ => cases (gs2.getD j dB).1 <;> cases (b ^^ (gs2.getD j dB).2.2.2) <;> rfl
  have hruleB_and_false (j : ℕ) (hj : j < gs2.length) (hand : (gs2.getD j dB).1 = true)
      (h0 : (gs2.getD j dB).2.1 = (0, false) ∨ (gs2.getD j dB).2.2 = (0, false)) :
      stF.getD (10 + j) (Sum.inl false) = Sum.inl false := by
    have hcl := hgs2_clean j hj
    have h7 := helim.2.2.2.2.2.2.1 j hj (by simpa only [List.length_nil, Nat.add_zero] using hcl.1)
      (by simpa only [List.length_nil, Nat.add_zero] using hcl.2.1)
    simp only [List.length_nil, Nat.add_zero] at h7
    apply h7.2 false
    dsimp only [elimGateM]
    rw [hand]
    rcases h0 with h1 | h2
    · rw [h1, hread_inl (0, false) false hstF_0]; rfl
    · rw [h2, hread_inl (0, false) false hstF_0]
      cases readPin stF (gs2.getD j dB).2.1 with
      | inl ca => cases ca <;> rfl
      | inr _ => rfl
  have hruleB_or_true (j : ℕ) (hj : j < gs2.length) (hor : (gs2.getD j dB).1 = false)
      (h0 : (gs2.getD j dB).2.1 = (0, true) ∨ (gs2.getD j dB).2.2 = (0, true)) :
      stF.getD (10 + j) (Sum.inl false) = Sum.inl true := by
    have hcl := hgs2_clean j hj
    have h7 := helim.2.2.2.2.2.2.1 j hj (by simpa only [List.length_nil, Nat.add_zero] using hcl.1)
      (by simpa only [List.length_nil, Nat.add_zero] using hcl.2.1)
    simp only [List.length_nil, Nat.add_zero] at h7
    apply h7.2 true
    dsimp only [elimGateM]
    rw [hor]
    rcases h0 with h1 | h2
    · rw [h1, hread_inl (0, true) false hstF_0]; rfl
    · rw [h2, hread_inl (0, true) false hstF_0]
      cases readPin stF (gs2.getD j dB).2.1 with
      | inl ca => cases ca <;> rfl
      | inr _ => rfl
  have hruleB_both_const (j : ℕ) (hj : j < gs2.length)
      (hb1 : ∃ b : Bool, stF.getD (gs2.getD j dB).2.1.1 (Sum.inl false) = Sum.inl b)
      (hb2 : ∃ b : Bool, stF.getD (gs2.getD j dB).2.2.1 (Sum.inl false) = Sum.inl b) :
      ∃ c : Bool, stF.getD (10 + j) (Sum.inl false) = Sum.inl c := by
    have hcl := hgs2_clean j hj
    have h7 := helim.2.2.2.2.2.2.1 j hj (by simpa only [List.length_nil, Nat.add_zero] using hcl.1)
      (by simpa only [List.length_nil, Nat.add_zero] using hcl.2.1)
    simp only [List.length_nil, Nat.add_zero] at h7
    obtain ⟨b1, hb1⟩ := hb1
    obtain ⟨b2, hb2⟩ := hb2
    have hr1 := hread_inl (gs2.getD j dB).2.1 b1 hb1
    have hr2 := hread_inl (gs2.getD j dB).2.2 b2 hb2
    cases hg1 : (gs2.getD j dB).1 with
    | false =>
      cases hca : (b1 ^^ (gs2.getD j dB).2.1.2) with
      | false =>
        exact ⟨b2 ^^ (gs2.getD j dB).2.2.2, h7.2 _ (by dsimp only [elimGateM]; rw [hg1, hr1, hr2, hca]; rfl)⟩
      | true =>
        exact ⟨true, h7.2 true (by dsimp only [elimGateM]; rw [hg1, hr1, hca]; rfl)⟩
    | true =>
      cases hca : (b1 ^^ (gs2.getD j dB).2.1.2) with
      | false =>
        exact ⟨false, h7.2 false (by dsimp only [elimGateM]; rw [hg1, hr1, hca]; rfl)⟩
      | true =>
        exact ⟨b2 ^^ (gs2.getD j dB).2.2.2, h7.2 _ (by dsimp only [elimGateM]; rw [hg1, hr1, hr2, hca]; rfl)⟩
  have count_bool_sum (l : List Bool) : l.count true + l.count false = l.length := by
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp <;> omega
  have filter_le_count_false : ∀ (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (fl : List Bool),
      fl.length = gs.length →
      (∀ j < gs.length, isAny0 (gs.getD j dB) = true → fl.getD j false = false) →
      (gs.filter isAny0).length ≤ fl.count false := by
    intro gs
    induction gs with
    | nil => intro fl _ _; simp
    | cons g rest ih =>
      intro fl hlen hcond
      cases fl with
      | nil => simp at hlen
      | cons b t =>
        have hlen' : t.length = rest.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen
        have hih := ih t hlen' (fun j hj hp => hcond (j + 1) (by simp only [List.length_cons]; omega) hp)
        simp only [List.filter_cons]
        cases hp : isAny0 g with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.count_cons]
          cases b <;> simp <;> omega
        | true =>
          have hb : b = false := hcond 0 (by simp) hp
          subst hb
          simp only [↓reduceIte, List.length_cons, List.count_cons, beq_self_eq_true]
          omega
  have filter_succ_le_count_false : ∀ (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (fl : List Bool) (j0 : ℕ),
      fl.length = gs.length →
      (∀ j < gs.length, isAny0 (gs.getD j dB) = true → fl.getD j false = false) →
      j0 < gs.length → isAny0 (gs.getD j0 dB) = false → fl.getD j0 false = false →
      (gs.filter isAny0).length + 1 ≤ fl.count false := by
    intro gs
    induction gs with
    | nil => intro _ _ _ _ hj0; cases hj0
    | cons g rest ih =>
      intro fl j0 hlen hcond hj0 hp0 hf0
      cases fl with
      | nil => simp at hlen
      | cons b t =>
        have hlen' : t.length = rest.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen
        have hcond' : ∀ j < rest.length, isAny0 (rest.getD j dB) = true → t.getD j false = false :=
          fun j hj hp => hcond (j + 1) (by simp only [List.length_cons]; omega) hp
        cases j0 with
        | zero =>
          change isAny0 g = false at hp0
          change b = false at hf0
          subst hf0
          have hle := filter_le_count_false rest t hlen' hcond'
          simp only [List.filter_cons, hp0, Bool.false_eq_true, ↓reduceIte, List.count_cons, beq_self_eq_true]
          omega
        | succ j0' =>
          have hih := ih t j0' hlen' hcond' (by simp only [List.length_cons] at hj0; omega) hp0 hf0
          simp only [List.filter_cons]
          cases hp : isAny0 g with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, List.count_cons]
            cases b <;> simp <;> omega
          | true =>
            have hb : b = false := hcond 0 (by simp) hp
            subst hb
            simp only [↓reduceIte, List.length_cons, List.count_cons, beq_self_eq_true]
            omega
  have filter_ge_two : ∀ (P : (Bool × (ℕ × Bool) × (ℕ × Bool)) → Bool)
      (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (j1 j2 : ℕ),
      j1 < j2 → j2 < gs.length → P (gs.getD j1 dB) = true → P (gs.getD j2 dB) = true →
      2 ≤ (gs.filter P).length := by
    intro P gs
    induction gs with
    | nil => intro _ _ _ h2; cases h2
    | cons g rest ih =>
      intro j1 j2 h12 h2 hp1 hp2
      simp only [List.filter_cons]
      cases j1 with
      | zero =>
        change P g = true at hp1
        cases j2 with
        | zero => omega
        | succ j2' =>
          have hj2' : j2' < rest.length := by simp only [List.length_cons] at h2; omega
          change P (rest.getD j2' dB) = true at hp2
          have hmem : rest.getD j2' dB ∈ rest.filter P := by
            rw [List.mem_filter, List.getD_eq_getElem _ _ hj2']
            exact ⟨List.getElem_mem hj2', by simpa only [List.getD_eq_getElem _ _ hj2'] using hp2⟩
          have hpos : 0 < (rest.filter P).length := List.length_pos_of_mem hmem
          simp only [hp1, ↓reduceIte, List.length_cons]; omega
      | succ j1' =>
        cases j2 with
        | zero => omega
        | succ j2' =>
          have hih := ih j1' j2' (by omega) (by simp only [List.length_cons] at h2; omega) hp1 hp2
          split_ifs
          · simp only [List.length_cons]; omega
          · omega
  have filter_ge_three : ∀ (gs : List (Bool × (ℕ × Bool) × (ℕ × Bool))) (j1 j2 j3 : ℕ),
      j1 < j2 → j2 < j3 → j3 < gs.length →
      isAny0 (gs.getD j1 dB) = true → isAny0 (gs.getD j2 dB) = true → isAny0 (gs.getD j3 dB) = true →
      3 ≤ (gs.filter isAny0).length := by
    intro gs
    induction gs with
    | nil => intro _ _ _ _ _ h3; cases h3
    | cons g rest ih =>
      intro j1 j2 j3 h12 h23 h3 hp1 hp2 hp3
      simp only [List.filter_cons]
      cases j1 with
      | zero =>
        change isAny0 g = true at hp1
        cases j2 with
        | zero => omega
        | succ j2' =>
          cases j3 with
          | zero => omega
          | succ j3' =>
            have h2 := filter_ge_two isAny0 rest j2' j3' (by omega) (by simp only [List.length_cons] at h3; omega) hp2 hp3
            simp only [hp1, ↓reduceIte, List.length_cons]; omega
      | succ j1' =>
        cases j2 with
        | zero => omega
        | succ j2' =>
          cases j3 with
          | zero => omega
          | succ j3' =>
            have hih := ih j1' j2' j3' (by omega) (by omega) (by simp only [List.length_cons] at h3; omega) hp1 hp2 hp3
            split_ifs
            · simp only [List.length_cons]; omega
            · omega
  have hisAny0_elim (j : ℕ) (hj : j < gs2.length) (hp : isAny0 (gs2.getD j dB) = true) :
      flF.getD j false = false := by
    apply hruleA j hj
    rcases (hisAny0_iff _).mp hp with h1 | h2
    · exact Or.inl ⟨false, by rw [h1]; exact hstF_0⟩
    · exact Or.inr ⟨false, by rw [h2]; exact hstF_0⟩
  have hfl_sum : gs0.length + flF.count false = gs2.length := by
    rw [hgs0_cnt, count_bool_sum, hflF_len]
  have hnAny_le_fl : nAny ≤ flF.count false :=
    filter_le_count_false gs2 flF hflF_len hisAny0_elim
  have hgs2_eq14 : gs2.length = 14 := by omega
  have hnAny_eq2 : nAny = 2 := by omega
  have hnPos_eq1 : nPos = 1 := by omega
  have hnNeg_eq1 : nNeg = 1 := by omega
  have hfl_eq2 : flF.count false = 2 := by omega
  have hno_const_gate (j1 : ℕ) (hj1 : j1 < gs2.length) (hP1 : isAny0 (gs2.getD j1 dB) = true)
      (c1 : Bool) (hc1 : stF.getD (10 + j1) (Sum.inl false) = Sum.inl c1) : False := by
    rcases hgs2_reach j1 hj1 with hu_eq | ⟨j2, hj2, h12in⟩
    · exact hout0_ne_inl c1 (by dsimp only [out0]; rw [← hu_eq]; exact hc1)
    have hcl2 := hgs2_clean j2 hj2
    have hj12 : j1 < j2 := by
      rcases h12in with h1 | h2
      · have := hcl2.1; omega
      · have := hcl2.2.1; omega
    have hfl2 : flF.getD j2 false = false := by
      apply hruleA j2 hj2
      rcases h12in with h1 | h2
      · exact Or.inl ⟨c1, by rw [h1]; exact hc1⟩
      · exact Or.inr ⟨c1, by rw [h2]; exact hc1⟩
    cases hP2 : isAny0 (gs2.getD j2 dB) with
    | false =>
      have h3 := filter_succ_le_count_false gs2 flF j2 hflF_len hisAny0_elim hj2 hP2 hfl2
      change nAny + 1 ≤ flF.count false at h3
      omega
    | true =>
      have h0_2 := (hisAny0_iff _).mp hP2
      have hboth2 : (∃ b : Bool, stF.getD (gs2.getD j2 dB).2.1.1 (Sum.inl false) = Sum.inl b) ∧
          (∃ b : Bool, stF.getD (gs2.getD j2 dB).2.2.1 (Sum.inl false) = Sum.inl b) := by
        rcases h12in with h1 | h2
        · rcases h0_2 with h01 | h02
          · omega
          · exact ⟨⟨c1, by rw [h1]; exact hc1⟩, ⟨false, by rw [h02]; exact hstF_0⟩⟩
        · rcases h0_2 with h01 | h02
          · exact ⟨⟨false, by rw [h01]; exact hstF_0⟩, ⟨c1, by rw [h2]; exact hc1⟩⟩
          · omega
      obtain ⟨c2, hc2⟩ := hruleB_both_const j2 hj2 hboth2.1 hboth2.2
      rcases hgs2_reach j2 hj2 with hu_eq2 | ⟨j3, hj3, h23in⟩
      · exact hout0_ne_inl c2 (by dsimp only [out0]; rw [← hu_eq2]; exact hc2)
      have hcl3 := hgs2_clean j3 hj3
      have hj23 : j2 < j3 := by
        rcases h23in with h1 | h2
        · have := hcl3.1; omega
        · have := hcl3.2.1; omega
      have hfl3 : flF.getD j3 false = false := by
        apply hruleA j3 hj3
        rcases h23in with h1 | h2
        · exact Or.inl ⟨c2, by rw [h1]; exact hc2⟩
        · exact Or.inr ⟨c2, by rw [h2]; exact hc2⟩
      cases hP3 : isAny0 (gs2.getD j3 dB) with
      | false =>
        have h3 := filter_succ_le_count_false gs2 flF j3 hflF_len hisAny0_elim hj3 hP3 hfl3
        change nAny + 1 ≤ flF.count false at h3
        omega
      | true =>
        have h3p := filter_ge_three gs2 j1 j2 j3 hj12 hj23 hj3 hP1 hP2 hP3
        change 3 ≤ nAny at h3p
        omega
  have hex_jp : ∃ jp : Fin 14, isPos0 (gs2.getD jp.val dB) = true := by
    cases hfl : gs2.filter isPos0 with
    | nil =>
      have : nPos = 0 := by dsimp only [nPos]; rw [hfl]; rfl
      omega
    | cons g _ =>
      have hmem : g ∈ gs2.filter isPos0 := by rw [hfl]; exact List.mem_cons_self
      obtain ⟨hmg, hpg⟩ := List.mem_filter.mp hmem
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmg
      refine ⟨⟨j, by omega⟩, ?_⟩
      rw [List.getD_eq_getElem _ _ hj, hget]; exact hpg
  have hex_jn : ∃ jn : Fin 14, isNeg0 (gs2.getD jn.val dB) = true := by
    cases hfl : gs2.filter isNeg0 with
    | nil =>
      have : nNeg = 0 := by dsimp only [nNeg]; rw [hfl]; rfl
      omega
    | cons g _ =>
      have hmem : g ∈ gs2.filter isNeg0 := by rw [hfl]; exact List.mem_cons_self
      obtain ⟨hmg, hng⟩ := List.mem_filter.mp hmem
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmg
      refine ⟨⟨j, by omega⟩, ?_⟩
      rw [List.getD_eq_getElem _ _ hj, hget]; exact hng
  obtain ⟨jp, hjp⟩ := hex_jp
  obtain ⟨jn, hjn⟩ := hex_jn
  have hjp_uniq (j : Fin 14) :
      ((gs2.getD j.val dB).2.1 = (0, false) ∨ (gs2.getD j.val dB).2.2 = (0, false)) ↔ j = jp := by
    constructor
    · intro hj
      have hjp' : isPos0 (gs2.getD j.val dB) = true := (hisPos0_iff _).mpr hj
      by_contra hne
      have hlt_or_gt : j.val < jp.val ∨ jp.val < j.val := by
        have hv : j.val ≠ jp.val := fun h => hne (Fin.ext h)
        omega
      rcases hlt_or_gt with hlt | hgt
      · have h2 := filter_ge_two isPos0 gs2 j.val jp.val hlt (by omega) hjp' hjp
        change 2 ≤ nPos at h2; omega
      · have h2 := filter_ge_two isPos0 gs2 jp.val j.val hgt (by omega) hjp hjp'
        change 2 ≤ nPos at h2; omega
    · rintro rfl; exact (hisPos0_iff _).mp hjp
  have hjn_uniq (j : Fin 14) :
      ((gs2.getD j.val dB).2.1 = (0, true) ∨ (gs2.getD j.val dB).2.2 = (0, true)) ↔ j = jn := by
    constructor
    · intro hj
      have hjn' : isNeg0 (gs2.getD j.val dB) = true := (hisNeg0_iff _).mpr hj
      by_contra hne
      have hlt_or_gt : j.val < jn.val ∨ jn.val < j.val := by
        have hv : j.val ≠ jn.val := fun h => hne (Fin.ext h)
        omega
      rcases hlt_or_gt with hlt | hgt
      · have h2 := filter_ge_two isNeg0 gs2 j.val jn.val hlt (by omega) hjn' hjn
        change 2 ≤ nNeg at h2; omega
      · have h2 := filter_ge_two isNeg0 gs2 jn.val j.val hgt (by omega) hjn hjn'
        change 2 ≤ nNeg at h2; omega
    · rintro rfl; exact (hisNeg0_iff _).mp hjn
  have hjp_ne_jn : jp.val ≠ jn.val := by
    intro heq
    have hcl := hgs2_clean jp.val (by omega)
    have hp := (hisPos0_iff _).mp hjp
    have hn := (hisNeg0_iff _).mp hjn
    rw [← heq] at hn
    rcases hp with hp1 | hp2 <;> rcases hn with hn1 | hn2
    · rw [hp1] at hn1; cases hn1
    · exact hcl.2.2.2.2.2.2.2 ⟨congrArg Prod.fst hp1, congrArg Prod.fst hn2⟩
    · exact hcl.2.2.2.2.2.2.2 ⟨congrArg Prod.fst hn1, congrArg Prod.fst hp2⟩
    · rw [hp2] at hn2; cases hn2
  have hjp_or : (gs2.getD jp.val dB).1 = false := by
    cases hop : (gs2.getD jp.val dB).1 with
    | false => rfl
    | true =>
      exfalso
      have h0 := (hisPos0_iff _).mp hjp
      have hP : isAny0 (gs2.getD jp.val dB) = true := by
        apply (hisAny0_iff _).mpr
        rcases h0 with h1 | h2
        · exact Or.inl (congrArg Prod.fst h1)
        · exact Or.inr (congrArg Prod.fst h2)
      exact hno_const_gate jp.val (by omega) hP false (hruleB_and_false jp.val (by omega) hop h0)
  have hjn_and : (gs2.getD jn.val dB).1 = true := by
    cases hop : (gs2.getD jn.val dB).1 with
    | true => rfl
    | false =>
      exfalso
      have h0 := (hisNeg0_iff _).mp hjn
      have hP : isAny0 (gs2.getD jn.val dB) = true := by
        apply (hisAny0_iff _).mpr
        rcases h0 with h1 | h2
        · exact Or.inl (congrArg Prod.fst h1)
        · exact Or.inr (congrArg Prod.fst h2)
      exact hno_const_gate jn.val (by omega) hP true (hruleB_or_true jn.val (by omega) hop h0)
  let isAnd2 : Fin 14 → Bool := fun j => (gs2.getD j.val dB).1
  let in1_2 : Fin 14 → ℕ × Bool := fun j => (gs2.getD j.val dB).2.1
  let in2_2 : Fin 14 → ℕ × Bool := fun j => (gs2.getD j.val dB).2.2
  let W2 : (Fin 9 → Bool) → ℕ → Bool := fun x k => (runB gs2 (in10 x)).getD k false
  have hW2_in (x : Fin 9 → Bool) (i : Fin 9) : W2 x i.val = x i := by
    dsimp only [W2]
    rw [runB_keep gs2 (in10 x) i.val (by rw [in10_len]; omega), in10_lt x i.val i.isLt]
  have hW2_gate (x : Fin 9 → Bool) (j : Fin 14) :
      have rd : ℕ × Bool → Bool := fun p => W2 x p.1 ^^ p.2
      W2 x (10 + j.val) = if isAnd2 j = true then rd (in1_2 j) && rd (in2_2 j) else rd (in1_2 j) || rd (in2_2 j) := by
    have hj : j.val < gs2.length := by omega
    have hsplit : gs2 = gs2.take j.val ++ [gs2.getD j.val dB] ++ gs2.drop (j.val + 1) := by
      have h1 : gs2 = gs2.take (j.val + 1) ++ gs2.drop (j.val + 1) := (List.take_append_drop (j.val + 1) gs2).symm
      conv_lhs => rw [h1, List.take_succ_eq_append_getElem hj, ← List.getD_eq_getElem gs2 dB hj]
    let w0 := runB (gs2.take j.val) (in10 x)
    have hw0_len : w0.length = 10 + j.val := by
      simp only [w0, runB_len, in10_len, List.length_take]; omega
    have hW2_lt (k : ℕ) (hk : k < 10 + j.val) : W2 x k = w0.getD k false := by
      dsimp only [W2]
      conv_lhs => rw [← List.take_append_drop j.val gs2, runB_append]
      exact runB_keep (gs2.drop j.val) w0 k (by omega)
    have hcl := hgs2_clean j.val hj
    dsimp only [W2]
    conv_lhs => rw [hsplit, runB_append, runB_append]
    have hstep_len : (runB [gs2.getD j.val dB] w0).length = 10 + j.val + 1 := by
      simp only [runB_len, List.length_cons, List.length_nil]; omega
    rw [runB_keep (gs2.drop (j.val + 1)) _ (10 + j.val) (by change 10 + j.val < (runB [gs2.getD j.val dB] w0).length; omega)]
    change (stepB w0 (gs2.getD j.val dB)).getD (10 + j.val) false = _
    dsimp only [stepB]
    rw [← hw0_len, getD_snoc_end]
    dsimp only [isAnd2, in1_2, in2_2]
    rw [← hW2_lt _ hcl.1, ← hW2_lt _ hcl.2.1]
  have hbd2 (j : Fin 14) :
      (in1_2 j).1 < 10 + j.val ∧ (in2_2 j).1 < 10 + j.val ∧ (in1_2 j).1 ≠ 9 ∧ (in2_2 j).1 ≠ 9 := by
    have hcl := hgs2_clean j.val (by omega)
    exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.1⟩
  have hpol2 (j : Fin 14) :
      ((in1_2 j).2 = true → (in1_2 j).1 = 0) ∧ ((in2_2 j).2 = true → (in2_2 j).1 = 0) := by
    have hcl := hgs2_clean j.val (by omega)
    exact ⟨hcl.2.2.2.2.1, hcl.2.2.2.2.2.1⟩
  rcases Nat.lt_or_gt_of_ne hjp_ne_jn with hlt | hgt
  · obtain ⟨x, hx⟩ := hPosFirst isAnd2 in1_2 in2_2 u2 W2 jp jn hlt hbd2 (by omega) hu2_ne9
      hpol2 hjp_uniq hjn_uniq hjp_or hjn_and hW2_in hW2_gate
    exact hx (hu2_val x)
  · obtain ⟨x, hx⟩ := hNegFirst isAnd2 in1_2 in2_2 u2 W2 jp jn hgt hbd2 (by omega) hu2_ne9
      hpol2 hjp_uniq hjn_uniq hjp_or hjn_and hW2_in hW2_gate
    exact hx (hu2_val x)
