import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3122_1
    (total : ¬ HasCircuitSize 9 (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) 14)
    (binary : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    (finite : ∀ a b : Fin 11, a ≤ b → ∀ gs : List Gate, gs.length = 13 →
      FanInTwo ⟨gs, 23⟩ → (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 24) →
      gs.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) ≤ 1 →
      ∃ x : Fin 9 → Bool, let u := List.ofFn x ++ [!x 0]
        (Circuit.mk gs 23).eval (u ++ [u.getD a.val false || u.getD b.val false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins hlen C hfan hsize _
  by_contra! correct
  let f : (Fin 9 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let seed := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0]
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let first : Gate := ⟨.not, [0]⟩
  let second : Gate := ⟨.or, pins⟩
  let full : List Gate → ℕ → Circuit := fun gs o => ⟨first :: second :: gs, o⟩
  have legal (gs : List Gate) (o : ℕ) (hs : FanInTwo ⟨gs, o⟩) :
      FanInTwo (full gs o) := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [first]
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [second], hlen⟩
    exact hs g hg
  have seed_eq (x : Fin 9 → Bool) : step (List.ofFn x) first = seed x := by
    change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = seed x
    simp [seed, List.getD_eq_getElem?_getD]
  let beginW := fun (x : Fin 9 → Bool) => step (seed x) second
  have agrees (x : Fin 9 → Bool) : C.eval (beginW x) = f x := by
    exact not_not.mp (correct x)
  have full_eval (gs : List Gate) (o : ℕ) (x : Fin 9 → Bool) :
      (full gs o).eval (List.ofFn x) = (Circuit.mk gs o).eval (beginW x) := by
    change (gs.foldl step (step (step (List.ofFn x) first) second)).getD o false = _
    rw [seed_eq]
    rfl
  have same (x : Fin 9 → Bool) : (full C.gates C.output).eval (List.ofFn x) = f x :=
    (full_eval _ _ x).trans (agrees x)
  have len : C.gates.length = 13 := by
    change C.gates.length ≤ 13 at hsize
    by_contra hn
    apply total
    exact ⟨_, legal _ _ hfan, (by change (first :: second :: C.gates).length ≤ 14; simp; omega), same⟩
  let isNot : Gate → Bool := fun g => GateOp.rec false false true (fun _ => false) false g.op
  have paid := binary _ (legal _ _ hfan) same
  have negCount : C.gates.countP isNot ≤ 1 := by
    let isPaid : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
    have split (gs : List Gate) : gs.countP isNot + gs.countP isPaid = gs.length := by
      induction gs with
      | nil => rfl
      | cons g gs ih =>
        cases g with | mk op ins => cases op <;> simp_all [isNot, isPaid] <;> omega
    change 13 ≤ (first :: second :: C.gates).countP isPaid at paid
    simp [isPaid, first, second] at paid
    have balance := split C.gates
    dsimp only [isPaid] at balance
    omega
  have startLen (x : Fin 9 → Bool) : (beginW x).length = 11 := by simp [beginW, step, seed]
  have runLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have out : C.output = 23 := by
    by_contra different
    have nonempty : C.gates ≠ [] := fun h => by simp [h] at len
    obtain ⟨gs, last, parts⟩ : ∃ gs last, C.gates = gs ++ [last] :=
      ⟨_, _, (List.dropLast_concat_getLast nonempty).symm⟩
    have gl : gs.length = 12 := by simp [parts] at len; omega
    have shortFan : FanInTwo ⟨gs, C.output⟩ := by
      intro g hg
      apply hfan g
      simp [parts, hg]
    apply total
    refine ⟨_, legal _ _ shortFan, (by change (first :: second :: gs).length ≤ 14; simp [gl]), ?_⟩
    intro x
    rw [full_eval]
    have hn : (gs.foldl step (beginW x)).length = 23 := by rw [runLen, startLen, gl]
    have eq := agrees x
    change (C.gates.foldl step (beginW x)).getD C.output false = _ at eq
    rw [parts, List.foldl_append] at eq
    change ((gs.foldl step (beginW x)) ++ [_]).getD C.output false = _ at eq
    change (gs.foldl step (beginW x)).getD C.output false = _
    by_cases lt : C.output < 23
    · rwa [List.getD_append _ _ _ _ (by omega)] at eq
    · rw [List.getD_eq_default _ _ (by omega)]
      rw [List.getD_eq_default _ _ (by simp [hn]; omega)] at eq
      exact eq
  let clip := fun i : ℕ => min i 24
  let tidy := fun (g : Gate) => Gate.mk g.op (g.inputs.map clip)
  have sameRead (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
      w.getD (clip i) false = w.getD i false := by
    by_cases h : i ≤ 24
    · simp [clip, min_eq_left h]
    · change w.getD (min i 24) false = w.getD i false
      rw [min_eq_right (by omega : 24 ≤ i), List.getD_eq_default w false hw,
        List.getD_eq_default w false (by omega : w.length ≤ i)]
  have tidyRun (gs : List Gate) (w : List Bool) (room : w.length + gs.length ≤ 24) :
      (gs.map tidy).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have h := sameRead w (by simp at room; omega)
      have eq : step w (tidy g) = step w g := by
        simp only [step, tidy, List.map_map, Function.comp_def, h]
      simp only [List.map_cons, List.foldl_cons, eq]
      apply ih
      simp [step] at *
      omega
  let gs := C.gates.map tidy
  have tidyFan : FanInTwo ⟨gs, 23⟩ := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    simpa [tidy] using hfan q hq
  have bounded : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 24 := by
    intro g hg i hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact Nat.min_le_right _ _
  have count : gs.countP isNot ≤ 1 := by
    simpa only [gs, List.countP_map, Function.comp_def, tidy] using negCount
  have form (w : List Bool) (hw : w.length = 10) (i : ℕ) :
      w.getD (min i 10) false = w.getD i false := by
    by_cases h : i ≤ 10
    · simp [min_eq_left h]
    · rw [min_eq_right (by omega : 10 ≤ i), List.getD_eq_default w false (by omega : w.length ≤ 10),
        List.getD_eq_default w false (by omega : w.length ≤ i)]
  have pair : ∃ a b : Fin 11, ∀ w : List Bool, w.length = 10 →
      GateOp.or.eval (pins.map fun i => w.getD i false) =
        (w.getD a.val false || w.getD b.val false) := by
    let pin := fun i : ℕ => (⟨min i 10, by have := Nat.min_le_right i 10; omega⟩ : Fin 11)
    cases pins with
    | nil =>
      refine ⟨10, 10, ?_⟩
      intro w hw
      change false = (w.getD 10 false || w.getD 10 false)
      rw [List.getD_eq_default w false (by omega : w.length ≤ 10)]
      rfl
    | cons i tail =>
      cases tail with
      | nil =>
        exact ⟨pin i, pin i, fun w hw => by
          change [w.getD i false].any id = (w.getD (min i 10) false || w.getD (min i 10) false)
          simp only [form w hw, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]⟩
      | cons j tail =>
        cases tail with
        | nil => exact ⟨pin i, pin j, fun w hw => by
            change [w.getD i false, w.getD j false].any id =
              (w.getD (min i 10) false || w.getD (min j 10) false)
            simp only [form w hw, List.any_cons, List.any_nil, id_eq, Bool.or_false]⟩
        | cons k tail => simp at hlen
  obtain ⟨p, q, sem⟩ := pair
  let a := min p q
  let b := max p q
  have ord : a ≤ b := le_trans (min_le_left _ _) (le_max_left _ _)
  have sorted (w : List Bool) (hw : w.length = 10) :
      GateOp.or.eval (pins.map fun i => w.getD i false) =
          (w.getD a.val false || w.getD b.val false) := by
    rw [sem w hw]
    rcases le_total p q with h | h
    · simp [a, b, min_eq_left h, max_eq_right h]
    · simp [a, b, min_eq_right h, max_eq_left h, Bool.or_comm]
  obtain ⟨x, bad⟩ := finite a b ord gs (by simp [gs, len]) tidyFan bounded count
  apply bad
  have hw : (seed x).length = 10 := by simp [seed]
  change (gs.foldl step (seed x ++ [_])).getD 23 false = f x
  rw [← sorted (seed x) hw]
  change ((C.gates.map tidy).foldl step (beginW x)).getD 23 false = f x
  rw [tidyRun _ _ (by rw [startLen, len]), ← out]
  exact agrees x
