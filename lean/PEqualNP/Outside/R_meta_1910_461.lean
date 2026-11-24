import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1910_461
    (complete : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      FormulaSat (enc n s g rows))
    (impossible :
      let p : List ℕ := [3,6,12,536,529,33,578,132,264,160,832,288]
      let n : List ℕ := [42,562,581,616,628,138,713,720,261,788,385,914]
      ¬ FormulaSat (enc 10 14 (fun r => p.contains r) (p ++ n)))
    (withNot : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           1 ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.false]) x1.gates → (16 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  intro C fan first correct readers
  by_cases hnot : C.gates.countP (fun g => g.op.eval [false]) = 0
  · by_contra hsmall
    have sizeLimit : C.size ≤ 15 := by omega
    let target := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
    have extend (gs : List Gate) (w : List Bool) :
        ∃ extra, run gs w = w ++ extra ∧ extra.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp [run], rfl⟩
      | cons g rest ih =>
        obtain ⟨extra, heq, hlen⟩ := ih (step w g)
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra, ?_, by simp [hlen]⟩
        change run rest (step w g) = _
        rw [heq]
        simp [step, List.append_assoc]
    obtain ⟨gs, out⟩ := C
    cases gs with
    | nil =>
      have h := first (fun _ => true)
      change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
      rw [List.getD_eq_default _ false (by simp)] at h
      contradiction
    | cons g rest =>
      have firstValue (x : Fin 9 → Bool) :
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
        let w := List.ofFn x
        let value := g.op.eval (g.inputs.map fun i => w.getD i false)
        obtain ⟨extra, heq, _⟩ := extend rest (w ++ [value])
        have h := first x
        change (run rest (w ++ [value])).getD 9 false = _ at h
        rw [heq, List.getD_append _ _ false 9 (by simp [w]),
          List.getD_append_right w [value] false 9 (by simp [w])] at h
        simpa [value, w] using h
      have computes (x : Fin 9 → Bool) :
          (run rest (List.ofFn x ++ [x 4 || x 6])).getD out false = target x := by
        have h := congrFun correct x
        change (run rest (List.ofFn x ++
          [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD out false = target x at h
        rw [firstValue] at h
        exact h
      let D : Circuit := ⟨rest, out⟩
      have mono : Monotone2 D := by
        intro a ha
        have hf := fan a (List.mem_cons_of_mem _ ha)
        have hz : ¬ (a.op.eval [false] = true) := (List.countP_eq_zero.mp hnot) a (List.mem_cons_of_mem _ ha)
        refine ⟨?_, hf.2⟩
        have hop := hf.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [h] at hz
          exact absurd rfl hz
      have small : D.size ≤ 14 := by
        change (g :: rest).length ≤ 15 at sizeLimit
        change rest.length ≤ 14
        simp only [List.length_cons] at sizeLimit
        omega
      let p : List ℕ := [3,6,12,536,529,33,578,132,264,160,832,288]
      let n : List ℕ := [42,562,581,616,628,138,713,720,261,788,385,914]
      let bare (r : ℕ) := List.ofFn fun i : Fin 10 => r.testBit i.val
      let bits (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i.val
      have bounded : ∀ r ∈ p ++ n, r < 2^10 := by
        intro r hr
        exact of_decide_eq_true (List.all_eq_true.mp (show (p ++ n).all (fun m => decide (m < 2^10)) = true from by decide +kernel) r hr)
      have checkPos : ∀ m ∈ p, bare m = List.ofFn (bits (m % 512)) ++ [bits (m % 512) 4 || bits (m % 512) 6] ∧
          target (bits (m % 512)) = true := by
        intro m hm
        exact of_decide_eq_true (List.all_eq_true.mp (show p.all (fun m => decide
          (bare m = List.ofFn (bits (m % 512)) ++ [bits (m % 512) 4 || bits (m % 512) 6] ∧
            target (bits (m % 512)) = true)) = true from by decide +kernel) m hm)
      have checkNeg : ∀ m ∈ n, bare m = List.ofFn (bits (m % 512)) ++ [bits (m % 512) 4 || bits (m % 512) 6] ∧
          target (bits (m % 512)) = false ∧ p.contains m = false := by
        intro m hm
        exact of_decide_eq_true (List.all_eq_true.mp (show n.all (fun m => decide
          (bare m = List.ofFn (bits (m % 512)) ++ [bits (m % 512) 4 || bits (m % 512) 6] ∧
            target (bits (m % 512)) = false ∧ p.contains m = false)) = true from by decide +kernel) m hm)
      apply impossible
      apply complete 10 14 (fun r => p.contains r) (p ++ n) D bounded mono small
      intro r hr
      change D.eval (bare r) = p.contains r
      rcases List.mem_append.mp hr with inPos | inNeg
      · obtain ⟨e, t⟩ := checkPos r inPos
        rw [e, List.contains_iff_mem.mpr inPos]
        exact (computes (bits (r % 512))).trans t
      · obtain ⟨e, t, off⟩ := checkNeg r inNeg
        rw [e, off]
        exact (computes (bits (r % 512))).trans t
  · exact withNot C fan first correct readers (Nat.pos_of_ne_zero hnot)
