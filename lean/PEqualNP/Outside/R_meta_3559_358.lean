import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3559_358
    (complete : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      FormulaSat (enc n s g rows))
    (impossible :
      let p : List ℕ := [6,66,132,160,288,320,1036,1288,1538,1552,1568]
      let n : List ℕ := [562,628,720,788,914,1066,1128,1162,1604,1736,1796,1920]
      ¬ FormulaSat (enc 11 13 (fun r => p.contains r) (p ++ n)))
    (withNot : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → 1 ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.false]) x2.gates → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False := by
  dsimp only
  intro C fan small correct
  by_cases hnot : C.gates.countP (fun g => g.op.eval [false]) = 0
  · have mono : Monotone2 C := by
      intro a ha
      have hf := fan a ha
      have hz : ¬ (a.op.eval [false] = true) := (List.countP_eq_zero.mp hnot) a ha
      refine ⟨?_, hf.2⟩
      have hop := hf.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rw [h] at hz
        exact absurd rfl hz
    let target := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
    let p : List ℕ := [6,66,132,160,288,320,1036,1288,1538,1552,1568]
    let n : List ℕ := [562,628,720,788,914,1066,1128,1162,1604,1736,1796,1920]
    let pw : List (ℕ × ℕ) := [(6,6),(66,66),(132,132),(160,160),(288,288),(320,320),(1036,12),(1288,264),(1538,3),(1552,17),(1568,33),(562,50),(628,116),(720,208),(788,276),(914,402),(1066,42),(1128,104),(1162,138),(1604,69),(1736,201),(1796,261),(1920,385)]
    let wit (r : ℕ) : ℕ := (pw.lookup r).getD 0
    let bare (r : ℕ) := List.ofFn fun i : Fin 11 => r.testBit i.val
    let bits (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i.val
    have bounded : ∀ r ∈ p ++ n, r < 2^11 := by
      intro r hr
      exact of_decide_eq_true (List.all_eq_true.mp (show (p ++ n).all (fun m => decide (m < 2^11)) = true from by decide +kernel) r hr)
    have check : ∀ r ∈ p ++ n, bare r = List.ofFn (Function.update (bits (wit r)) 0 false) ++
        [bits (wit r) 0 || bits (wit r) 4, bits (wit r) 0 || bits (wit r) 3] ∧
        target (bits (wit r)) = p.contains r := by
      intro r hr
      exact of_decide_eq_true (List.all_eq_true.mp (show (p ++ n).all (fun r => decide
        (bare r = List.ofFn (Function.update (bits (wit r)) 0 false) ++
          [bits (wit r) 0 || bits (wit r) 4, bits (wit r) 0 || bits (wit r) 3] ∧
          target (bits (wit r)) = p.contains r)) = true from by decide +kernel) r hr)
    apply impossible
    apply complete 11 13 (fun r => p.contains r) (p ++ n) C bounded mono small
    intro r hr
    change C.eval (bare r) = p.contains r
    obtain ⟨e, t⟩ := check r hr
    rw [e]
    exact (correct (bits (wit r))).trans t
  · exact withNot C fan small correct (Nat.pos_of_ne_zero hnot)
