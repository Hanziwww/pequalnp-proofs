import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3736

def targetC : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 13] }], output := 14 }

def evalFormula (b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  let g0 := b1 || b2
  let g1 := b2 && b3
  let g2 := b0 || g0
  let g3 := b4 && g0
  let g4 := b5 || g3
  let g5 := b6 || g4
  let g6 := g2 && g5
  g1 || g6

def specFormula (b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  (b0 && b5) || (b0 && b6) || (b1 && b4) || (b1 && b5) || (b1 && b6) ||
  (b2 && b3) || (b2 && b4) || (b2 && b5) || (b2 && b6)

lemma eval_eq_formula (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    targetC.eval [b0, b1, b2, b3, b4, b5, b6] = evalFormula b0 b1 b2 b3 b4 b5 b6 := by
  simp [targetC, evalFormula, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval]

lemma formula_eq_spec :
    ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      evalFormula b0 b1 b2 b3 b4 b5 b6 = specFormula b0 b1 b2 b3 b4 b5 b6 := by
  decide

lemma ofFn7 (x : Fin 7 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := rfl

lemma eval_eq_spec (x : Fin 7 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 7 targetC x =
      decide (∃ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true) := by
  have h1 : PEqualNP.MetaComplexity.circuitFun 7 targetC x =
      evalFormula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) := by
    unfold PEqualNP.MetaComplexity.circuitFun
    rw [ofFn7, eval_eq_formula]
  rw [h1, formula_eq_spec]
  simp [specFormula, Bool.or_assoc]

lemma isAO2_target : PEqualNP.TopForm.IsAO2 7 targetC := by
  decide

lemma reread_target :
    ∀ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)),
      PEqualNP.Core.ReadTwiceAt 7 targetC (targetC.output - 7) e.1 e.2 ↔
        e ∈ ([(1, 4), (2, 4)] : List (Fin 7 × Fin 7)) := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end PEqualNP.Outside.L_meta_3736

theorem PEqualNP.Outside.L_meta_3736 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 13] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 8 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(1, 4), (2, 4)] : List (Fin 7 × Fin 7))) := by
  rintro _ rfl
  exact ⟨PEqualNP.Outside.L_meta_3736.isAO2_target, rfl,
    PEqualNP.Outside.L_meta_3736.eval_eq_spec,
    PEqualNP.Outside.L_meta_3736.reread_target⟩
