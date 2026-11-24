import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_3481 :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro n k G C incident _ _ _ minimal _ output correct
  by_cases empty : n = 0
  · subst n
    have cap := minimal ∅ (by intro u; exact Fin.elim0 u)
    simp at cap
    omega
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have extendsWires (gs : List Gate) (w : List Bool) :
      ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp,rfl⟩
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t,eq,sz⟩ := ih (step w g)
      exact ⟨b :: t, by simp only [List.foldl_cons,eq,step,b,List.append_assoc,List.singleton_append],
        by simp [sz]⟩
  rcases output with input | beyond
  · let u : Fin n := ⟨C.output,input⟩
    let x := fun i : Fin n => decide (i=u ∨ i=u)
    obtain ⟨t,eq,_⟩ := extendsWires C.gates (List.ofFn x)
    have hit : C.eval (List.ofFn x) = true := by
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = true
      rw [eq,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using input),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using input),List.getElem_ofFn]
      simp [x,u]
    exact False.elim ((G.loopless.irrefl u) ((correct u u).mp hit))
  · let u : Fin n := ⟨0,Nat.pos_of_ne_zero empty⟩
    obtain ⟨v,edge⟩ := incident u
    let x := fun i : Fin n => decide (i=u ∨ i=v)
    have hit : C.eval (List.ofFn x) = true := (correct u v).mpr edge
    obtain ⟨t,eq,sz⟩ := extendsWires C.gates (List.ofFn x)
    change n + C.gates.length ≤ C.output at beyond
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = true at hit
    rw [eq,List.getD_eq_default _ _ (by simpa only [List.length_append,List.length_ofFn,sz] using beyond)] at hit
    contradiction
