import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_3572_648
    (assemble : ∀ (q N : ℕ) (s : Fin N → Finset (Fin N)), 1 ≤ q → (∀ l,(s l).card=q+1) →
  (∀ p r : Fin N,p≠r → ∃! l,p∈s l ∧ r∈s l) → ∀ k : ℕ,
  (∃ L : List (Finset (Fin N)), L.length ≤ k ∧ (∀ l,s l∈L) ∧
    ∀ i S, L[i]?=some S → ∃ A B, S=A∪B ∧ (A.card≤1 ∨ A∈L.take i) ∧ (B.card≤1 ∨ B∈L.take i)) ↔ N*q ≤ k)
    (triple : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    2 ≤ q → N = q^2+q+1 →
    (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
    (∀ p r : Fin N, p≠r → ∃! l : Fin N, I p l ∧ I r l) →
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) = true) →
    (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C x = false) → 3*N ≤ C.size)
    (witness : ∀ (q N : ℕ) (s : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  2 ≤ q → 0<N → (∀ l,(s l).card=q+1) → (∀ p r : Fin N,p≠r → ∃! l,p∈s l ∧ r∈s l) →
  PEqualNP.MetaComplexity.Monotone2 C →
  (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
    PEqualNP.MetaComplexity.circuitFun (N+N) C x=decide (∃ p l,p∈s l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true)) →
  N*q ≤ C.size ∨ ∃ (i : Fin C.size) (x : Fin (N+N) → Bool),
    Fintype.card {u : Fin (N+N) // x u=true} ≤ 2 ∧ (C.gates.get i).op=PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (C.wires (List.ofFn x)).getD (N+N+i.val) false=true ∧
    ¬∃ p l,p∈s l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true)
    (large : ∀ (q N : ℕ) (s : Fin N → Finset (Fin N)),
    301 ≤ q → N=q^2+q+1 → (∀ l,(s l).card=q+1) → (∀ p r : Fin N,p≠r → ∃! l,p∈s l ∧ r∈s l) →
    let edge := fun x : Fin (N+N) → Bool => ∃ p l,p∈s l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true
    let valid := fun C : Circuit => Monotone2 C ∧
      ∀ x, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q → circuitFun (N+N) C x=decide (edge x)
    ∀ C, valid C → (∀ D,valid D → C.size ≤ D.size) →
    (∃ (i : Fin C.size) (x : Fin (N+N) → Bool), Fintype.card {u : Fin (N+N) // x u=true}≤2 ∧
      (C.gates.get i).op=.and ∧ (C.wires (List.ofFn x)).getD (N+N+i.val) false=true ∧ ¬edge x) →
    N*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) → ∃ (x11 : List (Finset (Fin x2))), x11.length ≤ (100 : ℕ) * x4.size ∧ (∀ (x12 : Fin x2), x3 x12 ∈ x11) ∧ ∀ (x12 : ℕ) (x13 : Finset (Fin x2)), x11[x12]? = Option.some x13 → ∃ (x15 : Finset (Fin x2)) (x16 : Finset (Fin x2)), x13 = x15 ∪ x16 ∧ (x15.card ≤ (1 : ℕ) ∨ x15 ∈ List.take x12 x11) ∧ (x16.card ≤ (1 : ℕ) ∨ x16 ∈ List.take x12 x11) := by

  intro q N lines C hq order width unique mono correct
  classical
  have nq : 0<N := by omega
  have positive (p l : Fin N) (on : p∈lines l) : circuitFun (N+N) C
      (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true := by
    let x (i : Fin (N+N)) := decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)
    have distinct (a b : Fin N) : Fin.castAdd N a ≠ Fin.natAdd N b := by
      intro e
      have same := congrArg (fun t : Fin (N+N) => t.val) e
      change a.val=N+b.val at same
      omega
    have sparse : Fintype.card {r : Fin N // x (Fin.natAdd N r)=true}≤q := by
      rw [Fintype.card_subtype]
      have sub : (Finset.univ.filter (fun r : Fin N => x (Fin.natAdd N r)=true)) ⊆ {l} := by
        intro r mem
        have hit := of_decide_eq_true (Finset.mem_filter.mp mem).2
        rcases hit with wrong|eq
        · exact False.elim (distinct p r wrong.symm)
        · have h:=congrArg (fun t : Fin (N+N) => t.val) eq
          change N+r.val=N+l.val at h
          exact Finset.mem_singleton.mpr (Fin.ext (Nat.add_left_cancel h))
      have bound:=Finset.card_le_card sub
      rw [Finset.card_singleton] at bound
      omega
    have hit : ∃ a b,a∈lines b ∧ x (Fin.castAdd N a)=true ∧ x (Fin.natAdd N b)=true :=
      ⟨p,l,on,by simp [x],by simp [x]⟩
    exact (correct x sparse).trans (decide_eq_true hit)
  have full : N*q ≤ 100*C.size := by
    by_cases small : q≤300
    · have enough := triple q N (fun p l => p∈lines l) C (by omega) order (by intro l;simpa using width l)
        unique mono positive (fun x count no => (correct x count).trans (decide_eq_false no))
      have scale := Nat.mul_le_mul_left N small
      omega
    · let valid (D : Circuit) := Monotone2 D ∧
        ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
          circuitFun (N+N) D x=decide (∃ p l,p∈lines l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true)
      let witnessSize (k : ℕ) := ∃ D : Circuit, valid D ∧ D.size=k
      have someSize : ∃ k,witnessSize k := ⟨C.size,C,⟨mono,correct⟩,rfl⟩
      obtain ⟨D,good,price⟩ := Nat.find_spec someSize
      have least (B : Circuit) (hb : valid B) : D.size≤B.size := by
        rw [price]
        exact Nat.find_min' someSize (show witnessSize B.size from ⟨B,hb,rfl⟩)
      have maxCost := least C ⟨mono,correct⟩
      rcases witness q N lines D (by omega) nq width unique good.1 good.2 with big|bad
      · omega
      · have h := large q N lines (by omega) order width unique D good least bad
        omega
  exact (assemble q N lines (by omega) width unique (100*C.size)).mpr full
