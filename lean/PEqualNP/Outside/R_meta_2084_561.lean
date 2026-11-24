import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_2084_561
    (bare : ∀ (n : ℕ) (H : (Fin n → Bool) → Bool), (∃ x y,H x=false ∧ H y=true) →
  ∀ A : Finset (Fin n), (∀ x y, (∀ i, i∉A → x i=y i) → H x=H y) → ∀ s : ℕ,
  PEqualNP.MetaComplexity.HasCircuitSize n (fun x => decide (∃ a∈A,x a=true) || H x) s →
  ∃ t, t+A.card ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n H t)
    (factors : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ u, (∃ v,G.Adj u v) → 3 ≤ (G.neighborSet u).ncard) →
  (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
  ∀ f g : (Fin n → Bool) → Bool, (∀ x, (f x && g x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) →
  let active := fun (h : (Fin n → Bool) → Bool) => ∀ u, (∃ v,G.Adj u v) →
    ∃ x, x u=false ∧ h x=false ∧ h (Function.update x u true)=true
  active f ∨ active g)
    (pinCost : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → ∀ r : ℕ,
  ∃ S : Finset (Fin n), S.card ≤ (r+1-n)+1 ∧ ∀ x y : Fin n → Bool, (∀ u∈S, x u=y u) →
    (C.wires (List.ofFn x)).getD r false = (C.wires (List.ofFn y)).getD r false)
    (core :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ u, (∃ v,G.Adj u v) → (G.neighborSet u).ncard=3) →
    (∀ u (w : G.Walk u u), w.IsCycle → 7 ≤ w.length) → (∃ u v,G.Adj u v) →
    (∀ S : Finset (Fin n), (∀ u v,G.Adj u v → u∈S ∨ v∈S) → t ≤ S.card) →
    ∀ C : Circuit, FanInTwo C → circuitFun n C=graphFun G ∅ →
    let vertices := Finset.univ.filter (fun u => ∃ v,G.Adj u v)
    let W := fun (r : ℕ) (x : Fin n → Bool) => (C.wires (List.ofFn x)).getD r false
    let costly := fun r => vertices.card ≤ (r+1-n)+1 ∧
      ∀ u∈vertices, ∃ x : Fin n → Bool, x u=false ∧ W r x=false ∧ W r (Function.update x u true)=true
    (∀ a b : ℕ, (∀ x,(W a x && W b x)=graphFun G ∅ x) → costly a ∨ costly b) →
    3*vertices.card+2*t ≤ 2*C.size+2) :
  ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by

  intro n t G A f deg long iso edge vc spec s provided
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  let H (x : Fin n → Bool) := decide (∃ u v,G.Adj u v ∧ x u=true ∧ x v=true)
  have target : f=(fun x => decide (∃ a∈A,x a=true) || H x) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.or_eq_true,decide_eq_true_eq,H] using spec x
  have invisible (x y : Fin n → Bool) (eq : ∀ i,i∉A → x i=y i) : H x=H y := by
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨u,v,e,hu,hv⟩
      exact ⟨u,v,e,(eq u (iso _ _ e)).symm.trans hu,(eq v (iso _ _ (G.adj_symm e))).symm.trans hv⟩
    · rintro ⟨u,v,e,hu,hv⟩
      exact ⟨u,v,e,(eq u (iso _ _ e)).trans hu,(eq v (iso _ _ (G.adj_symm e))).trans hv⟩
  obtain ⟨i,j,e⟩ := edge
  have varied : ∃ x y,H x=false ∧ H y=true := by
    refine ⟨fun _ => false,fun _ => true,?_,decide_eq_true ⟨i,j,e,rfl,rfl⟩⟩
    simp [H]
  rw [target] at provided
  obtain ⟨left,paid,C,fan,cap,works⟩ := bare n H varied A invisible s provided
  have pure : graphFun G ∅=H := by
    funext x
    change (decide (∃ a∈(∅ : Finset (Fin n)),x a=true) || H x)=H x
    simp
  have comp : circuitFun n C=graphFun G ∅ := by rw [pure];exact funext works
  have cubic (v : Fin n) (used : ∃ w,G.Adj v w) : (G.neighborSet v).ncard=3 := by
    obtain ⟨w,h⟩ := used
    exact deg v (iso _ _ h)
  have least := core n t G cubic long ⟨i,j,e⟩ vc C fan comp
  let vertices := Finset.univ.filter (fun u => ∃ v,G.Adj u v)
  let W (r : ℕ) (x : Fin n → Bool) := (C.wires (List.ofFn x)).getD r false
  have locate (r : ℕ) (essential : ∀ u, (∃ v,G.Adj u v) →
      ∃ x, x u=false ∧ W r x=false ∧ W r (Function.update x u true)=true) :
      vertices.card ≤ (r+1-n)+1 ∧ ∀ u∈vertices, ∃ x, x u=false ∧ W r x=false ∧ W r (Function.update x u true)=true := by
    obtain ⟨S,cost,unchanged⟩ := pinCost n C fan r
    constructor
    · apply (Finset.card_le_card (show vertices ⊆ S from ?_)).trans cost
      intro u hu
      by_contra miss
      obtain ⟨x,_,lo,hi⟩ := essential u (Finset.mem_filter.mp hu).2
      have eq := unchanged x (Function.update x u true) (by
        intro z hz
        exact (Function.update_of_ne (show z≠u from fun e => miss (e ▸ hz)) ..).symm)
      change W r x = W r (Function.update x u true) at eq
      rw [lo,hi] at eq
      contradiction
    · exact fun u hu => essential u (Finset.mem_filter.mp hu).2
  have count := least (by
    intro a b h
    rcases factors n G (fun u q => (cubic u q).ge) long (W a) (W b) h with l|r
    · exact Or.inl (locate a l)
    · exact Or.inr (locate b r))
  change 3*vertices.card+2*t ≤ 2*C.size+2 at count
  have edges : 2*G.edgeSet.ncard=3*vertices.card := by
    rw [←G.coe_edgeFinset,Set.ncard_coe_finset,←G.sum_degrees_eq_twice_card_edges]
    have supported : ∑ v∈vertices,G.degree v = ∑ v : Fin n,G.degree v := by
      apply Finset.sum_subset (Finset.subset_univ vertices)
      intro v _ hv
      by_contra ne
      have used := (G.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero ne)
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,used⟩)
    rw [←supported]
    calc
      ∑ v∈vertices,G.degree v = ∑ _v∈vertices,(3 : ℕ) := by
        apply Finset.sum_congr rfl
        intro v mem
        have d := cubic v (Finset.mem_filter.mp mem).2
        rw [←G.coe_neighborFinset v,Set.ncard_coe_finset] at d
        exact d
      _ = 3*vertices.card := by simp [Nat.mul_comm]
  omega
