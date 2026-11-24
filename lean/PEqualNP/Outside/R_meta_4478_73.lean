import Mathlib
import PEqualNP.Defs

-- The first step covers all graphs with at most one more edge than active endpoints.
-- For a denser core, the second step removes one edge and all edges lost on peeling leaves.
-- Its price includes both the number of edges and the minimum vertex cover size.
open Classical in
theorem PEqualNP.Outside.R_meta_4478_73
    (hthin : ∀ m n : ℕ,
      let d := fun (v : Fin (m+n)) (e : Fin m × Fin n) => Fin.castAdd n e.1=v ∨ Fin.natAdd m e.2=v
      let good := fun F : Finset (Fin m × Fin n) => ∀ v, (F.filter (d v)).card ≠ 1
      let sq := fun F : Finset (Fin m × Fin n) => ∀ a b u v, a≠b → u≠v → ¬((a,u)∈F ∧ (a,v)∈F ∧ (b,u)∈F ∧ (b,v)∈F)
      let rep := fun (F : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.TopForm.IsAO2 (m+n) C ∧ ∀ x : Fin (m+n) → Bool, PEqualNP.MetaComplexity.circuitFun (m+n) C x =
          decide (∃ e∈F, x (Fin.castAdd n e.1)=true ∧ x (Fin.natAdd m e.2)=true)
      let cov := fun (F : Finset (Fin m × Fin n)) (S : Finset (Fin (m+n))) => ∀ e∈F, Fin.castAdd n e.1∈S ∨ Fin.natAdd m e.2∈S
      let active := fun F : Finset (Fin m × Fin n) => (F.image Prod.fst).card+(F.image Prod.snd).card
      ∀ E C, sq E → rep E C → good E → E.card ≤ active E+1 →
        ∃ S, cov E S ∧ E.card+S.card ≤ C.size+1)
    (hpeel : ∀ m n : ℕ,
      let d := fun (v : Fin (m+n)) (e : Fin m × Fin n) => Fin.castAdd n e.1=v ∨ Fin.natAdd m e.2=v
      let good := fun F : Finset (Fin m × Fin n) => ∀ v, (F.filter (d v)).card ≠ 1
      let sq := fun F : Finset (Fin m × Fin n) => ∀ a b u v, a≠b → u≠v → ¬((a,u)∈F ∧ (a,v)∈F ∧ (b,u)∈F ∧ (b,v)∈F)
      let rep := fun (F : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.TopForm.IsAO2 (m+n) C ∧ ∀ x : Fin (m+n) → Bool, PEqualNP.MetaComplexity.circuitFun (m+n) C x =
          decide (∃ e∈F, x (Fin.castAdd n e.1)=true ∧ x (Fin.natAdd m e.2)=true)
      let cov := fun (F : Finset (Fin m × Fin n)) (S : Finset (Fin (m+n))) => ∀ e∈F, Fin.castAdd n e.1∈S ∨ Fin.natAdd m e.2∈S
      let price := fun F : Finset (Fin m × Fin n) => F.card + sInf {k : ℕ | ∃ S, cov F S ∧ S.card=k}
      let core := fun F : Finset (Fin m × Fin n) => (F.powerset.filter good).biUnion id
      ∀ E C, sq E → rep E C → good E → (E.image Prod.fst).card+(E.image Prod.snd).card+1 < E.card →
        ∃ e∈E, ∃ D, rep (core (E.erase e)) D ∧ price E+D.size ≤ price (core (E.erase e))+C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → x6 x3 x4 → (∀ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card ≠ (1 : ℕ)) → ∃ (x10 : Finset (Fin (x1 + x2))), (∀ x11 ∈ x3, Fin.castAdd x2 x11.1 ∈ x10 ∨ Fin.natAdd x1 x11.2 ∈ x10) ∧ x3.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n
  let d := fun (v : Fin (m+n)) (e : Fin m × Fin n) => Fin.castAdd n e.1=v ∨ Fin.natAdd m e.2=v
  let good := fun F : Finset (Fin m × Fin n) => ∀ v, (F.filter (d v)).card ≠ 1
  let sq := fun F : Finset (Fin m × Fin n) => ∀ a b u v, a≠b → u≠v → ¬((a,u)∈F ∧ (a,v)∈F ∧ (b,u)∈F ∧ (b,v)∈F)
  let rep := fun (F : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.TopForm.IsAO2 (m+n) C ∧ ∀ x : Fin (m+n) → Bool, PEqualNP.MetaComplexity.circuitFun (m+n) C x =
          decide (∃ e∈F, x (Fin.castAdd n e.1)=true ∧ x (Fin.natAdd m e.2)=true)
  let cov := fun (F : Finset (Fin m × Fin n)) (S : Finset (Fin (m+n))) => ∀ e∈F, Fin.castAdd n e.1∈S ∨ Fin.natAdd m e.2∈S
  let price := fun F : Finset (Fin m × Fin n) => F.card + sInf {k : ℕ | ∃ S, cov F S ∧ S.card=k}
  let core := fun F : Finset (Fin m × Fin n) => (F.powerset.filter good).biUnion id
  let active := fun F : Finset (Fin m × Fin n) => (F.image Prod.fst).card+(F.image Prod.snd).card
  change ∀ (E : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    sq E → rep E C → good E → ∃ S, cov E S ∧ E.card+S.card ≤ C.size+1
  have core_sub (H : Finset (Fin m × Fin n)) : core H ⊆ H := by
    intro e he
    obtain ⟨J,hJ,h⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hJ).1) h
  have core_good (H : Finset (Fin m × Fin n)) : good (core H) := by
    intro v one
    have pos : 0 < ((core H).filter (d v)).card := by omega
    obtain ⟨e,he⟩ := Finset.card_pos.mp pos
    obtain ⟨ein,touch⟩ := Finset.mem_filter.mp he
    obtain ⟨J,hJ,h⟩ := Finset.mem_biUnion.mp ein
    have sub : J ⊆ core H := fun a ha => Finset.mem_biUnion.mpr ⟨J,hJ,ha⟩
    have small := Finset.card_le_card (Finset.filter_subset_filter (d v) sub)
    have big : 0 < (J.filter (d v)).card := Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨h,touch⟩⟩
    exact (Finset.mem_filter.mp hJ).2 v (by omega)
  have square_sub {H E : Finset (Fin m × Fin n)} (sub : H ⊆ E) (h : sq E) : sq H := by
    rintro a b u v ab uv ⟨h1,h2,h3,h4⟩
    exact h a b u v ab uv ⟨sub h1,sub h2,sub h3,sub h4⟩
  have costs (E : Finset (Fin m × Fin n)) :
      ∃ S, cov E S ∧ E.card+S.card=price E := by
    let K := {k : ℕ | ∃ S, cov E S ∧ S.card=k}
    have ne : K.Nonempty := ⟨(Finset.univ : Finset (Fin (m+n))).card,Finset.univ,
      (fun _ _ => Or.inl (Finset.mem_univ _)),rfl⟩
    obtain ⟨S,hs,e⟩ := (show ∃ S, cov E S ∧ S.card=sInf K from Nat.sInf_mem ne)
    exact ⟨S,hs,congrArg (E.card+·) e⟩
  have lowerCost (E : Finset (Fin m × Fin n)) {S} (hs : cov E S) : price E ≤ E.card+S.card := by
    apply Nat.add_le_add_left
    exact Nat.sInf_le (show S.card ∈ {k : ℕ | ∃ T, cov E T ∧ T.card=k} from ⟨S,hs,rfl⟩)
  have solve (k : ℕ) : ∀ (E : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      E.card=k → sq E → rep E C → good E → price E ≤ C.size+1 := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro E C size square realizes noLeaves
      by_cases bounded : E.card ≤ active E+1
      · obtain ⟨S,hS,budget⟩ := hthin m n E C square realizes noLeaves bounded
        exact (lowerCost E hS).trans budget
      · obtain ⟨e,mem,D,descends,drop⟩ := hpeel m n E C square realizes noLeaves (lt_of_not_ge bounded)
        let F := core (E.erase e)
        have sub : F ⊆ E.erase e := core_sub _
        have less : F.card<k := by
          have h1 := Finset.card_le_card sub
          have h2 := Finset.card_erase_lt_of_mem mem
          omega
        have small := ih F.card less F D rfl (square_sub (sub.trans (Finset.erase_subset _ _)) square)
          descends (core_good _)
        change price E+D.size ≤ price F+C.size at drop
        omega
  intro E C sqE ok coreE
  obtain ⟨S,covers,paid⟩ := costs E
  exact ⟨S,covers,paid.le.trans (solve E.card E C rfl sqE ok coreE)⟩
