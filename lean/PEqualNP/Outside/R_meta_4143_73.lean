import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Compute all three stars on an affine line. The residual can reuse six of their OR wires.
-- The 177-row table consists of 24 incident pairs and 153 maximal projected negatives.
-- The monotonicity induction follows the checked L_meta_1018 wire argument.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 22000000 in
theorem PEqualNP.Outside.R_meta_4143_73 :
  (∀ (P B : Circuit) (ids : List ℕ), Monotone2 P → Monotone2 B →
      ids.length ≤ 21+P.size → (∀ i ∈ ids, i < 21+P.size) → P.output < 21+P.size →
      B.output < ids.length+B.size →
      ∃ C : Circuit, Monotone2 C ∧ C.output < 21+C.size ∧ C.size = P.size+B.size+1 ∧
        ∀ x : List Bool, x.length = 21 → C.eval x =
          (P.eval x || B.eval (ids.map (fun i => (P.wires x).getD i false)))) →
  (∃ B : Circuit, Monotone2 B ∧ B.output < 23+B.size ∧ B.size ≤ 28 ∧
      ∀ j : Fin 177, B.eval (List.ofFn (fun i : Fin 23 => (24749718305498079621930527097498335442137279197626496029518248530172548797799224936072389485319537874714400543987346478869538328791042887897385431137650442121822125453581186143859513375427926096064882457539601859103283634154870303441993891390777986565919979175643416909449670950602159920178122801498454473219710784461778908339632453414244846348181503388326094920449037569956739384615695692720503057770755230646148445727895136269660718524009416891565235091620606408034846277441353553975027826559303807553151358216376089654963079479931175226745585581562067598134151238135934849740079126516116677933946731502218915207289099308788402556729120305016560022100387866781639473099223933714381775405707511715333472755765181285920998524596012045223019012856141229902566222499567409788571736535001044850045948519104417478168393581350093797594880276133575874627892204332253929210473323445576379226850372331156161802793413664305658512354074720882584860128250472586793504339970941661096119594122814361259934146331947574351489974766143078959438390575442253091517020141828254449237069821598701294883930803486712204568421125103817734495546200995830552389906655204687936231428280130610824327108107928367837470465918461767830348125370243594190913 : ℕ).testBit (23*j.val+i.val))) =
        decide (j.val < 24)) →
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); have x4 : List (Fin (26 : ℕ)) := List.filter (fun (x4 : Fin (26 : ℕ)) => Decidable.decide (↑x4 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.output < (21 : ℕ) + x5.size ∧ x5.size ≤ (43 : ℕ) ∧ (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∉ x1 → x6 - x7 ∈ x1 → x5.eval (List.map (fun (x10 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) x4) = Bool.true) ∧ ∀ x6 ∈ x2, ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool), x5.eval (List.map (x3 x6 x8 x10 x11) x4) = Bool.false := by
  intro routing core
  let D : Finset (Fin 13) := {0,1,3,9}
  let reps : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
  let mults : List (Fin 13) := [1,3,9]
  let inp := (List.finRange 26).filter (fun k => k.val ∉ ([0,1,3,9,13] : List ℕ))
  let pair := fun (p l : Fin 13) (i : Fin 26) => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)
  let row := fun (z : ℕ × ℕ) (m t : Fin 13) (d : Bool) =>
    let bit := fun (a b : ℕ) (i : Fin 13) => if d = true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
    Fin.append (bit z.1 z.2) (bit z.2 z.1)
  let g := fun (op : GateOp) (i j : ℕ) => (⟨op,[i,j]⟩ : Gate)
  let P : Circuit := ⟨[g .or 10 14, g .or 21 20, g .or 22 9, g .and 0 23, g .or 11 12, g .or 25 16, g .or 26 9, g .and 1 27, g .or 15 17, g .or 29 18, g .or 30 9, g .and 6 31, g .or 24 28, g .or 33 32],34⟩
  let ids : List ℕ := [2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 25, 26, 29, 30]
  let feats := fun (x : Fin 26 → Bool) => [(x 5), (x 6), (x 7), (x 8), (x 11), (x 12), (x 15), (x 16), (x 17), (x 18), (x 19), (x 20), (x 21), (x 22), (x 23), (x 24), (x 25), ((x 15) || (x 19)), (((x 15) || (x 19)) || (x 25)), ((x 16) || (x 17)), (((x 16) || (x 17)) || (x 21)), ((x 20) || (x 22)), (((x 20) || (x 22)) || (x 23))]
  let boundary := fun (x : Fin 26 → Bool) => ((((x 2) && ((((x 15) || (x 19)) || (x 25)) || (x 14))) || ((x 4) && ((((x 16) || (x 17)) || (x 21)) || (x 14)))) || ((x 10) && ((((x 20) || (x 22)) || (x 23)) || (x 14))))
  let table : ℕ := 24749718305498079621930527097498335442137279197626496029518248530172548797799224936072389485319537874714400543987346478869538328791042887897385431137650442121822125453581186143859513375427926096064882457539601859103283634154870303441993891390777986565919979175643416909449670950602159920178122801498454473219710784461778908339632453414244846348181503388326094920449037569956739384615695692720503057770755230646148445727895136269660718524009416891565235091620606408034846277441353553975027826559303807553151358216376089654963079479931175226745585581562067598134151238135934849740079126516116677933946731502218915207289099308788402556729120305016560022100387866781639473099223933714381775405707511715333472755765181285920998524596012045223019012856141229902566222499567409788571736535001044850045948519104417478168393581350093797594880276133575874627892204332253929210473323445576379226850372331156161802793413664305658512354074720882584860128250472586793504339970941661096119594122814361259934146331947574351489974766143078959438390575442253091517020141828254449237069821598701294883930803486712204568421125103817734495546200995830552389906655204687936231428280130610824327108107928367837470465918461767830348125370243594190913
  let sample := fun (j : ℕ) => List.ofFn (fun i : Fin 23 => table.testBit (23*j+i.val))
  let pickP := fun (p l : Fin 13) => ((173671011931810457051060143401965440055358600162717398050255838149085666127069916509681944142724516543052051467800466506867008121133178623776136412522276560310609957059612722584171951384431622652648501150453778065026969750085279535208963924306429363617792 : ℕ) >>> (5*(13*p.val+l.val))) % 32
  let pickN := fun (r : Fin 8) (s : Fin 3) (t : Fin 13) (d : Bool) =>
    ((343808314082767396231218740698062212823622357957447584911298276091451918212212270342608669845127243381548594684263592430160519015062412772841591164465309921526244836694278271320015345240838864573863124182889200311215412940902442314549118526740161875579170073539819946924323622055276570759485761251969763424518776951205359835867498457013048246255698863538106289762534181618004207319244024890735473169954957956186945026853955123521516925160912089732574107887662068257860863508442621838477652051232908104176352631574774791618284873926518595460657767327718559327665072427461843615797032141152825007009363425845683236524900496160889976461610498147196182712174244778075235673522313844547623190210043277394203619531875442403312020367009791994712295319855150182234137122460790021705581027854368672183027252875180280145826942248262950759195310391266130645229639318095078830784446851925550619682701474845369227069342001075758228387541846554081171389874621873726354735332837594196874656964464240758067550217891321425038806771163732969113747470662808294401055433247473380235496137463533103040580398180235756014529344091784637935095356972700193308319912676141316897650465456000871247124396744925976637991696508788713412837681072607467659145036400391890314022936224915865337784678009772385756901142999869603349631027681326984021700643955202769762108816137876465270654209947008750882268712468297588912955445094736265744522686482852473286007092940696609351045101855201598663172042745260366989783522831531599334242167107 : ℕ) >>> (8*(78*r.val+26*s.val+2*t.val+d.toNat))) % 256
  let nrow := fun (r : Fin 8) (s : Fin 3) t d => row (reps.getD r.val (0,0)) (mults.getD s.val 0) t d
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have wiresEq (Q : Circuit) (x : List Bool) : Q.wires x =
      Q.gates.foldl (fun w k => w ++ [k.op.eval (k.inputs.map (fun i => w.getD i false))]) x := rfl
  have evalEq (Q : Circuit) (x : List Bool) : Q.eval x = (Q.wires x).getD Q.output false := rfl
  have indices : inp = [2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25] := by decide
  have feat_eq (x : Fin 26 → Bool) :
      ids.map (fun i => (P.wires (inp.map x)).getD i false) = feats x := by
    rw [indices]
    simp [ids,P,g,wiresEq,evalAnd,evalOr,feats]
  have boundary_eq (x : Fin 26 → Bool) : P.eval (inp.map x) = boundary x := by
    rw [indices]
    simp [P,g,evalEq,wiresEq,evalAnd,evalOr,boundary]
  have positive : ∀ p l : Fin 13, p ∉ D → p-l ∈ D →
      boundary (pair p l) = true ∨
        (pickP p l < 24 ∧ feats (pair p l) = sample (pickP p l)) := by decide +kernel
  have negative : ∀ (r : Fin 8) (s : Fin 3) (t : Fin 13) (d : Bool),
      let y := nrow r s t d
      let j := pickN r s t d
      boundary y = false ∧ j < 177 ∧ 24 ≤ j ∧
        ∀ i : Fin 23, (feats y).getD i.val false = true → table.testBit (23*j+i.val) = true := by
    decide +kernel
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

  have getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
    simp

  have gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
      (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
      op.eval l₁ = true → op.eval l₂ = true := by
    rcases hop with rfl | rfl
    · simp only [evalAnd, List.all_eq_true, id_eq]
      intro h b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        have hi1 : i < l₁.length := by omega
        rw [List.getD_eq_getElem _ _ hi1]
        exact h _ (List.getElem_mem hi1)
      have h2 := hle i h1
      rwa [List.getD_eq_getElem _ _ hi] at h2
    · simp only [evalOr, List.any_eq_true, id_eq]
      rintro ⟨b, hb, rfl⟩
      obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        rw [List.getD_eq_getElem _ _ hi]; exact hbi
      have h2 := hle i h1
      have hi2 : i < l₂.length := by omega
      rw [List.getD_eq_getElem _ _ hi2] at h2
      exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

  have wiresFrom_mono (gs : List Gate)
      (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
    induction gs with
    | nil =>
      intro w₁ w₂ _ hle i hi
      exact hle i hi
    | cons g gs ih =>
      intro w₁ w₂ hlen hle i hi
      have hstep1 : wiresFrom (g :: gs) w₁ =
          wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
      have hstep2 : wiresFrom (g :: gs) w₂ =
          wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
      rw [hstep1] at hi
      rw [hstep2]
      apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle j hj
      · by_cases heq : j = w₁.length
        · subst heq
          rw [getD_snoc_eq] at hj
          rw [hlen, getD_snoc_eq]
          exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
            (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
            (by simp) (by
              intro t ht
              by_cases ht_lt : t < g.inputs.length
              · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
                rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
                simp only [List.getElem_map] at ht ⊢
                exact hle _ ht
              · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
                exact Bool.noConfusion ht) hj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj
  have monoEval (Q : Circuit) (mq : Monotone2 Q) (a b : List Bool)
      (hl : a.length=b.length) (h : ∀ i, a.getD i false=true → b.getD i false=true) :
      Q.eval a=true → Q.eval b=true := by
    apply wiresFrom_mono Q.gates _ a b hl h Q.output
    intro u hu
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (mq u hu).1
  obtain ⟨B,bm,bo,bs,fit⟩ := core
  have pm : Monotone2 P := by
    change ∀ u ∈ P.gates, u.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ u.inputs.length ≤ 2
    simp [P,g]
  obtain ⟨C,cm,co,cs,sem⟩ := routing P B ids pm bm (by decide) (by decide) (by decide) bo
  have joined (x : Fin 26 → Bool) :
      C.eval (inp.map x) = (boundary x || B.eval (feats x)) := by
    rw [sem _ (by rw [indices]; simp),boundary_eq,feat_eq]
  have ps : P.size = 14 := rfl
  refine ⟨C,cm,co,by omega,?_,?_⟩
  · intro p l hp hl
    change C.eval (inp.map (pair p l)) = true
    rw [joined,Bool.or_eq_true]
    rcases positive p l hp hl with h|⟨hj,he⟩
    · exact Or.inl h
    · apply Or.inr
      rw [he]
      let j : Fin 177 := ⟨pickP p l,by omega⟩
      have f := fit j
      change B.eval (sample (pickP p l)) = decide (pickP p l < 24) at f
      simpa only [hj,decide_true] using f
  · intro z hz m hm t d
    change z ∈ reps at hz
    change m ∈ mults at hm
    obtain ⟨ri,hr,er⟩ := List.mem_iff_getElem.mp hz
    obtain ⟨si,hs,es⟩ := List.mem_iff_getElem.mp hm
    let r : Fin 8 := ⟨ri,hr⟩
    let s : Fin 3 := ⟨si,hs⟩
    have e : nrow r s t d = row z m t d := by
      change row (reps.getD ri (0,0)) (mults.getD si 0) t d = _
      rw [List.getD_eq_getElem _ _ hr,List.getD_eq_getElem _ _ hs,er,es]
    change C.eval (inp.map (row z m t d)) = false
    rw [← e,joined]
    obtain ⟨bd,ju,jl,h⟩ := negative r s t d
    rw [bd,Bool.false_or]
    let j := pickN r s t d
    let y := nrow r s t d
    have f := fit ⟨j,ju⟩
    change B.eval (sample j) = decide (j < 24) at f
    have off : B.eval (sample j) = false := by
      simpa only [show ¬ j < 24 by exact Nat.not_lt.mpr jl,decide_false] using f
    apply Bool.eq_false_iff.mpr
    intro yes
    have len : (feats y).length = 23 := rfl
    have slen : (sample j).length = 23 := by simp [sample]
    have compare (i : ℕ) (hi : (feats y).getD i false = true) : (sample j).getD i false = true := by
      by_cases small : i < 23
      · rw [List.getD_eq_getElem _ _ (by omega : i < (sample j).length)]
        simpa only [sample,List.getElem_ofFn] using h ⟨i,small⟩ hi
      · rw [List.getD_eq_default _ _ (by omega : (feats y).length ≤ i)] at hi
        exact Bool.noConfusion hi
    exact Bool.noConfusion (off.symm.trans (monoEval B bm (feats y) (sample j) (len.trans slen.symm) compare yes))
