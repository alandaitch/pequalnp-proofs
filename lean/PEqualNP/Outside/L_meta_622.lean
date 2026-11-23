import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.MetaComplexity.Helpers.Machines.StrEq

-- The renaming argument is adapted from hpine2939's L_meta_500.
namespace PEqualNP.Outside.L_meta_622

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.Tab.StepW
  PEqualNP.Library.SearchHelpers.KSat.Hard

abbrev CP (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

theorem cpE {f f' : List Bool → List Bool} (h : CP f) (e : ∀ a, f a = f' a) : CP f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem findIdx_map' {α β : Type} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).findIdx q = l.findIdx (fun x => q (f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.findIdx_cons, ih]

theorem findIdx_range_succ (q : ℕ → Bool) (n : ℕ) :
    (List.range (n + 1)).findIdx q =
      if q 0 = true then 0 else (List.range n).findIdx (fun j => q (j + 1)) + 1 := by
  rw [List.range_succ_eq_map, List.findIdx_cons, findIdx_map']

theorem hd_un (k : ℕ) (a : List Bool) : hd (un k ++ false :: a) = un k := by
  induction k with
  | zero => simp [hd, un]
  | succ k ih =>
    rw [un_succ]
    simp only [hd] at ih
    simp [hd, ih]

theorem dropN_un (k : ℕ) (a : List Bool) : dropN (un k ++ false :: a) = a := by
  induction k with
  | zero => simp [dropN, un]
  | succ k ih =>
    rw [un_succ]
    simp only [dropN] at ih
    simp [dropN, ih]

theorem first_iter (g : List Bool → List Bool) (a : List Bool) (t : ℕ → Bool)
    (hg : ∀ i, g (un i ++ false :: a) =
      if t i = true then un i ++ false :: a else un (i + 1) ++ false :: a) :
    ∀ (n i : ℕ), g^[n] (un i ++ false :: a) =
      un (i + (List.range n).findIdx (fun j => t (i + j))) ++ false :: a := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [Function.iterate_succ_apply, hg i, findIdx_range_succ]
    by_cases h : t i = true
    · have hfix : g (un i ++ false :: a) = un i ++ false :: a := by
        rw [hg i]
        simp [h]
      simp only [Nat.add_zero, h, ↓reduceIte]
      exact Function.iterate_fixed hfix n
    · have hb : t i = false := by simpa using h
      simp only [Nat.add_zero, hb, Bool.false_eq_true, ↓reduceIte]
      rw [ih (i + 1)]
      have e : (fun j => t (i + 1 + j)) = (fun j => t (i + (j + 1))) := by
        funext j
        congr 1
        omega
      rw [e]
      congr 2
      omega

theorem cpt_first {p cnt arg : List Bool → List Bool} (hp : CP p) (hcnt : CP cnt)
    (harg : CP arg) :
    CP (fun s => un ((List.range (cnt s).length).findIdx
      (fun i => !(p (pairB (un i) (arg s))).isEmpty))) := by
  have hq : CP (fun y => pairB (hd y) (dropN y)) := cpt_pairB2 cpt_hd cpt_dropN
  have hg : CP (fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y) :=
    cpt_sel (cpt_comp hq hp) (cpt_cons1 true cpt_id) cpt_id
  have hit : CP (fun s => (fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y)^[(cnt s).length]
      (false :: arg s)) :=
    cpt_iterGrow hg 1
      (by
        intro y
        simp only [sel]
        split_ifs <;> simp)
      hcnt (cpt_cons1 false harg)
  refine cpE (cpt_comp hit cpt_hd) ?_
  intro s
  have h := first_iter (fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y) (arg s)
    (fun i => !(p (pairB (un i) (arg s))).isEmpty)
    (by
      intro i
      rw [hd_un, dropN_un]
      by_cases h0 : p (pairB (un i) (arg s)) = []
      · simp [sel, h0, un_succ]
      · simp [sel, h0])
    (cnt s).length 0
  simp only [un_zero, List.nil_append, Nat.zero_add] at h
  show hd ((fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y)^[(cnt s).length]
    (false :: arg s)) = _
  rw [h, hd_un]

def halfU (u : List Bool) : List Bool := un (u.length / 2)

def parU (u : List Bool) : List Bool := [decide (u.length % 2 = 1)]

def hfD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, none)
  | true, _ => (false, some true)

theorem hfD_run (l : List Bool) :
    fstRun hfD (fun _ => none) false l = un (l.length / 2) ∧
      fstRun hfD (fun _ => none) true l = un ((l.length + 1) / 2) := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons a l ih =>
    constructor
    · simp only [fstRun, hfD, Option.toList_none, List.nil_append, ih.2, List.length_cons]
    · simp only [fstRun, hfD, Option.toList_some, ih.1, List.length_cons]
      rw [show (l.length + 1 + 1) / 2 = l.length / 2 + 1 by omega, un_succ]
      rfl

theorem cpt_halfU : CP halfU :=
  fst_polyTime _ _ _ hfD (fun _ => none) false (fun s => (hfD_run s).1.symm)

def paD : Bool → Bool → Bool × Option Bool
  | q, _ => (!q, none)

theorem paD_run (l : List Bool) : ∀ q : Bool,
    fstRun paD (fun q => some q) q l = [xor q (decide (l.length % 2 = 1))] := by
  induction l with
  | nil => intro q; simp [fstRun]
  | cons a l ih =>
    intro q
    simp only [fstRun, paD, Option.toList_none, List.nil_append, ih, List.length_cons]
    by_cases h : l.length % 2 = 1
    · have h2 : ¬ (l.length + 1) % 2 = 1 := by omega
      cases q <;> simp [h, h2]
    · have h2 : (l.length + 1) % 2 = 1 := by omega
      cases q <;> simp [h, h2]

theorem cpt_parU : CP parU :=
  fst_polyTime _ _ _ paD (fun q => some q) false (fun s => by
    rw [paD_run]
    simp [parU])

def binStep (y : List Bool) : List Bool :=
  sel (unpairB y).1 y
    (pairB (halfU (unpairB y).1) ((unpairB y).2 ++ true :: parU (unpairB y).1))

def binU (u : List Bool) : List Bool := (unpairB (binStep^[u.length] (pairB u []))).2

theorem binStep_length (y : List Bool) : (binStep y).length ≤ y.length + 2 := by
  have h := unpairB_length y
  simp only [binStep, sel]
  split_ifs with h0
  · omega
  · have h1 : 1 ≤ (unpairB y).1.length := by
      rcases hl : (unpairB y).1 with _ | ⟨b, t⟩
      · exact absurd hl h0
      · simp
    simp only [pairB, halfU, parU, un, List.length_append, List.length_cons, List.length_replicate,
      List.length_nil]
    omega

theorem cpt_binStep : CP binStep :=
  cpt_sel cpt_unpairB1 cpt_id
    (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_halfU)
      (cpt_app2 cpt_unpairB2 (cpt_cons1 true (cpt_comp cpt_unpairB1 cpt_parU))))

theorem bits_pos (k : ℕ) (hk : 0 < k) :
    k.bits = decide (k % 2 = 1) :: (k / 2).bits := by
  have h := Nat.bits_append_bit (k / 2) (decide (k % 2 = 1))
    (by
      intro h0
      have : k % 2 = 1 := by omega
      simp [this])
  have e : Nat.bit (decide (k % 2 = 1)) (k / 2) = k := by
    rw [Nat.bit_val]
    by_cases h1 : k % 2 = 1
    · simp only [h1, decide_true, Bool.toNat_true]
      omega
    · simp only [h1, decide_false, Bool.toNat_false]
      omega
  rw [e] at h
  exact h

theorem binStep_iter : ∀ (n k : ℕ) (out : List Bool), k ≤ n →
    binStep^[n] (pairB (un k) out) = pairB [] (out ++ k.bits.flatMap (fun d => [true, d])) := by
  intro n
  induction n with
  | zero =>
    intro k out hk
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    intro k out hk
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · have e : binStep (pairB (un 0) out) = pairB (un 0) out := by
        simp [binStep, unpairB_pairB, sel]
      rw [e]
      exact ih 0 out (by omega)
    · have e : binStep (pairB (un k) out) =
          pairB (un (k / 2)) (out ++ [true, decide (k % 2 = 1)]) := by
        have hne : un k ≠ [] := by
          intro h0
          have := congrArg List.length h0
          simp at this
          omega
        simp [binStep, unpairB_pairB, sel, hne, halfU, parU]
      rw [e, ih (k / 2) _ (by omega), bits_pos k hpos]
      simp

theorem binU_un (k : ℕ) : binU (un k) = k.bits.flatMap (fun d => [true, d]) := by
  simp only [binU, un_length]
  rw [binStep_iter k k [] le_rfl, unpairB_pairB]
  rfl

theorem cpt_binU {U : List Bool → List Bool} (hU : CP U) : CP (fun s => binU (U s)) :=
  cpE (cpt_comp (cpt_iterGrow cpt_binStep 2 binStep_length hU (cpt_pairB2 hU (cpt_const [])))
    cpt_unpairB2) (fun _ => rfl)

theorem cpt_eqF {u v : List Bool → List Bool} (hu : CP u) (hv : CP v) :
    CP (fun s => bflag (decide (u s = v s))) := by
  have s : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  exact cpE (cpt_bitFlag (cpt_comp (cpt_pair hu hv) s)) (fun _ => rfl)

def testP (s : List Bool) : List Bool :=
  bflag (decide ((headI (dropI^[(unpairB s).1.length] (unpairB (unpairB s).2).2)).tail.tail =
    ((unpairB (unpairB s).2).1).tail.tail))

theorem cpt_testP : CP testP := by
  have h1 : CP (fun s => (unpairB (unpairB s).2).1) :=
    cpt_comp (f := fun s : List Bool => (unpairB s).2) (g := fun s : List Bool => (unpairB s).1)
      cpt_unpairB2 cpt_unpairB1
  have h2 : CP (fun s => (unpairB (unpairB s).2).2) :=
    cpt_comp (f := fun s : List Bool => (unpairB s).2) (g := fun s : List Bool => (unpairB s).2)
      cpt_unpairB2 cpt_unpairB2
  exact cpt_eqF
    (cpt_tail1 (cpt_tail1 (cpt_comp (cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 h2)
      cpt_headI)))
    (cpt_tail1 (cpt_tail1 h1))

def Kfun (it x : List Bool) : List Bool :=
  un ((List.range x.length).findIdx (fun j => !(testP (pairB (un j) (pairB it x))).isEmpty))

theorem cpt_K {I X : List Bool → List Bool} (hI : CP I) (hX : CP X) :
    CP (fun s => Kfun (I s) (X s)) :=
  cpE (cpt_first cpt_testP hX (cpt_pairB2 hI hX)) (fun _ => rfl)

def litR (it x : List Bool) : List Bool :=
  tk [true, true] it ++ (binU (Kfun it x) ++ [false, true])

theorem cpt_litR {I X : List Bool → List Bool} (hI : CP I) (hX : CP X) :
    CP (fun s => litR (I s) (X s)) :=
  cpE (cpt_app2 (cpt_tk (cpt_const [true, true]) hI)
    (cpt_app2 (cpt_binU (cpt_K hI hX)) (cpt_const [false, true]))) (fun _ => rfl)

def outR (x r : List Bool) : List Bool :=
  sel r [] (sel (bflag (isEnd r)) (litR (headI r) x) [false, false])

theorem cpt_outR {X R : List Bool → List Bool} (hX : CP X) (hR : CP R) :
    CP (fun s => outR (X s) (R s)) := by
  have hEnd : CP (fun s => bflag (isEnd (R s))) := cpE (cpt_comp hR cpt_isEndF) (fun _ => rfl)
  have hH : CP (fun s => headI (R s)) := cpt_comp hR cpt_headI
  exact cpE (cpt_sel hR (cpt_const []) (cpt_sel hEnd (cpt_litR hH hX) (cpt_const [false, false])))
    (fun _ => rfl)

def rndR (y : List Bool) : List Bool :=
  outR (unpairB y).2 (dropI^[(unpairB y).1.length] (unpairB y).2)

theorem cpt_rndR : CP rndR :=
  cpt_outR cpt_unpairB2 (cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 cpt_unpairB2)

def GR (x : List Bool) : List Bool :=
  (List.range x.length).flatMap fun i => outR x (dropI^[i] x)

theorem cpt_GR : CP GR :=
  cpE (cpt_flatMapRange cpt_rndR cpt_id cpt_id) (fun x => by
    simp only [rndR, unpairB_pairB, un_length]
    rfl)

def items (φ : CNF) : List (Option Literal) := φ.flatMap (fun c => c.map some ++ [none])

def encIt : Option Literal → List Bool
  | some l => encodeLiteral l
  | none => [false, false]

def encIts (L : List (Option Literal)) : List Bool := L.flatMap encIt

theorem encIts_cons (o : Option Literal) (L : List (Option Literal)) :
    encIts (o :: L) = encIt o ++ encIts L := rfl

theorem encIts_append (L M : List (Option Literal)) :
    encIts (L ++ M) = encIts L ++ encIts M := by
  simp [encIts]

theorem encIts_clause (c : Clause) :
    encIts (c.map some ++ [none]) = encodeClause c := by
  induction c with
  | nil => simp [encIts, encIt, encodeClause]
  | cons l c ih =>
    simp only [List.map_cons, List.cons_append, encIts_cons, ih, encIt]
    simp [encodeClause]

theorem encIts_items (φ : CNF) : encIts (items φ) = encodeCNF φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e : items (c :: φ) = (c.map some ++ [none]) ++ items φ := by simp [items]
    rw [e, encIts_append, encIts_clause, ih]
    simp [encodeCNF]

theorem headI_it (o : Option Literal) (r : List Bool) : headI (encIt o ++ r) = encIt o := by
  cases o with
  | none => rfl
  | some l => exact headI_lit l r

theorem dropI_it (o : Option Literal) (r : List Bool) : dropI (encIt o ++ r) = r := by
  cases o with
  | none => rfl
  | some l => exact dropI_lit l r

theorem encIt_length (o : Option Literal) : 1 ≤ (encIt o).length := by
  cases o with
  | none => simp [encIt]
  | some l => simp [encIt, encodeLiteral_eq]

theorem encIts_length (L : List (Option Literal)) : L.length ≤ (encIts L).length := by
  induction L with
  | nil => simp
  | cons o L ih =>
    have := encIt_length o
    rw [encIts_cons, List.length_append, List.length_cons]
    omega

theorem tt_it (o : Option Literal) (v : ℕ) :
    decide ((encIt o).tail.tail = vcode v) = o.any (fun l' => l'.1 == v) := by
  cases o with
  | none =>
    have h : ¬ ([] : List Bool) = vcode v := fun h => vcode_ne_nil v h.symm
    simp [encIt, h]
  | some l =>
    simp only [encIt, encodeLiteral_eq, List.tail_cons, Option.any_some]
    by_cases h : l.1 = v
    · simp [h]
    · have h2 : ¬ vcode l.1 = vcode v := fun e => h (vcode_injective e)
      simp [h, h2]

theorem find_spec (v : ℕ) : ∀ (L : List (Option Literal)) (n : ℕ) (rest : List Bool),
    (∃ o ∈ L, o.any (fun l' => l'.1 == v) = true) → L.length ≤ n →
    (List.range n).findIdx (fun j =>
      decide ((headI (dropI^[j] (encIts L ++ rest))).tail.tail = vcode v)) =
      L.findIdx (fun o => o.any (fun l' => l'.1 == v)) := by
  intro L
  induction L with
  | nil =>
    intro n rest h
    obtain ⟨o, ho, -⟩ := h
    simp at ho
  | cons o L ih =>
    intro n rest h hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [findIdx_range_succ, List.findIdx_cons]
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply, encIts_cons,
      List.append_assoc, headI_it, dropI_it, tt_it]
    by_cases h0 : o.any (fun l' => l'.1 == v) = true
    · simp [h0]
    · have hL : ∃ o' ∈ L, o'.any (fun l' => l'.1 == v) = true := by
        obtain ⟨o', ho', h1⟩ := h
        rcases List.mem_cons.1 ho' with rfl | hm
        · exact absurd h1 h0
        · exact ⟨o', hm, h1⟩
      have hb : o.any (fun l' => l'.1 == v) = false := by simpa using h0
      rw [ih n rest hL (by simp at hn; omega)]

theorem Kfun_spec (φ : CNF) (l : Literal) (hl : some l ∈ items φ) :
    Kfun (encodeLiteral l) (encodeCNF φ) =
      un ((items φ).findIdx (fun o => o.any (fun l' => l'.1 == l.1))) := by
  have h := find_spec l.1 (items φ) (encodeCNF φ).length []
    ⟨some l, hl, by simp⟩ (by rw [← encIts_items]; exact encIts_length _)
  rw [List.append_nil, encIts_items] at h
  rw [Kfun, ← h]
  congr 2
  funext j
  simp only [testP, unpairB_pairB, un_length, encodeLiteral_eq, List.tail_cons]
  cases hd : decide ((headI (dropI^[j] (encodeCNF φ))).tail.tail = vcode l.1) <;> simp [bflag]

def ren (φ : CNF) (l : Literal) : Literal :=
  ((items φ).findIdx (fun o => o.any (fun l' => l'.1 == l.1)), l.2)

theorem litR_spec (φ : CNF) (l : Literal) (hl : some l ∈ items φ) :
    litR (encodeLiteral l) (encodeCNF φ) = encodeLiteral (ren φ l) := by
  rw [litR, Kfun_spec φ l hl, binU_un, tk_eq, encodeLiteral_eq, encodeLiteral_eq]
  simp [ren, vcode]

def walkR (x : List Bool) : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, r => outR x r ++ walkR x n (dropI r)

theorem walkR_range (x : List Bool) (n : ℕ) : ∀ r : List Bool,
    (List.range n).flatMap (fun i => outR x (dropI^[i] r)) = walkR x n r := by
  induction n with
  | zero => intro r; rfl
  | succ n ih =>
    intro r
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, walkR, ← ih]
    rfl

theorem walkR_nil (x : List Bool) (n : ℕ) : walkR x n [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walkR, outR, sel, dropI, ih]

theorem walkR_items (φ : CNF) : ∀ (L : List (Option Literal)) (n : ℕ),
    (∀ o ∈ L, o ∈ items φ) → L.length ≤ n →
    walkR (encodeCNF φ) n (encIts L) = encIts (L.map (Option.map (ren φ))) := by
  intro L
  induction L with
  | nil => intro n _ _; exact walkR_nil _ _
  | cons o L ih =>
    intro n hm hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [walkR, encIts_cons, dropI_it, ih n (fun o' ho' => hm o' (List.mem_cons_of_mem _ ho'))
      (by simp at hn; omega), List.map_cons, encIts_cons]
    congr 1
    cases o with
    | none => simp [outR, encIt, sel, bflag, isEnd]
    | some l =>
      have hne : encodeLiteral l ++ encIts L ≠ [] := by simp [encodeLiteral_eq]
      simp only [outR, encIt, Option.map_some, isEnd_lit, headI_lit,
        litR_spec φ l (hm _ List.mem_cons_self), sel, bflag, hne]
      simp

theorem items_map (f : Literal → Literal) (φ : CNF) :
    items (φ.map (fun c => c.map f)) = (items φ).map (Option.map f) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e1 : items (c :: φ) = (c.map some ++ [none]) ++ items φ := by simp [items]
    have e2 : items ((c :: φ).map (fun c => c.map f)) =
        ((c.map f).map some ++ [none]) ++ items (φ.map (fun c => c.map f)) := by simp [items]
    rw [e1, e2, ih]
    simp

theorem GR_enc (φ : CNF) :
    GR (encodeCNF φ) = encodeCNF (φ.map (fun c => c.map (ren φ))) := by
  rw [GR, walkR_range]
  have h := walkR_items φ (items φ) (encodeCNF φ).length (fun o ho => ho)
    (by rw [← encIts_items]; exact encIts_length _)
  rw [encIts_items] at h
  rw [h, ← items_map, encIts_items]

end PEqualNP.Outside.L_meta_622

open PEqualNP.Outside.L_meta_622 in
theorem PEqualNP.Outside.L_meta_622 : PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF PEqualNP.Search.encodeCNF (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) := by
  obtain ⟨c⟩ := cpt_GR
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun φ => by
    have h := c.outputsFun (PEqualNP.Search.encodeCNF φ)
    rw [GR_enc φ] at h
    exact h⟩⟩
