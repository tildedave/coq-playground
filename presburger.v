Section definitions.

Require Import String List BinInt ZArith.
Import ListNotations.

Inductive func : Set := Plus | Sub.
Inductive relation  : Set := Eq | Lt | Cong : Z -> relation.

(* term: x + 1 = y ---> = + x 1 y  *)
(* http://lara.epfl.ch/w/_media/sav12:qe_presburger_arithmetic.pdf *)

Section BasicEquations.

Inductive atom : Set :=
| Atom_Var : string -> atom
| Atom_Const : Z -> atom.

Inductive term : Set :=
| Term_Atom : atom -> term
| Term_Func : func -> term -> term -> term
| Term_MultK : Z -> term -> term.

Inductive literal : Type :=
| Literal_Relation : relation -> term -> term -> literal
| Literal_NotRelation : relation -> term -> term -> literal.

Inductive exp : Set :=
| Exp_Literal : literal -> exp
| Exp_Exists : (string -> exp) -> exp
| Exp_And : exp -> exp -> exp
| Exp_Or : exp -> exp -> exp
| Exp_Not : exp -> exp -> exp.

Section NormalizedEquations.

Inductive linearTerm : Type :=
| LinearTerm : Z -> string -> linearTerm.

Inductive normalLiteral : Set :=
(* 0 < K_0 + K_i * x_i *)
| NormalLiteral_Gtz : Z -> list linearTerm -> normalLiteral
(* 0 =_{M} K_0 + K_i * x_i *)
| NormalLiteral_Congz : Z -> Z -> list linearTerm -> normalLiteral.

Inductive conjunction : Type :=
| Conj_NormalLiteral : normalLiteral -> conjunction
| Conj_And : conjunction -> conjunction -> conjunction.

Inductive disjunction : Set :=
  | Disj_Conj : conjunction -> disjunction
  | Disj_Disj : conjunction -> disjunction -> disjunction.

(* (A v B) ^ (C v D) => (A v B) C v (A v B)D => AC v BC v AD v BD *)

Section normalizingLiterals.

Fixpoint conj_and_disjunction (c : conjunction) (d : disjunction) :=
    match d with
    | (Disj_Conj c') => Disj_Conj (Conj_And c c')
    | (Disj_Disj c' d') =>
        (* C ^ (C' + D) => C^C' + CD *)
        let c_and_c' := (Conj_And c c') in
        Disj_Disj c_and_c' (conj_and_disjunction c d')
    end.

Fixpoint disjunction_or (d1 d2 : disjunction) : disjunction :=
  match d1 with
  | (Disj_Conj c') => (Disj_Disj c' d2)
  | (Disj_Disj c' d1') => (Disj_Disj c' (disjunction_or d1' d2))
  end.

Fixpoint disjunction_and (d1 d2 : disjunction) : disjunction :=
    match d1 with
    | (Disj_Conj c') => conj_and_disjunction c' d2
    (* (C v D1') * D2) = CD2 v D1'D2 *)
    | (Disj_Disj c' d1') =>
        let c'_and_d2 := (conj_and_disjunction c' d2) in
        (disjunction_or c'_and_d2 (disjunction_and d1' d2))
    end.

Fixpoint disjunction_and_helper (d : disjunction) (dl : list disjunction) {struct d} : list disjunction :=
    match d with
    | (Disj_Conj c') => map (fun x => conj_and_disjunction c' x) dl
    (* (C' + DL')(DL) = C'DL + DL'DL *)
    | (Disj_Disj c' d') => map (fun x => conj_and_disjunction c' x) dl ++ (disjunction_and_helper d' dl)
    end.

Fixpoint disjunction_list_and (d1 d2 : list disjunction) : list disjunction :=
    match (d1, d2) with
    | ([], _) => d2
    | (_, []) => d1
    (* (X + D1')(Y + D2') = XY + XD2' + YD1' + D1'D2' *)
    | (x :: d1', y :: d2') =>
        (disjunction_and x y) :: (disjunction_and_helper x d2') ++ (disjunction_and_helper y d1') ++ (disjunction_list_and d1' d2')
    end.

Fixpoint removeCoeff (l1 : list linearTerm) (x : string) : (option linearTerm * list linearTerm) :=
    match l1 with
    | [] => (None, [])
    | l :: tl =>
        match l with
        | (LinearTerm n y) =>
            if string_dec x y then
                (Some l, tl)
            else
                let (r, lt) := (removeCoeff tl x) in
                (r, l :: lt)
        end
    end.

Fixpoint addCoeff (l1 : list linearTerm) (l2 : list linearTerm) :=
    match l1 with
    | [] => l2
    | (LinearTerm m x) :: tl =>
        let (r, l2') := (removeCoeff l2 x) in
            match r with
            | None => addCoeff tl l2 (* cannot happen *)
            | (Some (LinearTerm n y)) =>
                if Z_eq_dec (m + n) 0 then
                    (addCoeff tl l2')
                else
                    (LinearTerm (m + n) y) :: (addCoeff tl l2')
            end
    end.

Fixpoint subCoeff (l1 : list linearTerm) (l2 : list linearTerm) :=
    addCoeff l1 (map (fun lt => match lt with (LinearTerm n y) => (LinearTerm (-n) y) end) l2).

Eval simpl in subCoeff [(LinearTerm 1 "x"); (LinearTerm 5 "y")] [(LinearTerm 3 "z") ; (LinearTerm 1 "x") ; (LinearTerm 2 "y")].

Fixpoint multCoeff (k : Z) (l : list linearTerm) :=
    map (fun lt => match lt with (LinearTerm n y) => (LinearTerm (k * n)%Z y) end) l.

Fixpoint collectTerms (t : term) : (Z * list linearTerm) :=
    match t with
    | (Term_Atom a) =>
        match a with
        | (Atom_Const m) => (m, [])
        | (Atom_Var x) => (Z0, [LinearTerm (Zpos 1) x])
        end
    | (Term_Func f t1 t2) =>
        let '(K0, l1) := collectTerms t1 in
        let '(K1, l2) := collectTerms t2 in
            match f with
            | Plus =>
                ((K0 + K1)%Z, addCoeff l1 l2)
            | Sub =>
                ((K0 - K1)%Z, subCoeff l1 l2)
            end
    | (Term_MultK k t) =>
        let '(K0, l1) := collectTerms t in
            ((K0 * k)%Z, multCoeff k l1)
    end.

Definition normalLiteralToDisjunction (nl : normalLiteral) :=
    (Disj_Conj (Conj_NormalLiteral nl)).

Definition isZeroTerm t : bool :=
    match t with
    | (Term_Atom (Atom_Const 0)) => true
    | _ => false
    end.

Fixpoint negatedCongToDisjunction (k : Z) (n : nat) (K : Z) (ltl : list linearTerm) : disjunction :=
    match n with
    | 0  => normalLiteralToDisjunction (NormalLiteral_Gtz 0 []) (* ~(t1_0 t2) -> divisible by 0 is impossible *)
    | (S 0) => normalLiteralToDisjunction (NormalLiteral_Gtz 0 []) (* unsatisfiable, nothing is not cong 1 *)
    | (S (S 0)) => normalLiteralToDisjunction (NormalLiteral_Gtz (K + 1)%Z ltl)
    | (S m) => Disj_Disj
        (Conj_NormalLiteral (NormalLiteral_Gtz (K + (Z_of_nat' n))%Z ltl))
        (negatedCongToDisjunction k m K ltl)
    end.

Fixpoint normalizeLiteral (l : literal) : disjunction :=
    match l with
    | (Literal_Relation r t1 t2) =>
        let (K1, t1') := collectTerms t1 in
        let (K2, t2') := collectTerms t2 in
        match r with
        | Eq =>
            (* t1 = t2 -> t1 < t2 + 1 ^ t2 < t1 + 1 -> 0 > t2 - t1  + 1 ^ 0 > t1 - t2  + 1*)
            let l1 := NormalLiteral_Gtz (K2 - K1 + 1)%Z (subCoeff t2' t1') in
            let l2 := NormalLiteral_Gtz (K1 - K2 + 1)%Z (subCoeff t1' t2') in
                disjunction_and (normalLiteralToDisjunction l1) (normalLiteralToDisjunction l2)
        | Lt =>
            (* t1 < t2 -> 0 > t2 - t1 *)
            let l := NormalLiteral_Gtz (K2 - K1)%Z (subCoeff t2' t1') in
                normalLiteralToDisjunction l
        | (Cong k) =>
            (* t1 =_k t2 -> 0 _=k t2 - t1 *)
            let l := NormalLiteral_Congz k (K2 - K1)%Z (subCoeff t2' t1') in
                normalLiteralToDisjunction l
        end
    | (Literal_NotRelation r t1 t2) =>
        let (K1, t1') := collectTerms t1 in
        let (K2, t2') := collectTerms t2 in
        match r with
        | Eq =>
        (* ~(t1' = t2') -> (t1' < t2' v t2' < t1') -> 0 < t2' - t1' v 0 < t1' - t2' *)
            let l1 := NormalLiteral_Gtz (K2 - K1)%Z (subCoeff t2' t1') in
            let l2 := NormalLiteral_Gtz (K1 - K2)%Z (subCoeff t1' t2') in
                disjunction_or (normalLiteralToDisjunction l1) (normalLiteralToDisjunction l2)
        | Lt =>
        (* ~(t1 < t2) -> t2 < t1 + 1 -> 0 < t1 - t2 + 1 *)
            let l := NormalLiteral_Gtz (K1 - K2 + 1)%Z (subCoeff t1' t2') in
                normalLiteralToDisjunction l
        | (Cong k) =>
        (* ~(t1 =_k t2) -> V_{i = 1...k-1} 0_k (t2 - t1) + i *)
            negatedCongToDisjunction k (Zabs_nat k) (K2 - K1)%Z (subCoeff t2' t1')
        end
    end.

Section DenotationalSemantics.

Fixpoint denoteAtom (a : atom) (G : (string -> Z)) : Z :=
  match a with
  | (Atom_Var x) => (G x)
  | (Atom_Const n) => n
  end.

Fixpoint denoteTerm (t : term) (G : (string -> Z)) : Z :=
  match t with
  | (Term_Atom a) => denoteAtom a G
  | (Term_Func f t1 t2) =>
    match f with
    | Plus => (denoteTerm t1 G) + (denoteTerm t2 G)
    | Sub => (denoteTerm t1 G) - (denoteTerm t2 G)
    end
  | (Term_MultK k t) => k * (denoteTerm t G)
  end.

Fixpoint denoteLiteral (l : literal) (G : (string -> Z)) : bool :=
  match l with
  | (Literal_Relation r t1 t2) =>
    let (n1, n2) := (denoteTerm t1 G, denoteTerm t2 G) in
    match r with
    | Eq => if Z_eq_dec n1 n2 then true else false
    | Lt => if Z_lt_dec n1 n2 then true else false
    | (Cong k) => if Z_eq_dec (n1 mod n2) 0 then true else false
    end
  | (Literal_NotRelation r t1 t2) =>
    let (n1, n2) := (denoteTerm t1 G, denoteTerm t2 G) in
    match r with
    | Eq => if Z_eq_dec n1 n2 then false else true
    | Lt => if Z_lt_dec n1 n2 then false else true
    | (Cong k) => if Z_eq_dec (n1 mod n2) 0 then false else true
    end
  end.

Fixpoint denoteLinearTerm (l : linearTerm) (G : (string -> Z)): Z :=
  match l with
  | (LinearTerm n x) => n * (G x)
  end.

Definition denoteLinearTermList (ltl : list linearTerm) (G : (string -> Z)) : Z :=
  (fold_left (fun n lt => (n + (denoteLinearTerm lt G))%Z) ltl Z0).

Definition denoteLinearTermSequence (K : Z) (ltl : list linearTerm) (G : (string -> Z)) : Z :=
  (denoteLinearTermList ltl G) + K.

Fixpoint denoteNormalLiteral (nl : normalLiteral) (G : (string -> Z)) : bool :=
  match nl with
  | (NormalLiteral_Gtz K0 ltl) => if Z_lt_dec Z0 (denoteLinearTermSequence K0 ltl G) then true else false
  | (NormalLiteral_Congz K K0 ltl) => if Z_eq_dec Z0 ((denoteLinearTermSequence K ltl G) mod K) then true else false
  end.

Fixpoint denoteConjunction (c : conjunction) (G : (string -> Z)) : bool :=
  match c with
  | (Conj_NormalLiteral n) => denoteNormalLiteral n G
  | (Conj_And c1 c2) => andb (denoteConjunction c1 G) (denoteConjunction c2 G)
  end.

Fixpoint denoteDisjunction (d : disjunction) (G : (string -> Z)) : bool :=
  match d with
  | Disj_Conj c => denoteConjunction c G
  | Disj_Disj c d' => orb (denoteConjunction c G) (denoteDisjunction d' G)
  end.

Eval simpl in denoteLinearTermSequence 100 [] (fun n => 1%Z).

Lemma removeCoeff_None :
  forall (G : string -> Z) ltl x ltl',
    (removeCoeff ltl x) = (None, ltl') -> ltl = ltl'.
Proof.
  intros.
  induction ltl.
  unfold removeCoeff in H.
  inversion H.
  reflexivity.
  destruct a.
  unfold removeCoeff in H.
  fold removeCoeff in H.
  destruct (string_dec x s) in H.
  (* impossible branch *)
  inversion H.
  destruct (removeCoeff ltl x).
  inversion H.

Lemma removeCoeff_works_None :
  forall (G : string -> Z) ltl x ltl',
    (removeCoeff ltl x) = (None, ltl') ->
    (denoteLinearTermList ltl G) = (denoteLinearTermList ltl' G).
Proof.
  intros.
  induction ltl'.
  (* ltl' is [] *)
  unfold removeCoeff in H.
  unfold denoteLinearTermList at 2.
  simpl.
  case ltl.
  (* ltl is [] *)
  unfold denoteLinearTermList at 1.
  simpl.
  reflexivity.
  (* ltl is a non-empty list *)

Lemma removeCoeff_works :
  forall (G : string -> Z) ltl n x ltl2,
    (removeCoeff ltl x) = (Some (LinearTerm n x), ltl2) ->
    (denoteLinearTermList ltl G) = (n * (G x) + (denoteLinearTermList ltl2 G))%Z.
Proof.
  intros.
  induction ltl.
  (* empty list case *)
  simpl in H.
  inversion H.
  (* list is populated case *)
  simpl in H.
  unfold denoteLinearTermList at 1.
  unfold denoteLinearTerm.
  simpl.

Lemma addCoeff_works :
  forall G lt0 lt1 lt,
    addCoeff lt0 lt1 = lt ->
    (denoteLinearTermList lt G) = ((denoteLinearTermList lt0 G) + (denoteLinearTermList lt1 G))%Z.
Proof.
  intros.
  induction lt0.
  simpl.
  simpl in H.
  rewrite H.
  reflexivity.
  unfold addCoeff in H.
  fold addCoeff in H.
  case a.
  intros.
  (* must use information on how removeCoeff works *)

      Lemma collectTerms_Plus :
  forall G t1 t2 K0 K1 lt0 lt1,
    (collectTerms t1) = (K0, lt0) ->
    (collectTerms t2) = (K1, lt1) ->

Theorem collectTerms_Denotation :
  forall t G K ltl,
    (collectTerms t) = (K, ltl) -> (denoteTerm t G) = (denoteLinearTermSequence K ltl G).
Proof.
  intros t G.
  induction t.
  (* t is an atom *)
  induction a.
  (* a is a variable *)
  intros.
  unfold denoteTerm.
  simpl.
  simpl in H.
  inversion H.
  unfold denoteLinearTermSequence.
  unfold fold_left.
  rewrite Z.add_0_r.
  rewrite Z.add_0_l.
  unfold denoteLinearTerm.
  rewrite Z.mul_1_l.
  reflexivity.
  (* a is a constant *)
  intros.
  simpl.
  simpl in H.
  inversion H.
  unfold denoteLinearTermSequence.
  unfold fold_left.
  rewrite Z.add_0_l.
  reflexivity.
  (* t is a function *)
  case f.
  (* plus *)
  intros.
  unfold denoteTerm.
  simpl.
  fold denoteTerm.
  (* need to get into a place where he can apply the induction hypothesis *)
  simpl in H.
  remember (collectTerms t1) as terms1.
  remember (collectTerms t2) as terms2.
Qed.


  unfold denoteLinearTermSequence.
  fold denoteLinearTermSequence.
  unfold fold_left.
  fold fold_left.
  simpl.

  Theorem normalizePreservesDenotation :
  forall l d G,
  (normalizeLiteral l) = d -> (denoteLiteral l G) = (denoteDisjunction d G).
Proof.
induction l.
elim r.
unfold normalizeLiteral.


Inductive expDnf : Type :=
  | expDnf_Exists : (string -> expDnf) -> expDnf
  | expDnf_Disjunction : list disjunction -> expDnf.


Fixpoint dnfOr_helper (e1 : expDnf) (dl : list disjunction) : expDnf :=
   match e1 with
   | (expDnf_Exists d) =>
       expDnf_Exists (fun (m : string) => dnfOr_helper (d m) dl)
   | (expDnf_Disjunction dl1) => expDnf_Disjunction (rev_append dl1 dl)
  end.

(* Combines two terms that are already DNF together *)
Fixpoint dnfOr (e1 e2 : expDnf) : expDnf :=
    match (e1, e2) with
    | (expDnf_Exists d1, expDnf_Exists d2) =>
        expDnf_Exists
            (fun (m : string) => expDnf_Exists
                (fun (n : string) => (dnfOr (d1 n) (d2 m))))
    | (expDnf_Exists d1, expDnf_Disjunction dl2) =>
        (expDnf_Exists
            (fun (m : string) => (dnfOr_helper (d1 m) dl2)))
    | (expDnf_Disjunction dl1, expDnf_Exists d2) =>
        (expDnf_Exists
            (fun (n : string) => (dnfOr_helper (d2 n) dl1)))
    | (expDnf_Disjunction dl1, expDnf_Disjunction dl2) =>
        (expDnf_Disjunction (rev_append dl1 dl2))
    end.


Eval simpl in (conj_and_disjunction (Conj_NormalLiteral (Gtz_LinearEquation 0 (Term_Atom (Atom_Var "A"))) (Disj_Disj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "B"))) (Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "C"))))))))).

Fixpoint dnfAnd_helper (e1 : expDnf) (dl : list disjunction) : expDnf :=
    match e1 with
    | (expDnf_Exists d) =>
        expDnf_Exists (fun (m : string) => dnfAnd_helper (d m) dl)
    | (expDnf_Disjunction dl1) => expDnf_Disjunction (disjunction_list_and dl1 dl)
    end.

Fixpoint dnfAnd (e1 e2 : expDnf) : expDnf :=
    (* this is where terms can explode *)
    match (e1, e2) with
    | (expDnf_Exists d1, expDnf_Exists d2) =>
        expDnf_Exists
            (fun (m : string) => expDnf_Exists
                (fun (n : string) => (dnfAnd (d1 n) (d2 m))))
    | (expDnf_Exists d1, expDnf_Disjunction dl2) =>
        expDnf_Exists
            (fun (m : string) => (dnfAnd_helper (d1 m) dl2))
    | (expDnf_Disjunction dl1, expDnf_Exists d2) =>
        expDnf_Exists
            (fun (n : string) => (dnfAnd_helper (d2 n) dl1))
    | (expDnf_Disjunction dl1, expDnf_Disjunction dl2) =>
        (expDnf_Disjunction (disjunction_list_and dl1 dl2))
    end.

Fixpoint dnfConvert (e : exp) : expDnf :=
    match e with
    | (Exp_Term l) => (expDnf_Disjunction [Disj_Conj (Conj_Lit l)])
    | (Exp_Exists d) =>
        expDnf_Exists
            (fun (m : string) => dnfConvert (d m))
    | (Exp_And e1 e2) => dnfAnd (dnfConvert e1) (dnfConvert e2)
    | (Exp_Or e1 e2) => dnfOr (dnfConvert e1) (dnfConvert e2)
    end.

(* TODO: valuations, prove normalization is right *)


Eval simpl in (dnfConvert (Exp_Or (Exp_Term (Lit_Var "A")) (Exp_Term (Lit_Var "B")))).
Eval simpl in (dnfConvert (Exp_Or (Exp_Term (Lit_Var "C")) (Exp_Term (Lit_Var "D")))).

Eval simpl in dnfAnd
    (expDnf_Disjunction [Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "A"))); Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "B")))])
    (expDnf_Disjunction [Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "C"))); Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "D")))]).

Eval simpl in (dnfConvert (Exp_And
    (Exp_Or (Exp_Lit (Lit_Var "A")) (Exp_Lit (Lit_Var "B")))
    (Exp_Or (Exp_Lit (Lit_Var "C")) (Exp_Lit (Lit_Var "D"))))).


Eval simpl in (dnfConvert (Exp_And
    (Exp_Or (Exp_Lit (Lit_Var "A")) (Exp_Exists (fun a => (Exp_Lit (Lit_Var a)))))
    (Exp_Or (Exp_Lit (Lit_Var "C")) (Exp_Lit (Lit_Var "D"))))).

(*
    Ex Ey Ez (x  + y + z = 2)
    Ew Ex Ey Ez (x + y = w) ^ (w + z = 2)

*)
